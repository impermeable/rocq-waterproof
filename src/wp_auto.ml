(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

open Auto
open Hints
open Names
open Pp
open Proofview
open Proofview.Notations
open Tactics
open Termops
open Unification
open Util

open Backtracking
open Proofutils

(* All the definitions below come from rocq-core hidden library (i.e not visible in the API) *)

let auto_core_unif_flags_of st1 st2 = {
  modulo_conv_on_closed_terms = Some st1;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = st2;
  modulo_delta_types = TransparentState.full;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true;
  allowed_evars = Evarsolve.AllowedEvars.all;
  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = false;
  modulo_eta = true;
}

let auto_unif_flags_of st1 st2 =
  let flags = auto_core_unif_flags_of st1 st2 in {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = { flags with modulo_delta = TransparentState.empty };
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = true
}

let auto_unif_flags =
  auto_unif_flags_of TransparentState.full TransparentState.empty

let unify_resolve_nodelta (h: hint): unit tactic = Hints.hint_res_pf ~with_evars:true ~flags:auto_unif_flags h

let exact (h: hint): unit tactic =
  Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let sigma, c = Hints.fresh_hint env sigma h in
    let sigma, t = Typing.type_of env sigma c in
    let concl = Goal.concl gl in
    if occur_existential sigma t || occur_existential sigma concl then
      try
        let _, sigma = Unification.w_unify env sigma CONV ~flags:auto_unif_flags concl t in
        Unsafe.tclEVARSADVANCE sigma <*>
        exact_no_check c
      with e when CErrors.noncritical e -> tclZERO e
    else Unsafe.tclEVARS sigma <*> exact_check c
  end

(**
  Same function as {! Auto.exists_evaluable_reference}
*)
let exists_evaluable_reference (env: Environ.env) (evaluable_ref: Evaluable.t): bool = match evaluable_ref with
  | Evaluable.EvalConstRef _ -> true
  | Evaluable.EvalProjectionRef _ -> true
  | Evaluable.EvalVarRef v -> try ignore(Environ.lookup_named v env); true with Not_found -> false

(* All the definitions below are inspired by the rocq-core hidden library (i.e not visible in the API) but modified for Waterproof *)

(**
  Prints "idtac" if the [log] field is [true]
*)
let pr_info_nop (): unit = Feedback.msg_notice (str "idtac.")

(**
  Prints a debug header if [log] is [true]
*)
let pr_dbg_header (): unit = Feedback.msg_notice (str "(* info wp_auto: *)")

(**
  Tries the given tactic and calls an info printer if it fails
*)
let tclTryDbg (debug_header_printer : unit -> unit) (tac: trace tactic): trace tactic =
  let new_tac =
    tac >>= fun trace ->
    if trace.log then
      begin
        debug_header_printer ();
        if trace.trace <> [] then
          begin
            pr_trace trace;
            Feedback.msg_notice @@ str "\nApplied lemmas:";
            pr_trace @@ keep_applied trace
          end;
      end;
    tclUNIT trace
  in
  let after =
    tac >>= fun trace ->
    if trace.log then pr_info_nop ();
    tclUNIT trace
  in
  tclTraceOrElse (tclPROGRESS new_tac) after

(**
  Creates a function that takes a hint database and returns a hint list
*)
let hintmap_of (env: Environ.env) (sigma: Evd.evar_map) (secvars: Id.Pred.t) (concl: Evd.econstr): hint_db -> FullHint.t list =
  let hdc = try Some (decompose_app_bound sigma concl) with Bound -> None in
  match hdc with
  | None -> Hint_db.map_none ~secvars
  | Some hdc ->
      if occur_existential sigma concl then (fun db ->
        match Hint_db.map_eauto env sigma ~secvars hdc concl db with
          | ModeMatch (_, l) -> l
          | ModeMismatch -> []
      )
      else Hint_db.map_auto env sigma ~secvars hdc concl

(**
  Returns a logged [intro] tactic
*)
let dbg_intro: Pp.t list -> trace tactic = tclLOG (fun _ _ -> (str "intro", str "")) (intro <*> tclUNIT no_trace)

(**
  Returns a logged [assumption] tactic
*)
let dbg_assumption: Pp.t list -> trace tactic = tclLOG (fun _ _ -> (str "assumption", str "")) (assumption <*> tclUNIT no_trace)

(**
  Returns a tactic that apply intro then try to solve the goal
*)
let intro_register (kont: hint_db -> trace tactic) (db: hint_db) (forbidden_tactics: Pp.t list): trace tactic =
  let nthDecl m gl =
    let hyps = Proofview.Goal.hyps gl in
    try
      List.nth hyps (m-1)
    with Failure _ -> CErrors.user_err Pp.(str "No such assumption.")
  in dbg_intro forbidden_tactics >>= fun new_trace ->
    TraceTactics.typedGoalEnter begin fun gl ->
      let extend_local_db decl db =
        let env = Goal.env gl in
        let sigma = Goal.sigma gl in
        push_resolve_hyp env sigma (Context.Named.Declaration.get_id decl) db
      in TraceTactics.typedGoalEnter @@ fun goal -> tclUNIT (nthDecl 1 goal) >>= (fun decl ->
        TraceTactics.typedThen
          (tclUNIT new_trace)
          (kont (extend_local_db decl db))
      )
    end

let rec trivial_fail_db (trace: trace) (db_list: hint_db list) (forbidden_tactics: Pp.t list) (local_db: hint_db): trace tactic =
  TraceTactics.typedIndependant @@
    tclTraceOrElse (dbg_assumption forbidden_tactics) @@
    tclTraceOrElse (intro_register (trivial_fail_db trace db_list forbidden_tactics) local_db forbidden_tactics) @@
    TraceTactics.typedGoalEnter begin fun gl ->
      let env = Goal.env gl in
      let sigma = Goal.sigma gl in
      let concl = Goal.concl gl in
      let secvars = compute_secvars gl in
      let hintmap = hintmap_of env sigma secvars concl in
      let hinttac = tac_of_hint trace db_list local_db concl forbidden_tactics in
      (local_db::db_list)
        |> List.map_append (fun db -> try hintmap db with Not_found -> [])
        |> List.filter_map begin fun h ->
            if Int.equal (FullHint.priority h) 0 then
              Some (Tacticals.tclCOMPLETE (hinttac h))
            else None
          end
        |> tclTraceFirst
    end

(**
  Returns a function that converts hints into tactics
*)
and tac_of_hint (trace: trace) (db_list: hint_db list) (local_db: hint_db) (concl: Evd.econstr) (forbidden_tactics: Pp.t list): FullHint.t -> trace tactic =
  let tactic = function
    | Res_pf h -> unify_resolve_nodelta h <*> tclUNIT @@ no_trace
    | ERes_pf _ -> TraceTactics.typedGoalEnter (fun gl ->
        let info = Exninfo.reify () in
        Tacticals.tclZEROMSG ~info (str "eres_pf"))
    | Give_exact h  -> exact h <*> tclUNIT @@ singleton_trace true (str "exact") (str "")
    | Res_pf_THEN_trivial_fail h ->
      tclTHEN
        (unify_resolve_nodelta h)
        (trivial_fail_db no_trace db_list forbidden_tactics local_db)
    | Unfold_nth c ->
      TraceTactics.typedGoalEnter begin fun gl ->
       if exists_evaluable_reference (Goal.env gl) c then
         Tacticals.tclPROGRESS (reduce (Genredexpr.Unfold [Locus.AllOccurrences,c]) Locusops.onConcl) <*>
         tclUNIT @@ singleton_trace true (str "unfold") (str "")
       else
         let info = Exninfo.reify () in
         Tacticals.tclFAIL ~info (str"Unbound reference")
       end
    | Extern (p, tacast) ->
      conclPattern concl p tacast <*> tclUNIT @@ singleton_trace true (str "") (str "extern")
  in
  let pr_hint (h: FullHint.t) (env: Environ.env) (sigma: Evd.evar_map): t * t =
    let origin = match FullHint.database h with
    | None -> mt ()
    | Some n -> str n
    in
    (Proofutils.pr_hint env sigma h, origin)
  in
  fun h -> tclLOG (pr_hint h) (FullHint.run h tactic) forbidden_tactics

(**
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal cannot contain evars
*)
let search (trace: trace) (max_depth: int) (lems: Tactypes.delayed_open_constr list) (db_list: hint_db list) (must_use_tactics: Pp.t list) (forbidden_tactics: Pp.t list): trace tactic =
  let make_local_db (gl: Goal.t): hint_db =
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    try make_local_hint_db env sigma false lems with _ -> make_local_hint_db env sigma false []
  in
  let rec inner_search (trace: trace) (n: int) (previous_envs: (EConstr.named_context * EConstr.constr * Evd.evar_map) list) (local_db: hint_db): trace tactic =
    if Int.equal n 0 then
      let info = Exninfo.reify () in
      tclZERO ~info (SearchBound no_trace)
    else
      begin
        tclTraceOrElse (dbg_assumption forbidden_tactics) @@
        tclTraceOrElse (intro_register (inner_search trace n previous_envs) local_db forbidden_tactics) @@
        TraceTactics.typedGoalEnter begin fun gl ->
          let env = Goal.env gl in
          let sigma = Goal.sigma gl in
          let concl = Goal.concl gl in
          let new_trace = incr_trace_depth trace in
          let secvars = compute_secvars gl in
          let hintmap = hintmap_of env sigma secvars  concl in
          let hinttac = tac_of_hint trace db_list local_db concl forbidden_tactics in
          (local_db::db_list)
            |> List.map_append (fun db -> try hintmap db with Not_found -> [])
            |> List.map
              begin fun h ->
                TraceTactics.typedThen
                  (hinttac h) @@
                  begin
                    TraceTactics.typedGoalEnter
                      begin fun goal ->
                        let local_db' = make_local_db goal in
                        if List.mem (Goal.hyps goal, Goal.concl goal, Goal.sigma goal) previous_envs
                          then tclZERO (SearchBound no_trace)
                          else inner_search new_trace (n-1) ((Goal.hyps goal, Goal.concl goal, Goal.sigma goal)::previous_envs) local_db'
                      end
                  end >>= fun trace ->
                  if n <> max_depth then tclUNIT trace else trace_check_used must_use_tactics trace
              end
            |> tclTraceFirst
        end
      end
  in
  TraceTactics.typedGoalEnter @@ fun goal ->
  let local_db = make_local_db goal in
  tclORELSE
    begin
      inner_search trace max_depth [] local_db
    end
    begin fun _ ->
      tclUNIT no_trace
    end

(**
  Generates the {! wp_auto} function
*)
let gen_wp_auto (log: bool) ?(n: int = 5) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list option) (must_use_tactics: Pp.t list) (forbidden_tactics: Pp.t list): trace tactic =
  TraceTactics.typedGoalEnter begin fun gl ->
    let db_list =
      match dbnames with
      | Some dbnames -> make_db_list dbnames
      | None -> current_pure_db ()
    in
    tclTryDbg pr_dbg_header @@ TraceTactics.typedThen (tclUNIT @@ new_trace log) @@ search no_trace n lems db_list must_use_tactics forbidden_tactics
  end

(**
  Waterproof auto

  This function is a rewrite around {! Auto.auto} with the same arguments to be able to retrieve which hints have been used in case of success.

  Returns a typed tactic containing the full trace
*)
let wp_auto (log: bool) (n: int) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list): trace tactic =
  gen_wp_auto log ~n lems (Some dbnames) [] []

(**
  Restricted Waterproof auto

  This function acts the same as {! wp_auto} but will fail if all proof found contain at least one must-use lemma that is unused or one hint that is in the [forbidden] list.
*)
let rwp_auto (log: bool) (n: int) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list) (must_use_tactics: Pp.t list) (forbidden_tactics: Pp.t list): trace tactic =
  gen_wp_auto log ~n lems (Some dbnames) must_use_tactics forbidden_tactics
