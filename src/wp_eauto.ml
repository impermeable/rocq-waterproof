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
open Context.Named
open EConstr
open Hints
open Names
open Pp
open Proofview
open Proofview.Notations
open Tactics
open Termops
open Util

open Backtracking
open Proofutils
open Wp_auto

(* All the definitions below come from rocq-core hidden library (i.e not visible in the API) *)

let eauto_unif_flags: Unification.unify_flags = auto_flags_of_state TransparentState.full

let e_give_exact ?(flags: Unification.unify_flags = eauto_unif_flags) (c: types): unit tactic =
  Goal.enter begin fun gl ->
    let sigma, t1 = Tacmach.pf_type_of gl c in
    let t2 = Tacmach.pf_concl gl in
    if occur_existential sigma t1 || occur_existential sigma t2 then
      Tacticals.tclTHENLIST [
        Unsafe.tclEVARS sigma;
        Clenv.unify ~cv_pb:CUMUL ~flags t1;
        exact_no_check c
      ]
    else exact_check c
  end

let e_assumption: trace tactic =
  TraceTactics.typedGoalEnter begin fun gl ->
    let hyps = Goal.hyps gl in
    let sigma = Goal.sigma gl in
    let concl = Tacmach.pf_concl gl in
    if List.is_empty hyps then
      Tacticals.tclZEROMSG (str "No applicable tactic.")
    else
      let not_ground = occur_existential sigma concl in
      let map (decl: (_, types, _) Declaration.pt): trace tactic =
        let id = Declaration.get_id decl in
        let t = Declaration.get_type decl in
        begin
          if not_ground || occur_existential sigma t
            then Clenv.unify ~cv_pb:CUMUL ~flags:eauto_unif_flags t <*> exact_no_check (mkVar id)
            else exact_check (mkVar id)
        end <*> tclUNIT @@ singleton_trace true (str "eassumption") (str "")
      in
      tclTraceFirst (List.map map hyps)
  end

let unify_e_resolve (flags: Unification.unify_flags) (h: hint): unit tactic =
  Hints.hint_res_pf ~with_evars:true ~with_classes:true ~flags h

let e_exact (h: hint): unit tactic =
  Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let sigma, c = Hints.fresh_hint env sigma h in
    Unsafe.tclEVARS sigma <*> e_give_exact c
  end

(* All the definitions below are inspired by the rocq-core hidden library (i.e not visible in the API) but modified for Waterproof *)

(**
  Cost to solve a hint
*)
type cost = {
  cost_priority : int;
  cost_subgoals : int;
}

(**
  Type alias containing functions that will return a [Hints.hint_db]
*)
type delayed_db = Environ.env -> Evd.evar_map -> hint_db

(**
  State of the search
*)
type search_state = {
  depth: int; (** Depth remaining before failing *)
  tactics_resolution: (Proofview_monad.goal_with_state * delayed_db) list;
  trace: trace; (** Current trace *)
}

let search_tactics_factory (initial_state: search_state): (module Mergeable with type elt = search_state) = (
    module struct
      type elt = search_state
      let empty = initial_state
      let merge state1 state2 = { state1 with trace = merge_traces state1.trace state2.trace }
    end: Mergeable with type elt = search_state
  )

(**
  Creates an initial state
*)
let initial_state (log: bool) (evk: Proofview_monad.goal_with_state) (local_db: delayed_db) (n: int): search_state =
  {
    depth = n;
    tactics_resolution = [(evk, local_db)];
    trace = new_trace log
  }

(**
  Prints a debug header
*)
let pr_dbg_header () = Feedback.msg_notice (str "(* info wp_eauto: *)")

let tclTraceComplete (t: trace tactic): trace tactic =
  t >>= fun res ->
    (
      tclINDEPENDENT
        (let info = Exninfo.reify () in
        tclZERO ~info (SearchBound no_trace))
    ) <*>
    tclUNIT res

let rec e_trivial_fail_db (db_list: hint_db list) (local_db: hint_db) (forbidden_tactics: Pp.t list): trace tactic =
  let next = TraceTactics.typedGoalEnter begin fun gl ->
    let d = Declaration.get_id @@ Tacmach.pf_last_hyp gl in
    let local_db = push_resolve_hyp (Tacmach.pf_env gl) (Tacmach.project gl) d local_db in
    e_trivial_fail_db db_list local_db forbidden_tactics
  end in
  TraceTactics.typedGoalEnter begin fun gl ->
    let secvars = compute_secvars gl in
    let tacl =
      e_assumption ::
      (Tactics.intro <*> next) ::
      (e_trivial_resolve (Tacmach.pf_env gl) (Tacmach.project gl) db_list local_db secvars (Tacmach.pf_concl gl) forbidden_tactics)
    in
    tclTraceFirst (List.map tclTraceComplete tacl)
  end

and esearch_find (env: Environ.env) (sigma: Evd.evar_map) (db_list: hint_db list) (local_db: hint_db) (secvars: Id.Pred.t) (concl: types) (forbidden_tactics: Pp.t list): (trace tactic * cost * Pp.t) list =
  let hint_of_db: hint_db -> FullHint.t list = hintmap_of env sigma secvars concl in
  let flagged_hints: (Unification.unify_flags * FullHint.t) list =
    List.map_append (fun db ->
      let flags = auto_flags_of_state (Hint_db.transparent_state db) in
      List.map (fun x -> (flags, x)) (hint_of_db db)
    ) (local_db::db_list)
  in

  (* Returns a tactic, its priority (which is an approximation of the cost), and its representation from the current state and a [Hints.FullHint.t] *)
  let tac_of_hint ((state, hint): (Unification.unify_flags * FullHint.t)): trace tactic * cost * Pp.t =
    let priority = match FullHint.repr hint with
      | Unfold_nth _ -> 1
      | _ -> FullHint.priority hint
    in let tac: hint hint_ast -> trace tactic = function
      | Res_pf h -> unify_e_resolve state h <*> tclUNIT @@ no_trace
      | ERes_pf h -> unify_e_resolve state h <*> tclUNIT @@ no_trace
      | Give_exact h -> e_exact h <*> tclUNIT @@ singleton_trace true (str "exact") (str "")
      | Res_pf_THEN_trivial_fail h ->
        (unify_e_resolve state h) <*>
        (e_trivial_fail_db db_list local_db forbidden_tactics)
      | Unfold_nth c ->
        TraceTactics.typedGoalEnter begin fun gl ->
          if exists_evaluable_reference (Goal.env gl) c then
            Tacticals.tclPROGRESS (reduce (Genredexpr.Unfold [Locus.AllOccurrences, c]) Locusops.onConcl) <*>
            tclUNIT @@ singleton_trace true (str "unfold") (str "")
          else
            let info = Exninfo.reify () in
            Tacticals.tclFAIL ~info (str"Unbound reference")
          end
      | Extern (pat, tacast) -> conclPattern concl pat tacast <*> tclUNIT @@ singleton_trace true (str "") (str "extern")
    in

    let subgoals = match FullHint.subgoals hint with
      | Some subgoals -> subgoals
      | None -> priority
  in let cost = { cost_priority = priority; cost_subgoals = subgoals } in

    let pr_hint (h: FullHint.t) (env: Environ.env) (sigma: Evd.evar_map): t * t =
      let origin = match FullHint.database h with
      | None -> mt ()
      | Some n -> str n
      in
      (Proofutils.pr_hint env sigma h, origin)
    in
    (* We cannot determine statically the cost of subgoals of an Extern hint, so approximate it by the hint's priority. *)
    let tactic = tclLOG (pr_hint hint) (FullHint.run hint tac) forbidden_tactics in
    (tactic, cost, FullHint.print env sigma hint)
  in
  (List.map tac_of_hint flagged_hints)

and e_trivial_resolve (env: Environ.env) (sigma: Evd.evar_map) (db_list: hint_db list) (local_db: hint_db) (secvars: Id.Pred.t) (gl: types) (forbidden_tactics: Pp.t list): trace tactic list =
  let filter (tac, pr, _) = if pr.cost_priority = 0 then Some tac else None in
  try List.map_filter filter (esearch_find env sigma db_list local_db secvars gl forbidden_tactics)
  with Not_found -> []

(**
  The goal is solved if the cost of solving is null
*)
let is_solved (cost: cost): bool = cost.cost_subgoals = 0

(* Solved comes first *)
let solve_order (c1: cost) (c2: cost): int = match (is_solved c1, is_solved c2) with
  | (true, true) | (false, false) -> 0
  | (false, true) -> 1
  | (true, false) -> -1

(**
  Compare two states

  Ordering of states is lexicographic:
    1. tactics known to solve the goal
    2. priority
    3. number of generated goals
*)
let compare ((_, c1, _): (trace tactic * cost * Pp.t)) ((_, c2, _): (trace tactic * cost * Pp.t)) =
  let solve_ordering = solve_order c1 c2 in
  let priority_ordering = Int.compare c1.cost_priority c2.cost_priority in
  if solve_ordering != 0 then solve_ordering
  else if priority_ordering != 0 then priority_ordering
  else Int.compare c1.cost_subgoals c2.cost_subgoals

(**
  Returns the list of tactics that will be tried for the proof search

  It always begins with [assumption] and [intros] (not exactly them but equivalent with evar support), then uses the hint databases
*)
let branching (n: int) (delayed_database: delayed_db) (dblist: hint_db list) (local_lemmas: Tactypes.delayed_open_constr list) (forbidden_tactics: Pp.t list): (bool * delayed_db * trace tactic * Pp.t) list tactic =
  Goal.enter_one
    begin fun gl ->
      let env = Goal.env gl in
      let sigma = Goal.sigma gl in
      let concl = Goal.concl gl in
      let hyps = EConstr.named_context env in
      let db = delayed_database env sigma in
      let secvars = secvars_of_hyps hyps in

      (* Construction of tactics equivalent to [assumption] *)
      let assumption_tacs : (bool * delayed_db * trace tactic * Pp.t) list =

        (* Ensure that no goal is generated *)
        let mkdb (env: Environ.env) (sigma: Evd.evar_map): 'a = assert false in

        let map_assum (id: variable): (bool * delayed_db * trace tactic * Pp.t) =
          let hint =  str "exact" ++ str " " ++ Id.print id in
          (false, mkdb, tclLOG (fun _ _ -> (hint, str "")) (e_give_exact (mkVar id) <*> tclUNIT no_trace) forbidden_tactics, hint)
        in List.map map_assum (ids_of_named_context hyps)
      in

      (* Construction of tactic equivalent to [intros] *)
      let intro_tac: (bool * delayed_db * trace tactic * Pp.t) =
        let mkdb (env: Environ.env) (sigma: Evd.evar_map): hint_db =
          push_resolve_hyp env sigma (Declaration.get_id (List.hd (EConstr.named_context env))) db
        in (false, mkdb, tclLOG (fun _ _ -> (str "intro", str "")) (Tactics.intro <*> tclUNIT no_trace) forbidden_tactics, str "intro")
      in

      (* Construction of tactics derivated from hint databases *)
      let rec_tacs: (bool * delayed_db * trace tactic * Pp.t) list tactic =
        let mkdb (env: Environ.env) (sigma: Evd.evar_map): hint_db =
          let hyps' = EConstr.named_context env in
          if hyps' == hyps
            then db
            else make_local_hint_db env sigma ~ts:TransparentState.full true local_lemmas
        in try
          esearch_find env sigma dblist db secvars concl forbidden_tactics
            |> List.sort compare
            |> List.map (fun (tac, _, pp) -> (true, mkdb, tac, pp))
            |> tclUNIT
        with Not_found -> tclUNIT []
      in

      rec_tacs >>= fun rec_tacs ->
      tclUNIT (assumption_tacs @ intro_tac :: rec_tacs)
    end

(**
  Actual search function
*)
let resolve_esearch (max_depth: int) (dblist: hint_db list) (local_lemmas: Tactypes.delayed_open_constr list) (state: search_state) (must_use_tactics: Pp.t list) (forbidden_tactics: Pp.t list): search_state tactic =
  let rec explore (state: search_state) (previous_envs: (EConstr.named_context * EConstr.constr) list) =
    if state.depth = 0
      then tclZERO (SearchBound no_trace)
      else match state.tactics_resolution with
        | [] -> tclUNIT state
        | (gl, db) :: rest ->
          tclEVARMAP >>= fun sigma ->
          match Unsafe.undefined sigma [gl] with
            | [] -> explore { state with tactics_resolution = rest; trace = incr_trace_depth state.trace } previous_envs
            | gl :: _ ->
              Unsafe.tclSETGOALS [gl] <*>
              branching state.depth db dblist local_lemmas forbidden_tactics >>= fun tacs ->
              let cast ((isrec, mkdb, tac, pp): (bool * delayed_db * trace tactic * Pp.t)): search_state tactic =
                tclONCE tac >>= fun trace ->
                Unsafe.tclGETGOALS >>= fun lgls ->
                tclEVARMAP >>= fun sigma ->
                let join (gl: Proofview_monad.goal_with_state): (Proofview_monad.goal_with_state * delayed_db) = (gl, mkdb) in
                let depth =
                  if isrec && not @@ List.is_empty lgls
                    then pred state.depth
                    else state.depth
                in tclUNIT { depth; tactics_resolution = List.map join lgls @ rest; trace = merge_traces state.trace trace }
              in
              tacs
                |> List.map cast
                |> explore_many previous_envs
                >>= fun s ->
                if state.depth = max_depth
                  then trace_check_used must_use_tactics s.trace >>= fun trace -> tclUNIT s
                  else tclUNIT s

  and explore_many (previous_envs: (EConstr.named_context * EConstr.constr) list) (tactic_list: search_state tactic list): search_state tactic = match tactic_list with
    | [] -> tclZERO (SearchBound no_trace)
    | tac :: l ->
      tclORELSE
        (tac >>= fun state ->
          let module SearchState = (val (search_tactics_factory {state with tactics_resolution = []})) in
          let module StateTactics = TypedTactics(SearchState) in
          let search_goal_enter: (Goal.t -> search_state tactic) -> search_state tactic = StateTactics.typedGoalEnter in
          search_goal_enter @@ fun goal ->
          if List.mem (Goal.hyps goal, Goal.concl goal) previous_envs
            then tclZERO (SearchBound no_trace)
            else explore state @@ (Goal.hyps goal, Goal.concl goal)::previous_envs
        )

        (
          fun (e, _) -> match e with
            | SearchBound trace -> explore_many previous_envs l
            | _ -> explore_many previous_envs l
        )

  in explore state []

(**
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal can contain evars
*)
let esearch (log: bool) (depth: int) (lems: Tactypes.delayed_open_constr list) (db_list: hint_db list) (must_use_tactics: Pp.t list) (forbidden_tactics: Pp.t list): trace tactic =
  TraceTactics.typedGoalEnter begin fun gl ->
  let local_db env sigma = make_local_hint_db env sigma ~ts:TransparentState.full true lems in
  let tac (s: search_state): search_state tactic = resolve_esearch depth db_list lems s must_use_tactics forbidden_tactics in
  tclORELSE
    begin
      let evk = goal_with_state (Goal.goal gl) (Goal.state gl) in
      tac (initial_state log evk local_db depth) >>= fun s ->
      assert (List.is_empty s.tactics_resolution);
      Unsafe.tclSETGOALS [] <*> tclUNIT s.trace
    end
    begin fun (exn, info) -> match exn with
      | SearchBound trace -> tclUNIT trace
      | _ -> tclZERO ~info exn
    end
  end

(**
  Generates the {! wp_eauto} function
*)
let gen_wp_eauto (log: bool) ?(n: int = 5) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list option) (must_use_tactics: Pp.t list) (forbidden_tactics: Pp.t list): trace tactic =
    TraceTactics.typedGoalEnter begin fun gl ->
    let db_list =
      match dbnames with
      | Some dbnames -> make_db_list dbnames
      | None -> current_pure_db ()
    in
    tclTryDbg pr_dbg_header @@ TraceTactics.typedThen (tclUNIT @@ new_trace log) @@ esearch log n lems db_list must_use_tactics forbidden_tactics
  end

(**
  Waterproof eauto

  This function is a rewrite around {! Eauto.eauto} with the same arguments to be able to retrieve which hints have been used in case of success.

  The code structure has been rearranged to match the one of [wp_auto.wp_auto].
*)
let wp_eauto (log: bool) (n: int) (lems: Tactypes.delayed_open_constr list) (db_names: hint_db_name list): trace tactic =
  gen_wp_eauto log ~n lems (Some db_names) [] []

(**
  Restricted Waterproof eauto

  This function acts the same as {! wp_eauto} but will fail if all proof found contain at least one must-use lemma that is unused or one hint that is in the [forbidden] list.
*)
let rwp_eauto (log: bool) (n: int) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list) (must_use_tactics: Pp.t list) (forbidden_tactics: Pp.t list): trace tactic =
  gen_wp_eauto log ~n lems (Some dbnames) must_use_tactics forbidden_tactics
