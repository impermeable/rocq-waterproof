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

open CErrors
open Constr
open Equality
open Locus
open Names
open Pp
open Proofview
open Proofview.Notations
open Util

open Backtracking
open Proofutils

(* All the definitions below come from coq-core hidden library (i.e not visible in the API) *)

type raw_rew_rule = (Constr.t * bool) CAst.t

(** Rewriting rules *)
type rew_rule = {
  rew_id : KerName.t;
  rew_lemma : constr;
  rew_type: types;
  rew_pat: constr;
  rew_l2r: bool;
}

module HintIdent = struct
  type t = rew_rule

  let compare r1 r2 = KerName.compare r1.rew_id r2.rew_id
end

(**
  Representation/approximation of terms to use in the dnet:
    - no meta or evar (use ['a pattern] for that)
    - [Rel]s and [Sort]s are not taken into account (that's why we need a second pass of linear filterin on the results - it's not a perfect term indexing structure)
*)

module DTerm =
struct
  type 't t =
    | DRel
    | DSort
    | DRef    of GlobRef.t
    | DProd
    | DLet
    | DLambda
    | DApp
    | DCase   of case_info
    | DFix    of int array * int
    | DCoFix  of int
    | DInt    of Uint63.t
    | DFloat  of Float64.t
    | DString of Pstring.t
    | DArray

  let compare_ci ci1 ci2 =
    let c = Ind.CanOrd.compare ci1.ci_ind ci2.ci_ind in
    if c = 0 then
      let c = Int.compare ci1.ci_npar ci2.ci_npar in
      if c = 0 then
        let c = Array.compare Int.compare ci1.ci_cstr_ndecls ci2.ci_cstr_ndecls in
        if c = 0 then
          Array.compare Int.compare ci1.ci_cstr_nargs ci2.ci_cstr_nargs
        else c
      else c
    else c

  let compare t1 t2 = match t1, t2 with
    | DRel, DRel -> 0
    | DRel, _ -> -1 | _, DRel -> 1
    | DSort, DSort -> 0
    | DSort, _ -> -1 | _, DSort -> 1
    | DRef gr1, DRef gr2 -> GlobRef.CanOrd.compare gr1 gr2
    | DRef _, _ -> -1 | _, DRef _ -> 1
    | DProd, DProd -> 0
    | DProd, _ -> -1 | _, DProd -> 1
    | DLet, DLet -> 0
    | DLet, _ -> -1 | _, DLet -> 1
    | DLambda, DLambda
    | DApp, DApp -> 0
    | DLambda, _ -> -1 | _, DLambda -> 1
    | DApp, _ -> -1 | _, DApp -> 1
    | DCase ci1, DCase ci2 -> compare_ci ci1 ci2
    | DCase _, _ -> -1 | _, DCase _ -> 1
    | DFix (i1, j1), DFix (i2, j2) ->
      let c = Int.compare j1 j2 in
      if c = 0 then
        Array.compare Int.compare i1 i2
      else c
    | DFix _, _ -> -1 | _, DFix _ -> 1
    | DCoFix i1, DCoFix i2 -> Int.compare i1 i2
    | DCoFix _, _ -> -1 | _, DCoFix _ -> 1
    | DInt i1, DInt i2 -> Uint63.compare i1 i2
    | DInt _, _ -> -1 | _, DInt _ -> 1
    | DFloat f1, DFloat f2 -> Float64.total_compare f1 f2
    | DFloat _, _ -> -1 | _, DFloat _ -> 1
    | DString s1, DString s2 -> Pstring.compare s1 s2
    | DString _, _ -> -1 | _, DString _ -> 1
    | DArray, DArray -> 1
end

(**
  Terms discrimination nets

  Uses the general dnet datatype on DTerm.t (here you can restart reading)
*)
module HintDN :
sig
  type t
  type ident = HintIdent.t

  val empty : t

  (** [add c i dn] adds the binding [(c,i)] to [dn]. [c] can be a
     closed term or a pattern (with untyped Evars). No Metas accepted *)
  val add : Environ.env -> constr -> ident -> t -> t

  (** [find_all dn] returns all idents contained in dn *)
  val find_all : t -> ident list

end = struct
  module Ident = HintIdent
  module PTerm =
  struct
    type t = unit DTerm.t
    let compare = DTerm.compare
  end
  module TDnet = Dn.Make(PTerm)(Ident)

  open DTerm

  type t = TDnet.t

  type ident = HintIdent.t

  let pat_of_constr env c : (unit DTerm.t * Constr.t list) option =
    let open GlobRef in
    let rec pat_of_constr c = match Constr.kind c with
      | Rel _ -> Some (DRel, [])
      | Sort _ -> Some (DSort, [])
      | Var i -> Some (DRef (VarRef i), [])
      | Const (c,u) -> Some (DRef (ConstRef c), [])
      | Ind (i,u) -> Some (DRef (IndRef i), [])
      | Construct (c,u) -> Some (DRef (ConstructRef c), [])
      | Meta _ -> assert false
      | Evar (i,_) -> None
      | Case (ci,u1,pms1,(c1,_),_iv,c2,ca) -> Some (DCase(ci), [snd c1; c2] @ Array.map_to_list snd ca)
      | Fix ((ia,i),(_,ta,ca)) -> Some (DFix(ia,i), Array.to_list ta @ Array.to_list ca)
      | CoFix (i,(_,ta,ca)) -> Some (DCoFix(i), Array.to_list ta @ Array.to_list ca)
      | Cast (c,_,_) -> pat_of_constr c
      | Lambda (_,t,c) -> Some (DLambda, [t; c])
      | Prod (_, t, u) -> Some (DProd, [t; u])
      | LetIn (_, c, t, u) -> Some (DLet, [c; t; u])
      | App (f,ca) ->
        let len = Array.length ca in
        let a = ca.(len - 1) in
        let ca = Array.sub ca 0 (len - 1) in
        Some (DApp, [mkApp (f, ca); a])
        (* Same change as in the autorewrite library: the motivation there is:
           UnsafeMonomorphic is fine because the term will only be used
           by pat_of_constr which ignores universes *)
      | Proj (p, _, c) -> pat_of_constr @@ mkApp (UnsafeMonomorphic.mkConst @@ Environ.projection_repr_constant env (Projection.repr p), [|c|])
      | Int i -> Some (DInt i, [])
      | Float f -> Some (DFloat f, [])
      | String s -> Some (DString s, [])
      | Array (_u,t,def,ty) -> Some (DArray, Array.to_list t @ [def ; ty])
    in pat_of_constr c

  (* Basic primitives *)

  let empty = TDnet.empty

  let add env (c:constr) (id:Ident.t) (dn:t) =
    let (ctx, c) = Term.decompose_prod_decls c in
    let c = TDnet.pattern (fun p -> pat_of_constr env p) c in
    TDnet.add dn c id

  let find_all dn = TDnet.lookup dn (fun () -> Everything) ()
end

(** Type of rewrite databases *)
type rewrite_db = {
  rdb_hintdn : HintDN.t;
  rdb_order : int KerName.Map.t;
  rdb_maxuid : int;
}

type hypinfo = {
  hyp_ty : EConstr.types;
  hyp_pat : EConstr.constr;
}

(** Empty rewrite database *)
let empty_rewrite_db = {
  rdb_hintdn = HintDN.empty;
  rdb_order = KerName.Map.empty;
  rdb_maxuid = 0;
}

(*
  Returns a unique identifier at each call
*)
let fresh_key: unit -> KerName.t =
  let id = ref 0 in
  fun () ->
    let cur = incr id; !id in
    let lbl = Id.of_string ("_" ^ string_of_int cur) in
    let kn = Lib.make_kn lbl in
    let (mp, _) = KerName.repr kn in
    let lbl = Id.of_string_soft (Printf.sprintf "%s#%i"
      (ModPath.to_string mp) cur)
    in KerName.make mp lbl

let decompose_applied_relation (env: Environ.env) (sigma: Evd.evar_map) (c: constr) (ctype: Evd.econstr) (left2right: bool): hypinfo option =
  let find_rel ty =
    let sigma, ty = EClause.make_evar_clause env sigma ty in
    let (_, args) = EConstr.decompose_app sigma ty.EClause.cl_concl in
    let len = Array.length args in
    if 2 <= len then
      let c1 = args.(len - 2) in
      let c2 = args.(len - 1) in
      Some (if left2right then c1 else c2)
    else None
  in match find_rel ctype with
    | Some c -> Some { hyp_pat = c; hyp_ty = ctype }
    | None ->
        let ctx,t' = Reductionops.whd_decompose_prod_decls env sigma ctype in (* Search for underlying eq *)
        let ctype = EConstr.it_mkProd_or_LetIn t' ctx in
        match find_rel ctype with
        | Some c -> Some { hyp_pat = c; hyp_ty = ctype }
        | None -> None


(* All the definitions below are inspired by the coq-core hidden library (i.e not visible in the API) but modified for Waterproof *)
let add_rew_rules (rewrite_database: rewrite_db) (rew_rules: rew_rule list): rewrite_db =
  List.fold_left (fun accu r -> {
    rdb_hintdn = HintDN.add (Global.env ()) r.rew_pat r accu.rdb_hintdn;
    rdb_order = KerName.Map.add r.rew_id accu.rdb_maxuid accu.rdb_order;
    rdb_maxuid = accu.rdb_maxuid + 1;
  }) rewrite_database rew_rules


module RewriteDatabase: Mergeable with type elt = rewrite_db = struct
  type elt = rewrite_db

  let empty = empty_rewrite_db

  let merge rewrite_db1 rewrite_db2 = add_rew_rules rewrite_db1 (HintDN.find_all rewrite_db2.rdb_hintdn)
end

module RewriteDatabaseTactics = TypedTactics(RewriteDatabase)

let find_rewrites (rewrite_database: rewrite_db): rew_rule list =
  let sort r1 r2 = Int.compare (KerName.Map.find r2.rew_id rewrite_database.rdb_order) (KerName.Map.find r1.rew_id rewrite_database.rdb_order) in
  List.sort sort (HintDN.find_all rewrite_database.rdb_hintdn)

(** Applies all the rules of one hint rewrite database *)
let one_base (where: variable option) (tactic: trace tactic) (rewrite_database: rewrite_db): unit tactic =
  let rew_rules = find_rewrites rewrite_database in
  let rewrite (dir: bool) (c: constr) (tac: unit tactic): unit tactic =
    let c = (EConstr.of_constr c, Tactypes.NoBindings) in
    general_rewrite ~where ~l2r:dir AllOccurrences ~freeze:true ~dep:false ~with_evars:false ~tac:(tac, AllMatches) c
  in
  let try_rewrite (rule: rew_rule) (tac: unit tactic): unit tactic =
    Proofview.Goal.enter begin fun gl ->
      let c' = rule.rew_lemma in
      rewrite rule.rew_l2r c' tac
    end
  in
  let eval (rule: rew_rule) =
    Tacticals.tclREPEAT_MAIN (tclTHEN (try_rewrite rule (Proofview.tclUNIT())) (tclIGNORE tactic))
  in
  let rules = tclMAP_rev eval rew_rules in
  Tacticals.tclREPEAT_MAIN @@ Proofview.tclPROGRESS rules

(** The [autorewrite] tactic *)
let autorewrite (tac: trace tactic) (rewrite_database: rewrite_db): unit tactic =
  Tacticals.tclREPEAT_MAIN (
    Proofview.tclPROGRESS @@ one_base None tac rewrite_database
  )

let autorewrite_multi_in (idl: variable list) (tac: trace tactic) (rewrite_database: rewrite_db): unit tactic =
  Proofview.Goal.enter begin fun gl ->
    Tacticals.tclMAP (fun id ->
      Tacticals.tclREPEAT_MAIN (
        Proofview.tclPROGRESS @@
        one_base (Some id) tac rewrite_database
      )
    ) idl
  end

let try_do_hyps (treat_id: 'a -> variable) (l: 'a list): trace tactic -> rewrite_db -> unit tactic =
  autorewrite_multi_in (List.map treat_id l)

let gen_auto_multi_rewrite (tac: trace tactic) (cl: clause) (rewrite_tab: rewrite_db): unit tactic =
  let concl_tac = (if cl.concl_occs != NoOccurrences then autorewrite tac rewrite_tab else Proofview.tclUNIT ()) in
  if not @@ Locusops.is_all_occurrences cl.concl_occs && cl.concl_occs != NoOccurrences
    then Tacticals.tclZEROMSG ~info:(Exninfo.reify ()) (str"The \"at\" syntax isn't available yet for the autorewrite tactic.")
    else match cl.onhyps with
      | Some [] -> concl_tac
      | Some l -> Tacticals.tclTHENFIRST concl_tac (try_do_hyps (fun ((_,id),_) -> id) l tac rewrite_tab)
      | None ->
        let hyp_tac =
          Proofview.Goal.enter begin fun gl ->
            let ids = Tacmach.pf_ids_of_hyps gl in
            try_do_hyps (fun id -> id)  ids tac rewrite_tab
          end
        in Tacticals.tclTHENFIRST concl_tac hyp_tac

let find_applied_relation ?(loc: Loc.t option) (env: Environ.env) sigma c left2right =
  let ctype = Retyping.get_type_of env sigma (EConstr.of_constr c) in
  match decompose_applied_relation env sigma c ctype left2right with
    | Some c -> c
    | None ->
      user_err ?loc (
        str "The type " ++
        Printer.pr_econstr_env env sigma ctype ++
        str " of this term does not end with an applied relation."
      )

let fill_rewrite_tab (env: Environ.env) (sigma: Evd.evar_map) (rule : raw_rew_rule) (rewrite_database: rewrite_db): rewrite_db =
  let to_rew_rule ({CAst.loc;v=(c,b)}: raw_rew_rule): rew_rule =
    let info = find_applied_relation ?loc env sigma c b in
    let pat = EConstr.Unsafe.to_constr info.hyp_pat in
    let uid = fresh_key () in {
      rew_id = uid;
      rew_lemma = c;
      rew_type = EConstr.Unsafe.to_constr info.hyp_ty;
      rew_pat = pat;
      rew_l2r = b;
    }
  in
  add_rew_rules rewrite_database [to_rew_rule rule]

(** Prints the current rewrite hint database *)
let print_rewrite_hintdb (env: Environ.env) (sigma: Evd.evar_map) (rewrite_database: rewrite_db) =
  str "Local rewrite database" ++
  fnl () ++
  prlist_with_sep fnl (fun h ->
    str (if h.rew_l2r then "rewrite -> " else "rewrite <- ") ++
    Printer.pr_lconstr_env env sigma h.rew_lemma ++ str " of type " ++ Printer.pr_lconstr_env env sigma h.rew_type
  ) (find_rewrites rewrite_database)

(**
  Converts a given hypothesis into a raw rule than can be added to the hint rewrite database
*)
let to_raw_rew_rule (env: Environ.env) (sigma: Evd.evar_map) (hyp: Constrexpr.constr_expr): raw_rew_rule =
  let econstr, context = Constrintern.interp_constr env sigma hyp in
  let sigma = Evd.from_ustate context in
  let sigma = Evd.collapse_sort_variables ~only_above_prop:false sigma in
  let constr = EConstr.to_constr sigma econstr in
  let (univs, csts) = Evd.universe_context_set sigma in
  let univs = match UGraph.check_declared_universes (Environ.universes (Global.env ())) univs with
  | Ok () -> Univ.Level.Set.empty
  | Error undeclared -> undeclared
  in
  let () = Global.push_context_set (univs, csts) in
  CAst.make ?loc:(Constrexpr_ops.constr_loc hyp) (constr, true)

(**
  This function will add in the rewrite hint database "core" every hint possible created from the hypothesis
*)
let fill_local_rewrite_database (): rewrite_db tactic =
  RewriteDatabaseTactics.typedGoalEnter @@ fun goal ->
    let env = Goal.env goal in
    let sigma = Goal.sigma goal in

    let hyps = List.map (fun decl ->
      Constrexpr_ops.mkIdentC @@ Context.Named.Declaration.get_id decl
    ) (Goal.hyps goal) in

    let new_rules = List.map (to_raw_rew_rule env sigma) hyps in
    tclUNIT @@ List.fold_left (fun acc rule ->
      try
        fill_rewrite_tab env sigma rule acc
      with _ -> acc
    ) RewriteDatabase.empty new_rules

(**
  Waterproof autorewrite

  This tactic is a rewrite of the coq-core's [autorewrite] tactic that will only consider current hypothesis as rewrite hints.
*)
let wp_autorewrite ?(print_hints: bool = false) (log: bool) (tac: trace tactic): unit tactic =
  let clause = {onhyps = Some []; concl_occs = Locus.AllOccurrences} in
  fill_local_rewrite_database () >>= fun rewrite_db ->
    Goal.enter @@ begin fun goal ->
    let env = Goal.env goal in
    let sigma = Goal.sigma goal in
    if print_hints then Feedback.msg_notice @@ print_rewrite_hintdb env sigma rewrite_db;
    if log then Feedback.msg_notice @@ str "(* application of wp_autorewrite *)";
    Tacticals.tclREPEAT @@ tclPROGRESS @@ gen_auto_multi_rewrite tac clause rewrite_db
  end >>= fun _ -> tclUNIT ()
