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

(**
In this module we keep two tables:
- [wp_unfold_map] a map from strings to global references, that is used to keep track of the
introduced notations, and the global reference they are associated with
- [wp_unfold_tbl] a table from global references to unfold actions, that can later be used
  by the unfold framework. The unfold actions can be of three types:
    - unfold the definition associated to the global reference
    - apply a bi-implication
    - rewrite an equality
*)

open Ltac2_plugin.Tac2entries
open Ltac2_plugin.Tac2expr
open Names

module StringMap = Map.Make(String)

(** A type to represent the different unfold actions, a name for the action, and the data they need. *)
type unfold_action =
  | Unfold of string * GlobRef.t
  | Apply of string * EConstr.constr
  | Rewrite of string * EConstr.constr

(** The map that associate notation strings to references *)
  let wp_unfold_map = Summary.ref ~name:"wp_unfold_map" StringMap.empty

(** The table that associates global references to unfold actions *)
let wp_unfold_tbl : unfold_action list GlobRef.Map_env.t ref = Summary.ref ~name:"wp_unfold_tbl" GlobRef.Map_env.empty

(** The following constructions are necessary to ensure persistence of the tables.. *)

let cache_unfold_map (s, id) =
  wp_unfold_map := StringMap.add s id !wp_unfold_map

let declare_unfold_map =
  let open Libobject in
  declare_object
    {
      (default_object "WP_UNFOLD_MAP") with
      cache_function = cache_unfold_map;
      load_function = (fun _ -> cache_unfold_map);
      classify_function = (fun _ -> Keep);
    }

let cache_unfold_tbl (id, ua) =
  wp_unfold_tbl := GlobRef.Map_env.update id
      (function None -> Some [ua] | Some prev -> Some (ua::prev))
      !wp_unfold_tbl


let declare_unfold_tbl =
  let open Libobject in
  declare_object
    {
      (default_object "WP_UNFOLD_TBL") with
      cache_function = cache_unfold_tbl;
      load_function = (fun _ -> cache_unfold_tbl);
      classify_function = (fun _ -> Keep);
    }

let add_to_unfold_map (toks : string list) (id : GlobRef.t) : unit =
  let s = String.concat " " toks in
  (* add_leaf puts (s, id) into the .vo *)
  Lib.add_leaf (declare_unfold_map (s, id))

let add_to_unfold_tbl (id : GlobRef.t) (ua : unfold_action) : unit =
  (* Adding a copy here, because otherwise we seem to get strange behavior when
     one adds definitions later in a file: earlier in a file it will already use
     to try the new definition and failing because it is not in the context yet.
     TODO: check with an expert what is best practice here. *)
  Lib.add_leaf (declare_unfold_tbl (id, ua))

let extract_def (s : string) : GlobRef.t option =
  StringMap.find_opt s !wp_unfold_map

(**
    Registers a new unfold notation in the notation table.

    Arguments:
    - [toks]: the list of string tokens that should follow "Expand" in the notation
    - [id]: the qualid to associate the unfold action to

    Returns:
    - (the notation interpretation data created, a deprecated version of the notation data)
*)
let register_unfold (toks : string list) (id : Libnames.qualid) : notation_interpretation_data * notation_interpretation_data =
  let glob_ref = Nametab.locate id in
  let full_id = Libnames.qualid_of_path (Nametab.path_of_global glob_ref) in
  let sexpr_seq = List.map (fun s -> SexprStr (CAst.make s)) ("Expand"::toks) in
  let get_qualid () = Libnames.qualid_of_string "Unfold.wp_expand" in
  let get_ref () = CAst.make @@ CTacExt (Ltac2_plugin.Tac2quote.wit_reference, CAst.make (Ltac2_plugin.Tac2qexpr.QReference full_id)) in
  let rhs = CTacApp (CAst.make (CTacRef (RelId (get_qualid ()))), [get_ref ()]) in
  let sexpr_seq_old = List.map (fun s -> SexprStr (CAst.make s)) (["Expand"; "the"; "definition"; "of"] @ toks) in
  let get_qualid_old () = Libnames.qualid_of_string "Unfold.wp_expand_deprecated" in
  let rhs_old = CTacApp (CAst.make (CTacRef (RelId (get_qualid_old ()))), [get_ref ()]) in
  (register_notation [] sexpr_seq None (CAst.make rhs), register_notation [] sexpr_seq_old None (CAst.make rhs_old))

(** A type that represents the datastructure that can be added
    to the unfold table. When it is added, it will be converted
    to an unfold action.
*)
type unfold_entry =
  | Unfold_entry of string
  | Apply_entry of string * Constrexpr.constr_expr
  | Rewrite_entry of string * Constrexpr.constr_expr

(** Registers a new entry in the table that stores a list of
    unfold actions associated to a reference.

    In this step, the [Constrexpr.constr_expr] is interpreted
    into an [EConstr.constr] to be stored in the unfold table.

    Arguments:
    - [id]: the global reference to associate the unfold action to
    - [ue]: the unfold action to register
*)
let register_unfold_entry (id : GlobRef.t) (ue : unfold_entry) : unit =
  let f (e : Constrexpr.constr_expr) =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let (constr_e, _) = Constrintern.interp_constr env sigma e in
    constr_e in
  match ue with
  | Unfold_entry s -> add_to_unfold_tbl id (Unfold (s,  id))
  | Apply_entry (s, e) ->
      add_to_unfold_tbl id (Apply (s, f e))
  | Rewrite_entry (s, e) ->
      add_to_unfold_tbl id (Rewrite (s, f e))

let get_all_references () : GlobRef.t list =
 !wp_unfold_tbl |> GlobRef.Map_env.domain |> GlobRef.Set_env.elements

let find_unfold_actions_by_ref (r : GlobRef.t) : unfold_action list =
  Option.default [] (GlobRef.Map_env.find_opt r !wp_unfold_tbl)

let find_unfold_actions_by_str (s : string) : unfold_action list =
  match extract_def s with
  | Some r -> find_unfold_actions_by_ref r
  | None -> []
