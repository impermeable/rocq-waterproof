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

open Names
open Ltac2_plugin.Tac2entries

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


(** A type to represent the different unfold actions, and the data they need. *)
type unfold_action =
  | Unfold of string * GlobRef.t
  | Apply of string * EConstr.constr
  | Rewrite of string * EConstr.constr

(** A type that represents the datastructure that can be added
    to the unfold table. When it is added, it will be converted
    to an unfold action. *)
type unfold_entry =
  | Unfold_entry of string
  | Apply_entry of string * Constrexpr.constr_expr
  | Rewrite_entry of string * Constrexpr.constr_expr

module StringMap : Map.S with type key = string

val wp_unfold_map : GlobRef.t StringMap.t ref

val add_to_unfold_map : string list -> GlobRef.t -> unit

val register_unfold : string list -> Libnames.qualid -> notation_interpretation_data * notation_interpretation_data

val register_unfold_entry : GlobRef.t -> unfold_entry -> unit

val extract_def : string -> GlobRef.t option

val find_unfold_actions_by_ref : GlobRef.t -> unfold_action list

val find_unfold_actions_by_str : string -> unfold_action list

val get_all_references : unit -> GlobRef.t list
