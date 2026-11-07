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
  Set the depth of the automation in the help function

  Raises a user error if the depth is not between 1 and 5.
*)
val set_help_automation_depth : int -> unit

(**
  Retrieve the depth of the automation in the help function
*)
val get_help_automation_depth : unit -> int

(**
  Should the help function check whether the goal can be shown automatically ?
*)
val use_help_automation : bool ref

(**
  Is automation shield enabled ?
*)
val automation_shield : bool ref

(**
  Do we want to debug the automation ?
*)
val automation_debug : bool ref

(**
  Should rewrite hints be printed ?
*)
val print_rewrite_hints: bool ref

(**
  Waterprove

  This function is the main automatic solver of rocq-waterproof.

  The databases used for the proof search are the one declared in the current imported dataset (see {! Hint_dataset.loaded_hint_dataset}).

  The forbidden patterns are defined in {! is_forbidden}.

  Arguments:
    - [depth] ([int]): max depth of the proof search
    - [shield] ([bool]): if set to [true], will stop the proof search if a forbidden pattern is found
    - [lems] ([Tactypes.delayed_open_constr list]): additional lemmas that are given to solve the proof
    - [dbs] ([hint_db_name list]): list of additional hint databases to use
    - [database_type] ([Hint_dataset_declarations]): type of databases that will be use as hint databases
*)
val waterprove :
  int ->
  ?shield:bool ->
  Tactypes.delayed_open_constr list ->
  Hints.hint_db_name list ->
  Hint_dataset_declarations.database_type ->
  unit Proofview.tactic

(**
  Restricted Waterprove

  This function is similar to {! waterprove} but use {! wp_auto.rwp_auto} and {! wp_eauto.rwp_eauto} instead of {! wp_auto.wp_auto} and {! wp_eauto.wp_eauto}.

  Arguments:
    - [depth] ([int]): max depth of the proof search
    - [shield] ([bool]): if set to [true], will stop the proof search if a forbidden pattern is found
    - [lems] ([Tactypes.delayed_open_constr list]): additional lemmas that are given to solve the proof
    - [dbs] ([hint_db_name list]): list of additional hint databases to use
    - [database_type] ([Hint_dataset_declarations]): type of databases that will be use as hint databases
    - [must_use] ([string list]): list of hints that have to be used during the automatic solving
    - [forbidden] ([string list]): list of hints that must not be used during the automatic solving
*)
val rwaterprove :
  int ->
  ?shield:bool ->
  Tactypes.delayed_open_constr list ->
  Hints.hint_db_name list ->
  Hint_dataset_declarations.database_type ->
  Evd.econstr list ->
  Evd.econstr list ->
  unit Proofview.tactic
