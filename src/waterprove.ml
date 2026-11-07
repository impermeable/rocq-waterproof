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

open EConstr
open Hints
open Proofview

open Hint_dataset
open Hint_dataset_declarations
open Wp_auto
open Wp_eauto
open Wp_rewrite

(**
  What should the depth of the automation in the help function be ?
*)
let help_automation_depth : int ref = Summary.ref ~name:"help_automation_depth" 2

(**
  Largest allowed depth for the automation in the help function
*)
let max_help_automation_depth : int = 5

(**
  Set the depth of the automation in the help function, checking that it is in range
*)
let set_help_automation_depth (depth : int) : unit =
  if depth < 1 || depth > max_help_automation_depth then
    CErrors.user_err Pp.(str "The depth of the help automation should be between 1 and "
      ++ int max_help_automation_depth ++ str ".")
  else
    help_automation_depth := depth

(**
  Retrieve the depth of the automation in the help function
*)
let get_help_automation_depth () : int =
  !help_automation_depth

(**
  Should the help function check whether the goal can be shown automatically ?
*)
let use_help_automation : bool ref = Summary.ref ~name:"use_help_automation" true

(**
  Is automation shield enabled ?
*)
let automation_shield: bool ref = Summary.ref ~name:"automation_shield" true

(**
  Do we want to debug the automation ?
*)
let automation_debug : bool ref = Summary.ref ~name:"automation_debug" false

(**
  Should rewrite hints be printed ?
*)
let print_rewrite_hints : bool ref = Summary.ref ~name:"print_rewrite_hints" false

(**
  Function that will actually call automation functions
*)
let automation_routine (depth: int) (lems: Tactypes.delayed_open_constr list) (databases: hint_db_name list): unit tactic =
  Tacticals.tclFIRST [
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_auto !automation_debug depth lems databases;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_eauto !automation_debug depth lems databases;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_autorewrite ~print_hints:(!print_rewrite_hints) !automation_debug @@ wp_auto !automation_debug depth lems databases;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_autorewrite ~print_hints:(!print_rewrite_hints) !automation_debug @@ wp_eauto !automation_debug depth lems databases
  ]

(**
  Same function as {! automation_routine} but with restricted version of automation functions
*)
let restricted_automation_routine (depth: int) (lems: Tactypes.delayed_open_constr list) (databases: hint_db_name list) (must_use: Pp.t list) (forbidden: Pp.t list): unit tactic =
  Tacticals.tclFIRST [
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ rwp_auto !automation_debug depth lems databases must_use forbidden;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ rwp_eauto !automation_debug depth lems databases must_use forbidden;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_autorewrite ~print_hints:(!print_rewrite_hints) !automation_debug @@ wp_auto !automation_debug depth lems databases;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_autorewrite ~print_hints:(!print_rewrite_hints) !automation_debug @@ wp_eauto !automation_debug depth lems databases
  ]

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
let waterprove (depth: int) ?(shield: bool = false) (lems: Tactypes.delayed_open_constr list)
  (dbs: hint_db_name list) (database_type: database_type): unit tactic =
  Proofview.Goal.enter @@ fun goal ->
    begin
      if shield && !automation_shield then
        automation_routine 3 lems (dbs @ (get_current_databases Shorten))
      else
        automation_routine depth lems (dbs @ get_current_databases database_type)
    end

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
let rwaterprove (depth: int) ?(shield: bool = false) (lems: Tactypes.delayed_open_constr list)
  (dbs : hint_db_name list) (database_type: database_type) (must_use: constr list) (forbidden: constr list): unit tactic =
  Proofview.Goal.enter @@ fun goal ->
    begin
      let env = Proofview.Goal.env goal in
      let sigma = Proofview.Goal.sigma goal in
      let must_use_tactics = List.map (Printer.pr_econstr_env env sigma) must_use in
      let forbidden_tactics = List.map (Printer.pr_econstr_env env sigma) forbidden in
      if shield && !automation_shield then
        restricted_automation_routine 3 lems (dbs @ (get_current_databases Shorten)) must_use_tactics forbidden_tactics
      else
        restricted_automation_routine depth lems (dbs @ (get_current_databases database_type)) must_use_tactics forbidden_tactics
      end
