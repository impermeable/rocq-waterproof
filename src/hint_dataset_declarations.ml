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

open Hints

open Exceptions

(**
  Interface to load and unload usual hint databases such as reals, integers, classical logic, ...
*)
type hint_dataset = {
  name: string; (** Dataset name *)
  main_databases: hint_db_name list; (** Databases that will be called to solve a goal *)
  decidability_databases: hint_db_name list; (** Databases that can be called to solve a goal with decidability properties *)
  shorten_databases: hint_db_name list; (** Databases that will be called to solve a goal faster than [positive_databases] *)
}

(**
  Type referencing all database lists that a {! hint_dataset} should contain
*)
type database_type = Main | Decidability | Shorten

(**
  Converts a string to a {! database_type}
*)
let database_type_of_string (database_type: string): database_type = match database_type with
  | "Main" -> Main
  | "Decidability" -> Decidability
  | "Shorten" -> Shorten
  | _ -> throw (NonExistingDataset "") (* TODO *)


(**
  Returns the name of the given [dataset]
*)
let name (dataset: hint_dataset): string = dataset.name

(**
  Returns the list of databases for the given {! database_type}
*)
let get_databases (dataset: hint_dataset) (databases: database_type): hint_db_name list = match databases with
  | Main -> dataset.main_databases
  | Decidability -> dataset.decidability_databases
  | Shorten -> dataset.shorten_databases

(**
  Create a new empty dataset with a given name
*)
let new_dataset (name: string): hint_dataset = {
  name;
  main_databases = [];
  decidability_databases = [];
  shorten_databases = []
}

(**
  Sets the databases of the given type for the given dataset
*)
let set_databases (dataset: hint_dataset) (database_type: database_type) (databases: string list): hint_dataset = match database_type with
  | Main -> { dataset with main_databases = databases }
  | Decidability -> { dataset with decidability_databases = databases }
  | Shorten -> { dataset with shorten_databases = databases }

let empty: hint_dataset = {
  name = "Empty";
  main_databases: hint_db_name list = ["nocore"];
  decidability_databases: hint_db_name list = ["nocore"];
  shorten_databases: hint_db_name list = ["nocore"];
}

let core: hint_dataset = {
  name = "Core";
  main_databases: hint_db_name list = ["core"];
  decidability_databases: hint_db_name list = ["nocore"];
  shorten_databases: hint_db_name list = ["core"];
}

let algebra: hint_dataset = {
  name = "Algebra";
  main_databases: hint_db_name list = ["wp_core"; "arith"; "zarith"; "wp_algebra"; "wp_integers"; "wp_negation_int"];
  decidability_databases: hint_db_name list = ["nocore"; "wp_decidability_classical"; "wp_decidability_nat"];
  shorten_databases: hint_db_name list = ["wp_core"; "wp_negation_int"];
}

let integers: hint_dataset = {
  name = "Integers";
  main_databases: hint_db_name list = ["arith"; "zarith"; "wp_core"; "wp_integers"; "wp_negation_int"];
  decidability_databases: hint_db_name list = ["nocore"; "wp_decidability_nat"];
  shorten_databases: hint_db_name list = ["wp_core"; "wp_negation_int"];
}

let reals_and_integers: hint_dataset = {
  name = "RealsAndIntegers";
  main_databases: hint_db_name list = ["arith"; "zarith"; "real"; "wp_core"; "wp_definitions"; "wp_alt_chars"; "wp_integers"; "wp_reals"; "wp_negation_reals"];
  decidability_databases: hint_db_name list = ["nocore"; "wp_decidability_nat"; "wp_decidability_integers"; "wp_decidability_reals"; "wp_decidability_classical"; "wp_decidability_constructive"];
  shorten_databases: hint_db_name list = ["wp_core"; "wp_definitions"; "wp_negation_reals"; "wp_alt_chars"];
}

let sets: hint_dataset = {
  name = "Sets";
  main_databases: hint_db_name list = ["arith"; "zarith"; "wp_core"; "wp_integers"; "wp_negation_int"; "wp_sets"];
  decidability_databases: hint_db_name list = ["nocore"; "wp_decidability_nat"];
  shorten_databases: hint_db_name list = ["wp_core"; "wp_negation_int"; "wp_sets"];
}

let intuition: hint_dataset = {
  name = "Intuition";
  main_databases: hint_db_name list = ["wp_intuition"];
  decidability_databases: hint_db_name list = [];
  shorten_databases: hint_db_name list = ["wp_intuition"];
}

let finite_sums: hint_dataset = {
  name = "FiniteSums";
  main_databases: hint_db_name list = ["wp_finite_sums"];
  decidability_databases: hint_db_name list = [];
  shorten_databases: hint_db_name list = ["wp_finite_sums"];
}

let classical_epsilon: hint_dataset = {
  name = "ClassicalEpsilon";
  main_databases: hint_db_name list = [];
  decidability_databases: hint_db_name list = ["nocore"; "wp_decidability_epsilon"];
  shorten_databases: hint_db_name list = [];
}
