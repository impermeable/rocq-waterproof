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
  Interface to load and unload usual hint databases such as reals, integers, classical logic, ...
*)
type hint_dataset

(**
  Type referencing all database lists that a {! hint_dataset} should contain
*)
type database_type = Main | Decidability | Shorten

(**
  Converts a string to a {! database_type}
*)
val database_type_of_string : string -> database_type

(**
  Returns the name of the given [dataset]
*)
val name : hint_dataset -> string

(**
  Returns the list of databases for the given {! database_type}
*)
val get_databases :
  hint_dataset ->
  database_type ->
  Hints.hint_db_name list

(**
  Create a new empty dataset with a given name
*)
val new_dataset : string -> hint_dataset

(**
  Sets the databases of the given type for the given dataset
*)
val set_databases :
  hint_dataset ->
  database_type ->
  string list ->
  hint_dataset

val empty : hint_dataset
val core : hint_dataset
val algebra : hint_dataset
val integers : hint_dataset
val reals_and_integers : hint_dataset
val finite_sums : hint_dataset
val sets : hint_dataset
val intuition: hint_dataset
val classical_epsilon : hint_dataset
