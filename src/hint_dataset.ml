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
open Summary

open Exceptions
open Hint_dataset_declarations
open Proofutils

(**
  Contains the hint dataset that is currently loaded
*)
let loaded_hint_dataset: string list ref = ref ~name:"loaded_hint_dataset" []

(**
  Dictionary with dataset names as keys and datasets as values
*)
let existing_datasets: hint_dataset StringMap.t ref = 
  ref ~name:"existing_datasets" @@ List.fold_left (fun dict (name, dataset) -> StringMap.add name dataset dict) StringMap.empty [("Empty", empty); ("Core", core); ("Algebra", algebra); ("Integers", integers); ("RealsAndIntegers", reals_and_integers); ("Sets", sets); ("Intuition", intuition); ("ClassicalEpsilon", classical_epsilon); ("FiniteSums", finite_sums)]

(**
  Adds a dataset to the currently loaded hint datasets
*)
let load_dataset (hint_dataset_name: string): unit =
  if StringMap.mem hint_dataset_name !existing_datasets then
    begin 
      if not @@ List.mem hint_dataset_name !loaded_hint_dataset
        then loaded_hint_dataset := hint_dataset_name::!loaded_hint_dataset
    end
  else
    throw (NonExistingDataset hint_dataset_name)

(**
  Removes a dataset to the currently loaded hint datasets
*)
let remove_dataset (hint_dataset_name: string): unit =
  loaded_hint_dataset := List.filter (fun dataset -> dataset <> hint_dataset_name) !loaded_hint_dataset

(**
  Clears all the currently loaded datasets
*)
let clear_dataset (): unit =
  loaded_hint_dataset := ["Empty"]

(**
  Creates a new empty dataset from a given name
*)
let create_new_dataset (dataset_name: string): unit =
  if StringMap.mem dataset_name !existing_datasets
    then throw (NonExistingDataset dataset_name) (* TODO *)
    else
      begin
        existing_datasets := StringMap.add dataset_name (new_dataset dataset_name) !existing_datasets
      end

(**
  Sets the databases of a given {! database_type} in a given dataset
*)
let populate_dataset (dataset_name: string) (database_type: database_type) (databases: string list): unit =
  existing_datasets := StringMap.update dataset_name (function
    | None -> throw (NonExistingDataset dataset_name)
    | Some dataset -> Some (set_databases dataset database_type databases)
  ) !existing_datasets

(**
  Converts a name into the corresponding hint dataset
*)
let dataset_of_name (name: string): hint_dataset = 
  try
    StringMap.find name !existing_datasets
  with Not_found -> throw (NonExistingDataset name)

(**
  Merges two lists without duplicates
*)
let rec merge (list1: 'a list) (list2: 'a list): 'a list = match list1 with
  | [] -> list2
  | x::p when List.mem x list2 -> merge p list2
  | x::p -> merge p (x::list2)

(**
  Returns the list of databases of the current loaded dataset for the given {! Hint_dataset_declarations.database_type}
*)
let get_current_databases (database_type: database_type): hint_db_name list =

  let datasets = List.map dataset_of_name !loaded_hint_dataset in
  List.fold_left (fun acc dataset -> merge acc (get_databases dataset database_type)) [] datasets
