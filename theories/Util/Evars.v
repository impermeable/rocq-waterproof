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

Require Export Ltac2.Ltac2.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Notations.Common.

Ltac2 @ external refine_goal_with_evar : string -> unit := "rocq-runtime.plugins.rocq-waterproof" "refine_goal_with_evar_external".

Ltac2 @ external blank_evars_in_term : constr -> evar list := "rocq-runtime.plugins.rocq-waterproof" "blank_evars_in_term_external".

Ltac2 rename_blank_evars_in_term (base_name : string) (x : constr) :=
  let evars := blank_evars_in_term x in
  let m := List.length evars in
  List.iter (fun ev => Control.new_goal ev) (evars);
  Control.focus 2 (Int.add m 1) (fun () =>
    ltac1:(refine (identity_seal _));
    refine_goal_with_evar base_name; Control.shelve()).
