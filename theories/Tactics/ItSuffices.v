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

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Util.Init.
Require Import Util.Goals.
Require Import Util.BySince.
Require Import Util.MessagesToUser.
Require Import Util.TypeCorrector.
Require Import Waterprove.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").

(**
  Custom version of the [enough] tactic that uses
  the waterproof automation system to prove that the proposed
  goal is enough to show the current goal.
  If successful, replaces current goal by proposed goal.

  We have added this to be able to use an enough tactic
  that doesn't throw a fatal error, which is useful
  in the expand framework.

  Arguments:
  - [new_goal]: proposed new goal.

  Throws:
  - [FailedToProve] if [rwaterprove] fails to prove that [new_goal]
    is enough to show current goal.
*)
Ltac2 wp_enough_base (new_goal : constr) :=
  let new_goal := correct_type_by_wrapping new_goal in
  enough $new_goal by (waterprove 5 true Main).

(** Attempts to prove that proposed goal is enough to show current goal.
  If succesful, replaces current goal by proposed goal. *)
Local Ltac2 wp_enough (new_goal : constr) :=
  let err_msg := concat_list
    [of_string "Could not verify that it suffices to show "; of_lconstr new_goal; of_string "."] in
  match Control.case (fun () => wp_enough_base new_goal) with
  | Val _ => ()
  | Err (FailedToProve _) => throw err_msg
  | Err exn => Control.zero exn
  end.


(** Attempts to prove that proposed goal is enough to show current goal,
  given an additional lemma that has to be used in said proof.
  If succesful, replaces current goal by proposed goal. *)
Local Ltac2 core_wp_enough_by (new_goal : constr) (xtr_lemmas : constr list) (xtr_dbs : hint_db_name list) :=
  let err_msg := concat_list
    [of_string "Could not verify that it suffices to show "; of_lconstr new_goal; of_string "."] in
  match Control.case (fun () =>
    let new_goal := correct_type_by_wrapping new_goal in
    enough $new_goal by
      (rwaterprove 5 true Main xtr_lemmas xtr_dbs))
  with
  | Val _ => ()
  | Err (FailedToProve _) => throw err_msg
  | Err exn => Control.zero exn (* includes FailedToUse error *)
  end.

(** Adaptation of [core_wp_enough_by] that turns the [FailedToUse] errors
  which might be thrown into user readable errors. *)
Local Ltac2 wp_enough_by (claim : constr) (xtr_lemmas : constr list) (xtr_dbs : hint_db_name list) :=
  wrapper_core_by_tactic (core_wp_enough_by claim) xtr_lemmas xtr_dbs.

(**
  Proves that proposed goal is enough to show current goal.

  Arguments:
  - [claim]: proposed goal.
  - [xtr_lemmas]: list of extra lemmas that can be used in the proof.
  - [xtr_dbs]: list of extra hint databases to use in the proof.

  Throws:
  - [FailedToProve] if [rwaterprove] fails to prove that [claim] is enough to show current goal using the specified lemmas and hint databases.
  - [FailedToUse] if [rwaterprove] fails to use a lemma in the proof while it should have used it.
*)
Ltac2 wp_enough_by_with_checks (claim : constr) (xtr_lemmas : constr list) (xtr_dbs : hint_db_name list) :=
  panic_if_goal_wrapped ();
  wp_enough_by claim xtr_lemmas xtr_dbs.

(** Adaptation of [core_wp_assert_by] that allows user to use mathematical statements themselves
  instead of references to them as extra information for the automation system.
  Uses the code in [Since.v]. *)
Local Ltac2 wp_enough_since (claim : constr) (xtr_claim : constr) :=
  since_framework (core_wp_enough_by claim) xtr_claim.

Local Ltac2 wp_enough_by_admit (claim : constr) :=
  enough $claim by admit;
  warn (concat_list [of_string "Please come back later to prove that";
    of_string " it suffices to show that ";
    of_lconstr claim]).

Ltac2 Notation "It" "suffices" "to" "show" _(opt("that")) statement(lconstr) :=
  panic_if_goal_wrapped ();
  wp_enough statement.

Ltac2 Notation "Since" xtr_claim(lconstr) "it" "suffices" "to" "show" _(opt("that")) statement(lconstr) :=
  panic_if_goal_wrapped ();
  wp_enough_since statement xtr_claim.

Ltac2 Notation "By" "magic" "it" "suffices" "to" "show" _(opt("that")) statement(lconstr) :=
  panic_if_goal_wrapped ();
  wp_enough_by_admit statement.
