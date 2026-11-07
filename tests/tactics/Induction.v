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

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.
Require Import Waterproof.Util.MessagesToUser.

Waterproof Enable Redirect Feedback.

(** Test 0: This should work fine *)
Goal forall n : nat, (n = n).
Proof.
    We use induction on n.
    - Fail We first show the base case 2 = 2.
      We first show the base case 0 = 0.
      Fail We first show the base case 1 = 1.
      reflexivity.
    - We now show the induction step.
      Fail We now show the induction step.
      intros n IHn.
      reflexivity.
Qed.

(** Test 1: This should work fine *)
Goal (0 = 0) -> forall n : nat, (n = n).
Proof.
    intro n.
    assert_feedback_with_string
    (fun () => We use induction on k) Warning
    "Expected variable name n0 instead of k.".
    - Fail We first show the base case 2 = 2.
      We first show the base case  0 = 0.
      Fail We first show the base case 1 = 1.
      reflexivity.
    - We now show the induction step.
      Fail We now show the induction step.
      intros k IHk.
      reflexivity.
Qed.

(* Test 2: throws error if variable name is 'Qed'
    (quick fix for Waterproof editor / Rocq lsp)  *)
Goal forall n : nat, (n = n).
Proof.
    Fail We use induction on Qed.
Abort.

Require Import Waterproof.Notations.Sets.
Open Scope subset_scope.

(* Test 3 : Induction on a variable quantified by
  [∀ x ∈ nat, ...], rather than [∀ x : nat, ...] --
  Case where variable is not introduced yet *)

Goal ∀ n ∈ nat, n >= 0.
Proof.
We use induction on n.
* We first show the base case 0 >= 0.
  We conclude that 0 >= 0.
* We now show the induction step.
  Take n ∈ nat.
  Assume that n >= 0.
  We need to show that (n + 1 >= 0).
Abort.

(* Test 4: Induction on a variable quantified by
  [∀ x ∈ nat, ...], rather than [∀ x : nat, ...] --
  Case where variable is already introduced  with
  [Take ... ∈ ...] statement *)

Goal ∀ n ∈ nat, n >= 0.
Proof.
Take n ∈ nat.
induction n.
* change (0 >= 0).
  We conclude that (0 >= 0).
* change (S n >= 0).
Abort.

(* Test 5: Induction on a variable quantified by
  [∀ x ∈ nat, ...], rather than [∀ x : nat, ...] --
  Case where variable is already introduced,
  with [Take .. : ...] statement *)

Goal ∀ n ∈ nat, n >= 0.
Proof.
Take n : nat.
induction n.
* change (0 ∈ nat -> 0 >= 0).
  Control.shelve ().
* change (S n ∈ nat -> S n >= 0).
Abort.

(* Test 6: test notation in wrapper *)
Goal ∀ n ∈ nat, n >= 0.
Proof.
We use induction on n.
* let s := Message.to_string (Message.of_constr (Control.goal ())) in
  assert_string_equal s 
 "(Add the following line to the proof:
 
 - We first show the base case 0 >= 0.)".
  Control.shelve ().
* let s := Message.to_string (Message.of_constr (Control.goal ())) in
  assert_string_equal s 
 "(Add the following line to the proof:
 
 We now show the induction step.)".
Abort.
