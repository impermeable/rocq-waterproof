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

From Stdlib Require Import Rbase.
From Stdlib Require Import Qreals.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import SeqSeries.
From Stdlib Require Import Rtrigo.
From Stdlib Require Import Ranalysis.
From Stdlib Require Import Integration.
From Stdlib Require Import Lra.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Redirect Feedback.

(** Test 0: works with existence statement*)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro H.
  Obtain such an n.
Abort.

(** Test 1: works with sigma type *)
Goal {n : nat | (n + 1 = n)%nat} -> False.
Proof.
  intro H.
  Obtain such an n.
Abort.

(** Test 2: Fails with other type. *)
Goal (exists n : nat, n + 1 = n)%nat -> (0 = 0) -> False.
Proof.
  intros H1 H2.
  Fail Obtain such an n.
Abort.

(** Test 3: Fails when variable name is already in use. *)
Goal forall m : nat, (exists n : nat, n + 1 = m)%nat -> False.
Proof.
  intros m H.
  Fail Obtain such an m.
Abort.

(** Test 4: existence statement is replaced by copy with the same label. *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Obtain such an n. (* check for yourself! *)
Abort.


(** Test 5: whether original hypothesis is destructed, so if the goal depends on the
      specific term of the sigma type, the goal changes as well.
      As one would expect when using 'destruct .. as [.. ..]'. *)
Goal forall p : {n : nat | (n + 1 = n)%nat}, (proj1_sig p = 0)%nat.
Proof.
  intro p.
  Obtain such an n.
  We need to show that (n = 0)%nat.
  assert_goal_is constr:((n = 0)%nat).
Abort.

(** Test 6: works with specifying statement.  *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Obtain n according to (i).
Abort.

(** Test 7: fails if specified statement does not exist.  *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Fail Obtain n according to (ii).
Abort.


(** Test 8: more advanced use of the [Obtain...such that...] in the context of limits of sequences *)
Local Open Scope R_scope.

Definition evt_eq_sequences (a b : nat -> R) := (exists k : nat, forall n : nat, (n >= k)%nat -> a n = b n).

Goal forall (a b : nat -> R) (l : R), evt_eq_sequences a b -> (Un_cv a l) -> (Un_cv b l).
Proof.
    intros.
    intro.
    intro.
    pose (H0 eps H1).
    Obtain such an N.
Abort.


(** Test 9: throws error if variable name is 'Qed'
    (quick fix for Waterproof editor / Rocq lsp)  *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Fail Obtain such Qed.
Abort.

(** Test 10: obtain multiple variables *)
Goal (exists n m : nat, n + 1 = m)%nat -> True.
Proof.
  intro H.
  Obtain n, m according to (H).
Abort.

(** Test 11: obtain multiple variables *)
Goal (exists n m k l : nat, n + k + 1 = l + m)%nat -> True.
Proof.
  intro H.
  Obtain such n, m, m0, l.
Abort.

(** TODO: we should actually test for warnings below,
    once the branch on testing warnings and errors is merged. *)

(** Test 12 : obtain but with a wrong variable name *)
Goal (exists n : nat, n = 0)%nat -> True.
Proof.
  intro H.
  assert_feedback_with_string (fun () => Obtain such an m) Warning
"Expected variable name n instead of m.".
Abort.

(** Test 13: obtain with multiple wrong variable names *)
Goal (exists n m: nat, n = m)%nat -> True.
Proof.
  intro H.
  assert_feedback_with_strings (fun () => Obtain such k, l) Warning
["Expected variable name n instead of k.";
"Expected variable name m instead of l."].
Abort.

(** Test 14 : obtain but with a wrong variabl ename, later
  in the string *)
Goal (exists n m k l : nat, n + k + 1 = l + m)%nat -> True.
Proof.
  intro H.
  assert_feedback_with_strings (fun () => Obtain such an n, k) Warning
["Expected variable name m instead of k."].
Abort.

(** Test 15 : obtain when the variable has been visibly renamed *)
Goal (exists n : nat, n = 0)%nat -> True.
Proof.
  intro H.
  set (n := 3).
  assert_no_feedback (fun () => Obtain n0 according to (H)) Warning.
Abort.

(** Test 16: obtain when wrongly using a previous variable *)
Goal (exists n m : nat, n = m)%nat -> True.
Proof.
  intro H.
  assert_feedback_with_strings (fun () => Obtain such m, m0) Warning
["Expected variable name n instead of m."].
Abort.

(** Test 17 : Check that intermediate hypotheses are deleted *)
Goal (exists n m k l : nat, n + k + 1 = l + m)%nat -> True.
Proof.
  intro H.
  Obtain such n, m, k, l.
  Fail Check _H0.
Abort.

Waterproof Enable Redirect Errors.

(** Test 19: Try to obtain too many variables *)
Goal (exists n m : nat, n = m)%nat -> True.
Proof.
  intro H.
  assert_fails_with_string (fun () => Obtain such n, m, k)
"Couldn't obtain k.
There aren't enough variables to obtain.".
Abort.

(** Test 20: Test that the correct variable has been renamed *)
Goal (exists n : nat, n = 0)%nat -> True.
Proof.
  intro H.
  Obtain such an n.
  assert (n = 0)%nat by exact _H.
  assert (exists n0 : nat, n0 = 0)%nat by exact H.
Abort.

(** Test 21: The indicated statement is not a "there exists..." statement*)
Goal (forall n : nat, n = 0)%nat -> True.
  intro H.
  assert_fails_with_string (fun () => Obtain n according to (H))
"Can only obtain variables from 'there exists...' statements.".
Abort.

(** TODO: we should actually test for warnings below,
    once the branch on testing warnings and errors is merged. *)

(** Test 12 : obtain but with a wrong variable name *)
Goal (exists n : nat, n = 0)%nat -> True.
Proof.
  intro H.
  assert_feedback_with_string (fun () => Obtain such an m) Warning
"Expected variable name n instead of m.".
Abort.

(** Test 13: obtain with multiple wrong variable names *)
Goal (exists n m: nat, n = m)%nat -> True.
Proof.
  intro H.
  assert_feedback_with_strings (fun () => Obtain such k, l) Warning
["Expected variable name n instead of k.";
"Expected variable name m instead of l."].
Abort.

(** Test 14 : obtain but with a wrong variabl ename, later
  in the string *)
Goal (exists n m k l : nat, n + k + 1 = l + m)%nat -> True.
Proof.
  intro H.
  assert_feedback_with_strings (fun () => Obtain such an n, k) Warning
["Expected variable name m instead of k."].
Abort.

(** Test 15 : obtain when the variable has been visibly renamed *)
Goal (exists n : nat, n = 0)%nat -> True.
Proof.
  intro H.
  set (n := 3).
  assert_no_feedback (fun () => Obtain n0 according to (H)) Warning.
Abort.

(** Test 16: obtain when wrongly using a previous variable *)
Goal (exists n m : nat, n = m)%nat -> True.
Proof.
  intro H.
  assert_feedback_with_strings (fun () => Obtain such m, m0) Warning
["Expected variable name n instead of m."].
Abort.

(** Test 17 : Check that intermediate hypotheses are deleted *)
Goal (exists n m k l : nat, n + k + 1 = l + m)%nat -> True.
Proof.
  intro H.
  Obtain such n, m, k, l.
  Fail Check _H0.
Abort.

Waterproof Enable Redirect Errors.

(** Test 19: Try to obtain too many variables *)
Goal (exists n m : nat, n = m)%nat -> True.
Proof.
  intro H.
  assert_fails_with_string (fun () => Obtain such n, m, k)
"Couldn't obtain k.
There aren't enough variables to obtain.".
Abort.

(** Test 20: Test that the correct variable has been renamed *)
Goal (exists n : nat, n = 0)%nat -> True.
Proof.
  intro H.
  Obtain such an n.
  assert (n = 0)%nat by exact _H.
  assert (exists n0 : nat, n0 = 0)%nat by exact H.
Abort.

(** Test 21: The indicated statement is not a "there exists..." statement*)
Goal (forall n : nat, n = 0)%nat -> True.
  intro H.
  assert_fails_with_string (fun () => Obtain n according to (H))
"Can only obtain variables from 'there exists...' statements.".
Abort.

Require Import Waterproof.Notations.Sets.

(** Test 22 : Use existence statements in sets *)
Close Scope R_scope.
Open Scope nat_scope.
Local Parameter A : nat -> Prop.
Definition B := as_subset _ A.

Open Scope subset_scope.

Goal (∃ n ∈ B, n = 0) -> True.
Proof.
  intro H.
  Obtain such an n.
  assert (n ∈ B) by assumption.
  assert (n = 0) by assumption.
Abort.

(** Test 23 : Use multiple existence statements in sets *)

Goal (exists n : nat, n ∈ B /\ exists m : nat, m ∈ B /\ n = m) -> True.
Proof.
  intro H.
  Obtain such an n, m.
  assert (n ∈ B) by assumption.
  assert (m ∈ B) by assumption.
  assert (n = m) by assumption.
Abort.

(** Test 24 : Obtain from a full set *)
Goal (∃ n ∈ nat, n = 0) -> True.
Proof.
  intro H.
  Obtain such an n.
Abort.

(** Test 25 : Obtain from a set by reference *)
Goal (∃ n ∈ B, n = 0) -> True.
Proof.
  intro H.
  Obtain n according to (H).
  assert (n ∈ B) by assumption.
Abort.

(** Test 26 : Obtain from a full set by reference *)
Goal (∃ n ∈ nat, n = 0) -> True.
Proof.
  intro H.
  Obtain n according to (H).
Abort.

(** Test 27 : Check that the type of the variable is simplified after using obtain *)
Goal (∃ n ∈ nat, n = 0) -> True.
Proof.
  intro H.
  Obtain such an n.
  let n_hyp := Control.hyp @n in
  assert_is_true (Constr.equal (Constr.type n_hyp) constr:(nat)).
Abort.
