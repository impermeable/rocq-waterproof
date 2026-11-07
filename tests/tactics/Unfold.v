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
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Redirect Feedback.
Waterproof Enable Redirect Errors.

Definition foo : nat := 0.

Waterproof Register Expand "foo";
  for foo;
  as "Definition of foo".

(* Tests general unfolding: *)

(* Test 1: unfold term in goal, and throws an error suggesting
  to remove the line after use. *)
Goal foo = 1.
Proof.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand foo)
"Remove this line in the final version of your proof.")
  Info
["Definition of foo:";
"Hint, replace with: We need to show that 0 = 1."].
Abort.

(* Test 2: unfold term in hypothese and goal, and throws an error suggesting
    to remove the line after use. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand foo)
"Remove this line in the final version of your proof.")
  Info
["Definition of foo:";
"Hint, insert: We need to show that 0 = 1.";
"Hint, insert: It holds that 0 = 0.";
"Hint, insert: It holds that 0 = 2."].
Abort.


(* Tests framework expand the definition. *)
Local Ltac2 unfold_foo (statement : constr) := eval unfold foo in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "foo2" x(opt(seq("in", constr))) :=
  wp_unfold unfold_foo (Some "foo2") true true x.

(* Test 6: unfold term in hypotheses and goal and throws an error suggesting
    to remove line after use. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand foo)
"Remove this line in the final version of your proof.")
  Info
["Definition of foo:";
"Hint, insert: We need to show that 0 = 1.";
"Hint, insert: It holds that 0 = 0.";
"Hint, insert: It holds that 0 = 2."].
Abort.

(* Test 7: fails to unfold term in statment without term. *)
Goal False.
Proof.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand foo)
"Remove this line in the final version of your proof.")
  Info
["'Definition of foo' cannot be used in any statement."].
Abort.

Local Parameter P Q R : Prop.
Local Parameter HPQ : P <-> Q.

Waterproof Register Expand "notation" "for" "P";
  for P ;
  as "Alternative characterization of P";
  by apply (HPQ).

(* Test 8: Use alternative characterization, with concept in conclusion,
but without having the automation able to prove the alternative
characterizations: then warnings should be thrown. *)
Goal R -> P.
Proof.
  intros.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand notation for P)
"Remove this line in the final version of your proof.")
  Warning
["The following suggestion will likely not work, (this is probably caused by a misalignment in the automation for unfolding statements. Please notify your teacher or the Waterproof developers):
It suffices to show that Q."].
assert_fails_with_string (fun () => It suffices to show that Q)
"Could not verify that it suffices to show Q.".
Abort.

(* Test 9: Use alternative characterization, with concept in assumption,
but without having the automation able to prove the alternative characterizations: then warnings should be thrown. *)

Goal P -> R.
Proof.
  intros.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand notation for P)
"Remove this line in the final version of your proof.")
  Warning
["The following suggestion will likely not work, (this is probably caused by a misalignment in the automation for unfolding statements. Please notify your teacher or the Waterproof developers):
It holds that Q."].
assert_fails_with_string (fun () => It holds that Q)
"Could not verify that Q.".
Abort.

Local Hint Resolve -> HPQ : core.
Local Hint Resolve <- HPQ : core.

(* Test 10: Use the [apply_in_constr] tactic for an alternative characterization, with concept in conclusion *)
Goal R -> P.
Proof.
  intros.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand notation for P)
"Remove this line in the final version of your proof.")
  Info
["Alternative characterization of P:";
"Hint, replace with: It suffices to show that Q."].
It suffices to show that Q.
Abort.

(* Test 11: Use the [apply_in_constr] tactic for an alternative characterization, with concept in assumption *)
Goal P -> R.
Proof.
  intros.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand notation for P)
"Remove this line in the final version of your proof.")
  Info
["Alternative characterization of P:";
"Hint, replace with: It holds that Q."].
It holds that Q.
Abort.

Local Parameter T : Prop.
Local Parameter HPR : P = R.
(* Test 12: Test for [tactic_in_constr] *)
Goal False.
Proof.
assert_constr_equal (tactic_in_constr constr:(HPR) constr:(P -> Q)) constr:(R -> Q).
Abort.

Waterproof Register Expand "characterization" "of" "P";
  for P ;
  as "Characterization of P";
  by rewrite HPR.

Local Hint Extern 1 => rewrite HPR : core.

(* Test 13: Test unfolding by rewriting *)

Goal T -> P.
Proof.
intros.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand characterization of P)
"Remove this line in the final version of your proof.")
  Info
["Characterization of P:";
"Hint, replace with: It suffices to show that R.";
"Alternative characterization of P:";
"Hint, replace with: It suffices to show that Q."].
It suffices to show that Q.
Abort.

From Stdlib Require Import Reals.Reals.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Libs.Analysis.SupAndInf.
Require Import Waterproof.Automation.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

Local Parameter A : subset R.

(* Test 14, test for infimum, as it is important that it works in practice. *)
Goal 4 is the infimum of A -> 3 is the infimum of A.
Proof.
intro H.
assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand infimum)
"Remove this line in the final version of your proof.")
  Info
["Definition infimum:";
"Hint, insert: We need to show that 3 is a _lower bound_ for A
                     ∧ (∀ l ∈ ℝ, l is a _lower bound_ for A ⇨ l ≤ 3).";
"Hint, insert: It holds that 4 is a _lower bound_ for A
              ∧ (∀ l ∈ ℝ, l is a _lower bound_ for A ⇨ l ≤ 4).";
"Alternative characterization infimum:";
"Hint, insert: It suffices to show that 3 is a _lower bound_ for A
                         ∧ (∀ ε > 0, ∃ a ∈ A, a < 3 + ε).";
"Hint, insert: It holds that 4 is a _lower bound_ for A ∧ (∀ ε > 0, ∃ a ∈ A, a < 4 + ε)."].
Abort.

(* Test 15, test for supremum, as it is important that it works in practice. *)
Goal 4 is the supremum of A -> 3 is the supremum of A.
Proof.
intro H.
assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand supremum)
"Remove this line in the final version of your proof.")
  Info
["Definition supremum:";
"Hint, insert: We need to show that 3 is an _upper bound_ for A
                     ∧ (∀ L ∈ ℝ, L is an _upper bound_ for A ⇨ 3 ≤ L).";
"Hint, insert: It holds that 4 is an _upper bound_ for A
              ∧ (∀ L ∈ ℝ, L is an _upper bound_ for A ⇨ 4 ≤ L).";
"Alternative characterization supremum:";
"Hint, insert: It suffices to show that 3 is an _upper bound_ for A
                         ∧ (∀ ε > 0, ∃ a ∈ A, 3 - ε < a).";
"Hint, insert: It holds that 4 is an _upper bound_ for A ∧ (∀ ε > 0, ∃ a ∈ A, 4 - ε < a)."].
Abort.

(* Test 15, use Expand All *)
Goal 4 is the supremum of A -> 3 is the infimum of A.
Proof.
intro H.
assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand All)
"Remove this line in the final version of your proof.")
  Info
[
"Definition supremum:";
"Hint, replace with: It holds that 4 is an _upper bound_ for A
              ∧ (∀ L ∈ ℝ, L is an _upper bound_ for A ⇨ 4 ≤ L).";
"Alternative characterization supremum:";
"Hint, replace with: It holds that 4 is an _upper bound_ for A ∧ (∀ ε > 0, ∃ a ∈ A, 4 - ε < a).";
"Definition infimum:";
"Hint, replace with: We need to show that 3 is a _lower bound_ for A
                     ∧ (∀ l ∈ ℝ, l is a _lower bound_ for A ⇨ l ≤ 3).";
"Alternative characterization infimum:";
"Hint, replace with: It suffices to show that 3 is a _lower bound_ for A
                         ∧ (∀ ε > 0, ∃ a ∈ A, a < 3 + ε)."
].
Abort.

Goal 4 is the supremum of [0, 4).

It suffices to show that (4 is an upper bound for [0,4))
  ∧ (∀ ε > 0, ∃ a ∈ [0, 4), 4 - ε < a).

We show both statements.
- We conclude that 4 is an upper bound for [0, 4).
- We need to show that
    ∀ ε > 0, ∃ a ∈ [0, 4), 4 - ε < a.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand All)
"Remove this line in the final version of your proof.")
  Info
[
"Alternative characterization supremum:"].
  Take ε > 0.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand All)
"Remove this line in the final version of your proof.")
  Warning
[
"The following suggestion will likely not work, (this is probably caused by a misalignment in the automation for unfolding statements. Please notify your teacher or the Waterproof developers):
It suffices to show that 
4 is the _supremum_ of [0, 4)."].
Abort.

Close Scope R_scope.


(* Test 16, expand a definition that has not been added to the framework *)

Open Scope nat_scope.

Definition my_nat : nat := 3.

Goal my_nat = 4.
Proof.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand my_nat)
"Remove this line in the final version of your proof.")
  Info
["Definition my_nat:";
"Hint, replace with: We need to show that 3 = 4."].
Abort.

(* Test 17, deprecated notation *)
Goal my_nat = 4.
Proof.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of my_nat)
"Remove this line in the final version of your proof.")
  Info
["Definition my_nat:";
"Hint, replace with: We need to show that 3 = 4."].
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of my_nat)
"Remove this line in the final version of your proof.")
  Warning
["Warning: The notation 'Expand the definition of' is deprecated. Please use 'Expand' instead."].
Abort.

Definition my_nat_2 : nat := 3.

Waterproof Register Expand "my_nat_2";
  for my_nat_2;
  as "Definition my_nat_2".

(* Test 17, deprecated notation with framework *)
Goal my_nat_2 = 4.
Proof.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of my_nat_2)
"Remove this line in the final version of your proof.")
  Info
["Definition my_nat_2:";
"Hint, replace with: We need to show that 3 = 4."].
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of my_nat)
"Remove this line in the final version of your proof.")
  Warning
["Warning: The notation 'Expand the definition of' is deprecated. Please use 'Expand' instead."].
Abort.

Close Scope nat_scope.

(** Test 18 *)

Local Parameter HypForApplyTest : P -> True -> True -> Q.

Goal Q.
Proof.
assert True by trivial.
let x := apply_in_constr constr:(HypForApplyTest) (Control.goal()) in
  assert_constr_equal x constr:(P).
Abort.
