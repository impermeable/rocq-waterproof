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
Require Import Ltac2.Option.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Tactics.Help.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Tactics.By.
Require Import Waterproof.Tactics.Unfold.
Open Scope subset_scope.

Waterproof Enable Hypothesis Help.
Waterproof Enable Redirect Feedback.

(** Test 0 : Suggest to follow advice in goal if goal is wrapped
  or [False] (i.e. prove contradiction). *)
Goal False.
  assert_feedback_with_string (fun () => Help) Info
"Follow the advice in the goal window.".
Abort.

(** Test 1 : Only suggest to follow advice in goal if goal is wrapped
  or [False] (i.e. prove contradiction). *)
Goal (forall n : nat, n = n) -> False.
  intros.
  assert_feedback_with_string (fun () => Help) Info
"Follow the advice in the goal window.".
Abort.

(** Test 2 : Suggest to solve directly if goal can be shown automatically. *)
Goal True.
  assert_feedback_with_strings (fun () => Help) Info
["The goal can be shown immediately.";
"Hint, replace with: We conclude that ...."].
Abort.

(** Test 3 : Only suggest to solve directly if goal can be shown automatically. *)
Goal (forall n : nat, n = n) -> True.
  intros.
  assert_feedback_with_strings (fun () => Help) Info
["The goal can be shown immediately.";
"Hint, replace with: We conclude that ...."].
Abort.

(** Test 4 : Report \forall hypotheses if available. *)
Goal (∀ n ∈ nat, n = n) -> (∀ m ∈ nat, m + 1 = m + 1) -> (0 = 1).
  intros.
  assert_feedback_with_strings (fun () => Help) Info
[
"You can use one of the ‘for all’-statements (∀):";
"    (∀ n ∈ nat, n = n)";
"    (∀ m ∈ nat, m + 1 = m + 1)";
"Hint, replace with: Use ... := ... in ...."].
Abort.

(** Test 5 : Report \exists hypotheses if available. *)
Goal (∃ n ∈ nat, n = n) -> (∃ m ∈ nat, m + 1 = m + 1) -> (0 = 1).
  intros.
  assert_feedback_with_strings (fun () => Help) Info
[
"You can use one of the ‘there exists’-statements (∃):";
"    (∃ n ∈ nat, n = n)";
"    (∃ m ∈ nat, m + 1 = m + 1)";
"Hint, replace with: Obtain ... according to ...."].
Abort.

(** Test 6 : Report \forall and \exists hypotheses if available. *)
Goal (∀ n ∈ nat, n = n) -> (∃ m ∈ nat, m = 0) -> (0 = 1).
  intros.
  assert_feedback_with_strings (fun () => Help) Info
["You can use one of the ‘for all’-statements (∀):";
"    (∀ n ∈ nat, n = n)";
"Hint, replace with: Use ... := ... in ....";
"You can use one of the ‘there exists’-statements (∃):";
"    (∃ m ∈ nat, m = 0)";
"Hint, replace with: Obtain ... according to ...."].
Abort.



(** Test advice how to use newly introduced statements. *)

Require Import Waterproof.Tactics.ItHolds.
Require Import Waterproof.Automation.
Waterproof Enable Automation RealsAndIntegers.

(** Test 7: It holds that, no label. *)
Goal False.
Proof.
  assert_feedback_with_strings
  (fun () => It holds that (∀ n ∈ nat, n = n)) Info
["To use (∀ n ∈ nat, n = n), consider:";
"Hint, insert: Use ... := ... in ...."].
Abort.

(** Test 8: It holds that, label. *)
Goal False.
Proof.
  assert_feedback_with_strings
  (fun () => It holds that ∀ n > 2, n = n as (i)) Info
["To use (∀ n > 2, n = n), consider:";
"Hint, insert: Use ... := ... in ...."].
Abort.

(** Test 9: By ... it holds that, no label. *)
Goal True -> False.
Proof.
  (** TODO: is this consistent with the statement
      without the by clause and with the since clause? *)
  intro i.
  By i it holds that (forall n : nat, True).
Abort.

(** Test 10: Since ... it holds that, no label. *)
Goal False.
Proof.
  assert_feedback_with_strings
  (fun () => Since (True) it holds that (∀ n ≥ 4, n = n))
  Info
["To use (∀ n ≥ 4, n = n), consider:";
"Hint, insert: Use ... := ... in ...."].
Abort.


Require Import Waterproof.Tactics.Assume.

(** Test 11: Assume that, no label. *)
Goal (∀ n ∈ nat, n = n) -> False.
Proof.
  assert_feedback_with_strings
  (fun () => Assume that (∀ n ∈ nat, n = n))
  Info
["To use (∀ n ∈ nat, n = n), consider:";
"Hint, insert: Use ... := ... in ...."].
Abort.

(** Test 12: Assume that, label. *)
Goal (∀ n > 3, n = n) -> False.
Proof.
  assert_feedback_with_strings
  (fun () => Assume that ∀ n > 3, n = n as (i))
  Info
["To use (∀ n > 3, n = n), consider:";
"Hint, insert: Use ... := ... in ...."].
Abort.

(** Test 13: Assume negation. *)
Goal not (∀ n ≥ 4, n = n).
Proof.
  assert_feedback_with_strings
  (fun () => Assume that ∀ n ≥ 4, n = n)
  Info
["To use (∀ n ≥ 4, n = n), consider:";
"Hint, insert: Use ... := ... in ...."].
Abort.


Require Import Waterproof.Tactics.Claims.

(** Test 14: We claim that, no label. *)
Goal False.
Proof.
  assert_feedback_with_strings
  (fun () => We claim that (forall n : nat, n = n))
  Info
["After proving (∀ n, n = n), consider:";
"Hint, insert: Use ... := ... in ...."].
Abort.

(** Test 15: Assume that, label. *)
Goal (forall n : nat, n = n) -> False.
Proof.
  assert_feedback_with_strings
  (fun () => We claim that (forall n : nat, n = n) as (i))
  Info
["After proving (∀ n, n = n), consider:";
"Hint, insert: Use ... := ... in ...."].
Abort.

Waterproof Disable Hypothesis Help.

(** Test 16: Test if no advice is indeed given if help is disabled. *)
Goal False.
Proof.
  assert_no_feedback
  (fun () => It holds that (forall n : nat, n = n))
  Info.
Abort.

(** Test 17: Help on a forall goal *)
Goal ∀ x ∈ nat, x = 0.
Proof.
assert_feedback_with_strings (fun () => Help) Info
["The goal is to show a 'for all'-statement (∀). Introduce an arbitrary variable in nat.";
 "Hint, replace with: Take ... ∈ ...."].
Abort.

(** Test 18: Help on a there-exists goal *)
Goal ∃ x > 3, x = 0.
Proof.
assert_feedback_with_strings (fun () => Help) Info
["The goal is to show a 'there exists'-statement (∃). Choose a specific variable strictly larger than 3.";
 "Hint, replace with: Choose ... := ...."].
Abort.

(** Test 19: Help on an assumption *)
Goal ∀ x > 3, x < 2 -> x > 6.
Proof.
intros x Hx.
assert_feedback_with_strings (fun () => Help) Info
[String.concat "" ["The goal is to show an implication (⇒). Assume the premise "; "(x < 2)."];
"Hint, replace with: Assume that ...."].
Abort.

(** Test 20: Help on forall with arbitrary predicate *)
Local Parameter B : nat -> Prop.

Goal ∀ x B, x < 2.
Proof.
assert_feedback_with_strings (fun () => Help) Info
["The goal is to show a 'for all'-statement (∀). Introduce an arbitrary variable that is (a/an) B.";
 "Hint, replace with: Take ... ...."].
Abort.

(** Test 21: Help on exists with arbitrary predicate *)
Goal ∃ x B, x < 2.
Proof.
assert_feedback_with_strings (fun () => Help) Info
["The goal is to show a 'there exists'-statement (∃). Choose a specific variable that is (a/an) B.";
 "Hint, replace with: Choose ... := ...."].
Abort.

(** Test 22: Help on expanding registered definitions *)
Definition foo := 37.

Waterproof Register Expand "foo";
  for foo;
  as "Definition foo".

Require Import Waterproof.Tactics.Conclusion.

Goal foo = 42.
Proof.
assert_feedback_with_strings (fun () => Help) Info
["You can try to expand definitions or use alternative characterizations:";
"Definition foo:";
"Hint, replace with: We need to show that 37 = 42."].
Abort.

(** Test 23: Combine expanding definitions with more hints *)
Goal (∀ n ∈ nat, n + 1 < 0) -> foo = 42.
Proof.
intro.
assert_feedback_with_strings (fun () => Help) Info
["You can try to expand definitions or use alternative characterizations:";
"Definition foo:";
"Hint, replace with: We need to show that 37 = 42.";
"You can use one of the ‘for all’-statements (∀):";
"    (∀ n ∈ nat, n + 1 < 0)";
"Hint, replace with: Use ... := ... in ...."].
Abort.

(** Test 24: Disable the automation in the help function *)
Waterproof Disable Help Automation.

Goal 0 = 0.
Proof.
assert_feedback_with_strings (fun () => Help) Info
["You can try to expand definitions or use alternative characterizations:"].
Abort.

Waterproof Enable Help Automation.

(** Test 25: The goal can be shown immediately after re-enabling the automation *)
Goal 0 = 0.
Proof.
assert_feedback_with_strings (fun () => Help) Info
["The goal can be shown immediately.";
"Hint, replace with: We conclude that ...."].
Abort.

(** Test 26: With a large enough automation depth, a chain of implications
    can be shown immediately. Every implication costs a step of the automation,
    unlike e.g. arithmetic, which a single hint (lia, congruence) can solve. *)
Waterproof Set Help Automation Depth 5.

Goal forall P Q R S : Prop, (P -> Q) -> (Q -> R) -> (R -> S) -> P -> S.
Proof.
intros P Q R S H1 H2 H3 p.
assert_feedback_with_strings (fun () => Help) Info
["The goal can be shown immediately.";
"Hint, replace with: We conclude that ...."].
Abort.

(** Test 27: With automation depth 1, the same chain of implications is not
    shown immediately. *)
Waterproof Set Help Automation Depth 1.

Goal forall P Q R S : Prop, (P -> Q) -> (Q -> R) -> (R -> S) -> P -> S.
Proof.
intros P Q R S H1 H2 H3 p.
assert_feedback_with_strings (fun () => Help) Info
["You can try to expand definitions or use alternative characterizations:"].
Abort.

(** Test 28: The automation depth should be between 1 and 5 *)
Fail Waterproof Set Help Automation Depth 0.
Fail Waterproof Set Help Automation Depth 6.

(* Reset to the default depth *)
Waterproof Set Help Automation Depth 2.
