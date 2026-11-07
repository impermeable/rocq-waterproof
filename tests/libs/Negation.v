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
From Stdlib Require Import Reals.Reals.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Libs.Negation.

(** Test 0: large example from real analysis.*)
Open Scope R_scope.
Definition Rdist (x y : R) := Rabs (x - y).
Local Parameter (f : R -> R) (a L : R).

Goal ~ (forall eps : R, eps > 0 -> exists delta : R, delta > 0 -> forall x : R,
          0 < Rdist x a < delta -> Rdist (f x) L < eps)
      ->
     (exists eps : R, eps > 0 /\ (forall delta : R, delta > 0 /\ (exists x : R,
          0 < Rdist x a < delta /\ ~ Rdist (f x) L < eps))).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.

Goal (exists eps : R, eps > 0 /\ (forall delta : R, delta > 0 /\ (exists x : R,
          0 < Rdist x a < delta /\ ~ Rdist (f x) L < eps)))
     ->
     ~ (forall eps : R, eps > 0 -> exists delta : R, delta > 0 -> forall x : R,
          0 < Rdist x a < delta -> Rdist (f x) L < eps).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
Close Scope R_scope.



(** Atomic propositions with negation. *)
Local Parameter P Q : Prop.
Local Parameter S : nat -> Prop.

(* Test 1: double negation cancels out. *)
Goal ~~P -> P.
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 2: double negation cancels out (reverse). *)
Goal P -> ~~P.
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.

(* Test 3: ~(P \/ Q) implies (~P /\ ~Q). *)
Goal ~(P \/ Q) -> (~P /\ ~Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 4: (~P /\ ~Q) implies ~(P \/ Q). *)
Goal (~P /\ ~Q) -> ~(P \/ Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.

(* Test 5: ~(P /\ Q) implies (~P \/ ~Q). *)
Goal ~(P /\ Q) -> (~P \/ ~Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 6: (~P \/ ~Q) implies ~(P /\ Q). *)
Goal (~P \/ ~Q) -> ~(P /\ Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.

(* Test 7: ~(P /\ Q) implies (P -> ~Q). *)
Goal ~(P /\ Q) -> (P -> ~Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 8: (P -> ~Q) implies ~(P /\ Q). *)
Goal (P -> ~Q) -> ~(P /\ Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.

(* Test 9: ~(P -> Q) implies (P /\ ~Q). *)
Goal ~(P -> Q) -> (P /\ ~Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 10: (P /\ ~Q) implies ~(P -> Q). *)
Goal (P /\ ~Q) -> ~(P -> Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.

(* Test 11: ~(forall x, S x) implies (exists x, ~S x). *)
Goal ~(forall x, S x) -> (exists x, ~S x).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 12: (exists x, ~S x) implies ~(forall x, S x). *)
Goal (exists x, ~S x) -> ~(forall x, S x).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.

(* Test 13: ~(exists x, S x) implies (forall x, ~S x). *)
Goal ~(exists x, S x) -> (forall x, ~S x).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 14: (forall x, ~S x) implies ~(exists x, S x). *)
Goal (forall x, ~S x) -> ~(exists x, S x).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.


(** Propositions with negations in subexpressions of logical operators. *)
(* Test 15: or *)
Goal (~~P \/ ~~Q) -> (P \/ Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 16: and *)
Goal (~~P /\ ~~Q) -> (P /\ Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 17: implies *)
Goal (~~P -> ~~Q) -> (P -> Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 18: for all *)
Goal (forall x, ~~S x) -> (forall x, S x).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.
(* Test 19: exists *)
Goal (exists x, ~~S x) -> (exists x, S x).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.


(** Some mixed stuff. *)
(* Test 20 *)
Goal (P \/ ~~Q) -> (~~P \/ Q).
Proof.
  intro H.
  solve_by_manipulating_negation_in @H.
Qed.

(** Difficult case from theory. *)
Open Scope R_scope.
Local Parameter A : R -> Prop.
(* Test 21 *)
Goal (~ (exists x : R, A x /\ L < x)) -> (forall x : R, A x ->  ~(L < x)).
Proof.
  intro H.
  solve_by_manipulating_negation (fun () => ()).
Qed.


(** Test tactic that tries every hypothesis *)

(* Test 22 *)
Goal ~ (forall eps : R, eps > 0 -> exists delta : R, delta > 0 -> forall x : R,
          0 < Rdist x a < delta -> Rdist (f x) L < eps)
      ->
     (exists eps : R, eps > 0 /\ (forall delta : R, delta > 0 /\ (exists x : R,
          0 < Rdist x a < delta /\ ~ Rdist (f x) L < eps))).
Proof.
  intro H.
  solve_by_manipulating_negation (fun () => ()).
Qed.

(* Test 23 *)
Goal (0 = 0) -> (2 = 2) -> ~ (forall eps : R, eps > 0 -> exists delta : R, delta > 0 -> forall x : R,
          0 < Rdist x a < delta -> Rdist (f x) L < eps)
      ->
     (exists eps : R, eps > 0 /\ (forall delta : R, delta > 0 /\ (exists x : R,
          0 < Rdist x a < delta /\ ~ Rdist (f x) L < eps))).
Proof.
  intros zero_eq_zero two_eq_two H.
  solve_by_manipulating_negation (fun () => ()).
Qed.
Close Scope R_scope.


(** Test theory specific negation manipulations. *)

(* Test 24 *)
Goal forall n m : nat, ~(n < m) -> (n >= m).
Proof.
  intros n m h.
  solve_by_manipulating_negation_in @h.
Fail Qed.
Abort.

Waterproof Enable Automation RealsAndIntegers.

(* Test 25 *)
Goal forall n m : nat, ~(n < m) -> (n >= m).
Proof.
  intros n m h.
  solve_by_manipulating_negation_in @h.
Fail Qed.
Abort.
