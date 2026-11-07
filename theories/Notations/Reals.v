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

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Qreals.

Require Import Notations.Common.
Require Import Notations.Sets.

(** ** (In)equalities
  Allowing unicode characters for uniqualities.
*)
Notation "x ≤ y" := (le x y) (at level 70, no associativity) : nat_scope.
Notation "x ≥ y" := (ge x y) (at level 70, no associativity) : nat_scope.
Notation "x ≤ y" := (x <= y)%R (at level 70, no associativity) : R_scope.
Notation "x ≥ y" := (x >= y)%R (at level 70, no associativity) : R_scope.

Open Scope nat_scope.
Open Scope R_scope.

(** ** Scopes and coercions *)
Notation "'ℕ'" := (nat).
Notation "'ℤ'" := (Z).
Notation "'ℚ'" := (Q).
Notation "'ℝ'" := (R).

(* We use coercions to get around writing INR and IZR *)
Coercion INR: nat >-> R.
Coercion IZR: Z >-> R.
Coercion Q2R: Q >-> R.

Open Scope subset_scope.

(** ** Sequences *)
Definition converges_to (a : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, R_dist (a n) c < ε.

Notation "a ⟶ c" := (converges_to a c) (at level 20).

Definition cv_implies_cv_abs_to_l_abs := cv_cvabs.

(** * Real numbers

  We have to take care with the associative level.
  When using this in rewrites, $<$, $>$, etc. should bind stronger.
*)

(* The symbol below is the standard pipe, unicode codepoint: U+007C *)
Notation "| x |" := (Rabs x) (at level 20, format "| x |") : R_scope.
Notation "|- x |" := (| (-x) |) (at level 20, x at next level, only parsing) : R_scope.
Notation dist_R := R_dist.

(** ** Powers *)
Notation "a ³" := (a * a * a) (at level 1) : R_scope.

(** ** Sums and series *)
Notation "'Σ' Cn 'equals' x" := (infinite_sum Cn x) (at level 50).

Definition finite_triangle_inequalty := sum_f_R0_triangle.

(** ** Subsets and intervals*)
Notation "[ a , b ]" := (as_subset R (fun x => (a <= x <= b))): R_scope.
Notation "[ a , b )" := (as_subset R (fun x => (a <= x <  b))): R_scope.
Notation "( a , b ]" := (as_subset R (fun x => (a <  x <= b))): R_scope.
Notation "( a , b )" := (as_subset R (fun x => (a <  x <  b))): R_scope.
Notation "( a , ∞ )" := (as_subset R (fun x => (a < x))): R_scope.
Notation "[ a , ∞ )" := (as_subset R (fun x => (a ≤ x))): R_scope.

Close Scope subset_scope.
Close Scope nat_scope.
Close Scope R_scope.
