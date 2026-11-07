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

Require Import Waterproof.Libs.Analysis.FiniteSums.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Util.Assertions.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Tactics.

Open Scope R_scope.
Open Scope sum_scope.
Waterproof Enable Automation FiniteSums.
Waterproof Enable Automation RealsAndIntegers.

Definition f (n : nat) : R := (n * n + 2)%nat.

(* Matches f on [0, 3] only *)
Definition g (n : nat) : R :=
  (
    match n with
    | 0 => 2
    | 1 => 3
    | 2 => 6
    | 3 => 11
    | k => k
    end
  )%nat.

(* Unit tests *)

Example test_sigma_split : Σ[ i = 2,6 ] f(i) = Σ[ i = 2,4 ] f(i) + Σ[ i = 5,6 ] f(i).
Proof.
  We conclude that Σ[ i = 2,6 ] f(i) = Σ[ i = 2,4 ] f(i) + Σ[ i = 5,6 ] f(i).
Qed.

Example test_sigma_diff : Σ[ i = 2,6 ] f(i) - (Σ[ i = 2,4 ] f(i)) = Σ[ i = 5,6 ] f(i).
Proof.
  We conclude that Σ[ i = 2,6 ] f(i) - (Σ[ i = 2,4 ] f(i)) = Σ[ i = 5,6 ] f(i).
Qed.

Example test_sigma_diff_neg : Σ[ i = 2,4 ] f(i) - (Σ[ i = 2,6 ] f(i)) = -Σ[ i = 5,6 ] f(i).
Proof.
  We conclude that Σ[ i = 2,4 ] f(i) - (Σ[ i = 2,6 ] f(i)) = -Σ[ i = 5,6 ] f(i).
Qed.

Example test_sigma_first_rhs_l : Σ[ i = 2,9 ] f(i) = f(2%nat) + Σ[ i = 3,9 ] f(i).
Proof.
  It holds that (2 < 9)%nat.
  We conclude that Σ[ i = 2,9 ] f(i) = f(2%nat) + Σ[ i = 3,9 ] f(i).
Qed.

Example test_sigma_first_rhs_r : Σ[ i = 2,9 ] f(i) = Σ[ i = 3,9 ] f(i) + f(2%nat).
Proof.
  We conclude that Σ[ i = 2,9 ] f(i) = Σ[ i = 3,9 ] f(i) + f(2%nat).
Qed.

Example test_sigma_first_lhs_l : f(2%nat) + (Σ[ i = 3,9 ] f(i)) = Σ[ i = 2,9 ] f(i).
Proof.
  We conclude that f(2%nat) + (Σ[ i = 3,9 ] f(i)) = Σ[ i = 2,9 ] f(i).
Qed.

Example test_sigma_first_lhs_r : Σ[ i = 3,9 ] f(i) + f(2%nat) = Σ[ i = 2,9 ] f(i).
Proof.
  We conclude that Σ[ i = 3,9 ] f(i) + f(2%nat) = Σ[ i = 2,9 ] f(i).
Qed.

Example test_sigma_last_rhs_l : Σ[ i = 2,9 ] f(i) = f(9%nat) + Σ[ i = 2,8 ] f(i).
Proof.
  We conclude that Σ[ i = 2,9 ] f(i) = f(9%nat) + Σ[ i = 2,8 ] f(i).
Qed.

Example test_sigma_last_rhs_r : Σ[ i = 2,9 ] f(i) = Σ[ i = 2,8 ] f(i) + f(9%nat).
Proof.
  We conclude that Σ[ i = 2,9 ] f(i) = Σ[ i = 2,8 ] f(i) + f(9%nat).
Qed.

Example test_sigma_last_lhs_l : f(9%nat) + (Σ[ i = 2,8 ] f(i)) = Σ[ i = 2,9 ] f(i).
Proof.
  We conclude that f(9%nat) + (Σ[ i = 2,8 ] f(i)) = Σ[ i = 2,9 ] f(i).
Qed.

Example test_sigma_last_lhs_r : Σ[ i = 2,8 ] f(i) + f(9%nat) = Σ[ i = 2,9 ] f(i).
Proof.
  We conclude that Σ[ i = 2,8 ] f(i) + f(9%nat) = Σ[ i = 2,9 ] f(i).
Qed.

Example test_sigma_eq_arg : Σ[ i = 1,1 ] f(i) = f(1%nat).
Proof.
  We conclude that Σ[ i = 1,1 ] f(i) = f(1%nat).
Qed.

Example test_dist_l : Σ[ i = 4,7 ] 3 * f(i) = 3 * Σ[ i = 4,7 ] f(i).
Proof.
  We conclude that Σ[ i = 4,7 ] 3 * f(i) = 3 * Σ[ i = 4,7 ] f(i).
Qed.

Example test_dist_r : Σ[ i = 4,7 ] f(i) * 5 = 5 * Σ[ i = 4,7 ] f(i).
Proof.
  We conclude that Σ[ i = 4,7 ] f(i) * 5 = 5 * Σ[ i = 4,7 ] f(i).
Qed.

Example test_sigma_comm :
  Σ[ i = 4,7 ] (f(i) + g(i)) = Σ[ i = 4,7 ] f(i) + Σ[ i = 4,7 ] g(i).
Proof.
  We conclude that Σ[ i = 4,7 ] (f(i) + g(i)) = Σ[ i = 4,7 ] f(i) + Σ[ i = 4,7 ] g(i).
Qed.

Example test_sigma_shift_add : Σ[ i = 4,7 ] f(i) = Σ[ i = 5,8 ] f(i-1)%nat.
Proof.
  We conclude that Σ[ i = 4,7 ] f(i) = Σ[ i = 5,8 ] f(i-1)%nat.
Qed.

Example test_sigma_shift_sub : Σ[ i = 4,7 ] f(i) = Σ[ i = 3,6 ] f(i+1)%nat.
Proof.
  We conclude that Σ[ i = 4,7 ] f(i) = Σ[ i = 3,6 ] f(i+1)%nat.
Qed.

Example test_sigma_rev : Σ[ i = 1,5 ] f(i) = Σ[i=0,4] f(5-i)%nat.
Proof.
  We conclude that Σ[ i = 1,5 ] f(i) = Σ[i=0,4] f(5-i)%nat.
Qed.

Example test_sigma_telescope : Σ[ i = 1,9 ] (f(i+1)%nat - f(i)) = f(10%nat) - f(1%nat).
Proof.
  We conclude that Σ[ i = 1,9 ] (f(i+1)%nat - f(i)) = f(10%nat) - f(1%nat).
Qed.

Example test_sigma_even_to_odd :
  Σ[ i = 2,7 ] f(i) = Σ[ i = 1,3 ] f(2 * i)%nat + Σ[ i = 1,3 ] f(2 * i + 1)%nat.
Proof.
  We conclude that Σ[ i = 2,7 ] f(i) = Σ[ i = 1,3 ] f(2 * i)%nat + Σ[ i = 1,3 ] f(2 * i + 1)%nat.
Qed.

Example test_sigma_odd_to_even :
  Σ[ i = 3,8 ] f(i) = Σ[ i = 2,4 ] f(2 * i)%nat + Σ[ i = 2,4 ] f(2 * i - 1)%nat.
Proof.
  We conclude that Σ[ i = 3,8 ] f(i) = Σ[ i = 2,4 ] f(2 * i)%nat + Σ[ i = 2,4 ] f(2 * i - 1)%nat.
Qed.

Close Scope R_scope.
Close Scope sum_scope.
