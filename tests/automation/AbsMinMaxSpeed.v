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

(** Regression tests for the speed of the [Rabs]/[Rmax]/[Rmin] case split in
    the [wp_reals] hints.

    Each goal has ten [Rabs]/[Rmax]/[Rmin] terms in irrelevant hypotheses and
    needs only the one in the goal. Splitting on every term at once gives
    [2^11] branches and takes several seconds per goal; splitting one term at
    a time (goal first) and trying [lra] after each split takes well under a
    second. The [Timeout]s fail if the full case split comes back. *)

From Stdlib Require Import Reals.Reals.
Require Import Ltac2.Ltac2.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Waterprove.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

Goal forall a b c d e f g h i j k l m n o x : R,
  Rabs a < 1 -> Rabs b < 1 -> Rmax c d > 0 -> Rmin e f < 2 -> Rabs g <= 3 ->
  Rabs h >= 0 -> Rmax i j <= 4 -> Rmin k l >= -4 -> Rabs m < 7 -> Rmax n o > -3 ->
  ~ (Rabs x < -1).
Proof.
  intros.
  Timeout 2 auto with wp_reals.
Qed.

Goal forall a b c d e f g h i j k l m n o x : R,
  Rabs a < 1 -> Rabs b < 1 -> Rmax c d > 0 -> Rmin e f < 2 -> Rabs g <= 3 ->
  Rabs h >= 0 -> Rmax i j <= 4 -> Rmin k l >= -4 -> Rabs m < 7 -> Rmax n o > -3 ->
  ~ (Rmax x 0 < x).
Proof.
  intros.
  Timeout 2 auto with wp_reals.
Qed.

Goal forall a b c d e f g h i j k l m n o x : R,
  Rabs a < 1 -> Rabs b < 1 -> Rmax c d > 0 -> Rmin e f < 2 -> Rabs g <= 3 ->
  Rabs h >= 0 -> Rmax i j <= 4 -> Rmin k l >= -4 -> Rabs m < 7 -> Rmax n o > -3 ->
  ~ (Rmin x 0 > x).
Proof.
  intros.
  Timeout 2 auto with wp_reals.
Qed.

Close Scope R_scope.
