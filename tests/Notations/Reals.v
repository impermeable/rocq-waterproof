(******************************************************************************)
(*                  This file is part of Waterproof-lib.                     *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify  *)
(*    it under the terms of the GNU General Public License as published by   *)
(*     the Free Software Foundation, either version 3 of the License, or     *)
(*                    (at your option) any later version.                    *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,     *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of       *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the        *)
(*               GNU General Public License for more details.                *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License     *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>. *)
(*                                                                            *)
(******************************************************************************)

Require Import Stdlib.Reals.Reals.

Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Chains.


Open Scope R_scope.
Open Scope subset_scope.

Goal |0| + |0| = |0| + |0|.
Abort.

Goal |0 + 3| = |3| + |0|.
Abort.

Goal |-3| = | -3 |.
Abort.

Goal exists g : R -> R, g (|- 3|) = |2|.
Abort.

Goal & |0| + |3| ≤ |-3| + |0| ≤ 4 + |5|.
Abort.

Goal & |0| * | 3 | ≤ | 4 + 3 | - |5| ≤ 3 * |- 2 |.
Abort.

Local Parameter a : nat -> R.
Goal ∀ x ∈ ℝ, ∀ n ∈ ℕ,
   | a(n) - 2 + 4 - 3 | = 34.
Abort.
