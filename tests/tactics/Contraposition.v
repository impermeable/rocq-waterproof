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
Require Import Waterproof.Tactics.Contraposition.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Redirect Errors.

(** Test 1: Goal of the form ~ P -> ~ Q *)
Goal forall (P Q : Prop), ~ P -> ~ Q.
Proof.
intros P Q.
We argue by contraposition.
assert_constr_equal constr:(Q -> P) (Control.goal()).
Abort.

(** Test 2: Goal of the form P -> Q *)
Goal forall (P Q : Prop), P -> Q.
Proof.
intros P Q.
We argue by contraposition.
assert_constr_equal constr:(~ Q -> ~ P) (Control.goal()).
Abort.

(** Test 3: Goal not an implication *)
Goal forall (P Q : Prop), P -> Q.
Proof.
assert_fails_with_string (fun () => We argue by contraposition)
"One can only use 'We argue by contraposition' when proving an implication (A ⇒ B)".
Abort.
