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

From Stdlib Require Import Classical.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Util.Init.
Require Import Util.Goals.
Require Import Util.MessagesToUser.

(** Small helper lemma for the [wp_contrapose] tactic. *)
Lemma wp_contrapositive (P Q : Prop) : (P -> Q) <-> (~Q -> ~P).
Proof.
  split.
  - exact (fun H1 H2 HP => H2 (H1 HP)).
  - exact (fun H1 HP => (NNPP _ (fun H2 => H1 H2 HP))).
Qed.

(** A custom contrapose tactic.
  Converts a goal of the form [A -> B] into [~B -> ~A],
  and a goal of the form [~A -> ~B] into [B -> A].

  Throws an error if the goal is not an implication.
*)
Ltac2 wp_contrapose () :=
  lazy_match! goal with
  | [ |- ~ ?a -> ~ ?b] =>
    apply (wp_contrapositive $b $a)
  | [ |- ?_a -> ?_b] =>
    apply wp_contrapositive
  | [|- _] => 
    let msg := of_string "One can only use 'We argue by contraposition' when proving an implication (A ⇒ B)" in
    throw msg
  end.

(** Notation for [wp_contrapose] *)
Ltac2 Notation "We" "argue" "by" "contraposition" :=
  panic_if_goal_wrapped ();
  wp_contrapose().
