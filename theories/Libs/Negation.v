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

From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Classical_Pred_Type.

Lemma or_func (A B C D : Prop) :
  (A -> C) -> (B -> D) -> (A \/ B) -> (C \/ D).
Proof.
  intros a_to_c b_to_d ab.
  destruct ab as [a | b].
  left; exact (a_to_c a).
  right; exact (b_to_d b).
Qed.

Lemma and_func (A B C D : Prop) :
  (A -> C) -> (B -> D) -> (A /\ B) -> (C /\ D).
Proof.
  intros a_to_c b_to_d ab.
  destruct ab as [a b].
  exact (conj (a_to_c a) (b_to_d b)).
Qed.

Lemma impl_func (A B C D : Prop) :
  (C -> A) -> (B -> D) -> (A -> B) -> (C -> D).
Proof.
  intros c_to_a b_to_d a_to_b c.
  exact (b_to_d (a_to_b (c_to_a c))).
Qed.

Lemma all_func (A : Type) (P Q : A -> Prop) :
  (forall x, P x -> Q x) -> (forall x, P x) -> (forall x, Q x).
Proof.
  intros allx_Px_to_Qx allx_Px x.
  exact ((allx_Px_to_Qx x) (allx_Px x)).
Qed.

Lemma ex_func (A : Type) (P Q : A -> Prop) :
  (forall x, P x -> Q x) -> (exists x, P x) -> (exists x, Q x).
Proof.
  intros allx_Px_to_Qx somex_Px.
  destruct somex_Px as [x Px].
  exists x.
  exact (allx_Px_to_Qx x Px).
Qed.

Lemma not_or_and_func (A B C D : Prop) :
  (~A -> C) -> (~B -> D) -> ~(A \/ B) -> (C /\ D).
Proof.
  intros na_to_c nb_to_d nab.
  tauto.
Qed.

(* Reverse *)
Lemma and_not_or_func (A B C D : Prop) :
  (C -> ~A) -> (D -> ~B) -> (C /\ D) -> ~(A \/ B).
Proof.
  intros c_to_na d_to_nb cd.
  tauto.
Qed.

Lemma not_and_or_func (A B C D : Prop) :
  (~A -> C) -> (~B -> D) -> ~(A /\ B) -> (C \/ D).
Proof.
  intros na_to_c nb_to_d nab.
  tauto.
Qed.

(* Reverse *)
Lemma or_not_and_func (A B C D : Prop) :
  (C -> ~A) -> (D -> ~B) -> (C \/ D) -> ~(A /\ B).
Proof.
  intros c_to_na d_to_nb cd.
  tauto.
Qed.

Lemma not_and_impl_func (A B C : Prop) :
  (~B -> C) -> ~(A /\ B) -> (A -> C).
Proof.
  intros nb_to_c nab.
  tauto.
Qed.

(* Reverse *)
Lemma impl_not_and_func (A B C : Prop) :
  (C -> ~B) -> (A -> C) -> ~(A /\ B).
Proof.
  intros c_to_nb a_to_c.
  tauto.
Qed.

Lemma not_impl_and_func (A B C : Prop) :
  (~B -> C) -> ~(A -> B) -> (A /\ C).
Proof.
  intros nb_to_c not_a_to_b.
  tauto.
Qed.

(* Reverse *)
Lemma and_not_impl_func (A B C : Prop) :
  (C -> ~B) -> (A /\ C) -> ~(A -> B).
Proof.
  intros c_to_nb ac a_to_b.
  exact ((c_to_nb (proj2 ac)) (a_to_b (proj1 ac))).
Qed.

Lemma not_all_ex_func (A : Type) (P Q : A -> Prop) :
  (forall x, ~P x -> Q x) -> (~forall x, P x) -> (exists x, Q x).
Proof.
  intros allx_notPx_to_Qx notallx_Px.
  apply not_all_ex_not in notallx_Px.
  destruct notallx_Px.
  exists x.
  apply allx_notPx_to_Qx.
  assumption.
Qed.

(* Reverse *)
Lemma ex_not_all_func (A : Type) (P Q : A -> Prop) :
  (forall x, Q x -> ~P x) -> (exists x, Q x) -> (~forall x, P x).
Proof.
  intros allx_Qx_to_notPx somex_Qx.
  apply ex_not_not_all.
  destruct somex_Qx as [x Qx].
  exists x.
  exact ((allx_Qx_to_notPx x) Qx).
Qed.

Lemma not_ex_all_func (A : Type) (P Q : A -> Prop) :
  (forall x, ~P x -> Q x) -> (~exists x, P x) -> (forall x, Q x).
Proof.
  intros allx_notPx_to_Qx notsomex_Px.
  intuition.
  apply allx_notPx_to_Qx.
  intros Px.
  apply notsomex_Px.
  exists x.
  assumption.
Qed.

Lemma all_not_ex_func (A : Type) (P Q : A -> Prop) :
  (forall x, Q x -> ~P x) -> (forall x, Q x) -> (~exists x, P x).
Proof.
  intros allx_Qx_to_notPx allx_Qx.
  apply all_not_not_ex.
  intro x.
  exact ((allx_Qx_to_notPx x) (allx_Qx x)).
Qed.

Lemma not_neg_pos_func (A B : Prop) :
  (A -> B) -> (~~A -> B).
Proof. intros a_to_b nna. exact (a_to_b (NNPP A nna)). Qed.

(* Reverse *)
Lemma pos_not_neg_func (A B : Prop) :
  (B -> A) -> (B -> ~~A).
Proof.
  intros b_to_a b na.
  exact (na (b_to_a b)).
Qed.

Require Import Ltac2.Ltac2.

Require Import Util.Constr.
Require Import Util.Hypothesis.
Require Import Waterprove.

Ltac2 Type exn ::= [ NegationError(string) ].

(** Hint *)
Ltac2 solve_by_manipulating_negation_in (h_id : ident) :=
  let h := Control.hyp h_id in
  (* Check whether h is a proposition. *)
  let type_h := get_value_of_hyp h in
  let sort_h := get_value_of_hyp type_h in
  match check_constr_equal sort_h constr:(Prop) with
  | false => Control.zero (NegationError "Can only manipulate negation in propositions.")
  | true =>
    let attempt () :=
      revert $h_id;
      repeat (
        first [
            (* finish directly if statements match *)
            exact id
            (* try all the different pattern matching to simplify goal *)
          | lazy_match! goal with
            (* without negation *)
            | [ |- (?a \/ ?b) -> (?c \/ ?d)] => apply (or_func $a $b $c $d)
            | [ |- (?a /\ ?b) -> (?c /\ ?d)] => apply (and_func $a $b $c $d)
            | [ |- (?a -> ?b) -> (?c -> ?d)] => apply (impl_func $a $b $c $d)
            | [ |- (forall x, @?p x) -> (forall x, @?q x)] =>
              apply (all_func _ $p $q);
              let x_id := Fresh.in_goal @x in
              intro $x_id
            | [ |- (exists x, @?p x) -> (exists x, @?q x)] =>
              apply (ex_func _ $p $q);
              let x_id := Fresh.in_goal @x in
              intro $x_id
              (* with negation *)
            | [ |- ~(?a \/ ?b) -> (?c /\ ?d)] => apply (not_or_and_func $a $b $c $d)
            | [ |- (?c /\ ?d) -> ~(?a \/ ?b)] => apply (and_not_or_func $a $b $c $d)
            | [ |- ~(?a /\ ?b) -> (?c \/ ?d)] => apply (not_and_or_func $a $b $c $d)
            | [ |- (?c \/ ?d) -> ~(?a /\ ?b)] => apply (or_not_and_func $a $b $c $d)
            | [ |- ~(?a /\ ?b) -> (?a -> ?c)] => apply (not_and_impl_func $a $b $c)
            | [ |- (?a -> ?c) -> ~(?a /\ ?b)] => apply (impl_not_and_func $a $b $c)
            | [ |- ~(?a -> ?b) -> (?a /\ ?c)] => apply (not_impl_and_func $a $b $c)
            | [ |- (?a /\ ?c) -> ~(?a -> ?b)] => apply (and_not_impl_func $a $b $c)
            | [ |- ~(forall x, @?p x) -> (exists x, @?q x)] =>
              apply (not_all_ex_func _ $p $q);
              let x_id := Fresh.in_goal @x in
              intro $x_id
            | [ |- (exists x, @?q x) -> ~(forall x, @?p x)] =>
              apply (ex_not_all_func _ $p $q);
              let x_id := Fresh.in_goal @x in
              intro $x_id
              | [ |- ~(exists x, @?p x) -> (forall x, @?q x)] =>
              apply (not_ex_all_func _ $p $q);
              let x_id := Fresh.in_goal @x in
              intro $x_id
            | [ |- (forall x, @?q x) -> ~(exists x, @?p x)] =>
              apply (all_not_ex_func _ $p $q);
              let x_id := Fresh.in_goal @x in
              intro $x_id
            | [ |- (~~?a) -> ?b] => apply (not_neg_pos_func $a $b)
            | [ |- ?b -> (~~?a)] => apply (pos_not_neg_func $a $b)
            end
        ]
      )
    in
    match Control.case attempt with
    | Val _ => ()
    | Err _ => Control.zero (NegationError "Failed to solve by manipulating negation.")
    end
  end.


Ltac2 solve_by_manipulating_negation (final_tac : unit -> unit) :=
  match! goal with
  | [ h : _ |- _ ] => progress (solve_by_manipulating_negation_in h; intro $h); final_tac ()
  end.
