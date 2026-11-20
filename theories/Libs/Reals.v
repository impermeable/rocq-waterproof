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

From Stdlib Require Import Lra.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import ROrderedType.

From Waterproof Require Import Notations.

Require Export Libs.Reals.Rational.
Require Export Libs.Reals.Integer.
Require Export Libs.Reals.RealInequalities.
Require Export Libs.Reals.Intervals.
Require Export Libs.Reals.ArchimedN.

Local Open Scope R_scope.

(** * Lemmas linking reals and booleans *)

Lemma Req_true : forall x y : R, x = y -> Reqb x y = true.
Proof.
  intros x y H.
  destruct (Reqb_eq x y).
  apply (H1 H).
Qed.

Lemma true_Req : forall x y : R, Reqb x y = true -> x = y.
Proof.
  intros.
  destruct (Reqb_eq x y).
  apply (H0 H).
Qed.

Lemma Req_false : forall x y : R, x <> y -> Reqb x y = false.
Proof.
  intros.
  unfold Reqb.
  destruct Req_dec.
  contradiction.
  trivial.
Qed.

Lemma false_Req : forall x y : R, Reqb x y = false -> x <> y.
Proof.
  intros.
  destruct (Req_dec x y).
  rewrite (Req_true x y e) in H.
  assert (H1 : true <> false).
  auto with *.
  contradiction.
  apply n.
Qed.

(** * Lemmas regarding identities for absolute values and inverses *)

Lemma div_sign_flip : forall r1 r2 : R, r1 > 0 -> r2 > 0 -> r1 > 1 / r2 -> 1 / r1 < r2.
Proof.
  intros.
  unfold Rdiv in *.
  rewrite Rmult_1_l in *.
  rewrite <- (Rinv_inv r2).
  apply (Rinv_lt_contravar (/ r2) r1).
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat.
  apply H0.
  apply H.
  apply H1.
Qed.

Lemma div_pos : forall r1 r2 : R, r1 > 0 ->1 / r1 > 0.
Proof.
  intros.
  unfold Rdiv.
  rewrite Rmult_1_l.
  apply Rinv_0_lt_compat.
  apply H.
Qed.

Lemma div_non_zero : forall a b : R, a ≠ 0 -> b ≠ 0 -> a / b ≠ 0.
Proof.
  intros a b Ha Hb.
  unfold Rdiv.
  apply Rmult_integral_contrapositive_currified.
  - exact Ha.
  - apply Rinv_neq_0_compat.
    exact Hb.
Qed.

Lemma div_one_neq_zero : forall x : R, x ≠ 0 -> 1 / x ≠ 0.
Proof.
  intros x Hx.
  apply div_non_zero.
  - apply R1_neq_R0.
  - exact Hx.
Qed.

Lemma Rabs_zero : forall r : R, Rabs (r - 0) = Rabs r.
Proof.
  intros.
  rewrite Rminus_0_r.
  trivial.
Qed.

Lemma inv_remove : forall r1 r2 : R, 0 < r1 -> 0 < r2 -> 1 / r1 < 1 / r2 -> r1 > r2.
Proof.
  intros.
  unfold Rdiv in *.
  rewrite Rmult_1_l in *.
  rewrite <- (Rinv_inv r1), <- (Rinv_inv r2).
  apply (Rinv_lt_contravar (/ r1) (/ r2)).
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat.
  apply H.
  apply Rinv_0_lt_compat.
  apply H0.
  rewrite Rmult_1_l in *.
  apply H1.
  all: apply Rgt_not_eq; assumption.
Qed.

Lemma Rle_abs_min : forall x : R, -x <= Rabs x.
Proof.
  intros.
  rewrite <- (Rabs_Ropp (x)).
  apply Rle_abs.
Qed.

Lemma Rge_min_abs : forall x : R, x >= -Rabs x.
Proof.
  intros.
  rewrite <- (Ropp_involutive x).
  apply Ropp_le_ge_contravar.
  rewrite (Rabs_Ropp (- x)).
  apply Rle_abs.
Qed.

Lemma Rmax_abs : forall a b : R, Rmax (Rabs a) (Rabs b) >= 0.
Proof.
  intros.
  apply (Rge_trans _ (Rabs a) _).
  apply Rle_ge.
  apply Rmax_l.
  apply (Rle_ge 0 (Rabs a)).
  apply Rabs_pos.
Qed.

Lemma Rabs_left1_with_minus :
  forall a b : R, 0 < a -> b = -a -> Rabs (b) = a.
Proof.
  intros a b a_gt_0 b_eq_min_a.
  rewrite b_eq_min_a.
  unfold Rabs.
  destruct (Rcase_abs(-a)).
  - apply Ropp_involutive.
  - assert (- a < 0).
    + rewrite<- Ropp_0.
      apply Ropp_lt_contravar.
      assumption.
    + pose proof (Rlt_not_ge (-a) 0 H).
      contradiction.
Qed.

(** * Lemmas for decidability *)

(** ** Lemmas to write e.g. <<{r1 ≤ r2} + {r2 < r1}>> *)

Lemma Rlt_ge_dec : forall r1 r2, sumbool (r1 < r2) (r1 >= r2).
Proof.
  intros.
  destruct (total_order_T r1 r2).
  destruct s.
  exact (left r).
  exact (right (Req_ge r1 r2 e)).
  exact (right (Rle_ge r2 r1 (Rlt_le r2 r1 r))).
Qed.

Lemma Rle_ge_dec : forall r1 r2, sumbool (r1 <= r2) (~ r2 >= r1).
Proof.
  intros.
  destruct (total_order_T r1 r2).
  destruct s.
  apply (left (Rlt_le r1 r2 r)).
  apply (left (Req_le r1 r2 e)).
  apply (right (Rlt_not_ge r2 r1 r)).
Qed.

Lemma Rge_le_dec : forall r1 r2, sumbool (r1 >= r2) (~ r2 <= r1).
Proof.
  intros.
  destruct (total_order_T r1 r2).
  destruct s.
  apply (right (Rlt_not_le r2 r1 r)).
  apply (left (Req_ge r1 r2 e)).
  apply (left (Rgt_ge r1 r2 r)).
Qed.


(** ** Lemmas to split e.g. <<{r1 <= r2}>> into <<{r1 < r2} + {r1 = r2}>> *)

Lemma Rge_lt_or_eq_dec : forall r1 r2, (r1 >= r2) -> sumbool (r2 < r1) (r1 = r2).
Proof.
  intros.
  destruct (total_order_T r2 r1).
  - destruct s.
    + left. exact r.
    + right. symmetry. exact e.
  - exfalso.
    exact (Rlt_not_ge _ _ r H).
Qed.

Open Scope subset_scope.

Lemma left_in_closed_open {a b : R} : (a < b) -> (a ∈ [a,b)).
Proof.
  intro a_lt_b.
  split.
  - apply Rle_refl.
  - exact a_lt_b.
Qed.

Lemma right_in_open_closed {a b : R} : (a < b) -> (b ∈ (a,b]).
Proof.
  intro a_lt_b.
  split.
  - exact a_lt_b.
  - apply Rle_refl.
Qed.
Close Scope subset_scope.

Close Scope R_scope.

Require Import Ltac2.Ltac2.

(** Tactic to deal with Rabs Rmin Rmax *)

Ltac2 crush_R_abs_min_max () :=
  unfold Rdist in *;
  unfold Rabs in *;
  unfold Rmax in *;
  unfold Rmin in *;
  repeat (destruct (Rcase_abs) in * );
  repeat (destruct (Rle_dec) in * );
  repeat (destruct (Rge_dec) in * ).

(** Incremental versions of [crush_R_abs_min_max].

    [crush_R_abs_min_max] case-splits on the sign of every [Rabs], [Rmax] and
    [Rmin] in the goal and in all hypotheses at once. That gives [2^n] goals
    for [n] such terms, whether or not they are relevant, and the automation
    then works on each of them. The tactics below split on one term at a time
    (terms in the goal first) and try [lra] after each split, so branches
    that [lra] can already close are not split any further. *)

(** Split one [Rcase_abs]/[Rle_dec]/[Rge_dec] (from an unfolded
    [Rabs]/[Rmax]/[Rmin]), preferring terms that occur in the goal.
    Fails if there is nothing left to split. *)
Ltac2 split_one_abs_min_max () :=
  match! goal with
  | [ |- context [ Rcase_abs ?x ] ] => destruct (Rcase_abs $x) in *
  | [ |- context [ Rle_dec ?x ?y ] ] => destruct (Rle_dec $x $y) in *
  | [ |- context [ Rge_dec ?x ?y ] ] => destruct (Rge_dec $x $y) in *
  | [ _ : context [ Rcase_abs ?x ] |- _ ] => destruct (Rcase_abs $x) in *
  | [ _ : context [ Rle_dec ?x ?y ] |- _ ] => destruct (Rle_dec $x $y) in *
  | [ _ : context [ Rge_dec ?x ?y ] |- _ ] => destruct (Rge_dec $x $y) in *
  end.

(** Split until [lra] closes the branch; fails as soon as one fully split
    branch is not closed by [lra]. Same result as
    [crush_R_abs_min_max (); lra], but a failure costs about [n] calls to
    [lra] instead of [2^n]. *)
Ltac2 rec split_abs_min_max_lra () :=
  first
  [ ltac1:(lra)
  | split_one_abs_min_max (); split_abs_min_max_lra () ].

Ltac2 unfold_abs_min_max () :=
  unfold Rdist in *;
  unfold Rabs in *;
  unfold Rmax in *;
  unfold Rmin in *.

(** Same goals as [crush_R_abs_min_max (); lra]. *)
Ltac2 crush_R_abs_min_max_lra () :=
  unfold_abs_min_max (); split_abs_min_max_lra ().

(** Drop-in replacement for [crush_R_abs_min_max]: closes the goal if [lra]
    can close every branch, and otherwise falls back to the full case split,
    leaving all branches to the automation as [crush_R_abs_min_max] does.

    The fallback is deliberately the full split rather than a pruned one:
    on goals the automation cannot prove, [lra] typically fails on every
    branch, and trying it at every node of the split tree (about [2^(n+1)]
    calls) made failing searches slower than the plain full split. The
    first attempt only costs about [n] calls to [lra] when it fails. *)
Ltac2 crush_R_abs_min_max_pruned () :=
  unfold_abs_min_max ();
  first [ split_abs_min_max_lra () | crush_R_abs_min_max () ].
