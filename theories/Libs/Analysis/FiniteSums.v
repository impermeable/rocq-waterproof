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
From Stdlib Require Import Classical_Pred_Type.
From Stdlib Require Export Reals.Reals.
From Stdlib Require Export Reals.Rsigma.
From Stdlib Require Import ClassicalChoice.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Arith.

Open Scope R_scope.

Declare Scope sum_scope.

Notation "'Σ' '[' i '=' m ',' n ']' e" :=
  (sigma (fun i => e) m n)
  (at level 50, i ident)
  : sum_scope.

Local Ltac simpl_INR :=
  repeat (
    rewrite plus_INR ||
    rewrite mult_INR ||
    rewrite S_INR ||
    rewrite INR_0 ||
    rewrite INR_1
  ).

(* Theorems and their helper lemmas *)

Local Lemma lt_plus_S : forall m k : nat, (m < m + S k)%nat.
Proof.
  intros m k.
  rewrite <- Nat.add_succ_comm.
  apply Nat.lt_lt_add_r.
  apply Nat.lt_succ_diag_r.
Qed.

Local Lemma Nat_double_S :
  forall n : nat, (2 * S n)%nat = S (S (2 * n))%nat.
Proof.
  intro n. unfold Nat.mul. rewrite Nat.add_0_r, Nat.add_0_r, Nat.add_succ_r.
  apply Nat.add_succ_l.
Qed.

Local Lemma Nat_pred_double_l :
  forall n : nat, (0 < n)%nat ->
  (Nat.pred (2 * n))%nat = S (2 * Nat.pred n)%nat.
Proof.
  intros n Hn. unfold Nat.mul.
  rewrite Nat.add_0_r, Nat.add_0_r.
  rewrite <- Nat.add_pred_r.
  rewrite <- Nat.add_succ_l.
  rewrite Nat.succ_pred. reflexivity.
  all: symmetry; apply Nat.lt_neq; assumption.
Qed.

Local Lemma sigma_eq_length :
  forall (f g : nat -> R) (m k : nat),
  (forall i : nat, (m <= i)%nat -> (i <= m+k)%nat -> f i = g i) ->
  sigma f m (m+k)%nat = sigma g m (m+k)%nat.
Proof.
  intros f g m. induction k; intro Heq.
  - rewrite <- plus_n_O.
    rewrite sigma_eq_arg. rewrite sigma_eq_arg. apply Heq.
    2: rewrite <- plus_n_O. all: apply Nat.le_refl.
  - rewrite (sigma_last f). rewrite (sigma_last g).
    rewrite <- Nat.add_succ_comm at 2 4. rewrite Nat.add_succ_l. rewrite Nat.pred_succ.
    rewrite IHk. f_equal. apply Heq. apply Nat.le_add_r. apply Nat.le_refl.
    { intros i Hbot Htop. apply Heq. assumption.
      rewrite <- Nat.add_succ_comm. apply (Nat.le_le_succ_r _ _ Htop). }
    all: apply Nat.lt_add_pos_r; apply Nat.lt_0_succ.
Qed.

Theorem sigma_eq :
  forall (f g : nat -> R) (m n : nat), (m <= n)%nat ->
  (forall i : nat, (m <= i)%nat -> (i <= n)%nat -> f i = g i) ->
  sigma f m n = sigma g m n.
Proof.
  intros f g m n Hleq Heq.
  rewrite <- (Arith_base.le_plus_minus_r_stt m n).
  apply sigma_eq_length.
  rewrite Arith_base.le_plus_minus_r_stt.
  intros i Hibot Hitop.
  apply Heq. all: assumption.
Qed.

Local Lemma sigma_distr_l_len :
  forall (f : nat -> R) (c : R) (m k : nat),
  sigma (fun i => c * f i) m (m+k) = c * (sigma f m (m+k)).
Proof.
  intros f c m. induction k.
  - rewrite <- plus_n_O.
    rewrite sigma_eq_arg.
    rewrite sigma_eq_arg.
    reflexivity.
  - rewrite (sigma_last f (lt_plus_S _ _)).
    rewrite (sigma_last _ (lt_plus_S _ _)).
    rewrite Nat.add_succ_r at 2 4. rewrite Nat.pred_succ.
    rewrite Rmult_plus_distr_l.
    rewrite IHk. reflexivity.
Qed.

Theorem sigma_distr_l :
  forall (f : nat -> R) (c : R) (m n : nat), (m <= n)%nat ->
  sigma (fun i => c * f(i)) m n = c * (sigma f m n).
Proof.
  intros f c m n Hleq.
  rewrite <- (Arith_base.le_plus_minus_r_stt m n).
  apply sigma_distr_l_len.
  assumption.
Qed.

Local Lemma sigma_distr_r_len :
  forall (f : nat -> R) (c : R) (m k : nat),
  sigma (fun i => f i * c) m (m+k) = c * (sigma f m (m+k)).
Proof.
  intros f c m. induction k.
  - rewrite <- plus_n_O.
    rewrite sigma_eq_arg.
    rewrite sigma_eq_arg.
    apply Rmult_comm.
  - rewrite (sigma_last f (lt_plus_S _ _)).
    rewrite (sigma_last _ (lt_plus_S _ _)).
    rewrite Nat.add_succ_r at 2 4. rewrite Nat.pred_succ.
    rewrite Rmult_plus_distr_l.
    rewrite IHk. f_equal. apply Rmult_comm.
Qed.

Theorem sigma_distr_r :
  forall (f : nat -> R) (c : R) (m n : nat), (m <= n)%nat ->
  sigma (fun i => f(i) * c) m n = c * (sigma f m n).
Proof.
  intros f c m n Hleq.
  rewrite <- (Arith_base.le_plus_minus_r_stt m n).
  apply sigma_distr_r_len.
  assumption.
Qed.

Local Lemma sigma_comm_len :
  forall (f g : nat -> R) (m k : nat),
    sigma f m (m+k) + sigma g m (m+k) = sigma (fun i => f i + g i) m (m+k).
Proof.
  intros f g m. induction k.
  - rewrite <- plus_n_O.
    rewrite sigma_eq_arg.
    rewrite sigma_eq_arg.
    rewrite sigma_eq_arg.
    reflexivity.
  - assert (Hleq : (m < m + S k)%nat).
    { apply (lt_plus_S m k). }
    rewrite (sigma_last f Hleq).
    rewrite (sigma_last g Hleq).
    rewrite (sigma_last _ Hleq).
    rewrite Nat.add_succ_r at 2 4 7. rewrite Nat.pred_succ.
    rewrite <- IHk,
      <- Rplus_assoc,
      (Rplus_assoc (f (m + S k)%nat)),
      (Rplus_comm _ (g (m + S k)%nat)),
      <- Rplus_assoc,
      <- Rplus_assoc.
    reflexivity.
Qed.

Theorem sigma_comm :
  forall (f g : nat -> R) (m n : nat), (m <= n)%nat ->
  sigma f m n + sigma g m n = sigma (fun i => f i + g i) m n.
Proof.
  intros f g m n Hleq.
  rewrite <- (Arith_base.le_plus_minus_r_stt m n).
  apply sigma_comm_len.
  assumption.
Qed.

Theorem sigma_shift_add :
  forall (f : nat -> R) (m n s : nat),
  sigma f m n = sigma (fun i => f (i - s)%nat) (m+s)%nat (n+s)%nat.
Proof.
  intros f m n s. unfold sigma.
  rewrite (Nat.add_comm m s) at 1. rewrite Nat.sub_add_distr. rewrite Nat.add_sub.
  f_equal. extensionality k. f_equal.
  rewrite Nat.add_shuffle0. symmetry. apply Nat.add_sub.
Qed.

Theorem sigma_shift_sub :
  forall (f : nat -> R) (m n s : nat), (s <= m)%nat -> (m <= n)%nat ->
  sigma f m n = sigma (fun i => f (i + s)%nat) (m-s)%nat (n-s)%nat.
Proof.

  intros f m n s H1 H2. unfold sigma.
  rewrite <- Nat.sub_add_distr. rewrite Nat.add_sub_assoc.
  rewrite Nat.add_comm. rewrite Nat.add_sub.
  f_equal. extensionality k. f_equal.
  rewrite <- Nat.add_assoc. rewrite (Nat.add_comm k s). rewrite Nat.add_assoc.
  rewrite Nat.sub_add. reflexivity. all: assumption.
Qed.

Theorem sigma_rev0 :
  forall (f : nat -> R) (k : nat),
  sigma f 0 k = sigma (fun i => f (k - i)%nat) 0 k.
Proof.
  intro f. induction k.
  - rewrite sigma_eq_arg. rewrite sigma_eq_arg.
    f_equal.
  - rewrite (sigma_last f).
    rewrite (@sigma_first _ _ (S k)).
    rewrite Nat.pred_succ.
    rewrite IHk.
    f_equal. all: apply Nat.lt_0_succ.
Qed.

Local Lemma sigma_rev_length :
  forall (f : nat -> R) (m k : nat),
  sigma f m (m+k) = sigma (fun i => f (m + k - i)%nat) 0 k.
Proof.
  intros f m k.
  rewrite (sigma_shift_sub _ _ _ m).
  rewrite Nat.sub_diag.
  rewrite Nat.add_comm. rewrite Nat.add_sub.
  rewrite sigma_rev0.
  assert (
    forall i : nat, (0 <= i)%nat -> (i <= k)%nat ->
     f (k - i + m)%nat = f (m + k - i)%nat
  ) as Heq.
  { intros i Hbot Htop. f_equal.
    rewrite <- (Nat.add_sub_swap _ _ _ Htop).
    rewrite Nat.add_comm. reflexivity.
  }
  apply sigma_eq. apply Nat.le_0_l.
  intros i Hbot Htop. f_equal. symmetry. apply (Nat.add_sub_swap _ _ _ Htop).
  apply Nat.le_refl. apply Nat.le_add_r.
Qed.

Theorem sigma_rev :
  forall (f : nat -> R) (m n : nat), (m <= n)%nat ->
  sigma f m n = sigma (fun i => f (n - i)%nat) 0 (n-m)%nat.
Proof.
  intros f m n Hmn.
  rewrite <- (Arith_base.le_plus_minus_r_stt m n).
  rewrite  (Arith_base.le_plus_minus_r_stt m n) at 2.
  apply sigma_rev_length. all: assumption.
Qed.

Local Lemma sigma_telescope_length :
  forall (f : nat -> R) (m k : nat),
  f (S m + k)%nat - f m = sigma (fun i => f (S i)%nat - f i) m (m + k)%nat.
Proof.
  intros f m. induction k.
  - rewrite Nat.add_0_r. rewrite Nat.add_0_r.
    rewrite sigma_eq_arg. reflexivity.
  - rewrite sigma_last.
    rewrite (Nat.add_succ_r m) at 3. rewrite Nat.pred_succ.
    rewrite Nat.add_succ_l.
    rewrite <- IHk.
    rewrite Rplus_minus_assoc. f_equal. rewrite <- Rplus_minus_swap.
    rewrite Nat.add_succ_comm.
    symmetry. apply Rplus_minus_r.
    apply lt_plus_S.
Qed.

Theorem sigma_telescope :
  forall (f : nat -> R) (m n : nat), (m <= n)%nat ->
  f (S n) - f m = sigma (fun i => f (S i) - f i) m n.
Proof.
  intros f m n Hmn.
  rewrite <- (Arith_base.le_plus_minus_r_stt m n).
  apply sigma_telescope_length.
  assumption.
Qed.

Theorem sigma_telescope_plus1 :
  forall (f : nat -> R) (m n : nat), (m <= n)%nat ->
  f (n + 1)%nat - f m = sigma (fun i => f (i + 1)%nat - f i) m n.
Proof.
  intros f m n Hmn. rewrite Nat.add_1_r.
  rewrite sigma_telescope.
  f_equal. extensionality i.
  rewrite Nat.add_1_r. reflexivity.
  assumption.
Qed.

Local Lemma sigma_zero_to_odd :
  forall (f : nat -> R) (t : nat),
  sigma f 0 (S (2 * t))
  = sigma (fun i => f (2 * i)%nat) 0 t
  + sigma (fun i => f (S (2 * i))%nat) 0 t.
Proof.
  intros f. induction t.
  - simpl. rewrite sigma_eq_arg. rewrite sigma_eq_arg. reflexivity.
  - rewrite sigma_last. rewrite Nat.pred_succ.
    rewrite sigma_last.
    rewrite Nat_double_S at 3. rewrite Nat.pred_succ.
    rewrite (@sigma_last _ _ (S t)). rewrite Nat.pred_succ.
    rewrite (@sigma_last _ _ (S t)). rewrite Nat.pred_succ.
    rewrite IHt.
    rewrite (Rplus_comm (f (S (2 * S t))%nat)).
    rewrite Rplus_assoc.
    rewrite Rplus_assoc.
    rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    apply Rplus_eq_compat_l.
    apply Rplus_comm.
    3: rewrite Nat_double_S.
    all: apply Nat.lt_0_succ.
Qed.

Local Lemma sigma_even_to_odd_length :
  forall (f : nat -> R) (s k : nat),
  sigma f (2 * s) (S (2 * (s + k)))
  = sigma (fun i => f (2 * i)%nat) s (s + k)%nat
  + sigma (fun i => f (S (2 * i))%nat) s (s + k)%nat.
Proof.
  intros f s k.
  rewrite (sigma_shift_sub _ (2 * s) _ (2 * s)).
  rewrite (sigma_shift_sub (fun i => f (2 * i)%nat) s _ s).
  rewrite (sigma_shift_sub (fun i => f (S (2 * i))) s _ s).
  rewrite Nat.sub_diag. rewrite Nat.sub_diag.
  rewrite Nat.sub_succ_l. rewrite <- Nat.mul_sub_distr_l.
  rewrite Nat.add_comm. rewrite Nat.add_sub.
  rewrite sigma_zero_to_odd.
  assert (
    sigma (fun i => f (2 * i + 2 * s)%nat) 0 k =
    sigma (fun i => f (2 * (i + s))%nat) 0
  k) as H. {
    f_equal. extensionality i. f_equal.
    symmetry. apply Nat.mul_add_distr_l.
  }
  rewrite H. apply Rplus_eq_compat_l.
  f_equal. extensionality i. f_equal.
  rewrite Nat.add_succ_l. f_equal.
  symmetry. apply Nat.mul_add_distr_l.
  apply Nat.mul_le_mono_l.
  1,3,5: apply Nat.le_add_r. 1,2,3: apply Nat.le_refl.
  (* A lot of shuffling to complete the last goal *)
  apply le_S_n. rewrite <- Nat_double_S.
  unfold Nat.mul. rewrite Nat.add_0_r, Nat.add_0_r.
  rewrite <- Nat.add_succ_l. rewrite (Nat.add_comm s k) at 2.
  rewrite <- Nat.add_succ_l. rewrite Nat.add_shuffle0.
  rewrite <- Nat.add_succ_l. rewrite Nat.add_assoc.
  rewrite (Nat.add_shuffle0 (S s) (S k) s).
  rewrite <- Nat.add_assoc. apply Nat.le_add_r.
Qed.

Theorem sigma_even_to_odd :
  forall (f : nat -> R) (s t : nat), (s <= t)%nat ->
  sigma f (2 * s) (S (2 * t))
  = sigma (fun i => f (2 * i)%nat) s t
  + sigma (fun i => f (S (2 * i))%nat) s t.
Proof.
  intros f s t Hst.
  rewrite <- (Arith_base.le_plus_minus_r_stt s t).
  apply sigma_even_to_odd_length.
  assumption.
Qed.

Corollary sigma_even_to_odd2 :
  forall (f : nat -> R) (m n : nat), (m < n)%nat -> Nat.Even m -> Nat.Odd n ->
  sigma f m n
  = sigma (fun i => f (2 * i)%nat) (Nat.div2 m) (Nat.div2 n)
  + sigma (fun i => f (S (2 * i))%nat) (Nat.div2 m) (Nat.div2 n).
Proof.
  unfold Nat.Odd, Nat.Even.
  intros f m n Hmn [m' Hm] [n' Hn].
  assert (Hm2 : Nat.div2 m = m'). { subst m. apply Nat.div2_even. }
  assert (Hn2 : Nat.div2 n = n'). { subst n. apply Nat.div2_odd'. }
  rewrite Hm2, Hn2, Hm, Hn, Nat.add_1_r.
  apply sigma_even_to_odd.
  rewrite (Nat.mul_le_mono_pos_l m' n' 2).
  apply Arith_base.lt_n_Sm_le_stt.
  rewrite <- (Nat.add_1_r (2 * n')), <- Hm, <- Hn.
  assumption. apply Nat.lt_0_succ.
Qed.

Corollary sigma_even_to_odd_auto :
  forall (f : nat -> R) (m n : nat), (m < n)%nat ->
  Nat.even m = true -> Nat.odd n = true ->
  sigma f m n
  = sigma (fun i => f (2 * i)%nat) (Nat.div2 m) (Nat.div2 n)
  + sigma (fun i => f (S (2 * i))%nat) (Nat.div2 m) (Nat.div2 n).
Proof.
  intros f m n Hmn Hm Hn.
  apply sigma_even_to_odd2. assumption.
  rewrite <- Nat.even_spec; assumption.
  rewrite <- Nat.odd_spec; assumption.
Qed.

Theorem sigma_odd_to_even :
  forall (f : nat -> R) (s t : nat), (s < t)%nat ->
  sigma f (S (2 * s)) (2 * t)%nat
  = sigma (fun i => f (2 * i)%nat) (S s) t
  + sigma (fun i => f (Nat.pred (2 * i))%nat) (S s) t.
Proof.
  intros f s t Hst.
  destruct (Nat.eq_dec (S s) t) as [H | H].
  - subst t.
    rewrite sigma_first. rewrite Nat_double_S.
    rewrite sigma_eq_arg. rewrite sigma_eq_arg. rewrite sigma_eq_arg.
    rewrite Nat_double_S. rewrite Nat.pred_succ. apply Rplus_comm.
    rewrite Nat_double_S. apply Nat.lt_succ_diag_r.
  - assert (S s < t)%nat as HSst. {
      destruct (Nat.lt_trichotomy (S s) t) as [H1 | [H1 | H1]].
      - assumption.
      - exfalso. apply H. assumption.
      - exfalso.
        apply (Arith_base.lt_not_le_stt _  _ Hst).
        apply Arith_base.lt_n_Sm_le_stt. assumption.
    }
    rewrite (sigma_shift_sub (fun i => f (Nat.pred (2 * i)%nat)) _ _ 1).
    rewrite Nat.sub_1_r. rewrite Nat.sub_1_r. rewrite Nat.pred_succ.
    rewrite sigma_first. rewrite sigma_last.
    rewrite (@sigma_last _ (S s)).
    rewrite (@sigma_first _ s).
    rewrite Nat.add_1_r. rewrite Nat_double_S. rewrite Nat.pred_succ.
    (* Shuffle to cancel some terms *)
    rewrite Rplus_comm.
    rewrite (Rplus_comm (f (S (2 * s)))).
    rewrite <- Rplus_assoc. apply Rplus_eq_compat_r.
    rewrite Rplus_assoc. apply Rplus_eq_compat_l.
    (* Prove equality *)
    rewrite Nat_pred_double_l.
    rewrite <- Nat_double_S.
    rewrite sigma_even_to_odd.
    f_equal. f_equal. extensionality i. f_equal.
    rewrite Nat.add_1_r. rewrite Nat_double_S. apply Nat.pred_succ.
    (* Clean up trivial goals *)
    rewrite Nat.succ_le_mono. rewrite Nat.succ_pred.
    apply Arith_base.lt_le_S_stt. assumption.
    symmetry. apply Arith_base.lt_0_neq_stt.
    1,2: apply (Nat.lt_trans _ (S s) _ (Nat.lt_0_succ _) HSst).
    apply Nat.lt_le_pred.
    1,2: assumption.
    2: apply Nat.lt_succ_l.
    1,2: rewrite <- Nat_double_S;
    rewrite <- (Nat.mul_lt_mono_pos_l _ _ _ (Nat.lt_0_succ 1%nat));
    assumption. apply Nat.le_1_succ. apply Nat.lt_le_incl. assumption.
Qed.

Corollary sigma_odd_to_even2 :
  forall (f : nat -> R) (m n : nat), (m < n)%nat -> Nat.Odd m -> Nat.Even n ->
  sigma f m n
  = sigma (fun i => f (2 * i)%nat) (S (Nat.div2 m)) (Nat.div2 n)
  + sigma (fun i => f (Nat.pred (2 * i))%nat) (S (Nat.div2 m)) (Nat.div2 n).
Proof.
  unfold Nat.Odd, Nat.Even.
  intros f m n Hmn [m' Hm] [n' Hn].
  assert (Hm2 : Nat.div2 m = m'). { subst m. apply Nat.div2_odd'. }
  assert (Hn2 : Nat.div2 n = n'). { subst n. apply Nat.div2_even. }
  rewrite Hm2, Hn2, Hm, Hn, Nat.add_1_r.
  apply sigma_odd_to_even.
  rewrite (Nat.mul_lt_mono_pos_l 2 m' n').
  apply Nat.lt_succ_l.
  rewrite <- Nat.add_1_r, <- Hm, <- Hn. assumption.
  apply Nat.lt_0_succ.
Qed.

Corollary sigma_odd_to_even_auto :
  forall (f : nat -> R) (m n : nat), (m < n)%nat ->
  Nat.odd m = true -> Nat.even n = true ->
  sigma f m n
  = sigma (fun i => f (2 * i)%nat) (S (Nat.div2 m)) (Nat.div2 n)
  + sigma (fun i => f (Nat.pred (2 * i))%nat) (S (Nat.div2 m)) (Nat.div2 n).
Proof.
  intros f m n Hmn Hm Hn.
  apply sigma_odd_to_even2. assumption.
  rewrite <- Nat.odd_spec; assumption.
  rewrite <- Nat.even_spec; assumption.
Qed.

Close Scope R_scope.

(* Waterproof imports here so they don't interfere with Rocq tactics
   in proofs above, like extensionality. *)

From Waterproof Require Import Tactics.
From Waterproof Require Import Automation.
From Waterproof Require Import Notations.Common.
From Waterproof Require Import Notations.Reals.
From Waterproof Require Import Chains.
From Waterproof Require Import Notations.Sets.

(* Build hint database *)

Create HintDb wp_finite_sums.
(* Waterproof Declare Automation FiniteSums. *)
Waterproof Set Main Databases FiniteSums wp_finite_sums.
Waterproof Set Shorten Databases FiniteSums wp_finite_sums.

#[export] Hint Resolve sigma_first : wp_finite_sums.
#[export] Hint Resolve sigma_last : wp_finite_sums.
#[export] Hint Resolve sigma_split : wp_finite_sums.
#[export] Hint Resolve sigma_diff : wp_finite_sums.
#[export] Hint Resolve sigma_diff_neg : wp_finite_sums.
#[export] Hint Resolve sigma_eq_arg : wp_finite_sums.
#[export] Hint Resolve sigma_eq : wp_finite_sums.
#[export] Hint Resolve sigma_distr_l : wp_finite_sums.
#[export] Hint Resolve sigma_distr_r : wp_finite_sums.
#[export] Hint Resolve sigma_comm : wp_finite_sums.
#[export] Hint Resolve sigma_shift_add : wp_finite_sums.
#[export] Hint Resolve sigma_shift_sub : wp_finite_sums.
#[export] Hint Resolve sigma_rev0 : wp_finite_sums.
#[export] Hint Resolve sigma_rev : wp_finite_sums.
#[export] Hint Resolve sigma_telescope : wp_finite_sums.
#[export] Hint Resolve sigma_even_to_odd : wp_finite_sums.
#[export] Hint Resolve sigma_odd_to_even : wp_finite_sums.
#[export] Hint Resolve sigma_even_to_odd_auto : wp_finite_sums.
#[export] Hint Resolve sigma_odd_to_even_auto : wp_finite_sums.

#[export] Hint Extern 1 (@eq R (Rplus _ (sigma ?f ?l' ?h')) (sigma ?f ?l ?h)) =>
  rewrite <- sigma_first : wp_finite_sums.
#[export] Hint Extern 1 (@eq R (Rplus (sigma ?f ?l' ?h') _) (sigma ?f ?l ?h)) =>
  rewrite Rplus_comm; rewrite <- sigma_first : wp_finite_sums.
#[export] Hint Extern 1 (@eq R (sigma ?f ?l ?h) (Rplus _ (sigma ?f ?l' ?h')) (sigma ?f ?l ?h)) =>
  rewrite <- sigma_first : wp_finite_sums.
#[export] Hint Extern 1 (@eq R (sigma ?f ?l ?h) (Rplus (sigma ?f ?l' ?h') _)) =>
  rewrite Rplus_comm; rewrite <- sigma_first : wp_finite_sums.

#[export] Hint Extern 1 (@eq R (Rplus _ (sigma ?f ?l' ?h')) (sigma ?f ?l ?h)) =>
  rewrite sigma_last : wp_finite_sums.
#[export] Hint Extern 1 (@eq R (Rplus (sigma ?f ?l' ?h') _) (sigma ?f ?l ?h)) =>
  rewrite Rplus_comm; rewrite <- sigma_last : wp_finite_sums.
#[export] Hint Extern 1 (@eq R (sigma ?f ?l ?h) (Rplus _ (sigma ?f ?l' ?h'))) =>
  rewrite sigma_last : wp_finite_sums.
#[export] Hint Extern 1 (@eq R (sigma ?f ?l ?h) (Rplus (sigma ?f ?l' ?h') _)) =>
  rewrite Rplus_comm; rewrite <- sigma_last : wp_finite_sums.

#[export] Hint Extern 1 (@eq R (sigma ?f ?l ?h) (sigma ?g ?l ?h)) =>
  (apply sigma_eq; auto) : wp_finite_sums.

#[export] Hint Extern 1 (@eq R (Rplus (sigma ?f1 ?l ?h) (sigma ?f2 ?l ?h)) (sigma ?f3 ?l ?h)) =>
  rewrite sigma_comm : wp_finite_sums.

#[export] Hint Extern 1 (@eq R (sigma ?f1 ?l ?h) (Rplus (sigma ?f2 ?l ?h) (sigma ?f3 ?l ?h))) =>
  rewrite sigma_comm : wp_finite_sums.

#[export] Hint Extern 1 (@eq R (Rminus (?g ?x) (?g ?l)) (sigma ?f ?l ?h)) =>
  rewrite sigma_telescope : wp_finite_sums.
#[export] Hint Extern 1 (@eq R (sigma ?f ?l ?h) (Rminus (?g ?x) (?g ?l))) =>
  rewrite sigma_telescope : wp_finite_sums.

#[export] Hint Extern 1 (@eq R (Rminus (?g ?x) (?g ?l)) (sigma ?f ?l ?h)) =>
  rewrite sigma_telescope_plus1 : wp_finite_sums.
#[export] Hint Extern 1 (@eq R (sigma ?f ?l ?h) (Rminus (?g ?x) (?g ?l))) =>
  rewrite sigma_telescope_plus1 : wp_finite_sums.
