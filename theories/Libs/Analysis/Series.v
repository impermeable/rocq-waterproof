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
From Stdlib Require Import Lra.
From Stdlib Require Import Classical.
From Stdlib Require Import Classical_Pred_Type.
From Stdlib Require Import ClassicalChoice.

From Waterproof Require Import Automation.
From Waterproof Require Import Libs.Analysis.Sequences.
From Waterproof Require Import Notations.Common.
From Waterproof Require Import Notations.Reals.
From Waterproof Require Import Notations.Sets.
From Waterproof Require Import Chains.
From Waterproof Require Import Tactics.

Waterproof Enable Automation RealsAndIntegers.

#[export] Hint Resolve Rabs_Rabsolu : wp_reals.
#[export] Hint Resolve Rabs_minus_sym : wp_reals.
#[export] Hint Resolve Rmult_lt_0_compat : wp_reals.
#[export] Hint Resolve Rinv_lt_contravar : wp_reals.

Open Scope R_scope.

Lemma sigma_split_v2 (a : ℕ → ℝ) (k  l M : ℕ) :
  (k < l)%nat ⇒ (l ≤ M)%nat
    ⇒ sigma a k M = sigma a k (l - 1)%nat + sigma a l M.
Proof.
  Assume that
    (k < l)%nat and (l ≤ M)%nat.
  It holds that l = S (l - 1)%nat as (i).
  (* TODO: It suffices to show that (sigma a k Nn = sigma a k (l - 1) + sigma a (S (l - 1)) Nn).*)
  rewrite (i) at 2.
  By sigma_split it suffices to show that (k <= l - 1 < M)%nat.
  We show both (k <= l - 1)%nat and (l - 1 < M)%nat.
  - We conclude that (k ≤ l - 1)%nat.
  - We conclude that (l - 1 < M)%nat.
Qed.

Notation partial_sums := sum_f_R0.

Lemma partial_sums_pos_incr (a : ℕ → ℝ) :
  (∀ n ∈ ℕ, a n ≥ 0) ⇒
    Un_growing (partial_sums a).
Proof.
  Assume that ∀ n ∈ ℕ, a n ≥ 0.
  We need to show that for all n : ℕ, partial_sums a n ≤ partial_sums a (S n).
  Take n : ℕ.
  It holds that a (S n) ≥ 0.
  It holds that (partial_sums a n) + a (S n) = partial_sums a (S n).
  We conclude that & partial_sums a n <= (partial_sums a n) + a (S n)
                                        = partial_sums a (S n).
Qed.

Definition series_cv_to (a : ℕ → ℝ) (l : ℝ) :=
  converges_to (partial_sums a) l.
Definition series_cv (a : ℕ → ℝ) (l : ℝ) :=
  series_cv_to a l.
Definition series_cv_abs (a : ℕ → ℝ) :=
  series_cv (fun n ↦ Rabs( a n )).
Definition series_cv_abs_to (a : ℕ → ℝ) (l : ℝ) :=
  series_cv_to (fun n ↦ Rabs(a n)) l.

Theorem mouse_tail (a : ℕ → ℝ) (k l : ℕ) (L : ℝ) :
    (k < l)%nat ⇒
      ((converges_to (fun Nn ↦ sigma a l Nn) L)
        ⇔
      (converges_to (fun Nn ↦ sigma a k Nn) ((sigma a k (l-1)) + L))).
Proof.
    Assume that (k < l)%nat as (i).
    We show both directions.
    - We need to show that converges_to (fun Nn ↦ (sigma a l Nn), L)
        ⇨ converges_to (fun Nn ↦ (sigma a k Nn), sigma a k (l - 1) + L).
      Assume that converges_to (fun Nn ↦ (sigma a l Nn), L).
      (* TODO: fix
         By lim_const_seq it holds that H1 : (Un_cv (fun N ↦ sigma a k (l-1)%nat) (sigma a k (l-1)%nat)). *)
      We claim that converges_to (fun N ↦ sigma a k (l-1)) (sigma a k (l-1)) as (xi).
      { We need to show that converges_to (constant_sequence (sigma a k (l-1))) (sigma a k (l-1)).
        By lim_const_seq we conclude that converges_to (constant_sequence (sigma a k (l-1))) (sigma a k (l-1)).
      }
      By convergence_plus it holds that converges_to (fun Nn ↦ sigma a k (l-1)%nat + sigma a l Nn) (sigma a k (l-1)%nat + L).
      We claim that evt_eq_sequences (fun Nn ↦ (sigma a k (l - 1) + sigma a l Nn)) (fun Nn ↦ (sigma a k Nn)) as (x).
      { We need to show that ∃ M ∈ ℕ, ∀ n : ℕ, (n ≥ M)%nat ⇒ sigma a k (l - 1)%nat + sigma a l n = sigma a k n.
        Choose M := l%nat.
        * Indeed, M ∈ ℕ.
        * We need to show that
            ∀ n ≥ M,
              sigma(a, k, (M - 1)%nat) + sigma(a, M, n) = sigma(a, k, n).
          Take n ≥ M.
          By sigma_split_v2 it suffices to show that (k < l <= n)%nat.
          We conclude that (k < l <= n)%nat.
      }
      (* TODO: find way of dealing with the case when Rocq cannot find parameters for apply ...*)
      apply conv_evt_eq_seq with (a := fun Nn ↦ sigma a k (l-1) + sigma a l Nn).
      + By x we conclude that evt_eq_sequences (fun Nn ↦ (sigma a k (l - 1) + sigma a l Nn), fun Nn ↦ (sigma a k Nn)).
      + (*TODO: fix  We conclude that ((Nn) ↦ (sigma a k (l - 1) + sigma a l Nn)). *)
        We need to show that converges_to (fun Nn ↦ (sigma a k (l - 1) + sigma a l Nn), sigma a k (l - 1) + L).
        By (xi) we conclude that converges_to (fun Nn ↦ (sigma a k (l - 1) + sigma a l Nn), sigma a k (l - 1) + L).
    - We need to show that converges_to (fun Nn ↦ (sigma a k Nn), (sigma a k (l - 1) + L)) ⇨ converges_to (fun Nn ↦ (sigma a l Nn), L).
      Assume that converges_to (fun Nn ↦ (sigma a k Nn), sigma a k (l - 1) + L) as (ii).
      We claim that converges_to (fun N ↦ (sigma a k (l-1)), (sigma a k (l-1))).
      { We need to show that (constant_sequence (sigma a k (l-1))) ⟶ (sigma a k (l-1)).
        By lim_const_seq we conclude that constant_sequence (sigma a k (l-1)) ⟶ sigma a k (l-1).
      }
      By convergence_minus it holds that converges_to (fun N ↦ sigma a k N - (sigma a k (l-1))) (sigma a k (l-1) + L - (sigma a k (l-1))).
      We claim that evt_eq_sequences (fun Nn ↦ (sigma a k Nn - sigma a k (l-1))) (fun Nn ↦ (sigma a l Nn)) as (iii).
      { We need to show that ∃ M ∈ ℕ, ∀ n : ℕ, (n ≥ M)%nat ⇒ sigma a k n - sigma a k (l-1) = sigma a l n.
        Choose M := l%nat.
        * Indeed, M ∈ ℕ.
        * We need to show that for all n, (n ≥ M)%nat
            ⇨ sigma(a, k, n) - sigma(a, k, (M - 1)%nat) = sigma(a, M, n).
          Take n : ℕ; such that (n ≥ M)%nat.
          It suffices to show that
            (sigma a k n = sigma a k (M - 1)%nat + sigma a l n).
          apply sigma_split_v2.
          - We conclude that (k < l)%nat.
          - We conclude that (l <= n)%nat.
      }
      apply conv_evt_eq_seq with (a := fun n ↦ sigma a k n - sigma a k (l-1)) (b := fun n ↦ sigma a l n).
      + By (iii) we conclude that evt_eq_sequences (fun n ↦ (sigma a k n - sigma a k (l - 1)), fun n ↦ (sigma a l n)).
      + We need to show that converges_to (fun N ↦ (sigma a k N - sigma a k (l - 1)), L).
        It holds that (sigma a k (l - 1) + L - sigma a k (l - 1)) = L as (iv).
        rewrite <- (iv). (* TODO come up with some notation for this (meaning transport)*)
        By (ii) we conclude that converges_to (fun N ↦ (sigma a k N - sigma a k (l - 1)), sigma a k (l - 1) + L - sigma a k (l - 1)).
Qed.

Close Scope R_scope.
