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

From Waterproof Require Import Tactics.
From Waterproof Require Import Automation.
From Waterproof Require Import Libs.Reals.
From Waterproof Require Import Libs.Reals.ArchimedN.
From Waterproof Require Import Notations.Common.
From Waterproof Require Import Notations.Reals.
From Waterproof Require Import Notations.Sets.
From Waterproof Require Import Chains.

#[export] Hint Resolve Rmult_lt_0_compat : wp_reals.
#[export] Hint Resolve Rinv_lt_contravar : wp_reals.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.
Open Scope subset_scope.

(** ** What is a sequence of real numbers?

A sequence of real numbers is a function from the natural numbers to the real numbers. So a function $a_seq : \mathbb{N} → \mathbb{R}$ is a sequence.*)

(** *** Examples of sequences

Let us give a few examples of sequences of real numbers. The first example is the sequence $a_seq : ℕ → ℝ$ defined by

$$a_seq := \mathsf{fun} \   n \mapsto \mathsf{INR}(n) + 2.$$

In Waterproof, we can write this as*)

Definition a_seq : ℕ → ℝ := fun n ↦ INR(n) + 2.
(** We could also have written that $a_seq: \mathbb{N} → ℝ$ is defined by $(a_seq)_n := \mathsf{INR} (n) + 2$, and usually we just leave out the function $\mathsf{INR}$ and would write $(a_seq)_n := n + 2$.*)
(**
Another example is the sequence $y_seq: ℕ → ℝ$ defined by $(y_seq)_n := 3$. The sequence $y_seq$ is just constant! Within Waterproof, we could define the sequence $y_seq$ by
```
Definition y_seq : ℕ → ℝ := 3.
```

However, let us also give an alternative way, which looks a  bit closer to the definition $y_seq_n := 3$.*)

Definition y_seq (n : ℕ) := 3.
(** ** Terminology about sequences

We call the function values $a(0)$, $a(1)$, $a(2)$, $\dots$ the **elements** of the sequence. Instead of $a(n)$, in mathematics we often write $a_n$. Moreover, instead of writing *let $a : \mathbb{N} \to \mathbb{R}$ be a sequence*, one often writes *let $(a_n)_{n \in \mathbb{N}}$ be a sequence*, or even shorter *let $(a_n)$ be a sequence*.

The reason for the name *sequence* becomes clearer by writing the elements in a row, i.e. in a sequence,
$$
a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, \dots
$$

However convenient and intuitive this notation is, it can also become confusing if you forget that a sequence of real numbers is *really* a function from the natural numbers to the real numbers.*)
(** ** Asymptotic behavior of sequences

Analysis all revolves around questions such as: what happens if a parameter gets very small? What happens if a parameter gets very large?

For sequences, the interesting question is: what can we say about the elements $a_n$ when $n$ gets very large? Think for instance about the sequence $a_n := 1/n$. Then we might want to say: when $n$ gets very large, the element $a_n$ is very close to zero.

The only thing is, that we need to make the previous sentence much more precise if we want to work with it in mathematics. For all $\epsilon : ℝ$, if $ε > 0$, then there is a certain threshold $N : ℕ$ such that for all $n: ℕ$, if $n \geq N$ then $a_n$ is within distance $\epsilon$ from $0$.`*)
(** The definition of [cv_to] is completely equivalent to the definition of [Un_cv] in the standard library. *)

Lemma convergence_equivalence (a : ℕ → ℝ) (q : ℝ) :
  a ⟶ q ⇔ Un_cv a q.
Proof. (* hide proof *)
  We show both directions.
  * We need to show that a ⟶ q ⇒ Un_cv a q.
    Assume that a ⟶ q as (i).
    unfold Un_cv.
    To show : ∀ ε1 > 0,
       ∃ N2 : ℕ,
       ∀ n ≥ N2, |a(n) - q| < ε1.
    Take ε1 > 0.
    By (i) it holds that
      ∃ N1 ∈ ℕ, (∀ n ≥ N1, (|a(n) - q| < ε1)%R)%nat.
    Obtain such an N1.
    Choose N2 := N1.
    Take n ≥ N2.
    We conclude that |a(n) - q| < ε1.
  * We need to show that Un_cv a q ⇒ a ⟶ q.
    Assume that Un_cv a q as (ii).
    To show : ∀ ε > 0, ∃ N1 ∈ ℕ, (∀ n ≥ N1, (|a(n) - q| < ε)%R)%nat.
    Take ε > 0.
    By (ii) it holds that  ∃ N2 : ℕ,
       ∀ n ≥ N2, |a(n) - q| < ε.
    Obtain such an N2.
    Choose N1 := N2.
    - Indeed, N1 ∈ ℕ.
    - We need to show that (∀ n ≥ N1, (|a(n) - q| < ε)%R)%nat.
      Take n ≥ N1.
      We conclude that |a(n) - q| < ε.
Qed.

(** Next, we introduce eventually equal sequences, and show that they converge to the same limit.*)
Definition evt_eq_sequences (a b : ℕ → ℝ) :=
  (∃ k ∈ ℕ, (∀ n ≥ k, (a n = b n)%R))%nat.

Lemma conv_evt_eq_seq (a b : ℕ → ℝ) (l : ℝ) :
   (evt_eq_sequences a b) ⇒ (a ⟶ l) ⇒ (b ⟶ l).
Proof.
  Assume that evt_eq_sequences a b as (i) and a ⟶ l.
  To show : ∀ ε > 0, ∃ N1 ∈ ℕ, (∀ n ≥ N1, (|b(n) - l| < ε)%R)%nat.
  Take ε > 0.
  It holds that
    ∃ N1 ∈ ℕ,  for all n : ℕ, (n ≥ N1)%nat ⇨ |a n - l| < ε.
  Obtain such an N1.
  By (i) it holds that
    ∃ K ∈ ℕ, for all n : ℕ, (n ≥ K)%nat ⇨ a n = b n.
  Obtain such a K.
  Choose N2 := Nat.max N1 K.
  * Indeed, N2 ∈ ℕ.
  * We need to show that (∀ n ≥ N2, (|b(n) - l| < ε)%R)%nat.
    Take n ≥ N2.
    It holds that b n = a n.
    We conclude that & |b n - l| = |a n - l| < ε.
Qed.

(** From this, it is fairly easy to prove that sequences that are exactly the same also converge to the same limit.
We do this by first using the lemma, and then proving that the sequences are indeed eventually equal.*)

Lemma eq_seq_conv_to_same_lim (a : ℕ → ℝ) (b : ℕ → ℝ) (l : ℝ) :
  (∀ n ∈ ℕ, a n = b n) ⇒ a ⟶ l ⇒ b ⟶ l.
Proof.
  Assume that ∀ n ∈ ℕ, a n = b n.
  By conv_evt_eq_seq
    it suffices to show that ∃ k ∈ ℕ, ∀ n ≥ k, (a n = b n)%R%nat.
  Choose k := O.
  * Indeed, k ∈ ℕ.
  * We conclude that (∀ n ≥ k, a(n) = b(n))%nat.
Qed.

(* Some limit theorems *)

Lemma convergence_plus (a b : ℕ → ℝ) (m l : ℝ) :
  converges_to a m ⇒ converges_to b l ⇒
    converges_to (fun n ↦ a n + b n) (m + l).
Proof.
  intros Hm Hl.
  assert (Un_cv a m) by (apply convergence_equivalence; assumption).
  assert (Un_cv b l) by (apply convergence_equivalence; assumption).
  enough (Un_cv (fun n ↦ a n + b n) (m + l)) by
    (apply convergence_equivalence; assumption).
  apply CV_plus; assumption.
Qed.

Lemma convergence_minus (a b : ℕ → ℝ) (m l : ℝ) :
  converges_to a m ⇒ converges_to b l ⇒
    converges_to (fun n ↦ a n - b n) (m - l).
Proof.
  intros Hm Hl.
  assert (Un_cv a m) by (apply convergence_equivalence; assumption).
  assert (Un_cv b l) by (apply convergence_equivalence; assumption).
  enough (Un_cv (fun n ↦ a n - b n) (m - l)) by
    (apply convergence_equivalence; assumption).
  apply CV_minus; assumption.
Qed.

Lemma convergence_opp (a : ℕ → ℝ) (m : ℝ) :
  converges_to a m ⇒ converges_to (opp_seq a) (-m).
Proof.
  intro H.
  assert (Un_cv a m) by (apply convergence_equivalence; assumption).
  enough (Un_cv (opp_seq a) (-m)) by (apply convergence_equivalence; assumption).
  apply CV_opp; assumption.
Qed.

(** ** A simple limit

The simplest sequence we can think of is the constant sequence, e.g. $1, 1, 1, 1, 1, ...$.
We can generalise this to any real number $c$, and define the constant sequence $s_n = c, ∀ n : \mathbb{N}$.
Since we can choose $n$ as large as possible, without changing the value of $s_n$, this sequences clearly converges to its constant value $c$, i.e. $\lim_{n \to \infty} s_n = c$.*)
Definition constant_sequence (c : ℝ) := fun (n : ℕ) ↦ c.
Lemma lim_const_seq (c : ℝ) :
  constant_sequence c ⟶ c.
Proof.
  Define s := constant_sequence c.
  To show: ∀ ε > 0, ∃ N1 ∈ ℕ, (∀ n ≥ N1, (|s(n) - c| < ε)%R)%nat.
  Take ε > 0.
  Choose N1 := O.
  * Indeed, N1 ∈ ℕ.
  * We need to show that (∀ n ≥ N1, (|s(n) - c| < ε)%R)%nat.
    Take n ≥ N1.
    It holds that s n = c.
    We conclude that & |s n - c| = | c - c | = |0| = 0 < ε.
Qed.

(** *** **Another simple limit**

Next, we consider another rather simple sequence, namely $1, \frac{1}{2}, \frac{1}{3}, \frac{1}{4}, ...$.
We can denote the sequence as follows:
$$
  d_n = \frac{1}{n+1}.
$$
This is a bit more involved than the constant sequence, since the value of our sequence now depends on $n$.
Still, it is easy to see that when $n$ increases, the value of $d_n$ converges to $0$.*)
Definition d := fun (n : ℕ) ↦ 1 / (n + 1).

Lemma lim_d_0 : converges_to d 0.
Proof.
  To show :
      ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, |d(n) - 0| < ε.
    Take ε > 0.
    By archimedN_exists it holds that ∃ n1 ∈ ℕ, n1 > / ε.
    Obtain such an n1. Choose N1 := n1.
    * Indeed, N1 ∈ ℕ.
    * We need to show that ∀ n ≥ N1, |d(n) - 0| < ε.
      Take n ≥ N1.
      It suffices to show that -ε < 1 / (n + 1) - 0 < ε.
      We show both -ε < 1 / (n + 1) - 0 and 1 / (n + 1) - 0 < ε.
      - It holds that 0 < n + 1. (* n + 1 > 0 is difficult?*)
        We conclude that & -ε < 0 < / (n + 1) = 1 / (n + 1) - 0.
      - We claim that / ε < n + 1.
        { We conclude that & / ε < n1 <= n <= n + 1. }
        We conclude that & 1 / (n + 1) - 0 = / (n + 1) < / / ε = ε.
Qed.

Lemma min_1_over_n_plus_1_to_0 :
  converges_to (fun (n : ℕ) ↦ - (1 / (INR(n) + 1))) 0.
Proof.
    By lim_d_0 it holds that converges_to d 0.
    We claim that Un_cv d 0.
    {
      apply convergence_equivalence; assumption.
    }
    By CV_opp it holds that Un_cv (opp_seq d) (-0) as (i).
    We claim that converges_to (opp_seq d) (-0).
    {
      apply convergence_equivalence; assumption.
    }
    It holds that  Un_cv (fun n ↦ -d(n), -0).
    It holds that  Un_cv (fun n ↦ -(1 / (n + 1)), -0).
    It holds that 0 = -0.
    It suffices to show that Un_cv (fun n ↦ -(1 / (n + 1)), -0).
    By (i) we conclude that Un_cv (fun n ↦ -(1 / (n + 1)), -0).
Qed.

(** ** The squeeze theorem*)
Theorem squeeze_theorem (a : ℕ → ℝ) (b : ℕ → ℝ) (c : ℕ → ℝ) (l : ℝ) :
    (∀ n ∈ ℕ, a n ≤ b n ∧ b n ≤ c n) ⇒
      a ⟶ l ⇒ c ⟶ l ⇒ b ⟶ l.
Proof.
  Assume that ∀ n ∈ ℕ, a n ≤ b n ∧ b n ≤ c n and a ⟶ l.
  Assume that c ⟶ l.
  To show: ∀ ε > 0, ∃ N1 ∈ ℕ, (∀ n ≥ N1, (|b(n) - l| < ε)%R)%nat.
  Take ε > 0.
  It holds that ∃ Na ∈ ℕ, ∀ n : ℕ, (n ≥ Na)%nat ⇒ |a n - l| < ε.
  Obtain such an Na.
  It holds that ∃ Nc ∈ ℕ, ∀ n : ℕ, (n ≥ Nc)%nat ⇒ |c n - l| < ε.
  Obtain such an Nc.
  Choose N1 := Nat.max Na Nc.
  * Indeed, N1 ∈ ℕ.
  * We need to show that (∀ n ≥ N1, (|b(n) - l| < ε)%R)%nat.
    Take n ≥ N1.
    We claim that -ε < a n - l.
    { It holds that (n ≥ Na)%nat.
      It holds that R_dist (a n) l < ε as (iii).
      By Rabs_def2 it holds that a n - l < ε /\ -ε < a n - l.
      We conclude that -ε < a n - l.
    }
    We claim that c n - l < ε.
    { It holds that (n ≥ Nc)%nat.
      It holds that R_dist (c n) l < ε as (iii).
      By Rabs_def2 it holds that c n - l < ε /\ -ε < c n - l.
      We conclude that c n - l < ε.
    }
    It suffices to show that -ε < b n - l < ε.
    It holds that a n ≤ b n ∧ b n ≤ c n.
    We show both - ε < b n - l and  b n - l < ε.
    - We conclude that & - ε < a n - l <= b n - l.
    - We conclude that & b n - l <= c n - l < ε.
Qed.

Lemma upp_bd_seq_is_upp_bd_lim (a : ℕ → ℝ) (L M: ℝ) :
  (∀ n ∈ ℕ, a n ≤ M) ⇒ (converges_to a L) ⇒ L ≤ M.
Proof.
  Assume that ∀ n ∈ ℕ, (a n) ≤ M.
  Assume that converges_to a L as (i).
  By Rle_or_lt it holds that L ≤ M ∨ M < L as (ii).
  Because (ii) either L ≤ M or M < L holds.
  - Case L ≤ M.
    It follows that L ≤ M.
  - Case M < L.
    Define ε := L-M.
    It holds that ε > 0.
    It holds that for all eps : ℝ, eps > 0
      ⇨ ∃ N ∈ ℕ, for all n : ℕ, (n ≥ N)%nat
      ⇨ | a n - L | < eps.
    It holds that ∃ Nn ∈ ℕ, ∀n : ℕ, (n ≥ Nn)%nat ⇒ R_dist (a n) L < ε.
    Obtain such an Nn.
    It holds that |a(Nn) - L| < ε.
    By Rabs_def2 it holds that a Nn - L < ε ∧ (- ε < a Nn - L).
    It holds that - ε < a Nn - L.
    It holds that a Nn ≤ M.
    It holds that - (L - M) < a Nn - L.
    It follows that L ≤ M.
Qed.

Lemma low_bd_seq_is_low_bd_lim (a : ℕ → ℝ) (L M: ℝ) :
  (∀ n ∈ ℕ, a n ≥ M) ⇒ (converges_to a L) ⇒ L ≥ M.
Proof.
  Assume that ∀ n ∈ ℕ, a n ≥ M.
  Define b := opp_seq a.
  Assume that converges_to a L.
  It holds that b = (fun n => - a n).
  By convergence_opp it holds that converges_to b (-L).
  We claim that -L ≤ -M.
  { (* FIXME, this should work *)
    (* By upp_bd_seq_is_upp_bd_lim it suffices to show that
      (∀ (n : nat) ∈ ℕ, b n ≤ - M).*)
    apply (upp_bd_seq_is_upp_bd_lim b).
    * Take n ∈ ℕ.
      We conclude that & b n = - a n <= -M.
    * assumption.
  }
  We conclude that L >= M.
Qed.

(** ** Order and limits*)
Lemma seq_ordered_lim_ordered (a b: ℕ → ℝ) (m l : ℝ) :
  converges_to a m ⇒ converges_to b l ⇒ (∀ n ∈ ℕ, a n ≤ b n) ⇒ m ≤ l.
Proof.
  Assume that converges_to a m and converges_to b l.
  Assume that ∀ n ∈ ℕ, a n ≤ b n.
  We argue by contradiction.
  Assume that ~ m <= l.
  It holds that l < m.
  Define ε := (m - l)/2.
  It holds that ε > 0.
  It holds that for all eps : ℝ, eps > 0
    ⇨ ∃ N ∈ ℕ, for all n : ℕ, (n ≥ N)%nat
    ⇨ | a n - m | < eps.
  It holds that for all eps : ℝ, eps > 0
    ⇨ ∃ N ∈ ℕ, for all n : ℕ, (n ≥ N)%nat
    ⇨ | b n - l | < eps.
  It holds that ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat ⇒ | (a n) - m | < ε.
  Obtain such an N1.
  It holds that ∃ N2 ∈ ℕ, ∀ n : ℕ, (n ≥ N2)%nat ⇒ | (b n) - l | < ε.
  Obtain such an N2.
  Define N3 := Nat.max N1 N2.
  We claim that b N3 < a N3.
  {
    It holds that |b(N3) - l| < ε.
    It holds that |a(N3) - m| < ε.
    By Rabs_def2 it holds that a N3 - m < ε ∧ - ε < a N3 - m.
    By Rabs_def2 it holds that b N3 - l < ε ∧ - ε < b N3 - l.
    We conclude that & b N3 < l + ε = l + (m - l)/2
                          = m - (m - l)/2 = m - ε < a N3.
  }
  It holds that a N3 <= b N3.
  Contradiction.
Qed.

Definition is_bounded (a : ℕ → ℝ) :=
  ∃ q ∈ ℝ,
    ∃ M > 0,
      ∀ n ∈ ℕ,
        |a n - q| ≤ M.
Notation "a 'is' '_bounded_'" := (is_bounded a) (at level 69).
Notation "a 'is' 'bounded'" := (is_bounded a) (at level 69, only parsing).

Waterproof Register Expand "bounded";
  for is_bounded;
  as "Definition bounded".

Definition is_bounded_equivalent (a : ℕ → ℝ) :=
  ∃ M > 0, ∀ n ∈ ℕ, |a n| ≤ M.

Lemma is_bounded_equivalence (a : ℕ → ℝ) :
  is_bounded a ⇔ is_bounded_equivalent a.
Proof.
We show both directions.
- We need to show that is_bounded a ⇨ is_bounded_equivalent a.
  Assume that is_bounded a.
  It holds that ∃ q ∈ R,
    ∃ M1 > 0, (∀ n ∈ ℕ, | a n - q | ≤ M1).
  Obtain such a q.
  It holds that there exists M1 : R, M1 > 0 ∧ (for all n : ℕ, | a n - q | ≤ M1).
  Obtain such an M1.
  It holds that M1 > 0 ∧ (for all n : ℕ, | a n - q | ≤ M1) as (i).
  Because (i) both M1 > 0 and
    for all n : ℕ, | a n - q | ≤ M1.
  We need to show that ∃ M > 0, (∀ n ∈ ℕ, | a n | ≤ M).
  Choose M := M1 + |q|.
  + We need to verify that M > 0.
    It holds that 0 ≤ |q|.
    It suffices to show that 0 <= M.
    We conclude that & 0 <= (M1 + |q|) = M.

  + We need to show that ∀ n ∈ ℕ, | a n | ≤ M .
    Take n ∈ ℕ.
    By Rabs_triang it holds that |a n - q + q| ≤ |a n - q| + |q|.
    We conclude that & |a n| = |a n - q + q|
                              <= (|a n - q| + |q|) <= (M1 + |q|) = M.

- We need to show that
    is_bounded_equivalent a ⇨ is_bounded a.
  Assume that ∃ M1 > 0, ∀ n ∈ ℕ, |a n| ≤ M1.
  Obtain such an M1. It holds that
    M1 > 0 ∧ ∀ n : ℕ, |a n| ≤ M1 as (i).
  Because (i) both M1 > 0 and
  for all n : ℕ, | a n | ≤ M1 hold.
  (* Expand the definition of is_bounded. *)
  We need to show that
    ∃ q ∈ ℝ, ∃ M > 0, (∀ n ∈ ℕ,
    | a n - q | ≤ M).
  Choose q := 0.
  + Indeed, q ∈ ℝ.
  + We need to show that ∃ M > q, ∀ n ∈ ℕ, |a(n) - q| ≤ M.
    Choose M := M1.
    * Indeed, M > q.
    * We need to show that
        ∀ n ∈ ℕ, | a n - q | ≤ M.
    Take n ∈ ℕ.
    We conclude that & |a n - q| = |a n| <= M.
Qed.

(** Definitions sequence bounded from above and below *)
Definition is_bounded_above (a : ℕ → ℝ) :=
  ∃ M ∈ ℝ, ∀ n ∈ ℕ, a(n) ≤ M.
Notation "a 'is' '_bounded' 'above_'" := (is_bounded_above a) (at level 69).
Notation "a 'is' 'bounded' 'above'" := (is_bounded_above a) (at level 69, only parsing).

Waterproof Register Expand "bounded" "above";
  for is_bounded_above;
  as "Definition bounded above".

Definition is_bounded_below (a : ℕ → ℝ) :=
  ∃ m ∈ ℝ, ∀ n ∈ ℕ, m ≤ a(n).
Notation "a 'is' '_bounded' 'below_'" := (is_bounded_below a) (at level 69).
Notation "a 'is' 'bounded' 'below'" := (is_bounded_below a) (at level 69, only parsing).

Waterproof Register Expand "bounded" "below";
  for is_bounded_below;
  as "Definition bounded below".

(** Convergence to +∞ and -∞. *)
Definition diverges_to_plus_infinity (a : ℕ → ℝ) :=
  ∀ M ∈ ℝ,
    (∃ N1 ∈ ℕ,
      ∀ n ≥ N1, (a(n) > M)%R)%nat.

Notation "a ⟶ ∞" := (diverges_to_plus_infinity a) (at level 20).
Notation "a '_diverges' 'to' '∞_'" := (diverges_to_plus_infinity a) (at level 20).
Notation "a 'diverges' 'to' '∞'"   := (diverges_to_plus_infinity a) (at level 20, only parsing).

Waterproof Register Expand "⟶" "∞";
  for diverges_to_plus_infinity;
  as "Definition divergence to infinity".

Waterproof Register Expand "diverges" "to" "∞";
  for diverges_to_plus_infinity;
  as "Definition divergence to infinity".

Definition diverges_to_minus_infinity (a : ℕ → ℝ) :=
  ∀ M ∈ ℝ,
    ∃ N1 ∈ ℕ,
      (∀ n ≥ N1, (a(n) < M)%R)%nat.

Notation "a ⟶ -∞" := (diverges_to_minus_infinity a) (at level 20).
Notation "a '_diverges' 'to' '-∞_'" := (diverges_to_minus_infinity a) (at level 20).
Notation "a 'diverges' 'to' '-∞'"   := (diverges_to_minus_infinity a) (at level 20, only parsing).

Waterproof Register Expand "⟶" "-∞";
  for diverges_to_minus_infinity;
  as "Definition divergence to minus infinity".

Waterproof Register Expand "diverges" "to" "-∞";
  for diverges_to_minus_infinity;
  as "Definition divergence to minus infinity".

Close Scope R_scope.
