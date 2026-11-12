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

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Classical_Pred_Type.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.
From Stdlib Require Import Logic.ClassicalEpsilon.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.Rdefinitions.
From Stdlib Require Import Sets.Classical_sets.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import ZArith.ZArith.

Require Import Notations.Sets.
Require Import Chains.
Require Import Libs.Negation.
Require Import Libs.Reals.
Require Import Libs.Logic.
Require Import Libs.Sets.
Require Import Libs.Integers.
Require Import Libs.Functions.

Local Set Default Proof Mode "Classic". (* Hint Extern respects Default Proof Mode after Rocq 9 *)

(** * Waterproof core *)

Create HintDb wp_core.

  (* #[export] Hint Extern 1 ( _ = _ ) => progress(cbn; ltac2:(simpl_ineq_chains ()); ltac2:(split_conjunctions ())) : wp_core. *)
  (* #[export] Hint Resolve eq_sym : wp_core. *)
  (* including [eq_sym] slows down automation significantly, and we can apparantly do without :)
    [eq_sym] is still included in [wp_reals] *)
  #[export] Hint Resolve f_equal : wp_core.
  #[export] Hint Resolve f_equal2 : wp_core.
  (* This uses congruence to generate 50 equalities. 20 was not enough for exercises involving an injective composition *)
  #[export] Hint Extern 9 => congruence 50 : wp_core.
  (* #[export] Hint Extern 2 ( _ = _ ) => congruence 20 : wp_core. *)
  #[export] Hint Extern 2 => progress ltac2:(simpl_ineq_chains ()) : wp_core.
  #[export] Hint Extern 1 ( _ = _ ) => progress ltac2:(simpl_ineq_chains ()); congruence 20 : wp_core.
  (* TODO: maybe tune this better *)
  #[export] Hint Extern 2 => progress (unfold seal, subset_type, gt_op, R_gt_type, nat_gt_type, ge_op, R_ge_type, nat_ge_type,
    lt_op, R_lt_type, nat_lt_type, le_op, R_le_type, nat_le_type, ne_op, nat_ne_type, R_ne_type in * ) : wp_core.
  #[export] Hint Extern 2 => progress (unfold subset_in, conv, as_subset in * ) : wp_core.
  #[export] Hint Resolve mem_subset_full_set : wp_core.
  #[export] Hint Extern 3 => progress ltac2:(split_conjunctions ()) : wp_core.
(** * Definitions *)

Create HintDb wp_definitions.

(** * Alternative characterizations *)

Create HintDb wp_alt_chars.

(** * Classical logic *)

Create HintDb wp_classical_logic.
(* Taken care of by [wp_negation_logic] / [wp_negation_...] *)

(** * Logical negation  *)

Create HintDb wp_negation_logic.

  #[export] Hint Extern 1 => ltac2:(solve_by_manipulating_negation (fun () => ())) : wp_negation_logic.

(** * Constructive logic *)

Create HintDb wp_constructive_logic.

  #[export] Hint Resolve not_ex_all_not : wp_constructive_logic.
  #[export] Hint Resolve ex_not_not_all : wp_constructive_logic.
  #[export] Hint Resolve all_not_not_ex : wp_constructive_logic.

(** * Decidability based on classical epsilon*)

Create HintDb wp_decidability_epsilon.

  #[export] Hint Resolve excluded_middle_informative : wp_decidability_epsilon.
  #[export] Hint Resolve informative_or_lift : wp_decidability_epsilon.

(** * Classical logic decidability *)

Create HintDb wp_decidability_classical.

  #[export] Hint Resolve classic : wp_decidability_classical.

(** * Constructive decidability *)

Create HintDb wp_decidability_constructive.

  #[export] Hint Resolve make_sumbool_uninformative_1 : wp_decidability_constructive.
  #[export] Hint Resolve make_sumbool_uninformative_2 : wp_decidability_constructive.
  #[export] Hint Resolve make_sumtriad_uninformative_1 : wp_decidability_constructive.
  #[export] Hint Resolve make_sumtriad_uninformative_2 : wp_decidability_constructive.
  #[export] Hint Resolve make_sumtriad_uninformative_3 : wp_decidability_constructive.
  #[export] Hint Resolve make_sumtriad_uninformative_4 : wp_decidability_constructive.
  #[export] Hint Resolve make_sumtriad_uninformative_5 : wp_decidability_constructive.
  #[export] Hint Resolve make_sumtriad_uninformative_6 : wp_decidability_constructive.

(** * Natural numbers decidability *)

Create HintDb wp_decidability_nat.

  #[export] Hint Resolve Nat.eq_dec : wp_decidability_nat.
  #[export] Hint Extern 1 => lia : wp_decidability_nat.

(** * Real numbers decidability *)

Create HintDb wp_decidability_reals.

  (**
    Automatically unfold > to <so (_ > _) no longer has to occur in the options below.
    We cannot do the same for >= as it is not defined as <=.
  *)
  #[export] Hint Extern 1 => unfold Rgt : wp_decidability_reals.
  #[export] Hint Extern 1 => lra : wp_decidability_reals.

  #[export] Hint Resolve Req_EM_T : wp_decidability_reals.
  #[export] Hint Resolve Rlt_le_dec : wp_decidability_reals.
  #[export] Hint Resolve Rgt_ge_dec : wp_decidability_reals.

  (** Lemmas to write e.g. <<{r1 ≤ r2} + {~r2 ≥ r1}>> *)
  #[export] Hint Resolve Rlt_dec Rle_dec Rge_dec : wp_decidability_reals.
  #[export] Hint Resolve Rle_lt_dec Rge_gt_dec : wp_decidability_reals.
  #[export] Hint Resolve Rle_lt_or_eq_dec : wp_decidability_reals.
  #[export] Hint Resolve Rge_lt_or_eq_dec : wp_decidability_reals.

  (** <<x < y>>, <<x = y>> or <<y < x>> *)
  #[export] Hint Resolve total_order_T : wp_decidability_reals.

  (** lemmas to relate <= with >= and < with > *)
  #[export] Hint Resolve Rge_le : wp_decidability_reals.
  #[export] Hint Resolve Rle_ge : wp_decidability_reals.
  #[export] Hint Resolve Rgt_lt : wp_decidability_reals.
  #[export] Hint Resolve Rlt_gt : wp_decidability_reals.


(** * Real numbers' addition and multiplication *)

Create HintDb wp_eq_plus.
Create HintDb wp_eq_mult.

  (** x * y = y * x *)
  #[export] Hint Extern 1 => (rewrite Rmult_comm) : wp_eq_mult.

  (**
    Associativity
    We have the following associative properties
  *)

  (** <<x * y * z = x * (y * z)>> *)
  #[export] Hint Extern 1 => (rewrite Rmult_assoc) : wp_eq_mult.

  (** <<x * (y+z) = x * y + x * z>> *)
  #[export] Hint Extern 1 => (rewrite Rmult_plus_distr_l) : wp_eq_mult wp_eq_plus.

  (** <<(x+y) * z = x * z + y * z>> *)
  #[export] Hint Extern 1 => (rewrite Rmult_plus_distr_r) : wp_eq_mult wp_eq_plus.

  (** <<x + y = y + x>> *)
  #[export] Hint Extern 1 => (rewrite Rplus_comm) : wp_eq_plus.

  (** <<x + y + z = x + (y + z)>> *)
  #[export] Hint Extern 1 => (rewrite Rplus_assoc) : wp_eq_plus.

  (* <<(x + y) / z = x / z + y / z>> *)
  #[export] Hint Extern 1 => (rewrite Rdiv_plus_distr) : wp_eq_plus.

  #[export] Hint Extern 1 => (rewrite Rmult_plus_distr_l) : wp_eq_plus.
  #[export] Hint Extern 1 => (rewrite Rmult_plus_distr_r) : wp_eq_plus.


(** * Opposite number *)

Create HintDb wp_eq_opp.

  (** <<- (x - y) = y - x>> *)
  #[export] Hint Extern 1 => (rewrite Ropp_minus_distr) : wp_eq_opp.

  (** <<- (x * y) = - x * y>> *)
  #[export] Hint Extern 1 => (rewrite Ropp_mult_distr_l) : wp_eq_opp.

  (** <<- (x * y) = x * - y>> *)
  #[export] Hint Extern 1 => (rewrite Ropp_mult_distr_r) : wp_eq_opp.

  (** <<- x * y = - (x * y)>> *)
  #[export] Hint Extern 1 => (rewrite Ropp_mult_distr_l_reverse) : wp_eq_opp.

  (** <<x * - y = - (x * y)>> *)
  #[export] Hint Extern 1 => (rewrite Ropp_mult_distr_r_reverse) : wp_eq_opp.

  (** <<- (x + y) = - x + - y>> *)
  #[export] Hint Extern 1 => (rewrite Ropp_plus_distr) : wp_eq_opp.

  (** <<--a = a>> *)
  #[export] Hint Extern 1 => (rewrite Ropp_involutive) : wp_eq_opp.

  (** <<-a * -b = a * b>> *)
  #[export] Hint Extern 1 => (rewrite Rmult_opp_opp) : wp_eq_opp.

  (** <<- a / b = - (a / b)>> *)
  #[export] Hint Extern 1 => (rewrite Rdiv_opp_l) : wp_eq_opp.

  (** <<-a  + a = 0>> *)
  #[export] Hint Extern 1 => (rewrite Rplus_opp_l) : wp_eq_opp.

  (** <<a  + -a = 0>> *)
  #[export] Hint Extern 1 => (rewrite Rplus_opp_r) : wp_eq_opp.


(** * Real numbers' minus *)

Create HintDb wp_eq_minus.

  (** <<(x - y) / z = x / z - y / z>> *)
  #[export] Hint Extern 1 => (rewrite Rdiv_minus_distr) :  wp_eq_minus.

  #[export] Hint Extern 1 => (unfold Rminus) : wp_eq_minus.


(** * Simplification with 0 *)

Create HintDb wp_eq_zero.

  (** <<0 + x = x>> *)
  #[export] Hint Extern 1 => (rewrite Rplus_0_l) : wp_eq_zero.

  (** <<x + 0 = x>> *)
  #[export] Hint Extern 1 => (rewrite Rplus_0_r) : wp_eq_zero.

  (** <<0 - x = - x>> *)
  #[export] Hint Extern 1 => (rewrite Rminus_0_l) : wp_eq_zero.

  (** <<x - 0 = x>> *)
  #[export] Hint Extern 1 => (rewrite Rminus_0_r) : wp_eq_zero.

  (** <<0 * x = 0>> *)
  #[export] Hint Extern 1 => (rewrite Rmult_0_l) : wp_eq_zero.

  (** <<x * 0 = 0>> *)
  #[export] Hint Extern 1 => (rewrite Rmult_0_r) : wp_eq_zero.

  (** <<x ^ 0 = 1>> *)
  #[export] Hint Extern 1 => (rewrite pow_O) : wp_eq_zero.


(** * Simplification with 1 *)

Create HintDb wp_eq_one.

  (** <<1 * x = x>> *)
  #[export] Hint Extern 1 => (rewrite Rmult_1_l) : wp_eq_one.

  (** <<x * 1 = x>> *)
  #[export] Hint Extern 1 => (rewrite Rmult_1_r) : wp_eq_one.

  (** <<x / 1 = x>> *)
  #[export] Hint Extern 1 => (rewrite Rinv_1) : wp_eq_one.

  (** <<x ^ 1 = x>> *)
  #[export] Hint Extern 1 => (rewrite pow_1) : wp_eq_one.

  (** <</ / x = x>> *)
  #[export] Hint Extern 1 => (rewrite Rinv_inv) : wp_eq_one.


(** * Absolute value *)

Create HintDb wp_eq_abs.

  (** << ||a - a|| = 0 >> *)
  #[export] Hint Extern 1 => (rewrite R_dist_eq) : wp_eq_abs.

  (** << ||a * b - a * c|| = ||a|| * ||b - c|| >> *)
  #[export] Hint Extern 1 => (rewrite R_dist_mult_l) : wp_eq_abs.

  (** <<||a - b|| = ||b - a||>> *)
  #[export] Hint Extern 1 => (rewrite R_dist_sym) : wp_eq_abs.

  (** << |a - b| = |b - a|, using Rabs >> *)
  #[export] Hint Extern 1 => (rewrite Rabs_minus_sym) : wp_eq_abs.

  (** << | |a| | = |a| >> *)
  #[export] Hint Extern 1 => (rewrite Rabs_Rabsolu) : wp_eq_abs.

  (** << |-a| = |a| >> *)
  #[export] Hint Extern 1 => (rewrite Rabs_Ropp) : wp_eq_abs.

  (** << |a * b| = |a| * |b| >> *)
  #[export] Hint Extern 1 => (rewrite Rabs_mult) : wp_eq_abs.

  (** << a^2 = |a|^2 >> *)
  #[export] Hint Extern 1 => (rewrite Rsqr_abs) : wp_eq_abs.

  (** << sqrt(a^2) = |a| >> *)
  #[export] Hint Extern 1 => (rewrite sqrt_Rsqr_abs) : wp_eq_abs.

  (** << | a |^2 = a^2 >> *)
  #[export] Hint Extern 1 => (rewrite pow2_abs) : wp_eq_abs.


(** * Square root *)

Create HintDb wp_eq_sqr.

  (** << a² = a ^ 2 >> *)
  #[export] Hint Extern 1 => (rewrite Rsqr_pow2) : wp_eq_sqr.

  (** << (a-b)² = a² + b² + 2*a*b >> *)
  #[export] Hint Extern 1 => (rewrite Rsqr_plus) : wp_eq_sqr.

  (** << (a+b)*(a-b) = a² - b² >> *)
  #[export] Hint Extern 1 => (rewrite Rsqr_plus_minus) : wp_eq_sqr.

  (** << (a-b)² = a² + b² - 2*a*b >> *)
  #[export] Hint Extern 1 => (rewrite Rsqr_minus) : wp_eq_sqr.

  (** << (a-b)*(a+b) = a² - b² >> *)
  #[export] Hint Extern 1 => (rewrite Rsqr_minus_plus) : wp_eq_sqr.

  (** << a² = (-a)² >> *)
  #[export] Hint Extern 1 => (rewrite Rsqr_neg) : wp_eq_sqr.

  (** << (a-b)² = (b-a)² >> *)
  #[export] Hint Extern 1 => (rewrite Rsqr_neg_minus) : wp_eq_sqr.

  (** << (a*b)² = a² * b² >> *)
  #[export] Hint Extern 1 => (rewrite Rsqr_mult) : wp_eq_sqr.


(** * Exponential and logarithm *)

Create HintDb wp_eq_exp.

  (** << ln (exp a)) = a >> *)
  #[export] Hint Extern 1 => (rewrite ln_exp) : wp_eq_exp.

  (** << exp (-a) = / exp a>> *)
  #[export] Hint Extern 1 => (rewrite exp_Ropp) : wp_eq_exp.

  (** << exp(a+b) = exp(a) * exp(b) >> *)
  #[export] Hint Extern 1 => (rewrite exp_plus) : wp_eq_exp.

  (** << ln (exp a)) = a >> *)
  #[export] Hint Extern 1 => (rewrite ln_exp) : wp_eq_exp.


(** * Integers *)

Create HintDb wp_integers.

  #[export] Hint Extern 3 ( _ = _ ) => ring : wp_integers.
  #[export] Hint Extern 1 ( @eq nat _  _) => cbn; ltac2:(simpl_ineq_chains ()); lia : wp_integers.
  #[export] Hint Extern 1 ( le _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : wp_integers.
  #[export] Hint Extern 1 ( ge _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : wp_integers.
  #[export] Hint Extern 1 ( lt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : wp_integers.
  #[export] Hint Extern 1 ( gt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : wp_integers.
  #[export] Hint Resolve divide_char : wp_integers.
  #[export] Hint Resolve divide_char_inv : wp_integers.
  #[export] Hint Resolve even_of : wp_integers.
  #[export] Hint Resolve odd_of : wp_integers.
  #[export] Hint Resolve Zeven_char : wp_integers.
  #[export] Hint Resolve Zeven.Zeven_not_Zodd : wp_integers.
  #[export] Hint Resolve Zeven.Zodd_not_Zeven : wp_integers.
  #[export] Hint Extern 3 => apply Zeven_char_inv; assumption : wp_integers.
  #[export] Hint Resolve Zodd_char : wp_integers.
  #[export] Hint Extern 3 => apply Zodd_char_inv; assumption : wp_integers.
  #[export] Hint Resolve not_even_and_odd : wp_integers.
  #[export] Hint Resolve square : wp_integers.
  #[export] Hint Resolve perfect_square_of : wp_integers.
  #[export] Hint Resolve remainder_of : wp_integers.

Create HintDb wp_decidability_integers.
  #[export] Hint Resolve Zeven.Zeven_odd_dec : wp_decidability_integers.


(** * Integer negation *)

Create HintDb wp_negation_int.

  #[export] Hint Extern 1 => ltac2:(solve_by_manipulating_negation (fun () => ltac1:(lia))) : wp_negation_int.


(** * Natural number negation *)

Create HintDb wp_negation_nat.

  #[export] Hint Extern 1 => ltac2:(solve_by_manipulating_negation (fun () => ltac1:(lia))) : wp_negation_nat.


(** * Real numbers *)

Create HintDb wp_reals.
   (* TODO : at the moment we don't use this version of subsets... *)
  #[export] Hint Extern 2 => ltac2:(simpl_member_subset ()); lra : wp_reals.

  #[export] Hint Extern 1 (pred R _ _) => simpl; lra : wp_reals.

  #[export] Hint Extern 1 ( @eq R _ _ ) => field : wp_reals.

  #[export] Hint Extern 1 ( Rle _ _ ) => lra : wp_reals.
  #[export] Hint Extern 1 ( Rge _ _ ) => lra : wp_reals.
  #[export] Hint Extern 1 ( Rlt _ _ ) => lra : wp_reals.
  #[export] Hint Extern 1 ( Rgt _ _ ) => lra : wp_reals.

  #[export] Hint Extern 1 (~ (Rle _ _) ) => lra : wp_reals.
  #[export] Hint Extern 1 (~ (Rge _ _) ) => lra : wp_reals.
  #[export] Hint Extern 1 (~ (Rlt _ _) ) => lra : wp_reals.
  #[export] Hint Extern 1 (~ (Rgt _ _) ) => lra : wp_reals.
  #[export] Hint Extern 1 (~ (@eq R _ _ ) ) => lra : wp_reals.

  #[export] Hint Extern 2 ( @eq R _ _ ) => ltac2:(crush_R_abs_min_max_pruned ()): wp_reals.

  #[export] Hint Extern 2 ( Rle _ _ ) => ltac2:(crush_R_abs_min_max_pruned ()) : wp_reals.
  #[export] Hint Extern 2 ( Rge _ _ ) => ltac2:(crush_R_abs_min_max_pruned ()) : wp_reals.
  #[export] Hint Extern 2 ( Rlt _ _ ) => ltac2:(crush_R_abs_min_max_pruned ()) : wp_reals.
  #[export] Hint Extern 2 ( Rgt _ _ ) => ltac2:(crush_R_abs_min_max_pruned ()) : wp_reals.

  #[export] Hint Extern 3 (~ (Rle _ _) ) => cbn; ltac2:(crush_R_abs_min_max_pruned ()) : wp_reals.
  #[export] Hint Extern 3 (~ (Rge _ _) ) => cbn; ltac2:(crush_R_abs_min_max_lra ()) : wp_reals.
  #[export] Hint Extern 3 (~ (Rlt _ _) ) => cbn; ltac2:(crush_R_abs_min_max_lra ()) : wp_reals.
  #[export] Hint Extern 3 (~ (Rgt _ _) ) => cbn; ltac2:(crush_R_abs_min_max_lra ()) : wp_reals.
  #[export] Hint Extern 3 (~ (@eq R _ _ ) ) => cbn; ltac2:(crush_R_abs_min_max_lra ()) : wp_reals.

  #[export] Hint Extern 3 ( Rle _ _ ) => nra : wp_reals.
  #[export] Hint Extern 3 ( Rge _ _ ) => nra : wp_reals.
  #[export] Hint Extern 3 ( Rlt _ _ ) => nra : wp_reals.
  #[export] Hint Extern 3 ( Rgt _ _ ) => nra : wp_reals.

  #[export] Hint Resolve eq_sym : wp_reals.
  #[export] Hint Resolve false_Req : wp_reals.
  #[export] Hint Resolve true_Req : wp_reals.

  #[export] Hint Resolve Rmin_l : wp_reals.
  #[export] Hint Resolve Rmin_r : wp_reals.
  #[export] Hint Resolve Rmax_l : wp_reals.
  #[export] Hint Resolve Rmax_r : wp_reals.
  #[export] Hint Resolve Rle_max_compat_l : wp_reals.
  #[export] Hint Resolve Rle_max_compat_r : wp_reals.
  #[export] Hint Resolve Rmax_lub : wp_reals.
  #[export] Hint Resolve Rmax_lub_lt : wp_reals.
  #[export] Hint Resolve Rmax_left : wp_reals.
  #[export] Hint Resolve Rmax_right : wp_reals.
  #[export] Hint Resolve Rmin_left : wp_reals.
  #[export] Hint Resolve Rmin_right : wp_reals.
  #[export] Hint Resolve Rmin_glb : wp_reals.
  #[export] Hint Resolve Rmin_glb_lt : wp_reals.
  (** lemmas to relate <= with >= and < with > *)
  (* #[export] Hint Resolve Rge_le : wp_reals.*) (* This was really hampering performance *)
  #[export] Hint Resolve Rle_ge : wp_reals.
  (* #[export] Hint Resolve Rgt_lt : wp_reals.*)
  #[export] Hint Resolve Rlt_gt : wp_reals.

  #[export] Hint Resolve div_sign_flip : wp_reals.
  #[export] Hint Resolve div_pos : wp_reals.
  #[export] Hint Resolve inv_remove : wp_reals.
  #[export] Hint Resolve Rinv_inv : wp_reals.
  #[export] Hint Resolve Rabs_def1 : wp_reals.
  #[export] Hint Resolve Rabs_le : wp_reals.
  #[export] Hint Resolve Rabs_left : wp_reals.
  #[export] Hint Resolve Rabs_minus_sym : wp_reals.
  #[export] Hint Resolve Rabs_right : wp_reals.
  #[export] Hint Resolve Rabs_left1 : wp_reals.
  #[export] Hint Resolve Rabs_left1_with_minus : wp_reals.
  #[export] Hint Resolve Rabs_pos_lt : wp_reals.
  #[export] Hint Resolve Rabs_Rabsolu : wp_reals.
  #[export] Hint Resolve Rabs_zero : wp_reals.
  #[export] Hint Resolve Rle_abs : wp_reals.
  #[export] Hint Resolve Rabs_pos : wp_reals.
  #[export] Hint Resolve Rle_abs_min : wp_reals.
  #[export] Hint Resolve Rge_min_abs : wp_reals.
  #[export] Hint Resolve Rmax_abs : wp_reals.
  #[export] Hint Resolve Rinv_0_lt_compat : wp_reals.
  #[export] Hint Resolve Rplus_lt_compat : wp_reals.
  #[export] Hint Resolve Rplus_lt_le_compat : wp_reals.

  #[export] Hint Resolve mult_neq_zero : wp_reals.
  #[export] Hint Resolve div_non_zero : wp_reals.
  #[export] Hint Resolve R1_neq_R0 : wp_reals.

  #[export] Hint Extern 1 => rewrite Rabs_zero : wp_reals.

  #[export] Hint Resolve plus_Z_in_R : wp_reals.
  #[export] Hint Resolve minus_Z_in_R : wp_reals.
  #[export] Hint Resolve mult_Z_in_R : wp_reals.
  #[export] Hint Resolve neg_Z_in_R : wp_reals.
  #[export] Hint Resolve zero_Z_in_R : wp_reals.
  #[export] Hint Resolve one_Z_in_R : wp_reals.
  #[export] Hint Resolve two_Z_in_R : wp_reals.

  #[export] Hint Extern 1 => rewrite INR_0 : wp_reals.
  #[export] Hint Extern 1 => rewrite INR_1 : wp_reals.
  #[export] Hint Resolve ge_zero_gt_one : wp_reals.
  #[export] Hint Extern 1 => apply le_INR : wp_reals.

  #[export] Hint Extern 1 => eapply rational_of : wp_reals.

  #[export] Hint Resolve int_is_rational : wp_reals.
  #[export] Hint Resolve sum_is_rational : wp_reals.
  #[export] Hint Resolve diff_is_rational : wp_reals.
  #[export] Hint Resolve mult_is_rational : wp_reals.
  #[export] Hint Resolve div_is_rational : wp_reals.
  #[export] Hint Resolve neg_is_rational : wp_reals.

  #[export] Hint Resolve plus_frac : wp_reals.
  #[export] Hint Resolve min_frac : wp_reals.
  #[export] Hint Resolve Rdivid_ineq_interchange : wp_reals.

  #[export] Hint Resolve archimedN_exists : wp_reals.

  #[export] Hint Resolve sqrt_lt_R0 : wp_reals.
  #[export] Hint Resolve Rsqr_sqrt : wp_reals.
  #[export] Hint Resolve Rlt_le : wp_reals.
  #[export] Hint Resolve Rsqr_plus_minus : wp_reals.
  #[export] Hint Resolve Rsqr_neg : wp_reals.

(** * Real number negation *)

Create HintDb wp_negation_reals.

#[export] Hint Extern 3 => ltac2:(solve_by_manipulating_negation (fun () => ltac1:(lra))) : wp_negation_reals.
(* Stricly speaking not about negation, but is needed in the shorten database*)
#[export] Hint Resolve Rmult_integral : wp_negation_reals.


(** * Sets *)

Create HintDb wp_sets.

  #[export] Hint Resolve left_in_closed_open : wp_sets.
  #[export] Hint Constructors Union Intersection Disjoint Full_set : wp_sets.
  #[export] Hint Resolve power_set_characterization : wp_sets.
  #[export] Hint Resolve power_set_characterization_alt : wp_sets.
  #[export] Hint Extern 1 => apply empty_set_characterization; eassumption : wp_sets.
  #[export] Hint Resolve not_in_empty : wp_sets.
  #[export] Hint Resolve set_difference_elim : wp_sets.
  #[export] Hint Resolve Extensionality_Ensembles : wp_sets.

  #[export] Hint Resolve Closed : wp_sets.
  #[export] Hint Resolve Open : wp_sets.
  #[export] Hint Resolve Closed_Open : wp_sets.
  #[export] Hint Resolve Open_Closed : wp_sets.

  #[export] Hint Extern 1 => apply intersection_characterization; assumption : wp_sets.
  #[export] Hint Extern 1 => apply intersection_characterization_left; assumption : wp_sets.
  #[export] Hint Extern 1 => apply union_characterization; assumption : wp_sets.
  #[export] Hint Extern 1 => apply union_characterization_left; assumption : wp_sets.

  #[export] Hint Extern 1 => eapply index_intersection_elim; eassumption : wp_sets.
  #[export] Hint Extern 2 => eapply index_intersection_elim_left; eassumption : wp_sets.

  #[export] Hint Extern 1 => eapply index_union_elim; eassumption : wp_sets.
  #[export] Hint Extern 2 => eapply index_union_elim_left; eassumption : wp_sets.

  (** * Function image hints *)
  #[export] Hint Resolve in_image_intro : wp_sets.
  #[export] Hint Resolve in_image_elim : wp_sets.

  (** * Function preimage hints *)
  #[export] Hint Resolve in_preimage_intro : wp_sets.
  #[export] Hint Resolve in_preimage_elim : wp_sets.

  (** * Function preimage translation hints *)
  #[export] Hint Resolve preimage_of_mem : wp_sets.
  #[export] Hint Resolve mem_of_preimage : wp_sets.

  #[export] Hint Resolve bijective_is_injective : wp_sets.
  #[export] Hint Resolve bijective_is_surjective : wp_sets.

  (** * Left inverse hints *)
  #[export] Hint Resolve left_inverse_elim : wp_sets.
  #[export] Hint Resolve left_inverse_intro : wp_sets.

  (** * Right inverse hints *)
  #[export] Hint Resolve right_inverse_elim : wp_sets.
  #[export] Hint Resolve right_inverse_intro : wp_sets.

  (** * Inverse hints *)
  #[export] Hint Resolve inverse_is_left_inverse : wp_sets.
  #[export] Hint Resolve inverse_is_right_inverse : wp_sets.
  #[export] Hint Resolve inverse_elim_left : wp_sets.
  #[export] Hint Resolve inverse_elim_right : wp_sets.
  #[export] Hint Resolve inverse_intro : wp_sets.

(** * Intuition *)

Create HintDb wp_intuition.

  #[export] Hint Extern 8 => intuition (auto 2 with core): wp_intuition.

Create HintDb wp_prop_logic.

  #[export] Hint Extern 1 => eapply proj1; eassumption : wp_prop_logic.
  #[export] Hint Extern 1 => eapply proj2; eassumption : wp_prop_logic.
  #[export] Hint Extern 1 => apply conj; assumption : wp_prop_logic.
  #[export] Hint Extern 1 => apply or_introl; assumption : wp_prop_logic.
  #[export] Hint Extern 1 => apply or_intror; assumption : wp_prop_logic.

Create HintDb wp_first_order_logic.

  #[export] Hint Extern 1 => apply alternative_char_unique_exists : wp_first_order_logic.
