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
Require Import Ltac2.Message.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").

Require Import Util.Binders.
Require Import Util.Constr.
Require Import Util.Evars.
Require Import Util.Goals.
Require Import Util.Hypothesis.
Require Import Util.MessagesToUser.

Require Import Notations.Sets.

(* Lemma to write Sn in goal induction step as n+1. *)
Lemma Sn_eq_nplus1 : forall n, S n = n + 1.
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Open Scope subset_scope.

(**
  The induction principle we would like to use
  with sealed notations.
*)
Lemma induction_principle_elements {P : nat -> Prop} :
    P 0 -> (∀ k ∈ nat, P k -> P (k + 1)) ->
    ∀ k ∈ nat, P k.
Proof.
  intros H_base IH k k_in_nat.
  induction k as [| k IHk].
  - exact H_base.
  - rewrite Sn_eq_nplus1.
    apply IH.
    + exact I.
    + apply IHk.
      exact I.
Qed.

(** * induction_without_hypothesis_naming
    Performs mathematical induction.

    Arguments:
        - [x: ident], the variable to perform the induction on.

    Does:
        - performs induction on [x].
        - If [x] is a natural number, the first goal is wrapped in
          NaturalInduction.Base.Wrapper and the second goal is wrapped in
          NaturalInduction.Step.Wrapper.
        - Otherwise, the resulting cases are wrapped in the StateGoal.Wrapper.

*)
Ltac2 induction_without_hypothesis_naming (x: ident) :=
  lazy_match! Control.goal () with
  | ∀ _ ∈ conv nat, _ =>
      check_binder_warn (Control.goal ()) x true;
      apply induction_principle_elements;
      Control.focus 1 1 (fun () => apply NaturalInduction.Base.unwrap);
      Control.focus 2 2 (fun () =>
        let stmt :=
          change_binder_name_under_seal (Control.goal ()) x in
        change $stmt;
        apply NaturalInduction.Step.unwrap)
  | forall _ : nat, _ =>
      check_binder_warn (Control.goal ()) x true;
      intro $x;
      let x_hyp := Control.hyp x in
      let ih_x := Fresh.in_goal @_IH in
      induction $x_hyp as [| $x $ih_x];
      Control.focus 1 1 (fun () =>
        apply NaturalInduction.Base.unwrap);
      Control.focus 2 2 (fun () =>
        rewrite Sn_eq_nplus1;
        revert $ih_x;
        revert $x;
        apply NaturalInduction.Step.unwrap)
  | _ =>
    throw (of_string "Cannot apply natural induction on this goal.")
  end.

(* Quick fix for Wateproof editor / Rocq lsp, where
  [We use induction on

   Qed.]
  was interpreted [We use induction on Qed.].
  Although in Rocq [Qed] is acceptable as variable name, it is confusing.
  Hence we throw an error in the form of a 'Syntax error'.

  TODO: can probably be fixed with binders...
*)
Local Ltac2 panic_ident_Qed (i : ident) :=
  if Ident.equal i @Qed
    then throw (of_string "Syntax error: variable name expected after 'on'.")
    else ().

Ltac2 Notation "We" "use" "induction" "on" x(ident) :=
  panic_ident_Qed (x);
  panic_if_goal_wrapped ();
  induction_without_hypothesis_naming x.

(** *
    Removes the NaturalInduction.Base.Wrapper.

    Arguments:
        - [t : constr], goal that is wrapped

    Does:
        - removes the NaturalInduction.Base.Wrapper from the goal

    Raises fatal exceptions:
        - If the [goal] is the type [t] wrapped in the base case wrapper,
          i.e. the goal is not of the form [NaturalInduction.Base.Wrapper t].
*)
Ltac2 base_case (t:constr) :=
  lazy_match! goal with
    | [|- NaturalInduction.Base.Wrapper ?v] =>
      match Constr.equal v t with
        | true => apply (NaturalInduction.Base.wrap)
        | false => throw (of_string "Wrong goal specified.")
      end
    | [|- _] => throw (of_string "No need to indicate showing a base case.")
  end.

Ltac2 Notation "We" "first" "show" "the" "base" "case" t(lconstr) := base_case t.

(** *
    Removes the NaturalInduction.Step.Wrapper.

    Arguments: none

    Does:
        - removes the NaturalInduction.Step.Wrapper from the goal

    Raises fatal exceptions:
        - If the [goal] is not wrapped in the induction step case wrapper,
          i.e. the goal is not of the form [NaturalInduction.Step.Wrapper G] for some type [G].
*)
Ltac2 induction_step () :=
  lazy_match! goal with
    | [|- NaturalInduction.Step.Wrapper _] => apply (NaturalInduction.Step.wrap)
    | [|- _] => throw (of_string "No need to indicate showing an induction step.")
  end.

Ltac2 Notation "We" "now" "show" "the" "induction" "step" := induction_step ().