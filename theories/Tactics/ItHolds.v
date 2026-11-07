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

Require Import Util.Constr.
Require Import Util.Goals.
Require Import Util.Hypothesis.
Require Import Util.Init.
Require Import Util.BySince.
Require Import Util.MessagesToUser.
Require Import Util.TypeCorrector.
Require Import Waterprove.

Require Import Waterproof.Tactics.HelpNewHyp.
Require Import Notations.Sets.


(** Tries to make the assertion [True] with label [label].
  Throws an error if this fails, i.e. if the label is already used
  for another one of the hypotheses.

  This check was separated out from the 'assert'-tactics below because the
  '[label] is already used error' would otherwise be caught in
  the code meant to catch [AutomationFailure] errors. *)

Local Ltac2 try_out_label (label : ident) :=
  match Control.case (fun () =>
    assert True as $label by exact I)
  with
  | Err exn => Control.zero exn
  | Val _ => clear $label
  end.

(** Simple version of a waterproof assert tactic.

  We have added this to be able to use an assert tactic
  that doesn't throw a fatal error, which is useful
  in the expand framework.

  Arguments:
  - [claim]: the claim to assert.

  Throws:
  - [FailedToProve] if [waterprove] fails to prove that [claim] holds.
*)
Ltac2 wp_assert_base (claim : constr) :=
  let claim := correct_type_by_wrapping claim in
  assert $claim by (waterprove 5 true Main).

(** Attempts to assert that [claim] holds, if succesful [claim] is added to the local
  hypotheses. If [label] is specified [claim] is given [label] as its identifier, otherwise an
  identifier starting with '_H' is generated.

  Additionally, if argument [postpone] is [true], actually proving the claim is postponed.
  The claim is asserted and the proof is given up on using admit.
  *)
Local Ltac2 wp_assert (claim : constr) (label : ident option) (postpone : bool):=
  let err_msg (g : constr) := concat_list
    [of_string "Could not verify that "; of_constr g; of_string "."] in
  let id :=
    match label with
    | None => Fresh.in_goal @_H
    | Some label => try_out_label label; label
    end
  in
  let claim := correct_type_by_wrapping claim in
  if postpone
    then
      assert $claim as $id;
      Control.focus 1 1 (fun () =>
        admit
        );
      warn (concat_list [of_string "Please come back later to provide an actual proof of ";
        of_constr claim; of_string "."])

    else
      (* Assert claim and attempt to prove automatically *)
      match Control.case (fun () =>
        assert $claim as $id by
          (waterprove 5 true Main))
      with
      | Val _ => ()
      | Err (FailedToProve g) => throw (err_msg g)
      | Err exn => Control.zero exn
      end;
  (* Print suggestion on how to use new statement. *)
  HelpNewHyp.suggest_how_to_use claim label.

(** Attempts to assert that [claim] holds, if succesful [claim] is added to the local
  hypotheses. If [label] is specified [claim] is given [label] as its identifier, otherwise an
  identifier starting with '_H' is generated.
  [xtr_lemma] has to be used in the proof that [claim] holds.
  *)
Local Ltac2 core_wp_assert_by (claim : constr) (label : ident option) (xtr_lemmas : constr list) (dbs : hint_db_name list) :=
  let err_msg (g : constr) := concat_list
    [of_string "Could not verify that "; of_constr g; of_string "."] in
  let id :=
    match label with
    | None => Fresh.in_goal @_H
    | Some label => try_out_label label; label
    end
  in
  let claim := correct_type_by_wrapping claim in
  match Control.case (fun () =>
    assert $claim as $id by
      (rwaterprove 5 true Main xtr_lemmas dbs))
  with
  | Val _ => ()
  | Err (FailedToProve g) => throw (err_msg g)
  | Err exn => Control.zero exn (* includes FailedToUse error *)
  end.



(** Adaptation of [core_wp_assert_by] that turns the [FailedToUse] errors
  which might be thrown into user readable errors. *)
Local Ltac2 wp_assert_by (claim : constr) (label : ident option) (xtr_lemmas : constr list) (xtr_dbs : hint_db_name list) :=
  wrapper_core_by_tactic (core_wp_assert_by claim label) xtr_lemmas xtr_dbs;
  (* Print suggestion on how to use new statement. *)
  HelpNewHyp.suggest_how_to_use claim label.

(** Adaptation of [core_wp_assert_by] that allows user to use mathematical statements themselves
  instead of references to them as extra information for the automation system.
  Uses the code in [Since.v]. *)
Local Ltac2 wp_assert_since (claim : constr) (label : ident option) (xtr_claim : constr) :=
  since_framework (core_wp_assert_by claim label) xtr_claim;
  (* Print suggestion on how to use new statement. *)
  HelpNewHyp.suggest_how_to_use claim label.


(**
  Attempts to assert a claim and proves it automatically using a specified lemma,
  this lemma has to be used.

  Arguments:
    - [xtr_lemma: constr], reference to a lemma used to prove the claim (via [rwaterprove]).
    - [label: ident option], optional name for the claim.
        If the proof succeeds, it will become a hypothesis (bearing [label] as name).
    - [claim: constr], the actual content of the claim to prove.

    Raises exception:
    - (fatal) if [rwaterprove] fails to prove the claim using the specified lemma.
    - [[label] is already used], if there is already another hypothesis with identifier [label].
*)
Ltac2 wp_assert_by_with_checks (claim : constr) (label : ident option) (xtr_lemmas : constr list) (xtr_dbs : hint_db_name list) :=
  panic_if_goal_wrapped ();
  wp_assert_by claim label xtr_lemmas xtr_dbs.


(** Attempts to prove that proposed goal is enough to show current goal,
  given an additional lemma that has to be used in said proof.
  If succesful, replaces current goal by proposed goal. *)

Ltac2 Notation "Since" xtr_claim(lconstr) "it" "holds" "that" claim(lconstr) label(opt(seq("as", "(", ident, ")"))) :=
  panic_if_goal_wrapped ();
  wp_assert_since claim label xtr_claim.

(** * It holds that ... (...)
  Attempts to assert a claim and proves it automatically.
  Removes [StateHyp.Wrapper] wrapper from the goal (proving claim by automation not necessary).

  Arguments:
    - [label: ident option], optional name for the claim.
        If the proof succeeds, it will become a hypothesis (bearing [label] as name).
    - [claim: constr], the actual content of the claim to prove.

    Raises exception:
    - (fatal) if [rwaterprove] fails to prove the claim using the specified lemma.
    - [[label] is already used], if there is already another hypothesis with identifier [label].
    - (fatal) If goal is wrapped in [StateHyp.Wrapper] and the wrong statement is specified.
*)
Local Ltac2 wp_assert_with_unwrap (claim : constr) (label : ident option) :=
  (* Try out label first.
    Code results in wrong error if done inside repeated match.. *)
  match label with | None => () | Some label => try_out_label label end;

  lazy_match! goal with
  | [_ : ?s |- StateHyp.Wrapper ?s _ _] =>
    if Bool.neg (check_constr_equal s claim) then
      throw (of_string "Wrong statement specified.")
    else
      match! goal with
      | [h : ?s |- StateHyp.Wrapper ?s ?h_spec _] =>
        let h_constr := Control.hyp h in
        (* sanity check "h = h_spec" *)
        if check_constr_equal h_constr h_spec then ()
          else fail;
        let w := match label with
          | None => Fresh.fresh (Fresh.Free.of_goal ()) @_H
          | Some label => label
          end in
        match Control.case (fun () => assert $claim as $w by exact $h_constr) with
        | Val _ =>
          apply (StateHyp.wrap $s);
          Std.clear [h]
        | Err exn => print (of_string "Exception occurred"); print (of_exn exn)
        end
      (* rename ident generated in specialize with user-specified label*)
      (* match label with
      | None => ()
      | Some label => Std.rename [(w, label)]
      end *)
      end
  | [|- _] =>
    panic_if_goal_wrapped ();
    wp_assert claim label false
  end.

Ltac2 Notation "It" "holds" "that" claim(lconstr) label(opt(seq("as", "(", ident, ")")))  :=
  wp_assert_with_unwrap claim label.


(** * By magic it holds that ... (...)
  Asserts a claim and gives up on proof using admit.

  Arguments:
    - [label: ident option], optional name for the claim.
    - [claim: constr], the actual content of the claim to prove.

    Raises exception:
    - [[label] is already used], if there is already another hypothesis with identifier [label].

    Raises warning:
    - [Please come back later to provide an actual proof of [claim].], always.
*)

Ltac2 Notation "By" "magic" "it" "holds" "that" claim(lconstr) label(opt(seq("as", "(", ident, ")"))) :=
  panic_if_goal_wrapped ();
  wp_assert claim label true.
