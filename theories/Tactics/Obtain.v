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

Require Import Util.Init.
Local Ltac2 get_type (x: constr) : constr := eval unfold type_of in (type_of $x).

Require Import Notations.Sets.

Require Import Util.Binders.
Require Import Util.Goals.
Require Import Util.MessagesToUser.

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

Local Ltac2 rec destruct_and (hyp : ident) :=
  let hyp_c := Control.hyp hyp in
  match! (Constr.type hyp_c) with
  | (_ /\ _) =>
    let w := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
    destruct $hyp_c as [$w $hyp];
    unfold ge_op, R_ge_type, nat_ge_type, gt_op, R_gt_type,
      nat_gt_type, subset_type in $w;
    destruct_and hyp
  | _ => ()
  end.


(** *
  Attempts to obtain a variable from a user-specified statement.

  Arguments:
    - [var : ident], the name of the variable to be obtained.
    - [hyp : ident], label of the statement the variable should be obtained from.
  Does:
    - Destructs the statement [hyp] into the variable [var] and its corresponding property.
    - Copies the statement [hyp] into a new statement with the same label [hyp]
      to preserve the statement despite its destruction.

  Returns:
    - the name of the new hypothesis.

  Raises exceptions:
    - [ObtainError], if no statement to destruct or if the previous statement was not an
      existence statement or a sigma type.
*)
Ltac2 obtain_according_to (var : ident) (hyp : ident) :=
  let h := Control.hyp hyp in
  let type_h := get_type h in
  match! type_h with
  | seal _ _ => unfold seal at 1 in $hyp
  | _ => ()
  end;
  let h := Control.hyp hyp in
  let type_h := get_type h in
  lazy_match! type_h with
  | ex  ?pred =>
    check_binder_warn pred var true
  | sig ?pred =>
    check_binder_warn pred var true
  | _ => throw (concat_list
    [of_string "Couldn't obtain "; of_ident var; of_string "."; fnl ();
     of_string "There aren't enough variables to obtain."])
  end;
  destruct $h as [$var $hyp];
  unfold subset_type in $var;
  destruct_and hyp.

  (* TODO: older code, was stricter on when to destruct,
    but new code seems more user-friendly *)
  (* match! Constr.type h with
  | (* TODO: check if agree: now immediately destruct 'and' statements *)
    (* ((pred _ _) ?a) /\ _ =>
    let var_constr := Control.hyp var in
    let w := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
    if Constr.equal var_constr a then
      destruct $h as [$w $hyp]
    else () *)
  | _ => ()
  end.*)

(* Quick fix for Wateproof editor / Rocq lsp, where
  [Obtain such an

   Qed.]
  was interpreted [Obtain such an Qed.].
  Although in Rocq [Qed] is acceptable as variable name, it is confusing.
  Hence we throw an error in the form of a 'Syntax error'.

  TODO: can probably be fixed with binders...
*)
Local Ltac2 panic_ident_Qed (i : ident) :=
  if Ident.equal i @Qed
    then throw (of_string "Syntax error: variable name expected after 'such'.")
    else ().

(** *
  Attempts to obtain variables from the indicated statement.

  Arguments:
    - [vars : ident list], the names of the variable to be obtained.
    - [hyp : ident], the label of the statement the variables should be obtained from.
  Does:
    - Destructs the statement [hyp] into the variables [vars] and their corresponding property.
    - Copies the previous statement into a new statement with the same identifier
      to preserve the statement despite its destruction.

  Raises fatal exceptions:
    - If no statement to destruct for the given
      amount of variables or if the previous statement was not an
      existence statement or a sigma type.
*)
Ltac2 obtain_seq_according_to (vars : ident list) (hyp) :=
  (* make a copy of the original proposition *)
  let prop_label := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
  let og_term := Control.hyp hyp in
  let pre_og_type := get_type og_term in
  let og_type :=
    match! pre_og_type with
    | seal _ _ => eval unfold seal at 1 in $pre_og_type
    | _ => pre_og_type
    end in
  lazy_match! og_type with
  | ex  _ => ()
  | sig _ => ()
  | _ => throw (concat_list
    [of_string "Can only obtain variables from 'there exists...' statements."])
  end;
  assert $pre_og_type as $prop_label;
  Control.focus 1 1 (fun () => exact $og_term);
  List.iter
    (fun var =>
      panic_ident_Qed var;
      try_out_label var;
      obtain_according_to var hyp) vars;
  Std.rename [(prop_label, hyp); (hyp, prop_label)].

(** *
  Attempts to obtain variables from the previous statement.

  Arguments:
    - [vars : ident list], the names of the variable to be obtained.
  Does:
    - Destructs the previous statement into the variables [vars] and their corresponding property.
    - Copies the previous statement into a new statement with the same identifier
      to preserve the statement despite its destruction.

  Raises fatal exceptions:
    - If no statement to destruct or if the previous statement was not an
      existence statement or a sigma type.
*)

Ltac2 obtain_according_to_last (vars : ident list) :=
  lazy_match! goal with
  | [id_h : _ |- _ ] =>
    let h := Control.hyp id_h in
    let pre_type_h := get_type h in
    let type_h :=
      match! pre_type_h with
      | seal _ _ => eval unfold seal at 1 in $pre_type_h
      | _ => pre_type_h
      end in
    lazy_match! type_h with
    | ex  _ =>
      obtain_seq_according_to vars id_h
    | sig _ => obtain_seq_according_to vars id_h
    | _ => throw (of_string
      "Previous statement is not of the form 'there exists ...'.")
    end
  | [ |- _] => throw (of_string
    "No statement to obtain variable from.")
  end.

Ltac2 Notation "Obtain" "such" _(opt("a")) _(opt("an"))
    vars(list1(ident, ",")) :=
  panic_if_goal_wrapped ();
  obtain_according_to_last vars.

Ltac2 Notation "Obtain" vars(list1(ident, ",")) "according" "to"
    hyp(seq("(", ident, ")")):=
  panic_if_goal_wrapped ();
  obtain_seq_according_to vars hyp.
