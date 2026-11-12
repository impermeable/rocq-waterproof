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


(**
Shared code for the 'Since ...' and 'By ...' prefix clauses for tactics like 'It holds that ...' or 'We conclude that ...'
*)



Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").

Require Import Util.Constr.
Require Import Util.MessagesToUser.
Require Import Waterprove.

Require Import Util.Init.
Require Import Util.TypeCorrector.
Require Import Notations.Sets.

Local Ltac2 check_if_not_reference (x : constr) :=
  let type_x := Constr.type x in
  lazy_match! type_x with
  | Prop => ()
  | Set => ()
  | Type => ()
  | bool => ()
  | _ => throw (concat_list
        [of_string "Cannot use reference "; of_constr x; of_string " with `Since`.
Try `By "; of_lconstr x; of_string " ...` instead."])
  end.

Local Ltac2 check_if_not_statement (x : constr) :=
  let err_msg := concat_list
    [of_string "Cannot use statement "; of_constr x; of_string " with `By`.
Try `Since "; of_lconstr x; of_string " ...` instead."]
  in
  let type_x := Constr.type x in
  lazy_match! type_x with
  | Prop => throw err_msg
  | Set => throw err_msg
  | Type => throw err_msg
  | bool => throw err_msg
  | _ => ()
  end.


(** Attempts to prove [claimed_cause] with minimal automation,
  and then executes [by_tactic] with the proof of [claimed_cause]
  as an argument.
  Expects that [by_tactic] can throw a [(Waterprove.)FailedToUse] error,
  those errors are caught; the extra lemma that the automation failed to use
  is used in a new error that is thrown.
*)

Ltac2 since_framework (by_tactic : constr list -> hint_db_name list -> unit) (claimed_cause : constr) :=
  (* first, check if [claimed_cause] is a statement. *)
  check_if_not_reference claimed_cause;
  (* Wrap in is_true if needed *)
  let claimed_cause := correct_type_by_wrapping claimed_cause in

  let id_cause := Fresh.in_goal @_temp in
  (* attempt to prove [claimed_cause]*)
  match Control.case (fun () =>
    let unsealed_claimed_cause := eval unfold seal in $claimed_cause in
    assert $unsealed_claimed_cause as $id_cause by
      (waterprove 1 true Shorten))
  with
  | Err (FailedToProve _) =>
    throw (concat_list
      [of_string "State that "; of_constr claimed_cause; of_string " holds";
       of_string " before using it in `Since ...`."])
  | Err exn => Control.zero exn
  | Val _ =>
    (* use proof of [claimed_cause] in [by_tactic] *)
    let cause := Control.hyp id_cause in
    match Control.case (fun () =>
      by_tactic [cause] [])
    with
    | Val _ => clear $id_cause
    | Err (FailedToUse _) =>
      clear $id_cause;
      throw (concat_list
        [of_string "Could not verify this follows from "; of_constr claimed_cause; of_string "."])
    | Err exn => clear $id_cause; Control.zero exn
    end
  end.

(** Returns [true] if [x] is a reference (a local variable, a constant, a constructor or
  an inductive type) possibly applied to (implicit) arguments that are all evars.
  This is similar to the check in Rocq when building hints from a "using" clause. *)
Local Ltac2 is_reference (x : constr) : bool :=
  let is_ref_head (h : constr) :=
    match Constr.Unsafe.kind h with
    | Constr.Unsafe.Var _ => true
    | Constr.Unsafe.Constant _ _ => true
    | Constr.Unsafe.Constructor _ _ => true
    | Constr.Unsafe.Ind _ _ => true
    | _ => false
    end in
  match Constr.Unsafe.kind x with
  | Constr.Unsafe.App h args =>
    Bool.and (is_ref_head h)
      (Array.for_all (fun a => match Constr.Unsafe.kind a with
                               | Constr.Unsafe.Evar _ _ => true
                               | _ => false end) args)
  | _ => is_ref_head x
  end.

(** Adds [xtr_lemma] (a proof term) to the local hypotheses, with statement [statement],
  and returns the identifier of the new hypothesis. *)
Local Ltac2 add_lemma_as_hyp (xtr_lemma : constr) (statement : constr) : ident :=
  let aux_id := Fresh.fresh (Fresh.Free.of_goal ()) @_aux in
  assert $statement as $aux_id;
  Control.focus 1 1 (fun () => exact $xtr_lemma);
  aux_id.

Ltac2 unseal_lemma (xtr_lemma : constr) : ident :=
  let aux_id := Fresh.fresh (Fresh.Free.of_goal ()) @_aux in
  let statement_xtr_lemma := Constr.type xtr_lemma in
  let unsealed_statement := eval unfold seal in $statement_xtr_lemma in
  assert $unsealed_statement as $aux_id;
  Control.focus 1 1 (fun () => exact $xtr_lemma);
  aux_id.

(** Wrapper for the main functionality of 'By ...'-tactics,
  such that the main fucntionality can be reused in 'Since ...'-tactics.

  Checks whether [xtr_lemma] is not a statement (i.e. not a Prop/Set/Type) and
  catches [(Waterprove.)FailedToUse] errors to turn them into user-readable errors. *)
Ltac2 wrapper_core_by_tactic (by_tactic : constr list -> hint_db_name list -> unit)
  (xtr_lemmas : constr list) (xtr_dbs : hint_db_name list) :=
  List.iter check_if_not_statement xtr_lemmas;
  (* check if necessary to unseal. Because we are adding to the local
    hypothesis if we need to unseal, this interferes with our
    capability to check whether a lemma is used... *)
  (* TODO: does this need to move away from here? *)
  let unseal_and_record (xtr_lemma : constr) :=
    (let xtr_lemma_contains_seal :=
      match! (Constr.type xtr_lemma) with
      | context [seal _ _ ] => true
      | _ => false
      end in
    if xtr_lemma_contains_seal then
      (let aux_id := unseal_lemma xtr_lemma in
      (Some aux_id, Control.hyp aux_id))
    else if Bool.or (is_reference xtr_lemma) (Constr.has_evar xtr_lemma) then
      (None, xtr_lemma)
    else
      (* Non-reference terms such as [(H x Hx)] are also added to the local
        hypotheses: Rocq deprecates non-reference terms in the "using"
        clauses of its hint machinery (warning [non-reference-hint-using]),
        and as hypotheses they are in addition visible to automation that
        only inspects the context (e.g. [lra], [nra]). *)
      (let aux_id := add_lemma_as_hyp xtr_lemma (Constr.type xtr_lemma) in
      (Some aux_id, Control.hyp aux_id)))
    in
  let unsealed_and_recorded := List.map unseal_and_record xtr_lemmas in
  let (opt_ids, aux_lemmas) := List.split unsealed_and_recorded in
  match Control.case (fun () => by_tactic aux_lemmas xtr_dbs) with
  | Val _ => ()
  | Err (FailedToUse _) => throw (concat_list
      [of_string "Could not verify this follows from the provided reasons."])
  | Err exn => Control.zero exn
  end;
  Std.clear (List.map_filter (fun id => id) opt_ids).
