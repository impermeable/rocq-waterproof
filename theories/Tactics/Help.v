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

From Waterproof Require Import Util.Constr.
From Waterproof Require Import Util.Goals.
From Waterproof Require Import Util.Hypothesis.
From Waterproof Require Import Util.MessagesToUser.
From Waterproof Require Import HelpNewHyp.
From Waterproof Require Import Tactics.Unfold.

Require Import Notations.Sets.
Require Import Waterprove.
Open Scope subset_scope.

Local Ltac2 goal_impl_msg (premise: constr) :=
  info_notice (concat_list [of_string "The goal is to show an implication (⇒). Assume the premise "; of_constr premise; of_string "."]);
  replace_msg "Assume that ...." "Assume that ${0:0 = 0}.${1}".

Local Ltac2 goal_func_msg (var_type: constr) :=
  info_notice (concat_list [of_string "The goal is to construct a map (⇒). Introduce an arbitrary variable of type "; of_constr var_type; of_string "."]);
  replace_msg "Take ... : ...." "Take ${0:x} : ${1:X}.${2}".

Local Ltac2 goal_forall_msg (var_type: constr) :=
  info_notice (concat_list [of_string "The goal is to show a ‘for all’-statement (∀).
Introduce an arbitrary variable of type "; of_constr var_type; of_string "."]);
  replace_msg "Take ... : ...." "Take ${0:x} : ${1:X}.${2}".

Ltac2 goal_forall_gt_msg (y: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'for all'-statement (∀). Introduce an arbitrary variable strictly larger than "; of_constr y; of_string "."]);
  replace_msg "Take ... > ...." "Take ${0:x} > ${1:0}.${2}".

Local Ltac2 goal_forall_ge_msg (y: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'for all'-statement (∀). Introduce an arbitrary variable larger than or equal to "; of_constr y; of_string "."]);
  replace_msg "Take ... ≥ ...." "Take ${0:x} ≥ ${1:0}.${2}".

Local Ltac2 goal_forall_lt_msg (y: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'for all'-statement (∀). Introduce an arbitrary variable strictly less than "; of_constr y; of_string "."]);
  replace_msg "Take ... < ...." "Take ${0:x} < ${1:0}.${2}".

Local Ltac2 goal_forall_le_msg (y: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'for all'-statement (∀). Introduce an arbitrary variable less than or equal to "; of_constr y; of_string "."]);
  replace_msg "Take ... ≤ ...." "Take ${0:x} ≤ ${1:0}.${2}".

Local Ltac2 goal_forall_ne_msg (y: constr) :=
  info_notice (concat_list [of_string "The goal is to show a ‘for all’-statement (∀). Introduce an arbitrary variable not equal to "; of_constr y; of_string "."]);
  replace_msg "Take ... ≠ ...." "Take ${0:x} ≠ ${1:0}.${2}".

Local Ltac2 goal_forall_pred_msg (q: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'for all'-statement (∀). Introduce an arbitrary variable that is (a/an) "; of_constr q; of_string "."]);
  replace_msg "Take ... ...." "Take ${0:x} ${1:0 = 0}.${2}".

Local Ltac2 goal_exists_el_msg (var_type: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'there exists'-statement (∃). Choose a specific variable in "; of_constr var_type; of_string "."]);
  replace_msg "Choose ... := ...." "Choose ${0:x} := ${1:0}.${2}".

Local Ltac2 goal_exists_gt_msg (y: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'there exists'-statement (∃). Choose a specific variable strictly larger than "; of_constr y; of_string "."]);
  replace_msg "Choose ... := ...." "Choose ${0:x} := ${1:0}.${2}".

Local Ltac2 goal_exists_ge_msg (y: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'there exists'-statement (∃). Choose a specific variable larger than or equal to "; of_constr y; of_string "."]);
  replace_msg "Choose ... := ...." "Choose ${0:x} := ${1:0}.${2}".

Local Ltac2 goal_exists_lt_msg (y: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'there exists'-statement (∃). Choose a specific variable strictly less than "; of_constr y; of_string "."]);
  replace_msg "Choose ... := ...." "Choose ${0:x} := ${1:0}.${2}".

Local Ltac2 goal_exists_le_msg (y: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'there exists'-statement (∃). Choose a specific variable less than or equal to "; of_constr y; of_string "."]);
  replace_msg "Choose ... := ...." "Choose ${0:x} := ${1:0}.${2}".

Local Ltac2 goal_exists_ne_msg (y: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'there exists'-statement (∃). Choose a specific variable not equal to "; of_constr y; of_string "."]);
  replace_msg "Choose ... := ...." "Choose ${0:x} := ${1:0}.${2}".

Local Ltac2 goal_exists_pred_msg (q: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'there exists'-statement (∃). Choose a specific variable that is (a/an) "; of_constr q; of_string "."]);
  replace_msg "Choose ... := ...." "Choose ${0:x} := ${1:0}.${2}".

Local Ltac2 goal_and_msg () :=
  info_notice (of_string "The goal is to show a conjunction (∧). Show both statements.");
  replace_msg "We show both statements." "We show both statements.${0}".

Local Ltac2 goal_or_msg () :=
  info_notice (of_string "The goal is to show a disjunction (∨). It suffices to show one of the statements.");
  replace_msg "It suffices to show that ...." "It suffices to show that ${0:0 = 0}.${1}".

Local Ltac2 goal_neg_msg (negated_type : constr) :=
  info_notice (concat_list [of_string "The goal is to show a negation (¬). Assume that the negated expression "; of_constr negated_type; of_string "."]);
  replace_msg "Assume that ...." "Assume that ${0:0 = 0}.${1}".

Local Ltac2 goal_directly () :=
  info_notice (of_string "The goal can be shown immediately.");
  replace_msg "We conclude that ...." "We conclude that ${0:0 = 0}.${1}".

Local Ltac2 goal_no_hint () :=
  info_notice (of_string "No direct hint available. Does the goal contain a definition that can be expanded?").

Local Ltac2 goal_exists_msg (var_type: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'there exists'-statement (∃). Choose a specific variable of type "; of_constr var_type; of_string "."]);
  replace_msg "Choose ... := ...." "Choose ${0:x} := ${1:0}.${2}".

Local Ltac2 goal_forall_el_msg (var_type: constr) :=
  info_notice (concat_list [of_string "The goal is to show a 'for all'-statement (∀). Introduce an arbitrary variable in "; of_constr var_type; of_string "."]);
  replace_msg "Take ... ∈ ...." "Take ${0:x} ∈ ${1:X}.${2}".

(**
  Auxilliary tactic that checks if goal can be shown with automation
*)
Local Ltac2 solvable_by_core_auto () :=
  let temp_id := Fresh.in_goal @temp in
  let goal := Control.goal () in
  assert $goal as $temp_id;
  Control.focus 1 1 (fun () => waterprove 5 true Main);
  clear $temp_id.

(** Strategy used by [Help] to check whether the goal can be shown directly.
    [None] disables the check. [Some tac]: [tac] should close the focused goal
    or fail; its effect on the proof state is discarded. *)
Ltac2 mutable help_auto_check : (unit -> unit) option :=
  Some (fun () => waterprove 5 true Main).

Local Ltac2 Type exn ::= [ AutoCheckResult (bool) ].

Local Ltac2 solvable_by (tac : unit -> unit) : bool :=
  match Control.case (fun () =>
    Control.focus 1 1 (fun () =>
      tac ();
      Control.zero (AutoCheckResult (Int.equal (Control.numgoals ()) 0))))
  with
  | Err (AutoCheckResult b) => b
  | _ => false
  end.

Local Ltac2 need_to_follow_advice () : bool :=
  let gl := Control.goal () in
  lazy_match! gl with
  | Case.Wrapper _ _                => true
  | NaturalInduction.Base.Wrapper _ => true
  | NaturalInduction.Step.Wrapper _ => true
  | StateGoal.Wrapper _             => true
  | StateHyp.Wrapper _ _ _          => true
  | ByContradiction.Wrapper _ _     => true
  | False                           => true
  | _ => false
  end.

(* TODO: Refactor this function to return an option with data and call print after *)
Local Ltac2 goal_hint () : bool :=
  let gl := Control.goal () in
  lazy_match! gl with
  | ?a -> ?_b  =>
    let sort_a := get_value_of_hyp a in
    match check_constr_equal sort_a constr:(Prop) with
      | true            => goal_impl_msg a; true
      | false           => goal_func_msg a; true
    end
    (* TODO: refactor this, so hints can be added in later library files *)
  | ∀ _ ∈ conv ?v_type, _  => goal_forall_el_msg v_type; true
  | ∀ _ ∈ ?v_type, _  => goal_forall_el_msg v_type; true
  | ∀ _ > ?y, _        => goal_forall_gt_msg y; true
  | ∀ _ ≥ ?y, _          => goal_forall_ge_msg y; true
  | ∀ _ < ?y, _          => goal_forall_lt_msg y; true
  | ∀ _ ≤ ?y, _          => goal_forall_le_msg y; true
  | ∀ _ ?q, _           => goal_forall_pred_msg q; true
  | ∃ _ ∈ conv ?v_type, _    => goal_exists_el_msg v_type; true
  | ∃ _ ∈ ?v_type, _    => goal_exists_el_msg v_type; true
  | ∃ _ > ?y, _         => goal_exists_gt_msg y; true
  | ∃ _ ≥ ?y, _         => goal_exists_ge_msg y; true
  | ∃ _ < ?y, _         => goal_exists_lt_msg y; true
  | ∃ _ ≤ ?y, _         => goal_exists_le_msg y; true
  | ∃ _ ≠ ?y, _         => goal_exists_ne_msg y; true
  | ∃ _ ?q, _           => goal_exists_pred_msg q; true
  | forall v:?v_type, _ => goal_forall_msg v_type; true
  | exists v:?v_type, _ => goal_exists_msg v_type; true
  | _ /\ _              => goal_and_msg (); true
  | _ \/ _              => goal_or_msg (); true
  | not ?g              => goal_neg_msg g; true
  | _                   => false
  end.

Local Ltac2 forall_filter (x : constr) : bool :=
  lazy_match! x with
  | _ -> ?_b     => false
  | ∀ _ _ _, _   => true
  | ∀ _ _, _   => true
  | forall _, _  => true
  | _            => false
  end.

Local Ltac2 exists_filter (x : constr) : bool :=
  lazy_match! x with
  | exists _, _  => true
  | ∃ _ _ _, _   => true
  | ∃ _ _, _   => true
  | _            => false
  end.

Local Ltac2 is_empty (ls : 'a list) :=
  match ls with
  | _::_ => false
  | []   => true
  end.

Ltac2 print_hints () :=
  (* If advice is given in proof window, suggest to follow that, nothing else. *)
  if (goal_wrapped_template_msg ())
    then (info_notice (of_string "Follow the advice in the goal window."))

    else
      let solvable := match help_auto_check with
      | Some tac => solvable_by tac
      | None => false
      end in
    if solvable then goal_directly () else
        (* Suggest hint to solve goal *)
        let hint_given := goal_hint () in

        (* Suggest how to expand definitions *)
        let ls := get_unfold_references_ffi () in
        let expand_list_empty := is_empty ls in
        if Bool.neg expand_list_empty then
          (info_notice (of_string "You can try to expand definitions or use alternative characterizations:");
          List.iter (fun l => wp_unfold_by_ref l false) ls)
        else ();

        (* Collect forall- and exists-statements *)
        let hyps := List.map (fun (_, _, t) => t) (Control.hyps ()) in
        let forall_hyps := List.filter (forall_filter) hyps in
        let exists_hyps := List.filter (exists_filter) hyps in

        (* Print how to use forall-statements. *)
        if (is_empty forall_hyps)
          then ()
          else (
            info_notice(of_string "You can use one of the ‘for all’-statements (∀):");
            List.iter (fun h => info_notice (concat (of_string "    ") (of_constr h))) forall_hyps;
            replace_msg "Use ... := ... in ...." "Use ${0:x} := ${1:0} in ({2:i}).${3}"
          );

        (* Print how to use exists statements. *)
        if (is_empty exists_hyps)
          then ()
          else (
            info_notice(of_string "You can use one of the ‘there exists’-statements (∃):");
            List.iter (fun h => info_notice (concat (of_string "    ") (of_constr h))) exists_hyps;
            replace_msg "Obtain ... according to ...." "Obtain ${0:x} according to (${1:i}).${2}"
          );

        (* Print no hints available if none have been given *)
        if List.fold_left (fun a b => Bool.and a b) true
            [is_empty forall_hyps;
             is_empty exists_hyps;
             Bool.neg hint_given;
             expand_list_empty]
          then (goal_no_hint ())
          else ().

(** * Help tactic
    Tries to give a hint how to proceed proving the current goal.
*)
Ltac2 Notation "Help" := print_hints ().





Module HelpNewHyp.



End HelpNewHyp.

Close Scope subset_scope.
