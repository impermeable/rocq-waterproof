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

Require Export Ltac2.Ltac2.
Require Import Ltac2.Bool.
Require Import Ltac2.Init.
Require Import Ltac2.String.

Require Import Waterproof.Waterproof.

(** TODO: in later versions of Rocq this can be replaced by a native function *)
Ltac2 fnl () := Message.of_string "
".

Ltac2 Type FeedbackLevel := [ Debug | Info | Notice | Warning | Error ].

Ltac2 @ external send_message_external: FeedbackLevel -> message -> unit := "rocq-runtime.plugins.rocq-waterproof" "message_external".
Ltac2 @ external throw_external: message -> unit := "rocq-runtime.plugins.rocq-waterproof" "throw_external".
Ltac2 @ external get_print_hypothesis_flag: unit -> bool := "rocq-runtime.plugins.rocq-waterproof" "get_print_hypothesis_flag_external".
Ltac2 @ external get_redirect_errors_flag : unit -> bool := "rocq-runtime.plugins.rocq-waterproof" "get_redirect_errors_flag_external".
Ltac2 @ external shortest_string_of_global_ffi : Std.reference -> string :=
  "rocq-runtime.plugins.rocq-waterproof" "shortest_string_of_global_external".

Ltac2 @ external get_last_warning : unit -> message option :=
  "rocq-runtime.plugins.rocq-waterproof" "get_last_warning_external".
Ltac2 @ external get_feedback_log_external : FeedbackLevel -> message list :=
  "rocq-runtime.plugins.rocq-waterproof" "get_feedback_log_external".

(** Can be removed in a later version of Rocq, probably 9.2,
    because it has then been integrated in Ltac2. *)
Ltac2 @ external of_lconstr : constr -> message := "rocq-runtime.plugins.rocq-waterproof" "message_of_lconstr".
(** Prints at level 200 (no surrounding parentheses).
    Panics if there is more than one goal under focus. *)

Ltac2 Type exn ::= [RedirectedToUserError (message)].

Ltac2 send_message (lvl : FeedbackLevel) (msg : message) :=
  send_message_external lvl msg.

Ltac2 inform (msg : message) :=
  send_message Info msg.

Ltac2 notice (msg : message) :=
  send_message Notice msg.

Ltac2 warn (msg : message) :=
  send_message Warning msg.

Ltac2 get_feedback_log (lvl : FeedbackLevel) :=
  get_feedback_log_external lvl.

Ltac2 info_notice (msg : message) := inform msg; notice msg.
  (* We send both here because with the right settings in rocq-waterproof,
     they show up in different places in the editor. *)

Ltac2 replace_notice (template : string) :=
  notice (Message.concat (Message.of_string "Hint, replace with: ") (Message.of_string template)).

(* We slightly abuse the levels here: notice shows up inline and has special treatment to
   work with the templates, inform shows up in the sidebar. *)
Ltac2 insert_msg (msg : string) (template : string) :=
  inform (Message.concat (Message.of_string "Hint, insert: ") (Message.of_string msg));
  notice (Message.concat (Message.of_string "Hint, insert: ") (Message.of_string template)).

Ltac2 replace_msg (msg : string) (template : string) :=
  inform (Message.concat (Message.of_string "Hint, replace with: ") (Message.of_string msg));
  replace_notice template.

(* Note, there could arise a use case for sending an error on the feedback channel without
  actually raising an error, but it could also be confusing. For now, errors are therefore
  handled through a different channel *)
Ltac2 throw (msg : message) :=
  if (get_redirect_errors_flag ()) then
    Control.zero (RedirectedToUserError msg)
  (** We use an OCaml error here, because it gets rendered much nicer in the editor *)
  else throw_external msg.
