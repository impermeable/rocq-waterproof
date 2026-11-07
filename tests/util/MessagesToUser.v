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
Require Import Waterproof.Waterproof.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.

(* Waterproof Enable Redirect Warnings. *)

Waterproof Enable Redirect Feedback.
Waterproof Enable Redirect Errors.

(** Test whether enabling the hypothesis flag works.
*)
Waterproof Enable Hypothesis Help.

Goal False.
assert_is_true (get_print_hypothesis_flag ()).
Abort.

(** Test whether disabling the hypothesis flag works.
*)
Waterproof Disable Hypothesis Help.

Goal False.
assert_is_false (get_print_hypothesis_flag ()).
Abort.

(** Test whether feedback levels are correctly passed through the ffi. *)
Ltac2 @ external check_feedback_level_Ltac2_to_Ocaml_ffi : FeedbackLevel -> int -> bool := "rocq-runtime.plugins.rocq-waterproof" "check_feedback_level_Ltac2_to_Ocaml_external".

Goal False.
assert_is_true (check_feedback_level_Ltac2_to_Ocaml_ffi Debug 0).
assert_is_true (check_feedback_level_Ltac2_to_Ocaml_ffi Info 1).
assert_is_true (check_feedback_level_Ltac2_to_Ocaml_ffi Notice 2).
assert_is_true (check_feedback_level_Ltac2_to_Ocaml_ffi Warning 3).
assert_is_true (check_feedback_level_Ltac2_to_Ocaml_ffi Error 4).
Abort.

(** Test a round-trip of feedback levels *)
Ltac2 @ external feedback_level_round_trip_ffi : FeedbackLevel -> FeedbackLevel := "rocq-runtime.plugins.rocq-waterproof" "feedback_level_round_trip_external".

Goal False.
match feedback_level_round_trip_ffi Debug with
| Debug => ()
| _ => Control.throw (TestFailedError (Message.of_string "Debug did not round-trip correctly."))
end.
match feedback_level_round_trip_ffi Info with
| Info => ()
| _ => Control.throw (TestFailedError (Message.of_string "Info did not round-trip correctly."))
end.
match feedback_level_round_trip_ffi Notice with
| Notice => ()
| _ => Control.throw (TestFailedError (Message.of_string "Notice did not round-trip correctly."))
end.
match feedback_level_round_trip_ffi Warning with
| Warning => ()
| _ => Control.throw (TestFailedError (Message.of_string "Warning did not round-trip correctly."))
end.
match feedback_level_round_trip_ffi Error with
| Error => ()
| _ => Control.throw (TestFailedError (Message.of_string "Error did not round-trip correctly."))
end.
Abort.
