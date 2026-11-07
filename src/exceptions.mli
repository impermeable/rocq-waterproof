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
  A flag that determines whether Waterproof should filter errors
*)
val filter_errors : bool ref

(**
  A rudimentary feedback log
*)
val feedback_log : Feedback.level -> Pp.t list ref

(**
  The id that we obtained when registering wp_feedback_logger as a feeder in Feedback.mli
*)
val wp_feedback_logger_id : int option ref

(**
  Our own logger that we add as a feeder to Rocq's feedback mechanism in Feedback.mli
*)
val wp_feedback_logger : Feedback.feedback -> unit

(**
  Adds the wp_feedback_logger to Rocq's feedback mechanism
*)
val add_wp_feedback_logger : unit -> unit

(**
  Should hypothesis hints be printed (For instance on how you can use a forall statement)?
*)
val print_hypothesis_help : bool ref

(**
  The last thrown warning
*)
val last_thrown_warning : Pp.t option ref

(**
  Redirect warnings: this is useful when testing the plugin: meant to redirect Waterproof
  errors directly to the log
*)
val redirect_feedback : bool ref

(**
  Redirect errors: this is useful when testing the plugin: meant to redirect errors
  to Control.zero rather than CErrors.user_err
*)
val redirect_errors : bool ref

(**
  Type of exceptions used in Waterproof
*)
type wexn =
  | CastError of string (** Indicates that a cast made by the FFI has failed  *)
  | FailedAutomation of string (** Indicates that the automatic solver called has failed  *)
  | FailedTest of string (** Indicates that the running test has failed *)
  | NonExistingDataset of Hints.hint_db_name (** Indicates that the user tried to import a non-existing hint dataset *)
  | UnusedLemmas (** Indicates that no proof using all the given lemmas has been found *)
  | ToUserError of Pp.t (** An error that should go directly to the user *)

(**
  Throws an error with given info and message
*)
val throw : ?info:Exninfo.info -> wexn -> 'a

(**
  Sends a warning
*)
val warn :
  Pp.t -> unit Proofview.tactic

(**
  Sends a notice
*)
val notice :
  Pp.t -> unit Proofview.tactic

(**
  Send an info message
*)
val inform :
  Pp.t -> unit Proofview.tactic

(**
  Throws an error
*)
val err :
  Pp.t -> unit Proofview.tactic

(**
  A general function for sending feedback
*)
val message :
  Feedback.level -> Pp.t -> unit Proofview.tactic

(**
  Check the last warning against a string
*)
val get_last_warning : unit -> Pp.t option

(**
  Convert a reference in a shortest string representation of the
  corresponding qualid
*)
val shortest_string_of_global : Names.GlobRef.t -> string

(**
  Purely for testing that passing Feedback levels through the ffi works
*)
val check_feedback_level_Ltac2_to_Ocaml : Feedback.level -> int -> bool
