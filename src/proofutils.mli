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
  Returns the index of the first element [x] of [l] such that `f x` is [true]
*)
val find_first : ('a -> bool) -> 'a list -> int option

(**
  Returns the index of the last element [x] of [l] such that `f x` is [true]
*)
val find_last : ('a -> bool) -> 'a list -> int option

(**
  Returns the queue of the given list after the [n]th element included
*)
val tail_end : 'a list -> int -> 'a list

(**
  Generic dictionnary taking strings as keys
*)
module StringMap : sig
  type key = string
  type 'a t = 'a Map.Make(String).t

  val empty : 'a t
  val is_empty : 'a t -> bool
  val mem : key -> 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
  val singleton : key -> 'a -> 'a t
  val remove : key -> 'a t -> 'a t

  val merge :
    (key -> 'a option -> 'b option -> 'c option) ->
    'a t ->
    'b t ->
    'c t

  val union :
    (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val for_all : (key -> 'a -> bool) -> 'a t -> bool
  val exists : (key -> 'a -> bool) -> 'a t -> bool
  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
  val cardinal : 'a t -> int
  val bindings : 'a t -> (key * 'a) list
  val min_binding : 'a t -> key * 'a
  val min_binding_opt : 'a t -> (key * 'a) option
  val max_binding : 'a t -> key * 'a
  val max_binding_opt : 'a t -> (key * 'a) option
  val choose : 'a t -> key * 'a
  val choose_opt : 'a t -> (key * 'a) option
  val split : key -> 'a t -> 'a t * 'a option * 'a t
  val find : key -> 'a t -> 'a
  val find_opt : key -> 'a t -> 'a option
  val find_first : (key -> bool) -> 'a t -> key * 'a

  val find_first_opt :
    (key -> bool) -> 'a t -> (key * 'a) option

  val find_last : (key -> bool) -> 'a t -> key * 'a

  val find_last_opt :
    (key -> bool) -> 'a t -> (key * 'a) option

  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  val to_seq : 'a t -> (key * 'a) Seq.t
  val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
  val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
  val of_seq : (key * 'a) Seq.t -> 'a t
end

(** Maps the given function to the list then applies every returned tactic *)
val tclMAP_rev :
  ('a -> unit Proofview.tactic) ->
  'a list ->
  unit Proofview.tactic

(** Generic mergeable type *)
module type Mergeable = sig

  (** Type of the elements *)
  type elt

  (** Empty value *)
  val empty : elt

  (** How to merge two elements *)
  val merge : elt -> elt -> elt

end

(** Generalization of tactics defined in rocq-core for {! Mergeable}-typed tactics *)
module TypedTactics : functor (M : Mergeable) -> sig

  (** Merge of tactics' returned elements *)
  val typedThen :
    M.elt Proofview.tactic ->
    M.elt Proofview.tactic ->
    M.elt Proofview.tactic

  (** Same as {! typedThen} with a list of tactics *)
  val typedLongThen :
    M.elt Proofview.tactic list -> M.elt Proofview.tactic

  (** Generalization of {! Proofview.Goal.enter} *)
  val typedGoalEnter :
    (Proofview.Goal.t -> M.elt Proofview.tactic) ->
    M.elt Proofview.tactic

  (** Generalisation of {! Proofview.tclINDEPENDENT} *)
  val typedIndependant :
    M.elt Proofview.tactic -> M.elt Proofview.tactic

end

module TraceTactics : sig
  val typedThen :
    Backtracking.trace Proofview.tactic ->
    Backtracking.trace Proofview.tactic ->
    Backtracking.trace Proofview.tactic

  val typedLongThen :
    Backtracking.trace Proofview.tactic list ->
    Backtracking.trace Proofview.tactic

  val typedGoalEnter :
    (Proofview.Goal.t -> Backtracking.trace Proofview.tactic) ->
    Backtracking.trace Proofview.tactic

  val typedIndependant :
    Backtracking.trace Proofview.tactic ->
    Backtracking.trace Proofview.tactic
end

(**
  Rewrite of [Auto.tclLOG]

  Updates the trace contained in the given tactic.

  Fails if the hint's name is forbidden, or if the proof will be complete without using all must-use lemmas.

  Arguments:
  - [pp: Environ.env -> Evd.evar_map -> Pp.t * Pp.t]: function to obtain the printable version of [(hint_name, source_hint_database)]
  - [tac: trace tactic]: tactic that will be tried
  - [must_use: : Pp.t list]: list of tactics that must be used during the automation
  - [forbidden: : Pp.t list]: list of tactics that mustn't be used during the automation
*)
val tclLOG :
  (Environ.env -> Evd.evar_map -> Pp.t * Pp.t) ->
  Backtracking.trace Proofview.tactic ->
  Pp.t list ->
  Backtracking.trace Proofview.tactic

(**
  Checks if every hint in [must_use] is contained in [tac] and returns an exception if not
*)
val trace_check_used :
  Pp.t list ->
  Backtracking.trace ->
  Backtracking.trace Proofview.tactic

(**
  Rewrite of {! Tacticals.tclORELSE0} to give the trace of the failed tactic instead of the exception
*)
val tclOrElse0 :
  Backtracking.trace Proofview.tactic ->
  (Backtracking.trace -> Backtracking.trace Proofview.tactic) ->
  Backtracking.trace Proofview.tactic

(**
  Wrapper around {! tclOrElse0} with merge of trace contained in the failed [trace tactic] into the second one
*)
val tclTraceOrElse :
  Backtracking.trace Proofview.tactic ->
  Backtracking.trace Proofview.tactic ->
  Backtracking.trace Proofview.tactic

(**
  Rewrite of {! Tacticals.tclTraceFirst} with [trace tactic] with a merge of traces of failed tactics 
*)
val tclTraceFirst :
  Backtracking.trace Proofview.tactic list ->
  Backtracking.trace Proofview.tactic

(**
  Rewrite of Rocq's hint printer to keep only the necessary parts
*)
val pr_hint :
  Environ.env -> Evd.evar_map -> Hints.FullHint.t -> Pp.t
