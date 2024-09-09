(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "thingsToDiscuss";

(* Started working on definition of viterbi trellis data which computes it row by row, in order to make it efficiently evaluable. *)

(* Representing each row as a list does not work, since we would not know which state corresponds to which element of the list. Instead defined each row as a function from states to values. *)

(* Concerned that however I defined it, it may require exponential computation. Wrote a function to test this theory. Turned out that this function did not require exponential computation. Still concerned that it may only be in this instance or something. Want to discuss with Michael. *)

(* The uncertainty with what order things are evaluated in seems to me to make it harder to work out the efficiency of functions in functional languages than in imperative languages *)

(* Attempted to remove select statement in viterbi trellis data. Ran into difficulties when using the generalised state machine. Attempted adding well-ordering to fix these difficulties. *)

(* In particular, using the normal state machine, how do you select a choice of prior state to take when going backwards through the path, when there are multiple equally good choices? There is no way to distiguish between two states, so I would need to add a well-ordering on the states. When I have such a well-ordering, this defines a least element to choose when going backwards through the path, but how do I actually compute what this element is, when all I have is the $< relation used to order the elements? It's a lot harder to enumerate over sets than it is over lists, because sets are in a universe which contains an infinite number of elements. Is it possible to enumerate over sets in a way which is efficiently evaluable by the computer? It's just generally much more of a headache to work with the normal state machine than it is with a num state machine. I've deliberately avoided sets and used lists instead for this reason. Maybe I ought to use sets, as they have their own advantages? *)

(* Wrote a num-based state machine. This can sometimes be easier to work with because we can use properties of num to help us, e.g. we can find the least num, or we can associate each state with an elemnet of a list, or we can enumerate through all states easily.

This is a stronger definition than the definition of a general state machine. This makes it easier to use when you are provided with one, but it's also harder to provide one yourself. The weaker, more general definition may be easier to use when providing one, but it gives you less information when you have one already.
It may be good to define the state machines using the weaker definition, then convert them to the stronger version, and use the stronger version when proving stuff about them.*)

(* Wrote row-based trellis algorithm for num-based state machine. Wrote theorem to ensure example state machines were well-formed.*)

(* Want to get list of prior states leading to a particular state, so I can enumerate over them and check which one provides the quickest path to the current state. Wrote code to *)

(* Finished viterbi trellis row code. Tested it. Includes code which replaces the select operation.*)

(* Finished code for finding the path back through the trellis. Wrote code for testing it, too *)

(* Maybe it would be good if some of my work could be reviewed *)

(* Completed Viterbi decoding and tested it. *)

(* Completed base case of proof of viterbi correctness. Included proofs that enccoding/decoding the empty list gives you back the empty list.*)

(* Renamed so that the num-based state machine is the default one. *)

(* Allowed finding the optimal path to terminate early if it reaches a point in the trellis with no previous state. *)

(* Added functions to determine which state we end up in when applying the state machine to a particular bitstring. This allows me to split the viterbi calculation up into multiple parts: starting at a particular point and applying viterbi, and then performing another calculation from the appropritate state to complete the algorithm. *)

(* Wrote theorems to split the viterbi process up into two parts: SNOC, CONS, and APPEND, with both helper and non-helper *)

(* functions to take a single step in the state machine. *)

(* Ensured that function for rewriting with cons didn't produce a result with a cons in it, avoiding infinite loops. *)

(* THeorem for simplifying hamming distance when bitstrings have been appended to each other *)

(* Theorems for calculating the length of the encoded string *).

(* Adding requirement htat machine has at least one state to definition of well-formed machine.*)

(* Proved that the state generated through the encoding process is a valid one *)

(* Proved that when the output length is 0, every message is the empty message *)

(* Started proving that the length of a decoded message is equal to the original length divided by the number of outputs per transition. Proved that the length of the binary message based on a path of states is one less than the length of the path of states. *)

(* Started using abbreviations *)

(* Proved that beyond the zeroth time step, all states in the trellis have a valid prior state. *)

(* Proved that all states returned by the inverse transition function are valid, and started proving that the output of the inverse transition function is nonempty *)

(* Issue: if there are states with no predecessor, a lot of things regarding travelling back through the trellis may break. *)

(* Added assumption that there's always at least one prior state in order to fix this issue *)

Datatype:
  transition_origin = <|
    origin : num;
    input : bool;
  |>
End

Theorem test:
  ∀r : transition_origin.
    r = <|origin := r.origin; input := r.input|>
Proof
  rpt strip_tac
  >> EVAL_TAC
  >> Cases_on ‘r’
  >> EVAL_TAC
  >> Cases_on ‘transition_origin n b’
  >> Cases_on ‘<|origin := n; input := b|>’
  >> EVAL_TAC
  >>  
  (*>> Cases_on ‘b’ >> Cases_on ‘b'’ >> EVAL_TAC*)
  >>
QED


(* This definition was changed to this form for the above reason. Originally used the following definition:
all_transitions_helper (m : state_machine) (b : bool) = GENLIST (λn. <| origin := n; input := b |>) m.num_states *)
Definition all_transitions_helper_def:
  all_transitions_helper (m : state_machine) (b : bool) = GENLIST (λn. transition_origin n b) m.num_states
End

(* proved that any transition is contained in the list of all transitions *)

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* How do I match inside a lambda expression? *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)


(* wrote a function for deleting the nth assumption *)


(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* open donotexpandLib.sml didn't work *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)



(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* Forgot how to expand out lambda term                                       *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* rewrote trellis node code to isolate large function as its own definition to improve readability *)



(* -------------------------------------------------------------------------- *)
(* Wrote set version of all_transitions and inverse transition function. This *)
(* is better for proving, but the list version is better for actual           *)
(* computation                                                                *)
(* -------------------------------------------------------------------------- *)



(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* How to disable case splitting on disjuncts?                                *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* Proved Given a function which always outputs one of its two inputs, if it is folded over a list, the result is one of the elements of the list.*)

(* Proved that each state in each row in the trellis is valid *)

(* Proved theorem calculating the exact length of the path back through the trellis *)

(* -------------------------------------------------------------------------- *)
(* Is there code for taking the max/min of a function over a list?            *)
(*                                                                            *)
(* What about the argmax/argmin?                                              *)
(* -------------------------------------------------------------------------- *)

(* Proved that viterbi decoding causes an output of a certain length *)

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* How to do Cases_on bs using SNOC? i.e.                                     *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

val _ = export_theory();

