(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "thingsToDiscuss";

(* I've done much better in terms of working for a sufficient number of hours this week: I spent 46 hours and 24 minutes actively working over the past 7 days. *)

(* As a result, I have been significantly more productive: *)

(* The Viterbi Algorithm has been replaced by an evaluable version, which runs, and is able to do both encoding and decoding, and has been tested. The main proof of the correctness of the Viterbi algorithm is almost complete: I have written a large number of relevant helper theorems, have tried proving it a couple times, and have a clear plan on what the proof will look like. I expect it to be complete by the end of next week. *)

(* Concerned that however I defined it, it may require exponential computation. Wrote a function to test this theory. Turned out that this function did not require exponential computation. Still concerned that it may only be in this instance or something.

   I understand that efficiency is not a massive concern, but I was worried that it would be so inefficient that it wouldn't be evaluable on inputs of a sensible size.
 *)

(* -------------------------------------------------------------------------- *)
(* An example function which generates a grid recursively, in a similar       *)
(* manner to the Viterbi algorithm.                                           *)
(*                                                                            *)
(* I wanted to test whether or not this kind of recursive implementation is   *)
(* super inefficient in HOL. In particular, I was concerned that since at     *)
(* each stage it needs to recurse multiple times, this might cause it to take *)
(* exponential time overall. Luckily, this doesn't seem to be the case.       *)
(* Perhaps it evaluates the previous row fully before substituting it in      *)
(* multiple places.                                                           *)
(* -------------------------------------------------------------------------- *)
Definition example_recursive_grid_row_def:
  example_recursive_grid_row 0 = REPLICATE 10 1 ∧
  example_recursive_grid_row (SUC n) =
  let
    prior_grid_row = example_recursive_grid_row n
  in
    MAP (λn. (if 0 < n then EL (n - 1) prior_grid_row else 0) + EL n prior_grid_row + (if n < 9 then EL (n + 1) prior_grid_row else 0)) (COUNT_LIST 10)
End

(* -------------------------------------------------------------------------- *)
(* Testing whether or not example_grid takes an exponential amount of time    *)
(* to compute. It could theoretically take an exponential amount of time if   *)
(* the previous row was substituted in multiple places, and expanded out      *)
(* fully multiple times. Each subsequent row would double the amount of time  *)
(* taken because it has to do the computation from the previous row twice.    *)
(*                                                                            *)
(* 100: 0.681                                                                 *)
(* 200: 2.311                                                                 *)
(* 300: 5.196                                                                 *)
(* 400: 8.997                                                                 *)
(* 500: 14.070                                                                *)
(* 600: 19.658                                                                *)
(* 700: 26.521                                                                *)
(* 800: 34.426                                                                *)
(* -------------------------------------------------------------------------- *)
(*Theorem example_grid_time_test:
  example_grid 800 = ARB
Proof
  EVAL_TAC
QED*)

(* //// The uncertainty with what order things are evaluated in seems to me to make it harder to work out the efficiency of functions in functional languages than in imperative languages *)

(* To make viterbi algorithm evaluable, removed the select statement. *)

(* Issues during implementation of this change led me to use a num-based state machine instead of a generalized state machine *)

(*In particular, using the normal state machine, how do you select a choice of prior state to take when going backwards through the path, when there are multiple equally good choices? There is no way to distiguish between two states, so I would need to add a well-ordering on the states. When I have such a well-ordering, this defines a least element to choose when going backwards through the path, but how do I actually compute what this element is, when all I have is the $< relation used to order the elements? It's a lot harder to enumerate over sets than it is over lists, because sets are in a universe which contains an infinite number of elements. Is it possible to enumerate over sets in a way which is efficiently evaluable by the computer? It's just generally much more of a headache to work with the normal state machine than it is with a num state machine.*)

(* Nums have useful properties that can be used. *)

(* Num-based state machine is a stronger definition, and is more useful in the hypothesis, whereas the general state machine is weaker, and is more useful in the conclusions.

It may be good to define the state machines using the weaker definition, then convert them to the stronger version, and use the stronger version when proving stuff about them.*)

(* I've also deliberately avoided sets and used lists instead because it is easier to write a function to be evaluable when using lists than when using sets. This despite the fact that sets are mathematically nicer. When using a generalized state machine, we cannot represent the trellis in terms of lists, because there is no canonical ordering on the elements, and so we have to represent each row as a function from states to values. Using nums provides a canonical ordering, which is useful.*)

(* Wrote a num-based state machine. This can sometimes be easier to work with because we can use properties of num to help us, e.g. we can find the least num, or we can associate each state with an elemnet of a list, or we can enumerate through all states easily.*)

(* Issue: if there are states with no predecessor, a lot of things regarding travelling back through the trellis may break. Added assumption that there's always at least one prior state in order to fix this issue *)

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

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* How do I match inside a lambda expression? *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* How to disable case splitting on disjuncts?                                *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* Proved Given a function which always outputs one of its two inputs, if it is folded over a list, the result is one of the elements of the list.

What is the name of this kind of function?*)

(* -------------------------------------------------------------------------- *)
(* Is there code for taking the max/min of a function over a list?            *)
(*                                                                            *)
(* What about the argmax/argmin?                                              *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* How to do Cases_on bs using SNOC? i.e.                                     *)
(* Note: can probably use a specific theorem                                  *)
(* -------------------------------------------------------------------------- *)
      
val _ = export_theory();
