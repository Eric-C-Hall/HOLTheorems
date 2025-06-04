(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

open factor_graphTheory;
open extrealTheory;
open probabilityTheory;

open state_machineTheory;
open wf_state_machineTheory;
open binary_symmetric_channelTheory;

val _ = new_theory "bcjr";

(* -------------------------------------------------------------------------- *)
(* This is largely based on Fundamentals of Convolutional Coding by           *)
(* Rolf Johannesson and Kamil Sh. Zigangirov                                  *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* An implementation of the forward metric for the BCJR algorithm for         *)
(* well-formed state machines                                                 *)
(*                                                                            *)
(* For every possible state and timestep, this represents the probability of  *)
(* having taken a path which arrives at this state and timestep while         *)
(* simultaneously observing the bits which were observed, up until that       *)
(* point.                                                                     *)
(*                                                                            *)
(* m: the well-formed state machine (abstract type)                           *)
(* p: the probability defining the binary symmetric channel                   *)
(* rs: the ultimately received data, after encoding and noise                 *)
(* t: the time-step in the trellis to calculate the forward metric at         *)
(* s: the state in the trellis to calculate the forward metric at             *)
(*                                                                            *)
(* At time 0:                                                                 *)
(* - At state 0: forward metric is 1 (we start in state 0 with 100% prob)     *)
(* - Otherwise: foward metric is 0 (we start in another state with 0% prob)   *)
(*                                                                            *)
(* At time t + 1:                                                             *)
(* - We want to calculate the probability of arriving at the current state    *)
(*   and timestep while observing the appropriate data.                       *)
(*                                                                            *)
(*   We do this by taking the sum over each possible predecessor state of the *)
(*   probability of arriving at that predecessor state while observing the    *)
(*   appropriate data, and then taking the transition to the current state    *)
(*   while observing the appropriate data.                                    *)
(*                                                                            *)
(*   In other words, each term in this sum is equal to the forward metric     *)
(*   for the predecessor state multiplied by the probability of taking the    *)
(*   appropriate transition from the predecessor state multiplied by the      *)
(*   probability of receiving the appropriate bits given that the bits        *)
(*   corresponding to this transition were sent.                              *)
(* -------------------------------------------------------------------------- *)
Definition bcjr_forward_metric_wfm_def:
  bcjr_forward_metric_wfm m p rs 0 0 = Normal 1 ∧
  bcjr_forward_metric_wfm m p rs 0 (SUC s) = Normal 0 ∧
  bcjr_forward_metric_wfm m p rs (SUC t) s =
  ∑ (λ(prev_state, b).
       (bcjr_forward_metric_wfm m p rs t prev_state) *
       (Normal 1 / Normal 2) *
       (let
          produced_bitstring = SND (wfm_transition_fn m (prev_state, b));
          expected_bitstring =
          TAKE (wfm_output_length m)
               (DROP (t * wfm_output_length m) rs);
        in
          bsc_probability p produced_bitstring expected_bitstring
       )
    )
  {(prev_state, b) | FST (wfm_transition_fn m (prev_state, b)) = s ∧
                     prev_state < wfm_num_states m ∧
                     (b ∨ ¬b)}
End

(* -------------------------------------------------------------------------- *)
(* The backward metric for the BCJR algorithm for well-formed state machines  *)
(*                                                                            *)
(* For every possible state and timestep, this represents the probability     *)
(* that, if we start at this state and timestep, we will take a path which    *)
(* eventually arrives at the final state, and produces all the expected       *)
(* outputs. This is very similar to the forward metric, except we are         *)
(* travelling backwards instead of fowards.                                   *)
(*                                                                            *)
(* m: the well-formed state machine (abstract type)                           *)
(* p: the probability defining the binary symmetric channel                   *)
(* rs: the ultimately received data, after encoding and noise                 *)
(* t: the time-step in the trellis to calculate the forward metric at         *)
(* s: the state in the trellis to calculate the forward metric at             *)
(*                                                                            *)
(* At the final timestep:                                                     *)
(* - At state 0: backward metric is 1 (there is a 100% chance of ending in    *)
(*     state 0 as a result of zero-tailing. This is an important assumption   *)
(*     that may not be the case for invalid choices of rs)                    *)
(* - At state 1: backward metric is 0 (there is a 0% chance of ending in      *)
(*   another state)                                                           *)
(*                                                                            *)
(* At time t - 1:                                                             *)
(* - We want to calculate the probability of taking a path from the current   *)
(*   state and time step in such a way that we observe the appropriate data.  *)
(*                                                                            *)
(*   We do this by taking the sum over all possible successor nodes of        *)
(*   transitioning to that successor node, observing the appropriate data     *)
(*   corresponding to that transition, and then subsequently taking a path    *)
(*   from this node in such a way that we observe the appropriate data.       *)
(*                                                                            *)
(*   In other words, each term in this sum is equal to the backward metric    *)
(*   for the appropriate state multiplied by the probability of taking the    *)
(*   transition to that state multiplied by the probability of receiving the  *)
(*   appropriate bits relating to this transition that was taken.             *)
(* -------------------------------------------------------------------------- *)
Definition bcjr_backward_metric_wfm_def:
  bcjr_backward_metric_wfm m p rs t s =
  let
    max_timestep = LENGTH rs DIV wfm_output_length m
  in
    if max_timestep ≤ t
    then
      if s = 0
      then Normal 1
      else Normal 0
    else
      ∑ (λ(next_state, b).
           (bcjr_backward_metric_wfm m p rs (t + 1) next_state) *
           (Normal 1 / Normal 2) *
           (let
              produced_bitstring = SND (wfm_transition_fn m (s, b));
              expected_bitstring =
              TAKE (wfm_output_length m)
                   (DROP (t * wfm_output_length m) rs);
            in
              bsc_probability p produced_bitstring expected_bitstring
           )
        )
        {(next_state, b) | FST (wfm_transition_fn m (s, b)) = next_state ∧
                           next_state < wfm_num_states m ∧
                           (b ∨ ¬b)}
Termination
  WF_REL_TAC ‘measure (λ(m,p,rs,t,s).(LENGTH rs DIV wfm_output_length m) - t)’
End

(* -------------------------------------------------------------------------- *)
(* We formalize the BCJR algorithm for state machines                         *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Main reference:"Modern Coding Theory" by Tom Richardson and Rüdiger        *)
(* Urbanke.                                                                   *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* The factor graph corresponding to a state machine.                         *)
(*                                                                            *)
(* P(x_i | y) = Σ P(x,σ|y)                                                    *)
(*            = Σ (P(x,σ,y) / P(y))                                           *)
(*            ∝ Σ P(x,σ,y)                                                   *)
(*            ∝ Σ P(y|x,σ) P(x,σ)                                            *)
(*            ∝ Σ P(y|x) P(x|σ) P(σ)                                         *)
(*            ∝ Σ P(y|x) P(x|σ) P(σ_0) (Π P(σ_(i+1), σ_i))                   *)
(*            ∝ Σ P(y|x) (Π P(x_(i+1)|σ_i, σ_(i+1))) P(σ_0)                  *)
(*                        (Π P(σ_(i+1), σ_i))                                 *)
(*     Not a tree: P(x_(i+1)|σ_i,σ_(i+1)) connects to σ_i and to σ_(i+1)      *)
(*     P(σ_(i+1),σ_i) also connects to these variables, thus creating a       *)
(*     loop. Should really combine these,                                     *)
(*            (Above was attempt 1: try different approach)                   *)
(*            ∝ Σ P(y|x,σ) P(x,σ)     (continued)                            *)
(*            ∝ Σ P(y|x) P(x,σ)                                              *)
(*            ∝ Σ P(y|x) P(                                                  *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*            ∝ Σ P(y|x) P(σ_0) Π P(x_(i+1),σ_(i+1)|x_i,σ_i) P(x_(i+1)       *)
(*                                                                           *)
(*                                                                            *)
(*      Note that each upwards branch is actually several different           *)
(*        branches: one per output bit which is produced in this step.        *)
(*        The P(x_1) component is only a part of the systematic component.    *)
(*                                                                            *)
(*                                                                            *)
(*           P(x_1)P(y_1|x_1)  P(x_2)P(y_2|x_2)           P(x_n)P(y_n|x_n)    *)
(*                  #                 #                          #            *)
(*                  |                 |                          |            *)
(*                  o x_1             o x_2                      o            *)
(*          σ_0     |       σ_1       |       σ_2                |     σ_n    *)
(*    # ---- o ---- # ------ o ------ # ------ o ------ ... ---- # ---- o     *)
(*  P(σ_0)   P(x_1,σ_1|x_0,σ_0) P(x_2,σ_2|x_1,σ_1)  P(x_n,σ_n|x_(n-1),σ_(n-1))*)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*              σ_0                                                           *)
(*        # ---- o ---- #                                                     *)
(*      P(σ_0)                                                                *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* Based on "Modern Coding Theory" by Tom Richardson and Rüdiger Urbanke,     *)
(* with modifications to work with arbitrary state machines rather than just  *)
(* recursive convolutional codes.                                             *)
(*                                                                            *)
(* Number of variable nodes in this state machine:                            *)
(* - We start in state 0, and each input bit updates the state by 1, so we    *)
(*   have n+1 state variable nodes                                            *)
(*                                                                            *)
(* This seems like a cool formalism approach. In particular, formalize so     *)
(* that BCJR works for a general state machine. Then try to formalize the     *)
(* turbo code BCJR to use this.                                               *)
(*                                                                            *)
(*                                                                            *)
(* TODO: implement this                                                       *)
(* -------------------------------------------------------------------------- *)
(*Definition state_machine_factor_graph_def:
  state_machine_factor_graph m = fg_add_n_variable_nodes () fg_empty
End*)

(* -------------------------------------------------------------------------- *)
(* Decode assuming transmission over a binary symmetric channel               *)
(*                                                                            *)
(* m: the state machine used to encode the message                            *)
(* cs: the message to decode (bs represents the original message, and ds      *)
(*     represents the decoded message)                                        *)
(* p: the probability of an error when a bit is sent over the binary          *)
(*    symmetric channel.                                                      *)
(*                                                                            *)
(* TODO: implement this                                                       *)
(* -------------------------------------------------------------------------- *)
Definition BCJR_decode_def:
  BCJR_decode m cs p = ARB
End

val _ = export_theory();
