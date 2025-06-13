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
(* priors: the prior probabilities that each of the sent bits are equal to 1, *)
(*         as an extreal list                                                 *)
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
(*   appropriate transition from the predecessor state (which is dependent on *)
(*   the prior probability of the relevant input bit being read) multiplied   *)
(*   by the probability of receiving the appropriate bits given that the bits *)
(*   corresponding to this transition were sent.                              *)
(* -------------------------------------------------------------------------- *)
Definition bcjr_forward_metric_wfm_def:
  bcjr_forward_metric_wfm m p priors rs 0 0 = Normal 1 ∧
  bcjr_forward_metric_wfm m p priors rs 0 (SUC s) = Normal 0 ∧
  bcjr_forward_metric_wfm m p priors rs (SUC t) s =
  ∑ (λ(prev_state, b).
       (bcjr_forward_metric_wfm m p priors rs t prev_state) *
       (if b then EL t priors else 1 - EL t priors) *
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
(* priors: the prior probabilities that each of the sent bits are equal to 1, *)
(*         as an extreal list                                                 *)
(* rs: the ultimately received data, after encoding and noise                 *)
(* t: the time-step in the trellis to calculate the backward metric at        *)
(* s: the state in the trellis to calculate the backward metric at            *)
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
(*   transition to that state (which depends on the prior probability of      *)
(*   receiving the associated input) multiplied by the probability of         *)
(*   receiving the appropriate bits relating to this transition that was      *)
(*   taken.                                                                   *)
(* -------------------------------------------------------------------------- *)
Definition bcjr_backward_metric_wfm_def:
  bcjr_backward_metric_wfm m p priors rs t s =
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
           (bcjr_backward_metric_wfm m p priors rs (t + 1) next_state) *
           (if b then EL t priors else 1 - EL t priors) *
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
  WF_REL_TAC ‘measure (λ(m,p,priors,rs,t,s).(LENGTH rs DIV wfm_output_length m) - t)’
End

(* -------------------------------------------------------------------------- *)
(* Calculate gamma_t from the BCJR algorithm.                                 *)
(*                                                                            *)
(* This is the probability that we take a path through the trellis, and that  *)
(* we then observe the appropriate observed bits, and the path we took had    *)
(* the t-th input bit set to 1.                                               *)
(*                                                                            *)
(* m: the well-formed state machine (abstract type)                           *)
(* p: the probability defining the binary symmetric channel                   *)
(* priors: the prior probabilities that each of the sent bits are equal to 1, *)
(*         as an extreal list                                                 *)
(* rs: the ultimately received data, after encoding and noise                 *)
(* t: the time-step in the trellis which is having the input set to 1         *)
(*                                                                            *)
(* We sum over the probabilities of all possible starting/ending states for   *)
(* the t-th transition. We only sum over a starting state and ending state if *)
(* the transition corresponding to the input 1 arrives at the appropriate     *)
(* ending state, because we are requiring the t-th input bit to be 1.         *)
(*                                                                            *)
(* We use the forward metric to calculate the probability of observing the    *)
(* appropriate bits up to the current step (i.e. with the same t).            *)
(*                                                                            *)
(* We use the backward metric to calculate the probability of observing the   *)
(* appropriate bits from the next step onwards (i.e. with the subsequent t)   *)
(*                                                                            *)
(* To calculate the probability relating to the current transition, which has *)
(* the input bit set to 1, we take the probability of receving the            *)
(* appropriate information given that we produced the output corresponding to *)
(* the transition, multiply it by the probability of taking this transition   *)
(* given that the current bit was 1, and multiply this by the prior           *)
(* probability of the current bit being 1.                                    *)
(* -------------------------------------------------------------------------- *)
Definition bcjr_gamma_t_wfm_def:
  bcjr_gamma_t_wfm m p priors rs t s =
  ∑ (λ(s1, s2).
       bcjr_forward_metric_wfm m p priors rs t s1 *
       (let
          produced_bitstring = SND (wfm_transition_fn m (s1, T));
          expected_bitstring =
          TAKE (wfm_output_length m)
               (DROP (t * wfm_output_length m) rs);
        in
          bsc_probability p produced_bitstring expected_bitstring            
       ) *
       (EL t priors) *
       bcjr_backward_metric_wfm m p priors rs (SUC t) s2)
    {(s1, s2) | FST (wfm_transition_fn m (s1, T)) = s2 ∧
                s1 < wfm_num_states m ∧
                s2 < wfm_num_states m }
End

(* -------------------------------------------------------------------------- *)
(* Return the probability of a particular bit being equal to 1 given that     *)
(* the received data was originally encoded using a recursive convolutional   *)
(* code.                                                                      *)
(*                                                                            *)
(* m: the well-formed state machine (abstract type)                           *)
(* p: the probability defining the binary symmetric channel                   *)
(* priors: the prior probabilities that each of the sent bits are equal to 1, *)
(*         as an extreal list                                                 *)
(* rs: the ultimately received data, after encoding and noise                 *)
(* t: the time-step we are finding the a posteriori probability for           *)
(*                                                                            *)
(* TODO: Ensure that this correctly handles decoding of zero-tailed sequences.*)
(* -------------------------------------------------------------------------- *)
Definition bcjr_prob_wfm_def:
  bcjr_prob_wfm m p priors rs t s =
  let
    last_t = LENGTH rs
  in
    bcjr_gamma_t_wfm m p priors rs t s /
                     bcjr_forward_metric_wfm m p priors rs last_t 0
End

(* -------------------------------------------------------------------------- *)
(* A version of bcjr_gamma_t_wfm which does not use the systematic data from  *)
(* the current step.                                                          *)
(*                                                                            *)
(* Thus, it provides only the extrinsic data, and not the intrinsic data      *)
(*                                                                            *)
(* We assume that the systematic component is the first component.            *)
(* -------------------------------------------------------------------------- *)
Definition bcjr_gamma_t_wfm_exclude_current_def:
  bcjr_gamma_t_wfm m p priors rs t s =
  ∑ (λ(s1, s2).
       bcjr_forward_metric_wfm m p priors rs t s1 *
       (let
          produced_bitstring = SND (wfm_transition_fn m (s1, T));
          expected_bitstring =
          TAKE (wfm_output_length m)
               (DROP (t * wfm_output_length m) rs);
          produced_bitstring_no_sys = TL produced_bitstring;
          expected_bitstring_no_sys = TL expected_bitstring;
        in
          bsc_probability p produced_bitstring_no_sys expected_bitstring_no_sys
       ) *
       (EL t priors) *
       bcjr_backward_metric_wfm m p priors rs (SUC t) s2)
    {(s1, s2) | FST (wfm_transition_fn m (s1, T)) = s2 ∧
                s1 < wfm_num_states m ∧
                s2 < wfm_num_states m }
End

val _ = export_theory();
