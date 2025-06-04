(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

open factor_graphTheory;
open extrealTheory;
open probabilityTheory;

open state_machineTheory;
open wf_state_machineTheory;

val _ = new_theory "bcjr";

(* -------------------------------------------------------------------------- *)
(* An implementation of the forward metric for the BCJR algorithm for         *)
(* well-formed state machines                                                 *)
(*                                                                            *)
(* TODO: complete this                                                        *)
(* -------------------------------------------------------------------------- *)
Definition wfm_bcjr_forward_metric_def:
  bcjr_forward_metric m p rs 0 0 = Normal 1 ∧
  bcjr_forward_metric m p rs 0 (SUC s) = Normal 0 ∧
  bcjr_forward_metric m p (rs : bool list) (SUC t) s =
  ∑ (λprev_state.
       (bcjr_forward_metric m t prev_state) *
       (if ∃b. (prev_state, b) ∈ (wfm_transition_inverse m s) then 1 else 0) *
       (let
          produced_bitstring =
          SND (wfm_transition_fn
               (prev_state,
                (@b. (prev_state,b) ∈ (wfm_transition_inverse))
               )
              );
          expected_bitstring =
          DROP (t * wfm_output_length m) (TAKE (wfm_output_length m) rs);
        in
          bsc_probability p produced_bitstring expected_bitstring
       )
    )
    (count m.num_states)
End

(* -------------------------------------------------------------------------- *)
(* TODO: complete this                                                        *)
(* -------------------------------------------------------------------------- *)
Definition bcjr_backward_metric_def:
  bchr_backward_metric m t s = ARB
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
