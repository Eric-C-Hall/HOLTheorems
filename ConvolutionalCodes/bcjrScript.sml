(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

open factor_graphScript;

val _ = new_theory "bcjr";

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
(*            ∝ Σ P(σ_0) Π P(y_j|x_j) P(x_j) P(x_j,σ_j|x_(j-1),σ(j-1))       *)
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
(*          σ_0     |       σ_1       |                          |     σ_n    *)
(*    # ---- o ---- # ------ o ------ # ------ o ------ ... ---- # ---- o     *)
(*  P(σ_0)                                                                    *)
(*                                                                            *)
(* Based on "Modern Coding Theory" by Tom Richardson and Rüdiger Urbanke,     *)
(* with modifications to work with arbitrary state machines rather than just  *)
(* recursive convolutional codes.                                             *)
(*                                                                            *)
(* Number of variable nodes in this state machine:                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition state_machine_factor_graph_def:
  state_machine_factor_graph m = fg_add_n_variable_nodes () fg_empty
End
  

(* -------------------------------------------------------------------------- *)
(* Decode assuming transmission over a binary symmetric channel               *)
(*                                                                            *)
(* m: the state machine used to encode the message                            *)
(* cs: the message to decode (bs represents the original message, and ds      *)
(*     represents the decoded message)                                        *)
(* p: the probability of an error when a bit is sent over the binary          *)
(*    symmetric channel.                                                      *)
(* -------------------------------------------------------------------------- *)
Definition BCJR_decode_def:
  BCJR_decode m cs p = 
End



val _ = export_theory();
