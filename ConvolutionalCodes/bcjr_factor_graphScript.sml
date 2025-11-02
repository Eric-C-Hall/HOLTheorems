(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory bcjr_factor_graph

Ancestors factor_graph extreal prim_rec probability state_machine wf_state_machine binary_symmetric_channel

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

(* -------------------------------------------------------------------------- *)
(* Add the function nodes corresponding to the initial input probabilities    *)
(* and errors in the systematic bits.                                         *)
(*                                                                            *)
(* n: the number of bits as input to the convolutional code                   *)
(* p: the probability of an error                                             *)
(* i: the current node being added. Initially should be 0, ranges up to n.    *)
(* prior: a list of the prior probabilities of each input bit being 1         *)
(* ds: the received systematic bits                                           *)
(* fg: the factor graph we are modifying (fg is the last argument to make it  *)
(*     easier to compose)                                                     *)
(* -------------------------------------------------------------------------- *)
Definition rcc_factor_graph_add_func_nodes_input_sys:
  rcc_factor_graph_add_func_nodes_input_sys n p i prior ds fg =
  if n ≤ i
  then
    fg
  else
    (rcc_factor_graph_add_func_nodes_input_sys n p (i + 1) prior ds)
    (fg_add_function_node
     {INR i}
     (λbss. (EL i prior) * (if EL i ds ⇎ HD (HD bss) then p else 1 - p))
     fg)
Termination
  WF_REL_TAC ‘measure (λ(n,p,i,prior,ds,fg). n - i)’
End

(* -------------------------------------------------------------------------- *)
(* Add the function nodes corresponding to errors in the encoded bits         *)
(*                                                                            *)
(* fg                                                                         *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition rcc_factor_graph_add_func_nodes_enc_def:
  rcc_factor_graph_add_func_nodes_enc fg =
End

(* -------------------------------------------------------------------------- *)
(* Add the function nodes corresponding to the state transitions              *)
(* -------------------------------------------------------------------------- *)
Definition rcc_factor_graph_add_func_nodes_state_def:
  rcc_factor_graph_add_func_nodes_state fg = ARB
End

(* -------------------------------------------------------------------------- *)
(* The factor graph for a recursive systematic convolutional code with one    *)
(*   set of parity equations.                                                 *)
(*                                                                            *)
(*                                                     P(b_{n-1}) *           *)
(*          P(b_0)P(d_0|b_0)    P(b_1)P(d_1|b_1)       P(d_{n-1}|b_{n-1})     *)
(*                 #                 #                          #             *)
(*                 |                 |                          |             *)
(*                 o b_0             o b_1              b_{n-1} o             *)
(* P(σ_0)  σ_0     |       σ_1       |       σ_2                |    σ_{n-1}  *)
(*   # ---- o ---- # ------ o ------ # ------ o ------ ... ---- # ---- o      *)
(*          P(cp_0,σ_1|       P(cp_1,σ_2|                P(cpn-1,σn|          *)
(*                 b_0,σ_0)         b_1,σ_1)                   bn-1,σn-1)     *)
(*                 |                 |                          |             *)
(*                 o cp_0            o cp_1                     o cp_{n-1}    *)
(*                 |                 |                          |             *)
(*                 #                 #                          #             *)
(*            P(dp_0|cp_0)        P(cp_1|b_1)             P(cp_{n-1}|b_{n-1})  *)
(*                                                                            *)
(*                                                                            *)
(* The n variable nodes relating to the inputs b_i have labels 0 through n    *)
(* The n variable nodes relating to the encoded inputs cp_i have labels       *)
(*   n + 1 through 2n                                                         *)
(* The (n + 1) variable nodes relating to the states σ_i have labels 2n + 1   *)
(*   through 3n + 1                                                           *)
(*                                                                            *)
(* The n function nodes relating to the probability of c_i given b_i have     *)
(*   labels 3n + 2 through 4n + 1                                             *)
(* The n function nodes relating to the probability of cp_i given b_i have *)
(*   labels 4n + 2 through 5n + 1                                             *)
(* The n + 1 function nodes relating to the probability of the next state and *)
(*   output given the current state have labels 5n + 2 through 6n + 2         *)
(* -------------------------------------------------------------------------- *)
Definition rcc_factor_graph_def:
  state_machine_factor_graph n (ps,qs) =
  (rcc_factor_graph_add_func_nodes_state)
  ∘ (rcc_factor_graph_add_func_nodes_enc)
  ∘ (rcc_factor_graph_add_func_nodes_input_sys)
  ∘ (fg_add_n_variable_nodes (3 * n + 1)) fg_empty
End

