(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "convolutional_codes";

(* Standard library theories *)
open arithmeticTheory;
open listTheory;
open rich_listTheory;

(* Standard library tactics, etc *)
open dep_rewrite;
open ConseqConv; (* SPEC_ALL_TAC *)
open simpLib;

(* My own libraries *)
open donotexpandLib;
open useful_tacticsLib;

(* My own utility theories *)
open infnumTheory;
open hamming_distanceTheory;
open useful_theoremsTheory;

(* My own core theories *)
open state_machineTheory;
open trellisTheory;

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"
                   
(* -------------------------------------------------------------------------- *)
(* Based on the MIT 6.02 DRAFT Lecture Notes Fall 2010                        *)
(*                                                                            *)
(* TODO: Cite better                                                          *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* If you want to work on my code, I recommend using abbreviations, because   *)
(* many of my variable names are quite long. for example, when I type the     *)
(* letters "gnecs", my emacs will automatically expand this out to            *)
(* "get_num_errors_after_step_slow". Similarly, if I type "vtn", my emcs will  *)
(* automatically expand this out to "viterbi_trellis_node".                   *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Main property we need to prove:                                            *)
(*                                                                            *)
(* The Viterbi algorithm determines the maximum likelihood encoded sequence   *)
(* (Theorem 7.3.1 from A Course in Error-Correcting Codes)                    *)
(*                                                                            *)
(* More detail:                                                               *)
(*                                                                            *)
(* For any sequence cs that could potentially be produced by applying         *)
(* convolutional coding to some sequence and adding some noise to it,         *)
(* then applying the Viterbi algorithm to cs will produce the choice of bs    *)
(* which minimizes the amount of noise that needs to be added to the encoded  *)
(* sequence to produce cs                                                     *)
(* -------------------------------------------------------------------------- *)
(* Alternative formulation using Hidden Markov Models, that does not directly *)
(* capture the convolutional coding aspect:                                   *)
(*                                                                            *)
(* Given an arbitrary Hidden Markov Model and an arbitrary sequence of states *)
(* through that hidden Markov Model, the Viterbi algorithm returns the most   *)
(* likely sequence of states that could have taken through that Hidden Markov *)
(* Model.                                                                     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Describe the relationship between the function for calculating the number  *)
(* of errors computationally during a single step of the Viterbi algorithm,   *)
(* and the function for calculating the total number of errors                *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the input bitstring for which we're finding the code to recreate as    *)
(* closely as possible.                                                       *)
(* s: the state we are aiming to end up in                                    *)
(* t: the time-step we are aiming to end up in                                *)
(* -------------------------------------------------------------------------- *)
Theorem get_num_errors_after_step_get_num_errors:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ∧
  is_reachable m s t ∧
  LENGTH bs = t * m.output_length ⇒
  get_num_errors m bs (vd_find_optimal_code m bs s t) = infnum_to_num (get_num_errors_after_step_slow m bs t (best_origin_slow m bs t s))
Proof
  Induct_on ‘t’ >> rpt strip_tac >> gvs[]
  >- (gvs[get_num_errors_def, get_num_errors_from_state_def, vd_encode_from_state_def]
      >> gvs[get_num_errors_after_step_slow_def]
      >> Cases_on_if_goal >> gvs[]
     )
  (* Reduce SUC in LHS to allow usage of inductive hypothesis *)
  >> gvs[vd_find_optimal_code_suc]
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_append]
  >> gvs[]
  >> conj_tac >- gvs[ADD1]
  (* The inductive hypothesis will be applicable to indL, and the inductive step
     will be applicable to stepL. *)
  >> qmatch_goalsub_abbrev_tac ‘indL + stepL = _’
  (* Reduce SUC in RHS to allow usage of inductive hypothesis *)
  >> gvs[get_num_errors_after_step_slow_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[infnum_to_num_inplus]
  >> qmatch_goalsub_abbrev_tac ‘_ = indR + stepR’
  (* Prove dependencies *)
  >> gvs[]
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM is_reachable_viterbi_trellis_node_slow_num_errors]
  >> gvs[]
  >> gvs[is_reachable_best_origin_slow]
  (* It suffices to prove that the inductive parts are equal and that the step
     parts are equal*)
  >> ‘indL = indR ∧ stepL = stepR’ suffices_by gvs[]
  >> conj_tac
  >- (unabbrev_all_tac
      (* Apply the inductive hypothesis *)
      >> last_x_assum (qspecl_then [‘m’, ‘TAKE (t * m.output_length) bs’, ‘vd_step_back m bs s (SUC t)’] assume_tac)
      >> gvs[]
      >> gvs[vd_find_optimal_code_restrict_input]
      >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC [th])
      (* Simplify *)
      >> gvs[is_reachable_vd_step_back]
      >> gvs[best_origin_slow_restrict_input, get_num_errors_after_step_slow_restrict_input]
      (* Get LHS and RHS into the same form *)
      >> gvs[vd_step_back_def_slow]
      >> gvs[viterbi_trellis_node_slow_def]
      (* Focus in on the parts we need to prove are the same *)
      >> AP_TERM_TAC
      >> AP_TERM_TAC
      >> AP_TERM_TAC
      (* If the if statement is true, it is trivial. Derive a contraditction
         in the case where the if statement is false. *)
      >> Cases_on_if_goal >> gvs[]
      >> ‘F’ suffices_by gvs[]
      (* The if statement cannot be false because it is equivalent to stating that the point is not reachable, and it is reachable *)
      >> gvs[get_num_errors_after_step_slow_is_reachable]
     )
  >> unabbrev_all_tac
  (* Simplify left hand side to make it more similar to right hand side *)
  >> gvs[get_num_errors_from_state_def]
  (* Simplify right hand side to make it more similar to left hand side:
     DROP (t * m.output_length) bs. *)
  >> gvs[relevant_input_def]
  >> gvs[TAKE_DROP_SWAP]
  >> DEP_PURE_ONCE_REWRITE_TAC[TAKE_LENGTH_TOO_LONG]
  (* Simplify dependency *)
  >> conj_tac
  >- gvs[ADD1]
  (* Focus in on the important part we need to proce the equivalence of *)
  >> PURE_REWRITE_TAC[Once hamming_distance_symmetric]
  >> AP_THM_TAC
  >> AP_TERM_TAC
  (*  *)
QED

(* -------------------------------------------------------------------------- *)
(* Main theorem that I want to prove                                          *)
(*                                                                            *)
(* Prove that the result of using Viterbi decoding is the choice of original  *)
(* message that is closer to the input when encoded than any other original   *)
(* message.                                                                   *)
(*                                                                            *)
(* In other words: for all choices of bs, the hamming distance between the    *)
(* received message and the value that bs encodes to is less than or equal to *)
(* the hamming distance between the received message and the value that the   *)
(* Viterbi decoding of the received message encodes to                        *)
(*                                                                            *)
(* rs: the received message                                                   *)
(* bs: the alternate possible original messages                               *)
(* -------------------------------------------------------------------------- *)
(* Proof outline:                                                             *)
(*                                                                            *)
(* - Want to prove a stronger statement: for any of the states at any time    *)
(*   step, the viterbi path arriving at this state is optimal, i.e. going     *)
(*   back through the trellis will provide a path that has a shorter hamming  *)
(*   distance to the appropriate portion of the received string than any      *)
(*   other path which arrives at this state.                                  *)
(*                                                                            *)
(* - Can do this by induction on the maximum timestep: if the maximum         *)
(*   timestep is zero, then it is trivial that the trivial path is optimal to *)
(*   any state. If, on the other hand, the maximum time step is SUC k, and we *)
(*   know that the viterbi path arriving at any node at time step k is        *)
(*   optimal, then any viterbi path to the current node will consist of a     *)
(*   path to a previous node, followed by an additional step. By the          *)
(*   inductive hypothesis, the path to the previous node is optimal, and then *)
(*   the fact that I'm choosing from the best choice on the next step will    *)
(*   essentially make the current node optimal. I skimmed over quite a bit,   *)
(*  there, but that's the idea                                                *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(* Proof of the more general statement of optimality of the viterbi algorithm *)
(* when arriving at any point.                                                *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem viterbi_correctness_general:
  ∀m bs rs s t.
  wfmachine m ∧
  s < m.num_states ∧
  LENGTH bs = t ∧
  LENGTH rs = m.output_length * t ∧
  vd_encode_state m bs = s ⇒
  get_num_errors m rs (vd_find_optimal_code m rs s t) ≤ get_num_errors m rs bs
Proof
  (* Complete base case and simplify *)
  gen_tac
  >> Induct_on ‘t’
  >- gvs[]
  >> rpt strip_tac
  >> donotexpand_tac
  >> gvs[]
  (* Expand out relevant definitions. *)
  (* These are some of the relevant definitions
     - vd_find_optimal_path_def
     - vd_find_optimal_reversed_path_def
     - vd_step_back_def
     - viterbi_trellis_row_def
     - viterbi_trellis_node_def
     - get_better_origin_def
     - get_num_errors_after_step_def *)
  >> gvs[vd_find_optimal_code_def]
  >> gvs[vd_find_optimal_path_def]
  >> gvs[vd_step_back_def]
  >> gvs[viterbi_trellis_row_def]
  >> gvs[viterbi_trellis_node_def]
  >> gvs[GSYM vd_find_optimal_path_def]
  (* For any choice of bs, the encoding of m bs will be some path which
     eventually reaches s. Thus, we can decompose it into ... s'' s.
     The choice of s' was such that it minimizes the number of errors to
     get to the previous state plus the number of errors in the transition
     between s' and s. This is equal to the hamming distance from the
     relevant parts of rs to ... s'' plus the hamming distance from the
     relevant parts of rs to s'' s.*)
  >> qspecl_then [‘m’, ‘bs’] assume_tac path_to_code_code_to_path
  >> gvs[]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
  >> qspecl_then [‘code_to_path m bs’] assume_tac SNOC_LAST_FRONT
  >> Cases_on ‘code_to_path m bs = []’
  >- gvs[]
  >> gvs[]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
  >> gvs[code_to_path_last]
  >> doexpand_tac
  >> first_assum (fn th => PURE_REWRITE_TAC[th])
  >> donotexpand_tac
  (* Split the appended paths apart, so that we can deal with the inductive
     path and the current transition separately. *)
  >> DEP_PURE_REWRITE_TAC[path_to_code_append]
  >> gvs[]
  >> conj_tac
  >- (Cases_on ‘bs’ >> gvs[code_to_path_def, code_to_path_from_state_def])
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_append]
  >> gvs[]
  >> conj_tac
  >- gvs[ADD1]
  (* Split the RHS appended paths apart *)
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_append]
  >> gvs[]
  >> gvs[LENGTH_FRONT]
  >> gvs[PRE_SUB1]
  >> gvs[ADD1]
  >> gvs[code_to_path_length]
  (* Give the components names. *)
  >> qmatch_goalsub_abbrev_tac ‘DROP n’
  >> qmatch_goalsub_abbrev_tac ‘lInd + lStep ≤ rInd + rStep’
  (* lInd + lStep is necessarily better than rInd + rStep, but it is not
     necessarily the case that lInd is better than rInd, nor that lStep
     is better than rStep, because s' is chosen to minimize the total sum
     rather than either individual component.
   *)
  >>  
  
QED

Theorem viterbi_correctness:
  ∀m : state_machine.
  ∀bs rs : bool list.
  wfmachine m ∧
  LENGTH rs = m.output_length * LENGTH bs ⇒
  get_num_errors m rs (vd_decode m rs) ≤ get_num_errors m rs bs
Proof
  rpt strip_tac
  >> gvs[vd_decode_def]
  >> qmatch_goalsub_abbrev_tac ‘vd_find_optimal_path m rs s t’
  (* TODO: bs may not lead to the state s, so we cannot immediately apply the
     generalized viterbi correctness theorem here. We must first prove that
     our specific choice of s will give a better result than any other choice
     of s, so that we can deal with cases in which bs leads to another state.
     Then we can finish our proof by showing that for an arbitrary valid state,
     if we consider all paths bs leading to that state, the path which was
     designed to be optimal is, in fact, optimal.*)
  >> irule viterbi_correctness_general
  >> gvs[]
  >> conj_tac
  >- (unabbrev_all_tac
      >> qmatch_goalsub_abbrev_tac ‘FOLDR (get_better_final_state rs') 0 ts’
      >> qspecl_then [‘rs'’, ‘0’, ‘ts’] assume_tac get_better_final_state_foldr_mem
      >> qmatch_goalsub_abbrev_tac ‘s < m.num_states’
      >> Cases_on ‘s’ >> gvs[]
      >> gvs[Abbr ‘ts’]
      >> gvs[MEM_COUNT_LIST])
  >> conj_tac
  >- (unabbrev_all_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[MULT_DIV]
      >> gvs[]
      >> gvs[wfmachine_output_length_greater_than_zero]
     )
  >> conj_tac
  >- (unabbrev_all_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[MULT_DIV]
      >> gvs[]
      >> gvs[wfmachine_output_length_greater_than_zero]
     )
  >> gvs[vd_encode_state_def, vd_encode_state_from_state_def]

QED

val _ = export_theory();
