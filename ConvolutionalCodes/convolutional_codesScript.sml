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
open argminTheory;
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
(*   there, but that's the idea                                               *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(* Proof of the more general statement of optimality of the viterbi algorithm *)
(* when arriving at any point.                                                *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(* Todo: start from the init state rather than 0                              *)
(* -------------------------------------------------------------------------- *)
Theorem viterbi_correctness_general:
  ∀m bs rs s t.
    wfmachine m ∧
    s < m.num_states ∧
    LENGTH bs = t ∧
    LENGTH rs = m.output_length * t ∧
    vd_encode_state m bs 0 = s ⇒
    get_num_errors m rs (vd_decode_to_state m rs s t) 0 ≤ get_num_errors m rs bs 0
Proof
  (* We would like to prove that

Follow the plan outlined above:
     - use induction
     - at each step, the previous element is defined to be the best origin.
     - the bitstring on the left hand side can be split into two parts: the
       string leading up to and arriving at the final best origin, and then
       the remaining string consisting of stepping from the best origin to
       the end. By the definition of best-origin, this total sum is minimized
       amongst all possible choices of final origin, assuming we take the
       optimal path up to the best origin, and then take the
     - See get_num_errors_after_step_slow_get_num_errors: this is a useful
       property that we have already proven, which relates the number of
       errors of a decoded string to the number of errors calculated using
       the trellis functions.
     - However, this is not enough to prove the inequality, because it may be
       that the right-hand-side does not take the optimal path up until the
       previous
     - Note that we have already proven that the number of errors through the
       decoded path is equal to the number of errors calculating after taking
       the slow step 

is the optimal string that arrives
       at states s and t (although we have not yet proved it is optimal).
       In a previous theorem, we have proved that the left hand side expression

total number of errors on the left hand side is equal to the
       sum of an inductive part and a step part. The 

       
       optimal number of errors up until the best origin,
       followed by a certain number of errors. such that this sum is optimized
       amongst all choices of origin
     - The right hand side can similarly be split into a path up until some
       final origin, followed by another step.
     - The left hand side can be rewritten as 
       
     since the We will use induction, since the previous
     best_origin is defined to be optimal with respect *)

  (* Complete base case and simplify *)
  gen_tac
  >> Induct_on ‘t’
  >- gvs[]
  >> rpt strip_tac
  (* This is easier to solve when we simplify it to the form of
     get_num_errors_after_step_slow applied to best_origin_slow,
     since best_origin_slow is defined such that it minimizes get_num_errors_after_step_slow. *)
  >> gvs[get_num_errors_after_step_slow_get_num_errors]
  >> simp[best_origin_slow_def]
  >> qmatch_goalsub_abbrev_tac ‘infnum_to_num (f (inargmin _ ls))’
  >> qspecl_then [‘f’, ‘ls’] assume_tac inargmin_inle
  >> gvs[]
        

(*gen_tac
   >> Induct_on ‘t’
   >- gvs[]
   >> rpt strip_tac
   >> donotexpand_tac
   >> gvs[]
   (* Reduce "SUC t" to "t" in order to apply the inductive hypothesis *)
   >> gvs[vd_decode_to_state_def]
   >> gvs[SNOC_APPEND]
   >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_append]
   (* prove dependencies *)
   >> gvs[]
   >> conj_tac >- gvs[ADD1]
   (* Give things nice names.
     - optStep: the optimal step to optimize the overall sum (the step itself
                is not necessarily the minimum cost step, but it will end up
                optimizing the overall sum) 
     - optInd: the optimal path which leads up to the state . By the inductive hypotesis, this*)
>> qmatch_goalsub_abbrev_tac ‘optStep + optInd ≤ _’
   (* Modify the  *)*)
  


                             
(* Note that the best origin here is defined in such a way that it is the
     choice which minimizes the entire expression. If we can change this
     expression to be in the form *)

(* This bs has some penultimate element. The RHS is equivalent to the number
   of errors up to the penultimate element, plus the number of errors from the
   penultimate element.



 *)
                             
(*(* ATTEMPTED THIS ALTERNATE PROOF METHOD, BUT IT DID NOT END UP WORKING OUT *)
  (* Complete base case and simplify *)
  gen_tac
  >> Induct_on ‘t’
  >- gvs[]
  >> rpt strip_tac
  (* This is easier to solve when we simplify it to the form of
     get_num_errors_after_step_slow applied to best_origin_slow,
     since best_origin_slow is defined such that it minimizes get_num_errors_after_step_slow. *)
  >> gvs[get_num_errors_after_step_slow_get_num_errors]
  >> simp[best_origin_slow_def]
  >> qmatch_goalsub_abbrev_tac ‘infnum_to_num (f (inargmin _ ls))’
  >> qspecl_then [‘f’, ‘ls’] assume_tac inargmin_inle
  >> gvs[]
  (* We want to transform the right hand side into a form involving f, so that
     we can use the main property of inargmin to prove that the left hand side
     is less than or equal to the right hand side.
.
     The most sensible way to do this would be to use the theorem which related
     get_num_errors_after_step_slow to get_num_errors. However, this requires
     that bs be in the form best_origin_slow _ _ _ _. But bs may not be in this
     form. Nevertheless, bs is still a "worse" option than whatever the best
     origin is which leads to the same state and timestep that bs leads to,
     so it should be possible to show that the number of errors via bs is at
     least as big as the best origin leading to that state and timestamp, which
     is then at least as big as the left hand side
 *)
  >> qmatch_goalsub_abbrev_tac ‘LHS ≤ RHS’
  >> ‘get_num_errors m rs (vd_decode_to_state m rs (vd_encode_state m bs 0) (LENGTH bs)) 0 = ARB ⇒ T’ by gvs[]
  >> qmatch_asmsub_abbrev_tac ‘MHS = ARB ⇒ T’
  >> qsuff_tac ‘LHS ≤ MHS ∧ MHS ≤ RHS’ >> gvs[]
  (* We have now split it up into proving two inequalities as per the above
     comment *)
  >> conj_tac
  (* First we prove the inequality that the inargmin minimizes over any
     application of the function that was inargmin'd over *)
  >- (gvs[Abbr ‘LHS’, Abbr ‘RHS’, Abbr ‘MHS’]
      >> gvs[get_num_errors_after_step_slow_get_num_errors]
      >> gvs[best_origin_slow_def])
  (* Now we prove that decoding minimizes the number of errors to arrive at
     a particular state*)
  >> gvs[Abbr ‘LHS’, Abbr ‘RHS’, Abbr ‘MHS’]
  >> gvs[GSYM get_num_errors_after_step_slow_get_num_errors]
  >> unabbrev_all_tac
 *) 
QED

(*Theorem viterbi_correctness:
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
QED*)
val _ = export_theory();
