
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
  (* The plan:
     - use induction
     - the bitstring on the left hand side can be split into two parts: the
       string leading up to and arriving at the final best origin, and then
       the remaining string consisting of stepping from the best origin to
       the end. By the definition of best-origin, this total sum is minimized
       amongst all possible choices of final origin, assuming we take the
       optimal path up to the origin, and then take the final step.
     - the bitstring on the right hand side can also be split into two parts:
       the string leading up to and arriving at the final origin, and the
       remaining string consisting of stepping from the best origin to the
       end.
     - By the inductive hypothesis, the string leading up to and arriving at
       the final origin on the right hand side will provide a worse result than
       taking the optimal path to the final origin on the right hand side. Thus,
       our right hand side becomes having an optimal path up until the final
       origin, then taking a final step.
     - 
     - See get_num_errors_get_num_errors_after_step_slow: this is a useful
       property that we have already proven, which relates the number of
       errors of a decoded string to the number of errors calculated using
       the trellis functions.
   *)
  (* Complete base case and simplify *)
  gen_tac
  >> Induct_on ‘t’
  >- gs[]
  >> rpt strip_tac
  (* This is easier to solve when we simplify it to the form of
     get_num_errors_after_step_slow applied to best_origin_slow,
     since best_origin_slow is defined such that it minimizes get_num_errors_after_step_slow. *)
  >> rw[get_num_errors_get_num_errors_after_step_slow]
  >> simp[best_origin_slow_def]
  >> qmatch_goalsub_abbrev_tac ‘infnum_to_num (f (inargmin _ ls))’
  >> qspecl_then [‘f’, ‘ls’] assume_tac inargmin_inle
  >> gs[]
  (* Now we need to get the right hand side into the form of f applied to
   something. Since bs may not take the optimal path, we will need to
   split it up into two halves. We'll show that taking the optimal
   path up until the last step will provide a better result than
   taking an arbitrary path up until the last step, at which point the
   result will in theory be equivalent to f applied to the last transition.
.
   Our first step is to break this up into the two parts.
   *)
  >> qmatch_goalsub_abbrev_tac ‘LHS ≤ _’
  >> Cases_on ‘bs’ using SNOC_CASES >> gs[]
  >> gs[SNOC_APPEND]
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_append]
  >> gs[]
  >> conj_tac >- gs[ADD1]
  >> qmatch_goalsub_abbrev_tac ‘_ ≤ step + ind’
  >> qmatch_asmsub_abbrev_tac ‘DROP indLength’
  (*>> qmatch_asmsub_abbrev_tac ‘get_num_errors m indString’
    >> qmatch_asmsub_abbrev_tac ‘get_num_errors m stepString [x]’*)
  (* Show that taking the optimal path up until the last step provides a better
     result than taking an arbitrary path up until the last step. This uses
     the inductive hypothesis. *)
  >> sg ‘step + get_num_errors m (TAKE indLength rs) (vd_decode_to_state m (TAKE indLength rs) (vd_encode_state m l 0) (LENGTH l)) 0 ≤ step + ind’
  >- (gvs[]
      >> gvs[Abbr ‘ind’]
      >> last_x_assum $ qspecl_then [‘l’, ‘TAKE indLength rs’] assume_tac
      >> gvs[]
      >> unabbrev_all_tac
      >> gvs[])
  >> qmatch_asmsub_abbrev_tac ‘step + optInd ≤ step + ind’
  >>  ‘LHS ≤ step + optInd’ suffices_by gvs[]
  (* If we were to show that the right hand side was equal to f applied to
     the last transition, that would be sufficient. *)
  >> qsuff_tac ‘step + optInd = infnum_to_num (f (<| origin := vd_encode_state m l 0; input := x; |>))’
  >- (gvs[]
      >> disch_tac >> pop_assum kall_tac
      >> gvs[Abbr ‘LHS’]
      >> cheat (* I will need to modify this to better handle infinity, but
                  other than that, it looks pretty simple, so I'll leave it
                  for now *)
     )
  (* We no longer need ind, as we have replaced it with optInd *)
  >> qpat_x_assum ‘_ ≤ _ + ind’ kall_tac
  >> qpat_x_assum ‘Abbrev (ind = _)’ kall_tac
  (* Now we need to actually show that the step plus the inductive part is
     equal to f applied to the transition. We want to get the left hand side
     into a form involving f, which should arise naturally when aiming for
     a form involving get_num_errors_after_step_slow.
.
     First, expand out the part we are focusing on, and collapse the part we
     are not focusing on.
   *)
  >> qmatch_goalsub_abbrev_tac ‘_ = RHS’
  >> gvs[Abbr ‘LHS’, Abbr ‘step’, Abbr ‘optInd’]
  >> simp[Abbr ‘indLength’]
  (* We now want to reverse the effects of get_num_errors_append. When the
     inductive part and the step are combined, we'll get closer to having
     get_num_errors_after_step_slow, which combines these parts.
.
     Note: maybe instead of taking this approach, it would've been better
     to take the approach of simplifying get_num_errors_after_step_slow
     into two parts. Too late now.
.
     In order to
     draw parallels between the current state of the goal and this theorem,
     collapse irrelevant parts into a new abbreviation called bs'. *)
  >> PURE_ONCE_REWRITE_TAC[ADD_COMM]
  >> qmatch_goalsub_abbrev_tac ‘get_num_errors m _ bs' _’
  (* assume the relevant values for the variables in the theorem. *)
  >> qspecl_then [‘m’, ‘rs’, ‘bs'’, ‘[x]’, ‘0’] assume_tac (GSYM get_num_errors_append)
  >> gvs[ADD1]
  (* The differences between the assumed theorem and the corresponding part of
     the goal are: LENGTH bs' vs LENGTH l and vd_encode_state m bs' 0 vs
     vd_encode_state m l 0. Prove each of these equalities, starting with
     LENGTH bs' = LENGTH l *)
  >> sg ‘LENGTH bs' = LENGTH l’
  >- (unabbrev_all_tac
      >> gvs[])
  >> gvs[]
  >> sg ‘vd_encode_state m bs' 0 = vd_encode_state m l 0’
  >- (unabbrev_all_tac
      >> gvs[])
  (* After applying gvs, we have successfully recombined the append. *)
  >> gvs[]
  (* Clean up assumptions that are no longer necessary *)
  >> qpat_x_assum ‘get_num_errors _ _ _ _ + get_num_errors _ _ _ _ = get_num_errors _ _ (APPEND _ _) _’ kall_tac
  >> qpat_x_assum ‘vd_encode_state m bs' 0 = vd_encode_state m l 0’ kall_tac
  (* Simplify the RHS in the direction of the LHS *)
  >> gvs[Abbr ‘RHS’]
  >> gvs[Abbr ‘f’]
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM get_num_errors_get_num_errors_after_step_slow]
  
  (* Expand so we can see what we need to work on *)


        
  >> gvs[Abbr ‘bs'’]
  (* *)
  >> qmatch_goalsub_abbrev_tac ‘get_num_errors _ _ ((vd_decode_to_state _ _ _ _) ⧺ _)’
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_get_num_errors_after_step_slow]
  >> 

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
  >> gvs[get_num_errors_get_num_errors_after_step_slow]
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
      >> gvs[get_num_errors_get_num_errors_after_step_slow]
      >> gvs[best_origin_slow_def])
  (* Now we prove that decoding minimizes the number of errors to arrive at
     a particular state*)
  >> gvs[Abbr ‘LHS’, Abbr ‘RHS’, Abbr ‘MHS’]
  >> gvs[GSYM get_num_errors_get_num_errors_after_step_slow]
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
