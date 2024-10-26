
(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "convolutional_codes";

(* Standard library theories *)
open arithmeticTheory;
open listTheory;
open markerTheory;
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
  >> ‘LHS ≤ step + optInd’ suffices_by gvs[]
  (* If we were to show that the right hand side was equal to f applied to
     the last transition, that would be sufficient. *)
  >> qsuff_tac ‘step + optInd = infnum_to_num (f (<| origin := vd_encode_state m l 0; input := x; |>))’
  >- (gvs[]
      >> disch_tac >> pop_assum kall_tac
      >> gvs[Abbr ‘LHS’]
      >> unabbrev_all_tac
      >> qmatch_goalsub_abbrev_tac ‘infnum_to_num (f (inargmin _ qs)) ≤ infnum_to_num (f q)’
      >> qmatch_goalsub_abbrev_tac ‘infnum_to_num min ≤ infnum_to_num specific’
      >> sg ‘f (inargmin (λa. f a) qs) ≤ f q’
      >- (gvs[ETA_THM]
          >> unabbrev_all_tac
          >> irule inargmin_inle
          >> gvs[transition_inverse_mem] (* TODO: should transition_inverse_mem and all_transitions_mem be simp rules? *)
          >> gvs[all_transitions_mem]
          >> gvs[GSYM SNOC_APPEND]
          >> gvs[vd_encode_state_snoc]
         )
      >> qsuff_tac ‘min ≠ INFINITY ∧ specific ≠ INFINITY’
      >- gvs[]
      >> gvs[Abbr ‘min’, Abbr ‘specific’]
      >> qsuff_tac ‘f q ≠ INFINITY’
      >- (gvs[]
          >> qmatch_goalsub_abbrev_tac ‘LHS ≠ INFINITY ⇒ RHS ≠ INFINITY’
          >> Cases_on ‘LHS’ >> Cases_on ‘RHS’ >> gvs[]
          >> qpat_x_assum ‘f (inargmin _ _) ≤ f _’ kall_tac
          >> unabbrev_all_tac
          >> gvs[get_num_errors_after_step_slow_def]
         )
      >> unabbrev_all_tac
      >> gvs[get_num_errors_after_step_slow_def]
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
  >> all_tac (* avoid adjacent comments by performing a no-op *)
  (* Simplify the RHS in the direction of the LHS *)
  >> gvs[Abbr ‘RHS’]
  >> gvs[Abbr ‘f’]
  (* Simplify get_num_errors_after_step_slow into two parts, written
     in terms of get_num_errors *)
  >> gvs[get_num_errors_after_step_slow_get_num_errors, ADD1]
  >> gvs[vd_decode_to_state_restrict_input]
  (* Simplify relevant_input in the direction of DROP _ _ *)
  >> gvs[relevant_input_def]
  >> gvs[TAKE_LENGTH_TOO_LONG]
  >> gvs[get_num_errors_def]
  >> gvs[hamming_distance_symmetric]
QED

Theorem best_state_fn_zero:
  ∀m rs.
    (λs. (EL s (viterbi_trellis_row m rs 0)).num_errors) = (λs. if (s = 0) then N0 else (if s < m.num_states then INFINITY else (EL s (viterbi_trellis_row m rs 0)).num_errors))
Proof
  rpt strip_tac
  >> gvs[FUN_EQ_THM]
  >> rpt strip_tac
  >> rw[]
  >> gvs[viterbi_trellis_row_def]
  >> Cases_on ‘s’ >> gvs[]
QED

Theorem MEM_ZERO_MAP_SUC[simp]:
  ∀ls.
    MEM 0 (MAP SUC ls) ⇔ F
Proof
  rpt strip_tac
  >> Induct_on ‘ls’ >> gvs[]
QED

(* Prove that best_state in vd_decode_def is 0 at time 0. *)
Theorem best_state_zero_zero[simp]:
  ∀m rs.
    wfmachine m ⇒
    inargmin (λs. (EL s (viterbi_trellis_row m rs 0)).num_errors)
             (COUNT_LIST m.num_states) = 0
Proof
  rpt strip_tac
  >> Cases_on ‘COUNT_LIST m.num_states’ >> gvs[]
  >> Cases_on ‘m.num_states’ >> gvs[]
  >> gvs[COUNT_LIST_def]
  >> gvs[inargmin_def]       
  >> Cases_on ‘n = 0’ >> gvs[]
  >> PURE_REWRITE_TAC[inargmin2_def]
  >> gvs[]
  >> rw[]
  >> ‘F’ suffices_by gvs[]
  >> qmatch_asmsub_abbrev_tac ‘(EL best_state _).num_errors ≤ N0’
  >> qmatch_asmsub_abbrev_tac ‘inargmin f _’
  (* Rewrite _.num_errors ≤ N0 as f best_state ≤ N0 *)
  >> ‘f best_state ≤ N0’ by gvs[] >> qpat_x_assum ‘_.num_errors ≤ N0’ kall_tac
  (* *)
  >> ‘MEM best_state (MAP SUC (COUNT_LIST n))’ by (unabbrev_all_tac >> gvs[])
  >> qpat_x_assum ‘Abbrev (best_state = _)’ kall_tac
  >> gvs[best_state_fn_zero]
  >> unabbrev_all_tac
  >> gvs[]
  >> Cases_on ‘best_state = 0’ >> gvs[]
  >> Cases_on ‘best_state < SUC n’ >> gvs[]
  >> gvs[MEM_MAP] (* TODO: Should this be in simp set? *)
  >> gvs[MEM_COUNT_LIST] (* TODO: Should this be in simp set? *)
QED

Theorem exists_is_reachable:
  ∀m t.
    wfmachine m ⇒
    ∃s. s < m.num_states ∧ is_reachable m 0 s t
Proof
  rpt strip_tac
  >> Induct_on ‘t’
  >- (qexists ‘0’ >> gvs[])
  >> gvs[]
  >> qexists ‘(m.transition_fn <|origin := s; input := F |>).destination’
  >> gvs[]
  >> gvs[is_reachable_suc]
  >> qexistsl [‘s’, ‘F’]
  >> gvs[]
QED

Theorem inle_not_infinity:
  ∀i j.
    i ≤ j ∧
    j ≠ INFINITY ⇒
    i ≠ INFINITY
Proof
  rpt strip_tac
  >> Cases_on ‘i’ >> Cases_on ‘j’ >> gvs[]
QED

Theorem best_state_is_reachable[simp]:
  ∀m rs t.
    wfmachine m ⇒
    is_reachable m 0 (inargmin (λs. (EL s (viterbi_trellis_row m rs t)).num_errors) (COUNT_LIST m.num_states)) t
Proof
  rpt strip_tac
  >> qspecl_then [‘m’, ‘t’] assume_tac exists_is_reachable
  >> gvs[]
  >> qspecl_then [‘m’, ‘rs’] assume_tac is_reachable_viterbi_trellis_node_slow_num_errors
  >> pop_assum (fn th => gvs[th])
  >> qmatch_goalsub_abbrev_tac ‘inargmin f ls’
  >> sg ‘f (inargmin f ls) ≤ f s’
  >- (irule inargmin_inle
      >> unabbrev_all_tac
      >> gvs[MEM_COUNT_LIST]
     )
  >> unabbrev_all_tac
  >> gvs[]
  >> gvs[viterbi_trellis_row_el]
  >> qmatch_goalsub_abbrev_tac ‘least_num_errors ≠ INFINITY’
  >> gvs[]
  >> metis_tac[inle_not_infinity]
QED

Theorem viterbi_correctness:
  ∀m bs rs.
    wfmachine m ∧
    LENGTH rs = m.output_length * LENGTH bs ⇒
    get_num_errors m rs (vd_decode m rs) 0 ≤ get_num_errors m rs bs 0
Proof
  rpt strip_tac
  >> gvs[vd_decode_def]
  >> qmatch_goalsub_abbrev_tac ‘get_num_errors m rs (vd_decode_to_state m rs best_state _)’
  >> gvs[MULT_DIV] (* TODO: Should MULT_DIV be in the simp set already? *)
  >> qmatch_goalsub_abbrev_tac ‘best_state_best_path_errs ≤ actual_state_actual_path_errs’
  >> qabbrev_tac ‘actual_state_best_path_errs = get_num_errors m rs (vd_decode_to_state m rs (vd_encode_state m bs 0) (LENGTH bs)) 0’
  >> qsuff_tac ‘best_state_best_path_errs ≤ actual_state_best_path_errs ∧
                actual_state_best_path_errs ≤ actual_state_actual_path_errs’
  >- gvs[]
  >> conj_tac >> gvs[Abbr ‘best_state_best_path_errs’, Abbr ‘actual_state_best_path_errs’, Abbr ‘actual_state_actual_path_errs’]
  >- (unabbrev_all_tac
      >> qmatch_goalsub_abbrev_tac ‘inargmin f ls’
      >> DEP_PURE_REWRITE_TAC[get_num_errors_get_num_errors_after_step_slow]
      >> gvs[]
      >> conj_tac
      >- (unabbrev_all_tac
          >> gvs[]
         )
      >> sg ‘f (inargmin f ls) ≤ f (vd_encode_state m bs 0)’
      >- (irule inargmin_inle
          >> unabbrev_all_tac
          >> gvs[MEM_COUNT_LIST]
         )
      >> DEP_PURE_ONCE_REWRITE_TAC[infnum_to_num_inle]
      >> gvs[]
      >> conj_tac
      >- (gvs[get_num_errors_after_step_slow_is_reachable]
          >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_after_step_slow_is_reachable]
          >> gvs[]
          >> sg ‘inargmin f ls < m.num_states’
          >- (unabbrev_all_tac
              >> gvs[]
             )
          >> gvs[]
          >> unabbrev_all_tac
          >> gvs[]
         )
      >> unabbrev_all_tac
      >> gvs[]
      >> gvs[viterbi_trellis_row_el]
      >> gvs[viterbi_trellis_node_slow_def]
     )
  >> irule viterbi_correctness_general
  >> gvs[]
QED

val _ = export_theory();
