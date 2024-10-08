open HolKernel Parse boolLib bossLib;

val _ = new_theory "trellis";

(* Standard library theories *)
open arithmeticTheory;
open dividesTheory;
open listTheory;
open rich_listTheory;

(* Standard library tactics, etc *)
open dep_rewrite;
open ConseqConv; (* SPEC_ALL_TAC *)

(* My own libraries *)
open donotexpandLib;
open useful_tacticsLib;

(* My own utility theories *)
open infnumTheory;
open hamming_distanceTheory;
open argminTheory;

(* My own core theories *)
open state_machineTheory;

(* -------------------------------------------------------------------------- *)
(* VITERBI DECODING                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Each node in the trellis contains the number of errors on an optimal path  *)
(* to this point in the trellis as well as the previous state on an optimal   *)
(* path to this point in the trellis.                                         *)
(* -------------------------------------------------------------------------- *)
Datatype:
  viterbi_node_datatype = <|
    num_errors : infnum;
    prev_state : α option;
  |> 
End

(* -------------------------------------------------------------------------- *)
(* Returns the portion of the input bitstring which is relevant to the        *)
(* current time-step                                                          *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire input bitstring                                             *)
(* t: the time-step to take the input for. We will return the appropriate     *)
(*    input for calculating the value of the node in the trellis which is at  *)
(*    time-step t. This also means that our inputs are indexed starting at 1, *)
(*    rather than 0, so that the first slice of input is indexed with 1,      *)
(*    rather than 0.                                                          *)
(*                                                                            *)
(* Output: the corresponding portion of the input bitstring.                  *)
(* -------------------------------------------------------------------------- *)
Definition relevant_input_def:
  relevant_input m bs t = TAKE m.output_length (DROP ((t - 1) * m.output_length) bs)
End

(* -------------------------------------------------------------------------- *)
(* Returns the total number of errors that would be present if we took a path *)
(* through the transition with origin r, given the number of errors in the    *)
(* previous row.                                                              *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire input bitstring                                             *)
(* t: the time-step that we will arrive at after taking the transition r. The *)
(*    origins are at the prior time-step to t.                                *)
(* r: the choice of origin that we are returning the number of errors for if  *)
(*    we were to pass through this transition.                                *)
(*                                                                            *)
(* Invalid at time-step 0 because there is no previous row in this case.      *)
(* -------------------------------------------------------------------------- *)
Definition get_num_errors_after_step_def:
  get_num_errors_after_step m bs t previous_row r = (EL r.origin previous_row).num_errors + N (hamming_distance (m.transition_fn r).output (relevant_input m bs t))
End

(* -------------------------------------------------------------------------- *)
(* Returns the best choice of origin you should take if you want to arrive at *)
(* the state s at timestep t, given the number of errors at each state in the *)
(* previous row.                                                              *)
(* -------------------------------------------------------------------------- *)
Definition best_origin_def:
  best_origin m bs previous_row t s = inargmin (get_num_errors_after_step m bs t previous_row) (transition_inverse m s)
End

(* -------------------------------------------------------------------------- *)
(* Returns a specific node in the trellis. Takes the previous row as input,   *)
(* so that we can reuse those precomputed values rather than recomputing them,*)
(* which would end up taking exponential time.                                *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire input bitstring                                             *)
(* s: the state associated with this node in the trellis                      *)
(* t: the time step associated with this node in the trellis                  *)
(* previous_row: the row of data associated with the previous time step.      *)
(*                                                                            *)
(* Outputs a tuple containing the number of errors at this point as well as   *)
(* the previous state on the optimal path towards this point                  *)
(*                                                                            *)
(* Only valid when a previous row exists, i.e. when we aren't in the zeroth   *)
(* time-step.                                                                 *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_trellis_node_def:
  viterbi_trellis_node m bs s t previous_row =
  let
    local_best_origin = best_origin m bs previous_row t s;
    local_num_errors = get_num_errors_after_step m bs t previous_row local_best_origin;
    local_prev_state = (if local_num_errors = INFINITY then NONE else SOME local_best_origin.origin);
  in
    <| num_errors := local_num_errors;
       prev_state := local_prev_state; |>
End

(* -------------------------------------------------------------------------- *)
(* Returns a row of the trellis, used by the Viterbi algorithm to decode a    *)
(* convolutional code. The previous row is completely evaluated before        *)
(* starting the evaluation of this row, and so we can reuse it multiple times *)
(* in the evaluation of this row, in a dynamic programming way. This ensures  *)
(* that the trellis is evaluated in linear time rather than exponential time. *)(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire bitstring we want to decode                                 *)
(* t: the timestep to calculate the row for,                                  *)
(*                                                                            *)
(* Output: the corresponding row of the trellis, in list form, where the nth  *)
(* element of the list corresponds to the nth state, and is a tuple of the    *)
(* the form <| num_errors; prev_state |>                                      *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_trellis_row_def:
  viterbi_trellis_row (m : state_machine) bs 0
  = <| num_errors := N0; prev_state := NONE |> :: REPLICATE (m.num_states - 1) <| num_errors := INFINITY; prev_state := NONE |>
  ∧
  viterbi_trellis_row m bs (SUC t)
  = let
      previous_row = viterbi_trellis_row m bs t
    in
      GENLIST (λn. viterbi_trellis_node m bs n (SUC t) previous_row) m.num_states
End

(* -------------------------------------------------------------------------- *)
(* Calculate a node in the trellis for the fast version when the previous row *)
(* is not available (by calculating all prior rows of the trellis)            *)
(*                                                                            *)
(* Defined in such a way as to be valid even at time-step 0, when there isn't *)
(* a previous row present.                                                    *)
(*                                                                            *)
(* Note: avoid writing theorems for this definition, as it may cause          *)
(* duplication with theorems for viterbi_trellis_row and viterbi_trellis_node *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_trellis_node_no_prev_data_def[simp]:
  viterbi_trellis_node_no_prev_data m bs s t = EL s (viterbi_trellis_row m bs t)
End

(* -------------------------------------------------------------------------- *)
(* Version of get_num_errors_after_step which works even if you do not provide*)
(* it with the previous row of errors                                         *)
(*                                                                            *)
(* TODO: should this be removed, because it's not significant enough to be    *)
(* worth adding a definition, which may cause duplication in necessary        *)
(* theorems between this function and get_num_errors_after_step?              *)
(* -------------------------------------------------------------------------- *)
Definition get_num_errors_after_step_no_prev_data_def:
  get_num_errors_after_step_no_prev_data m bs 0 r = (if (vd_step_tran m r = 0) then N0 else INFINITY) ∧
  get_num_errors_after_step_no_prev_data m bs (SUC t) r = get_num_errors_after_step m bs (SUC t) (viterbi_trellis_row m bs t) r
End

(* -------------------------------------------------------------------------- *)
(* A slower but mathematically simpler implementation of the function for     *)
(* working out the best origin in the viterbi trellis.                        *)
(*                                                                            *)
(* We remove the previous_row argument, which effectively holds state. This   *)
(* makes the definitions more purely functional.                              *)
(*                                                                            *)
(* Combined definition of several functions because these functions are       *)
(* recursively dependent on each other.                                       *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_trellis_slow:
  get_num_errors_after_step_slow m bs 0 r = (if (vd_step_tran m r = 0) then N0 else INFINITY) ∧
  get_num_errors_after_step_slow m bs (SUC t) r = 
  (viterbi_trellis_node_slow m bs r.origin t).num_errors + N (hamming_distance (m.transition_fn r).output (relevant_input m bs (SUC t))) ∧
  (best_origin_slow m bs t s = inargmin (get_num_errors_after_step_slow m bs t) (transition_inverse m s)) ∧
  viterbi_trellis_node_slow m bs s t = 
  let
    local_best_origin = best_origin_slow m bs t s;
    local_num_errors = get_num_errors_after_step_slow m bs t local_best_origin;
    local_prev_state = (if (t = 0 ∨ local_num_errors = INFINITY) then NONE else SOME local_best_origin.origin);
  in
    <| num_errors := local_num_errors;
       prev_state := local_prev_state; |>    
Termination
  (* Use a standard measure-based method for proving termination. (see the
     HOL System Description on proving termination). We have a circular
     recursion of 3 functions, where on every loop, t decreases by 1.
.
     best_origin_slow (SUC t) -> get_better_origin_slow (SUC t) ->
     get_num_errors_after_step_slow (SUC t) -> best_origin_slow t ->
     get_better_origin_slow t -> ...
.
     Thus, in order to ensure that our measure decreases on every function
     call, we should multiply t by 3, and add a number between 0 and 2 such
     that functions earlier in this sequence have a larger measure. *)
  (*
    Since there are 3 mutually recursive functions being defined here,
    we are using the disjoint sum type
  *)
  WF_REL_TAC ‘measure (λx.
                         (* test if we're currently in the first function
                            call, and thus being provided with the arguments
                            to the first fucntion *)
                         if ISL x 
                         then
                           (* get the argument t given the arguments to the
                              first function *)
                           3 * (FST $ SND $ SND $ OUTL x)
                         else
                           let x' = OUTR x in
                             if ISL x'
                             then
                               3 * (FST $ SND $ SND $ OUTL x') + 1
                             else
                               3 * (SND $ SND $ SND $ OUTR x') + 2
                      )’
  >> gvs[]
End

(* -------------------------------------------------------------------------- *)
(* Creating theorems in order to adhere to standard naming conventions for    *)
(* function definitions, as this was not possible because multiple functions  *)
(* were defined in the same definition                                        *)
(* -------------------------------------------------------------------------- *)
Theorem get_num_errors_after_step_slow_def = LIST_CONJ [cj 1 viterbi_trellis_slow, cj 2 viterbi_trellis_slow]
Theorem best_origin_slow_def = cj 3 viterbi_trellis_slow
Theorem viterbi_trellis_node_slow_def = cj 4 viterbi_trellis_slow

(* -------------------------------------------------------------------------- *)
(* Performs one step back through the trellis.                                *)
(*                                                                            *)
(* m: the state machine which generates the trellis                           *)
(* bs: the bitstring being decoded                                            *)
(* s: the state to step back from                                             *)
(* t: the time-step to step back from                                         *)
(*                                                                            *)
(* Only valid for t > 0, since we can't step back at t = 0.                   *)
(* -------------------------------------------------------------------------- *)
(* Note: this requires generating the entire trellis up to this point, which  *)
(* is slow. Repeatedly calling this function should therefore in theory be    *)
(* less efficient than generating the trellis once and then stepping back     *)(* through the thing.                                                         *)
(* -------------------------------------------------------------------------- *)
Definition vd_step_back_def:
  vd_step_back m bs s t =
  let
    trellis_row = viterbi_trellis_row m bs t;
    trellis_node = EL s trellis_row
  in
    THE trellis_node.prev_state
End

(* -------------------------------------------------------------------------- *)
(* Returns the optimal path leading to state s at timestep t, with respect to *)
(* the bitstring bs that we are trying to approximate.                        *)
(*                                                                            *)
(* Returns the path as a list of all states encountered along the path,       *)
(* including the very first and last states, with the first element of this   *)
(* list being the first state encountered in the path, and the last element   *)
(* of this list being the last state encountered in the path.                 *)
(*                                                                            *)
(* vd stands for Viterbi Decode                                               *)
(* -------------------------------------------------------------------------- *)
(* TODO: Repeatedly calling vd_step_back is slow, because it regenerates the  *)
(* trellis at each step.                                                      *)
(* -------------------------------------------------------------------------- *)
Definition vd_find_optimal_path_def:
  vd_find_optimal_path m bs s 0 = [s] ∧
  vd_find_optimal_path m bs s (SUC t) =
  SNOC s (vd_find_optimal_path m bs (vd_step_back m bs s (SUC t)) t)
End

(* -------------------------------------------------------------------------- *)
(* Added for legacy reasons. Do not use in new code. Phase out where possible.*)(* -------------------------------------------------------------------------- *)
Definition vd_find_optimal_reversed_path_def:
  vd_find_optimal_reversed_path m bs s t = REVERSE (vd_find_optimal_path m bs s t)
End

Definition get_num_errors_from_state_def:
  get_num_errors_from_state m rs bs s = hamming_distance rs (vd_encode_from_state m bs s)
End

(* -------------------------------------------------------------------------- *)
(* The number of errors present if we encoded the input bs with the state     *)(* machine m and compared it to the expected output rs.                       *)
(* -------------------------------------------------------------------------- *)
Definition get_num_errors_def:
  get_num_errors m rs bs = get_num_errors_from_state m rs bs 0
End

(* -------------------------------------------------------------------------- *)
(* TODO: use argmin instead of this                                           *)
(* -------------------------------------------------------------------------- *)
Definition get_better_final_state_def:
  get_better_final_state last_row s1 s2 = if (EL s1 last_row).num_errors < (EL s2 last_row).num_errors then s1 else s2
End

(* -------------------------------------------------------------------------- *)
(* vd_find_optimal_path, but converted to code form                           *)
(* -------------------------------------------------------------------------- *)
Definition vd_find_optimal_code_def:
  vd_find_optimal_code m bs s t = path_to_code m (vd_find_optimal_path m bs s t)
End

(* -------------------------------------------------------------------------- *)
(* Input: bitstring and state machine                                         *)
(* Output: Most likely original bitstring                                     *)
(* -------------------------------------------------------------------------- *)
(* TODO: This recalculates the whole trellis again, which is already          *)
(* recalculated several times when producing the path back through the        *)
(* trellis                                                                    *)
(* -------------------------------------------------------------------------- *)
Definition vd_decode_def:
  vd_decode m bs =
  let
    max_timestep = (LENGTH bs) DIV m.output_length;
    last_row = viterbi_trellis_row m bs max_timestep;
    best_state = FOLDR (get_better_final_state last_row) 0 (COUNT_LIST m.num_states)
  in
    vd_find_optimal_code m bs best_state max_timestep
End

Theorem best_origin_is_valid[simp]:
  ∀m bs prev_row t s.
  wfmachine m ∧
  s < m.num_states ⇒
  (best_origin m bs prev_row t s).origin < m.num_states
Proof
  rpt strip_tac
  >> gvs[best_origin_def]
  >> irule transition_inverse_mem_is_valid
  >> qexists ‘s’
  >> irule inargmin_mem
  >> gvs[]
QED

Theorem viterbi_trellis_node_slow_num_errors:
  ∀m bs t r.
  (viterbi_trellis_node_slow m bs r.origin t).num_errors = get_num_errors_after_step_slow m bs (SUC t) r - N (hamming_distance (m.transition_fn r).output (relevant_input m bs (SUC t)))
Proof
  rpt strip_tac
  >> gvs[get_num_errors_after_step_slow_def]
QED

Theorem viterbi_trellis_row_el:
  ∀m bs s t. 
  s < m.num_states ⇒
  EL s (viterbi_trellis_row m bs (SUC t)) = viterbi_trellis_node m bs s (SUC t) (viterbi_trellis_row m bs t)
Proof
  gvs[viterbi_trellis_row_def]
QED

(* -------------------------------------------------------------------------- *)
(* Prove that each previous state in the trellis is valid.                    *)
(* -------------------------------------------------------------------------- *)
Theorem viterbi_trellis_row_prev_state_valid[simp]:
  ∀m bs t s.
  wfmachine m ∧
  s < m.num_states ∧
  (EL s (viterbi_trellis_row m bs t)).prev_state ≠ NONE ⇒
  THE (EL s (viterbi_trellis_row m bs t)).prev_state < m.num_states
Proof
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac ‘THE n’
  >> Cases_on ‘n’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[viterbi_trellis_row_def]
  >- (Cases_on ‘s’ >> gvs[]
      >> gvs[EL_REPLICATE])
  >> gvs[viterbi_trellis_node_def]
QED

Theorem get_num_errors_after_step_slow_best_origin_slow:
  ∀m bs t s r.
  r.origin < m.num_states ∧
  vd_step_tran m r = s ⇒
  get_num_errors_after_step_slow m bs t (best_origin_slow m bs t s) ≤ get_num_errors_after_step_slow m bs t r
Proof
  rpt gen_tac
  >> strip_tac
  >> gs[best_origin_slow_def]
  >> qmatch_goalsub_abbrev_tac ‘get_num_errors_after_step_slow _ _ _ (inargmin f _) ≤ _’
  >> qspecl_then [‘f’, ‘r’, ‘transition_inverse m s’] assume_tac inargmin_inle
  >> imp_prove
  >- (gvs[]
      >> irule mem_transition_inverse_vd_step_tran
      >> gvs[])
QED

Theorem best_origin_slow_transition_inverse:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  MEM (best_origin_slow m bs t s) (transition_inverse m s)
Proof
  rpt strip_tac
  >> gvs[best_origin_slow_def]
  >> gvs[inargmin_mem]
QED

Theorem best_origin_slow_is_valid[simp]:
  ∀m bs t s.
  wfmachine m ∧
  s < m.num_states ⇒
  (best_origin_slow m bs t s).origin < m.num_states
Proof
  rpt strip_tac
  >> qspecl_then [‘m’, ‘bs’, ‘s’, ‘t’] assume_tac best_origin_slow_transition_inverse
  >> metis_tac[transition_inverse_mem_is_valid]
QED

Theorem best_origin_slow_get_num_errors_after_step_slow:
  ∀m bs t r s.
  wfmachine m ∧
  s < m.num_states ∧
  MEM r (transition_inverse m s) ⇒
  get_num_errors_after_step_slow m bs t (best_origin_slow m bs t s) ≤ get_num_errors_after_step_slow m bs t r
Proof
  rpt strip_tac
  >> gvs[best_origin_slow_def]
QED

Theorem vd_step_tran_best_origin_slow[simp]:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  vd_step_tran m (best_origin_slow m bs t s) = s
Proof
  rpt strip_tac
  >> simp[best_origin_slow_def]
QED

Theorem vd_step_best_origin_slow:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  vd_step m (best_origin_slow m bs t s).input (best_origin_slow m bs t s).origin = s
Proof
  rpt strip_tac
  >> metis_tac[vd_step_tran_best_origin_slow, vd_step_tran_def]
QED

Theorem is_reachable_viterbi_trellis_node_slow_num_errors:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  (is_reachable m s t ⇔ (viterbi_trellis_node_slow m bs s t).num_errors ≠ INFINITY)
Proof
  Induct_on ‘t’ >> rpt strip_tac >> gvs[]
  (* Prove the base case *)
  >- (gvs[viterbi_trellis_node_slow_def, get_num_errors_after_step_slow_def]
      >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[]
     )
  (* Start the inductive step. Reduce the suc using the definition of
     get_num_errors_after_step_slow, so that we are at the previous stage and
     can therefore use the inductive hypothesis. *)
  >> simp[viterbi_trellis_node_slow_def]
  >> simp[get_num_errors_after_step_slow_def]
  (* Let r denote the best origin leading to s *)
  >> qmatch_goalsub_abbrev_tac ‘viterbi_trellis_node_slow m bs r.origin t’
  >> simp[is_reachable_suc_vd_step_tran]
  (* The second goal turns out to be easier, so we do it first *)
  >> REVERSE EQ_TAC
  >- (rpt strip_tac
      >> qexists ‘r’
      >> gvs[]
      >> REVERSE conj_tac
      >- (unabbrev_all_tac
          >> gvs[vd_step_tran_best_origin_slow])
      >> last_x_assum (fn th => (irule (iffRL th)))
      >> gvs[]
      >> conj_tac
      >- (qexists ‘bs’ >> gvs[])
      >> unabbrev_all_tac
      >> gvs[best_origin_slow_is_valid])
  >> strip_tac
  >> last_x_assum (qspecl_then [‘m’, ‘bs’, ‘r'.origin’] assume_tac)
  >> gs[]
  >> imp_prove
  >- (unabbrev_all_tac
      >> metis_tac[is_reachable_is_valid])
  >> gs[]
  (* r' and r both lead to s, *)
  >> gs[viterbi_trellis_node_slow_num_errors]
  >> unabbrev_all_tac
  >> qspecl_then [‘m’, ‘bs’, ‘SUC t’, ‘s’, ‘r'’] assume_tac get_num_errors_after_step_slow_best_origin_slow
  >> gs[]
  >> strip_tac
  >> gvs[]
QED

Theorem is_reachable_get_num_errors_after_step_slow:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  (is_reachable m s t ⇔ get_num_errors_after_step_slow m bs t (best_origin_slow m bs t s) ≠ INFINITY)
Proof
  rpt strip_tac
  >> qspecl_then [‘m’, ‘bs’, ‘s’, ‘t’] assume_tac is_reachable_viterbi_trellis_node_slow_num_errors
  >> gvs[viterbi_trellis_node_slow_def]        
QED

Theorem vd_find_optimal_path_nonempty[simp]:
  ∀m bs s t.
  vd_find_optimal_path m bs s t ≠ []
Proof
  rpt strip_tac
  >> Cases_on ‘t’ >> gvs[vd_find_optimal_path_def]
QED

Theorem vd_find_optimal_path_time_zero[simp]:
  ∀m bs s t. vd_find_optimal_path m bs s 0 = [s]
Proof
  rpt strip_tac
  >> EVAL_TAC
QED

Theorem vd_find_optimal_path_length[simp]:
  ∀m bs s t.
  LENGTH (vd_find_optimal_path m bs s t) = t + 1
Proof
  gen_tac
  (* Induct over t *)
  >> Induct_on ‘t’
  >- (rpt strip_tac >> EVAL_TAC)
  (* Expand out definitions *)
  >> gvs[vd_find_optimal_path_def, vd_step_back_def]
QED

Theorem vd_find_optimal_path_last[simp]:
  ∀m bs s t.
  LAST (vd_find_optimal_path m bs s t) = s
Proof
  Induct_on ‘t’ >> rpt strip_tac >> gvs[]
  >> gvs[vd_find_optimal_path_def]
  >> gvs[vd_find_optimal_reversed_path_def]
QED
   
Theorem vd_find_optimal_path_suc:
  ∀m bs s t.
  vd_find_optimal_path m bs s (SUC t) = SNOC s (vd_find_optimal_path m bs (vd_step_back m bs s (SUC t)) t)
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[vd_find_optimal_path_def]
  >> PURE_REWRITE_TAC[GSYM (cj 2 REVERSE_SNOC_DEF)]
  >> AP_TERM_TAC
  >> gvs[vd_find_optimal_reversed_path_def]
QED

Theorem vd_find_optimal_reversed_path_length[simp]:
  ∀m bs s t.
  LENGTH (vd_find_optimal_reversed_path m bs s t) = t + 1
Proof
  gvs[vd_find_optimal_reversed_path_def]
QED

(* -------------------------------------------------------------------------- *)
(* This is already contained in the definition of                             *)
(* vd_find_optimal_reversed_path, but it is good to automatically use it      *)
(* -------------------------------------------------------------------------- *)
Theorem vd_find_optimal_reversed_path_time_zero[simp]:
  ∀m bs s.
  vd_find_optimal_reversed_path m bs s 0 = [s]
Proof
  rpt strip_tac >> EVAL_TAC
QED

Theorem get_num_errors_from_state_append:
  ∀m rs bs bs' s.
  wfmachine m ∧
  s < m.num_states ∧
  LENGTH rs = (LENGTH bs + LENGTH bs') * m.output_length ⇒
  get_num_errors_from_state m rs (bs ⧺ bs') s = get_num_errors_from_state m (TAKE (LENGTH bs * m.output_length) rs) bs s + get_num_errors_from_state m (DROP (LENGTH bs * m.output_length) rs) bs' (vd_encode_state_from_state m bs s) 
Proof
  rpt strip_tac
  >> gvs[get_num_errors_from_state_def]
  >> gvs[vd_encode_from_state_append]
  >> gvs[hamming_distance_append_right]
QED

Theorem get_num_errors_append:
  ∀m rs bs bs'.
  wfmachine m ∧
  LENGTH rs = (LENGTH bs + LENGTH bs') * m.output_length ⇒
  get_num_errors m rs (bs ⧺ bs') = get_num_errors m (TAKE (LENGTH bs * m.output_length) rs) bs + get_num_errors_from_state m (DROP (LENGTH bs * m.output_length) rs) bs' (vd_encode_state m bs)
Proof
  rpt strip_tac
  >> gvs[get_num_errors_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_from_state_append]
  >> gvs[]
  >> gvs[vd_encode_state_def]
QED

Theorem vd_find_optimal_code_time_zero[simp]:
  ∀m bs s. vd_find_optimal_code m bs s 0 = []
Proof
  rpt strip_tac
  >> gvs[vd_find_optimal_code_def]
QED

Theorem vd_find_optimal_code_length[simp]:
  ∀m bs s t.
  LENGTH (vd_find_optimal_code m bs s t) = t
Proof
  rpt strip_tac
  >> gvs[vd_find_optimal_code_def]
QED

(* -------------------------------------------------------------------------- *)
(* Theorem statement not designed by hand: identified after seeing what       *)
(* happens when we expand out vd_find_optimal_code in order to remove the     *)
(* SUC, intended for use in applying the inductive step.                      *)
(* -------------------------------------------------------------------------- *)
Theorem vd_find_optimal_code_suc:
  ∀m bs s t.
  vd_find_optimal_code m bs s (SUC t) = vd_find_optimal_code m bs (vd_step_back m bs s (SUC t)) t ⧺ [states_to_transition_input m (vd_step_back m bs s (SUC t))s] 
Proof
  gvs[vd_find_optimal_code_def]
  >> gvs[vd_find_optimal_path_def]
  >> gvs[vd_find_optimal_reversed_path_def]
  >> gvs[GSYM vd_find_optimal_reversed_path_def]
  >> gvs[GSYM vd_find_optimal_path_def]
  >> gvs[path_to_code_append]
  >> gvs[GSYM vd_find_optimal_code_def]
QED

(* -------------------------------------------------------------------------- *)
(* Alternate definition that could be used for vd_find_optimal_code           *)
(* -------------------------------------------------------------------------- *)
Theorem vd_find_optimal_code_suc':
  ∀m bs s t.
  vd_find_optimal_code m bs s (SUC t) =
  let
    x = vd_step_back m bs s (SUC t)
  in
    vd_find_optimal_code m bs x t ⧺ [states_to_transition_input m x s]
Proof
  gvs[vd_find_optimal_code_def]
  >> gvs[vd_find_optimal_path_def]
  >> gvs[vd_find_optimal_reversed_path_def]
  >> gvs[GSYM vd_find_optimal_reversed_path_def]
  >> gvs[GSYM vd_find_optimal_path_def]
  >> gvs[path_to_code_append]
  >> gvs[GSYM vd_find_optimal_code_def]
QED

(* -------------------------------------------------------------------------- *)
(* Alternate method to prove a theorem without having to re-write out the     *)
(* entire statement of the theorem.                                           *)
(* -------------------------------------------------------------------------- *)
Theorem vd_find_optimal_code_suc'' =
        “vd_find_optimal_code m bs s (SUC t)”
          |> SCONV  [vd_find_optimal_code_def, vd_find_optimal_path_def,
                     vd_find_optimal_reversed_path_def]
          |> SRULE [GSYM vd_find_optimal_reversed_path_def,
                    GSYM vd_find_optimal_path_def,
                    path_to_code_append,
                    GSYM vd_find_optimal_code_def]
          |> GEN_ALL

Theorem vd_decode_empty[simp]:
  ∀m. vd_decode m [] = []
Proof
  rpt strip_tac
  >> gvs[vd_decode_def, vd_find_optimal_code_def]
QED

Theorem vd_decode_length[simp]:
  ∀m bs.
  wfmachine m ∧
  divides (LENGTH bs) m.output_length ∧
  m.output_length ≠ 0 ⇒
  LENGTH (vd_decode m bs) = LENGTH bs DIV m.output_length
Proof
  (* Prepare for induction with a stride of the output length.
     Need to expand out the definition of divides, and then put
     all the variables into foralls. *)
  rpt strip_tac
  >> gvs[divides_def]
  >> NTAC 3 (pop_assum mp_tac)
  >> SPEC_ALL_TAC
  (* Start the induction *)
  >> Induct_on ‘q’ >> rpt strip_tac
  >- gvs[] (* Deal with invalid case with output length of 0 *)
  (* expand definition *)
  >> gvs[vd_decode_def]
QED

(*Theorem viterbi_trellis_node_slow_viterbi_trellis_node_no_prev_data:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  viterbi_trellis_node_slow m bs s t = viterbi_trellis_node_no_prev_data m bs s t
Proof
  rpt strip_tac
  >> Cases_on ‘t’ >> gvs[viterbi_trellis_node_slow_def, viterbi_trellis_node_no_prev_data_def, viterbi_trellis_node_def]
  >- (gvs[get_num_errors_after_step_slow_def]
      >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[]
      >- gvs[viterbi_trellis_row_def]
      >> Cases_on ‘s’
      >- gvs[]
      >> gvs[]
      >> gvs[viterbi_trellis_row_def]
      >> gvs[EL_REPLICATE])
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_after_step_slow_get_num_errors_after_step]
  >> gvs[]
  >> gvs[best_origin_slow_is_valid]
  >> gvs[best_origin_slow_best_origin]
  >> gvs[viterbi_trellis_row_def]
  >> gvs[viterbi_trellis_node_def]
QED*)

(*Theorem get_num_errors_after_step_slow_get_num_errors_after_step_no_prev_data:
  ∀m bs t r.
  wfmachine m ∧
  r.origin < m.num_states ⇒
  get_num_errors_after_step_slow m bs (SUC t) r = get_num_errors_after_step_no_prev_data m bs (SUC t) r
Proof
  gen_tac
  >> Induct_on ‘t’
  >- (gvs[get_num_errors_after_step_no_prev_data_def]
      >> rpt strip_tac
      (* expand stuff out *)
      >> gvs[]
      >> gvs[get_num_errors_after_step_slow_def, get_num_errors_after_step_def]
      >> gvs[viterbi_trellis_row_def]
      (* When r.origin is nonzero, the RHS simplifies to infinity. Deal
         with this special case. *)
      >> REVERSE (Cases_on ‘r.origin’)
      >- (gvs[EL_REPLICATE]
          >> PURE_REWRITE_TAC [ONE]
          >> gvs[get_num_errors_after_step_slow_def]
          >> gvs[EL_REPLICATE])
      >> gvs[]
      >> PURE_REWRITE_TAC[ONE]
      >> gvs[get_num_errors_after_step_slow_def]
     )
  (* Inductive step *)
  >> rpt strip_tac
  (* Expand out the slow version so that all slow version functions are
     calculated at a lower time-step, and all slow version funcctions are
     get_num_errors_after_step_slow, so that we can use our inductive
     hypothesis to translate to a statement entirely in terms of fast version
     functions. *)
  >> PURE_ONCE_REWRITE_TAC[get_num_errors_after_step_slow_def]
  >> gvs[best_origin_slow_def]
  >> gvs[get_better_origin_slow_def]
  (* translate the inner function so that it is written in terms of the fast
        version. *)
  >> qmatch_goalsub_abbrev_tac ‘FOLDR f _ _’
  (* ------------------------------------------------------------------------ *)
  (* Are there nicer ways to deal with functions that are equal to each other *)
  (* only on a specific domain?                                               *)
  (* ------------------------------------------------------------------------ *)
  >> sg ‘f = (λa' a. if (a.origin < m.num_states ∧ a'.origin < m.num_states) then (if get_num_errors_after_step_no_prev_data m bs (SUC t) a' < get_num_errors_after_step_no_prev_data m bs (SUC t) a then a' else a) else f a' a)’
  >- (unabbrev_all_tac
      >> irule EQ_EXT >> rpt strip_tac >> gvs[]
      >> irule EQ_EXT >> rpt strip_tac >> gvs[]
      >> qmatch_goalsub_abbrev_tac ‘_ = if b then _ else _’
      >> Cases_on ‘b’ >> gvs[]
      >> last_assum $ qspecl_then [‘bs’, ‘x’] assume_tac
      >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
     )
  (* Replace the other slow function with a fast function, using the inductive
     hypothesis. *)
  (*>> last_assum $ (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
      >> conj_tac
      >- (qmatch_goalsub_abbrev_tac ‘FOLDR f tr trs’
          >> sg ‘MEM (FOLDR f tr trs) (tr::trs)’
          >- (irule FOLDR_BISWITCH
              >> rpt strip_tac
              >> unabbrev_all_tac
              >> gvs[]
              >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
              >> Cases_on ‘b’ >> gvs[])
          >> sg ‘MEM (FOLDR f tr trs) (transition_inverse m r.origin)’
          >- (‘tr::trs = transition_inverse m r.origin’ suffices_by (disch_tac >> metis_tac[])
              >> unabbrev_all_tac
              >> simp[transition_inverse_cons])
          >> metis_tac[transition_inverse_mem_is_valid])*)
  >> irule EQ_SYM
  >> gvs[get_num_errors_after_step_no_prev_data_def]
  >> simp[Once get_num_errors_after_step_def]
  >> AP_THM_TAC
  >> AP_TERM_TAC
  >> gvs[viterbi_trellis_row_def]
  >> gvs[viterbi_trellis_node_def]
  >> AP_TERM_TAC
  >> gvs[best_origin_def]
  >> unabbrev_all_tac
  >> gvs[]
  >> irule FOLDR_DOMAIN_MEM
  >> rpt gen_tac
  >> MEM_DONOTEXPAND_TAC
  >> gvs[]
  >> REVERSE conj_tac
  >- (gvs[get_better_origin_def]
      >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[]
     )
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> sg ‘b’
  >- (unabbrev_all_tac
      >> MEM_DOEXPAND_TAC
      >> metis_tac[transition_inverse_mem_is_valid]
     )
  >> gvs[]
  >> gvs[get_better_origin_def]
QED*)

(*Theorem get_num_errors_after_step_slow_get_num_errors_after_step:
  ∀m bs t r.
  wfmachine m ∧
  r.origin < m.num_states ⇒
  get_num_errors_after_step_slow m bs (SUC t) r = get_num_errors_after_step m bs (SUC t) (viterbi_trellis_row m bs t) r
Proof
  gvs[get_num_errors_after_step_slow_get_num_errors_after_step_no_prev_data, get_num_errors_after_step_no_prev_data_def]
QED*)

(*Theorem get_better_origin_slow_get_better_origin:
  ∀m bs t r1 r2.
  wfmachine m ∧
  r1.origin < m.num_states ∧
  r2.origin < m.num_states ⇒
  get_better_origin_slow m bs (SUC t) r1 r2 = get_better_origin m bs (SUC t) (viterbi_trellis_row m bs t) r1 r2
Proof
  rpt strip_tac
  >> gvs[get_better_origin_slow_def, get_better_origin_def]
  >> gvs[get_num_errors_after_step_slow_get_num_errors_after_step]
QED*)

(*Theorem best_origin_slow_best_origin:
  ∀m bs t s.
  wfmachine m ∧
  s < m.num_states ⇒
  best_origin_slow m bs (SUC t) s = best_origin m bs (SUC t) (viterbi_trellis_row m bs t) s  
Proof
  rpt strip_tac
  >> gvs[best_origin_slow_def, best_origin_def]
  >> irule FOLDR_DOMAIN
  >> MEM_DONOTEXPAND_TAC
  >> qexists ‘all_transitions_set m’
  >> gvs[]
  >> rpt strip_tac
  >- (DEP_PURE_ONCE_REWRITE_TAC[get_better_origin_slow_get_better_origin]
      >> gvs[all_transitions_set_def]
     )
  >- (gvs[get_better_origin_slow_def]
      >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[])
  >> MEM_DOEXPAND_TAC
  >> metis_tac[transition_inverse_mem_all_transitions_set]
QED*)

(*Theorem vd_step_back_is_valid[simp]:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ∧
  0 < t ∧
  is_reachable m s t ⇒
  vd_step_back m bs s t < m.num_states
Proof
  rpt strip_tac
  >> gvs[vd_step_back_def]
  >> Cases_on ‘t’ >> gvs[]
  >> gvs[viterbi_trellis_row_el]
  >> qmatch_goalsub_abbrev_tac ‘THE node’
  >> REVERSE (Cases_on ‘node’) >> gvs[]
  >- gvs[viterbi_trellis_node_def]
  >> gvs[viterbi_trellis_node_def]
QED*)

(* -------------------------------------------------------------------------- *)
(* Efficiency tests                                                           *)
(* -------------------------------------------------------------------------- *)

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
    MAP (λm. (if 0 < m then EL (m - 1) prior_grid_row else 0) + EL m prior_grid_row + (if m < 9 then EL (m + 1) prior_grid_row else 0)) (COUNT_LIST 10)
End

(* -------------------------------------------------------------------------- *)
(* Testing whether or not example_recursive_grid_row takes an exponential     *)
(* amount of time to compute. It could theoretically take an exponential      *)
(* amount of time if the previous row was substituted in multiple places, and *)
(* expanded out fully multiple times. Each subsequent row would double the    *)
(* amount of time taken because it has to do the computation from the         *)
(* previous row twice.                                                        *)
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
(*Theorem example_recursive_grid_row_time_test:
  example_recursive_grid_row 100 = ARB
Proof
  EVAL_TAC
QED*)

(* -------------------------------------------------------------------------- *)
(* A similar test as above, with a slightly different definition.             *)
(* -------------------------------------------------------------------------- *)
Definition example_recursive_grid_row2_def:
  example_recursive_grid_row2 0 = REPLICATE 10 1 ∧
  example_recursive_grid_row2 (SUC n) =
  MAP (λm. (if 0 < m then EL (m - 1) (example_recursive_grid_row2 n) else 0) + EL m (example_recursive_grid_row2 n) + (if m < 9 then EL (m + 1) (example_recursive_grid_row2 n) else 0)) (COUNT_LIST 10)
End

Theorem example_recursive_grid_row_example_recursive_grid_row2:
  ∀n. example_recursive_grid_row n = example_recursive_grid_row2 n
Proof
  Induct_on ‘n’ >> gvs[example_recursive_grid_row_def, example_recursive_grid_row2_def]
QED

(* -------------------------------------------------------------------------- *)
(* This implementation is much slower, as expected.                           *)
(*                                                                            *)
(* 2: 0.201                                                                   *)
(* 3: 5.443                                                                   *)
(* 4: 145.7                                                                   *)
(* -------------------------------------------------------------------------- *)
(*Theorem example_recursive_grid_row_time_test:
  example_recursive_grid_row2 4 = ARB
Proof
  EVAL_TAC
QED*)

(* -------------------------------------------------------------------------- *)
(* Prior to making the relevant input calculated at the point at which it is  *)
(* actually needed, resulting in the relevant input being calculated multiple *)
(* times:                                                                     *)
(*                                                                            *)
(* 200: 3.700                                                                 *)(*                                                                            *)
(* After the aforementioned relevant input change:                            *)
(*                                                                            *)(* 200: 9.070                                                                 *)
(* -------------------------------------------------------------------------- *)
(* Theorem viterbi_trellis_row_efficiency_test:
  let
    n = 200;
    n' = n * example_state_machine.output_length
  in
    viterbi_trellis_row example_state_machine (REPLICATE n' T) n = ARB
Proof
  EVAL_TAC
QED*)

(* -------------------------------------------------------------------------- *)
(* Unit tests                                                                 *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Unit test to ensure that the values returned by the trellis data function  *)
(* are those you would expect.                                                *)
(*                                                                            *)
(* Hand-calculated trellis (num errors):                                      *)
(*                                                                            *)
(* 0  1  2  3  3  3  4                                                        *)
(* -  1  2  2  3  3  4                                                        *)
(* -  -  2  2  2  5  4                                                        *)
(* -  -  2  3  4  3  3                                                        *)
(*                                                                            *)
(* Hand-calculated previous states:                                           *)
(*                                                                            *)
(* -  0  0  2  2  02 0                                                        *)
(* -  0  0  0  02 2  0                                                        *)
(* -  -  1  1  1  13 13                                                       *)
(* -  -  1  3  13 1  3                                                        *)
(* -------------------------------------------------------------------------- *)
Theorem viterbi_trellis_row_test:
  let
    node s t = (EL s (viterbi_trellis_row example_state_machine test_path t));
  in
    (* First row first state *)
    (node 0 0).num_errors = N 0 ∧
    (node 0 0).prev_state = NONE ∧
    (* First row other state *)
    (node 2 0).num_errors = INFINITY ∧
    (node 2 0).prev_state = NONE ∧
    (* Row in the middle *)
    (node 0 4).num_errors = N 3 ∧
    (node 1 4).num_errors = N 3 ∧
    (node 2 4).num_errors = N 2 ∧
    (node 3 4).num_errors = N 4 ∧
    (node 0 4).prev_state = SOME 2 ∧
    ((node 1 4).prev_state = SOME 0 ∨ (node 1 4).prev_state = SOME 2) ∧
    (node 2 4).prev_state = SOME 1 ∧
    ((node 3 4).prev_state = SOME 1 ∨ (node 3 4).prev_state = SOME 3) ∧
    (* Node which isn't reachable, but isn't in the first row *)
    (node 2 1).num_errors = INFINITY ∧
    (node 2 1).prev_state = NONE
Proof
  EVAL_TAC
QED

(*Theorem viterbi_trellis_row_eval:
  let
    t = 5;
    test_row = viterbi_trellis_row example_state_machine test_path t
  in
    test_row = ARB
Proof
  EVAL_TAC
QED*)

Theorem get_num_errors_after_step_slow_get_num_errors_after_step_no_prev_data_test:
  ∀t r.
              t < 3 ∧
              r.origin < 4 ⇒
              get_num_errors_after_step_slow example_state_machine test_path (SUC t) r = get_num_errors_after_step_no_prev_data example_state_machine test_path (SUC t) r
Proof
  rpt strip_tac
  >> sg ‘(t = 0 ∨ t = 1 ∨ t = 2) ∧ (r.origin = 0 ∨ r.origin = 1 ∨ r.origin = 2 ∨ r.origin = 3)’ >> gvs[]
  (* This sequence of tactics will simultaneously prove all 12 proof
     obligations *)
  >> (qmatch_asmsub_abbrev_tac ‘r.origin = r_val’
      >> Cases_on ‘r’
      >> ‘n = r_val’ by gvs[]
      >> unabbrev_all_tac
      >> gvs[]
      >> Cases_on ‘b’
      >> EVAL_TAC)
QED

(* -------------------------------------------------------------------------- *)
(* test_path: [F; T; T; F; T; T; T; T; F; F; T; F]                            *)
(*                                                                            *)
(*   0 -> 0/00 -> 0                                                           *)
(*     -> 1/11 -> 1                                                           *)
(*   1 -> 0/11 -> 2                                                           *)
(*     -> 1/00 -> 3                                                           *)
(*   2 -> 0/10 -> 0                                                           *)
(*     -> 1/01 -> 1                                                           *)
(*   3 -> 0/01 -> 2                                                           *)
(*     -> 1/10 -> 3                                                           *)
(*                                                                            *)
(* 0  1  2  3  3  3  4                -  0  0  2  2  02 0                     *)
(* -  1  2  2  3  3  4                -  0  0  0  02 2  0                     *)
(* -  -  2  2  2  5  4                -  -  1  1  1  13 13                    *)
(* -  -  2  3  4  3  3                -  -  1  3  13 1  3                     *)
(*    FT TF TT TT FF TF                  FT TF TT TT FF TF                    *)
(*                                                                            *)
(* Starting at state 0, t=6: [0, 0, 0, 2, 1, 0, 0]                            *)
(*                               .. 2, 1, 0, 0, 0]                            *)
(*                                                                            *)
(*                                                                            *)
(* Starting at state 1, t=4: [1, 0, 2, 1, 0]                                  *)
(*                            .. 2, 1, 0, 0]                                  *)
(*                                                                            *)
(* Starting at state 2, t=4: [2, 1, 0, 0, 0]                                  *)
(*                                                                            *)
(* Starting at state 3, t=6; [3, 3, 1, 0, 2, 1, 0]                            *)
(*                                  .. 2, 1, 0, 0]                            *)
(* -------------------------------------------------------------------------- *)
Theorem vd_find_optimal_reversed_path_test:
  let
    result1 = (vd_find_optimal_reversed_path example_state_machine test_path 0 6);
    result2 = (vd_find_optimal_reversed_path example_state_machine test_path 1 4);
    result3 = (vd_find_optimal_reversed_path example_state_machine test_path 2 4);
    result4 = (vd_find_optimal_reversed_path example_state_machine test_path 3 6);
  in
    (result1 = [0;0;0;2;1;0;0] ∨ result1 = [0;0;2;1;0;0;0]) ∧
    (result2 = [1;0;2;1;0] ∨ result2 = [1;2;1;0;0]) ∧
    (result3 = [2;1;0;0;0]) ∧
    (result4 = [3;3;1;0;2;1;0] ∨ result4 = [3;3;1;2;1;0;0])
Proof
  EVAL_TAC
QED

(*Theorem vd_find_optimal_reversed_path_eval:
  let
    result1 = (vd_find_optimal_reversed_path example_state_machine test_path 0 6);
    result2 = (vd_find_optimal_reversed_path example_state_machine test_path 1 4);
    result3 = (vd_find_optimal_reversed_path example_state_machine test_path 2 4);
    result4 = (vd_find_optimal_reversed_path example_state_machine test_path 3 6);
  in
    result1 = ARB ∧
    result2 = ARB ∧
    result3 = ARB ∧
    result4 = ARB
Proof
  EVAL_TAC
QED*)

(* -------------------------------------------------------------------------- *)
(* Test equivalance of slow version of trellis calculation with fast version  *)
(* for some small values of s and t, through evaluation.                      *)
(* -------------------------------------------------------------------------- *)
Theorem viterbi_trellis_node_slow_test:
  ∀s t.
           s < 4 ∧ t ≤ 3 ⇒
           viterbi_trellis_node_slow example_state_machine test_path s t = viterbi_trellis_node_no_prev_data example_state_machine test_path s t
Proof
  rpt strip_tac
  >> sg ‘(s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) ∧ (t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3)’ >> gvs[]
  >> EVAL_TAC
QED

(*Theorem viterbi_trellis_node_slow_eval:
  let
    s = 0;
    t = 0
  in
    viterbi_trellis_node_slow example_state_machine test_path s t = ARB ∧
    viterbi_trellis_node_no_prev_data example_state_machine test_path s t = ARB
Proof
  rpt strip_tac
  >> EVAL_TAC
QED*)

(* -------------------------------------------------------------------------- *)
(* Test that the slow and fast versions of the function that calculates       *)
(* errors in the trellis are equivalent for some simple examples.             *)
(* -------------------------------------------------------------------------- *)
Theorem get_num_errors_after_step_slow_get_num_errors_after_step_test:
  ∀t r.
  t < 4 ∧
  r.origin < 4 ⇒
  get_num_errors_after_step_slow example_state_machine test_path (SUC t) r = get_num_errors_after_step example_state_machine test_path (SUC t) (viterbi_trellis_row example_state_machine test_path t) r
Proof
  rpt strip_tac
  >> sg ‘(t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) ∧ (r.origin = 0 ∨ r.origin = 1 ∨ r.origin = 2 ∨ r.origin = 3)’
  (* This sequence of tactics will simultaneously prove all 16 proof
     obligations *)
  >> (gvs[]
      >> qmatch_asmsub_abbrev_tac ‘r.origin = r_val’
      >> Cases_on ‘r’
      >> ‘n = r_val’ by gvs[]
      >> unabbrev_all_tac
      >> gvs[]
      >> Cases_on ‘b’
      >> EVAL_TAC)
QED

(*Theorem temp_test_theorem:
  let
    s = 2;
    t = 1;
  in
    viterbi_trellis_node_slow example_state_machine test_path s t = ARB ∧
    viterbi_trellis_node_no_prev_data example_state_machine test_path s t = ARB
Proof
  EVAL_TAC
QED*)

(* -------------------------------------------------------------------------- *)
(* Be extra careful with the special case at time step zero, and test to      *)
(* ensure that it has the expected value, not just the same value as the      *)
(* other implementation.                                                      *)
(* -------------------------------------------------------------------------- *)
(*Theorem viterbi_trellis_node_slow_time_step_zero_test:
  ∀s.
  s < 4 ⇒
  viterbi_trellis_node_slow example_state_machine test_path s 0 =
  <| num_errors := if s = 0 then N0 else INFINITY; prev_state := NONE|>
Proof
  rpt strip_tac
  >> sg ‘(s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3)’ >> gvs[]
  >> EVAL_TAC
QED*)

(*Theorem vd_decode_test:
  let
    decoded_path = vd_decode example_state_machine test_path;
    encoded_decoded_path = vd_encode example_state_machine decoded_path
  in
    decoded_path = ARB ∧
    encoded_decoded_path = ARB ∧
    test_path = ARB ∧
    hamming_distance encoded_decoded_path test_path = ARB                
Proof
  EVAL_TAC
QED*)

val _ = export_theory();
