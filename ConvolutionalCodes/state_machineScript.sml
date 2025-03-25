open HolKernel Parse boolLib bossLib;

val _ = new_theory "state_machine";

open arithmeticTheory;
open listTheory;
open rich_listTheory;
open pred_setTheory;

open logrootTheory;

open dep_rewrite;
  
(* -------------------------------------------------------------------------- *)
(* This theory contains the definition of the state machine used in my proofs *)
(* of the correctness of convolutional codes.                                 *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* CONVOLUTIONAL STATE MACHINE ENCODING                                       *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* It makes sense for all the definitions to be contained at the top of the   *)
(* file because then people can browse through all the definitions, without   *)
(* being distracted by long, verbose proofs that get in the way.              *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* A concrete state machine based on the num type.                            *)
(*                                                                            *)
(* The states of this state machine are all the consecutive natural numbers   *)
(* starting at zero and ending at num_states.                                 *)
(*                                                                            *)
(* The initial state is state 0.                                              *)
(*                                                                            *)
(* Disadvantages:                                                             *)
(* - lacks the generality of the state machine. For example, it's nice to be  *)
(*   able to represent the viterbi state machine where each state is a        *)
(*   bitstring                                                                *)
(*                                                                            *)
(* Advantages:                                                                *)
(* - Has a simple mapping between states and natural numbers, thus can use    *)
(*   the structure of the natural numbers to do nice things.                  *)
(*   - A natural way to "choose" an element of a set by taking the least      *)
(*     element                                                                *)
(*   - A natural way of enumerating through the states                        *)
(*   - A correspondence between states and elements of a list. It is easier   *)
(*     to evaluate a function when enumerating over a list than over a set,   *)
(*     because there are potentially infinite elements in the space that the  *)
(*     set is contained in, and you can't simply enumerate over infinite      *)
(*     elements.                                                              *)
(* -------------------------------------------------------------------------- *)
Datatype:
  state_machine = <|
    num_states : num;
    transition_fn : num # bool -> num # bool list;
    output_length : num;
  |>
End

(* -------------------------------------------------------------------------- *)
(* Ensure that the num state machine is well-formed                           *)
(*                                                                            *)
(* Note: gvs[wfmachine_def] is currently often very inefficient, I assume     *)
(* it's trying to do a lot of simplifications using the properties provided   *)
(* by wfmachine.                                                              *)
(* -------------------------------------------------------------------------- *)
Definition wfmachine_def:
  wfmachine (m : state_machine) ⇔
    (* num_states:
       - there must be at least one state *)
    0 < m.num_states ∧
    (* transition_fn:
       - if the origin of the transition is a valid state, then the
         destination must also be a valid state.
       - any valid state has at least one valid predecessor.
         This is necessary because otherwise when we attempt to find a path
         back through the trellis, we may reach a dead end.
       - the two transitions out of a state must not each arrive at the same
         state. This makes it easier to determine which input was provided to
         the state machine if we know what path was taken through the state
         machine's states. *)
    (∀s b. s < m.num_states ⇒ FST (m.transition_fn (s, b)) < m.num_states) ∧
    (∀s. s < m.num_states ⇒
         (∃s' b. s' < m.num_states ∧ FST (m.transition_fn (s', b)) = s)) ∧
    (* output_length:
       - each transition must output a string of length output_length
       - output_length must be greater than 0 *)
    (∀n b. n < m.num_states ⇒
           LENGTH (SND (m.transition_fn (n, b))) =
           m.output_length) ∧
    0 < m.output_length
End

(* Old property included in well-formedness: the two transitions leading from a state may not arrive at the same state.
(∀s. s < m.num_states ⇒
     ((m .transition_fn <| origin := s; input := T; |>).destination)
≠ (m.transition_fn <| origin := s; input := F; |>).destination) ∧*)


Theorem wfmachine_zero_is_valid[simp] = cj 1 (iffLR wfmachine_def);
Theorem wfmachine_transition_fn_destination_is_valid[simp] = cj 2 (iffLR wfmachine_def) |> SRULE [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM];
Theorem wfmachine_every_state_has_prior_state = cj 3 (iffLR wfmachine_def) |> SRULE [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM];
(*Theorem wfmachine_transition_fn_from_state_injective[simp] = cj 4 (iffLR wfmachine_def) |> SRULE [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM];*)
Theorem wfmachine_transition_fn_output_length[simp] = cj 4 (iffLR wfmachine_def) |> SRULE [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM];
Theorem wfmachine_output_length_greater_than_zero[simp] = cj 5 (iffLR wfmachine_def);

(* -------------------------------------------------------------------------- *)
(* Encodes a binary string using convolutional coding, according to a chosen  *)
(* state machine, starting from a given state                                 *)
(*                                                                            *)
(* Note: you probably should use vd_encode_def2: this ensures consistency     *)
(* with other parts where it is more natural to use FST and SND rather than   *)
(* let (..., ...) = ...                                                       *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_def:
  vd_encode _ [] _ = [] ∧
  vd_encode (m : state_machine) (b::bs : bool list) (s : num) =
  let
    (s', out) = m.transition_fn (s, b)
  in
    out ⧺ vd_encode m bs s'
End

(* -------------------------------------------------------------------------- *)
(* A version of vd_encode which uses the zero-tail termination method for     *)
(* convolutional codes. Assumes that the number of states is equal to         *)
(* 2 ** (window length), as is standard in a convolutional code state         *)
(* machine, but may not be the case for all state machines.                   *)
(*                                                                            *)
(* In general, avoid using this definition, and instead use the vanilla       *)
(* vd_encode, in order to avoid unnecessary duplication of theorems.          *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_padded_def[simp]:
  vd_encode_padded m bs s =
  vd_encode m (bs ⧺ REPLICATE (LOG 2 m.num_states) F) s
End

(* -------------------------------------------------------------------------- *)
(* Calculates the final state you'll end up in if you apply the given state   *)
(* machine to the given bitstring, given an initial state                     *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_state_def:
  vd_encode_state (m : state_machine) [] s = s ∧
  vd_encode_state m (b::bs) s =
  vd_encode_state m bs (FST (m.transition_fn (s, b)))
End 

Definition all_transitions_helper_def:
  all_transitions_helper (m : state_machine) (b : bool) = GENLIST (λn. (n, b)) m.num_states
End

(* -------------------------------------------------------------------------- *)
(* Returns a list of all valid choices of a transition             *)
(* -------------------------------------------------------------------------- *)
Definition all_transitions_def:
  all_transitions (m : state_machine) = all_transitions_helper m T ⧺ all_transitions_helper m F
End

Definition all_transitions_set_helper_def:
  all_transitions_set_helper (m : state_machine) b = {(s, b) | s < m.num_states}
End

(* -------------------------------------------------------------------------- *)
(* Set version of function to return a list of all valid choices of           *)
(* transition                                                                 *)
(* -------------------------------------------------------------------------- *)
Definition all_transitions_set_def:
  all_transitions_set (m : state_machine) = {(s, b) | s < m.num_states ∧ (b ∨ ¬b)}
End

(* -------------------------------------------------------------------------- *)
(* Returns a list of transitions that lead to the given state, as well as the *)
(* input which leads to them. Each element of the list is a                   *)
(* transition                                                          *)
(* -------------------------------------------------------------------------- *)
Definition transition_inverse_def:
  transition_inverse (m : state_machine) dest =
  FILTER (λorgn. FST (m.transition_fn orgn) = dest) (all_transitions m)
End

(* -------------------------------------------------------------------------- *)
(* Returns true if it is possible to reach the state s at time t when         *)
(* starting at the initial state i                                            *)
(* -------------------------------------------------------------------------- *)
Definition is_reachable_def:
  is_reachable m i s t = ∃bs. (LENGTH bs = t ∧ vd_encode_state m bs i = s)
End

Theorem vd_encode_def2:
  ∀m b bs s.
    vd_encode m [] s = [] ∧
    vd_encode m (b::bs) s =
    SND (m.transition_fn (s, b)) ⧺ vd_encode m bs (FST (m.transition_fn (s, b)))
Proof
  rpt strip_tac
  >> gvs[vd_encode_def]
  >> Cases_on ‘m.transition_fn (s,b)’
  >> gvs[]
QED

Theorem wfmachine_nonzero[simp]:
  ∀m.
    wfmachine m ⇒ m.num_states ≠ 0
Proof
  gvs[NOT_ZERO]
QED

Theorem vd_encode_empty[simp]:
  ∀m s. vd_encode m [] s = []
Proof
  rpt strip_tac
  >> EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* See comment for vd_encode_cons                             *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_cons = cj 2 vd_encode_def2;

(* -------------------------------------------------------------------------- *)
(* See comment for vd_encode_append                           *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_append:
  ∀m bs cs s.
    vd_encode m (bs ⧺ cs) s =
    vd_encode m bs s ⧺ vd_encode m cs (vd_encode_state m bs s)          
Proof
  gen_tac
  >> Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[APPEND]
  >> gvs[vd_encode_cons]
  >> gvs[vd_encode_state_def]
QED

Theorem vd_encode_snoc:
  ∀m b bs s.
    vd_encode m (SNOC b bs) s =
    vd_encode m bs s ⧺ SND (m.transition_fn (vd_encode_state m bs s, b))
Proof
  rpt strip_tac
  >> gvs[SNOC_APPEND]
  >> gvs[vd_encode_append]
  >> gvs[vd_encode_def2]
QED

Theorem vd_encode_state_snoc:
  ∀m b bs s.
    vd_encode_state m (SNOC b bs) s = FST (m.transition_fn ((vd_encode_state m bs s), b))
Proof
  Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[]
  >> gvs[vd_encode_state_def]
QED

Theorem all_transitions_helper_mem_is_valid[simp]:
  ∀m b r.
    MEM r (all_transitions_helper m b) ⇒ FST r < m.num_states
Proof
  rpt strip_tac
  >> gvs[all_transitions_helper_def]
  >> gvs[MEM_GENLIST]
QED

Theorem all_transitions_mem_is_valid[simp]:
  ∀m r.
    MEM r (all_transitions m) ⇒ FST r < m.num_states
Proof
  rpt strip_tac
  >> gvs[all_transitions_def]
  >> metis_tac[all_transitions_helper_mem_is_valid]
QED

Theorem all_transitions_helper_mem:
  ∀m r b.
    FST r < m.num_states ∧
    SND r = b ⇒
    MEM r (all_transitions_helper m b)
Proof
  rpt strip_tac
  >> gvs[all_transitions_helper_def]
  >> gvs[MEM_GENLIST]
  >> qexists ‘FST r’
  >> gvs[]
QED

Theorem all_transitions_mem:
  ∀m r.
    FST r < m.num_states ⇒
    MEM r (all_transitions m)
Proof
  rpt strip_tac
  >> gvs[all_transitions_def]
  >> Cases_on ‘SND r’ >> gvs[all_transitions_helper_mem]
QED

Theorem all_transitions_set_list_equiv:
  ∀m t.
    MEM t (all_transitions m) ⇔ t ∈ all_transitions_set m
Proof
  rpt strip_tac
  >> gvs[all_transitions_def, all_transitions_set_def]
  >> EQ_TAC >> rpt strip_tac
  >- (gvs[all_transitions_helper_def]
      >> gvs[MEM_GENLIST])
  >- (gvs[all_transitions_helper_def]
      >> gvs[MEM_GENLIST])
  >> gvs[all_transitions_helper_def]
  >> gvs[MEM_GENLIST]
QED

Theorem all_transitions_helper_listtoset:
  ∀m b.
    set (all_transitions_helper m b) = all_transitions_set_helper m b
Proof
  rpt strip_tac
  >> gvs[all_transitions_helper_def, all_transitions_set_helper_def]
  >> rpt strip_tac
  >> gvs[LIST_TO_SET_GENLIST]
  >> gvs[EXTENSION]
QED

Theorem all_transitions_set_all_transitions_set_helper:
  ∀m. all_transitions_set m = all_transitions_set_helper m T ∪ all_transitions_set_helper m F
Proof
  rpt strip_tac
  >> gvs[all_transitions_set_def, all_transitions_set_helper_def]
  >> gvs[EXTENSION]
  >> rpt strip_tac
  >> EQ_TAC >> rpt strip_tac >> gvs[]
QED

Theorem all_transitions_listtoset:
  ∀m.
    set (all_transitions m) = all_transitions_set m
Proof
  rpt strip_tac
  >> gvs[all_transitions_def, all_transitions_set_all_transitions_set_helper]
  >> gvs[all_transitions_helper_listtoset]
QED

Theorem transition_inverse_mem_all_transitions_set:
  ∀m s r.
    MEM r (transition_inverse m s) ⇒
    r ∈ all_transitions_set m
Proof
  rpt strip_tac
  >> gvs[transition_inverse_def]
  >> gvs[MEM_FILTER]
  >> gvs[all_transitions_set_def]
  >> gvs[all_transitions_def]
  >> gvs[all_transitions_helper_def]
  >> gvs[MEM_GENLIST]
QED

Theorem transition_inverse_mem:
  ∀m s r.
    MEM r (transition_inverse m s) ⇔
      FST (m.transition_fn r) = s ∧ MEM r (all_transitions m)
Proof
  rpt strip_tac
  >> gvs[transition_inverse_def]
  >> gvs[MEM_FILTER]
QED

Theorem transition_inverse_mem_forward[simp]:
  ∀m s r.
    MEM r (transition_inverse m s) ⇒
    FST (m.transition_fn r) = s
Proof
  metis_tac[transition_inverse_mem]
QED

Theorem transition_inverse_mem_is_valid[simp]:
  ∀m s r.
    MEM r (transition_inverse m s) ⇒
    FST r < m.num_states
Proof
  rpt strip_tac
  >> gvs[transition_inverse_def]
  >> gvs[MEM_FILTER]
QED

Theorem transition_inverse_nonempty[simp]:
  ∀m s.
    wfmachine m ∧
    s < m.num_states ⇒
    transition_inverse m s ≠ []
Proof
  rpt strip_tac
  >> gvs[transition_inverse_def]
  >> drule (wfmachine_every_state_has_prior_state)
  >> rpt strip_tac
  >> pop_assum $ qspec_then ‘s’ assume_tac
  >> gvs[]
  >> gvs[FILTER_EQ_NIL]
  >> gvs[EVERY_MEM]
  >> first_x_assum $ qspec_then ‘(s', b)’ assume_tac
  >> gvs[]
  >> pop_assum mp_tac
  >> gvs[NOT_DEF]
  >> irule all_transitions_mem
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* This reduction is used often because we often fold functions to find the   *)
(* best origin over the list of all transitions in the previous step.         *)
(* -------------------------------------------------------------------------- *)
Theorem transition_inverse_cons[simp]:
  ∀m s.
    wfmachine m ∧
    s < m.num_states ⇒
    (HD (transition_inverse m s)) :: (TL (transition_inverse m s)) = transition_inverse m s
Proof
  rpt strip_tac
  >> gvs[CONS]
QED

Theorem vd_encode_length[simp]:
  ∀m bs s.
    wfmachine m ∧
    s < m.num_states ⇒
    LENGTH (vd_encode m bs s) = m.output_length * LENGTH bs
Proof
  gen_tac
  >> Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[vd_encode_cons]
  >> gvs[ADD1]
QED

Theorem vd_encode_state_is_valid[simp]:
  ∀m bs s.
    wfmachine m ∧ 
    s < m.num_states ⇒
    vd_encode_state m bs s < m.num_states
Proof
  gen_tac
  >> Induct_on ‘bs’
  >- (rpt strip_tac
      >> gvs[vd_encode_state_def]
     )
  >> rpt strip_tac
  >> gvs[vd_encode_state_def]
QED

Theorem transition_fn_output_length_0[simp]:
  ∀m b s.
    wfmachine m ∧
    s < m.num_states ∧
    m.output_length = 0 ⇒
    SND (m.transition_fn (s, b)) = []
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[GSYM LENGTH_EQ_0]
  >> metis_tac[wfmachine_transition_fn_output_length]
QED

Theorem vd_encode_output_length_0[simp]:
  ∀m bs s.
    wfmachine m ∧
    s < m.num_states ∧
    m.output_length = 0 ⇒
    vd_encode m bs s = []
Proof
  gen_tac
  >> Induct_on ‘bs’ >> rpt strip_tac
  >- gvs[vd_encode_def2]
  >> gvs[vd_encode_cons]
QED

Theorem all_transitions_helper_valid:
  ∀m b.
    EVERY (λs2. FST s2 < m.num_states) (all_transitions_helper m b)
Proof
  rpt strip_tac
  >> gvs[EVERY_EL]
  >> rpt strip_tac
  >> gvs[all_transitions_helper_def]
QED

Theorem all_transitions_valid:
  ∀m.
    EVERY (λs2. FST s2 < m.num_states) (all_transitions m)
Proof
  rpt strip_tac
  >> gvs[all_transitions_def]
  >> gvs[all_transitions_helper_valid]
QED

Theorem transition_inverse_valid:
  ∀m s.
    EVERY (λs2. FST s2 < m.num_states) (transition_inverse m s)
Proof
  rpt strip_tac
  >> gvs[transition_inverse_def]
  >> irule EVERY_FILTER_IMP
  >> gvs[all_transitions_valid]
QED

Theorem mem_transition_inverse_transition_fn_destination:
  ∀m r.
    FST r < m.num_states ⇒
    MEM r (transition_inverse m (FST (m.transition_fn r)))
Proof
  rpt strip_tac
  >> irule (iffRL transition_inverse_mem)
  >> gvs[]
  >> gvs[all_transitions_def, all_transitions_helper_def]
  >> gvs[MEM_GENLIST]
  >> Cases_on ‘SND r’
  >- (disj1_tac
      >> qexists ‘FST r’
      >> gvs[]
      >> Cases_on ‘r’ >> gvs[])
  >> disj2_tac
  >> qexists ‘FST r’
  >> gvs[]
  >> Cases_on ‘r’ >> gvs[]
QED

Theorem is_reachable_init_zero[simp]:
  ∀m i. is_reachable m i i 0
Proof
  rpt strip_tac
  >> EVAL_TAC
  >> qexists ‘[]’
  >> EVAL_TAC
QED

Theorem not_is_reachable_noninit_zero[simp]:
  ∀m i s.
    s ≠ i ⇒
    ¬is_reachable m i s 0
Proof
  rpt gen_tac
  >> disch_tac
  >> EVAL_TAC
  >> gvs[]
  >> EVAL_TAC
  >> CCONTR_TAC
  >> gvs[]
QED

Theorem is_reachable_transition_fn:
  ∀m i s t b.
    is_reachable m i s t ⇒ is_reachable m i (FST (m.transition_fn (s, b))) (SUC t)
Proof
  rpt strip_tac
  >> gvs[is_reachable_def]
  >> qexists ‘SNOC (b) bs’
  >> gvs[]
  >> gvs[vd_encode_state_snoc]
QED

Theorem is_reachable_transition_fn_destination:
  ∀m i r t.
    is_reachable m i (FST r) t ⇒ is_reachable m i (FST (m.transition_fn r)) (SUC t)
Proof
  rpt strip_tac
  >> qspecl_then [‘m’, ‘i’, ‘FST r’, ‘t’, ‘SND r’] assume_tac is_reachable_transition_fn
  >> gvs[]
QED

Theorem is_reachable_suc:
  ∀m i s t.
    is_reachable m i s (SUC t) ⇔ ∃s' b. is_reachable m i s' t ∧ (FST (m.transition_fn (s', b))) = s
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (disch_tac
      >> gvs[is_reachable_def]
      >> qexistsl [‘vd_encode_state m (FRONT bs) i’, ‘LAST bs’]
      >> conj_tac
      >- (qexists ‘FRONT bs’
          >> gvs[]
          >> Cases_on ‘bs’ using SNOC_CASES >> gvs[])
      >> Cases_on ‘bs’ using SNOC_CASES
      >- gvs[]
      >> gvs[vd_encode_state_snoc]
     )
  >> rpt strip_tac
  >> gvs[]
  >> irule is_reachable_transition_fn
  >> gvs[]
QED

Theorem is_reachable_suc_transition_fn_destination:
  ∀m i s t.
    is_reachable m i s (SUC t) ⇔ ∃r. is_reachable m i (FST r) t ∧ (FST (m.transition_fn r)) = s
Proof
  rpt strip_tac
  >> gvs[]
  >> gvs[is_reachable_suc]
  >> EQ_TAC
  >- (rpt strip_tac
      >> qexists ‘(s', b)’
      >> gvs[])
  >> rpt strip_tac
  >> qexistsl [‘FST r’, ‘SND r’]
  >> gvs[]
QED

Theorem vd_encode_state_empty[simp]:
  ∀m s.
    vd_encode_state m [] s = s
Proof
  rpt strip_tac
  >> gvs[vd_encode_state_def]
QED

Theorem is_reachable_init[simp]:
  ∀m i s.
    is_reachable m i s 0 ⇔ s = i
Proof
  rpt strip_tac
  >> gvs[is_reachable_def]
QED

Theorem vd_encode_singleton[simp]:
  ∀m b s.
    vd_encode m [b] s = SND (m.transition_fn (s, b))
Proof
  rpt strip_tac
  >> gvs[vd_encode_def2]
QED

Theorem is_reachable_vd_encode_state[simp]:
  ∀m i bs t.
    LENGTH bs = t ⇒
    is_reachable m i (vd_encode_state m bs i) t
Proof
  rpt strip_tac
  >> gvs[is_reachable_def]
  >> qexists ‘bs’
  >> gvs[]
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
  >> qexists ‘FST (m.transition_fn (s, F))’
  >> gvs[]
  >> gvs[is_reachable_suc]
  >> qexistsl [‘s’, ‘F’]
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Unit tests                                                                 *)
(* (It makes sense for tests to be at the end because then they won't slow    *)
(*  down computation when writing theories and modifying the file, but they   *)
(*  will be run once during holmake to ensure correctness of the final        *)
(*  combined binary)                                                          *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* This num state machine corresponds to the convolutional code which has a   *)
(* window size of 3, and creates two parity bits, the first of which is       *)
(* formed by adding together all inputs, and the second of which is formed    *)
(* by adding together the last 2 inputs.                                      *)
(* -------------------------------------------------------------------------- *)
Definition example_state_machine_def:
  example_state_machine = <|
    num_states := 4;
    transition_fn := λd.
                       case SND d of
                         T => (case FST d of
                                 0 => (1, [T; T])
                               | 1 => (3, [F; F])
                               | 2 => (1, [F; T])
                               | 3 => (3, [T; F])
                              )
                       | F => (case FST d of
                                 0 => (0, [F; F])
                               | 1 => (2, [T; T])
                               | 2 => (0, [T; F])
                               | 3 => (2, [F; T])
                              );
    output_length := 2;
  |> : state_machine
End

Theorem wfmachine_example_state_machine:
  wfmachine example_state_machine
Proof
  PURE_REWRITE_TAC[wfmachine_def]
  >> rpt conj_tac
  >- EVAL_TAC
  >- (gvs[example_state_machine_def]
      >> rpt strip_tac
      >> Cases_on ‘b’ >> gvs[]
      >> Cases_on ‘s’ >> gvs[]
      >> Cases_on ‘n’ >> gvs[]
      >> Cases_on ‘n'’ >> gvs[]
     )
  >- (gvs[example_state_machine_def]
      >> rpt strip_tac
      >> Cases_on ‘s’
      >- (qexistsl [‘0’, ‘F’]
          >> EVAL_TAC
         )
      >> Cases_on ‘n’
      >- (qexistsl [‘0’, ‘T’]
          >> EVAL_TAC
         )
      >> Cases_on ‘n'’
      >- (qexistsl [‘1’, ‘F’]
          >> EVAL_TAC
         )
      >> Cases_on ‘n’
      >- (qexistsl [‘1’, ‘T’]
          >> EVAL_TAC
         )
      >> EVAL_TAC
      >> gvs[ADD1]
     )
  (*>- (rpt strip_tac
          >> gvs[example_state_machine_def]
          >> Cases_on ‘s’ >> gvs[]
          >> Cases_on ‘n’ >> gvs[]
          >> Cases_on ‘n'’ >> gvs[]
     )*)
  >- (rpt strip_tac
      >> gvs[example_state_machine_def]
      >> Cases_on ‘b’ >> gvs[]
      >> Cases_on ‘n’ >> gvs[]
      >> Cases_on ‘n'’ >> gvs[]
      >> Cases_on ‘n’ >> gvs[]
     )
  >- gvs[example_state_machine_def]
QED 

(* -------------------------------------------------------------------------- *)
(* An example message which may have been recieved.                           *)
(*                                                                            *)
(* Length: 12                                                                 *)
(* Decoded length: 6 (if using example_state_machine)                         *)
(* -------------------------------------------------------------------------- *)
Definition test_path_def:
  test_path = [F; T; T; F; T; T; T; T; F; F; T; F]
End

(* -------------------------------------------------------------------------- *)
(* Simple test to make sure the convolutional code is providing the output    *)
(* I would expect if I manually did the computation myself                    *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_test1:
  vd_encode example_state_machine [F; T; T; T; F] 0 = [F; F; T; T; F; F; T; F; F; T]  
Proof
  EVAL_TAC
QED

Theorem transition_inverse_test:
  let
    test_inverse = transition_inverse example_state_machine 2;
  in
    LENGTH test_inverse = 2 ∧
    MEM (1, F) test_inverse ∧
    MEM (3, F) test_inverse
Proof
  EVAL_TAC
QED

val _ = export_theory();
