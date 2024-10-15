open HolKernel Parse boolLib bossLib;

val _ = new_theory "state_machine";

open arithmeticTheory;
open listTheory;
open rich_listTheory;
open pred_setTheory;

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

Datatype:
  transition = <|
    origin : num;
    input : bool;
  |>
End

(* -------------------------------------------------------------------------- *)
(* The automatically generated record theorems don't seem to be automatically *)
(* fetched or something, so I have to fetch them manually.                    *)
(* -------------------------------------------------------------------------- *)
val transition_component_equality_local = fetch "state_machine" "transition_component_equality";

Theorem transition_literal_components[simp]:
  ∀r.
    <| origin := r.origin; input := r.input |> = r
Proof
  rpt strip_tac
  >> gvs[transition_component_equality_local]
QED

Datatype:
  transition_destination = <|
    destination : num;
    output : bool list;
  |> 
End

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
    transition_fn : transition -> transition_destination;
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
    (∀r. r.origin < m.num_states ⇒ (m.transition_fn r).destination < m.num_states) ∧
    (∀s. s < m.num_states ⇒ (∃s' b. s' < m.num_states ∧ (m.transition_fn <| origin := s'; input := b; |>).destination = s)) ∧
    (∀s. s < m.num_states ⇒ (m.transition_fn <| origin := s; input := T; |>).destination ≠ (m.transition_fn <| origin := s; input := F; |>).destination) ∧
    (* output_length:
       - each transition must output a string of length output_length
       - output_length must be greater than 0*)
    (∀n b. n < m.num_states ⇒ LENGTH (m.transition_fn <| origin := n; input := b |>).output = m.output_length) ∧
    0 < m.output_length
End

Theorem wfmachine_zero_is_valid[simp] = cj 1 (iffLR wfmachine_def);
Theorem wfmachine_transition_fn_destination_is_valid[simp] = cj 2 (iffLR wfmachine_def) |> SRULE [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM];
Theorem wfmachine_every_state_has_prior_state = cj 3 (iffLR wfmachine_def) |> SRULE [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM];
Theorem wfmachine_transition_fn_from_state_injective[simp] = cj 4 (iffLR wfmachine_def) |> SRULE [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM];
Theorem wfmachine_transition_fn_output_length[simp] = cj 5 (iffLR wfmachine_def) |> SRULE [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM];
Theorem wfmachine_output_length_greater_than_zero[simp] = cj 6 (iffLR wfmachine_def);

(* -------------------------------------------------------------------------- *)
(* Helper function that does the actual work to encode a binary string using  *)
(* convolutional coding, according to a chosen state machine.                 *)
(*                                                                            *)
(* This function additionally has a parameter to keep track of the current    *)
(* state that the state machine is in.                                        *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_from_state_def:
  vd_encode_from_state _ [] _ = [] ∧
  vd_encode_from_state (m : state_machine) (b::bs : bool list) (s : num) =
  let
    d = m.transition_fn <| origin := s; input := b; |>
  in
    d.output ⧺ vd_encode_from_state m bs d.destination
End

(* -------------------------------------------------------------------------- *)
(* Encodes a binary string using convolutional coding, according to a chosen  *)
(* state machine                                                              *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_def:
  vd_encode (m : state_machine) bs = vd_encode_from_state m bs 0
End

(* -------------------------------------------------------------------------- *)
(* Helper function to calculate the final state you'll end up in if you apply *)
(* the given state machine to the given bitstring. Also has a variable to     *)
(* keep track of the current state we're in.                                  *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_state_from_state_def:
  vd_encode_state_from_state (m : state_machine) [] s = s ∧
  vd_encode_state_from_state m (b::bs) s =
  vd_encode_state_from_state m bs (m.transition_fn <| origin := s; input := b; |>).destination
End 

(* -------------------------------------------------------------------------- *)
(* Calculates the final state you'll end up in if you apply the given state   *)
(* machine to the given bitstring.                                            *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_state_def:
  vd_encode_state (m : state_machine) bs = vd_encode_state_from_state m bs 0
End

Definition all_transitions_helper_def:
  all_transitions_helper (m : state_machine) (b : bool) = GENLIST (λn. <| origin := n; input := b |>) m.num_states
End

(* -------------------------------------------------------------------------- *)
(* Returns a list of all valid choices of a transition             *)
(* -------------------------------------------------------------------------- *)
Definition all_transitions_def:
  all_transitions (m : state_machine) = all_transitions_helper m T ⧺ all_transitions_helper m F
End

Definition all_transitions_set_helper_def:
  all_transitions_set_helper (m : state_machine) b = {<| origin := s; input := b |> | s < m.num_states}
End

(* -------------------------------------------------------------------------- *)
(* Set version of function to return a list of all valid choices of           *)
(* transition                                                                 *)
(* -------------------------------------------------------------------------- *)
Definition all_transitions_set_def:
  all_transitions_set (m : state_machine) = {<| origin := s; input := b |> | s < m.num_states ∧ (b ∨ ¬b)}
End

(* -------------------------------------------------------------------------- *)
(* Returns a list of transitions that lead to the given state, as well as the *)
(* input which leads to them. Each element of the list is a                   *)
(* transition                                                          *)
(* -------------------------------------------------------------------------- *)
Definition transition_inverse_def:
  transition_inverse (m : state_machine) dest =
  FILTER (λorgn. (m.transition_fn orgn).destination = dest) (all_transitions m)
End

(* -------------------------------------------------------------------------- *)
(* Obsolete. We no longer need to work with paths when decoding.              *)
(* TODO: Move to obsolete.txt, along with relevant theorems                   *)
(* -------------------------------------------------------------------------- *)
Definition code_to_path_from_state_def:
  code_to_path_from_state m [] s = [s] ∧
  code_to_path_from_state m (b::bs) s =  s::(code_to_path_from_state m bs (m.transition_fn <| origin := s; input := b; |>).destination)
End

(* -------------------------------------------------------------------------- *)
(* Obsolete. We no longer need to work with paths when decoding               *)
(* TODO: Move to obsolete.txt, along with relevant theorems                   *)
(* -------------------------------------------------------------------------- *)
Definition code_to_path_def:
  code_to_path m bs = code_to_path_from_state m bs 0
End

(* -------------------------------------------------------------------------- *)
(* Takes a state machine and two states, and returns the input that would     *)
(* lead between those states.                                                 *)
(*                                                                            *)
(* Returns either F or T arbitrarily (undefined behaviour) if there is no     *)
(* such input.                                                                *)
(* -------------------------------------------------------------------------- *)
Definition states_to_transition_input_def:
  states_to_transition_input m s1 s2 =
  let
    output_on_F = m.transition_fn <| origin := s1; input := F |>
  in
    if output_on_F.destination = s2 then F else T
End

(* -------------------------------------------------------------------------- *)
(* Takes a sequence of states which denotes a path through the state machine, *)
(* and returns the sequence of 0s/1s which would produce that path through    *)
(* the state machine                                                          *)
(* -------------------------------------------------------------------------- *)
Definition path_to_code_def:
  path_to_code m [] = [] ∧
  path_to_code m (p::[]) = [] ∧
  path_to_code m (p1::p2::ps) = (states_to_transition_input m p1 p2) :: (path_to_code m (p2::ps))
End

(* -------------------------------------------------------------------------- *)
(* Returns true if it is possible to reach the state s at time t when         *)
(* starting at 0.                                                             *)
(* -------------------------------------------------------------------------- *)
Definition is_reachable_def:
  is_reachable m s t = ∃bs. (LENGTH bs = t ∧ vd_encode_state m bs = s)
End

(* -------------------------------------------------------------------------- *)
(* This should be automatically expanded, because it's not an important       *)
(* enough definition to write out a bunch of theorems for, but it is          *)
(* complicated enough that I feel it may deserve its own name.                *)
(* -------------------------------------------------------------------------- *)
Definition vd_can_step_def:
  vd_can_step m s s' = ∃b. (m.transition_fn <| origin := s; input := b; |>).destination = s'
End

Definition path_is_connected_def:
  path_is_connected m [] = T ∧
  path_is_connected m (p::[]) = T ∧
  path_is_connected m (p::p'::ps) = (vd_can_step m p p' ∧ path_is_connected m (p'::ps))
End

Definition path_is_valid_def:
  path_is_valid m ps = ∃bs. code_to_path m bs = ps
End

Definition path_is_valid_from_state_def:
  path_is_valid_from_state m ps s = ∃bs. code_to_path_from_state m bs s = ps
End

Definition path_is_valid_or_empty_def:
  path_is_valid_or_empty m ps = ((ps = []) ∨ path_is_valid m ps)
End  

Theorem vd_encode_empty[simp]:
  ∀m. vd_encode m [] = []
Proof
  rpt strip_tac
  >> EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* See comment for vd_encode_cons                             *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_from_state_cons:
  ∀m b bs s.
    vd_encode_from_state m (b :: bs) s =
    (m.transition_fn <| origin := s; input := b; |>).output ⧺ (vd_encode_from_state m bs (m.transition_fn <| origin := s; input := b; |>).destination)
Proof
  rpt strip_tac
  >> gvs[vd_encode_from_state_def]
  >> gvs[vd_encode_state_from_state_def]
QED

(* -------------------------------------------------------------------------- *)
(* Can break convolutional encoding up into doing a step, with the rest of    *)
(* the encoding appended on, starting from the appropriate state              *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_cons:
  ∀m b bs. vd_encode m (b :: bs) =
           (m.transition_fn <| origin := 0; input := b; |>).output ⧺ (vd_encode_from_state m bs (m.transition_fn <| origin := 0; input := b; |>).destination)
Proof
  rpt strip_tac
  >> gvs[vd_encode_def]
  >> gvs[vd_encode_state_def]
  >> PURE_ONCE_REWRITE_TAC[vd_encode_from_state_cons]
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* See comment for vd_encode_append                           *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_from_state_append:
  ∀m bs cs s.
    vd_encode_from_state m (bs ⧺ cs) s =
    vd_encode_from_state m bs s ⧺ vd_encode_from_state m cs (vd_encode_state_from_state m bs s)          
Proof
  gen_tac
  >> Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[APPEND]
  >> gvs[vd_encode_from_state_cons]
  >> gvs[vd_encode_state_from_state_def]
QED

(* -------------------------------------------------------------------------- *)
(* Can break convolutional encoding up into two halves: doing a bunch of      *)
(* steps from the initial state, then doing a bunch of steps from the state   *)
(* that is reached at this point.                                             *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_append:
  ∀m bs cs.
    vd_encode m (bs ⧺ cs) =
    (vd_encode m bs) ⧺ (vd_encode_from_state m cs (vd_encode_state m bs))
Proof
  rpt strip_tac
  >> gvs[vd_encode_def, vd_encode_state_def]
  >> gvs[vd_encode_from_state_append]
QED

(* -------------------------------------------------------------------------- *)
(* Can break convolutional encoding up into doing a bunch of steps from the   *)
(* initial state, then doing a final step from the final state.               *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_snoc:
  ∀m b bs. vd_encode m (SNOC b bs) =
           (vd_encode m bs) ⧺ (vd_encode_from_state m [b] (vd_encode_state m bs))
Proof
  gvs[SNOC]
  >> gvs[vd_encode_append]
QED

Theorem vd_encode_state_from_state_snoc:
  ∀m b bs s.
    vd_encode_state_from_state m (SNOC b bs) s = (m.transition_fn <| origin := (vd_encode_state_from_state m bs s); input := b; |>).destination
Proof
  Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[]
  >> gvs[vd_encode_state_from_state_def]
QED

Theorem vd_encode_state_snoc:
  ∀m b bs.
    vd_encode_state m (SNOC b bs) = (m.transition_fn <| origin := (vd_encode_state m bs); input := b; |>).destination
Proof
  gvs[vd_encode_state_def, vd_encode_state_from_state_snoc]
QED

Theorem all_transitions_helper_mem_is_valid[simp]:
  ∀m b r.
    MEM r (all_transitions_helper m b) ⇒ r.origin < m.num_states
Proof
  rpt strip_tac
  >> gvs[all_transitions_helper_def]
  >> gvs[MEM_GENLIST]
QED

Theorem all_transitions_mem_is_valid[simp]:
  ∀m r.
    MEM r (all_transitions m) ⇒ r.origin < m.num_states
Proof
  rpt strip_tac
  >> gvs[all_transitions_def]
  >> metis_tac[all_transitions_helper_mem_is_valid]
QED


Theorem all_transitions_helper_mem:
  ∀m r b.
    r.origin < m.num_states ∧
    r.input = b ⇒
    MEM r (all_transitions_helper m b)
Proof
  rpt strip_tac
  >> gvs[all_transitions_helper_def]
  >> gvs[MEM_GENLIST]
  >> qexists ‘r.origin’
  >> gvs[]
  >> gvs[transition_component_equality_local]
QED

Theorem all_transitions_mem:
  ∀m r.
    r.origin < m.num_states ⇒
    MEM r (all_transitions m)
Proof
  rpt strip_tac
  >> Cases_on ‘r’
  >> gvs[all_transitions_def]
  >> Cases_on ‘b’ >> gvs[all_transitions_helper_mem]
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
      (m.transition_fn r).destination = s ∧ MEM r (all_transitions m)
Proof
  rpt strip_tac
  >> gvs[transition_inverse_def]
  >> gvs[MEM_FILTER]
QED

Theorem transition_inverse_mem_forward[simp]:
  ∀m s r.
    MEM r (transition_inverse m s) ⇒
    (m.transition_fn r).destination = s
Proof
  metis_tac[transition_inverse_mem]
QED

Theorem transition_inverse_mem_is_valid[simp]:
  ∀m s r.
    MEM r (transition_inverse m s) ⇒
    r.origin < m.num_states
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
  >> first_x_assum $ qspec_then ‘<|origin := s'; input := b |>’ assume_tac
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

Theorem vd_encode_from_state_length[simp]:
  ∀m bs s.
    wfmachine m ∧
    s < m.num_states ⇒
    LENGTH (vd_encode_from_state m bs s) = m.output_length * LENGTH bs
Proof
  gen_tac
  >> Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[vd_encode_from_state_cons]
  >> gvs[ADD1]
QED

Theorem vd_encode_length[simp]:
  ∀m bs.
    wfmachine m ⇒
    LENGTH (vd_encode m bs) = m.output_length * LENGTH bs
Proof
  rpt strip_tac
  >> gvs[vd_encode_def]
  >> DEP_PURE_ONCE_REWRITE_TAC [vd_encode_from_state_length]
  >> gvs[]
QED

Theorem transition_fn_destination_is_valid[simp]:
  ∀m r.
    wfmachine m ∧
    r.origin < m.num_states ⇒
    (m.transition_fn r).destination < m.num_states
Proof
  rpt strip_tac
  >> gvs[]
QED

Theorem vd_encode_state_from_state_is_valid[simp]:
  ∀m bs s.
    wfmachine m ∧ 
    s < m.num_states ⇒
    vd_encode_state_from_state m bs s < m.num_states
Proof
  gen_tac
  >> Induct_on ‘bs’
  >- (rpt strip_tac
      >> gvs[vd_encode_state_from_state_def]
     )
  >> rpt strip_tac
  >> gvs[vd_encode_state_from_state_def]
QED

Theorem vd_encode_state_is_valid[simp]:
  ∀m bs.
    wfmachine m ⇒
    vd_encode_state m bs < m.num_states
Proof
  rpt strip_tac
  >> gvs[vd_encode_state_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[vd_encode_state_from_state_is_valid]
QED

Theorem transition_fn_output_length_0[simp]:
  ∀m b s.
    wfmachine m ∧
    s < m.num_states ∧
    m.output_length = 0 ⇒
    (m.transition_fn <| origin := s; input := b |>).output = []
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[GSYM LENGTH_EQ_0]
  >> metis_tac[wfmachine_transition_fn_output_length]
QED

Theorem vd_encode_from_state_output_length_0[simp]:
  ∀m bs s.
    wfmachine m ∧
    s < m.num_states ∧
    m.output_length = 0 ⇒
    vd_encode_from_state m bs s = []
Proof
  gen_tac
  >> Induct_on ‘bs’ >> rpt strip_tac
  >- gvs[vd_encode_from_state_def]
  >> gvs[vd_encode_from_state_cons]
QED

Theorem vd_encode_output_length_0[simp]:
  ∀m bs s.
    wfmachine m ∧
    m.output_length = 0 ⇒
    vd_encode m bs = []
Proof
  gvs[vd_encode_def]
  >> rpt strip_tac
  >> irule vd_encode_from_state_output_length_0
  >> gvs[]
QED

Theorem all_transitions_helper_valid:
  ∀m b.
    EVERY (λs2. s2.origin < m.num_states) (all_transitions_helper m b)
Proof
  rpt strip_tac
  >> gvs[EVERY_EL]
  >> rpt strip_tac
  >> gvs[all_transitions_helper_def]
QED

Theorem all_transitions_valid:
  ∀m.
    EVERY (λs2. s2.origin < m.num_states) (all_transitions m)
Proof
  rpt strip_tac
  >> gvs[all_transitions_def]
  >> gvs[all_transitions_helper_valid]
QED

Theorem transition_inverse_valid:
  ∀m s.
    EVERY (λs2. s2.origin < m.num_states) (transition_inverse m s)
Proof
  rpt strip_tac
  >> gvs[transition_inverse_def]
  >> irule EVERY_FILTER_IMP
  >> gvs[all_transitions_valid]
QED

Theorem mem_transition_inverse_transition_fn_destination:
  ∀m r.
    r.origin < m.num_states ⇒
    MEM r (transition_inverse m (m.transition_fn r).destination)
Proof
  rpt strip_tac
  >> irule (iffRL transition_inverse_mem)
  >> gvs[]
  >> gvs[all_transitions_def, all_transitions_helper_def]
  >> gvs[MEM_GENLIST]
  >> Cases_on ‘r.input’
  >- (disj1_tac
      >> qexists ‘r.origin’
      >> gvs[transition_component_equality_local])
  >> disj2_tac
  >> qexists ‘r.origin’
  >> gvs[transition_component_equality_local]
QED

Theorem code_to_path_from_state_hd:
  ∀m bs s.
    HD (code_to_path_from_state m bs s) = s
Proof
  Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[code_to_path_from_state_def]
QED

Theorem code_to_path_hd:
  ∀m bs.
    HD (code_to_path m bs) = 0
Proof
  gvs[code_to_path_from_state_hd, code_to_path_def]
QED

Theorem code_to_path_from_state_null[simp]:
  ∀m bs s.
    ¬NULL (code_to_path_from_state m bs s)
Proof
  rpt strip_tac
  >> Cases_on ‘bs’
  >> gvs[code_to_path_from_state_def]
QED

Theorem code_to_path_null[simp]:
  ∀m bs.
    ¬NULL (code_to_path m bs)
Proof
  gvs[code_to_path_def, code_to_path_from_state_null]
QED

Theorem code_to_path_from_state_length:
  ∀m bs s.
    LENGTH (code_to_path_from_state m bs s) = LENGTH bs + 1
Proof
  Induct_on ‘bs’ >> rpt strip_tac >> gvs[code_to_path_from_state_def]
QED

Theorem code_to_path_length:
  ∀m bs.
    LENGTH (code_to_path m bs) = LENGTH bs + 1
Proof
  rpt strip_tac
  >> gvs[code_to_path_def, code_to_path_from_state_length] 
QED

Theorem code_to_path_from_state_nonempty[simp]:
  ∀m bs s.
    code_to_path_from_state m bs s ≠ []
Proof
  rpt strip_tac
  >> gvs[GSYM NULL_EQ, code_to_path_from_state_null]
QED

Theorem code_to_path_nonempty[simp]:
  ∀m bs.
    code_to_path m bs ≠ []
Proof
  gvs[code_to_path_from_state_nonempty, code_to_path_def]
QED

Theorem code_to_path_from_state_append:
  ∀m bs cs s.
    code_to_path_from_state m (bs ⧺ cs) s = (code_to_path_from_state m bs s) ⧺ (TL (code_to_path_from_state m cs (vd_encode_state_from_state m bs s)))
Proof
  Induct_on ‘bs’
  >- (EVAL_TAC
      >> rpt strip_tac
      >> qspecl_then [‘m’, ‘cs’, ‘s’] assume_tac code_to_path_from_state_hd
      >> qmatch_goalsub_abbrev_tac ‘TL donotrewrite’
      >> last_x_assum (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
      >> unabbrev_all_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[CONS]
      >> gvs[])
  >> rpt strip_tac
  >> gvs[]
  >> gvs[code_to_path_from_state_def]
  >> gvs[vd_encode_state_from_state_def]
QED

Theorem code_to_path_from_state_snoc:
  ∀m b bs s.
    code_to_path_from_state m (SNOC b bs) s = SNOC ((m.transition_fn <| origin := (vd_encode_state_from_state m bs s); input := b |>).destination ) (code_to_path_from_state m bs s)
Proof
  rpt strip_tac
  >> gvs[SNOC]
  >> gvs[code_to_path_from_state_append]
  >> gvs[code_to_path_from_state_def]
QED

Theorem code_to_path_append:
  ∀m bs cs.
    code_to_path m (bs ⧺ cs) = (code_to_path m bs) ⧺ (TL (code_to_path_from_state m cs (vd_encode_state m bs)))
Proof
  rpt strip_tac
  >> gvs[code_to_path_def, code_to_path_from_state_append, vd_encode_state_def]
QED

Theorem code_to_path_snoc:
  ∀m b bs.
    code_to_path m (SNOC b bs) = SNOC ((m.transition_fn <| origin := (vd_encode_state m bs); input := b |>).destination) (code_to_path m bs)
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[code_to_path_def]
  >> PURE_REWRITE_TAC[code_to_path_from_state_snoc]
  >> gvs[]
  >> gvs[vd_encode_state_def]
QED

Theorem code_to_path_from_state_last:
  ∀m bs s.
    LAST (code_to_path_from_state m bs s) = (vd_encode_state_from_state m bs s)
Proof
  Induct_on ‘bs’ >> rpt strip_tac
  >- EVAL_TAC
  >> gvs[vd_encode_state_from_state_def]
  >> gvs[code_to_path_from_state_def]
  >> pop_assum $ qspecl_then [‘m’, ‘(m.transition_fn <| origin := s; input := h |>).destination’] assume_tac
  >> pop_assum (fn th => gvs[SYM th])
  >> gvs[LAST_DEF]
QED

Theorem code_to_path_last:
  ∀m bs.
    LAST (code_to_path m bs) = (vd_encode_state m bs)
Proof
  gvs[code_to_path_from_state_last, code_to_path_def, vd_encode_state_def]
QED

Theorem code_to_path_from_state_vd_can_step_cons:
  ∀m bs p p' ps s.
    code_to_path_from_state m bs s = p::p'::ps ⇒
    vd_can_step m p p'
Proof
  rpt strip_tac
  >> Cases_on ‘bs’
  >- gvs[code_to_path_def, code_to_path_from_state_def]
  >> gvs[code_to_path_def, code_to_path_from_state_def]
  >> Cases_on ‘t’
  >- (gvs[code_to_path_def, code_to_path_from_state_def]
      >> gvs[vd_can_step_def]
      >> qexists ‘h’
      >> gvs[])
  >> gvs[code_to_path_from_state_def]
  >> gvs[vd_can_step_def]
  >> qexists ‘h’
  >> gvs[]
QED

Theorem code_to_path_from_state_vd_can_step:
  ∀m bs p p' ps ps' s.
    code_to_path_from_state m bs s = (ps ⧺ [p; p'] ⧺ ps') ⇒
    vd_can_step m p p'
Proof
  Induct_on ‘ps’
  >- (rpt strip_tac
      >> gvs[]
      >> irule code_to_path_from_state_vd_can_step_cons
      >> qexistsl [‘bs’, ‘ps'’, ‘s’]
      >> gvs[]
     )
  >> rpt strip_tac
  >> last_x_assum irule
  >> Cases_on ‘bs’
  >- gvs[code_to_path_def, code_to_path_from_state_def]
  >> gvs[]
  >> gvs[code_to_path_def, code_to_path_from_state_def]
  >> qexistsl [‘t’, ‘ps'’, ‘(m.transition_fn <| origin := h; input := h' |>).destination’]
  >> gvs[]
QED

Theorem code_to_path_from_state_vd_can_step_snoc:
  ∀m bs p p' ps s.
    code_to_path_from_state m bs s  = SNOC p' (SNOC p ps) ⇒
    vd_can_step m p p'
Proof
  rpt strip_tac
  >> irule code_to_path_from_state_vd_can_step
  >> qexistsl [‘bs’, ‘ps’, ‘[]’, ‘s’]
  >> gvs[]
QED

Theorem code_to_path_vd_can_step_cons:
  ∀m bs p p' ps.
    code_to_path m bs = p::p'::ps ⇒
    vd_can_step m p p'
Proof
  metis_tac[code_to_path_def, code_to_path_from_state_vd_can_step_cons]
QED

Theorem code_to_path_vd_can_step:
  ∀m bs p p' ps ps'.
    code_to_path m bs = (ps ⧺ [p; p'] ⧺ ps') ⇒
    vd_can_step m p p'
Proof
  metis_tac[code_to_path_def, code_to_path_from_state_vd_can_step]
QED

Theorem code_to_path_vd_can_step_snoc:
  ∀m bs p p' ps.
    code_to_path m bs = SNOC p' (SNOC p ps) ⇒
    vd_can_step m p p'
Proof
  metis_tac[code_to_path_def, code_to_path_from_state_vd_can_step_snoc]
QED

(* -------------------------------------------------------------------------- *)
(* If there exists a way to step from s to s', then states_to_transition_input*)
(* will return that way.                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem transition_fn_states_to_transition_input:
  ∀m s s' b. (m.transition_fn <| origin := s; input := b |>).destination = s' ⇒
             (m.transition_fn <| origin := s; input := (states_to_transition_input m s s') |>).destination = s'
Proof
  rpt strip_tac
  >> simp[states_to_transition_input_def]
  >> Cases_on ‘(m.transition_fn <|origin := s; input := F|>).destination ≠ s'’ >> simp[]
  >> Cases_on ‘b’ >> gvs[]
QED

Theorem states_to_transition_input_transition_fn:
  ∀m b s.
    wfmachine m ∧
    s < m.num_states ⇒
    states_to_transition_input m s (m.transition_fn <| origin := s; input := b |>).destination = b
Proof
  rpt strip_tac
  >> Cases_on ‘b’ >> EVAL_TAC
  >> drule wfmachine_transition_fn_from_state_injective
  >> rpt strip_tac
  >> gvs[]
QED

Theorem states_to_transition_input_vd_encode_state_snoc:
  ∀m b bs.
    wfmachine m ⇒
    states_to_transition_input m (vd_encode_state m bs) (vd_encode_state m (SNOC b bs)) = b
Proof
  rpt strip_tac
  >> gvs[vd_encode_state_snoc]
  >> gvs[states_to_transition_input_transition_fn]
QED

Theorem path_to_code_singleton[simp]:
  ∀m s. path_to_code m [s] = []
Proof
  rpt strip_tac
  >> EVAL_TAC
QED

Theorem path_to_code_length[simp]:
  ∀m ps.
    LENGTH (path_to_code m ps) = LENGTH ps - 1
Proof
  rpt strip_tac
  >> Induct_on ‘ps’
  >- EVAL_TAC
  >> rpt strip_tac
  >> Cases_on ‘ps’
  >- EVAL_TAC
  >> gvs[path_to_code_def]
QED

Theorem path_to_code_append:
  ∀m ss ss'.
    ss ≠ [] ∧ ss' ≠ [] ⇒
    path_to_code m (ss ⧺ ss') = path_to_code m ss ⧺ (states_to_transition_input m (LAST ss) (HD ss')) :: (path_to_code m ss')
Proof
  gen_tac
  >> Induct_on ‘ss’ >> rpt strip_tac
  >- gvs[]
  >> Cases_on ‘ss’
  >- (gvs[]
      >> Cases_on ‘ss'’
      >- gvs[]
      >> gvs[path_to_code_def])
  >> gvs[path_to_code_def]
QED

Theorem path_to_code_snoc:
  ∀m s ss.
    ss ≠ [] ⇒
    path_to_code m (SNOC s ss) = SNOC (states_to_transition_input m (LAST ss) s) (path_to_code m ss)
Proof
  rpt strip_tac
  >> gvs[path_to_code_append]
QED

Theorem path_to_code_code_to_path:
  ∀m bs.
    wfmachine m ⇒
    path_to_code m (code_to_path m bs) = bs
Proof
  rpt strip_tac
  >> Induct_on ‘bs’ using SNOC_INDUCT
  >- EVAL_TAC
  >> rpt strip_tac
  >> gvs[]
  >> gvs[code_to_path_append]
  >> DEP_PURE_ONCE_REWRITE_TAC[path_to_code_append]
  >> gvs[]
  >> conj_tac
  >- (gvs[code_to_path_from_state_def])
  >> REVERSE conj_tac
  >- (gvs[code_to_path_from_state_def])
  >> gvs[code_to_path_def, vd_encode_state_def]
  >> gvs[code_to_path_from_state_def]
  >> gvs[code_to_path_from_state_last]
  >> DEP_PURE_ONCE_REWRITE_TAC[states_to_transition_input_transition_fn]
  >> gvs[]
  >> irule vd_encode_state_from_state_is_valid
  >> gvs[]
QED

Theorem is_reachable_zero_zero[simp]:
  ∀m.
    is_reachable m 0 0
Proof
  rpt strip_tac
  >> EVAL_TAC
  >> qexists ‘[]’
  >> EVAL_TAC
QED

Theorem not_is_reachable_nonzero_zero[simp]:
  ∀m s.
    s ≠ 0 ⇒
    ¬is_reachable m s 0
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
  ∀m s t b.
    is_reachable m s t ⇒ is_reachable m (m.transition_fn <| origin := s; input := b |>).destination (SUC t)
Proof
  rpt strip_tac
  >> gvs[is_reachable_def]
  >> qexists ‘SNOC (b) bs’
  >> gvs[]
  >> gvs[vd_encode_state_snoc]
QED

Theorem is_reachable_transition_fn_destination:
  ∀m r t.
    is_reachable m r.origin t ⇒ is_reachable m (m.transition_fn r).destination (SUC t)
Proof
  rpt strip_tac
  >> qspecl_then [‘m’, ‘r.origin’, ‘t’, ‘r.input’] assume_tac is_reachable_transition_fn
  >> gvs[]
QED

Theorem is_reachable_suc:
  ∀m s t.
    is_reachable m s (SUC t) ⇔ ∃s' b. is_reachable m s' t ∧ (m.transition_fn <| origin := s'; input := b |>).destination = s
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (disch_tac
      >> gvs[is_reachable_def]
      >> qexistsl [‘vd_encode_state m (FRONT bs)’, ‘LAST bs’]
      >> conj_tac
      >- (qexists ‘FRONT bs’
          >> gvs[]
          >> Cases_on ‘bs’ using SNOC_CASES >> gvs[])
      >> Cases_on ‘bs’ using SNOC_CASES
      >- gvs[]
      >> gvs[vd_encode_state_snoc])
  >> rpt strip_tac
  >> gvs[]
  >> irule is_reachable_transition_fn
  >> gvs[]
QED

Theorem is_reachable_suc_transition_fn_destination:
  ∀m s t.
    is_reachable m s (SUC t) ⇔ ∃r. is_reachable m r.origin t ∧ (m.transition_fn  r).destination = s
Proof
  rpt strip_tac
  >> gvs[]
  >> gvs[is_reachable_suc]
  >> EQ_TAC
  >- (rpt strip_tac
      >> qexists ‘<| origin := s'; input := b|>’
      >> gvs[])
  >> rpt strip_tac
  >> qexistsl [‘r.origin’, ‘r.input’]
  >> gvs[]
QED

Theorem vd_can_step_vd_step[simp]:
  ∀m b s.
    vd_can_step m s (m.transition_fn <| origin := s; input := b |>).destination
Proof
  rpt strip_tac
  >> gvs[vd_can_step_def]
  >> qexists ‘b’
  >> gvs[]
QED

Theorem path_is_connected_cons1:
  ∀m h t.
    path_is_connected m (h::t) ⇒
    path_is_connected m t
Proof
  rpt strip_tac
  >> Induct_on ‘t’ >> gvs[path_is_connected_def]
QED

Theorem path_is_connected_append1:
  ∀m p1 p2.
    path_is_connected m (p1 ⧺ p2) ⇒ path_is_connected m p1 ∧ path_is_connected m p2
Proof
  rpt strip_tac
  >- (Induct_on ‘p1’
      >- gvs[path_is_connected_def]
      >> rpt strip_tac
      >> Cases_on ‘p1’
      >- gvs[path_is_connected_def]
      >> gvs[path_is_connected_def])
  >> Induct_on ‘p1’
  >- gvs[]
  >> rpt strip_tac
  >> Cases_on ‘p1’ >> gvs[path_is_connected_def]
  >> Cases_on ‘p2’ >> gvs[path_is_connected_def]
QED

Theorem path_is_connected_snoc1:
  ∀m p ps.
    path_is_connected m (SNOC p ps) ⇒ path_is_connected m ps
Proof
  rpt strip_tac
  >> Induct_on ‘ps’
  >- gvs[path_is_connected_def]
  >> rpt strip_tac
  >> Cases_on ‘ps’ >> gvs[path_is_connected_def]
QED

(* -------------------------------------------------------------------------- *)
(* This proof contains a significant amount of repetition. Perhaps it could   *)
(* be automated?                                                              *)
(*                                                                            *)
(* TODO: What is path_is_connected_append1? Repetition?                       *)
(* -------------------------------------------------------------------------- *)
Theorem path_is_connected_append:
  ∀m p p' ps ps'.
    path_is_connected m (ps ⧺ [p; p'] ⧺ ps') ⇔
      path_is_connected m ps ∧
      path_is_connected m ps' ∧
      vd_can_step m p p' ∧
      (ps = [] ∨ vd_can_step m (LAST ps) p) ∧
      (ps' = [] ∨ vd_can_step m p' (HD ps'))
Proof
  rpt strip_tac
  >> Induct_on ‘ps’ >> gvs[path_is_connected_def]
  >- (gvs[]
      >> Induct_on ‘ps'’ >> gvs[path_is_connected_def]
      >> rpt strip_tac
      >> Cases_on ‘ps'’ >> gvs[path_is_connected_def]
      >> decide_tac)
  >> rpt strip_tac
  >> Cases_on ‘ps’
  >- (gvs[path_is_connected_def]
      >> Induct_on ‘ps'’ >> gvs[path_is_connected_def]
      >- decide_tac
      >> rpt strip_tac
      >> decide_tac
     )   
  >> Cases_on ‘ps'’ >> gvs[path_is_connected_def]
  >- (gvs[path_is_connected_def]
      >> decide_tac)
  >> gvs[path_is_connected_def]
  >> decide_tac
QED

Theorem path_is_connected_snoc:
  ∀m p p' ps.
    path_is_connected m (SNOC p' (SNOC p ps)) ⇔ vd_can_step m p p' ∧ path_is_connected m (SNOC p ps)
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (rpt strip_tac
      >- (gvs[]
          >> Induct_on ‘ps’
          >- (gvs[]
              >> gvs[path_is_connected_def])
          >> rpt strip_tac
          >> Cases_on ‘ps’ >> gvs[path_is_connected_def])
      >> irule path_is_connected_snoc1
      >> qexists ‘p'’
      >> gvs[])
  >> rpt strip_tac
  >> Induct_on ‘ps’
  >- gvs[path_is_connected_def]
  >> rpt strip_tac
  >> Cases_on ‘ps’ >> gvs[path_is_connected_def]
QED

Theorem path_is_connected_cons:
  ∀m p p' ps.
    path_is_connected m (p::p'::ps) ⇔ vd_can_step m p p' ∧ path_is_connected m (p'::ps)
Proof
  rpt strip_tac
  >> qspecl_then [‘m’, ‘p’, ‘p'’, ‘[]’, ‘ps’] assume_tac path_is_connected_append
  >> gvs[path_is_connected_def, vd_can_step_def]
QED

Theorem path_is_connected_code_to_path_from_state:
  ∀m bs s.
    path_is_connected m (code_to_path_from_state m bs s)
Proof
  Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[code_to_path_from_state_def]
  >> gvs[path_is_connected_cons1]
  >> pop_assum $ qspecl_then [‘m’, ‘(m.transition_fn <| origin := s; input := h |>).destination’] assume_tac
  >> qmatch_goalsub_abbrev_tac ‘(_::ps)’
  >> Cases_on ‘ps’
  >- gvs[]
  >> gvs[path_is_connected_cons]
  >> Cases_on ‘bs’ >> gvs[code_to_path_from_state_def]
QED

Theorem path_is_connected_code_to_path:
  ∀m bs s.
    path_is_connected m (code_to_path m bs)
Proof
  gvs[path_is_connected_code_to_path_from_state, code_to_path_def]
QED

Theorem path_is_valid_nonempty:
  ∀m ps.
    path_is_valid m ps ⇒ ps ≠ []
Proof
  rpt strip_tac
  >> gvs[path_is_valid_def]
QED

Theorem not_path_is_valid_empty[simp]:
  ∀m ps.
    ¬path_is_valid m []
Proof
  gvs[path_is_valid_def]
QED

Theorem path_is_valid_from_state_path_is_connected:
  ∀m ps s.
    path_is_valid_from_state m ps s ⇔ path_is_connected m ps ∧ ps ≠ [] ∧ HD ps = s
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (rpt strip_tac 
      >- (gvs[path_is_valid_from_state_def]
          >> gvs[path_is_connected_code_to_path_from_state])
      >- gvs[path_is_valid_from_state_def]
      >> gvs[path_is_valid_from_state_def]
      >> Cases_on ‘bs’ >> gvs[code_to_path_from_state_def])
  >> rpt strip_tac
  >> gvs[path_is_valid_from_state_def]
  >> Induct_on ‘ps’ using SNOC_INDUCT
  >- gvs[]
  >> rpt strip_tac
  >> Cases_on ‘ps’ using SNOC_CASES >> gvs[code_to_path_def, path_is_connected_def, path_is_valid_from_state_def]
  >- (qexists ‘[]’ >> gvs[code_to_path_from_state_def])
  >> gvs[path_is_connected_snoc]
  >> gs[vd_can_step_def]
  >> qexists ‘SNOC b bs’
  >> Cases_on ‘l’
  >- (gvs[path_is_connected_def]
      >> Cases_on ‘bs’
      >> gvs[code_to_path_from_state_def])
  >> gvs[]
  >> PURE_REWRITE_TAC[GSYM SNOC_APPEND]
  >> PURE_REWRITE_TAC[code_to_path_from_state_snoc]
  >> gvs[]
  >> AP_TERM_TAC
  >> qspecl_then [‘m’, ‘bs’, ‘h’] assume_tac code_to_path_from_state_last
  >> gvs[]
  >> pop_assum (fn th => PURE_REWRITE_TAC [GSYM th])
  >> gvs[LAST_DEF]
QED

Theorem path_is_valid_path_is_valid_from_state:
  ∀m ps.
    path_is_valid m ps ⇔ path_is_valid_from_state m ps 0
Proof
  rpt strip_tac
  >> gvs[path_is_valid_def, path_is_valid_from_state_def, code_to_path_def]
QED

Theorem path_is_valid_path_is_connected:
  ∀m ps.
    path_is_valid m ps ⇔ path_is_connected m ps ∧ ps ≠ [] ∧ HD ps = 0
Proof
  gvs[path_is_valid_path_is_valid_from_state, path_is_valid_from_state_path_is_connected]
QED

Theorem path_is_valid_snoc:
  ∀m p ps.
    path_is_valid m (SNOC p ps) ⇔ (SNOC p ps = [0]) ∨ (vd_can_step m (LAST ps) p ∧ path_is_valid m ps)
Proof
  rpt strip_tac
  >> gvs[path_is_valid_path_is_connected]
  >> Cases_on ‘ps’ >> gvs[]
  >- (Cases_on ‘p’ >> gvs[] >> EVAL_TAC)
  >> Cases_on ‘h = 0’ >> gvs[]
  >> Induct_on ‘t’ using SNOC_INDUCT >> gvs[]
  >- EVAL_TAC
  >> rpt strip_tac
  >> PURE_REWRITE_TAC[GSYM SNOC_CONS]
  >> gvs[path_is_connected_snoc]
QED

Theorem path_is_valid_cons:
  ∀m p ps.
    path_is_valid m (p::ps) ⇔ (p::ps = [0] ∨ (p = 0 ∧ vd_can_step m p (HD ps) ∧ path_is_connected m ps))
Proof
  rpt strip_tac
  >> gvs[path_is_valid_path_is_connected]
  >> Cases_on ‘ps’ >> gvs[]
  >- (Cases_on ‘p’ >> gvs[] >> EVAL_TAC)
  >> Cases_on ‘p = 0’ >> gvs[]
  >> Induct_on ‘t’ >> gvs[]
  >- EVAL_TAC
  >> rpt strip_tac
  >> gvs[path_is_connected_cons]
QED


Theorem is_reachable_is_valid[simp]:
  ∀m s t.
    wfmachine m ∧
    is_reachable m s t
    ⇒ s < m.num_states
Proof
  Induct_on ‘t’
  >- (rpt strip_tac
      >> gvs[is_reachable_def]
      >> gvs[vd_encode_state_def, vd_encode_state_from_state_def])
  >> rpt strip_tac
  >> gvs[is_reachable_def]
QED

Theorem path_is_valid_first_two_elements:
  ∀m h h' t.
    path_is_valid m (h::h'::t) ⇒ vd_can_step m h h'
Proof
  rpt strip_tac
  >> gvs[vd_can_step_def]
  >> gvs[path_is_valid_def]
  >> gvs[code_to_path_def]
  >> Cases_on ‘bs’
  >- gvs[code_to_path_from_state_def]
  >> gvs[code_to_path_from_state_def]
  >> Cases_on ‘t'’
  >- (gvs[code_to_path_from_state_def]
      >> qexists ‘h''’ >> gvs[])
  >> gvs[code_to_path_from_state_def]
  >> qexists ‘h''’ >> gvs[]
QED

Theorem path_is_valid_code_to_path:
  ∀m bs.
    path_is_valid m (code_to_path m bs)
Proof
  rpt strip_tac
  >> gvs[path_is_valid_path_is_connected]
  >> gvs[path_is_connected_code_to_path]
  >> Cases_on ‘bs’ >> EVAL_TAC
QED

Theorem path_is_valid_or_empty_code_to_path:
  ∀m bs.
    path_is_valid_or_empty m (code_to_path m bs)
Proof
  gvs[path_is_valid_or_empty_def, path_is_valid_code_to_path]
QED

Theorem code_to_path_from_state_path_to_code:
  ∀m ps.
    ps ≠ [] ∧
    path_is_connected m ps ⇒
    code_to_path_from_state m (path_to_code m ps) (HD ps) = ps
Proof
  rpt strip_tac
  >> Induct_on ‘ps’
  >- gvs[path_is_connected_def]
  >> rpt strip_tac
  >> Cases_on ‘ps’ >> gvs[]
  >- gvs[code_to_path_def, code_to_path_from_state_def]
  >> drule path_is_connected_cons1
  >> rpt strip_tac
  >> gvs[]        
  >> gvs[path_to_code_def]
  >> gvs[code_to_path_from_state_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[transition_fn_states_to_transition_input]
  >> gvs[]
  >> gvs[path_is_connected_def, vd_can_step_def]
  >> qexists ‘b’
  >> gvs[]
QED

Theorem code_to_path_path_to_code:
  ∀m ps.
    ps ≠ [] ∧
    HD ps = 0 ∧
    path_is_connected m ps ⇒
    code_to_path m (path_to_code m ps) = ps
Proof
  metis_tac[code_to_path_def, code_to_path_from_state_path_to_code]
QED

Theorem vd_encode_state_from_state_path_to_code:
  ∀m ps s.
    ps ≠ [] ∧
    HD ps = s ∧
    path_is_connected m ps ⇒
    vd_encode_state_from_state m (path_to_code m ps) s = LAST ps
Proof
  rpt strip_tac
  >> qspecl_then [‘m’, ‘ps’] assume_tac code_to_path_from_state_path_to_code
  >> Cases_on ‘ps’ >> gvs[]
  >> gvs[GSYM code_to_path_from_state_last]
  >> gvs[path_is_valid_path_is_connected]
QED

Theorem vd_encode_state_path_to_code:
  ∀m ps.
    ps ≠ [] ∧
    path_is_valid m ps ⇒
    vd_encode_state m (path_to_code m ps) = LAST ps
Proof
  rpt strip_tac 
  >> gvs[vd_encode_state_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[vd_encode_state_from_state_path_to_code]
  >> gvs[]
  >> gvs[path_is_valid_path_is_connected]
QED

Theorem vd_encode_state_from_state_empty[simp]:
  ∀m s.
    vd_encode_state_from_state m [] s = s
Proof
  rpt strip_tac
  >> gvs[vd_encode_state_from_state_def]
QED

Theorem vd_encode_state_empty[simp]:
  ∀m.
    vd_encode_state m [] = 0
Proof
  rpt strip_tac
  >> gvs[vd_encode_state_def]
QED

Theorem is_reachable_zero[simp]:
  ∀m s.
    is_reachable m s 0 ⇔ s = 0
Proof
  rpt strip_tac
  >> gvs[is_reachable_def]
QED

Theorem vd_encode_from_state_singleton[simp]:
  ∀m b s.
    vd_encode_from_state m [b] s = (m.transition_fn <| origin := s; input := b |>).output
Proof
  rpt strip_tac
  >> gvs[vd_encode_from_state_def]
QED

(* -------------------------------------------------------------------------- *)
(* Unit tests                                                                 *)
(* (It makes sense for tests to be at the end because then they won't slow    *)
(*  down computation when writing theories and modifying the file, but they   *)
(*  will be run once during holmake to ensure correctness of the final        *)
(*  combined binary)                                                          *)
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
                       case d.input of
                         T => (case d.origin of
                                 0 => <| destination := 1; output := [T; T] |>
                               | 1 => <| destination := 3; output := [F; F] |>
                               | 2 => <| destination := 1; output := [F; T] |>
                               | 3 => <| destination := 3; output := [T; F] |>
                              )
                       | F => (case d.origin of
                                 0 => <| destination := 0; output := [F; F] |>
                               | 1 => <| destination := 2; output := [T; T] |>
                               | 2 => <| destination := 0; output := [T; F] |>
                               | 3 => <| destination := 2; output :=  [F; T] |>
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
      >> Cases_on ‘r.input’ >> gvs[]
      >> Cases_on ‘r.origin’ >> gvs[]
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
  >- (rpt strip_tac
      >> gvs[example_state_machine_def]
      >> Cases_on ‘s’ >> gvs[]
      >> Cases_on ‘n’ >> gvs[]
      >> Cases_on ‘n'’ >> gvs[]
     )
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
  vd_encode example_state_machine [F; T; T; T; F] = [F; F; T; T; F; F; T; F; F; T]  
Proof
  EVAL_TAC
QED

Theorem transition_inverse_test:
  let
    test_inverse = transition_inverse example_state_machine 2;
  in
    LENGTH test_inverse = 2 ∧
    MEM (<| origin := 1; input := F |>) test_inverse ∧
    MEM (<| origin := 3; input := F |>) test_inverse
Proof
  EVAL_TAC
QED

val _ = export_theory();
