open HolKernel Parse boolLib bossLib;

val _ = new_theory "state_machine";

open arithmeticTheory;
open listTheory;
open pred_setTheory;

(* -------------------------------------------------------------------------- *)
(* This theory contains the definition of the state machine used in my proofs *)
(* of the correctness of convolutional codes.                                 *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* CONVOLUTIONAL STATE MACHINE ENCODING                                       *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* TODO: rename this as transition. It's better to think of this as a         *)
(* transition, because the transition origin is exclusively the state and not *)
(* the provided input. Then the transition function will take a transition    *)(* and return the destination state and output.                               *)
(* -------------------------------------------------------------------------- *)
Datatype:
  transition_origin = <|
    (* possibly rename this, because t.origin sounds like you're finding the
       origin of the origin, rather than finding the state that comprises the
       origin. Maybe call it state, or something. *)
    origin : num;
    input : bool;
  |>
End

(* -------------------------------------------------------------------------- *)
(* The automatically generated record theorems don't seem to be automatically *)
(* fetched or something, so I have to fetch them manually.                    *)
(* -------------------------------------------------------------------------- *)
val transition_origin_component_equality_local = fetch "state_machine" "transition_origin_component_equality";

Theorem transition_origin_literal_components[simp]:
  ∀r.
  <| origin := r.origin; input := r.input |> = r
Proof
  rpt strip_tac
  >> gvs[transition_origin_component_equality_local]
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
    transition_fn : transition_origin -> transition_destination;
    output_length : num;
  |>
End

(* -------------------------------------------------------------------------- *)
(* Takes a step using the state machine and returns a record of the           *)
(* destination and the output                                                 *)
(* -------------------------------------------------------------------------- *)
Definition vd_step_record_def:
  vd_step_record (m : state_machine) b s =
  m.transition_fn <| origin := s; input := b |>
End

(* -------------------------------------------------------------------------- *)
(* Takes a step using the state machine and returns the output.               *)
(* -------------------------------------------------------------------------- *)
Definition vd_step_output_def:
  vd_step_output (m : state_machine) b s =
  (vd_step_record m b s).output
End

(* -------------------------------------------------------------------------- *)
(* Takes a step using the state machine to arrive at a new state.             *)
(* -------------------------------------------------------------------------- *)
Definition vd_step_def:
  vd_step (m : state_machine) b s =
  (vd_step_record m b s).destination
End

(* -------------------------------------------------------------------------- *)
(* Takes a step using the state machine, taking a transition as input.        *)
(* -------------------------------------------------------------------------- *)
Definition vd_step_tran_def:
  vd_step_tran m r =
  vd_step m r.input r.origin
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
    (∀n b. n < m.num_states ⇒ vd_step m b n < m.num_states) ∧
    (∀s. s < m.num_states ⇒ (∃s' b. s' < m.num_states ∧ vd_step m b s' = s)) ∧
    (∀s. s < m.num_states ⇒ vd_step m T s ≠ vd_step m F s) ∧
    (* output_length:
       - each transition must output a string of length output_length
       - output_length must be greater than 0*)
    (∀n b. n < m.num_states ⇒ LENGTH (m.transition_fn <| origin := n; input := b |>).output = m.output_length) ∧
    0 < m.output_length
End

(* -------------------------------------------------------------------------- *)
(* Automatically apply commonly used property of a well-formed machine        *)
(* -------------------------------------------------------------------------- *)
Theorem wfmachine_zero_is_valid[simp]:
  ∀m.
  wfmachine m ⇒ 0 < m.num_states
Proof
  PURE_REWRITE_TAC[wfmachine_def]
  >> rpt strip_tac
QED

(* -------------------------------------------------------------------------- *)
(* Extract the property of a wfmachine that says that taking a step from a    *)
(* valid state will result in a valid state.                                  *)
(* -------------------------------------------------------------------------- *)
Theorem wfmachine_vd_step_is_valid:
  ∀m.
  wfmachine m ⇒
  (∀n b. n < m.num_states ⇒ vd_step m b n < m.num_states)
Proof
  PURE_REWRITE_TAC[wfmachine_def]
  >> rpt strip_tac
QED

(* -------------------------------------------------------------------------- *)
(* Extract the property of a wfmachine that says that every state has a prior *)
(* state, i.e. one from which it is possible to take a step to arrive at the  *)
(* state.                                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem wfmachine_every_state_has_prior_state:
  ∀m.
  wfmachine m ⇒
  (∀s. s < m.num_states ⇒ (∃s' b. s' < m.num_states ∧ vd_step m b s' = s))
Proof
  PURE_REWRITE_TAC[wfmachine_def]
  >> rpt strip_tac  
QED

(* -------------------------------------------------------------------------- *)
(* Extract the property of a wfmachine that says that the two transitions     *)
(* leading from a state do not arrive at the same state.                      *)
(* -------------------------------------------------------------------------- *)
Theorem wfmachine_transition_fn_from_state_injective:
  ∀m.
  wfmachine m ⇒
  (∀s. s < m.num_states ⇒ vd_step m T s ≠ vd_step m F s)
Proof
  PURE_REWRITE_TAC[wfmachine_def]
  >> rpt strip_tac
QED

(* -------------------------------------------------------------------------- *)
(* Extract the property of a wfmachine that says that all transition outputs  *)
(* have the same length as the output length of the wfmachine.                *)
(* -------------------------------------------------------------------------- *)
Theorem wfmachine_transition_fn_output_length:
  ∀m.
  wfmachine m ⇒
  (∀n b. n < m.num_states ⇒ LENGTH (m.transition_fn <| origin := n; input := b |>).output = m.output_length)
Proof
  PURE_REWRITE_TAC[wfmachine_def]
  >> rpt strip_tac
QED

(* -------------------------------------------------------------------------- *)
(* Extract the property of a well-formed machine which says that the output   *)
(* length must be greater than zero                                           *)
(* -------------------------------------------------------------------------- *)
Theorem wfmachine_output_length_greater_than_zero:
  ∀m.
  wfmachine m ⇒
  0 < m.output_length
Proof
  PURE_REWRITE_TAC[wfmachine_def]
  >> rpt strip_tac
QED

(* -------------------------------------------------------------------------- *)
(* Helper function that does the actual work to encode a binary string using  *)
(* convolutional coding, according to a chosen state machine.                 *)
(*                                                                            *)
(* This function additionally has a parameter to keep track of the current    *)
(* state that the state machine is in.                                        *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_helper_def:
  vd_encode_helper _ [] _ = [] ∧
  vd_encode_helper (m : state_machine) (b::bs : bool list) (s : num) =
  let
    d = vd_step_record m b s
  in
    d.output ⧺ vd_encode_helper m bs d.destination
End

(* -------------------------------------------------------------------------- *)
(* Encodes a binary string using convolutional coding, according to a chosen  *)
(* state machine                                                              *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_def:
  vd_encode (m : state_machine) bs = vd_encode_helper m bs 0
End

(* -------------------------------------------------------------------------- *)
(* Helper function to calculate the final state you'll end up in if you apply *)
(* the given state machine to the given bitstring. Also has a variable to     *)
(* keep track of the current state we're in.                                  *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_state_helper_def:
  vd_encode_state_helper (m : state_machine) [] s = s ∧
  vd_encode_state_helper m (b::bs) s =
  vd_encode_state_helper m bs (vd_step m b s)
End 

(* -------------------------------------------------------------------------- *)
(* Calculates the final state you'll end up in if you apply the given state   *)
(* machine to the given bitstring.                                            *)
(* -------------------------------------------------------------------------- *)
Definition vd_encode_state_def:
  vd_encode_state (m : state_machine) bs = vd_encode_state_helper m bs 0
End

(* -------------------------------------------------------------------------- *)
(* Returns true if it is possible to reach the state s at time t when         *)
(* starting at 0.                                                             *)
(* -------------------------------------------------------------------------- *)
Definition is_reachable_def:
  is_reachable m s t = ∃bs. (LENGTH bs = t ∧ vd_encode_state m bs = s)
End

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

(* -------------------------------------------------------------------------- *)
(* An example message which may have been recieved.                           *)
(*                                                                            *)
(* Length: 12                                                                 *)
(* Decoded length: 6 (if using example_state_machine)                         *)
(* -------------------------------------------------------------------------- *)
Definition test_path_def:
  test_path = [F; T; T; F; T; T; T; T; F; F; T; F]
End

Theorem wfmachine_example_state_machine:
  wfmachine example_state_machine
Proof
  PURE_REWRITE_TAC[wfmachine_def]
  >> rpt conj_tac
  >- EVAL_TAC
  >- (gvs[example_state_machine_def, vd_step_def, vd_step_record_def]
      >> rpt strip_tac
      >> Cases_on ‘b’ >> gvs[]
      >> Cases_on ‘n’ >> gvs[]
      >> Cases_on ‘n'’ >> gvs[]
      >> Cases_on ‘n’ >> gvs[])
  >- (gvs[example_state_machine_def, vd_step_def, vd_step_record_def]
      >> rpt strip_tac
      >> Cases_on ‘s’
      >- (qexistsl [‘0’, ‘F’]
          >> EVAL_TAC)
      >> Cases_on ‘n’
      >- (qexistsl [‘0’, ‘T’]
          >> EVAL_TAC)
      >> Cases_on ‘n'’
      >- (qexistsl [‘1’, ‘F’]
          >> EVAL_TAC)
      >> Cases_on ‘n’
      >- (qexistsl [‘1’, ‘T’]
          >> EVAL_TAC)
      >> EVAL_TAC
      >> gvs[ADD1])
  >- (rpt strip_tac
      >> gvs[example_state_machine_def, vd_step_def, vd_step_record_def]
      >> Cases_on ‘s’ >> gvs[]
      >> Cases_on ‘n’ >> gvs[]
      >> Cases_on ‘n'’ >> gvs[])
  >- (rpt strip_tac
      >> gvs[example_state_machine_def, vd_step_def, vd_step_record_def]
      >> Cases_on ‘b’ >> gvs[]
      >> Cases_on ‘n’ >> gvs[]
      >> Cases_on ‘n'’ >> gvs[]
      >> Cases_on ‘n’ >> gvs[])
  >- (gvs[example_state_machine_def])
QED

(* -------------------------------------------------------------------------- *)
(* Simple test to make sure the convolutional code is providing the output    *)
(* I would expect if I manually did the computation myself                    *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_test1:
  vd_encode example_state_machine [F; T; T; T; F] = [F; F; T; T; F; F; T; F; F; T]  
Proof
  EVAL_TAC
QED

(* Originally used the following definition, but this led to issues:
  all_transitions_helper (m : state_machine) (b : bool) = GENLIST (λn. <| origin := n; input := b |>) m.num_states
 *)


Definition all_transitions_helper_def:
  all_transitions_helper (m : state_machine) (b : bool) = GENLIST (λn. <| origin := n; input := b |>) m.num_states
End

Theorem all_transitions_helper_mem_is_valid[simp]:
  ∀m b r.
  MEM r (all_transitions_helper m b) ⇒ r.origin < m.num_states
Proof
  rpt strip_tac
  >> gvs[all_transitions_helper_def]
  >> gvs[MEM_GENLIST]
QED

(* -------------------------------------------------------------------------- *)
(* Returns a list of all valid choices of a transition_origin             *)
(* -------------------------------------------------------------------------- *)
Definition all_transitions_def:
  all_transitions (m : state_machine) = all_transitions_helper m T ⧺ all_transitions_helper m F
End

Theorem all_transitions_mem_is_valid[simp]:
  ∀m r.
  MEM r (all_transitions m) ⇒ r.origin < m.num_states
Proof
  rpt strip_tac
  >> gvs[all_transitions_def]
  >> metis_tac[all_transitions_helper_mem_is_valid]
QED

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

(*Theorem all_transitions_test:
  all_transitions example_state_machine = faz
Proof
  EVAL_TAC
End*)

(* -------------------------------------------------------------------------- *)
(* Returns a list of transitions that lead to the given state, as well as the *)
(* input which leads to them. Each element of the list is a                   *)
(* transition_origin                                                          *)
(* -------------------------------------------------------------------------- *)
Definition transition_inverse_def:
  transition_inverse (m : state_machine) dest =
  FILTER (λorgn. (m.transition_fn orgn).destination = dest) (all_transitions m)
End

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
    vd_step_tran m r = s ∧ MEM r (all_transitions m)
Proof
  rpt strip_tac
  >> gvs[transition_inverse_def]
  >> gvs[MEM_FILTER]
  >> gvs[vd_step_tran_def, vd_step_def, vd_step_record_def]
QED

Theorem transition_inverse_mem_forward[simp]:
  ∀m s r.
  MEM r (transition_inverse m s) ⇒
  vd_step_tran m r = s
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
  >> gvs[transition_origin_component_equality_local]
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
  >> gvs[vd_step_def, vd_step_record_def]
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

(*Theorem transition_inverse_test:
  transition_inverse example_state_machine 2 = ARB
Proof
  EVAL_TAC
End*)

val _ = export_theory();
