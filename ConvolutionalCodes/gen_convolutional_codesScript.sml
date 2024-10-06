open HolKernel Parse boolLib bossLib;

val _ = new_theory "gen_convolutional_codes";


(* -------------------------------------------------------------------------- *)
(* The datatype used as the input of a transition in a state machine          *)
(* -------------------------------------------------------------------------- *)
Datatype:
  gen_transition = <|
    origin : α;
    input : bool;
  |>
End

(* -------------------------------------------------------------------------- *)
(* The datatype used as the output of a transition in a state machine         *)
(* -------------------------------------------------------------------------- *)
Datatype:
  gen_transition_destination = <|
    destination : α;
    output : bool list;
  |> 
End


(* -------------------------------------------------------------------------- *)
(* A state machine consists of:                                               *)
(* - A set of states                                                          *)
(* - A function which takes a state and an input bit, and returns a new state *)
(* and an output bitstring.                                                   *)
(* - An initial state                                                         *)
(*                                                                            *)
(* We additionally have the assumption of binary input and output.            *)
(* -------------------------------------------------------------------------- *)
Datatype:
  gen_state_machine = <|
    states : α set;
    transition_fn : α gen_transition -> α gen_transition_destination;
    init : α;
    output_length : num;
    state_ordering : α -> α -> bool;
  |>
End


(* -------------------------------------------------------------------------- *)
(* Ensure that the state machine is well-formed                               *)
(* -------------------------------------------------------------------------- *)
Definition gen_wfmachine_def:
  gen_wfmachine (m : α gen_state_machine) ⇔
    (* states:
       - must be finite *)
    FINITE m.states ∧
    (* transition_fn:
       - must take valid states to valid states *)
    (∀s i. s ∈ m.states ⇒ (m.transition_fn <| origin := s; input := i |>).destination ∈ m.states) ∧                                                             (* init:
       - must be a valid state *)
    m.init ∈ m.states ∧
    (* output_length:
       - each output given by transition_fn has the length of output_length *)
    (∀s i. s ∈ m.states ⇒ LENGTH (m.transition_fn <| origin := s; input := i |>).output = m.output_length) ∧
    (* state_ordering:
       - the ordering of the states must be well-founded. *)
    WF m.state_ordering
End


(* -------------------------------------------------------------------------- *)
(* Helper function that does the actual work to encode a binary string using  *)
(* convolutional coding, according to a chosen state machine.                 *)
(*                                                                            *)
(* This function additionally has a parameter to keep track of the current    *)
(* state that the state machine is in.                                        *)
(* -------------------------------------------------------------------------- *)
Definition gen_vd_encode_from_state_def:
  gen_vd_encode_from_state _ [] _ = [] ∧
  gen_vd_encode_from_state (m : α gen_state_machine) (b::bs : bool list) (s : α) =
  let
    d = m.transition_fn <| origin := s; input := b |>
  in
    d.output ⧺ gen_vd_encode_from_state m bs d.destination
End

(* -------------------------------------------------------------------------- *)
(* Encodes a binary string using convolutional coding, according to a chosen  *)
(* state machine                                                              *)
(* -------------------------------------------------------------------------- *)
Definition gen_vd_encode_def:
  gen_vd_encode (m : α gen_state_machine) bs = gen_vd_encode_from_state m bs m.init
End

(* -------------------------------------------------------------------------- *)
(* This state machine corresponds to the convolutional code which has a       *)
(* window size of 3, and creates two parity bits, the first of which is       *)
(* formed by adding together all inputs, and the second of which is formed    *)
(* by adding together the last 2 inputs.                                      *)
(* -------------------------------------------------------------------------- *)
Definition gen_example_state_machine_def:
  gen_example_state_machine = <|
    states := {0; 1; 2; 3};
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
    init := 0;
    output_length := 2;
    state_ordering := $<    
  |> : num gen_state_machine
End

(* -------------------------------------------------------------------------- *)
(* Simple test to make sure the convolutional code is providing the output    *)
(* I would expect if I manually did the computation myself                    *)
(* -------------------------------------------------------------------------- *)
Theorem gen_vd_encode_test1:
  gen_wfmachine gen_example_state_machine ∧
  gen_vd_encode gen_example_state_machine [F; T; T; T; F] = [F; F; T; T; F; F; T; F; F; T]  
Proof
  REVERSE CONJ_TAC
  >- EVAL_TAC
  >> gvs[gen_wfmachine_def]
  >> rpt conj_tac
  >- gvs[gen_example_state_machine_def]
  >- (rpt strip_tac >> gvs[gen_example_state_machine_def] >> Cases_on ‘i’ >> gvs[])
  >- gvs[gen_example_state_machine_def]
  >- (rpt strip_tac >> gvs[gen_example_state_machine_def] >> Cases_on ‘i’ >> gvs[])
  >- (gvs[gen_example_state_machine_def])
QED



val _ = export_theory();
