(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "convolutional_codes";

open arithmeticTheory;
open listTheory;

(* -------------------------------------------------------------------------- *)
(* Based on the MIT 6.02 DRAFT Lecture Notes Fall 2010                        *)
(*                                                                            *)
(* TODO: Cite better                                                          *)
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
(* CONVOLUTIONAL STATE MACHINE ENCODING                                       *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* A state machine consists of:                                               *)
(* - A set of states                                                          *)
(* - transitions between states. Each transition consists of:                 *)
(*   - an input that would cause that transition to be taken                  *)
(*   - a string that is output when that transition is taken                  *)
(*                                                                            *)
(* We additionally have the assumption of binary input and output.            *)
(* -------------------------------------------------------------------------- *)
(* In practice, the state machine is represented in terms of                  *)
(* - a number n representing the number of states.                            *)
(* - a list where each element corresponds to one of the n states, and is a   *)
(*   tuple with the following members:                                        *)
(*   - the transitioned-to state when 0 is provided as input to the current   *)
(*     state                                                                  *)
(*   - the output string when 0 is provided as input to the current state     *)
(*   - the transitioned-to state when 1 is provided as input to the current   *)
(*     state                                                                  *)
(*   - the output string when 1 is provided as input to the current state     *)
(*                                                                            *)
(* Thus, it has the type (num, (num, num, bool list, bool list) list)         *)
(* In Hol's notation: num # (num # bool list # num # bool list) list          *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Helper function that does the actual work to encode a binary string using  *)
(* convolutional coding, according to a chosen state machine.                 *)
(*                                                                            *)
(* This function additionally has a parameter to keep track of the current    *)
(* state that the state machine is in.                                        *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_code_encode_helper_def:
  convolutional_code_encode_helper [] _ _ = [] ∧
  convolutional_code_encode_helper (b::bs : bool list) (m : num # (num # bool list # num # bool list) list) (s : num) =
  let
    (t0, o0, t1, o1) = EL s (SND m)
  in
    if b then
      o1 ⧺ convolutional_code_encode_helper bs m t1
    else
      o0 ⧺ convolutional_code_encode_helper bs m t0
End

(* -------------------------------------------------------------------------- *)
(* Encodes a binary string using convolutional coding, according to a chosen  *)
(* state machine                                                              *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_code_encode_def:
  convolutional_code_encode bs m = convolutional_code_encode_helper bs m 0
End

(*Datatype:
  viterbi_state_machine = <|
    foo : num;
    bar : num
  |>
End*)

(* -------------------------------------------------------------------------- *)
(* A simple example of a state machine for convolutional coding               *)
(* -------------------------------------------------------------------------- *)
Definition example_state_machine_def:
  example_state_machine = (4,
                           [
                             (0, [F; F], 1, [T; T]);
                             (2, [T; T], 3, [F; F]);
                             (0, [T; F], 1, [F; T]);
                             (2, [F; T], 3, [T; F]);
                           ]
                          ) : num # (num # bool list # num # bool list) list
End

(* -------------------------------------------------------------------------- *)
(* Simple test to make sure the convolutional code is providing the output    *)
(* I would expect if I manually did the computation myself                    *)
(* -------------------------------------------------------------------------- *)
Theorem convolutional_encode_test1:
  convolutional_code_encode [F; T; T; T; F] example_state_machine = [F; F; T; T; F; F; T; F; F; T]  
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* VITERBI DECODING                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Viterbi data                                                               *)
(*                                                                            *)
(* List, where list index corresponds to time step.                           *)
(* Each element of list is itself a list where each index corresponds to a    *)
(*   state.                                                                   *)
(* Each element of this inner list contains the number of errors on the       *)
(*   current optimal path, followed by the state number of the previous state *)
(*   on the optimal path.                                                     *)
(*                                                                            *)
(* Type: ((num # num) list) list                                              *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* The number used to represent the distance it would take to reach an        *)
(* unreachable state. Effectively infnity, but infinity isn't a natural       *)
(* number.                                                                    *)
(* -------------------------------------------------------------------------- *)
Definition vd_unreachable_distance_def:
  vd_unreachable_distance = 999999999999999999
End

(* -------------------------------------------------------------------------- *)
(* Viterbi data for a state which is unreachable                              *)
(* -------------------------------------------------------------------------- *)
Definition vd_unreachable_def:
  vd_unreachable = (vd_unreachable_distance, 0)
End

(* -------------------------------------------------------------------------- *)
(* Viterbi data for n states which are all unreachable                        *)
(* -------------------------------------------------------------------------- *)
Definition vd_unreachable_list_def:
  vd_unreachable_list 0 = [] ∧
  vd_unreachable_list (SUC n) = vd_unreachable::(vd_unreachable_list n)
End

(* -------------------------------------------------------------------------- *)
(* Outputs the first row of (num errors, previous state) pairs                *)
(* -------------------------------------------------------------------------- *)
Definition vd_initial_data_def:
  vd_initial_data 0 = [] ∧
  vd_initial_data (SUC n) = (0,0)::(vd_unreachable_list n)
End



(* -------------------------------------------------------------------------- *)
(* Outputs the states that have a transition to a given state s in the state  *)
(* machine m                                                                  *)
(* -------------------------------------------------------------------------- *)
Definition vd_get_prior_states_def:
  vd_get_prior_states m s =
End

(* -------------------------------------------------------------------------- *)
(* Input:                                                                     *)
(* - convolutional code state machine                                         *)
(* - Entire row of Viterbi data in the current  timestep                      *)
(* - state number to calculate the Viterbi data for                           *)
(*                                                                            *)
(* Output:                                                                    *)
(* - Viterbi data for the given state number in the next timestep             *)
(* -------------------------------------------------------------------------- *)
Definition vd_get_next_row_state_data_def:
  vd_get_next_row_state_data m d s
  let
    (* the two previous states leading to s *)
    (t1, t2) = vd_get_prior_states m s
  in
    let
      (* number of errors when arriving at s via t1 *)
      e1 =
    in
      let
        (* number of errors when arriving at s via t2 *)
        e2 =
      in
        vd_get_next_row_state_data m d s = if
        e1 < e2
        then
          (e1, )
        else
          
End

(* -------------------------------------------------------------------------- *)
(* Helper function for function which outputs the next row of                 *)
(* (num errors, previous state) pairs, given the previous row of              *)
(* (num errors, previous state) pairs. This function additionally has a       *)
(* parameter which keeps track of the number of states for which the data     *)
(* still needs to be generated                                                *)
(* -------------------------------------------------------------------------- *)
Definition vd_get_next_data_helper_def:
  vd_get_next_data_helper m d 0 = [] ∧
  vd_get_next_data m d (SUC n) = (vd_get_next_row_state_data m d n)::(vd_get_next_data_helper m d n)
End

(* -------------------------------------------------------------------------- *)
(* Returns the number of states in a state machine                            *)
(* -------------------------------------------------------------------------- *)
Definition vd_state_machine_num_states_def:
  vd_state_machine_num_states m = FST m
End

(* -------------------------------------------------------------------------- *)
(* Outputs the next row of (num errors, previous state) pairs, given the      *)
(* previous row of (num errors, previous state) pairs                         *)
(* -------------------------------------------------------------------------- *)
Definition vd_get_next_data_def:
  vd_get_next_data m d = vd_get_next_data_helper m d (vd_state_machine_num_states m)
End

(* -------------------------------------------------------------------------- *)
(* Input: number of states                                                    *)
(*                                                                            *)
(* Output: Viterbi data for the 0th time step (i.e. first row of Viterbi data)*)
(* -------------------------------------------------------------------------- *)
Definition vd_initialise_viterbi_data_def:
  vd_initialise_viterbi_data 0 _ = [] ∧
  vd_initialise_viterbi_data (SUC n) (b : bool) = [()]::(vd_initialise_viterbi_data n)
End


(* 
Definition vd_calculate_viterbi_data_def:
  vd_calculate_viterbi_data =
  vd_loop_calculate_viterbi_data (vd_initialise_viterbi_data)
End*)






(* -------------------------------------------------------------------------- *)
(* Input: bitstring and state machine                                         *)
(* Output: Most likely original bitstring                                     *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_decode_def:
  viterbi_decode bs m =
  let
    d = vd_calculate_viterbi_data
  in
    vd_calculate_trellis_path p m
End



(* Produces a state machine with n states and 2n transitions given by its *)
Definition viterbi_state_machine_def:
  viterbi_state_machine (n : num) (ts : 

                                   ss ts = (states, transitions_on_0, transitions_on_1)


Definition encode_def:

Definition viterbi_state_def:
           viterbi_state

Definition viterbi_helper:
           vitebri_helper (l1 : bool list) (: state) = 

Definition viterbi_def:
           viterbi (l1 : bool list) =  



Theorem viterbi_cor



val _ = export_theory();
