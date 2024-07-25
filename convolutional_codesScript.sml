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
(* -------------------------------------------------------------------------- *)

(* state machine type: num # (num # bool list # num # bool list) list *)

(*
   
   *)
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

(* Encodes a binary string using convolutional coding, according to a chosen
   state machine *)
Definition convolutional_code_encode_def:
  convolutional_code_encode bs m = convolutional_code_encode_helper bs m 0
End

(* *)
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

Theorem convolutional_encode_test1:
  convolutional_code_encode [F; T; T; T; F] example_state_machine = [F; F; T; T; F; F; T; F; F; T]  
Proof
  EVAL_TAC
QED

(* @@

Definition viterbi_decode_helper_def:
  viterbi_decode_helper bs m (e : (num list) list) (t : num) (s : num) = 
End*)

Definition vd_calculate_trellis_errors_def:
  vd_calculate_trellis_errors 
End

Definition vd_initialise_viterbi_data_def:
  vd_initialise_viterbi_data = ([], )
End

Definition vd_calculate_viterbi_data_def:
  vd_calculate_viterbi_data =
  vd_loop_calculate_viterbi_data (vd_initialise_viterbi_data)
End



(* -------------------------------------------------------------------------- *)
(* Viterbi data                                                               *)
(*                                                                            *)
(* List, where list index corresponds to time step.                           *)
(* Each element of list                                                       *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* Viter

         List of time rows. Each time row has list of stateEach state has prior *)
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
