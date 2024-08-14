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

Datatype:
  transition_origin = <|
    origin : α;
    input : bool;
  |>
End

Datatype:
  transition_destination = <|
    destination : α;
    output : bool list;
  |> 
End

(* -------------------------------------------------------------------------- *)
(* A state machine consists of:                                               *)
(* - A set of states                                                          *)
(* - A function which takes a state and an input, and returns a new state and *)
(*   an output                                                                *)
(*                                                                            *)
(* We additionally have the assumption of binary input and output.            *)
(* -------------------------------------------------------------------------- *)
Datatype:
  state_machine = <|
    states : α set ;
    transition_fn : α transition_origin -> α transition_destination;
    init : α;
  |>
End

(* -------------------------------------------------------------------------- *)
(* Helper function that does the actual work to encode a binary string using  *)
(* convolutional coding, according to a chosen state machine.                 *)
(*                                                                            *)
(* This function additionally has a parameter to keep track of the current    *)
(* state that the state machine is in.                                        *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_code_encode_helper_def:
           convolutional_code_encode_helper [] _ _ = [] ∧
           convolutional_code_encode_helper (b::bs : bool list) (m : num state_machine) (s : num) =
           let
             d = m.transition_fn <| origin := s; input := b |>
           in
             d.output ⧺ convolutional_code_encode_helper bs m d.destination
End

(* -------------------------------------------------------------------------- *)
(* Encodes a binary string using convolutional coding, according to a chosen  *)
(* state machine                                                              *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_code_encode_def:
  convolutional_code_encode bs (m : num state_machine) = convolutional_code_encode_helper bs m m.init
End

Definition example_state_machine_def:
  example_state_machine = <|
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
  |> : num state_machine
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

Datatype:
  viterbi_node_datatype = <|
    num_errors : num option;
    prev_state : α option;
  |> 
End

(* -------------------------------------------------------------------------- *)
(* Viterbi trellis data                                                       *)
(*                                                                            *)
(* Function from time steps and states to number of errors on optimal path to *)
(* this point in the trellis and previous state on optimal path to this point *)
(* in the trellis                                                             *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_trellis_data_def:
  viterbi_trellis_data m bs s 0 = (if s = m.init then <| num_errors := SOME 0; prev_state := NONE |> else <| num_errors := NONE; prev_state := NONE |>) ∧
  viterbi_trellis_data m bs s (SUC t) =
  let
    best_origin = @o. ∀o2. (m.transition_fn o).output


                                              
                                              (previous_state, input) = @(r, b). FST m.transition_fn (r, b) = s ∧ ∀(r2, b2) FST()
                                                                                                                  in 
                                                                                                                    <| num_errors := prev_state := |>
                                                                                                                    

End

Datatype:
  viterbi_trellis_data = <|
    num_errors : num # α -> num option;
    optimal_prior_state : num # α -> α option;
  |>
End

(* -------------------------------------------------------------------------- *)
(* According to the Viterbi algorithm, the number of errors incurred at time  *)
(* step 0 is NONE except in the init state, and at every successive time      *)
(* step, it is the minimimum of the number of errors                          *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_trellis_def:
  
End




viterbi_trellis_data.num_errors (t + 1, s) = 

Definition vd_initial_trellis_data_def:
  vd_initial_trellis_data = <|
    num_errors := λ(t, s). NONE;
    optimal_prior_state := λ(t, s). NONE;
  |>
End

Definition vd_calculate_trellis_data_def:
  vd_calculate_trellis_data = <|
    num_errors
  |>
End


(* -------------------------------------------------------------------------- *)
(* Input: bitstring and state machine                                         *)
(* Output: Most likely original bitstring                                     *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_decode_def:
  viterbi_decode bs m =
  let
    data = vd_calculate_trellis_data
  in
    vd_calculate_trellis_path data
End

Theorem viterbi_correctness:
  ∀i cs noise M.
    cs = encode M i ⊕ noise ∧ LENGTH noise = LENGTH (encode M i)
    ⇒
    ∀bs'. LENGTH (encode M bs') = LENGTH cs ⇒
          cs ⊖ encode M (viterbi M cs) ≤ cs ⊖ encode M bs'
Proof

  ...
QED


val _ = export_theory();
