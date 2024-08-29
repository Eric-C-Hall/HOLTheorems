(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "convolutional_codes";

open arithmeticTheory;
open listTheory;
open bitstringTheory;
open infnumTheory;

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


Definition add_noise_def:
  add_noise = bxor
End
val _ = set_mapped_fixity{fixity = Infixl 500, term_name = "add_noise",
tok = "⊕"}
         
Definition hamming_weight_def:
  hamming_weight [] = 0 ∧
  hamming_weight (b::bs) = (if b then 1 else 0) + hamming_weight bs
End

Definition hamming_distance_def:
  hamming_distance l1 l2 = hamming_weight (l1 ⊕ l2)
End

val _ = set_mapped_fixity{fixity = Infixl 500, term_name = "hamming_distance",
tok = "⊖"};

Theorem add_noise_test:
  [F; T; T; F; T; F; F] ⊕ [T; T; F; F; T; T; F] = [T; F; T; F; F; T; F]
Proof
  EVAL_TAC  
QED

Theorem hamming_distance_test:
  [F; T; T; F; T; F; F] ⊖ [T; T; F; F; T; T; F] = 3
Proof
  EVAL_TAC
QED

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
    output_length : num;
  |>
End

Definition wfmachine_def:
  wfmachine (m : α state_machine) ⇔
    m.init ∈ m.states ∧
    ∀s. s ∈ m.states ⇒
        ∀b. LENGTH (m.transition_fn <| origin := s; input := b |>).output = m.output_length
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
  convolutional_code_encode_helper (b::bs : bool list) (m : α state_machine) (s : α) =
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
  convolutional_code_encode bs (m : α state_machine) = convolutional_code_encode_helper bs m m.init
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
    num_errors : infnum;
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
val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

(* -------------------------------------------------------------------------- *)
(* Describes the data stored at a particular point in the trellis             *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire input bitstring                                             *)
(* s: the state associated with this node in the trellis                      *)
(* t: the time step associated with this node in the trellis                  *)
(*                                                                            *)
(* Outputs a tuple containing the number of errors at this point as well as   *)
(* the previous state on the optimal path towards this point                  *)
(*                                                                            *)
(* relevant_input denotes the input to the Viterbi algorithm which corresponds*)
(* to the current step in the trellis                                         *)
(*                                                                            *)
(* get_num_errors is a helper sub-function which takes a point in the         *)
(*                                                                            *)
(* origin_leads_to_s is a helper sub-function which returns whether or not a  *)
(* (state, input) pair will lead us to the state s in our state machine m.    *)
(*                                                                            *)
(* best_origin is the choice of previous state and input which minimizes the  *)
(* number of errors when transitioning to the current state and time.         *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_trellis_data_def:
  viterbi_trellis_data m bs s 0 : α viterbi_node_datatype =
  (if s = m.init then
     <| num_errors := N0; prev_state := NONE |>
   else <| num_errors := INFINITY; prev_state := NONE |>) ∧
  viterbi_trellis_data m bs s (SUC t) : α viterbi_node_datatype =
  let
    relevant_input = TAKE m.output_length (DROP (t * m.output_length) bs) ;
    get_num_errors = λr. (viterbi_trellis_data m bs r.origin t).num_errors +
                         N ((m.transition_fn r).output ⊖ relevant_input) ;
    origin_leads_to_s = λr. ((m.transition_fn r).destination = s);
    best_origin =  @r. origin_leads_to_s r ∧
                       ∀r2. origin_leads_to_s r2 ⇒
                            get_num_errors r ≤ get_num_errors r2 ;
  in
    <| num_errors := get_num_errors best_origin;
       prev_state := SOME best_origin.origin |>
End

(* -------------------------------------------------------------------------- *)
(* Returns the optimal path going from back to front.                         *)
(*                                                                            *)
(* Returns the path as a list of all states encountered along the path,       *)
(* including the very first and last states, with the first element of this   *)
(* list being the last state encountered in the path, and the last element of *)
(* this list being the first state encountered in the path.                   *)
(*                                                                            *)
(* vd stands for Viterbi Decode                                               *)
(* -------------------------------------------------------------------------- *)
Definition vd_find_optimal_reversed_path_def:
  vd_find_optimal_reversed_path m bs s 0 : α list = [s] ∧
  vd_find_optimal_reversed_path m bs s (SUC t) : α list =
  let
    trellis_data = viterbi_trellis_data m bs s (SUC t);
    s2 = THE trellis_data.prev_state;
  in
    s :: (vd_find_optimal_reversed_path m bs s2 t)
End

(* -------------------------------------------------------------------------- *)
(* See comment for vd_find_optimal_reversed_path                              *)
(*                                                                            *)
(* Reverses the path returned by that function to ensure the path is returned *)
(* in the forwards direction                                                  *)
(* -------------------------------------------------------------------------- *)
Definition vd_find_optimal_path_def:
  vd_find_optimal_path m bs s t = REVERSE (vd_find_optimal_reversed_path m bs s t)
End

(* -------------------------------------------------------------------------- *)
(* An unknown, valid state, used for testing purposes                         *)
(* -------------------------------------------------------------------------- *)
Definition test_state_def:
  test_state : α = @s. T
End

(* -------------------------------------------------------------------------- *)
(* An arbitrary, valid transition_origin, used for testing purposes           *)
(* -------------------------------------------------------------------------- *)
Definition test_transition_origin_def:
  test_transition_origin : α transition_origin = <| origin := test_state; input := F |>
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
  path_to_code m (p1::p2::ps) = () :: (path_to_code m (p2::ps))
End

(* -------------------------------------------------------------------------- *)
(* Input: bitstring and state machine                                         *)
(* Output: Most likely original bitstring                                     *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_decode_def:
  viterbi_decode m bs =
  let
    max_timestep = (LENGTH bs) DIV m.output_length;
    last_state = @s. ∀s2. (viterbi_trellis_data m bs s max_timestep).num_errors ≤ (viterbi_trellis_data m bs s2 timestep);
    
  in
    REVERSE 
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
