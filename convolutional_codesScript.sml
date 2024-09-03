(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "convolutional_codes";

open arithmeticTheory;
open listTheory;
open bitstringTheory;
open infnumTheory;
open relationTheory;

open dep_rewrite;
(*open "donotexpandScript.sml"*)

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

(* -------------------------------------------------------------------------- *)
(* Is it really a good idea to assign ⊕ to add_noise instead of to bxor?     *)
(* -------------------------------------------------------------------------- *)
val _ = set_mapped_fixity{fixity = Infixl 500, term_name = "add_noise",
tok = "⊕"}
         
Definition hamming_weight_def:
  hamming_weight [] = 0 ∧
  hamming_weight (b::bs) = (if b then 1 else 0) + hamming_weight bs
End

Definition hamming_distance_def:
  hamming_distance l1 l2 = hamming_weight (l1 ⊕ l2)
End

(*val _ = set_mapped_fixity{fixity = Infixl 500, term_name = "hamming_distance",
 tok = "⊖"};*)

Theorem add_noise_test:
  [F; T; T; F; T; F; F] ⊕ [T; T; F; F; T; T; F] = [T; F; T; F; F; T; F] ∧
  [F; F; F; F; F; F; F] ⊕ [T; F; F; T; T; F; F] = [T; F; F; T; T; F; F] ∧
  [T; T; T; T; F; F; F] ⊕ [F; F; F; T; T; T; T] = [T; T; T; F; T; T; T]
Proof
  EVAL_TAC  
QED

Theorem hamming_weight_test:
  hamming_weight [F; T; F; F; F; F; F; F; F; T; T; F; F; F; F; T] = 4 ∧
  hamming_weight [] = 0 ∧
  hamming_weight [T; T; T] = 3 ∧
  hamming_weight [F; T; F; T] = 2
Proof
  EVAL_TAC
QED

Theorem hamming_distance_test:
  hamming_distance [F; T; T; F; T; F; F] [T; T; F; F; T; T; F] = 3 ∧
  hamming_distance [F; F; F] [T; T; T] = 3 ∧
  hamming_distance [F; T; F; T; F] [F; T; F; T; F] = 0
Proof
  EVAL_TAC
QED

Theorem MAX_SUC:
  ∀n m. MAX (SUC n) (SUC m) = SUC (MAX n m)
Proof
  rpt strip_tac
  >> gvs[MAX_DEF]
QED

Theorem bitwise_cons:
  ∀f b bs c cs.
    LENGTH bs = LENGTH cs ⇒
    bitwise f (b::bs) (c::cs) = (f b c)::(bitwise f bs cs)
Proof
  rpt strip_tac
  >> gvs[bitwise_def]
QED

Theorem bxor_cons:
  ∀b bs c cs.
    LENGTH bs = LENGTH cs ⇒
    bxor (b::bs) (c::cs) = (b ⇎ c) :: bxor bs cs
Proof
  rpt strip_tac
  >> gvs[bxor_def]
  >> gvs[bitwise_cons]
QED

Theorem hamming_distance_self[simp]:
  ∀bs. hamming_distance bs bs = 0
Proof
  rpt strip_tac
  >> gvs[hamming_distance_def, add_noise_def]
  >> Induct_on ‘bs’
  >- EVAL_TAC
  >> rpt strip_tac
  >> DEP_PURE_ONCE_REWRITE_TAC[bxor_cons]
  >> gvs[]
  >> gvs[hamming_weight_def]
QED

(*
(* Note: reverse_assum_list doens't work, it maintains the order*)
val reverse_assum_list = pop_assum (fn th => (TRY reverse_assum_list; assume_tac th))

val bury_assumption = pop_assum (fn th => reverse_assum_list >> assume_tac th >> reverse_assum_list)*)

Theorem bitwise_commutative:
  ∀f bs cs.
    (∀b c. f b c = f c b) ⇒
    bitwise f bs cs = bitwise f cs bs
Proof
  rpt strip_tac
  >> gvs[bitwise_def]
  >> gvs[SPECL [“LENGTH bs”, “LENGTH cs”] MAX_COMM]
  >> qmatch_goalsub_abbrev_tac `ZIP (bs', cs')`
  >> sg ‘LENGTH bs' = LENGTH cs'’
  >- (unabbrev_all_tac
      >> gvs[])
  >> pop_assum mp_tac
  >> NTAC 2 (pop_assum kall_tac)
  >> SPEC_TAC (“cs' : bool list”, “cs' : bool list”)
  >> Induct_on ‘bs'’ >> rpt strip_tac >> gvs[]
  >> Cases_on ‘cs'’ >> gvs[]
  >> first_x_assum $ qspec_then ‘t’ assume_tac
  >> gvs[]
QED

Theorem bxor_commutative:
  ∀bs cs. bxor bs cs = bxor cs bs
Proof
  rpt strip_tac
  >> gvs[bxor_def]
  >> DEP_PURE_ONCE_REWRITE_TAC [bitwise_commutative]
  >> gvs[]
  >> rpt Cases >> gvs[]
QED

Theorem add_noise_commutative:
  ∀bs cs : bool list. bs ⊕ cs = cs ⊕ bs
Proof
  rpt strip_tac
  >> gvs[add_noise_def]
  >> gvs[bxor_commutative]
QED

Theorem hamming_distance_symmetric:
  ∀bs cs. hamming_distance bs cs = hamming_distance cs bs
Proof
  rpt strip_tac
  >> gvs[hamming_distance_def]
  >> gvs[add_noise_commutative]
QED

(*Theorem hamming_distance_triangle_inequality:
  ∀bs cs ds. hamming_distance bs ds ≤ hamming_distance bs cs + hamming_distance cs ds
Proof
  rpt strip_tac
QED*)



(* -------------------------------------------------------------------------- *)
(* CONVOLUTIONAL PARITY EQUATION ENCODING                                     *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* A parity equation is represented as a bit-string of which bits in the      *)
(* window are included in the linear expression.                              *)
(*                                                                            *)
(* A parity equation can be equivalently represented as the same equation     *)
(* with an arbitary number of zeros after it, so any parity equation can be   *)
(* treated as a parity equation of longer length. Therefore, in situations    *)
(* where we are provided with multiple equations of different lengths, pad    *)
(* the shorter parity equations with F's at the end.                          *)
(* -------------------------------------------------------------------------- *)
Datatype:
  (* Placeholder while waiting for better parity equation definition *)
  parity_equation = <| temp_p : bool list; |>;
  
  (* Why doesn't the following work: *)
  (* parity_equation = bool list; *)
  (* parity_equation = (min$bool list$list); *)
  (* parity_equation = “:bool list”; *)
  (* parity_equation = “(:bool list)”; *)
  (* parity_equation = (“:min$bool list$list”); *)
End

(* type_of “a : bool list” *)

(* -------------------------------------------------------------------------- *)
(* Returns the length of a parity equation                                    *)
(* -------------------------------------------------------------------------- *)
Definition parity_equation_length_def:
  parity_equation_length p = LENGTH p.temp_p
End

(* -------------------------------------------------------------------------- *)
(* Returns the maximum length of a set of parity equations                    *)
(* -------------------------------------------------------------------------- *)
Definition parity_equations_max_length_def:
  parity_equations_max_length [] = 0 ∧
  parity_equations_max_length (p::ps) = MAX (parity_equation_length p) (parity_equations_max_length ps)
End

(* -------------------------------------------------------------------------- *)
(* Treats a bitstring as a parity equation, and applies it to a bitstring     *)
(* with a sufficiently large window length                                    *)
(*                                                                            *)
(* p::ps represents the bitstring that is being treated as a parity equation. *)
(* bs represents the bitstring that the parity equation is applied to.        *)
(* -------------------------------------------------------------------------- *)
Definition apply_bitstring_as_parity_equation_def:
  apply_bitstring_as_parity_equation [] bs = F ∧
  apply_bitstring_as_parity_equation (p::ps) (b::bs) = ((p ⇎ b) ⇎ (apply_bitstring_as_parity_equation ps bs))
End

(* -------------------------------------------------------------------------- *)
(* Applies a single parity equation to a bitstring with a sufficiently large  *)
(* window length                                                              *)
(* -------------------------------------------------------------------------- *)
Definition apply_parity_equation_def:
  apply_parity_equation p bs = apply_bitstring_as_parity_equation p.temp_p bs
End

(* -------------------------------------------------------------------------- *)
(* Applies a bunch of parity equations to a bitstring with a sufficiently     *)
(* large window length                                                        *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_parity_encode_step_def:
  convolutional_parity_encode_step [] bs = [] ∧
  convolutional_parity_encode_step (p::ps) bs = (apply_parity_equation p bs)::(convolutional_parity_encode_step ps bs)
End

(* -------------------------------------------------------------------------- *)
(* Takes a number of parity equations and a bitstring, and encodes the        *)
(* bitstring according to the parity equations                                *)
(* -------------------------------------------------------------------------- *)
(*Definition convolutional_parity_encode_def:
  convolutional_parity_encode ps bs =
  let
    window_length = parity_equations_max_length ps;
  in
    if LENGTH bs < window_length then [] else
      let
        first_window = TAKE window_length bs;
        step_values = convolutional_parity_encode_step ps first_window;
        remaining_bitstring = DROP 1 bs;
        remaining_values = convolutional_parity_encode ps remaining_bitstring;
      in
        step_values ⧺ remaining_values
Termination
  qexists ‘λ(_, bs) (_, cs). LENGTH bs < LENGTH cs’
  >> gvs[]
  >> CONJ_TAC
  >- (WF_LESS
      gvs[WF_DEF]
      >> rpt strip_tac
      >> CCONTR_TAC
      >> gvs[]
      >> first_assum $ qspec_then ‘w’ assume_tac
      >> gvs[]
      >> Cases_on ‘B w’
      End

Theorem test_convolutional_parity_encode:

Proof
QED*)


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
    states : α set;
    transition_fn : α transition_origin -> α transition_destination;
    init : α;
    output_length : num;
    num_states : num;
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
  convolutional_code_encode_helper _ [] _ = [] ∧
  convolutional_code_encode_helper (m : α state_machine) (b::bs : bool list) (s : α) =
  let
    d = m.transition_fn <| origin := s; input := b |>
  in
    d.output ⧺ convolutional_code_encode_helper m bs d.destination
End

(* -------------------------------------------------------------------------- *)
(* Encodes a binary string using convolutional coding, according to a chosen  *)
(* state machine                                                              *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_code_encode_def:
  convolutional_code_encode (m : α state_machine) bs = convolutional_code_encode_helper m bs m.init
End

(* -------------------------------------------------------------------------- *)
(* This state machine corresponds to the convolutional code which has a       *)
(* window size of 3, and creates two parity bits, the first of which is       *)
(* formed by adding together all inputs, and the second of which is formed    *)
(* by adding together the last 2 inputs.                                      *)
(* -------------------------------------------------------------------------- *)
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
  convolutional_code_encode example_state_machine [F; T; T; T; F] = [F; F; T; T; F; F; T; F; F; T]  
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
    relevant_input = TAKE m.output_length (DROP (t * m.output_length) bs);
    get_num_errors = λr. (viterbi_trellis_data m bs r.origin t).num_errors +
                         N (hamming_distance (m.transition_fn r).output relevant_input);
    origin_leads_to_s = λr. ((m.transition_fn r).destination = s);
    best_origin = @r. origin_leads_to_s r ∧
                      ∀r2. origin_leads_to_s r2 ⇒
                           get_num_errors r ≤ get_num_errors r2;
  in
    <| num_errors := get_num_errors best_origin;
       prev_state := SOME best_origin.origin |>
End

(* -------------------------------------------------------------------------- *)
(* Outputs a row for a certain time step of the data stored in the trellis    *)
(*                                                                            *)
(* m: the state machine (must be a num state machine to ease computation)     *)
(* bs: the entire input bitstring                                             *)
(* t: the time step associated with this node in the trellis                  *)
(*                                                                            *)
(* Outputs a set of                                                           *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(*Definition viterbi_trellis_data_row_def:
  viterbi_trellis_data_row m bs 0 = 
End*)

Definition test_path_def:
           test_path = [F; T; T; F; T; T; T; T; F; F; T; F]
End

(* -------------------------------------------------------------------------- *)
(* Unit test to ensure that the values returned by the trellis data function  *)
(* are those you would expect.                                                *)
(*                                                                            *)
(* Hand-calculated trellis:                                                   *)
(*                                                                            *)
(* 0  1  2  3  3  3  4                                                        *)
(* -  0  2  2  3  3  4                                                        *)
(* -  -  2  2  2  5  4                                                        *)
(* -  -  2  3  4  3  3                                                        *)
(* -------------------------------------------------------------------------- *)
(*Theorem viterbi_trellis_data_test:
  viterbi_trellis_data example_state_machine test_path 2 4 = <| num_errors := N 2; prev_state := SOME 1 |>
Proof
  (* Want to use the following command, but it doesn't do anything for some reason:*)
  gvs[viterbi_trellis_data_def]

  (* Tried instead the following, which doesn't help *)
  >> assume_tac (cj 2 viterbi_trellis_data_def)
  >> pop_assum $ qspec_then ‘example_state_machine’ assume_tac
  >> (* pop_assum $ qspecl_then [‘example_state_machine’, ‘test_path’, ‘2’, ‘4’] assume_tac*)
QED*)

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
  path_to_code m (p1::p2::ps) = (states_to_transition_input m p1 p2) :: (path_to_code m (p2::ps))
End

(* -------------------------------------------------------------------------- *)
(* Input: bitstring and state machine                                         *)
(* Output: Most likely original bitstring                                     *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_decode_def:
  viterbi_decode m bs =
  let
    max_timestep = (LENGTH bs) DIV m.output_length;
    last_state = @s. ∀s2. (viterbi_trellis_data m bs s max_timestep).num_errors ≤ (viterbi_trellis_data m bs s2 max_timestep).num_errors;
  in
    path_to_code m (vd_find_optimal_path m bs last_state max_timestep)
End

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
(*Theorem viterbi_correctness:
  ∀m : α state_machine.
    ∀bs rs : bool list.
      hamming_distance rs (convolutional_code_encode m bs) ≤ hamming_distance rs (convolutional_code_encode m (viterbi_decode m rs))
Proof

  ...
QED*)




val _ = export_theory();
