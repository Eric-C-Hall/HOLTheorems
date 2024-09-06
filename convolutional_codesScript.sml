(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "convolutional_codes";

open arithmeticTheory;
open listTheory;
open bitstringTheory;
open infnumTheory;
open prim_recTheory;
open relationTheory;
open rich_listTheory;

open dep_rewrite;
(*open "donotexpandScript.sml"*)

open WFTheoremsTheory;

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

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

Definition test_parity_equation_def:
  test_parity_equation = <| temp_p := [T; T; T]|>
End

Definition test_parity_equation2_def:
  test_parity_equation2 = <| temp_p := [F; T; T]|>
End

Definition test_parity_equations_def:
  test_parity_equations = [test_parity_equation; test_parity_equation2]
End

(* -------------------------------------------------------------------------- *)
(* Returns the length of a parity equation                                    *)
(* -------------------------------------------------------------------------- *)
Definition parity_equation_length_def:
  parity_equation_length p = LENGTH p.temp_p
End

Theorem test_parity_equation_length:
  parity_equation_length test_parity_equation = 3 ∧
  parity_equation_length test_parity_equation2 = 3
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* Returns the maximum length of a set of parity equations                    *)
(* -------------------------------------------------------------------------- *)
Definition parity_equations_max_length_def:
  parity_equations_max_length [] = 0 ∧
  parity_equations_max_length (p::ps) = MAX (parity_equation_length p) (parity_equations_max_length ps)
End

Theorem test_parity_equations_max_length:
  parity_equations_max_length test_parity_equations = 3
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* Treats a bitstring as a parity equation, and applies it to a bitstring     *)
(* with a sufficiently large window length                                    *)
(*                                                                            *)
(* p::ps represents the bitstring that is being treated as a parity equation. *)
(* bs represents the bitstring that the parity equation is applied to.        *)
(* -------------------------------------------------------------------------- *)
Definition apply_bitstring_as_parity_equation_def:
  apply_bitstring_as_parity_equation [] bs = F ∧
  apply_bitstring_as_parity_equation (p::ps) (b::bs) = ((p ∧ b) ⇎ (apply_bitstring_as_parity_equation ps bs))
End

(* -------------------------------------------------------------------------- *)
(* Applies a single parity equation to a bitstring with a sufficiently large  *)
(* window length                                                              *)
(* -------------------------------------------------------------------------- *)
Definition apply_parity_equation_def:
  apply_parity_equation p bs = apply_bitstring_as_parity_equation p.temp_p bs
End

Theorem test_apply_parity_equation:
  apply_parity_equation <| temp_p := [T; F; T] |> [F; F; T] = T ∧
  apply_parity_equation <| temp_p := [F; F; F] |> [T; T; T] = F ∧
  apply_parity_equation <| temp_p := [T; T; T] |> [T; T; T] = T ∧
  apply_parity_equation <| temp_p := [T; T; T] |> [T; F; T] = F ∧
  apply_parity_equation <| temp_p := [T; T; T; F; F] |> [T; F; T; F; T] = F ∧
  apply_parity_equation <| temp_p := [T; F; T; F; T] |> [F; F; F; T; T] = T ∧
  apply_parity_equation <| temp_p := [T; T; T] |> [T; F; T; F; T] = F
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* Applies a bunch of parity equations to a bitstring with a sufficiently     *)
(* large window length                                                        *)
(* -------------------------------------------------------------------------- *)
Definition apply_parity_equations_def:
  apply_parity_equations [] bs = [] ∧
  apply_parity_equations (p::ps) bs = (apply_parity_equation p bs)::(apply_parity_equations ps bs)
End

(* -------------------------------------------------------------------------- *)
(* Takes a number of parity equations and a bitstring, and encodes the        *)
(* bitstring according to the parity equations                                *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_parity_encode_def:
  convolutional_parity_encode ps bs =
  let
    window_length = parity_equations_max_length ps;
  in
    (* Note: if the window length is 0, then LENGTH bs < window_length will
       never be true and thus we will never terminate. Therefore, we also
       terminate if bs = []. *)
    if (LENGTH bs < window_length ∨ bs = []) then [] else
      let
        first_window = TAKE window_length bs;
        step_values = apply_parity_equations ps first_window;
        remaining_bitstring = DROP 1 bs;
        remaining_values = convolutional_parity_encode ps remaining_bitstring;
      in
        step_values ⧺ remaining_values
Termination (* Apparently it's a better idea to do something along the lines of WF_REL_TAC `measure (LENGTH o SND)` *)
  qexists ‘λ(_, bs) (_, cs). LENGTH bs < LENGTH cs’
  >> gvs[]
  >> CONJ_TAC
  >- (assume_tac WF_LESS
      >> qspecl_then [‘$< : num -> num -> bool’, ‘LENGTH ∘ SND : parity_equation list # bool list -> bool list’] assume_tac WF_IMAGE
      >> gvs[]
      >> qmatch_asmsub_abbrev_tac ‘WF f’
      >> qmatch_goalsub_abbrev_tac ‘WF g’
      >> ‘f = g’ suffices_by (strip_tac >> gvs[])
      >> last_x_assum kall_tac
      >> irule EQ_EXT
      >> strip_tac
      >> irule EQ_EXT
      >> strip_tac
      >> unabbrev_all_tac
      >> gvs[]
      >> Cases_on ‘x’
      >> Cases_on ‘x'’
      >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘LENGTH bs’  >> gvs[]
End

Theorem test_convolutional_parity_encode:
  convolutional_parity_encode test_parity_equations [F; F; F; T; T; F; T; F; T; T; T] = [F; F; T; T; F; F; F; T; F; T; T; T; F; T; F; F; T; F]
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* CONVOLUTIONAL STATE MACHINE ENCODING                                       *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* The datatype used as the input of a transition in a state machine          *)
(* -------------------------------------------------------------------------- *)
Datatype:
  gen_transition_origin = <|
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
    transition_fn : α gen_transition_origin -> α gen_transition_destination;
    init : α;
    output_length : num;
    state_ordering : α -> α -> bool;
  |>
End

Datatype:
  transition_origin = <|
    origin : num;
    input : bool;
  |>
End

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
(* Ensure that the num state machine is well-formed                           *)
(* -------------------------------------------------------------------------- *)
Definition wfmachine_def:
  wfmachine (m : state_machine) ⇔
    (* transition_fn:
       - if the origin of the transition is a valid state, then the
         destination must also be a valid state. *)
    (∀n b. n < m.num_states ⇒ (m.transition_fn <| origin := n; input := b |>).destination < m.num_states) ∧
    (* output_length:
       - each transition must output a string of length output_length *)
    (∀n b. n < m.num_states ⇒ LENGTH (m.transition_fn <| origin := n; input := b |>).output = m.output_length)
End

(* -------------------------------------------------------------------------- *)
(* Function for converting from a list of parity equations to a corresponding *)
(* state machine                                                              *)
(* -------------------------------------------------------------------------- *)
Definition parity_equations_to_gen_state_machine_def:
  parity_equations_to_gen_state_machine ps =
  let
    num_parity_equations = LENGTH ps;
    window_length = parity_equations_max_length ps;
    memory_length = window_length - 1;
    num_memory_configurations = 2 ** memory_length;
  in
    <|
      states := {s | LENGTH s = memory_length} : (bool list) set;
      transition_fn := (λorigin.
                          <| destination := TL (SNOC origin.input origin.origin);
                             output := apply_parity_equations ps (SNOC origin.input origin.origin) |>
                       ) : (bool list) gen_transition_origin -> (bool list) gen_transition_destination;
      init := REPLICATE window_length F : (bool list);
      output_length := num_parity_equations : num;
    |>
End

(* -------------------------------------------------------------------------- *)
(* Helper function that does the actual work to encode a binary string using  *)
(* convolutional coding, according to a chosen state machine.                 *)
(*                                                                            *)
(* This function additionally has a parameter to keep track of the current    *)
(* state that the state machine is in.                                        *)
(* -------------------------------------------------------------------------- *)
Definition gen_convolutional_code_encode_helper_def:
  gen_convolutional_code_encode_helper _ [] _ = [] ∧
  gen_convolutional_code_encode_helper (m : α gen_state_machine) (b::bs : bool list) (s : α) =
  let
    d = m.transition_fn <| origin := s; input := b |>
  in
    d.output ⧺ gen_convolutional_code_encode_helper m bs d.destination
End

(* -------------------------------------------------------------------------- *)
(* Encodes a binary string using convolutional coding, according to a chosen  *)
(* state machine                                                              *)
(* -------------------------------------------------------------------------- *)
Definition gen_convolutional_code_encode_def:
  gen_convolutional_code_encode (m : α gen_state_machine) bs = gen_convolutional_code_encode_helper m bs m.init
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
Theorem gen_convolutional_encode_test1:
  gen_wfmachine gen_example_state_machine ∧
  gen_convolutional_code_encode gen_example_state_machine [F; T; T; T; F] = [F; F; T; T; F; F; T; F; F; T]  
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
(* Helper function that does the actual work to encode a binary string using  *)
(* convolutional coding, according to a chosen state machine.                 *)
(*                                                                            *)
(* This function additionally has a parameter to keep track of the current    *)
(* state that the state machine is in.                                        *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_code_encode_helper_def:
  convolutional_code_encode_helper _ [] _ = [] ∧
  convolutional_code_encode_helper (m : state_machine) (b::bs : bool list) (s : num) =
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
  convolutional_code_encode (m : state_machine) bs = convolutional_code_encode_helper m bs 0
End

(* -------------------------------------------------------------------------- *)
(* Takes a step using the state machine to arrive at a new state.             *)
(* -------------------------------------------------------------------------- *)
Definition vd_step_def:
  vd_step (m : state_machine) b s =
  (vd_step_record m b s).destination
End

(* -------------------------------------------------------------------------- *)
(* Helper function to calculate the final state you'll end up in if you apply *)
(* the given state machine to the given bitstring. Also has a variable to     *)
(* keep track of the current state we're in.                                  *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_code_encode_state_helper_def:
  convolutional_code_encode_state_helper (m : state_machine) [] s = s ∧
  convolutional_code_encode_state_helper m (b::bs) s =
  convolutional_code_encode_state_helper m bs (vd_step m b s)
End 

(* -------------------------------------------------------------------------- *)
(* Calculates the final state you'll end up in if you apply the given state   *)
(* machine to the given bitstring.                                            *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_code_encode_state_def:
  convolutional_code_encode_state (m : state_machine) bs = convolutional_code_encode_state_helper m bs 0
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
(* Simple test to make sure the convolutional code is providing the output    *)
(* I would expect if I manually did the computation myself                    *)
(* -------------------------------------------------------------------------- *)
Theorem convolutional_encode_test1:
  wfmachine example_state_machine ∧
  convolutional_code_encode example_state_machine [F; T; T; T; F] = [F; F; T; T; F; F; T; F; F; T]  
Proof
  REVERSE conj_tac
  >- EVAL_TAC
  >> PURE_REWRITE_TAC[wfmachine_def, example_state_machine_def]
  >> gvs[]
  >> conj_tac
  >> rpt strip_tac >> Cases_on ‘b’ >> Cases_on ‘n’ >> gvs[] >> Cases_on ‘n'’ >> gvs[] >> Cases_on ‘n’ >> gvs[] >> Cases_on ‘n'’ >> gvs[]
QED

Definition all_transitions_helper_def:
  all_transitions_helper (m : state_machine) (b : bool) = GENLIST (λn. <| origin := n; input := b |>) m.num_states
End

(* -------------------------------------------------------------------------- *)
(* Returns a list of all valid choices of a transition_origin             *)
(* -------------------------------------------------------------------------- *)
Definition all_transitions_def:
  all_transitions (m : state_machine) = all_transitions_helper m T ⧺ all_transitions_helper m F
End

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

(*Theorem transition_inverse_test:
  transition_inverse example_state_machine 2 = qkdmv  
Proof
  EVAL_TAC
End*)

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
(* Viterbi trellis data                                                       *)
(*                                                                            *)
(* Function from time steps and states to number of errors on optimal path to *)
(* this point in the trellis and previous state on optimal path to this point *)
(* in the trellis                                                             *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Describes the data stored at a particular point in the trellis             *)
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
Definition viterbi_trellis_node_def:
  viterbi_trellis_node m bs s t previous_row =
  let
    relevant_input = TAKE m.output_length (DROP ((t - 1) * m.output_length) bs);    get_num_errors = λr. (EL r.origin previous_row).num_errors + N (hamming_distance (m.transition_fn r).output relevant_input);
    possible_origins = transition_inverse m s;
    best_origin = FOLDR (λr1 r2 : transition_origin. if (get_num_errors r1) < (get_num_errors r2) then r1 else r2) (HD possible_origins) (TL possible_origins)
  in
    <| num_errors := get_num_errors best_origin;
       prev_state := SOME best_origin.origin; |>
End

(* -------------------------------------------------------------------------- *)
(* Evaluate the trellis row-by-row, to take advantage of the dynamic          *)
(* programming nature of the algorithm and ensure it evaluates efficiently.   *)
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
    MAP (λn. (if 0 < n then EL (n - 1) prior_grid_row else 0) + EL n prior_grid_row + (if n < 9 then EL (n + 1) prior_grid_row else 0)) (COUNT_LIST 10)
End

(* -------------------------------------------------------------------------- *)
(* Testing whether or not example_grid takes an exponential amount of time    *)
(* to compute. It could theoretically take an exponential amount of time if   *)
(* the previous row was substituted in multiple places, and expanded out      *)
(* fully multiple times. Each subsequent row would double the amount of time  *)
(* taken because it has to do the computation from the previous row twice.    *)
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
(*Theorem example_grid_time_test:
  example_grid 800 = ARB
Proof
  EVAL_TAC
QED*)

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
(* -  1  2  2  3  3  4                                                        *)
(* -  -  2  2  2  5  4                                                        *)
(* -  -  2  3  4  3  3                                                        *)
(* -------------------------------------------------------------------------- *)
(*Theorem viterbi_trellis_row_test:
  viterbi_trellis_row example_state_machine test_path 4 = ARB
Proof
  EVAL_TAC
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
(* TODO: this will currently regenerate the entire trellis on every           *)
(* iteration, which is slow.                                                  *)
(* -------------------------------------------------------------------------- *)
Definition vd_find_optimal_reversed_path_def:
  vd_find_optimal_reversed_path m bs s 0 = [s] ∧
  vd_find_optimal_reversed_path m bs s (SUC t) =
  let
    trellis_row = viterbi_trellis_row m bs (SUC t);
    trellis_node = EL s trellis_row;
  in 
    s :: (case trellis_node.prev_state of
            NONE => []
          | SOME s2 => vd_find_optimal_reversed_path m bs s2 t
         )
End

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
(* 0  1  2  3  3  3  4                -  0  0  2  2  01 0                     *)
(* -  1  2  2  3  3  4                -  0  0  0  02 2  0                     *)
(* -  -  2  2  2  5  4                -  -  1  1  1  13 13                    *)
(* -  -  2  3  4  3  3                -  -  1  3  13 1  3                     *)
(*    FT TF TT TT FF TF                  FT TF TT TT FF TF                    *)
(*                                                                            *)
(* Starting at state 0, t=6: [0, 0, 0, 2, 1, 0, 0]                            *)
(*                               .. 1, 0, 2, 1, 0]                            *)
(*                                  .. 2, 1, 0, 0]                            *)
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
(*Theorem vd_find_optimal_reversed_path_test:
  vd_find_optimal_reversed_path example_state_machine test_path 0 6 = ARB ∧
  vd_find_optimal_reversed_path example_state_machine test_path 1 4 = ARB ∧
  vd_find_optimal_reversed_path example_state_machine test_path 2 4 = ARB ∧
  vd_find_optimal_reversed_path example_state_machine test_path 3 6 = ARB
Proof
  EVAL_TAC
End*)

(* -------------------------------------------------------------------------- *)
(* See comment for vd_find_optimal_reversed_path                              *)
(*                                                                            *)
(* Reverses the path returned
 by that function to ensure the path is returned *)
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
(* An arbitrary, valid gen_transition_origin, used for testing purposes       *)
(* -------------------------------------------------------------------------- *)
Definition test_transition_origin_def:
  test_transition_origin : α gen_transition_origin = <| origin := test_state; input := F |>
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
(* TODO: This recalculates the whole trellis again, which is already          *)
(* recalculated several times when producing the path back through the        *)
(* trellis                                                                    *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_decode_def:
  viterbi_decode m bs =
  let
    max_timestep = (LENGTH bs) DIV m.output_length;
    last_row = viterbi_trellis_row m bs max_timestep;
    best_state = FOLDR (λs1 s2. if (EL s1 last_row).num_errors < (EL s2 last_row).num_errors then s1 else s2) 0 (COUNT_LIST m.num_states)
  in
    path_to_code m (vd_find_optimal_path m bs best_state max_timestep)
End

(*Theorem viterbi_decode_test:
  let
    decoded_path = viterbi_decode example_state_machine test_path;
    encoded_decoded_path = convolutional_code_encode example_state_machine decoded_path
  in
    decoded_path = ARB ∧
    encoded_decoded_path = ARB ∧
    test_path = ARB ∧
    hamming_distance encoded_decoded_path test_path = ARB                
Proof
  EVAL_TAC
QED*)

Theorem convolutional_code_encode_empty[simp]:
  ∀m. convolutional_code_encode m [] = []
Proof
  rpt strip_tac
  >> EVAL_TAC
QED

Theorem vd_find_optimal_path_empty[simp]:
  ∀m bs s t. vd_find_optimal_path m bs s 0 = [s]
Proof
  rpt strip_tac
  >> EVAL_TAC
QED

Theorem path_to_code_singleton[simp]:
  ∀m s. path_to_code m [s] = []
Proof
  rpt strip_tac
  >> EVAL_TAC
QED

Theorem convolutional_code_decode_empty[simp]:
  ∀m. viterbi_decode m [] = []
Proof
  rpt strip_tac
  >> gvs[viterbi_decode_def]
QED

(* -------------------------------------------------------------------------- *)
(* See comment for convolutional_code_encode_cons                             *)
(* -------------------------------------------------------------------------- *)
Theorem convolutional_code_encode_helper_cons:
  ∀m b bs s.
    convolutional_code_encode_helper m (b :: bs) s =
    (vd_step_output m b s) ⧺ (convolutional_code_encode_helper m bs (convolutional_code_encode_state_helper m [b] s))
Proof
  rpt strip_tac
  >> gvs[convolutional_code_encode_helper_def]
  >> gvs[convolutional_code_encode_state_helper_def]
  >> gvs[vd_step_def, vd_step_record_def, vd_step_output_def]
QED

(* -------------------------------------------------------------------------- *)
(* Can break convolutional encoding up into doing a step, with the rest of    *)
(* the encoding appended on, starting from the appropriate state              *)
(* -------------------------------------------------------------------------- *)
Theorem convolutional_code_encode_cons:
  ∀m b bs. convolutional_code_encode m (b :: bs) =
           (vd_step_output m b 0) ⧺ (convolutional_code_encode_helper m bs (convolutional_code_encode_state m [b]))
Proof
  rpt strip_tac
  >> gvs[convolutional_code_encode_def]
  >> gvs[convolutional_code_encode_state_def]
  >> PURE_ONCE_REWRITE_TAC[convolutional_code_encode_helper_cons]
  >> gvs[]
QED



(* -------------------------------------------------------------------------- *)
(* See comment for convolutional_code_encode_append                           *)
(* -------------------------------------------------------------------------- *)
Theorem convolutional_code_encode_helper_append:
  ∀m bs cs s.
    convolutional_code_encode_helper m (bs ⧺ cs) s =
    convolutional_code_encode_helper m bs s ⧺ convolutional_code_encode_helper m cs (convolutional_code_encode_state_helper m bs s)          
Proof
  gen_tac
  >> Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[APPEND]
  >> gvs[convolutional_code_encode_helper_cons]
  >> gvs[convolutional_code_encode_state_helper_def]
QED

(* -------------------------------------------------------------------------- *)
(* Can break convolutional encoding up into two halves: doing a bunch of      *)
(* steps from the initial state, then doing a bunch of steps from the state   *)
(* that is reached at this point.                                             *)
(* -------------------------------------------------------------------------- *)
Theorem convolutional_code_encode_append:
  ∀m bs cs.
    convolutional_code_encode m (bs ⧺ cs) =
    (convolutional_code_encode m bs) ⧺ (convolutional_code_encode_helper m cs (convolutional_code_encode_state m bs))
Proof
  rpt strip_tac
  >> gvs[convolutional_code_encode_def, convolutional_code_encode_state_def]
  >> gvs[convolutional_code_encode_helper_append]
QED

(* -------------------------------------------------------------------------- *)
(* Can break convolutional encoding up into doing a bunch of steps from the   *)
(* initial state, then doing a final step from the final state.               *)
(* -------------------------------------------------------------------------- *)
Theorem convolutional_code_encode_snoc:
  ∀m b bs. convolutional_code_encode m (SNOC b bs) =
           (convolutional_code_encode m bs) ⧺ (convolutional_code_encode_helper m [b] (convolutional_code_encode_state m bs))
Proof
  gvs[SNOC]
  >> gvs[convolutional_code_encode_append]
QED

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
(* Proof outline:                                                             *)
(*                                                                            *)
(* Induct over bs                                                             *)
(*                                                                            *)
(* In base case, bs and rs are both empty. So too is the encoding of bs, the  *)
(* decoding of rs, and the encoding and decoding of rs, so our statement      *)(* reduces to hamming_distance [] [] ≤ hamming_distance [] []                 *)
(*                                                                            *)
(* In the inductive step, we know that for all lesser lengthed bs, assuming   *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem viterbi_correctness:
        ∀m : state_machine.
          ∀bs rs : bool list.
            wfmachine m ∧
            LENGTH rs = m.output_length * LENGTH bs ⇒
            hamming_distance rs (convolutional_code_encode m bs) ≤ hamming_distance rs (convolutional_code_encode m (viterbi_decode m rs))
Proof
  gen_tac
  >> Induct_on ‘bs’ using SNOC_INDUCT
  >- gvs[]
  >> rpt strip_tac
  >> gvs[]
  >> 
  
QED




val _ = export_theory();
