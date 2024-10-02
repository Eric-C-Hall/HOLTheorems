(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "convolutional_codes";

open arithmeticTheory;
open listTheory;
open bitstringTheory;
open infnumTheory;
open pred_setTheory;
open prim_recTheory;
open relationTheory;
open rich_listTheory;
open dividesTheory;

open dep_rewrite;
open ConseqConv; (* SPEC_ALL_TAC *)
(*use "donotexpandLib.sml"*)

open WFTheoremsTheory;

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"
                   
(* -------------------------------------------------------------------------- *)
(* Based on the MIT 6.02 DRAFT Lecture Notes Fall 2010                        *)
(*                                                                            *)
(* TODO: Cite better                                                          *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* If you want to work on my code, I recommend using abbreviations, because   *)
(* many of my variable names are quite long. for example, when I type the     *)
(* letters "gnecs", my emacs will automatically expand this out to            *)
(* "get_num_errors_calculate_slow". Similarly, if I type "vtn", my emcs will  *)
(* automatically expand this out to "viterbi_trellis_node".                   *)
(* -------------------------------------------------------------------------- *)
                   
(*

        TODO: Temporary place for donotexpand while asking about how to use it properly as a library

*)


(* TODO: Find better way to do this *)
Definition donotexpand_def:
  donotexpand P = P
End

Theorem donotexpand_thm:
  donotexpand P ⇔ P
Proof
  gvs[donotexpand_def]
QED

open simpLib

(* tactic that allows you to tell HOL4 to not expand the top theorem *)
val donotexpand_tac =
(* abbreviate relevant assumption *)
qmatch_asmsub_abbrev_tac ‘donotexpand_var’
(* Ignore top assumption (Abbrev), apply donotexpand to second assumption *)
>> pop_assum (fn th => drule $ iffRL donotexpand_thm >> assume_tac th)
(* expand abbreviation *)
>> simp_tac empty_ss [Abbr ‘donotexpand_var’]
(* remove original assumption without donotexpand *)
>> pop_assum kall_tac
(* discharge donotexpand-ed assumption to assumptions *)
>> disch_tac

(* Tactic that undoes the effect of donotexpand_tac *)
val doexpand_tac =
(* abbreviate assumption to expand *)
qmatch_asmsub_abbrev_tac ‘donotexpand donotexpand_var’
(* move assumption to expand to top *)
>> qpat_x_assum ‘donotexpand donotexpand_var’ assume_tac
(* expand assumption*)
>> ‘donotexpand_var’ by (irule $ iffLR donotexpand_thm >> simp[])
(* remove unexpanded assumption *)
>> qpat_x_assum ‘donotexpand donotexpand_var’ kall_tac
(* unabbreviate assumption *)
>> simp_tac empty_ss [Abbr ‘donotexpand_var’]

Definition MEM_DONOTEXPAND_def:
  MEM_DONOTEXPAND = $MEM
End

Theorem MEM_DONOTEXPAND_thm:
  ∀l ls.
  MEM_DONOTEXPAND l ls = MEM l ls
Proof
  rpt strip_tac >> EVAL_TAC
QED

val MEM_DONOTEXPAND_TAC = rpt (pop_assum mp_tac) >> PURE_REWRITE_TAC[GSYM MEM_DONOTEXPAND_thm] >> rpt disch_tac
val MEM_DOEXPAND_TAC = rpt (pop_assum mp_tac) >> PURE_REWRITE_TAC[MEM_DONOTEXPAND_thm] >> rpt disch_tac

(* -------------------------------------------------------------------------- *)
(* This seems like a particularly useful function that could potentially be   *)
(* added to HOL, although I haven't spent much time polishing it              *)
(* -------------------------------------------------------------------------- *)
fun GCONTRAPOS th = GEN_ALL (CONTRAPOS (SPEC_ALL th));

val Cases_on_if_goal = qmatch_goalsub_abbrev_tac ‘if jwlifmn then _ else _’ >> Cases_on ‘jwlifmn’;

val Cases_on_if_asm = qmatch_asmsub_abbrev_tac ‘if jwlifmn then _ else _’ >> Cases_on ‘jwlifmn’;

val imp_prove = qmatch_asmsub_abbrev_tac ‘jwlifmn ⇒ _’ >> sg ‘jwlifmn’ >> asm_simp_tac bool_ss [Abbr ‘jwlifmn’];

fun with_all_in_goal t = rpt (pop_assum mp_tac) >> t >> rpt disch_tac;

(* -------------------------------------------------------------------------- *)
(* Not sure what the term is for a function which returns one of its inputs   *)
(* as its output, so I used the term "bi-switch", because the function        *)
(* switches between two of its inputs.                                        *)
(* -------------------------------------------------------------------------- *)
Theorem FOLDR_BISWITCH:
  ∀f h ts.
  (∀x y.  f x y = x ∨ f x y = y) ⇒
  MEM (FOLDR f h ts) (h::ts)
Proof
  rpt strip_tac
  (* Induct over ts. Base case trivial *)
  >> Induct_on ‘ts’
  >- gvs[]
  >> rpt strip_tac
  >> PURE_REWRITE_TAC[FOLDR]
  (* do not expand mem, it creates a messy case structure *)
  >> MEM_DONOTEXPAND_TAC
  >> last_x_assum $ qspecl_then [‘h'’, ‘FOLDR f h ts’] assume_tac
  >> MEM_DOEXPAND_TAC
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Probably not widely applicable enough to become a proper theorem           *)
(* -------------------------------------------------------------------------- *)
Theorem MEM_CONS_CONS:
  ∀x l l' ls.
  MEM x (l::l'::ls) ⇔ MEM x (l::ls) ∨ x = l'
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (gvs[]
      >> rpt strip_tac >> gvs[])
  >> rpt strip_tac >> gvs[]
QED


Theorem FOLDR_DOMAIN_HELPER:
  ∀f g l ls s.
  (∀x. MEM x (l::ls) ⇒ x ∈ s) ∧
  (∀x y. x ∈ s ∧ y ∈ s ⇒ f x y = g x y ∧ (f x y) ∈ s) ⇒
  FOLDR f l ls = FOLDR g l ls ∧ (FOLDR f l ls) ∈ s
Proof
  Induct_on ‘ls’
  >- gvs[]
  >> rpt gen_tac
  >> rpt disch_tac
  >> MEM_DONOTEXPAND_TAC
  >> gvs[FOLDR]
  >> qsuff_tac ‘FOLDR f l ls = FOLDR g l ls ∧ FOLDR f l ls ∈ s’
  >- (disch_tac
      >> gvs[]
      >> first_assum irule
      >> conj_tac
      >- (MEM_DOEXPAND_TAC
          >> gvs[])
      >> gvs[])
  >> last_assum irule
  >> gvs[]
  >> MEM_DOEXPAND_TAC
  >> gvs[]
  >> rpt strip_tac
  >> gvs[]
QED

val FOLDR_DOMAIN = cj 1 FOLDR_DOMAIN_HELPER;

Theorem FOLDR_DOMAIN_MEM_HELPER:
  ∀f g l ls.
  (∀x y. MEM x (l::ls) ∧ MEM y (l::ls) ⇒ f x y = g x y ∧ MEM (f x y) (l::ls)) ⇒
  FOLDR f l ls = FOLDR g l ls ∧ MEM (FOLDR f l ls) (l::ls)
Proof
  rpt gen_tac
  >> rpt disch_tac
  >> irule FOLDR_DOMAIN_HELPER
  >> rpt strip_tac >> gvs[]
QED

val FOLDR_DOMAIN_MEM = cj 1 FOLDR_DOMAIN_MEM_HELPER;

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
val _ = set_mapped_fixity{fixity = Infixl 500, term_name = "add_noise", tok = "⊕"}

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
val transition_origin_component_equality = fetch "convolutional_codes" "transition_origin_component_equality";

Theorem transition_origin_literal_components[simp]:
  ∀r.
  <| origin := r.origin; input := r.input |> = r
Proof
  rpt strip_tac
  >> gvs[transition_origin_component_equality]
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
Definition gen_vd_encode_helper_def:
  gen_vd_encode_helper _ [] _ = [] ∧
  gen_vd_encode_helper (m : α gen_state_machine) (b::bs : bool list) (s : α) =
  let
    d = m.transition_fn <| origin := s; input := b |>
  in
    d.output ⧺ gen_vd_encode_helper m bs d.destination
End

(* -------------------------------------------------------------------------- *)
(* Encodes a binary string using convolutional coding, according to a chosen  *)
(* state machine                                                              *)
(* -------------------------------------------------------------------------- *)
Definition gen_vd_encode_def:
  gen_vd_encode (m : α gen_state_machine) bs = gen_vd_encode_helper m bs m.init
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

Theorem transition_inverse_mem[simp]:
  ∀m s r.
  MEM r (transition_inverse m s) ⇒
  vd_step_tran m r = s 
Proof
  rpt strip_tac
  >> gvs[transition_inverse_def]
  >> gvs[MEM_FILTER]
  >> gvs[vd_step_tran_def, vd_step_def, vd_step_record_def]
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
  >> gvs[transition_origin_component_equality]
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

(*Definition transition_inverse_set_def:
  transition_inverse_set (m : state_machine) =
  IMAGE 
End*)

(*Theorem transition_inverse_test:
  transition_inverse example_state_machine 2 = ARB
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
(* Returns the portion of the input bitstring which is relevant to the        *)
(* current time-step                                                          *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire input bitstring                                             *)
(* t: the time-step to take the input for. We will return the appropriate     *)
(*    input for calculating the value of the node in the trellis which is at  *)
(*    time-step t. This also means that our inputs are indexed starting at 1, *)
(*    rather than 0, so that the first slice of input is indexed with 1,      *)
(*    rather than 0.                                                          *)
(*                                                                            *)
(* Output: the corresponding portion of the input bitstring.                  *)
(* -------------------------------------------------------------------------- *)
Definition relevant_input_def:
  relevant_input m bs t = TAKE m.output_length (DROP ((t - 1) * m.output_length) bs)
End

(* -------------------------------------------------------------------------- *)
(* Returns the total number of errors that would be present if we took a path *)
(* through the transition with origin r, given the number of errors in the    *)
(* previous row and the part of the received message which corresponds to     *)
(* this transition.                                                           *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire input bitstring                                             *)
(* t: the time-step that we will arrive at after taking the transition r. The *)
(*    origins are at the prior time-step to t.                                *)
(* r: the choice of origin that we are returning the number of errors for if  *)
(*    we were to pass through this transition.                                *)
(*                                                                            *)
(* Invalid at time-step 0 because there is no previous row in this case.      *)
(* -------------------------------------------------------------------------- *)
Definition get_num_errors_calculate_def:
  get_num_errors_calculate m bs t previous_row r = (EL r.origin previous_row).num_errors + N (hamming_distance (m.transition_fn r).output (relevant_input m bs t))
End

(* -------------------------------------------------------------------------- *)
(* Returns which of the given two origins would be a better choice to pass    *)
(* through if we want to minimize the number of errors in the final path      *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire input bitstring                                             *)
(* t: the time-step that we will arrive at. The origins are at the prior      *)
(*    time-step to t.                                                         *)
(* previous_row: the row of data in the trellis at time-step t - 1            *)
(* r1: the first potential choice of origin to compare                        *)
(* r2: the second potential choice of origin to compare                       *)
(*                                                                            *)
(* Output: either r1 or r2, depending on which choice of origin will minimize *)
(*         the number of errors in the final path.                            *)
(* -------------------------------------------------------------------------- *)
Definition get_better_origin_def:
  get_better_origin m bs t previous_row r1 r2 =
  if (get_num_errors_calculate m bs t previous_row r1) < (get_num_errors_calculate m bs t previous_row r2) then r1 else r2
End

(* -------------------------------------------------------------------------- *)
(* Works out which origin is the best origin to pass through in order to      *)
(* arrive at s optimally, given the previous row of errors and the part of    *)
(* the input which is relevant to this transition.                            *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire input that needs to be decoded                              *)
(* t: the time step that s is at, when we arrive at it. This means that the   *)(*    best origin will be at the prior time-step to t.                        *)
(* previous_row: the row of data in the trellis at time-step t - 1            *)
(* s: the state that we would like to arrive at.                              *)
(*                                                                            *)
(* Output: The choice of origin which will optimally arrive at the state s at *)
(*         time-step t, as a transition_origin including an origin state and  *)
(*         an input boolean.                                                  *)
(* -------------------------------------------------------------------------- *)
Definition best_origin_def:
  best_origin m bs t previous_row s =
  let
    possible_origins = transition_inverse m s;
  in
    FOLDR (get_better_origin m bs t previous_row) (HD possible_origins) (TL possible_origins)
End

(* -------------------------------------------------------------------------- *)
(* Returns a specific node in the trellis. Takes the previous row as input,   *)
(* so that we can reuse those precomputed values rather than recomputing them,*)
(* which would end up taking exponential time.                                *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire input bitstring                                             *)
(* s: the state associated with this node in the trellis                      *)
(* t: the time step associated with this node in the trellis                  *)
(* previous_row: the row of data associated with the previous time step.      *)
(*                                                                            *)
(* Outputs a tuple containing the number of errors at this point as well as   *)
(* the previous state on the optimal path towards this point                  *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_trellis_node_def:
  viterbi_trellis_node m bs s t previous_row =
  let
    best_origin_local = best_origin m bs t previous_row s;
  in
    <| num_errors := get_num_errors_calculate m bs t previous_row best_origin_local;
       prev_state := SOME best_origin_local.origin; |>
End

(* -------------------------------------------------------------------------- *)
(* Returns a row of the trellis, used by the Viterbi algorithm to decode a    *)
(* convolutional code. The previous row is completely evaluated before        *)
(* starting the evaluation of this row, and so we can reuse it multiple times *)
(* in the evaluation of this row, in a dynamic programming way. This ensures  *)
(* that the trellis is evaluated in linear time rather than exponential time. *)(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the entire bitstring we want to decode                                 *)
(* t: the timestep to calculate the row for,                                  *)
(*                                                                            *)
(* Output: the corresponding row of the trellis, in list form, where the nth  *)
(* element of the list corresponds to the nth state, and is a tuple of the    *)
(* the form <| num_errors; prev_state |>                                      *)
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
(* Calculate a node in the trellis for the fast version when the previous row *)
(* is not available (by calculating all prior rows of the trellis)            *)
(*                                                                            *)
(* Defined in such a way as to be valid even at time-step 0, when there isn't *)
(* a previous row present.                                                    *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_trellis_node_no_prev_data_def:
  viterbi_trellis_node_no_prev_data m bs s t = EL s (viterbi_trellis_row m bs t)
End

(* -------------------------------------------------------------------------- *)
(* Version of get_num_errors_calculate which works even if you do not provide *)
(* it with the previous row of errors                                         *)
(*                                                                            *)
(* Invalid at time-step 0 because there is no previous row in this case.      *)
(* -------------------------------------------------------------------------- *)
Definition get_num_errors_calculate_no_prev_data_def:
  get_num_errors_calculate_no_prev_data m bs 0 r = (if (vd_step_tran m r = 0) then N0 else INFINITY) ∧
  get_num_errors_calculate_no_prev_data m bs (SUC t) r = get_num_errors_calculate m bs (SUC t) (viterbi_trellis_row m bs t) r
End

(* -------------------------------------------------------------------------- *)
(* A slower but mathematically simpler implementation of the function for     *)
(* working out the best origin in the viterbi trellis.                        *)
(*                                                                            *)
(* Combined definition of several functions because these functions are       *)
(* recursively dependent on each other.                                       *)
(* -------------------------------------------------------------------------- *)
Definition viterbi_trellis_slow:
  get_num_errors_calculate_slow m bs 0 r = (if (vd_step_tran m r = 0) then N0 else INFINITY) ∧
  (get_num_errors_calculate_slow m bs (SUC t) r =
   (get_num_errors_calculate_slow m bs t (best_origin_slow m bs t r.origin)) + N (hamming_distance (m.transition_fn r).output (relevant_input m bs (SUC t)))
  ) ∧ 
  (get_better_origin_slow m bs t r1 r2 =
   if (get_num_errors_calculate_slow m bs t r1) < (get_num_errors_calculate_slow m bs t r2) then r1 else r2) ∧
  (best_origin_slow m bs t s =
   let
     possible_origins = transition_inverse m s;
   in
     FOLDR (get_better_origin_slow m bs t) (HD possible_origins) (TL possible_origins))
Termination
  (* Use a standard measure-based method for proving termination. (see the
     HOL System Description on proving termination). We have a circular
     recursion of 3 functions, where on every loop, t decreases by 1.
.
     best_origin_slow (SUC t) -> get_better_origin_slow (SUC t) ->
     get_num_errors_calculate_slow (SUC t) -> best_origin_slow t ->
     get_better_origin_slow t -> ...
.
     Thus, in order to ensure that our measure decreases on every function
     call, we should multiply t by 3, and add a number between 0 and 2 such
     that functions earlier in this sequence have a larger measure. *)
  (*
    Since there are 3 mutually recursive functions being defined here,
    we are using the disjoint sum type
  *)
  WF_REL_TAC ‘measure (λx.
                         (* test if we're currently in the first function
                            call, and thus being provided with the arguments
                            to the first fucntion *)
                         if ISL x 
                         then
                           (* get the argument t given the arguments to the
                              first function *)
                           3 * (FST $ SND $ SND $ OUTL x)
                         else
                           let x' = OUTR x in
                             if ISL x'
                             then
                               3 * (FST $ SND $ SND $ OUTL x') + 1
                             else
                               3 * (FST $ SND $ SND $ OUTR x') + 2
                      )’
  >> gvs[]
End

(* -------------------------------------------------------------------------- *)
(* Creating theorems in order to adhere to standard naming conventions for    *)
(* function definitions, as this was not possible because multiple functions  *)
(* were defined in the same definition                                        *)
(* -------------------------------------------------------------------------- *)
Theorem get_num_errors_calculate_slow_def = LIST_CONJ [cj 1 viterbi_trellis_slow, cj 2 viterbi_trellis_slow]
Theorem get_better_origin_slow_def = cj 3 viterbi_trellis_slow
Theorem best_origin_slow_def = cj 4 viterbi_trellis_slow

Theorem get_better_origin_slow_biswitch[simp]:
  ∀m bs t x y.
  get_better_origin_slow m bs t x y = x ∨
  get_better_origin_slow m bs t x y = y
Proof
  rpt strip_tac
  >> gvs[get_better_origin_slow_def]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’ >> gvs[]
QED

Theorem FOLDR_get_better_origin_slow:
  ∀m bs t r rs.
  MEM (FOLDR (λa' a. get_better_origin_slow m bs t a' a) r rs) (r::rs)
Proof
  rpt strip_tac
  >> gvs[FOLDR_BISWITCH]
QED

Theorem best_origin_slow_transition_inverse:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  MEM (best_origin_slow m bs t s) (transition_inverse m s)
Proof
  rpt strip_tac
  >> gvs[best_origin_slow_def]
  >> qspecl_then [‘m’, ‘bs’, ‘t’, ‘HD (transition_inverse m s)’, ‘TL (transition_inverse m s)’] assume_tac FOLDR_get_better_origin_slow
  >> MEM_DONOTEXPAND_TAC
  >> gvs[]
QED

Theorem best_origin_slow_is_valid[simp]:
  ∀m bs t s.
  wfmachine m ∧
  s < m.num_states ⇒
  (best_origin_slow m bs t s).origin < m.num_states
Proof
  rpt strip_tac
  >> qspecl_then [‘m’, ‘bs’, ‘s’, ‘t’] assume_tac best_origin_slow_transition_inverse
  >> metis_tac[transition_inverse_mem_is_valid]
QED

Definition viterbi_trellis_node_slow_def:
  viterbi_trellis_node_slow m bs s t =
  let
    best_origin_local = best_origin_slow m bs t s;
  in
    <| num_errors := get_num_errors_calculate_slow m bs t best_origin_local;
       prev_state := if (t = 0) then NONE else SOME best_origin_local.origin; |>
End  
     
(* -------------------------------------------------------------------------- *)
(* Test equivalance of slow version of trellis calculation with fast version  *)
(* for some small values of s and t, through evaluation.                      *)
(* -------------------------------------------------------------------------- *)
Theorem viterbi_trellis_node_slow_test:
  ∀s t.
  s < 4 ∧ t ≤ 3 ⇒
  viterbi_trellis_node_slow example_state_machine test_path s t = viterbi_trellis_node_no_prev_data example_state_machine test_path s t
Proof
  rpt strip_tac
  >> sg ‘(s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) ∧ (t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3)’ >> gvs[]
  >> EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* Be extra careful with the special case at time step zero, and test to      *)
(* ensure that it has the expected value, not just the same value as the      *)
(* other implementation.                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem viterbi_trellis_node_slow_time_step_zero_test:
  ∀s.
  s < 4 ⇒
  viterbi_trellis_node_slow example_state_machine test_path s 0 =
  <| num_errors := if s = 0 then N0 else INFINITY; prev_state := NONE|>
Proof
  rpt strip_tac
  >> sg ‘(s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3)’ >> gvs[]
  >> EVAL_TAC
QED

Theorem viterbi_trellis_row_el:
  ∀m bs s t. 
  s < m.num_states ⇒
  EL s (viterbi_trellis_row m bs (SUC t)) = viterbi_trellis_node m bs s (SUC t) (viterbi_trellis_row m bs t)
Proof
  gvs[viterbi_trellis_row_def]
QED

Theorem vd_step_tran_best_origin_slow[simp]:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  vd_step_tran m (best_origin_slow m bs t s) = s
Proof
  rpt strip_tac
  >> gvs[best_origin_slow_def]
  >> qmatch_goalsub_abbrev_tac ‘FOLDR f h ts’
  (* Apply FOLDR_BISWITCH to prove that the result of this fold must be
     contained within the list formed by the input to the FOLDR. *)
  >> sg ‘MEM (FOLDR f h ts) (h::ts)’
  >- (irule FOLDR_BISWITCH
      >> unabbrev_all_tac
      >> rpt strip_tac
      >> gvs[])
  >> MEM_DONOTEXPAND_TAC
  (* Simplify h::ts into transition_inverse m s *)
  >> sg ‘h::ts = transition_inverse m s’
  >- (unabbrev_all_tac
      >> gvs[CONS]
     )
  >> gvs[]
  >> pop_assum kall_tac
  (* *)
  >> MEM_DOEXPAND_TAC
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Test that the slow and fast versions of the function that calculates       *)
(* errors in the trellis are equivalent for some simple examples.             *)
(* -------------------------------------------------------------------------- *)
Theorem get_num_errors_calculate_slow_get_num_errors_calculate_test:
  ∀t r.
  t < 4 ∧
  r.origin < 4 ⇒
  get_num_errors_calculate_slow example_state_machine test_path (SUC t) r = get_num_errors_calculate example_state_machine test_path (SUC t) (viterbi_trellis_row example_state_machine test_path t) r
Proof
  rpt strip_tac
  >> sg ‘(t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) ∧ (r.origin = 0 ∨ r.origin = 1 ∨ r.origin = 2 ∨ r.origin = 3)’
  (* This sequence of tactics will simultaneously prove all 16 proof
     obligations *)
  >> (gvs[]
      >> qmatch_asmsub_abbrev_tac ‘r.origin = r_val’
      >> Cases_on ‘r’
      >> ‘n = r_val’ by gvs[]
      >> unabbrev_all_tac
      >> gvs[]
      >> Cases_on ‘b’
      >> EVAL_TAC)
QED

Theorem get_num_errors_calculate_slow_get_num_errors_calculate_no_prev_data_test:
  ∀t r.
  t < 3 ∧
  r.origin < 4 ⇒
  get_num_errors_calculate_slow example_state_machine test_path (SUC t) r = get_num_errors_calculate_no_prev_data example_state_machine test_path (SUC t) r
Proof
  rpt strip_tac
  >> sg ‘(t = 0 ∨ t = 1 ∨ t = 2) ∧ (r.origin = 0 ∨ r.origin = 1 ∨ r.origin = 2 ∨ r.origin = 3)’ >> gvs[]
  (* This sequence of tactics will simultaneously prove all 12 proof
     obligations *)
  >> (qmatch_asmsub_abbrev_tac ‘r.origin = r_val’
      >> Cases_on ‘r’
      >> ‘n = r_val’ by gvs[]
      >> unabbrev_all_tac
      >> gvs[]
      >> Cases_on ‘b’
      >> EVAL_TAC)
QED

Theorem get_num_errors_calculate_slow_get_num_errors_calculate_no_prev_data:
  ∀m bs t r.
  wfmachine m ∧
  r.origin < m.num_states ⇒
  get_num_errors_calculate_slow m bs (SUC t) r = get_num_errors_calculate_no_prev_data m bs (SUC t) r
Proof
  gen_tac
  >> Induct_on ‘t’
  >- (gvs[get_num_errors_calculate_no_prev_data_def]
      >> rpt strip_tac
      (* expand stuff out *)
      >> gvs[]
      >> gvs[get_num_errors_calculate_slow_def, get_num_errors_calculate_def]
      >> gvs[viterbi_trellis_row_def]
      (* When r.origin is nonzero, the RHS simplifies to infinity. Deal
         with this special case. *)
      >> REVERSE (Cases_on ‘r.origin’)
      >- (gvs[EL_REPLICATE]
          >> PURE_REWRITE_TAC [ONE]
          >> gvs[get_num_errors_calculate_slow_def]
          >> gvs[EL_REPLICATE])
      >> gvs[]
      >> PURE_REWRITE_TAC[ONE]
      >> gvs[get_num_errors_calculate_slow_def]
     )
  (* Inductive step *)
  >> rpt strip_tac
  (* Expand out the slow version so that all slow version functions are
     calculated at a lower time-step, and all slow version funcctions are
     get_num_errors_calculate_slow, so that we can use our inductive
     hypothesis to translate to a statement entirely in terms of fast version
     functions. *)
  >> PURE_ONCE_REWRITE_TAC[get_num_errors_calculate_slow_def]
  >> gvs[best_origin_slow_def]
  >> gvs[get_better_origin_slow_def]
  (* translate the inner function so that it is written in terms of the fast
        version. *)
  >> qmatch_goalsub_abbrev_tac ‘FOLDR f _ _’
  (* ------------------------------------------------------------------------ *)
  (* Are there nicer ways to deal with functions that are equal to each other *)
  (* only on a specific domain?                                               *)
  (* ------------------------------------------------------------------------ *)
  >> sg ‘f = (λa' a. if (a.origin < m.num_states ∧ a'.origin < m.num_states) then (if get_num_errors_calculate_no_prev_data m bs (SUC t) a' < get_num_errors_calculate_no_prev_data m bs (SUC t) a then a' else a) else f a' a)’
  >- (unabbrev_all_tac
      >> irule EQ_EXT >> rpt strip_tac >> gvs[]
      >> irule EQ_EXT >> rpt strip_tac >> gvs[]
      >> qmatch_goalsub_abbrev_tac ‘_ = if b then _ else _’
      >> Cases_on ‘b’ >> gvs[]
      >> last_assum $ qspecl_then [‘bs’, ‘x’] assume_tac
      >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
     )
  (* Replace the other slow function with a fast function, using the inductive
     hypothesis. *)
  (*>> last_assum $ (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
      >> conj_tac
      >- (qmatch_goalsub_abbrev_tac ‘FOLDR f tr trs’
          >> sg ‘MEM (FOLDR f tr trs) (tr::trs)’
          >- (irule FOLDR_BISWITCH
              >> rpt strip_tac
              >> unabbrev_all_tac
              >> gvs[]
              >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
              >> Cases_on ‘b’ >> gvs[])
          >> sg ‘MEM (FOLDR f tr trs) (transition_inverse m r.origin)’
          >- (‘tr::trs = transition_inverse m r.origin’ suffices_by (disch_tac >> metis_tac[])
              >> unabbrev_all_tac
              >> simp[transition_inverse_cons])
          >> metis_tac[transition_inverse_mem_is_valid])*)
  >> irule EQ_SYM
  >> gvs[get_num_errors_calculate_no_prev_data_def]
  >> simp[Once get_num_errors_calculate_def]
  >> AP_THM_TAC
  >> AP_TERM_TAC
  >> gvs[viterbi_trellis_row_def]
  >> gvs[viterbi_trellis_node_def]
  >> AP_TERM_TAC
  >> gvs[best_origin_def]
  >> unabbrev_all_tac
  >> gvs[]
  >> irule FOLDR_DOMAIN_MEM
  >> rpt gen_tac
  >> MEM_DONOTEXPAND_TAC
  >> gvs[]
  >> REVERSE conj_tac
  >- (gvs[get_better_origin_def]
      >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[]
     )
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> sg ‘b’
  >- (unabbrev_all_tac
      >> MEM_DOEXPAND_TAC
      >> metis_tac[transition_inverse_mem_is_valid]
     )
  >> gvs[]
  >> gvs[get_better_origin_def]
QED

Theorem get_num_errors_calculate_slow_get_num_errors_calculate:
  ∀m bs t r.
       wfmachine m ∧
       r.origin < m.num_states ⇒
       get_num_errors_calculate_slow m bs (SUC t) r = get_num_errors_calculate m bs (SUC t) (viterbi_trellis_row m bs t) r
Proof
  gvs[get_num_errors_calculate_slow_get_num_errors_calculate_no_prev_data, get_num_errors_calculate_no_prev_data_def]
QED


Theorem get_better_origin_slow_get_better_origin:
  ∀m bs t r1 r2.
  wfmachine m ∧
  r1.origin < m.num_states ∧
  r2.origin < m.num_states ⇒
  get_better_origin_slow m bs (SUC t) r1 r2 = get_better_origin m bs (SUC t) (viterbi_trellis_row m bs t) r1 r2
Proof
  rpt strip_tac
  >> gvs[get_better_origin_slow_def, get_better_origin_def]
  >> gvs[get_num_errors_calculate_slow_get_num_errors_calculate]
QED

Theorem best_origin_slow_best_origin:
  ∀m bs t s.
  wfmachine m ∧
  s < m.num_states ⇒
  best_origin_slow m bs (SUC t) s = best_origin m bs (SUC t) (viterbi_trellis_row m bs t) s  
Proof
  rpt strip_tac
  >> gvs[best_origin_slow_def, best_origin_def]
  >> irule FOLDR_DOMAIN
  >> MEM_DONOTEXPAND_TAC
  >> qexists ‘all_transitions_set m’
  >> gvs[]
  >> rpt strip_tac
  >- (DEP_PURE_ONCE_REWRITE_TAC[get_better_origin_slow_get_better_origin]
      >> gvs[all_transitions_set_def]
     )
  >- (gvs[get_better_origin_slow_def]
      >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[])
  >> MEM_DOEXPAND_TAC
  >> metis_tac[transition_inverse_mem_all_transitions_set]
QED         

Theorem viterbi_trellis_node_slow_viterbi_trellis_node_no_prev_data:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  viterbi_trellis_node_slow m bs s t = viterbi_trellis_node_no_prev_data m bs s t
Proof
  rpt strip_tac
  >> Cases_on ‘t’ >> gvs[viterbi_trellis_node_slow_def, viterbi_trellis_node_no_prev_data_def, viterbi_trellis_node_def]
  >- (gvs[get_num_errors_calculate_slow_def]
      >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[]
      >- gvs[viterbi_trellis_row_def]
      >> Cases_on ‘s’
      >- gvs[]
      >> gvs[]
      >> gvs[viterbi_trellis_row_def]
      >> gvs[EL_REPLICATE])
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_calculate_slow_get_num_errors_calculate]
  >> gvs[]
  >> gvs[best_origin_slow_is_valid]
  >> gvs[best_origin_slow_best_origin]
  >> gvs[viterbi_trellis_row_def]
  >> gvs[viterbi_trellis_node_def]
QED

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
    MAP (λm. (if 0 < m then EL (m - 1) prior_grid_row else 0) + EL m prior_grid_row + (if m < 9 then EL (m + 1) prior_grid_row else 0)) (COUNT_LIST 10)
End

(* -------------------------------------------------------------------------- *)
(* Testing whether or not example_recursive_grid_row takes an exponential     *)
(* amount of time to compute. It could theoretically take an exponential      *)
(* amount of time if the previous row was substituted in multiple places, and *)
(* expanded out fully multiple times. Each subsequent row would double the    *)
(* amount of time taken because it has to do the computation from the         *)
(* previous row twice.                                                        *)
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
(*Theorem example_recursive_grid_row_time_test:
  example_recursive_grid_row 100 = ARB
Proof
  EVAL_TAC
QED*)

(* -------------------------------------------------------------------------- *)
(* A similar test as above, with a slightly different definition.             *)
(* -------------------------------------------------------------------------- *)
Definition example_recursive_grid_row2_def:
  example_recursive_grid_row2 0 = REPLICATE 10 1 ∧
  example_recursive_grid_row2 (SUC n) =
  MAP (λm. (if 0 < m then EL (m - 1) (example_recursive_grid_row2 n) else 0) + EL m (example_recursive_grid_row2 n) + (if m < 9 then EL (m + 1) (example_recursive_grid_row2 n) else 0)) (COUNT_LIST 10)
End

Theorem example_recursive_grid_row_example_recursive_grid_row2:
  ∀n. example_recursive_grid_row n = example_recursive_grid_row2 n
Proof
  Induct_on ‘n’ >> gvs[example_recursive_grid_row_def, example_recursive_grid_row2_def]
QED

(* -------------------------------------------------------------------------- *)
(* This implementation is much slower, as expected.                           *)
(*                                                                            *)
(* 2: 0.201                                                                   *)
(* 3: 5.443                                                                   *)
(* 4: 145.7                                                                   *)
(* -------------------------------------------------------------------------- *)
(*Theorem example_recursive_grid_row_time_test:
  example_recursive_grid_row2 4 = ARB
Proof
  EVAL_TAC
QED*)

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
Theorem viterbi_trellis_row_test:
  let
    test_row = viterbi_trellis_row example_state_machine test_path 4
  in
    (EL 0 test_row).num_errors = N 3 ∧
    (EL 1 test_row).num_errors = N 3 ∧
    (EL 2 test_row).num_errors = N 2 ∧
    (EL 3 test_row).num_errors = N 4
(*viterbi_trellis_row example_state_machine test_path 4 = ARB*)
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* Prior to making the relevant input calculated at the point at which it is  *)
(* actually needed, resulting in the relevant input being calculated multiple *)
(* times:                                                                     *)
(*                                                                            *)
(* 200: 3.700                                                                 *)(*                                                                            *)
(* After the aforementioned relevant input change:                            *)
(*                                                                            *)(* 200: 9.070                                                                 *)
(* -------------------------------------------------------------------------- *)
(* Theorem viterbi_trellis_row_efficiency_test:
  let
    n = 200;
    n' = n * example_state_machine.output_length
  in
    viterbi_trellis_row example_state_machine (REPLICATE n' T) n = ARB
Proof
  EVAL_TAC
QED*)

(* -------------------------------------------------------------------------- *)
(* Performs one step back through the trellis.                                *)
(*                                                                            *)
(* m: the state machine which generates the trellis                           *)
(* bs: the bitstring being decoded                                            *)
(* s: the state to step back from                                             *)
(* t: the time-step to step back from                                         *)
(*                                                                            *)
(* Only valid for t > 0, since we can't step back at t = 0.                   *)
(* -------------------------------------------------------------------------- *)
(* Note: this requires generating the entire trellis up to this point, which  *)
(* is slow. Repeatedly calling this function should therefore in theory be    *)
(* less efficient than generating the trellis once and then stepping back     *)(* through the thing.                                                         *)
(* -------------------------------------------------------------------------- *)
Definition vd_step_back_def:
  vd_step_back m bs s t =
  let
    trellis_row = viterbi_trellis_row m bs t;
    trellis_node = EL s trellis_row
  in
    THE trellis_node.prev_state
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
(* TODO: Repeatedly calling vd_step_back is slow, because it regenerates the  *)
(* trellis at each step.                                                      *)
(* -------------------------------------------------------------------------- *)
Definition vd_find_optimal_reversed_path_def:
  vd_find_optimal_reversed_path m bs s 0 = [s] ∧
  vd_find_optimal_reversed_path m bs s (SUC t) =
  s :: vd_find_optimal_reversed_path m bs (vd_step_back m bs s (SUC t)) t
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
Theorem vd_find_optimal_reversed_path_test:
  let
    result1 = (vd_find_optimal_reversed_path example_state_machine test_path 0 6);
    result2 = (vd_find_optimal_reversed_path example_state_machine test_path 1 4);
    result3 = (vd_find_optimal_reversed_path example_state_machine test_path 2 4);
    result4 = (vd_find_optimal_reversed_path example_state_machine test_path 3 6);
  in
    (result1 = [0;0;0;2;1;0;0] ∨ result1 = [0;0;1;0;2;1;0] ∨ result1 = [0;0;1;2;1;0;0]) ∧
    (result2 = [1;0;2;1;0] ∨ result2 = [1;2;1;0;0]) ∧
    (result3 = [2;1;0;0;0]) ∧
    (result4 = [3;3;1;0;2;1;0] ∨ result4 = [3;3;1;2;1;0;0])
Proof
  EVAL_TAC
QED

(*
--------------------------------------------------------------------------
*)
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

(* Perhaps this and get_better_origin can be combined somehow.
   In general, perhaps there should be general code for taking the
   argmax of a function over a list. Is that code avaialable somewhere? *)
Definition get_better_final_state_def:
  get_better_final_state last_row s1 s2 = if (EL s1 last_row).num_errors < (EL s2 last_row).num_errors then s1 else s2
End

(* -------------------------------------------------------------------------- *)
(* vd_find_optimal_path, but converted to code form                           *)
(* -------------------------------------------------------------------------- *)
Definition vd_find_optimal_code_def:
  vd_find_optimal_code m bs s t = path_to_code m (vd_find_optimal_path m bs s t)
End

(* -------------------------------------------------------------------------- *)
(* Input: bitstring and state machine                                         *)
(* Output: Most likely original bitstring                                     *)
(* -------------------------------------------------------------------------- *)
(* TODO: This recalculates the whole trellis again, which is already          *)
(* recalculated several times when producing the path back through the        *)
(* trellis                                                                    *)
(* -------------------------------------------------------------------------- *)
Definition vd_decode_def:
  vd_decode m bs =
  let
    max_timestep = (LENGTH bs) DIV m.output_length;
    last_row = viterbi_trellis_row m bs max_timestep;
    best_state = FOLDR (get_better_final_state last_row) 0 (COUNT_LIST m.num_states)
  in
    vd_find_optimal_code m bs best_state max_timestep
End

(*Theorem vd_decode_test:
  let
    decoded_path = vd_decode example_state_machine test_path;
    encoded_decoded_path = vd_encode example_state_machine decoded_path
  in
    decoded_path = ARB ∧
    encoded_decoded_path = ARB ∧
    test_path = ARB ∧
    hamming_distance encoded_decoded_path test_path = ARB                
Proof
  EVAL_TAC
QED*)

Theorem vd_encode_empty[simp]:
  ∀m. vd_encode m [] = []
Proof
  rpt strip_tac
  >> EVAL_TAC
QED

Theorem vd_find_optimal_path_time_zero[simp]:
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

Theorem vd_find_optimal_code_time_zero[simp]:
  ∀m bs s. vd_find_optimal_code m bs s 0 = []
Proof
  rpt strip_tac
  >> gvs[vd_find_optimal_code_def]
QED

Theorem vd_decode_empty[simp]:
  ∀m. vd_decode m [] = []
Proof
  rpt strip_tac
  >> gvs[vd_decode_def, vd_find_optimal_code_def]
QED

(* -------------------------------------------------------------------------- *)
(* See comment for vd_encode_cons                             *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_helper_cons:
  ∀m b bs s.
  vd_encode_helper m (b :: bs) s =
  (vd_step_output m b s) ⧺ (vd_encode_helper m bs (vd_step  m b s))
Proof
  rpt strip_tac
  >> gvs[vd_encode_helper_def]
  >> gvs[vd_encode_state_helper_def]
  >> gvs[vd_step_def, vd_step_record_def, vd_step_output_def]
QED

(* -------------------------------------------------------------------------- *)
(* Can break convolutional encoding up into doing a step, with the rest of    *)
(* the encoding appended on, starting from the appropriate state              *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_cons:
  ∀m b bs. vd_encode m (b :: bs) =
           (vd_step_output m b 0) ⧺ (vd_encode_helper m bs (vd_step m b 0))
Proof
  rpt strip_tac
  >> gvs[vd_encode_def]
  >> gvs[vd_encode_state_def]
  >> PURE_ONCE_REWRITE_TAC[vd_encode_helper_cons]
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* See comment for vd_encode_append                           *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_helper_append:
  ∀m bs cs s.
  vd_encode_helper m (bs ⧺ cs) s =
  vd_encode_helper m bs s ⧺ vd_encode_helper m cs (vd_encode_state_helper m bs s)          
Proof
  gen_tac
  >> Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[APPEND]
  >> gvs[vd_encode_helper_cons]
  >> gvs[vd_encode_state_helper_def]
QED

(* -------------------------------------------------------------------------- *)
(* Can break convolutional encoding up into two halves: doing a bunch of      *)
(* steps from the initial state, then doing a bunch of steps from the state   *)
(* that is reached at this point.                                             *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_append:
  ∀m bs cs.
  vd_encode m (bs ⧺ cs) =
  (vd_encode m bs) ⧺ (vd_encode_helper m cs (vd_encode_state m bs))
Proof
  rpt strip_tac
  >> gvs[vd_encode_def, vd_encode_state_def]
  >> gvs[vd_encode_helper_append]
QED

(* -------------------------------------------------------------------------- *)
(* Can break convolutional encoding up into doing a bunch of steps from the   *)
(* initial state, then doing a final step from the final state.               *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_snoc:
  ∀m b bs. vd_encode m (SNOC b bs) =
           (vd_encode m bs) ⧺ (vd_encode_helper m [b] (vd_encode_state m bs))
Proof
  gvs[SNOC]
  >> gvs[vd_encode_append]
QED

Theorem hamming_distance_cons:
  ∀b bs c cs.
  LENGTH bs = LENGTH cs ⇒
  hamming_distance (b::bs) (c::cs) = (if b = c then 0 else 1) + hamming_distance bs cs
Proof
  rpt strip_tac
  >> gvs[hamming_distance_def]
  >> gvs[add_noise_def]
  >> gvs[bxor_cons]
  >> gvs[hamming_weight_def]
  >> Cases_on ‘b’ >> Cases_on ‘c’ >> gvs[]
QED

Theorem hamming_distance_append_left:
  ∀bs cs ds.
  LENGTH bs + LENGTH cs = LENGTH ds ⇒
  hamming_distance (bs ⧺ cs) ds = hamming_distance bs (TAKE (LENGTH bs) ds) + hamming_distance cs (DROP (LENGTH bs) ds)
Proof
  Induct_on ‘ds’
  >- (Cases_on ‘bs’ >> Cases_on ‘cs’ >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘bs’
  >- gvs[]
  >> gvs[APPEND]
  >> gvs[hamming_distance_cons]
QED

Theorem hamming_distance_append_right:
  ∀bs cs ds.
  LENGTH bs = LENGTH cs + LENGTH ds ⇒
  hamming_distance bs (cs ⧺ ds) = hamming_distance (TAKE (LENGTH cs) bs) cs + hamming_distance (DROP (LENGTH cs) bs) ds
Proof
  metis_tac[hamming_distance_append_left, hamming_distance_symmetric]
QED

Theorem vd_step_output_length[simp]:
  ∀m b s.
  wfmachine m ∧
  s < m.num_states ⇒
  LENGTH (vd_step_output m b s) = m.output_length
Proof
  rpt strip_tac
  >> drule wfmachine_transition_fn_output_length
  >> rpt strip_tac
  >> gvs[vd_step_output_def, vd_step_record_def]
QED

Theorem vd_encode_helper_length[simp]:
  ∀m bs s.
  wfmachine m ∧
  s < m.num_states ⇒
  LENGTH (vd_encode_helper m bs s) = m.output_length * LENGTH bs
Proof
  gen_tac
  >> Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[vd_encode_helper_cons]
  >> gvs[vd_step_output_length]
  >> qmatch_goalsub_abbrev_tac ‘vd_encode_helper _ _ s2’
  >> last_x_assum $ qspec_then ‘s2’ assume_tac
  >> gvs[]
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC [th])
  >> conj_tac
  >- (drule wfmachine_vd_step_is_valid
      >> rpt strip_tac
      >> last_x_assum $ qspecl_then [‘s’, ‘h’] assume_tac
      >> gvs[])
  >> gvs[SUC_ONE_ADD]
QED

Theorem vd_encode_length[simp]:
  ∀m bs.
  wfmachine m ⇒
  LENGTH (vd_encode m bs) = m.output_length * LENGTH bs
Proof
  rpt strip_tac
  >> gvs[vd_encode_def]
  >> DEP_PURE_ONCE_REWRITE_TAC [vd_encode_helper_length]
  >> gvs[]
QED

Theorem vd_step_is_valid[simp]:
  ∀m b s.
  wfmachine m ∧
  s < m.num_states ⇒
  vd_step m b s < m.num_states
Proof
  rpt strip_tac
  >> drule wfmachine_vd_step_is_valid
  >> rpt strip_tac
  >> gvs[vd_step_def, vd_step_record_def]
QED

Theorem vd_encode_state_helper_is_valid[simp]:
  ∀m bs s.
  wfmachine m ∧ 
  s < m.num_states ⇒
  vd_encode_state_helper m bs s < m.num_states
Proof
  gen_tac
  >> Induct_on ‘bs’
  >- (rpt strip_tac
      >> gvs[vd_encode_state_helper_def])
  >> rpt strip_tac
  >> gvs[vd_encode_state_helper_def]
  >> last_x_assum $ qspec_then ‘vd_step m h s’ assume_tac
  >> gvs[vd_step_is_valid]
QED

Theorem vd_encode_state_is_valid[simp]:
  ∀m bs.
  wfmachine m ⇒
  vd_encode_state m bs < m.num_states
Proof
  rpt strip_tac
  >> gvs[vd_encode_state_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[vd_encode_state_helper_is_valid]
QED

Theorem vd_step_output_output_length_0[simp]:
  ∀m b s.
  wfmachine m ∧
  s < m.num_states ∧
  m.output_length = 0 ⇒
  vd_step_output m b s = []
Proof
  rpt strip_tac
  >> drule wfmachine_transition_fn_output_length
  >> rpt strip_tac
  >> EVAL_TAC
  >> gvs[]
QED

Theorem vd_encode_helper_output_length_0[simp]:
  ∀m bs s.
  wfmachine m ∧
  s < m.num_states ∧
  m.output_length = 0 ⇒
  vd_encode_helper m bs s = []
Proof
  gen_tac
  >> Induct_on ‘bs’ >> rpt strip_tac
  >- gvs[vd_encode_helper_def]
  >> gvs[vd_encode_helper_cons]
QED

Theorem vd_encode_output_length_0[simp]:
  ∀m bs s.
  wfmachine m ∧
  m.output_length = 0 ⇒
  vd_encode m bs = []
Proof
  gvs[vd_encode_def]
  >> rpt strip_tac
  >> irule vd_encode_helper_output_length_0
  >> gvs[]
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

Theorem FILTER_EXISTS:
  ∀f bs.
  FILTER f bs ≠ [] ⇔ EXISTS f bs
Proof
  rpt strip_tac 
  >> Induct_on ‘bs’
  >- gvs[]
  >> rpt strip_tac
  >> gvs[FILTER]
  >> Cases_on ‘f h’ >> gvs[]
QED

Theorem FILTER_EXISTS2:
  ∀f bs.
  FILTER f bs = [] ⇔ ¬(EXISTS f bs)
Proof
  PURE_REWRITE_TAC[GSYM FILTER_EXISTS]
  >> gvs[]
QED

(* TODO: Move this to a library *)

fun delete_nth_assumption n = (if (n = 0) then pop_assum kall_tac else pop_assum (fn th => delete_nth_assumption (n - 1) >> assume_tac th))

(* TODO: function for bringing nth assumption to top *)

(*Theorem get_better_origin_foldr:
  ∀m is ps h t f.
    FOLDR (get_better_origin m is ps) h t = f ⇔ MEM f (h::t) ∧ ∀f'. MEM f' (h::t) ⇒ get_num_errors_calculate m is ps 


transition_origin (MIN_SET ARB)  (*(IMAGE (get_num_errors_calculate m is ps) (set (h::t)))*)
Proof
QED*)

(*Theorem get_better_origin_foldr:
                                get_num_errors_calculate m is ps (FOLDR (get_better_origin m is ps)) h ts ≤ get_num_errors_calculate m is ps h
Proof
QED*)

(* -------------------------------------------------------------------------- *)
(* The result of folding get_better_origin over a list is the list itself,    *)
(* since at each stage, the output is equal to one of the inputs.             *)
(* -------------------------------------------------------------------------- *)
Theorem get_better_origin_foldr_mem:
  ∀m bs t ps h ts.
  MEM (FOLDR (get_better_origin m bs t ps) h ts) (h::ts)
Proof
  rpt strip_tac
  >> irule FOLDR_BISWITCH
  >> rpt strip_tac
  >> gvs[get_better_origin_def]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’
  >> gvs[]
QED

Theorem best_origin_is_valid:
  ∀m bs t ps s.
  wfmachine m ∧
  s < m.num_states ⇒
  (best_origin m bs t ps s).origin < m.num_states
Proof
  rpt strip_tac
  >> gvs[best_origin_def]
  >> qmatch_goalsub_abbrev_tac ‘FOLDR fn _ _’
  >> qmatch_goalsub_abbrev_tac ‘FOLDR _ (HD ts)’
  >> qmatch_goalsub_abbrev_tac ‘tran.origin < _’
  (* Use the proof that transition_inverse always returns a valid state
     to simplify to merely needing to prove that t is a member of ts. *)
  >> qsuff_tac ‘MEM tran ts’
  >- (strip_tac
      >> qspecl_then [‘m’, ‘s’] assume_tac transition_inverse_valid
      >> gvs[Abbr ‘ts’]
      >> gvs[EVERY_MEM])
  (* t can only be a member of ts if ts is nonempty, so prove that ts is nonempty, using the fact that transition_inverse is nonempty given a well formed machine and valid state.*)
  >> sg ‘ts ≠ []’
  >- (gvs[Abbr ‘ts’]
      >> gvs[transition_inverse_nonempty])
  (* No longer need the information provided by the exact form of ts. The fact that it is a nonempty bitstring is enough. *)
  >> delete_nth_assumption 2
  (* Use get_better_origin_foldr_mem to finish the proof. Since the function's
     output is always one of the inputs, folding the function over a list
     will always give you a member of that list. *)
  >> unabbrev_all_tac
  >> Cases_on ‘ts’
  >- gvs[]
  >> MEM_DONOTEXPAND_TAC
  >> simp[get_better_origin_foldr_mem]
  >> MEM_DOEXPAND_TAC
  >> PURE_REWRITE_TAC[get_better_origin_foldr_mem]
QED

(* -------------------------------------------------------------------------- *)
(* Prove that each previous state in the trellis is valid.                    *)
(* -------------------------------------------------------------------------- *)
Theorem viterbi_trellis_row_prev_state_valid[simp]:
  ∀m bs t s.
  wfmachine m ∧
  s < m.num_states ∧
  0 < t ⇒
  (EL s (viterbi_trellis_row m bs t)).prev_state ≠ NONE ∧
  THE (EL s (viterbi_trellis_row m bs t)).prev_state < m.num_states
Proof
  (* Handle proving that previous state is not NONE *)
  rpt strip_tac
  >- (Cases_on ‘t’ >> gvs[]
      >> gvs[viterbi_trellis_row_def]
      >> gvs[viterbi_trellis_node_def])
  (* Start of proof that previous state is within the valid range for states *)
  (* Expand definitions, and use abbreviations insted to make it readable *)
  >> Cases_on ‘t’ >> gvs[]
  >> gvs[viterbi_trellis_row_def]
  >> gvs[viterbi_trellis_node_def]
  >> gvs[best_origin_is_valid]   
QED

Theorem vd_find_optimal_reversed_path_length[simp]:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  LENGTH (vd_find_optimal_reversed_path m bs s t) = t + 1
Proof
  (* Induct over t *)
  gen_tac
  >> Induct_on ‘t’ >> rpt strip_tac
  >- EVAL_TAC
  (* Expand out definitions *)
  >> gvs[vd_find_optimal_reversed_path_def, vd_step_back_def]
  (* Deal with the case where the previous state is NONE, so that we can work
     on the more interesting case where there is a preivous state *)
  >> qspecl_then [‘m’, ‘bs’, ‘SUC t’, ‘s’] assume_tac (cj 1 viterbi_trellis_row_prev_state_valid)
  >> gvs[]
  >> qmatch_asmsub_abbrev_tac ‘s' ≠ NONE’
  >> Cases_on ‘s'’ >> gvs[]
  (* Use the inductive hypothesis to finish the proof, leaving open the
     unproven assumption that travelling back to a prior state resulted
     om a valid state.*)
  >> last_x_assum $ qspecl_then [‘bs’, ‘x’] assume_tac
  >> gvs[]
  >> ‘x < m.num_states’ suffices_by decide_tac
  >> pop_assum kall_tac
  (* We just need to prove that travelling back through the trellis
        results in a valid state *)
  >> qspecl_then [‘m’, ‘bs’, ‘(SUC t)’, ‘s’] assume_tac (cj 2 viterbi_trellis_row_prev_state_valid)
  >> gvs[]
QED

Theorem vd_find_optimal_path_length[simp]:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ⇒
  LENGTH (vd_find_optimal_path m bs s t) = t + 1
Proof
  gvs[vd_find_optimal_path_def]
QED

Theorem get_better_final_state_foldr_mem:
  ∀rs h ts.
  MEM (FOLDR (get_better_final_state rs) h ts) (h::ts)
Proof
  rpt strip_tac
  >> irule FOLDR_BISWITCH
  >> rpt strip_tac
  >> gvs[get_better_final_state_def]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* This is already contained in the definition of                             *)
(* vd_find_optimal_reversed_path, but it is good to automatically use it      *)
(* -------------------------------------------------------------------------- *)
Theorem vd_find_optimal_reversed_path_time_zero[simp]:
  ∀m bs s.
  vd_find_optimal_reversed_path m bs s 0 = [s]
Proof
  rpt strip_tac >> EVAL_TAC
QED

Theorem vd_find_optimal_reversed_path_length[simp]:
  ∀m bs s t.
  LENGTH (vd_find_optimal_reversed_path m bs s t) = t + 1
Proof
  Induct_on ‘t’ >> rpt strip_tac >> gvs[]
  >> gvs[vd_find_optimal_reversed_path_def]
QED

Theorem vd_find_optimal_path_length[simp]:
  ∀m bs s t.
  LENGTH (vd_find_optimal_path m bs s t) = t + 1
Proof
  gvs[vd_find_optimal_path_def, vd_find_optimal_reversed_path_length]
QED

Theorem vd_find_optimal_code_length[simp]:
  ∀m bs s t.
  LENGTH (vd_find_optimal_code m bs s t) = t
Proof
  rpt strip_tac
  >> gvs[vd_find_optimal_code_def]
QED

Theorem vd_decode_length[simp]:
  ∀m bs.
  wfmachine m ∧
  divides (LENGTH bs) m.output_length ∧
  m.output_length ≠ 0 ⇒
  LENGTH (vd_decode m bs) = LENGTH bs DIV m.output_length
Proof
  (* Prepare for induction with a stride of the output length.
     Need to expand out the definition of divides, and then put
     all the variables into foralls. *)
  rpt strip_tac
  >> gvs[divides_def]
  >> NTAC 3 (pop_assum mp_tac)
  >> SPEC_ALL_TAC
  (* Start the induction *)
  >> Induct_on ‘q’ >> rpt strip_tac
  >- gvs[] (* Deal with invalid case with output length of 0 *)
  (* expand definition *)
  >> gvs[vd_decode_def]
QED

Theorem vd_find_optimal_path_suc:
  ∀m bs s t.
  vd_find_optimal_path m bs s (SUC t) = SNOC s (vd_find_optimal_path m bs (vd_step_back m bs s (SUC t)) t)
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[vd_find_optimal_path_def]
  >> PURE_REWRITE_TAC[GSYM (cj 2 REVERSE_SNOC_DEF)]
  >> AP_TERM_TAC
  >> gvs[vd_find_optimal_reversed_path_def]
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

Theorem vd_find_optimal_path_nonempty[simp]:
  ∀m bs s t.
  vd_find_optimal_path m bs s t ≠ []
Proof
  rpt strip_tac
  >> gvs[vd_find_optimal_path_def]
  >> Cases_on ‘t’
  >> gvs[vd_find_optimal_reversed_path_def]
QED

Theorem vd_step_back_is_valid[simp]:
  ∀m bs s t.
  wfmachine m ∧
  s < m.num_states ∧
  0 < t ⇒
  vd_step_back m bs s t < m.num_states
Proof
  rpt strip_tac
  >> gvs[vd_step_back_def]
  >> gvs[cj 2 viterbi_trellis_row_prev_state_valid]
QED

Theorem vd_step_record_length[simp]:
  ∀m b s.
  wfmachine m ∧
  s < m.num_states ⇒
  LENGTH ((vd_step_record m b s).output) = m.output_length
Proof
  rpt strip_tac
  >> drule wfmachine_transition_fn_output_length
  >> rpt strip_tac
  >> gvs[vd_step_record_def]
QED

Theorem vd_step_output_length[simp]:
  ∀m b s.
  wfmachine m ∧
  s < m.num_states ⇒
  LENGTH (vd_step_output m b s) = m.output_length
Proof
  gvs[vd_step_record_length, vd_step_output_def]
QED

Theorem length_suc_nonempty[simp]:
  ∀ls n.
  LENGTH ls = SUC n ⇒ ls ≠ []
Proof
  Cases_on ‘ls’ >> gvs[]  
QED

(* Encode: dbs -> ebs via path*)
(* Decode: ebs -> dbs via path *)
(* Code to path: dbs -> path *)
(* Path to code: path -> dbs *)
(* Encode_state: dbs -> state *)

Definition code_to_path_helper_def:
  code_to_path_helper m [] s = [s] ∧
  code_to_path_helper m (b::bs) s =  s::(code_to_path_helper m bs (vd_step m b s))
End

Definition code_to_path_def:
  code_to_path m bs = code_to_path_helper m bs 0
End

Theorem code_to_path_helper_hd:
  ∀m bs s.
  HD (code_to_path_helper m bs s) = s
Proof
  Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[code_to_path_helper_def]
QED

Theorem code_to_path_hd:
  ∀m bs.
  HD (code_to_path m bs) = 0
Proof
  gvs[code_to_path_helper_hd, code_to_path_def]
QED

Theorem code_to_path_helper_null[simp]:
  ∀m bs s.
  ¬NULL (code_to_path_helper m bs s)
Proof
  rpt strip_tac
  >> Cases_on ‘bs’
  >> gvs[code_to_path_helper_def]
QED

Theorem code_to_path_null[simp]:
  ∀m bs.
  ¬NULL (code_to_path m bs)
Proof
  gvs[code_to_path_def, code_to_path_helper_null]
QED

Theorem code_to_path_helper_nonempty[simp]:
  ∀m bs s.
  code_to_path_helper m bs s ≠ []
Proof
  rpt strip_tac
  >> gvs[GSYM NULL_EQ, code_to_path_helper_null]
QED

Theorem code_to_path_nonempty[simp]:
  ∀m bs.
  code_to_path m bs ≠ []
Proof
  gvs[code_to_path_helper_nonempty, code_to_path_def]
QED

Theorem code_to_path_helper_append:
  ∀m bs cs s.
  code_to_path_helper m (bs ⧺ cs) s = (code_to_path_helper m bs s) ⧺ (TL (code_to_path_helper m cs (vd_encode_state_helper m bs s)))
Proof
  Induct_on ‘bs’
  >- (EVAL_TAC
      >> rpt strip_tac
      >> qspecl_then [‘m’, ‘cs’, ‘s’] assume_tac code_to_path_helper_hd
      >> qmatch_goalsub_abbrev_tac ‘TL donotrewrite’
      >> last_x_assum (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
      >> unabbrev_all_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[CONS]
      >> gvs[])
  >> rpt strip_tac
  >> gvs[]
  >> gvs[code_to_path_helper_def]
  >> gvs[vd_encode_state_helper_def]
QED

Theorem code_to_path_helper_snoc:
  ∀m b bs s.
  code_to_path_helper m (SNOC b bs) s = SNOC (vd_step m b (vd_encode_state_helper m bs s)) (code_to_path_helper m bs s)
Proof
  rpt strip_tac
  >> gvs[SNOC]
  >> gvs[code_to_path_helper_append]
  >> gvs[code_to_path_helper_def]
QED

Theorem code_to_path_append:
  ∀m bs cs.
  code_to_path m (bs ⧺ cs) = (code_to_path m bs) ⧺ (TL (code_to_path_helper m cs (vd_encode_state m bs)))
Proof
  rpt strip_tac
  >> gvs[code_to_path_def, code_to_path_helper_append, vd_encode_state_def]
QED

Theorem code_to_path_snoc:
  ∀m b bs.
  code_to_path m (SNOC b bs) = SNOC (vd_step m b (vd_encode_state m bs)) (code_to_path m bs)
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[code_to_path_def]
  >> PURE_REWRITE_TAC[code_to_path_helper_snoc]
  >> gvs[]
  >> gvs[vd_encode_state_def]
QED

Theorem code_to_path_helper_last:
  ∀m bs s.
  LAST (code_to_path_helper m bs s) = (vd_encode_state_helper m bs s)
Proof
  Induct_on ‘bs’ >> rpt strip_tac
  >- EVAL_TAC
  >> gvs[vd_encode_state_helper_def]
  >> gvs[code_to_path_helper_def]
  >> pop_assum $ qspecl_then [‘m’, ‘vd_step m h s’] assume_tac
  >> pop_assum (fn th => gvs[SYM th])
  >> gvs[LAST_DEF]
QED

Theorem code_to_path_last:
  ∀m bs.
  LAST (code_to_path m bs) = (vd_encode_state m bs)
Proof
  gvs[code_to_path_helper_last, code_to_path_def, vd_encode_state_def]
QED

Theorem states_to_transition_input_vd_step:
  ∀m b s.
  wfmachine m ∧
  s < m.num_states ⇒
  states_to_transition_input m s (vd_step m b s) = b
Proof
  rpt strip_tac
  >> Cases_on ‘b’ >> EVAL_TAC
  >> drule wfmachine_transition_fn_from_state_injective
  >> rpt strip_tac
  >> gvs[vd_step_def, vd_step_record_def]
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
  >- (gvs[code_to_path_helper_def])
  >> REVERSE conj_tac
  >- (gvs[code_to_path_helper_def])
  >> gvs[code_to_path_def, vd_encode_state_def]
  >> gvs[code_to_path_helper_def]
  >> gvs[code_to_path_helper_last]
  >> DEP_PURE_ONCE_REWRITE_TAC[states_to_transition_input_vd_step]
  >> gvs[]
  >> irule vd_encode_state_helper_is_valid
  >> gvs[]
QED

Definition path_is_valid_def:
  path_is_valid m ps = ∃bs. code_to_path m bs = ps
End

Definition path_is_valid_from_state_def:
  path_is_valid_from_state m ps s = ∃bs. code_to_path_helper m bs s = ps
End

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

Definition path_is_valid_or_empty_def:
  path_is_valid_or_empty m ps = ((ps = []) ∨ path_is_valid m ps)
End  

Definition vd_can_step_def:
  vd_can_step m s s' = ∃b. vd_step m b s = s' 
End

Definition path_is_connected_def:
  path_is_connected m [] = T ∧
  path_is_connected m (p::[]) = T ∧
  path_is_connected m (p::p'::ps) = (vd_can_step m p p' ∧ path_is_connected m (p'::ps))
End

(* -------------------------------------------------------------------------- *)
(* If there exists a way to step from s to s', then states_to_transition_input*)
(* will return that way.                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem vd_step_states_to_transition_input:
  ∀m s s' b. vd_step m b s = s' ⇒
             vd_step m (states_to_transition_input m s s') s = s'
Proof
  rpt strip_tac
  >> simp[states_to_transition_input_def, vd_step_def, vd_step_record_def]
  >> Cases_on ‘(m.transition_fn <|origin := s; input := F|>).destination ≠ s'’ >> simp[]
  >> Cases_on ‘b’ >> gvs[vd_step_def, vd_step_record_def]
QED

Theorem path_is_valid_first_two_elements:
  ∀m h h' t.
  path_is_valid m (h::h'::t) ⇒ ∃b. vd_step m b h = h'
Proof
  rpt strip_tac
  >> gvs[path_is_valid_def]
  >> gvs[code_to_path_def]
  >> Cases_on ‘bs’
  >- gvs[code_to_path_helper_def]
  >> gvs[code_to_path_helper_def]
  >> Cases_on ‘t'’
  >- (gvs[code_to_path_helper_def]
      >> qexists ‘h''’ >> gvs[])
  >> gvs[code_to_path_helper_def]
  >> qexists ‘h''’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* The suffix "1" is added to distinguish this implication-based version from *)
(* a potential, stronger iff-based one. See the commented out theorem below.  *)
(* -------------------------------------------------------------------------- *)
(*Theorem path_is_valid_cons1:
  ∀m h t.
    t ≠ [] ∧
    path_is_valid m (h::t) ⇒
    path_is_valid m t
Proof
  rpt strip_tac
  >> gvs[path_is_valid_def]
  >> Cases_on ‘bs’
  >- gs[code_to_path_def, code_to_path_helper_def]
  >> gs[code_to_path_def, code_to_path_helper_def]
  >> qexists ‘h'::t'’
  >> gvs[code_to_path_helper_def]
QED*)

(*Theorem path_is_valid_cons:
  ∀m h t.
    path_is_valid m (h::t) ⇔ path_is_valid m t ∧ (t = [] ∨ ∃b. vd_step m b h = HD t)
Proof
  rpt strip_tac
  >> gvs[path_is_valid_def]
  >> EQ_TAC
  >- (rpt strip_tac
      >> Cases_on ‘bs’
QED*)

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

Theorem code_to_path_helper_path_to_code:
  ∀m ps.
  ps ≠ [] ∧
  path_is_connected m ps ⇒
  code_to_path_helper m (path_to_code m ps) (HD ps) = ps
Proof
  rpt strip_tac
  >> Induct_on ‘ps’
  >- gvs[path_is_connected_def]
  >> rpt strip_tac
  >> Cases_on ‘ps’ >> gvs[]
  >- gvs[code_to_path_def, code_to_path_helper_def]
  >> drule path_is_connected_cons1
  >> rpt strip_tac
  >> gvs[]        
  >> gvs[path_to_code_def]
  >> gvs[code_to_path_helper_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[vd_step_states_to_transition_input]
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
  metis_tac[code_to_path_def, code_to_path_helper_path_to_code]
QED

Theorem vd_encode_state_helper_snoc:
  ∀m b bs s.
  vd_encode_state_helper m (SNOC b bs) s = vd_step m b (vd_encode_state_helper m bs s)
Proof
  Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[]
  >> gvs[vd_encode_state_helper_def]
QED

Theorem vd_encode_state_snoc:
  ∀m b bs.
  vd_encode_state m (SNOC b bs) = vd_step m b (vd_encode_state m bs)
Proof
  gvs[vd_encode_state_def, vd_encode_state_helper_snoc]
QED

Theorem code_to_path_helper_vd_can_step_cons:
  ∀m bs p p' ps s.
  code_to_path_helper m bs s = p::p'::ps ⇒
  vd_can_step m p p'
Proof
  rpt strip_tac
  >> Cases_on ‘bs’
  >- gvs[code_to_path_def, code_to_path_helper_def]
  >> gvs[code_to_path_def, code_to_path_helper_def]
  >> Cases_on ‘t’
  >- (gvs[code_to_path_def, code_to_path_helper_def]
      >> gvs[vd_can_step_def]
      >> qexists ‘h’
      >> gvs[])
  >> gvs[code_to_path_helper_def]
  >> gvs[vd_can_step_def]
  >> qexists ‘h’
  >> gvs[]
QED

Theorem code_to_path_helper_vd_can_step:
  ∀m bs p p' ps ps' s.
  code_to_path_helper m bs s = (ps ⧺ [p; p'] ⧺ ps') ⇒
  vd_can_step m p p'
Proof
  Induct_on ‘ps’
  >- (rpt strip_tac
      >> gvs[]
      >> irule code_to_path_helper_vd_can_step_cons
      >> qexistsl [‘bs’, ‘ps'’, ‘s’]
      >> gvs[]
     )
  >> rpt strip_tac
  >> last_x_assum irule
  >> Cases_on ‘bs’
  >- gvs[code_to_path_def, code_to_path_helper_def]
  >> gvs[]
  >> gvs[code_to_path_def, code_to_path_helper_def]
  >> qexistsl [‘t’, ‘ps'’, ‘vd_step m h' h’]
  >> gvs[]
QED

Theorem code_to_path_helper_vd_can_step_snoc:
  ∀m bs p p' ps s.
  code_to_path_helper m bs s  = SNOC p' (SNOC p ps) ⇒
  vd_can_step m p p'
Proof
  rpt strip_tac
  >> irule code_to_path_helper_vd_can_step
  >> qexistsl [‘bs’, ‘ps’, ‘[]’, ‘s’]
  >> gvs[]
QED

Theorem code_to_path_vd_can_step_cons:
  ∀m bs p p' ps.
  code_to_path m bs = p::p'::ps ⇒
  vd_can_step m p p'
Proof
  metis_tac[code_to_path_def, code_to_path_helper_vd_can_step_cons]
QED

Theorem code_to_path_vd_can_step:
  ∀m bs p p' ps ps'.
  code_to_path m bs = (ps ⧺ [p; p'] ⧺ ps') ⇒
  vd_can_step m p p'
Proof
  metis_tac[code_to_path_def, code_to_path_helper_vd_can_step]
QED

Theorem code_to_path_vd_can_step_snoc:
  ∀m bs p p' ps.
  code_to_path m bs = SNOC p' (SNOC p ps) ⇒
  vd_can_step m p p'
Proof
  metis_tac[code_to_path_def, code_to_path_helper_vd_can_step_snoc]
QED

Theorem vd_can_step_vd_step[simp]:
  ∀m b s.
  vd_can_step m s (vd_step m b s)
Proof
  rpt strip_tac
  >> gvs[vd_can_step_def]
  >> qexists ‘b’
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* This proof contains a significant amount of repetition. Perhaps it could   *)
(* be automated?                                                              *)
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

Theorem HD_SNOC:
  ∀l ls.
  HD (SNOC l ls) = if ls = [] then l else HD ls
Proof
  rpt strip_tac
  >> Cases_on ‘ls’ >> gvs[]
QED

Theorem path_is_connected_code_to_path_helper:
  ∀m bs s.
  path_is_connected m (code_to_path_helper m bs s)
Proof
  Induct_on ‘bs’
  >- (rpt strip_tac >> EVAL_TAC)
  >> rpt strip_tac
  >> gvs[code_to_path_helper_def]
  >> gvs[path_is_connected_cons1]
  >> pop_assum $ qspecl_then [‘m’, ‘vd_step m h s’] assume_tac
  >> qmatch_goalsub_abbrev_tac ‘(_::ps)’
  >> Cases_on ‘ps’
  >- gvs[]
  >> gvs[path_is_connected_cons]
  >> Cases_on ‘bs’ >> gvs[code_to_path_helper_def]
QED

Theorem path_is_valid_from_state_path_is_connected:
  ∀m ps s.
  path_is_valid_from_state m ps s ⇔ path_is_connected m ps ∧ ps ≠ [] ∧ HD ps = s
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (rpt strip_tac 
      >- (gvs[path_is_valid_from_state_def]
          >> gvs[path_is_connected_code_to_path_helper])
      >- gvs[path_is_valid_from_state_def]
      >> gvs[path_is_valid_from_state_def]
      >> Cases_on ‘bs’ >> gvs[code_to_path_helper_def])
  >> rpt strip_tac
  >> gvs[path_is_valid_from_state_def]
  >> Induct_on ‘ps’ using SNOC_INDUCT
  >- gvs[]
  >> rpt strip_tac
  >> Cases_on ‘ps’ using SNOC_CASES >> gvs[code_to_path_def, path_is_connected_def, path_is_valid_from_state_def]
  >- (qexists ‘[]’ >> gvs[code_to_path_helper_def])
  >> gvs[path_is_connected_snoc]
  >> gs[vd_can_step_def]
  >> qexists ‘SNOC b bs’
  >> Cases_on ‘l’
  >- (gvs[path_is_connected_def]
      >> Cases_on ‘bs’
      >> gvs[code_to_path_helper_def])
  >> gvs[]
  >> PURE_REWRITE_TAC[GSYM SNOC_APPEND]
  >> PURE_REWRITE_TAC[code_to_path_helper_snoc]
  >> gvs[]
  >> AP_TERM_TAC
  >> qspecl_then [‘m’, ‘bs’, ‘h’] assume_tac code_to_path_helper_last
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

Theorem path_is_connected_code_to_path:
  ∀m bs s.
  path_is_connected m (code_to_path m bs)
Proof
  gvs[path_is_connected_code_to_path_helper, code_to_path_def]
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

Theorem states_to_transition_input_vd_encode_state_snoc:
  ∀m b bs.
  wfmachine m ⇒
  states_to_transition_input m (vd_encode_state m bs) (vd_encode_state m (SNOC b bs)) = b
Proof
  rpt strip_tac
  >> gvs[vd_encode_state_snoc]
  >> gvs[states_to_transition_input_vd_step]
QED

Theorem vd_encode_state_helper_path_to_code:
  ∀m ps s.
  ps ≠ [] ∧
  HD ps = s ∧
  path_is_connected m ps ⇒
  vd_encode_state_helper m (path_to_code m ps) s = LAST ps
Proof
  rpt strip_tac
  >> qspecl_then [‘m’, ‘ps’] assume_tac code_to_path_helper_path_to_code
  >> Cases_on ‘ps’ >> gvs[]
  >> gvs[GSYM code_to_path_helper_last]
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
  >> DEP_PURE_ONCE_REWRITE_TAC[vd_encode_state_helper_path_to_code]
  >> gvs[]
  >> gvs[path_is_valid_path_is_connected]
QED

(*Theorem get_better_origin_foldr_transition_inverse_is_valid:
  ∀m bs prev_row s.
  (FOLDR (get_better_origin m bs prev_row) (HD (transition_inverse m s)) (TL (transition_inverse m s))).origin < m.num_states
Proof
  rpt strip_tac
  >> 
QED*)

Theorem code_to_path_helper_length:
  ∀m bs s.
  LENGTH (code_to_path_helper m bs s) = LENGTH bs + 1
Proof
  Induct_on ‘bs’ >> rpt strip_tac >> gvs[code_to_path_helper_def]
QED

Theorem code_to_path_length:
  ∀m bs.
  LENGTH (code_to_path m bs) = LENGTH bs + 1
Proof
  rpt strip_tac
  >> gvs[code_to_path_def, code_to_path_helper_length] 
QED


Definition get_num_errors_helper_def:
  get_num_errors_helper m rs bs s = hamming_distance rs (vd_encode_helper m bs s)
End
        
(* -------------------------------------------------------------------------- *)
(* The number of errors present if we encoded the input bs with the state     *)(* machine m and compared it to the expected output rs.                       *)
(* -------------------------------------------------------------------------- *)
Definition get_num_errors_def:
  get_num_errors m rs bs = get_num_errors_helper m rs bs 0
End

Theorem get_num_errors_helper_append:
  ∀m rs bs bs' s.
  wfmachine m ∧
  s < m.num_states ∧
  LENGTH rs = (LENGTH bs + LENGTH bs') * m.output_length ⇒
  get_num_errors_helper m rs (bs ⧺ bs') s = get_num_errors_helper m (TAKE (LENGTH bs * m.output_length) rs) bs s + get_num_errors_helper m (DROP (LENGTH bs * m.output_length) rs) bs' (vd_encode_state_helper m bs s) 
Proof
  rpt strip_tac
  >> gvs[get_num_errors_helper_def]
  >> gvs[vd_encode_helper_append]
  >> gvs[hamming_distance_append_right]
QED

Theorem get_num_errors_append:
  ∀m rs bs bs'.
  wfmachine m ∧
  LENGTH rs = (LENGTH bs + LENGTH bs') * m.output_length ⇒
  get_num_errors m rs (bs ⧺ bs') = get_num_errors m (TAKE (LENGTH bs * m.output_length) rs) bs + get_num_errors_helper m (DROP (LENGTH bs * m.output_length) rs) bs' (vd_encode_state m bs)
Proof
  rpt strip_tac
  >> gvs[get_num_errors_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_helper_append]
  >> gvs[]
  >> gvs[vd_encode_state_def]
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

Theorem is_reachable_vd_step:
  ∀m s t b.
  is_reachable m s t ⇒ is_reachable m (vd_step m b s) (SUC t)
Proof
  rpt strip_tac
  >> gvs[is_reachable_def]
  >> qexists ‘SNOC (b) bs’
  >> gvs[]
  >> gvs[vd_encode_state_snoc]
QED

Theorem is_reachable_vd_step_tran:
  ∀m r t.
  is_reachable m r.origin t ⇒ is_reachable m (vd_step_tran m r) (SUC t)
Proof
  rpt strip_tac
  >> gvs[vd_step_tran_def]
  >> irule is_reachable_vd_step
  >> gvs[]
QED

Theorem is_reachable_suc:
  is_reachable m s (SUC t) ⇔ ∃s' b. is_reachable m s' t ∧ vd_step m b s' = s
Proof
  EQ_TAC
  >- (disch_tac
      >> gvs[is_reachable_def]
      >> qexistsl [‘vd_encode_state m (FRONT bs)’, ‘LAST bs’]
      >> conj_tac
      >- (qexists ‘FRONT bs’
          >> gvs[]
          >> gvs[FRONT_LENGTH])
      >> Cases_on ‘bs’ using SNOC_CASES
      >- gvs[]
      >> gvs[vd_encode_state_snoc])
  >> rpt strip_tac
  >> gvs[]
  >> irule is_reachable_vd_step
  >> gvs[]
QED

val is_reachable_suc_vd_step = is_reachable_suc;

Theorem is_reachable_suc_vd_step_tran:
  ∀m s t.
  is_reachable m s (SUC t) ⇔ ∃r. is_reachable m r.origin t ∧ vd_step_tran m r = s
Proof
  rpt strip_tac
  >> gvs[vd_step_tran_def]
  >> gvs[is_reachable_suc]
  >> EQ_TAC
  >- (rpt strip_tac
      >> qexists ‘<| origin := s'; input := b|>’
      >> gvs[])
  >> rpt strip_tac
  >> qexistsl [‘r.origin’, ‘r.input’]
  >> gvs[]
QED

Theorem FOLDR_LEQ:
  ∀s h t (f : α -> infnum).
  MEM s (h::t) ⇒
  f (FOLDR (λx y. if f x ≤ f y then x else y) h t) ≤ f s 
Proof
  rpt strip_tac
  >> Induct_on ‘t’
  >- (rpt strip_tac
      >> gvs[])
  >> rpt strip_tac
  >> MEM_DONOTEXPAND_TAC
  >> Cases_on ‘s = h'’ >> gvs[]
  >- (Cases_on_if_asm >> gvs[]
      >> qmatch_asmsub_abbrev_tac ‘f h' < f v’
      >> gvs[inlt_inlt_F]
     )
  >> qmatch_asmsub_abbrev_tac ‘f v' ≤ f s’
  >> imp_prove
  >- (MEM_DOEXPAND_TAC
      >> with_all_in_goal (PURE_REWRITE_TAC[MEM_CONS_CONS])
      >> MEM_DONOTEXPAND_TAC
      >> gvs[])
  >> gvs[]
  >> Cases_on_if_asm >> gvs[]
  >> metis_tac[inle_TRANS]
QED

Theorem best_origin_slow_get_num_errors_calculate_slow:
  ∀m bs t r s.
  wfmachine m ∧
  s < m.num_states ∧
  MEM r (transition_inverse m s) ⇒
  get_num_errors_calculate_slow m bs t (best_origin_slow m bs t s) ≤ get_num_errors_calculate_slow m bs t r
Proof
  rpt strip_tac
  >> drule_all best_origin_slow_transition_inverse
  >> rpt strip_tac
  >> first_x_assum $ qspecl_then [‘bs’, ‘t’] assume_tac
  >> gvs[best_origin_slow_def]
  >>
  >>
  >> gvs[best_origin_slow_def]
  >> 
  >>
  >> gvs[get_better_origin_slow_def]
QED

(* This is false, because there might be multiple best origins
Theorem best_origin_slow_get_num_errors_calculate_slow:
  ∀m bs t r.
  get_num_errors_calculate_slow m bs t r ≤
  get_num_errors_calculate_slow m bs t
                                (best_origin_slow m bs t (vd_step_tran m r)) ⇔
    r = best_origin_slow m bs t (vd_step_tran m r)
Proof
  rpt strip_tac
  >> REVERSE EQ_TAC
  >- (rpt strip_tac
      >> qmatch_asmsub_abbrev_tac ‘best_origin_slow _ _ _ step’
      >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘t’ >> gvs[get_num_errors_calculate_slow_def]
  >- (gvs[best_origin_slow_def]
     )

QED*)

(* This is false, because there might be multiple best origins *)
(*Theorem best_origin_slow_get_better_origin:
  ∀m bs t r.
       get_better_origin_slow m bs t (best_origin_slow m bs t (vd_step_tran m r)) r = (best_origin_slow m bs t (vd_step_tran m r))
Proof
  rpt strip_tac
  >> gvs[get_better_origin_slow_def]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’ >> gvs[]
  >> gvs[best_origin_slow_get_num_errors_calculate_slow]
        QED*)


(*best_origin_slow m bs (SUC t) (vd_step m b s) *)

Theorem viterbi_trellis_node_slow_num_errors_is_reachable:
  ∀m s t.
  wfmachine m ∧
  s < m.num_states ⇒
  (is_reachable m s t ⇔ (viterbi_trellis_node_slow m [] s t).num_errors ≠ INFINITY)
Proof
  Induct_on ‘t’ >> rpt strip_tac >> gvs[]
  >- (gvs[viterbi_trellis_node_slow_def, get_num_errors_calculate_slow_def]
      >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[])
  >> gvs[viterbi_trellis_node_slow_def]
  >> gvs[get_num_errors_calculate_slow_def]
  >> qmatch_goalsub_abbrev_tac ‘i + N _’
  >> Cases_on ‘i’ >> gvs[]
  >- (CCONTR_TAC
      >> gvs[]
      >> qmatch_asmsub_abbrev_tac ‘best_origin_slow m [] t s'’
      >> last_x_assum $ qspecl_then [‘m’, ‘s'’] assume_tac
      >> gvs[]
      (* Prove the premise of an implication in the assumptions *)
      >> qmatch_asmsub_abbrev_tac ‘prem ⇒ concl’
      >> sg ‘prem’
      >- (unabbrev_all_tac >> gvs[])
      >> gvs[]
      (* *)
      >> gs[is_reachable_suc]
      >> gvs[]
      >> sg ‘∃b. s = vd_step m b s'’
      >- (unabbrev_all_tac
          >> gvs[vd_step_best_origin_slow]
         )
QED


(* -------------------------------------------------------------------------- *)
(* Describe the relationship between the function for calculating the number  *)
(* of errors computationally during a single step of the Viterbi algorithm,   *)
(* and the function for calculating the total number of errors                *)
(*                                                                            *)
(* m: the state machine                                                       *)
(* bs: the input bitstring for which we're finding the code to recreate as    *)
(* closely as possible.                                                       *)
(* s: the state we are aiming to end up in                                    *)
(* t: the time-step we are aiming to end up in                                *)
(* -------------------------------------------------------------------------- *)
Theorem get_num_errors_calculate_get_num_errors:
  ∀m bs s t.
         wfmachine m ∧
         s < m.num_states ∧
         LENGTH bs = t * m.num_states ⇒
         get_num_errors m bs (vd_find_optimal_code m bs s t) = infnum_to_num (get_num_errors_calculate_slow m bs t (best_origin_slow m bs t s))
Proof
  Induct_on ‘t’ >> rpt strip_tac >> gvs[]
  >- (gvs[get_num_errors_def, get_num_errors_helper_def, vd_encode_helper_def]
      >> gvs[get_num_errors_calculate_slow_def]
      >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[]
     )
  
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
(* - Want to prove a stronger statement: for any of the states at any time    *)
(*   step, the viterbi path arriving at this state is optimal, i.e. going     *)
(*   back through the trellis will provide a path that has a shorter hamming  *)
(*   distance to the appropriate portion of the received string than any      *)
(*   other path which arrives at this state.                                  *)
(*                                                                            *)
(* - Can do this by induction on the maximum timestep: if the maximum         *)
(*   timestep is zero, then it is trivial that the trivial path is optimal to *)
(*   any state. If, on the other hand, the maximum time step is SUC k, and we *)
(*   know that the viterbi path arriving at any node at time step k is        *)
(*   optimal, then any viterbi path to the current node will consist of a     *)
(*   path to a previous node, followed by an additional step. By the          *)
(*   inductive hypothesis, the path to the previous node is optimal, and then *)
(*   the fact that I'm choosing from the best choice on the next step will    *)
(*   essentially make the current node optimal. I skimmed over quite a bit,   *)
(*  there, but that's the idea                                                *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* Proof of the more general statement of optimality of the viterbi algorithm *)
(* when arriving at any point.                                                *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem viterbi_correctness_general:
  ∀m bs rs s t.
       wfmachine m ∧
       s < m.num_states ∧
       LENGTH bs = t ∧
       LENGTH rs = m.output_length * t ∧
       vd_encode_state m bs = s ⇒
       get_num_errors m rs (vd_find_optimal_code m rs s t) ≤ get_num_errors m rs bs
Proof
  (* Complete base case and simplify *)
  gen_tac
  >> Induct_on ‘t’
  >- gvs[]
  >> rpt strip_tac
  >> donotexpand_tac
  >> gvs[]
  (* Expand out relevant definitions. *)
  (* These are some of the relevant definitions
     - vd_find_optimal_path_def
     - vd_find_optimal_reversed_path_def
     - vd_step_back_def
     - viterbi_trellis_row_def
     - viterbi_trellis_node_def
     - get_better_origin_def
     - get_num_errors_calculate_def *)
  >> gvs[vd_find_optimal_code_def]
  >> gvs[vd_find_optimal_path_def]
  >> gvs[vd_find_optimal_reversed_path_def]
  >> qmatch_goalsub_abbrev_tac ‘vd_find_optimal_reversed_path _ _ s' _’
  >> gvs[vd_step_back_def]
  >> gvs[viterbi_trellis_row_def]
  >> gvs[viterbi_trellis_node_def]
  >> gvs[GSYM vd_find_optimal_path_def]
  (* For any choice of bs, the encoding of m bs will be some path which
     eventually reaches s. Thus, we can decompose it into ... s'' s.
     The choice of s' was such that it minimizes the number of errors to
     get to the previous state plus the number of errors in the transition
     between s' and s. This is equal to the hamming distance from the
     relevant parts of rs to ... s'' plus the hamming distance from the
     relevant parts of rs to s'' s.*)
  >> qspecl_then [‘m’, ‘bs’] assume_tac path_to_code_code_to_path
  >> gvs[]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
  >> qspecl_then [‘code_to_path m bs’] assume_tac SNOC_LAST_FRONT
  >> Cases_on ‘code_to_path m bs = []’
  >- gvs[]
  >> gvs[]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
  >> gvs[code_to_path_last]
  >> doexpand_tac
  >> first_assum (fn th => PURE_REWRITE_TAC[th])
  >> donotexpand_tac
  (* Split the appended paths apart, so that we can deal with the inductive
     path and the current transition separately. *)
  >> DEP_PURE_REWRITE_TAC[path_to_code_append]
  >> gvs[]
  >> conj_tac
  >- (Cases_on ‘bs’ >> gvs[code_to_path_def, code_to_path_helper_def])
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_append]
  >> gvs[]
  >> conj_tac
  >- gvs[ADD1]
  (* Split the RHS appended paths apart *)
  >> DEP_PURE_ONCE_REWRITE_TAC[get_num_errors_append]
  >> gvs[]
  >> gvs[LENGTH_FRONT]
  >> gvs[PRE_SUB1]
  >> gvs[ADD1]
  >> gvs[code_to_path_length]
  (* Give the components names. *)
  >> qmatch_goalsub_abbrev_tac ‘DROP n’
  >> qmatch_goalsub_abbrev_tac ‘lInd + lStep ≤ rInd + rStep’
  (* lInd + lStep is necessarily better than rInd + rStep, but it is not
     necessarily the case that lInd is better than rInd, nor that lStep
     is better than rStep, because s' is chosen to minimize the total sum
     rather than either individual component.
   *)
  >> 
  
  
QED

Theorem viterbi_correctness:
  ∀m : state_machine.
           ∀bs rs : bool list.
           wfmachine m ∧
           LENGTH rs = m.output_length * LENGTH bs ⇒
           get_num_errors m rs (vd_decode m rs) ≤ get_num_errors m rs bs
Proof
  rpt strip_tac
  >> gvs[vd_decode_def]
  >> qmatch_goalsub_abbrev_tac ‘vd_find_optimal_path m rs s t’
  (* TODO: bs may not lead to the state s, so we cannot immediately apply the
     generalized viterbi correctness theorem here. We must first prove that
     our specific choice of s will give a better result than any other choice
     of s, so that we can deal with cases in which bs leads to another state.
     Then we can finish our proof by showing that for an arbitrary valid state,
     if we consider all paths bs leading to that state, the path which was
     designed to be optimal is, in fact, optimal.*)
  >> irule viterbi_correctness_general
  >> gvs[]
  >> conj_tac
  >- (unabbrev_all_tac
      >> qmatch_goalsub_abbrev_tac ‘FOLDR (get_better_final_state rs') 0 ts’
      >> qspecl_then [‘rs'’, ‘0’, ‘ts’] assume_tac get_better_final_state_foldr_mem
      >> qmatch_goalsub_abbrev_tac ‘s < m.num_states’
      >> Cases_on ‘s’ >> gvs[]
      >> gvs[Abbr ‘ts’]
      >> gvs[MEM_COUNT_LIST])
  >> conj_tac
  >- (unabbrev_all_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[MULT_DIV]
      >> gvs[]
      >> gvs[wfmachine_output_length_greater_than_zero]
     )
  >> conj_tac
  >- (unabbrev_all_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[MULT_DIV]
      >> gvs[]
      >> gvs[wfmachine_output_length_greater_than_zero]
     )
  >> gvs[vd_encode_state_def, vd_encode_state_helper_def]

QED

val _ = export_theory();
