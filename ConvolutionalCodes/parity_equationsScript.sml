open HolKernel Parse boolLib bossLib;

val _ = new_theory "parity_equations";

(* Standard theories *)
open arithmeticTheory
open bitstringTheory;
open listTheory;
open numposrepTheory; (* LENGTH_n2l *)
open logrootTheory; (* LOG2_LE_MONO *)

(* Standard libraries *)
open dep_rewrite;

(* My theories *)
open state_machineTheory;

(* -------------------------------------------------------------------------- *)
(* CONVOLUTIONAL PARITY EQUATION ENCODING                                     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* A parity equation is represented as a bool list. The nth bit is true if    *)
(* the nth bit in the sliding window is used in the linear equation.          *)
(*                                                                            *)
(* A parity equation can be equivalently represented as the same equation     *)
(* with an arbitary number of zeros after it, so any parity equation can be   *)
(* treated as a parity equation of longer length. Therefore, in situations    *)
(* where we are provided with multiple equations of different lengths, pad    *)
(* the shorter parity equations with F's at the end.                          *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Treats a bitstring as a parity equation, and applies it to a sufficiently  *)
(* long bitstring. Unspecified behaviour if the second bitstring isn't        *)
(* sufficiently large.                                                        *)
(*                                                                            *)
(* p::ps represents the bitstring that is being treated as a parity equation. *)
(* bs represents the bitstring that the parity equation is applied to.        *)
(* -------------------------------------------------------------------------- *)
Definition apply_parity_equation_def:
  apply_parity_equation [] bs = F ∧
  apply_parity_equation (p::ps) (b::bs) = ((p ∧ b) ⇎ (apply_parity_equation ps bs))
End

(* -------------------------------------------------------------------------- *)
(* Applies a bunch of parity equations to a bitstring with a sufficiently     *)
(* large window length. Unspecified behaviour if the second bitstring isn't   *)
(* sufficiently large.                                                        *)
(* -------------------------------------------------------------------------- *)
Definition apply_parity_equations_def:
  apply_parity_equations [] bs = [] ∧
  apply_parity_equations (p::ps) bs = (apply_parity_equation p bs)::(apply_parity_equations ps bs)
End

Definition convolve_parity_equations_def:
  convolve_parity_equations ps bs =
  (* Note: if the window length is 0, then LENGTH bs < window_length will
       never be true and thus we will never terminate. Therefore, we also
       terminate if bs = []. *)
  if (LENGTH bs < MAX_LIST (MAP LENGTH ps) ∨ bs = []) then [] else
    let
      step_values = apply_parity_equations ps bs;
      remaining_bitstring = DROP 1 bs;
      remaining_values = convolve_parity_equations ps remaining_bitstring;
    in
      step_values ⧺ remaining_values
Termination
  WF_REL_TAC ‘measure (LENGTH ∘ SND)’
  >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘bs’ >> gvs[]
End

Definition parity_equations_to_state_machine_def:
  parity_equations_to_state_machine ps =
  <|
    num_states := 2 ** (MAX_LIST (MAP LENGTH ps));
    transition_fn := λr.
                       let
                         r_vec = zero_extend (MAX_LIST (MAP LENGTH ps)) (n2v (r.origin))
                       in
                         <|
                           destination := v2n (TL (SNOC r.input r_vec));
                           output := apply_parity_equations ps r_vec
                         |>
    ;
    output_length := LENGTH ps;
  |>
End

(* -------------------------------------------------------------------------- *)
(* Note: There are two LOG2's. One is an overloading for logroot$LOG applied  *)
(* to the value 2, and the other is bit$LOG. I only want to use logroot$LOG,  *)
(* because that one can be evaluated using EVAL_TAC when applied to a         *)
(* constant, whereas the other cannot.                                        *)
(* -------------------------------------------------------------------------- *)

Theorem v2n_lt_imp:
  ∀v l.
    LENGTH v ≤ l ⇒ v2n v < 2 ** l
Proof
  rpt strip_tac
  >> ‘2 ** LENGTH v ≤ 2 ** l’ by gvs[]
  >> ‘v2n v < 2 ** LENGTH v’ by gvs[v2n_lt]
  >> metis_tac[LESS_LESS_EQ_TRANS]
QED

(* -------------------------------------------------------------------------- *)
(* In my opinion, this is a better candidate to be length_zero_extend,        *)
(* largely because it is an unconditional rewrite rule, whereas               *)
(* length_zero_extend is conditional                                          *)
(* -------------------------------------------------------------------------- *)
Theorem length_zero_extend_2:
  ∀bs l.
    LENGTH (zero_extend l bs) = MAX (LENGTH bs) l
Proof
  rpt strip_tac
  >> Induct_on ‘l’ >> gvs[zero_extend_def, PAD_LEFT]
  >> gvs[ADD1]
  >> gvs[MAX_DEF]
QED

Theorem boolify_length:
  ∀a v.
    LENGTH (boolify a v) = LENGTH a + LENGTH v
Proof
  Induct_on ‘v’ >> gvs[boolify_def]
QED

(* Seems relevant: LOG2_PROPERTY *)

Theorem n2v_length:
  ∀n l.
    0 < l ∧
    n < 2 ** l ⇒
    LENGTH (n2v n) ≤ l
Proof
  rpt strip_tac
  >> gvs[n2v_def]
  >> gvs[boolify_length]
  >> gvs[LENGTH_n2l]
  >> rw[]
QED


Theorem asdf:
  parity_equations_to_state_machine [] = ARB
Proof
  PURE_REWRITE_TAC[parity_equations_to_state_machine_def]
  >> simp[]
QED


(* -------------------------------------------------------------------------- *)
(* Prove that the state machine generated from the parity equations is        *)
(* well-formed                                                                *)
(* -------------------------------------------------------------------------- *)
Theorem parity_equations_to_state_machine_wfmachine:
  ∀ps.
    ps ≠ [] ⇒
    wfmachine (parity_equations_to_state_machine ps)
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[wfmachine_def]
  >> conj_tac
  >- gvs[parity_equations_to_state_machine_def]
  >> conj_tac
  >- (rpt strip_tac
      >> gvs[parity_equations_to_state_machine_def]
      >> rename1 ‘r.origin < 2 ** l’
      >> irule v2n_lt_imp
      >> gvs[LENGTH_TL]
      >> gvs[length_zero_extend_2]
      >> gvs[]
            
QED

(* -------------------------------------------------------------------------- *)
(* Prove that the state machine representation of a convolutional code is     *)
(* equivalent to the parity equations representation                          *)
(* -------------------------------------------------------------------------- *)
Theorem parity_equations_to_state_machine_equivalent:
  ∀ps bs.
    convolve ps bs = vd_encode (parity_equations_to_state_machine ps) bs 0
Proof
QED

(* TODO: this uses general state machines, which I no longer use in order to
   reduce maintenance requiements.

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
                       ) : (bool list) gen_transition -> (bool list) gen_transition_destination;
      init := REPLICATE window_length F : (bool list);
      output_length := num_parity_equations : num;
    |>
End
 *)


(* -------------------------------------------------------------------------- *)
(* Unit tests                                                                 *)
(* -------------------------------------------------------------------------- *)

Definition test_parity_equation_def:
  test_parity_equation = [T; T; T]
End

Definition test_parity_equation2_def:
  test_parity_equation2 = [F; T; T]
End

Definition test_parity_equations_def:
  test_parity_equations = [test_parity_equation; test_parity_equation2]
End

Theorem test_apply_parity_equation:
  apply_parity_equation [T; F; T] [F; F; T] = T ∧
  apply_parity_equation [F; F; F] [T; T; T] = F ∧
  apply_parity_equation [T; T; T] [T; T; T] = T ∧
  apply_parity_equation [T; T; T] [T; F; T] = F ∧
  apply_parity_equation [T; T; T; F; F] [T; F; T; F; T] = F ∧
  apply_parity_equation [T; F; T; F; T] [F; F; F; T; T] = T ∧
  apply_parity_equation [T; T; T] [T; F; T; F; T] = F
Proof
  EVAL_TAC
QED

Theorem test_convolutional_parity_encode:
  convolve_parity_equations test_parity_equations [F; F; F; T; T; F; T; F; T; T; T] = [F; F; T; T; F; F; F; T; F; T; T; T; F; T; F; F; T; F]
Proof
  EVAL_TAC
QED

val _ = export_theory();
