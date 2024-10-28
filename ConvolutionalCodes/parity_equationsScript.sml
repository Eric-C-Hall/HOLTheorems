open HolKernel Parse boolLib bossLib;

val _ = new_theory "parity_equations";

(* Standard theories *)
open arithmeticTheory
open listTheory;
open rich_listTheory;

(* Less commonly used standard theories *)
open logrootTheory; (* LOG2_LE_MONO *)
open numposrepTheory; (* LENGTH_n2l *)
open bitstringTheory;

(* Standard libraries *)
open dep_rewrite;

(* My theories *)
open state_machineTheory;
open parity_equations_helperTheory;

(* My libraries *)
open donotexpandLib;

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

(* -------------------------------------------------------------------------- *)
(* n2v chooses n2v 0 to be [F], however, this makes many proofs messy, because*)
(* this is the only number it creates with a leading F; it is treating 0 in a *)
(* very special way. My version (called n2v_2) chooses n2v 0 to be [], which  *)
(* is more consistent with how all the other numbers have their leading       *)
(* zeroes/F's removed, and leads to many nicer proofs.                        *)
(*                                                                            *)
(* One advantage is that it allows the state machine converted from parity    *)
(* equations to be a valid state machine even if all input parity equations   *)
(* have length 0 (or at least I think it does. It certainly removes some      *)
(* barriers.) Another advantage is that it ensures that the equation          *)
(* LENGTH (n2v_2 n) ≤ 2 **                                                    *)
(*                                                                            *)
(* We use big-endian because to a mathematician that is more natural,         *)
(* although this may mean some definitions are less natural.                  *)
(*                                                                            *)
(* Disadvantage of this definition: errant SUC. However, this is still better *)
(* than using if n = 0 then [] else ... <recursive call> ..., because the     *)
(* if-then-else definition has the issue that when used as a rewrite rule, it *)
(* will enter an infinite loop of rewrites.                                   *)
(* -------------------------------------------------------------------------- *)
Definition n2v_2_def:
  n2v_2 0 = [] ∧
  n2v_2 (SUC n) = SNOC ((SUC n) MOD 2 = 1) (n2v_2 ((SUC n) DIV 2))
End

Definition parity_equations_to_state_machine_def:
  parity_equations_to_state_machine ps =
  <|
    num_states := 2 ** (MAX_LIST (MAP LENGTH ps));
    transition_fn := λr.
                       let
                         r_vec = zero_extend (MAX_LIST (MAP LENGTH ps)) (n2v_2 (r.origin))
                       in
                         <|
                           destination := v2n (TL (SNOC r.input r_vec));
                           output := apply_parity_equations ps r_vec
                         |>
    ;
    output_length := LENGTH ps;
  |>
End

(* Note: this can have issues where when used as a rewrite rule, it will enter
   an infinite loop of rewrites, which is why it isn't used as the original
   definition. However, it's still useful if the input isn't of the form
   (SUC n) or of the form 0, and we still want to expand the function anyway. *)
Theorem n2v_2_expand:
  ∀n.
    n2v_2 n = if n = 0 then [] else SNOC (n MOD 2 = 1) (n2v_2 (n DIV 2))
Proof
  Cases_on ‘n’
  >> gvs[n2v_2_def]
QED

(* -------------------------------------------------------------------------- *)
(* These four theorems are probably a little messy: ADD_DIV_LEFT_EQ,          *)
(* ADD_DIV_RIGHT_EQ, SUC_SUC_DIV_2, DIV_2_0. I say this because they are      *)
(* strictly less general than ADD_DIV_ADD_DIV. However, I found it difficult  *)
(* to use a more general theorem like ADD_DIV_ADD_DIV directly, so maybe they *)
(* are useful anyway.                                                         *)
(* -------------------------------------------------------------------------- *)
Theorem ADD_DIV_LEFT_EQ:
  ∀n m.
    0 < m ⇒
    (m + n) DIV m = n DIV m + 1
Proof
  rpt strip_tac
  >> ‘m = 1 * m’ by gvs[]
  >> pop_assum (fn th => PURE_REWRITE_TAC[Once th])
  >> gvs[ADD_DIV_ADD_DIV]
QED

Theorem ADD_DIV_RIGHT_EQ:
  ∀n m.
    0 < m ⇒
    (n + m) DIV m = n DIV m + 1
Proof
  rpt strip_tac
  >> gvs[ADD_COMM, ADD_DIV_LEFT_EQ]
QED

Theorem SUC_SUC_DIV_2:
  ∀n.
    SUC (SUC n) DIV 2 = (n DIV 2) + 1
Proof
  rpt strip_tac
  >> gvs[ADD1]
  >> gvs[ADD_DIV_RIGHT_EQ]
QED

Theorem DIV_2_0:
  ∀n.
    n DIV 2 = 0 ⇔ n = 0 ∨ n = 1
Proof
  rpt strip_tac
  >> REVERSE EQ_TAC >> gvs[]
  >- (rw[] >> EVAL_TAC)
  >> rpt strip_tac
  >> Cases_on ‘n’ >> gvs[]
  >> Cases_on ‘n'’ >> gvs[]
  >> gvs[SUC_SUC_DIV_2]
QED

Theorem boolify_acc:
  ∀a v.
    boolify a v = boolify [] v ⧺ a
Proof
  Induct_on ‘v’ >> rpt strip_tac >> gvs[]
  >- EVAL_TAC
  >> PURE_REWRITE_TAC[boolify_def]
  >> last_assum $ qspec_then ‘(h ≠ 0)::a’ assume_tac
  >> last_x_assum $ qspec_then ‘[h ≠ 0]’ assume_tac
  >> gvs[]
QED

Theorem n2v_2_n2v:
  ∀n.
    n2v_2 n = (if n = 0 then [] else n2v n)
Proof
  rpt strip_tac
  >> rw[n2v_2_def]
  >> completeInduct_on ‘n’
  >> rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[n2v_2_expand]
  >> rw[]
  >> last_x_assum $ qspec_then ‘n DIV 2’ assume_tac
  >> gvs[]
  >> Cases_on ‘n DIV 2 = 0’ >> gvs[]
  >- (gvs[DIV_2_0]
      >> EVAL_TAC
     )
  >> gvs[n2v_def]
  >> irule EQ_SYM
  >> PURE_REWRITE_TAC[Once n2l_def]
  >> gvs[]
  >> rw[]
  >- (Cases_on ‘n’ >> gvs[]
      >> Cases_on ‘n'’ >> gvs[])
  >> gvs[boolify_def]
  >> qspec_then ‘[n MOD 2 ≠ 0]’ assume_tac boolify_acc
  >> gvs[]
  >> Cases_on ‘n MOD 2’ >> gvs[]
  >> Cases_on ‘n'’ >> gvs[]
  >> gvs[ADD1]
  >> ‘n MOD 2 < 2’ by gvs[]
  >> ‘n'' + 2 < 2’ by gvs[]
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Prove that the state machine generated from the parity equations is        *)
(* well-formed                                                                *)
(* -------------------------------------------------------------------------- *)
Theorem parity_equations_to_state_machine_wfmachine:
  ∀ps.
    0 < MAX_LIST (MAP LENGTH ps) ⇒
    wfmachine (parity_equations_to_state_machine ps)
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[wfmachine_def]
  >> conj_tac
  >- gvs[parity_equations_to_state_machine_def]
  >> conj_tac
  >- (rpt strip_tac
      >> gvs[parity_equations_to_state_machine_def]
      >> qmatch_asmsub_abbrev_tac ‘r.origin < 2 ** l’
      >> irule v2n_lt_imp
      >> gvs[LENGTH_TL]
      >> gvs[length_zero_extend_2]
      >> irule n2v_length_le
      >> gvs[]
     )
  >> conj_tac
  >- (rpt strip_tac
      >> gvs[parity_equations_to_state_machine_def]
      >> qexistsl [‘v2n (F::(FRONT (n2v s)))’, ‘LAST (n2v s)’]
      >> conj_tac
      >- (
       )
      >> gvs[n2v_v2n]
            
            
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

(* -------------------------------------------------------------------------- *)
(* We want to be sure that n2v_2 is evaluable                                 *)
(* -------------------------------------------------------------------------- *)
Theorem n2v_2_test:
  n2v_2 22 = [T; F; T; T; F]
Proof
  EVAL_TAC
QED

val _ = export_theory();
