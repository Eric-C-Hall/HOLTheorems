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
open bitTheory;

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

Theorem n2v_2_length_le:
  ∀n l.
    n < 2 ** l ⇒ LENGTH (n2v_2 n) ≤ l
Proof
  rpt strip_tac
  >> gvs[n2v_2_n2v]
  >> Cases_on ‘n = 0’ >> gvs[]
  >> DEP_PURE_ONCE_REWRITE_TAC[n2v_length_le]
  >> gvs[]
  >> Cases_on ‘l’ >> gvs[]
QED

Theorem v2n_tl:
  ∀bs.
    bs ≠ [] ⇒
    v2n (TL bs) = (v2n bs) - (if (HD bs) then 2 ** (LENGTH bs - 1) else 0)
Proof
  rpt strip_tac
  >> Cases_on ‘bs’ >> gvs[]
  >> gvs[v2n]
  >> rw[]
QED

Theorem v2n_empty[simp]:
  v2n [] = 0
Proof
  gvs[v2n]
QED

Theorem v2n_append:
  ∀bs bs'.
    v2n (bs ⧺ bs') = 2 ** (LENGTH bs') * (v2n bs) + v2n bs'
Proof
  rpt strip_tac
  >> Induct_on ‘bs’
  >- gvs[]
  >> rpt strip_tac
  >> gvs[v2n]
  >> rw[]
  >> gvs[EXP_ADD]
QED

Theorem v2n_snoc:
  ∀b bs.
    v2n (SNOC b bs) = 2 * (v2n bs) + if b then 1 else 0
Proof
  gvs[SNOC_APPEND]
  >> gvs[v2n_append]
  >> rpt strip_tac
  >> rw[v2n]   
QED

Theorem v2n_n2v_2:
  ∀n.
    v2n (n2v_2 n) = n
Proof
  rpt strip_tac
  >> gvs[n2v_2_n2v]
  >> Cases_on ‘n = 0’ >> gvs[]
QED

Theorem v2n_front:
  ∀v.
    v ≠ [] ⇒
    v2n (FRONT v) = (v2n v) DIV 2
Proof
  rpt strip_tac
  >> sg ‘v2n v = v2n ((FRONT v) ⧺ [LAST v])’
  >- (gvs[APPEND_FRONT_LAST])
  >> gvs[]
  >> gvs[v2n_append]
  >> Cases_on ‘LAST v’ >> gvs[v2n]
QED

Theorem last_n2v_2[simp]:
  ∀n.
    n ≠ 0 ⇒
    (if LAST (n2v_2 n) then 1n else 0n) = n MOD 2
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[n2v_2_expand]
  >> Cases_on ‘n’ >> gvs[]
  >> qmatch_goalsub_abbrev_tac ‘_ = m’
  >> Cases_on ‘m’ >> gvs[]
  >> Cases_on ‘n’ >> gvs[]
  >> gvs[ADD1]
  >> qspecl_then [‘n' + 1’, ‘2’] assume_tac MOD_LESS
  >> gvs[]
QED

Theorem n2v2_2_zero[simp]:
  n2v_2 0 = []
Proof
  gvs[n2v_2_def]
QED

Theorem zero_extend_empty[simp]:
  ∀n.
    zero_extend n [] = REPLICATE n F
Proof
  rpt strip_tac
  >> Induct_on ‘n’
  >- EVAL_TAC
  >> gvs[zero_extend_suc, REPLICATE]
QED

Theorem v2n_suc_F[simp]:
  ∀v.
    v2n (F::v) = v2n v
Proof
  rpt strip_tac
  >> gvs[v2n]
QED

Theorem v2n_replicate_f[simp]:
  ∀n.
    v2n (REPLICATE n F) = 0
Proof
  rpt strip_tac
  >> Induct_on ‘n’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Prove that the state machine generated from the parity equations is        *)
(* well-formed                                                                *)
(* -------------------------------------------------------------------------- *)
Theorem parity_equations_to_state_machine_wfmachine:
  ∀ps.
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
      >> irule n2v_2_length_le
      >> gvs[]
     )
  >> conj_tac
  >- (rpt strip_tac
      >> gvs[parity_equations_to_state_machine_def]
      >> Cases_on ‘s = 0’
      >- (gvs[]
          >> qexistsl [‘0’, ‘F’]
          >> gvs[]
         )
      >> qexistsl [‘v2n (FRONT (F::(n2v_2 s)))’, ‘LAST (n2v_2 s)’]
      >> conj_tac
      >- (irule v2n_lt_imp
          >> gvs[LENGTH_FRONT, LENGTH_CONS]
          >> irule n2v_2_length_le
          >> gvs[]
         )
      >> gvs[v2n_tl]
      >> qmatch_goalsub_abbrev_tac ‘_ - n’
      >> gvs[v2n_snoc]
      >> gvs[v2n_zero_extend]
      >> gvs[v2n_n2v_2]
      >> gvs[v2n_front]
      >> gvs[v2n_n2v_2]
      >> gvs[DIV_MULT_THM2]
      >> DEP_PURE_ONCE_REWRITE_TAC[SUB_ADD]
      >> gvs[MOD_LESS_EQ]
      >> sg ‘n = 0’ >> gvs[]
      >> unabbrev_all_tac
      >> rw[]
      >> pop_assum mp_tac >> gvs[]
      >> qmatch_asmsub_abbrev_tac ‘s < 2 ** l’
      >> qsuff_tac ‘LENGTH (n2v_2 (s DIV 2)) < l’
      >- (disch_tac
          >> Cases_on ‘l’ >> gvs[]
          >> gvs[zero_extend_suc])
      >> drule n2v_2_length_le
      >> sg ‘s DIV 2 < 2 ** (l - 1)’
      >- (gvs[DIV_LT_X]
          >> gvs[ADD1]
          >> Cases_on ‘l’ >> gvs[ADD1]
         )
      >> drule n2v_2_length_le
      >> gvs[LESS_EQ, ADD1]
      >> rpt strip_tac
      >> Cases_on ‘l = 0’ >> gvs[])
      
             
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
