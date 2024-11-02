
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
open useful_theoremsTheory;

(* My libraries *)
open useful_tacticsLib;

(* -------------------------------------------------------------------------- *)
(* CONVOLUTIONAL PARITY EQUATION ENCODING                                     *)
(* -------------------------------------------------------------------------- *)

(* TODO: elaborate: what do you mean by "is used in the parity equtaion *)
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
(* long bitstring. If the second bitstring isn't sufficiently large, pads it  *)
(* to the right with zeros.                                                   *)
(*                                                                            *)
(* p::ps represents the bitstring that is being treated as a parity equation. *)
(* bs represents the bitstring that the parity equation is applied to.        *)
(* -------------------------------------------------------------------------- *)
Definition apply_parity_equation_def:
  apply_parity_equation [] bs = F ∧
  apply_parity_equation (p::ps) [] = F ∧
  apply_parity_equation (p::ps) (b::bs) = ((p ∧ b) ⇎ (apply_parity_equation ps bs))
End

(* -------------------------------------------------------------------------- *)
(* Applies a bunch of parity equations to a bitstring with a sufficiently     *)
(* large window length. If the second bitstring isn't sufficiently large,     *)
(* pads it to the right with zeros.                                           *)
(* -------------------------------------------------------------------------- *)
Definition apply_parity_equations_def:
  apply_parity_equations [] bs = [] ∧
  apply_parity_equations (p::ps) bs = (apply_parity_equation p bs)::(apply_parity_equations ps bs)
End

(* -------------------------------------------------------------------------- *)
(* Convolves a list of parity equations over an input bitstring.              *)
(*                                                                            *)
(* Pads the input bitstring to the right with zeroes so that the parity       *)
(* equations can be applied with the left of the window starting at each      *)
(* element. This simplifies the implementation, and it is always possible to  *)
(* drop the last elements that were generated later.                          *)
(* -------------------------------------------------------------------------- *)
Definition convolve_parity_equations_def:
  convolve_parity_equations ps [] = [] ∧
  convolve_parity_equations ps (b::bs) =
  let
    step_values = apply_parity_equations ps (b::bs);
    remaining_values = convolve_parity_equations ps bs;
  in
    step_values ⧺ remaining_values
End

(* -------------------------------------------------------------------------- *)
(* Convolves a list of parity equations over an input bitstring, padding      *)
(* zeros to both the left and right to ensure that the window is valid when   *)
(* applied both in such a way that the rightmost element of the first window  *)
(* is the first element of the string and the leftmost element of the last    *)
(* window is the last element of the string.                                  *)
(*                                                                            *)
(* This ensures that it is equivalent to zero-tailed convolutional encoding,  *)
(* where the input string has zeros appended to it to ensure that the state   *)
(* machine both starts and ends at the zero state.                            *)
(*                                                                            *)
(* Note that the vanilla convolution code already adds zeros to the right, so *)
(* we only need to additionally add zeros to the left.                        *)
(*                                                                            *)
(* In order to avoid having an excessive number of definitions which can get  *)
(* in the way of applying automated simp rules and require additional         *)
(* theorems to be written about them, this definition is added as a simp rule *)
(* so that it will automatically expand out in terms of the basic             *)
(* convolve_parity_equations function. In most circumstances, it ought to be  *)
(* expanded out.                                                              *)
(* -------------------------------------------------------------------------- *)
Definition convolve_parity_equations_padded_def[simp]:
  convolve_parity_equations_padded ps bs = convolve_parity_equations ps (zero_extend (MAX_LIST (MAP LENGTH ps) - 1) bs)
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

Theorem n2v2_2_zero[simp]:
  n2v_2 0 = []
Proof
  gvs[n2v_2_def]
QED

Theorem v2n_n2v_2:
  ∀n.
    v2n (n2v_2 n) = n
Proof
  rpt strip_tac
  >> gvs[n2v_2_n2v]
  >> Cases_on ‘n = 0’ >> gvs[]
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

Theorem apply_parity_equations_length[simp]:
  ∀ps bs.
    LENGTH (apply_parity_equations ps bs) = LENGTH ps
Proof
  rpt strip_tac
  >> Induct_on ‘ps’ >> gvs[apply_parity_equations_def]
QED

(* -------------------------------------------------------------------------- *)
(* Prove that the state machine generated from the parity equations is        *)
(* well-formed                                                                *)
(* -------------------------------------------------------------------------- *)
(* Note: this can be changed to an iff, I think                               *)
(* -------------------------------------------------------------------------- *)
Theorem parity_equations_to_state_machine_wfmachine[simp]:
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
  >> conj_tac
  >- (rpt strip_tac
      >> gvs[parity_equations_to_state_machine_def]
      >> pop_assum mp_tac >> gvs[]
      >> qmatch_goalsub_abbrev_tac ‘SNOC T ls’
      >> Cases_on ‘ls = []’
      >- gvs[]
      >> gvs[v2n_tl]
      >> gvs[v2n_snoc]
      >> sg ‘HD (SNOC T ls) = HD (SNOC F ls)’ >> gvs[]
      >- gvs[HD_SNOC]
      >> DEP_PURE_ONCE_REWRITE_TAC[CANCEL_SUB]
      >> gvs[]
      >> qmatch_goalsub_abbrev_tac ‘P1 ∧ P2’
      >> qsuff_tac ‘P2’ >> gvs[Abbr ‘P1’, Abbr ‘P2’]
      >- (rpt strip_tac
          >> gvs[GSYM ADD1, LE])
      >> rw[]
      >> Cases_on ‘ls’ >> gvs[]
      >> gvs[EXP]
      >> gvs[le_v2n]
     )
  >> conj_tac
  >- (rpt strip_tac
      >> gvs[parity_equations_to_state_machine_def]
     )
  >- (gvs[parity_equations_to_state_machine_def]
      >> Cases_on ‘ps’ >> gvs[]
     )
QED

Theorem apply_parity_equation_empty_l[simp]:
  ∀bs. apply_parity_equation [] bs = F
Proof
  gvs[apply_parity_equation_def]
QED

Theorem apply_parity_equation_empty_r[simp]:
  ∀ps. apply_parity_equation ps [] = F
Proof
  rpt strip_tac
  >> Induct_on ‘ps’ >> gvs[apply_parity_equation_def]
QED

Theorem apply_parity_equations_empty_l[simp]:
  ∀bs.
    apply_parity_equations [] bs = []
Proof
  gvs[apply_parity_equations_def]
QED

Theorem apply_parity_equations_empty_r[simp]:
  ∀ps.
    apply_parity_equations ps [] = REPLICATE (LENGTH ps) F
Proof
  rpt strip_tac
  >> Induct_on ‘ps’
  >- gvs[]
  >> rpt strip_tac
  >> gvs[apply_parity_equations_def]
QED

Theorem convolve_parity_equations_empty_r[simp]:
  ∀ps.
    convolve_parity_equations ps [] = []
Proof
  gvs[convolve_parity_equations_def]
QED

Theorem convolve_parity_equations_empty_l[simp]:
  ∀bs.
    convolve_parity_equations [] bs = []
Proof
  Induct_on ‘bs’ >> gvs[convolve_parity_equations_def]
QED

(* -------------------------------------------------------------------------- *)
(* Note that in the presence of the assumption wfmachine m, m.output_length   *)
(* is equivalent to F, although I keep that theorem separate to this one in   *)
(* order to make the statement of this theorem more clear, and leave open the *)
(* possibility of later redefining well-formedness to allow for machines with *)
(* an output length of 0                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem transition_fn_output_empty[simp]:
  ∀m s b.
    wfmachine m ∧
    s < m.num_states ⇒
    ((m.transition_fn <| origin := s; input := h |>).output = [] ⇔ m.output_length = 0)
Proof
  rpt strip_tac
  >> EQ_TAC >> gvs[]
  >> PURE_REWRITE_TAC[GSYM LENGTH_EQ_0]
  >> rpt strip_tac
  >> gvs[Excl "LENGTH_NIL"]
QED

(* -------------------------------------------------------------------------- *)
(* Note that in the presence of the assumption wfmachine m, m.output_length   *)
(* is equivalent to F, although I keep that theorem separate to this one in   *)
(* order to make the statement of this theorem more clear, and leave open the *)
(* possibility of later redefining well-formedness to allow for machines with *)
(* an output length of 0                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_empty_forall[simp]:
  ∀m bs s.
    wfmachine m ∧
    s < m.num_states ∧
    bs ≠ [] ⇒
    (vd_encode m bs s = [] ⇔ (m.output_length = 0))
Proof
  rpt strip_tac
  >> EQ_TAC >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘bs’ >> gvs[]
  >> gvs[vd_encode_def]
QED

Theorem output_length_nonzero[simp]:
  ∀m.
    wfmachine m ⇒
    (m.output_length = 0 ⇔ F)
Proof
  rpt strip_tac
  >> qspec_then ‘m’ assume_tac wfmachine_output_length_greater_than_zero
  >> gvs[Excl "wfmachine_output_length_greater_than_zero"]
QED

Theorem vd_encode_parity_equations_to_state_machine_empty[simp]:
  ∀bs s.
    vd_encode (parity_equations_to_state_machine []) bs s = []
Proof
  gvs[parity_equations_to_state_machine_def]
  >> Induct_on ‘bs’ >> gvs[vd_encode_def]
QED

Theorem convolve_parity_equations_length:
  ∀bs ps.
    LENGTH (convolve_parity_equations ps bs) = LENGTH ps * LENGTH bs
Proof
  Induct_on ‘bs’ >> rpt strip_tac >> gvs[convolve_parity_equations_def]
  >> gvs[ADD1]
QED

Theorem parity_equations_to_state_machine_output_length[simp]:
  ∀ps.
    (parity_equations_to_state_machine ps).output_length = LENGTH ps
Proof
  rpt strip_tac
  >> gvs[parity_equations_to_state_machine_def]
QED

(*
    Proving the equivalence of the parity equations and state machine versions:
    
.
    If we let % denote junk values and - correspond to meaningful values, we
    essentially want to prove:
.  
    - - - - - - - % % % %   corresponds to   % % % % - - - - - - -
.
    i.e. on the left hand side, we are taking the first few meaningful values,
       and on the right hand side we are dropping the first few junk values.
.
    I originally tried inducting on bs, i.e. the input string, however, this
    did not work because we would essentially have to choose to induct on bs
    from either the left or the right, which would mean that the inductive step
    would take either the left or right part of bs, but this would add a junk
    value on one half and add a meaningful value on the other half, so the
    inductive steps would not be equal in reality.
.
    I then considered inducting on the maximum parity equation degree, because
    at a degree of 1, this has no junk values, and at each increment of the
    degree, we add one junk value to each side. However, it wasn't clear how
    this would allow us to use the inductive hypothesis to prove the indcutive
    step, as there is no clear, simple, relation between the property holding
    for a set of parity equations of a certain degree and the property holing
    for a set of parity equations of lesser degree.
.
    I then considered proving the equivalence of the first
    meaningful value of the LHS with the first meaningful value of the RHS, and
    use this prove the the equivalence of the first two meaningful values of the
    LHS with the first two meaningful values of the RHS, etc. That is, I should
    prove:
.
    TAKE i (convolve_parity_equations ps bs) =
      TAKE i (DROP num_to_drop) (vd_encode m bs 0)
.
    by induction on i, for i between 0 and the appropriate length.
.
    I then decided that it might make more sense to aim to prove the
    equivalence of individual elements, and then use the repeated equivalence
    of individual elements to prove the equivalence of the lists. This would
    simplify the proof by splitting up into these two steps, the equivalence of
    individual elements and the equivalence of the lists, rather than trying to
    prove both at the same time
.
    I then decided maybe it would be a better idea to prove the equivalence of
    blocks which combine all the outputs from the parity equations for a given
    window, as this will essentially split our proof along a sensible boundary:
    firstly, induct over windows, and then, induct over parity equations within
    the window. Indeed, each of our functions is creating the output of the
    entire window at once, so it makes more sense to induct over windows.
*)

(* It's often conceptually simpler to have this definition which calculates
   the ith window of outputs in the output. *)
Definition ith_output_window_def:
  ith_output_window i ps bs = TAKE (LENGTH ps) (DROP (i * LENGTH ps) bs)
End

(* Note: this isn't automaticaly applied as a simp rule if we know
   0 < LENGTH bs instead of bs ≠ []. Perhaps we could add this as an
   alternative assumption leading to the conclusion, using an or statement? *)
Theorem convolve_parity_equations_take[simp]:
  ∀ps bs.
    bs ≠ [] ⇒
    TAKE (LENGTH ps) (convolve_parity_equations ps bs) =
    apply_parity_equations ps bs
Proof
  rpt strip_tac
  >> Cases_on ‘bs’ >> gvs[convolve_parity_equations_def]
  >> gvs[TAKE_APPEND]
QED

Theorem ith_output_window_suc:
  ∀n ps bs.
    ith_output_window (SUC n) ps bs =
    ith_output_window n ps (DROP (LENGTH ps) bs)
Proof
  rpt strip_tac
  >> gvs[ith_output_window_def]
  >> gvs[DROP_DROP_T]
  >> gvs[ADD1, LEFT_ADD_DISTRIB]
QED

Theorem DROP_apply_parity_equations_append[simp]:
  ∀ps bs cs.
    DROP (LENGTH ps) ((apply_parity_equations ps bs) ⧺ cs) =
    cs
Proof
  rpt strip_tac
  >> gvs[DROP_APPEND]
QED

Theorem ith_output_window_apply_parity_equations_append[simp]:
  ∀n ps bs cs.
    ith_output_window n ps ((apply_parity_equations ps bs) ⧺ cs) =
    if n = 0
    then
      apply_parity_equations ps bs
    else
      ith_output_window (n - 1) ps (cs)
Proof
  rpt strip_tac
  >> Cases_on ‘n’ >> gvs[]
  >- gvs[ith_output_window_def, TAKE_APPEND]
  >> gvs[ith_output_window_suc]
QED

Theorem ith_output_window_convolve_parity_equations[simp]:
  ∀i ps bs.
    i < LENGTH bs ⇒
    ith_output_window i ps (convolve_parity_equations ps bs) =
    apply_parity_equations ps (DROP i bs)
Proof
  Induct_on ‘bs’ >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘i’ >> gvs[]
  >- (rpt strip_tac >> gvs[ith_output_window_def])
  >> gvs[convolve_parity_equations_def]
QED

(* head of encode is apply_parity_equations of all zeros followed by first element*)

Theorem lkgfjhew:
  vd_encode (parity_equations_to_state_machine ps) bs 0 =
  apply_parity_equations ps ()
Proof
QED

Theorem ith_output_window_vd_encode_parity_equations_to_state_machine:
  ∀i ps bs.
    i < LENGTH bs ⇒
    ith_output_window (i + MAX_LIST (MAP LENGTH ps) - 1) ps (vd_encode (parity_equations_to_state_machine ps) bs 0) = apply_parity_equations ps (DROP i bs)
Proof
  Induct_on ‘bs’ >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘i’ >> gvs[]
QED

Theorem convolve_parity_equations_window:
  ∀i ps bs.
    i < LENGTH bs ⇒
    ith_output_window i ps (convolve_parity_equations ps bs) =
    ith_output_window (i + MAX_LIST (MAP LENGTH ps) - 1) ps (vd_encode (parity_equations_to_state_machine ps) bs 0)
Proof
  rpt strip_tac
  >> gvs[]
QED

Theorem parity_equations_to_state_machine_equivalent_individual:
  ∀ps bs i.
    (*0 < MAX_LIST (MAP LENGTH ps) ⇒*)
    i < (LENGTH ps * LENGTH bs) - (LENGTH ps) * (MAX_LIST (MAP LENGTH ps) - 1) ⇒
    EL i (convolve_parity_equations ps bs) =
    EL (i + (LENGTH ps) * (MAX_LIST (MAP LENGTH ps) - 1))
       (vd_encode (parity_equations_to_state_machine ps) bs 0)
Proof
  rpt strip_tac
  >> gvs[convolve_parity_equations_def]
QED

(* -------------------------------------------------------------------------- *)
(* Prove that the state machine representation of a convolutional code is     *)
(* equivalent to the parity equations representation                          *)
(* -------------------------------------------------------------------------- *)
Theorem parity_equations_to_state_machine_equivalent:
  ∀ps bs.
    0 < MAX_LIST (MAP LENGTH ps) ⇒
    let
      max_degree = MAX_LIST (MAP LENGTH ps);
      num_to_drop = (LENGTH ps) * (max_degree - 1);
    in
      TAKE ((LENGTH ps) * (LENGTH bs) - num_to_drop)
           (convolve_parity_equations ps bs) =
      DROP num_to_drop (vd_encode (parity_equations_to_state_machine ps) bs 0)
Proof
  gvs[]
  >> rpt strip_tac
  (* Handle the special case of ps = [] now so that we don't have to deal with
       it later. Note: this was more meaningful before adding the assumption
       0 < MAX_LIST (MAP LENGTH ps) *)
  >> Cases_on ‘ps = []’
  >- (rpt strip_tac
      >> gvs[]
     )
  (* Give names to the important parts of the goal*)
  >> qmatch_goalsub_abbrev_tac ‘TAKE nl csl = DROP nr csr’
  (* Handle the special case where the maximum parity equation degree is greater
        than the length of bs. In this special case, the LHS and RHS both reduce
        to [], because there's not enough room to apply the parity equations. *)
  >> Cases_on ‘LENGTH bs < MAX_LIST (MAP LENGTH ps)’
  >- (sg ‘nl = 0’ >> gvs[]
      >- (unabbrev_all_tac
          >> gvs[ADD1]
          >> PURE_REWRITE_TAC[Once MULT_COMM]
          >> gvs[]
         )
      >> unabbrev_all_tac
      >> gvs[]
      >> gvs[parity_equations_to_state_machine_def]
     )
  >> gvs[NOT_LT]
  (* Show that the state machine we are working on is well-formed, so that we
     don't have to re-prove that later. *)
  >> qmatch_asmsub_abbrev_tac ‘vd_encode m bs 0’
  >> sg ‘wfmachine m’
  >- (gvs[Abbr ‘m’]
     )
  (* We have finished handling special cases, now we don't have to worry about
     them whenever they arise during the course of the main proof. *)
  >> unabbrev_all_tac
  >> gvs[]
  
  >> qsuff_tac
     ‘∀i.
        i ≤ LENGTH bs * LENGTH ps - LENGTH ps * (MAX_LIST (MAP LENGTH ps) - 1) ⇒
        TAKE i (convolve_parity_equations ps bs) =
        TAKE i (DROP (LENGTH ps * (MAX_LIST (MAP LENGTH ps) - 1))
                     (vd_encode (parity_equations_to_state_machine ps) bs 0))
     ’

        
  >> Induct_on ‘MAX_LIST (MAP LENGTH ps)’


        
  >> Induct_on ‘LENGTH bs’
  >- gvs[convolve_parity_equations_def, parity_equations_to_state_machine_def,
         vd_encode_def]
  >> rpt strip_tac
  (* Move the SUC's and CONS's out in order to make the conclusion a closer
       match with the inductive hypothesis. *)
  >> simp[convolve_parity_equations_def]
  >> gvs[MULT_SUC]
  (*>> DEP_PURE_ONCE_REWRITE_TAC[LESS_EQ_ADD_SUB]
         >> conj_tac
         >- (unabbrev_all_tac
             >> gvs[ADD1]
             >> PURE_REWRITE_TAC[Once MULT_COMM]
             >> simp[]
            )*)
  >> gvs[TAKE_SUM, TAKE_APPEND, TAKE_LENGTH_ID_rwt, DROP_APPEND, TAKE_APPEND,
         DROP_LENGTH_NIL_rwt]
  >> qmatch_goalsub_abbrev_tac ‘stepL ⧺ indL = _’
  (* The left hand side has been successfully transformed into a form
        which allows us to use the inductive hypothesis. Now work on the RHS *)
  >> qspec_then ‘h::bs’ assume_tac (GSYM APPEND_FRONT_LAST)
  >> gvs[Excl "APPEND_FRONT_LAST"]
  >> pop_assum (fn th => PURE_REWRITE_TAC [Once th])
  >> gvs[vd_encode_append, DROP_APPEND]
  >> 
  (* This is essentially the base case, where the size of the bitstring is
       only just big enough to fit one window of parity equations. *)
  >> Cases_on ‘MAX_LIST (MAP LENGTH ps) = SUC (LENGTH bs)’
  >- (gvs[]
      >> gvs[vd_encode_def, parity_equations_to_state_machine_def]
      >> cheat (* Come back to this later *)
     )
  (* This uses the inductive hypothesis to complete the inductive step *)
                                >> drule_all (iffRL LT_LE)
                                >> rpt strip_tac >> gvs[]
                                >> 
QED

Theorem TODOpaddedequal:

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

Definition test_parity_equations_input_def:
  test_parity_equations_input = [T; F; F; F; T; T; T; T; F; T; F; T]
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
  convolve_parity_equations test_parity_equations
  [F; F; F; T; T; F; T; F; T; T; T] =
  [F; F; T; T; F; F; F; T; F; T; T; T; F; T; F; F; T; F; F; T; T; F]
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

Theorem parity_equations_to_state_machine_vd_encode_test:
  vd_encode (parity_equations_to_state_machine test_parity_equations)
  test_parity_equations_input 0 = ARB
(* [T; T; T; T; T; F; F; F; T; T; F; F; T; F; T; F; F; T; F; T; T; T. F; T]*)
Proof
  EVAL_TAC
QED

Theorem parity_equations_to_state_machine_equivalent_test:
  ∀bs.
    LENGTH bs < 8 ⇒
    convolve_parity_equations test_parity_equations bs =
    vd_encode (parity_equations_to_state_machine test_parity_equations) bs 0
Proof
  rpt strip_tac
  >> Cases_on ‘bs’
  >- EVAL_TAC
  >> Cases_on ‘t’
  >- (Cases_on ‘h’ >> EVAL_TAC)
  >> Cases_on ‘t'’
  >- (Cases_on ‘h’ >> EVAL_TAC)
  >> Cases_on ‘t’
  >- (Cases_on ‘h’ >> EVAL_TAC)
  >> Cases_on ‘t'’
  >- (Cases_on ‘h’ >> EVAL_TAC)
  >> Cases_on ‘t’
  >- (Cases_on ‘h’ >> EVAL_TAC)
  >> Cases_on ‘t'’
  >- (Cases_on ‘h’ >> EVAL_TAC)
  >> Cases_on ‘t’
  >- (Cases_on ‘h’ >> EVAL_TAC)
  >> Cases_on ‘t'’
  >- (Cases_on ‘h’ >> EVAL_TAC)
QED

val _ = export_theory();
