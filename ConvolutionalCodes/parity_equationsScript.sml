open HolKernel Parse boolLib bossLib;

(* TODO: In many instances, it may be possible to remove or weaken the
   precondition 0 < MAX_LIST (MAP LENGTH ps) - 1. This is because this
   precondition has been weakened to 0 < LENGTH ps in the proof of the
   well-formedness of the state machine derived from parity equations. This was
   possible due to a weakening of the definition of well-formedness, where we
   no longer require that the transitions from a state arrive at different
   states. I should check to make sure that this precondition has been
   replaced by a weaker precondition where possible *)

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
open ConseqConv;

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

Overload window_length = “\m. MAX_LIST (MAP LENGTH m)”

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
  apply_parity_equation (p::ps) (b::bs) =
  ((p ∧ b) ⇎ (apply_parity_equation ps bs))
End

(* -------------------------------------------------------------------------- *)
(* Applies a bunch of parity equations to a bitstring with a sufficiently     *)
(* large window length. If the second bitstring isn't sufficiently large,     *)
(* pads it to the right with zeros.                                           *)
(* -------------------------------------------------------------------------- *)
Definition apply_parity_equations_def:
  apply_parity_equations [] bs = [] ∧
  apply_parity_equations (p::ps) bs =
  (apply_parity_equation p bs)::(apply_parity_equations ps bs)
End

(* -------------------------------------------------------------------------- *)
(* Convolves a list of parity equations over an input bitstring.              *)
(*                                                                            *)
(* The parity equation is first applied to the first n elements of the input, *)
(* rather than padding to the left with zeroes.                               *)
(*                                                                            *)
(* Treats the input as though it had been padded to the right with zeroes.    *)
(* This simplifies the implementation, because it allows us to terminate      *)
(* when we completely run out of inputs and are left with the empty input,    *)
(* rather than having to use an if-statement or something to terminate early  *)
(* when there aren't enough inputs left to fill an entire window.             *)
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
  convolve_parity_equations_padded ps bs =
  convolve_parity_equations
  ps (REPLICATE (MAX_LIST (MAP LENGTH ps) - 1) F ⧺ bs)
End

(* -------------------------------------------------------------------------- *)
(* bitstringTheory.n2v chooses n2v 0 to be [F]. This makes many proofs messy, *)
(* because this is the only number it creates with a leading F; it is         *)
(* treating 0 in a very special way.                                          *)
(* My version (called parity_equationsTheory.n2v) chooses n2v 0 to be [],     *)
(* which is more consistent with how all the other numbers have their leading *)
(* zeroes/F's removed, and leads to many nicer theorems and proofs.           *)
(*                                                                            *)
(* We use big-endian, because that's how binary numbers are usually written   *)
(* in English.                                                                *)
(*                                                                            *)
(* In the inductive case, we deconstruct our input using SUC to ensure it is  *)
(* nonzero. Unfortunately we have to reconstruct our input using SUC on the   *)
(* right hand side. This deconstructing and reconstructing process is a bit   *)
(* of a waste of time, but necessary to ensure that the number is nonzero.    *)
(* It is also better than using if n = 0 then [] else <recursive call>,       *)
(* because the if-then-else definition has the issue that when used as a      *)
(* rewrite rule, it will enter an infinite loop of rewrites.                  *)
(* -------------------------------------------------------------------------- *)
Definition n2v_def:
  n2v 0 = [] ∧
  n2v (SUC n) = SNOC ((SUC n) MOD 2 = 1) (n2v ((SUC n) DIV 2))
End

Definition parity_equations_to_state_machine_def:
  parity_equations_to_state_machine ps =
  <|
    num_states := 2 ** (MAX_LIST (MAP LENGTH ps) - 1);
    transition_fn :=
    λ(s, b).
      let
        s_vec = zero_extend (MAX_LIST (MAP LENGTH ps) - 1) (n2v s);
        window = s_vec ⧺ [b];
        new_vec = TL (window);
      in
        (v2n new_vec, apply_parity_equations ps window)
    ;
    output_length := LENGTH ps;
  |>
End

(* Automatically appply this obvious simplification *)
Theorem parity_equations_to_state_machine_num_states[simp]:
  ∀ps.
    (parity_equations_to_state_machine ps).num_states =
    2 ** (MAX_LIST (MAP LENGTH ps) - 1)
Proof
  gvs[parity_equations_to_state_machine_def]
QED

(* Automatically appply this obvious simplification *)
Theorem parity_equations_to_state_machine_output_length[simp]:
  ∀ps.
    (parity_equations_to_state_machine ps).output_length = LENGTH ps
Proof
  gvs[parity_equations_to_state_machine_def]
QED

(* Note: this can have issues where when used as a rewrite rule, it will enter
   an infinite loop of rewrites, which is why it isn't used as the original
   definition. However, it's still useful if the input isn't of the form
   (SUC n) or of the form 0, and we still want to expand the function anyway. *)
Theorem n2v_expand:
  ∀n.
    n2v n = if n = 0 then [] else SNOC (n MOD 2 = 1) (n2v (n DIV 2))
Proof
  Cases_on ‘n’
  >> gvs[n2v_def]
QED

Theorem n2v_bitstring_n2v:
  ∀n.
    n2v n = (if n = 0 then [] else bitstring$n2v n)
Proof
  rpt strip_tac
  >> rw[n2v_def]
  >> completeInduct_on ‘n’
  >> rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[n2v_expand]
  >> rw[]
  >> last_x_assum $ qspec_then ‘n DIV 2’ assume_tac
  >> gvs[]
  >> Cases_on ‘n DIV 2 = 0’ >> gvs[]
  >- (gvs[DIV_2_0]
      >> EVAL_TAC
     )
  >> gvs[bitstringTheory.n2v_def]
  >> irule EQ_SYM
  >> PURE_REWRITE_TAC[Once n2l_def]
  >> gvs[]
  >> rw[]
  >- (Cases_on ‘n’ >> gvs[]
      >> Cases_on ‘n'’ >> gvs[])
  >> gvs[boolify_def]
  >> qspec_then ‘[n MOD 2 ≠ 0]’ assume_tac boolify_acc
  >> gvs[]
  >> Cases_on ‘n MOD 2’ >> gvs[SNOC_APPEND]
  >> qpat_x_assum ‘_ = boolify _ _’ kall_tac
  >> qpat_x_assum ‘∀v._’ kall_tac
  >> qpat_x_assum ‘¬(n < 2)’ kall_tac
  >> sg ‘n MOD 2 = 0 ∨ n MOD 2 = 1’
  >- (‘n MOD 2 < 2’ by gvs[]
      >> Cases_on ‘n MOD 2’ >> gvs[]
     )
  >> gvs[]
QED

Theorem n2v_length_le:
  ∀n l.
    n < 2 ** l ⇒ LENGTH (n2v n) ≤ l
Proof
  rpt strip_tac
  >> gvs[n2v_bitstring_n2v]
  >> Cases_on ‘n = 0’ >> gvs[]
  >> DEP_PURE_ONCE_REWRITE_TAC[bitstring_n2v_length_le]
  >> gvs[]
  >> Cases_on ‘l’ >> gvs[]
QED

Theorem n2v2_2_zero[simp]:
  n2v 0 = []
Proof
  gvs[n2v_def]
QED

Theorem v2n_n2v[simp]:
  ∀n.
    v2n (n2v n) = n
Proof
  rpt strip_tac
  >> gvs[n2v_bitstring_n2v]
  >> Cases_on ‘n = 0’ >> gvs[]
QED

Theorem last_n2v[simp]:
  ∀n.
    n ≠ 0 ⇒
    (if LAST (n2v n) then 1n else 0n) = n MOD 2
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[n2v_expand]
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

Theorem n2v_empty[simp]:
  ∀n.
    n2v n = [] ⇔ n = 0
Proof
  rpt strip_tac
  >> EQ_TAC >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘n’ >> gvs[n2v_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: This theorem is designed to support legacy behaviour, specifically,  *)
(* a change from the precondition 0 < MAX_LIST (MAP LENGTH ps) - 1 to the     *)
(* precondition 0 < LENGTH ps. This legacy behaviour should probably be fixed *)
(* and this theorem should be deleted                                         *)
(* -------------------------------------------------------------------------- *)
Theorem legacy_precondition[simp]:
  ∀ps.
    0 < MAX_LIST (MAP LENGTH ps) ⇒
    0 < LENGTH ps
Proof
  rpt strip_tac
  >> Cases_on ‘ps’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Prove that the state machine generated from the parity equations is        *)
(* well-formed                                                                *)
(* -------------------------------------------------------------------------- *)
(* Note: this can be changed to an iff, I think                               *)
(* -------------------------------------------------------------------------- *)
Theorem parity_equations_to_state_machine_wfmachine[simp]:
  ∀ps.
    0 < LENGTH ps ⇒
    wfmachine (parity_equations_to_state_machine ps)
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[wfmachine_def]
  >> conj_tac
  >- gvs[parity_equations_to_state_machine_def]
  >> conj_tac
  >- (rpt strip_tac
      >> gvs[parity_equations_to_state_machine_def]
      (*>> qmatch_asmsub_abbrev_tac ‘FST r < 2 ** l’*)
      >> irule v2n_lt_imp
      >> gvs[LENGTH_TL]
      >> gvs[length_zero_extend_2]
      >> irule n2v_length_le
      >> gvs[]
     )
  >> conj_tac
  >- (rpt strip_tac
      >> gvs[parity_equations_to_state_machine_def]
      >> PURE_REWRITE_TAC[GSYM SNOC_APPEND]
      >> Cases_on ‘s = 0’
      >- (gvs[]
          >> qexistsl [‘0’, ‘F’]
          >> gvs[]
         )
      >> qexistsl [‘v2n (FRONT (F::(n2v s)))’, ‘LAST (n2v s)’]
      >> conj_tac
      >- (irule v2n_lt_imp
          >> gvs[LENGTH_FRONT, LENGTH_CONS]
          >> irule n2v_length_le
          >> gvs[]
         )
      >> gvs[v2n_tl]
      >> qmatch_goalsub_abbrev_tac ‘_ - n’
      >> gvs[v2n_snoc]
      >> gvs[v2n_zero_extend]
      >> gvs[v2n_n2v]
      >> gvs[v2n_front]
      >> gvs[v2n_n2v]
      >> gvs[DIV_MULT_THM2]
      >> DEP_PURE_ONCE_REWRITE_TAC[SUB_ADD]
      >> gvs[MOD_LESS_EQ]
      >> sg ‘n = 0’ >> gvs[]
      >> unabbrev_all_tac
      >> rw[]
      >> pop_assum mp_tac >> gvs[]
      >> qmatch_asmsub_abbrev_tac ‘s < 2 ** l’
      >> qsuff_tac ‘LENGTH (n2v (s DIV 2)) < l’
      >- (disch_tac
          >> Cases_on ‘l’ >> gvs[]
          >> gvs[zero_extend_suc])
      >> drule n2v_length_le
      >> sg ‘s DIV 2 < 2 ** (l - 1)’
      >- (gvs[DIV_LT_X]
          >> gvs[ADD1]
          >> Cases_on ‘l’ >> gvs[ADD1]
         )
      >> drule n2v_length_le
      >> gvs[LESS_EQ, ADD1]
      >> rpt strip_tac
      >> Cases_on ‘l = 0’ >> gvs[])
  (*>> conj_tac
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
     )*)
  >> conj_tac
  >- (rpt strip_tac
      >> gvs[parity_equations_to_state_machine_def]
     )
  >- (gvs[parity_equations_to_state_machine_def]
      >> Cases_on ‘ps’ >> gvs[]
     )
QED

Theorem apply_parity_equation_append:
  ∀ps bs ds.
    apply_parity_equation ps (bs ++ ds) =
    (apply_parity_equation ps bs ⇎
                           apply_parity_equation (DROP (LENGTH bs) ps) ds)
Proof
  Induct_on ‘bs’ >> rw[]
  >> namedCases_on ‘ps’ ["", "p ps'"] >> gvs[apply_parity_equation_def]
  >> metis_tac[]
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
    (SND (m.transition_fn (s, b)) = [] ⇔
       m.output_length = 0)
Proof
  rpt strip_tac
  >> EQ_TAC >> gvs[]
  >> PURE_REWRITE_TAC[GSYM LENGTH_EQ_0]
  >> rpt strip_tac
  >> gvs[Excl "LENGTH_NIL"]
  >> metis_tac[wfmachine_transition_fn_output_length, LENGTH]
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
  >> gvs[vd_encode_def2]
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
  >> Induct_on ‘bs’ >> gvs[vd_encode_def2]
QED

Theorem convolve_parity_equations_length:
  ∀bs ps.
    LENGTH (convolve_parity_equations ps bs) = LENGTH ps * LENGTH bs
Proof
  Induct_on ‘bs’ >> rpt strip_tac >> gvs[convolve_parity_equations_def]
  >> gvs[ADD1]
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
(* TODO: Generalise this to state machines in general *)
(* TODO: Alternatively, remove this entirely and just use TAKE and DROP *)
(* TODO: Probably ought to have used chunks instead. *)
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

Theorem drop_apply_parity_equations_append[simp]:
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

Theorem apply_parity_equation_replicate_f[simp]:
  ∀ps n.
    apply_parity_equation ps (REPLICATE n F) = F
Proof
  Induct_on ‘n’ >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘ps’ >> gvs[apply_parity_equation_def]
QED

Theorem apply_parity_equations_replicate_f[simp]:
  ∀ps n.
    apply_parity_equations ps (REPLICATE n F) = REPLICATE (LENGTH ps) F
Proof
  Induct_on ‘ps’ >> gvs[apply_parity_equations_def]
QED

Theorem apply_parity_equations_maxdeg_zero[simp]:
  ∀ps bs.
    MAX_LIST (MAP LENGTH ps) = 0 ⇒
    apply_parity_equations ps bs = REPLICATE (LENGTH ps) F
Proof
  Induct_on ‘ps’ >> gvs[apply_parity_equations_def]
QED

Theorem parity_equations_to_state_machine_maxdeg_zero_transition_fn[simp]:
  ∀ps s b.
    MAX_LIST (MAP LENGTH ps) = 0 ∧
    s = 0 ⇒
    (parity_equations_to_state_machine ps).transition_fn
                                          (s, b) =
    (0, REPLICATE (LENGTH ps) F)
Proof
  rpt strip_tac
  >> gvs[parity_equations_to_state_machine_def]
QED

Theorem parity_equations_to_state_machine_maxdeg_0_vd_encode[simp]:
  ∀ps bs i.
    MAX_LIST (MAP LENGTH ps) = 0 ∧
    i = 0 ⇒
    vd_encode (parity_equations_to_state_machine ps) bs i =
    REPLICATE (LENGTH ps * LENGTH bs) F
Proof
  Induct_on ‘bs’ >> gvs[vd_encode_def, REPLICATE_APPEND, ADD1, LEFT_ADD_DISTRIB]
QED

(* We use i = LENGTH bs instead of subsituting LENGTH bs for i because by my
   understanding, this allows gvs to attempt to calculate the LENGTH of bs
   in order to attempt to apply this to equations not immediately in the
   form of LENGTH bs *)
Theorem drop_vd_encode[simp]:
  ∀i bs ps s.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ∧
    s < (parity_equations_to_state_machine ps).num_states ∧
    i = LENGTH bs ⇒ 
    DROP (i * LENGTH ps) (vd_encode (parity_equations_to_state_machine ps) bs s) = []
Proof
  rpt strip_tac
  >> gvs[]
QED

Theorem drop_vd_encode_append[simp]:
  ∀i bs cs ps s.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ∧
    s < (parity_equations_to_state_machine ps).num_states ∧
    i = LENGTH bs ⇒ 
    DROP (i * LENGTH ps)
         (vd_encode (parity_equations_to_state_machine ps) bs s ⧺ cs) = cs
Proof
  rpt strip_tac
  >> gvs[DROP_APPEND]
QED

Theorem vd_encode_state_parity_equations_to_state_machine_maxdeg_0[simp]:
  ∀ps bs s.
    MAX_LIST (MAP LENGTH ps) = 0 ∧
    s = 0 ⇒
    vd_encode_state (parity_equations_to_state_machine ps) bs s = 0
Proof
  Induct_on ‘bs’ >> gvs[vd_encode_state_def]
QED                                                                                         
(* -------------------------------------------------------------------------- *)
(* Goal: to show that each window of parity equations is equivalent to the    *)
(* corresponding window of state machines.                                    *)
(*                                                                            *)
(* Step 1: Show that a particular window can be calculated by first using     *)
(* vd_encode_state to arrive at the appropriate state, then applying the      *)
(* transition to generate the corresponding output.                           *)
(*                                                                            *)
(* Step 2: Induct over vd_encode_state to show that at any point, the state   *)
(* that has been encoded is equivalent to the last few bits in the bitstring. *)
(* It is easier to use induction for this purpose over vd_encode_state than   *)
(* over vd_encode for reasons that I hope are clear but would take a bit of   *)
(* thinking on my part to explain concretely.                                 *)
(*                                                                            *)
(* Step 3: Combine these steps to show that a particular window is equal to   *)
(* the output which corresponds to the relevant bits in the bitstring.        *)
(* -------------------------------------------------------------------------- *)
Theorem ith_output_window_vd_encode_vd_encode_state:
  ∀i ps bs.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ∧
    i < LENGTH bs ⇒
    ith_output_window i ps
                      (vd_encode (parity_equations_to_state_machine ps) bs 0) =
    (SND ((parity_equations_to_state_machine ps)
          .transition_fn (vd_encode_state
                          (parity_equations_to_state_machine ps)
                          (TAKE i bs) 0
                          , EL i bs
                         )))
Proof
  rpt strip_tac
  >> Cases_on ‘bs = []’ >> gvs[]
  (*
  (* Here, we used to treat the special case of MAX_LIST (MAP LENGTH ps) = 0
     separately, but now the special case includes MAX_LIST (MAP LENGTH ps) = 1,
     so we can't prove it as trivially any more. *)
  (* Treat special case separately *)
  >> Cases_on ‘¬(0 < MAX_LIST (MAP LENGTH ps))’
  (* TODO: This seems unnecessarily long *)
  >- (gvs[]
      >> gvs[ith_output_window_def]
      >> gvs[TAKE_REPLICATE]
      >> gvs[MIN_DEF]
      >> rw[]
      >> qmatch_goalsub_abbrev_tac ‘REPLICATE l1 _ = REPLICATE l2 _’
      >> Cases_on ‘l1 = l2’ >> gvs[]
      >> qsuff_tac ‘F’ >> gvs[]
      >> sg ‘l1 < l2’ >> gvs[]
      >> gvs[Abbr ‘l1’]
      >> sg ‘l2 + i * l2 = (1 + i) * l2’
      >- gvs[]
      >> pop_assum (fn th => gvs[Once th])
     )
  >> gvs[]
  *)
  >> sg ‘wfmachine (parity_equations_to_state_machine ps)’
  >- gvs[]
  >> qmatch_goalsub_abbrev_tac ‘_ = RHS’
  >> sg ‘bs = (TAKE i bs) ⧺ [EL i bs] ⧺ (DROP (i + 1) bs)’
  >- (sg ‘bs = TAKE i bs ⧺ DROP i bs’
      >- gvs[]
      >> pop_assum (fn th => PURE_REWRITE_TAC [Once th])
      >> gvs[]
      >> gvs[DROP_BY_DROP_SUC, ADD1]
     )
  >> pop_assum (fn th => PURE_REWRITE_TAC [Once th])
  >> gvs[vd_encode_append]
  >> gvs[ith_output_window_def]
  >> gvs[DROP_APPEND]
  >> gvs[TAKE_APPEND]
  >> sg ‘LENGTH RHS = LENGTH ps’
  >- (unabbrev_all_tac
      >> gvs[])
  >> gvs[]
QED

Theorem LASTN_LENGTH_ID_LEQ[simp]:
  ∀vs l.
    LENGTH vs ≤ l ⇒
    LASTN l vs = vs
Proof
  rpt strip_tac
  >> gvs[LASTN_def]
  >> gvs[TAKE_LENGTH_TOO_LONG]
QED

Theorem PAD_LEFT_LENGTH_LEQ[simp]:
  ∀c n ls.
    n ≤ LENGTH ls ⇒
    PAD_LEFT c n ls = ls
Proof
  Induct_on ‘n’ >> gvs[PAD_LEFT_SUC]
QED

Theorem zero_extend_length_leq[simp]:
  ∀l bs.
    l ≤ LENGTH bs ⇒
    zero_extend l bs = bs
Proof
  rpt strip_tac
  >> gvs[zero_extend_def, PAD_LEFT_LENGTH_LEQ]
QED

Theorem lastn_zero_extend[simp]:
  ∀n bs.
    n ≤ LENGTH bs ⇒ zero_extend n (LASTN n bs) = LASTN n bs
Proof
  rpt strip_tac
  >> gvs[zero_extend_length_leq, LENGTH_LASTN]
QED

Theorem zero_extend_lastn[simp]:
  ∀n bs.
    LENGTH bs ≤ n ⇒ LASTN n (zero_extend n bs) = zero_extend n bs
Proof
  rpt strip_tac
  >> gvs[length_zero_extend_2]
QED

Theorem zero_extend_lastn_swap:
  ∀n bs.
    LASTN n (zero_extend n bs) = zero_extend n (LASTN n bs)
Proof
  rpt strip_tac
  >> Cases_on ‘n ≤ LENGTH bs’ >> gvs[]
QED

(* TODO: Idea: would be helpful to have a more interactive way to see which
     theorems were actually used for the purposes of simplification, without
     failure, when applying the simplifier. Would be nice to see a nice
     graphical tree of simplifications that occurred. *)


(* Maybe this should be automatically provable somehow using
   wfmachine_transition_fn_destination_is_valid as well as
   the definition of parity_equations_to_state_machine and
   parity_equations_to_state_machine_wfmachine *)
Theorem parity_equations_to_state_machine_destination_is_valid[simp]:
  ∀ps i b.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ∧
    i < 2 ** (MAX_LIST (MAP LENGTH ps) - 1) ⇒
    (FST ((parity_equations_to_state_machine ps)
          .transition_fn (i, b))) <
    2 ** (MAX_LIST (MAP LENGTH ps) - 1)
Proof
  gvs[]
  >> rpt strip_tac
  >> gvs[]
  (* TODO: IDEA: would be nice to be able to irule
     wfmachine_transition_fn_destination_is_valid here, but i *)
  >> qspecl_then [‘parity_equations_to_state_machine ps’,
                  ‘i’,
                  ‘b’]
                 assume_tac wfmachine_transition_fn_destination_is_valid
  >> gvs[Excl "wfmachine_transition_fn_destination_is_valid"]
QED

Theorem null_zero_extend[simp]:
  ∀n bs.
    NULL (zero_extend n bs) ⇔ n = 0 ∧ bs = []
Proof
  rpt strip_tac
  >> Cases_on ‘n’ >> Cases_on ‘bs’ >> rw[zero_extend_suc]
QED

Theorem n2v_snoc:
  ∀i j.
    (i ≠ 0 ∨ j ≠ 0) ∧
    j < 2 ⇒
    n2v (2 * i + j) = SNOC (j = 1) (n2v i)
Proof
  rpt gen_tac
  >> rpt disch_tac
  >> Cases_on ‘2 * i + j’ >> gvs[]
  >> gvs[n2v_def]
  >> pop_assum (fn th => PURE_REWRITE_TAC[GSYM th])
  >> conj_tac
  >- gvs[MOD_MULT]
  >> AP_TERM_TAC
  >> gvs[DIV_MULT]
  >> Cases_on ‘j’ >> gvs[]
  >> Cases_on ‘n’ >> gvs[]
QED

Theorem bitstring_n2v_n2v:
  ∀n.
    bitstring$n2v n = if n = 0 then [F] else n2v n
Proof
  rpt strip_tac >> rw[]
  >- EVAL_TAC
  >> gvs[n2v_bitstring_n2v]
QED

Theorem zero_extend_replicate:
  ∀n bs.
    zero_extend n bs = REPLICATE (n - LENGTH bs) F ⧺ bs
Proof
  sg ‘∀m bs. zero_extend (m + LENGTH bs) bs = REPLICATE m F ⧺ bs’
  >- (Induct_on ‘m’ >> gvs[]
      >> rpt strip_tac
      >> gvs[GSYM ADD_SUC]
      >> gvs[zero_extend_suc])
  >> rpt strip_tac
  >> pop_assum $ qspecl_then [‘n - LENGTH bs’, ‘bs’] assume_tac
  >> Cases_on ‘LENGTH bs ≤ n’ >> gvs[]
QED

Theorem if_eq_then[simp]:
  ∀b n m.
    ((if b then n else m) = n) ⇔ (b ∨ n = m)
Proof
  rpt strip_tac
  >> rw[]
  >> simp[EQ_SYM_EQ]
QED

Theorem if_eq_else[simp]:
  ∀b n m.
    ((if b then n else m) = m) ⇔ (¬b ∨ n = m)
Proof
  rpt strip_tac
  >> rw[]
  >> simp[EQ_SYM_EQ]
QED

Theorem zero_extend_snoc:
  ∀n b bs.
    zero_extend n (SNOC b bs) = SNOC b (zero_extend (n - 1) bs)
Proof
  Induct_on ‘n’ >> gvs[] >> rpt strip_tac
  >> gvs[zero_extend_suc]
  >> rw[]
  >> Cases_on ‘n’ >> gvs[]
  >> gvs[zero_extend_suc]
QED

Theorem zero_extend_append:
  ∀n bs cs.
    zero_extend n (bs ⧺ cs) = zero_extend (n - LENGTH cs) bs ⧺ cs
Proof
  Induct_on ‘n’ >> gvs[] >> rpt strip_tac
  >> gvs[zero_extend_suc]
  >> rw[]
  >> gvs[SUB]
  >> gvs[zero_extend_suc]
QED

Theorem zero_extend_append_b:
  ∀n bs cs.
    zero_extend n bs ⧺ cs = zero_extend (n + LENGTH cs) (bs ⧺ cs)
Proof
  rw[]
  >> qspecl_then [‘n + LENGTH cs’, ‘bs’, ‘cs’] assume_tac zero_extend_append
  >> gvs[]
QED

Theorem zero_extend_n2v_v2n[simp]:
  ∀l bs.
    l = LENGTH bs ⇒
    zero_extend l (n2v (v2n bs)) = bs
Proof
  Induct_on ‘bs’ using SNOC_INDUCT >> gvs[SNOC_APPEND] >> rpt strip_tac
  >> Cases_on ‘LENGTH bs’ >> gvs[]
  >- (Cases_on ‘x’ >> EVAL_TAC)
  >> PURE_REWRITE_TAC[GSYM SNOC_APPEND, v2n_snoc]
  >> Cases_on ‘v2n bs = 0 ∧ (if x then 1 else 0) = 0’
  >- (gvs[]
      >> gvs[ADD1]
      >> gvs[GSYM SNOC_APPEND, SNOC_REPLICATE]
      >> PURE_REWRITE_TAC[GSYM $ cj 2 REPLICATE]
      >> PURE_REWRITE_TAC[ADD1]
      >> gvs[])
  >> DEP_PURE_ONCE_REWRITE_TAC[n2v_snoc]
  >> gvs[SNOC_APPEND]
  >> gvs[zero_extend_append]
  >> Cases_on ‘x’ >> gvs[]
QED

Theorem lastn_zero_extend_length[simp]:
  ∀n bs.
    LENGTH (LASTN n (zero_extend n bs)) = n
Proof
  rpt strip_tac
  >> Cases_on ‘n ≤ LENGTH bs’
  >- gvs[LENGTH_LASTN]
  >> gvs[]
  >> gvs[length_zero_extend]
QED

Theorem LASTN_0[simp]:
  ∀l. LASTN 0 l = []
Proof
  gvs[LASTN]
QED

Theorem LASTN_1_LAST:
  ∀l.
    l ≠ [] ⇒
    LASTN 1n l = [LAST l]
Proof
  rpt strip_tac
  >> Induct_on ‘l’
  >- gvs[]
  >> rpt strip_tac
  >> Cases_on ‘1 ≤ LENGTH l’
  >- (gvs[LASTN_CONS]
      >> Cases_on ‘l’ >> gvs[])
  >> Cases_on ‘l’ >> gvs[]
QED

Theorem TL_LASTN:
  ∀n ls.
    SUC n ≤ LENGTH ls ⇒
    TL (LASTN (SUC n) ls) = LASTN n ls
Proof
  Induct_on ‘n’ >> gvs[]
  >- (rpt strip_tac
      >> Cases_on ‘ls’ using SNOC_CASES >> gvs[]
      >> gvs[LASTN_1_LAST]
     )
  >> rpt strip_tac
  >> Cases_on ‘ls’ using SNOC_CASES
  >- gvs[]
  >> PURE_REWRITE_TAC[LASTN]
  >> PURE_REWRITE_TAC[TL_SNOC]
  >> rw[]
  >- (gvs[NULL_EQ]
      >> Cases_on ‘l’ using SNOC_CASES
      >- gvs[]
      >> gvs[LASTN])
  >> gvs[]
QED

Theorem snoc_zero_extend:
  ∀n b bs.
    SNOC b (zero_extend n bs) = zero_extend (n + 1) (SNOC b bs)
Proof
  rpt strip_tac
  >> qabbrev_tac ‘m = n + 1’
  >> sg ‘n = m - 1’ >- gvs[Abbr ‘m’]
  >> PURE_REWRITE_TAC[zero_extend_snoc]
  >> gvs[]
QED

Theorem tl_zero_extend:
  ∀l bs.
    TL (zero_extend l bs) =
    if (l ≤ LENGTH bs) then TL bs else zero_extend (l - 1) bs
Proof
  rpt strip_tac
  >> rw[]
  >> sg ‘LENGTH bs < l’ >> gvs[]
  >> Cases_on ‘l’ >> gvs[]
  >> Cases_on ‘bs’ >> gvs[]
  >> gvs[zero_extend_suc]
QED

Theorem LASTN_APPEND1b:
  ∀l1 l2 n.
    (LASTN n l1) ++ l2 = LASTN (n + LENGTH l2) (l1 ++ l2) 
Proof
  rw[]
  >> qspecl_then [‘l2’, ‘n + LENGTH l2’] assume_tac LASTN_APPEND1
  >> gvs[]
QED

Theorem LASTN_LENGTH_MINUS_ONE:
  ∀bs.
    LASTN (LENGTH bs - 1) bs = TL bs
Proof
  rw[]
  >> Induct_on ‘bs’ >> gvs[LASTN_CONS]
QED

Theorem tl_lastn_zero_extend:
  ∀n bs.
    TL (LASTN n (zero_extend n bs)) = LASTN (n - 1) (zero_extend (n - 1) bs)
Proof
  rw[]
  >> Cases_on ‘n ≤ LENGTH bs’
  >- (gvs[zero_extend_length_leq]
      >> Cases_on ‘n’ >> gvs[]
      >> gvs[TL_LASTN]
     )
  >> gvs[NOT_LE]
  >> Cases_on ‘n’ >> gvs[]
  >> gvs[tl_zero_extend]
QED

(* -------------------------------------------------------------------------- *)
(* If we are in the state corresponding to the vector bs and we apply a       *)
(* transition to this state, then the resulting state will simply be the      *)
(* vector bs with the input to the transition postpended                      *)
(* -------------------------------------------------------------------------- *)
Theorem fst_parity_equations_to_state_machine_transition_fn_v2n_lastn_zero_extend:
  ∀ps bs b.
    FST (((parity_equations_to_state_machine ps).transition_fn)
         ((v2n (LASTN (window_length ps - 1)
                      (zero_extend (window_length ps - 1) bs)
               )
          ), b)) = v2n (LASTN (window_length ps − 1)
                              (zero_extend (window_length ps − 1) (bs ⧺ [b])))
Proof
  rw[]
  >> gvs[parity_equations_to_state_machine_def]
  >> gvs[LASTN_APPEND1b]
  >> gvs[zero_extend_append_b]
  >> gvs[tl_lastn_zero_extend]
QED

(* -------------------------------------------------------------------------- *)
(* The state we end up in after applying the state machine to an input bs,    *)
(* starting from an initial state i, is equivalent to taking the initial      *)
(* state i, converting it into the vector of the most recently seen bits,     *)
(* appending the string bs to reflect the fact that these are now the most    *)
(* recently seen bits, restricting to the correct size, and converting back   *)
(* into the state's natural number representation.                            *)
(*                                                                            *)
(* We require that the window length is greater than 1, so that we have a     *)
(* nonzero number of information bits in the state.                           *)
(*                                                                            *)
(* We also require that the state is valid (within the appropriate range)     *)
(* -------------------------------------------------------------------------- *)
Theorem vd_encode_state_parity_equations_to_state_machine:
  ∀ps bs i.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ∧
    i < 2 ** (MAX_LIST (MAP LENGTH ps) - 1) ⇒
    vd_encode_state (parity_equations_to_state_machine ps) bs i =
    v2n (LASTN (MAX_LIST (MAP LENGTH ps) - 1)
               (zero_extend (MAX_LIST (MAP LENGTH ps) - 1) (n2v i ⧺ bs)))
Proof
  (* Induct on the input bitstring. We use SNOC_INDUCT because we want to make
     sure that the most recently added element is at the end. *)
  Induct_on ‘bs’ using SNOC_INDUCT >> gvs[]
  >- (rpt strip_tac
      >> PURE_REWRITE_TAC[Once zero_extend_lastn_swap]
      >> gvs[]
      >> gvs[n2v_length_le, v2n_n2v] (* Maybe these length functions should
                                            be in the simp set *)
     )
  >> rpt strip_tac
  >> gvs[vd_encode_state_snoc]
  >> last_x_assum kall_tac (* The inductive hypothesis has been used, and we
                              don't need it any more *)
  >> gvs[fst_parity_equations_to_state_machine_transition_fn_v2n_lastn_zero_extend]
  >> gvs[SNOC_APPEND]
QED

(* Possibly a better theorem than LENGTH_TAKE, because it isn't dependent on
   any preconditions, and hence can always be used, even when the precondition
   required by LENGTH_TAKE is false.

   Didn't notice LENGTH_TAKE_EQ when I wrote this. Still, I don't like how
   the variables aren't quantified in LENGTH_TAKE_EQ *)
Theorem LENGTH_TAKE_2:
  ∀n l.
    LENGTH (TAKE n l) = MIN n (LENGTH l)
Proof
  rpt strip_tac
  >> Cases_on ‘n ≤ LENGTH l’ >> gvs[LENGTH_TAKE]
  >- rw[MIN_DEF]
  >> rw[MIN_DEF]
  >> gvs[TAKE_LENGTH_TOO_LONG]
QED

Theorem LENGTH_TAKE_LE_2[simp]:
  ∀n l.
    LENGTH (TAKE n l) ≤ n
Proof
  gvs[LENGTH_TAKE_2]
QED

Theorem LASTN_TAKE:
  ∀bs n m.
    m ≤ LENGTH bs ⇒
    LASTN n (TAKE m bs) = DROP (m - n) (TAKE m bs)
Proof
  rpt strip_tac
  >> Cases_on ‘m ≤ n’ >> gvs[]
  >- (sg ‘m - n = 0’ >- gvs[]
      >> simp[]
     )
  >> sg ‘n < m’ >> gvs[]
  >> Cases_on ‘m ≤ LENGTH bs’ >> gvs[LASTN_DROP]
QED

Theorem apply_parity_equation_take_maxdeg[simp]:
  ∀ps bs l.
    LENGTH ps ≤ l ⇒
    apply_parity_equation ps (TAKE l bs) =
    apply_parity_equation ps bs
Proof
  Induct_on ‘ps’ >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘bs’ >> gvs[]
  >> Cases_on ‘l’ >> gvs[]
  >> Cases_on ‘n’ >> gvs[]
  >- gvs[apply_parity_equation_def]
  >> gvs[apply_parity_equation_def]
QED

Theorem apply_parity_equations_take_maxdeg[simp]:
  ∀ps bs l.
    MAX_LIST (MAP LENGTH ps) ≤ l ⇒
    apply_parity_equations ps (TAKE l bs) =
    apply_parity_equations ps bs
Proof
  Induct_on ‘ps’ >> gvs[]
  >> rpt strip_tac
  >> gvs[apply_parity_equations_def]
QED

Theorem ith_output_window_vd_encode_parity_equations_to_state_machine[simp]:
  ∀i ps bs.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ∧
    i < LENGTH bs ⇒
    ith_output_window
    i ps (vd_encode (parity_equations_to_state_machine ps) bs 0) =
    apply_parity_equations
    ps (DROP i (REPLICATE (MAX_LIST (MAP LENGTH ps) - 1) F ⧺ bs))
Proof
  rpt strip_tac
  >> gvs[ith_output_window_vd_encode_vd_encode_state]
  >> gvs[vd_encode_state_parity_equations_to_state_machine]
  >> gvs[parity_equations_to_state_machine_def]
  >> PURE_REWRITE_TAC[GSYM SNOC_APPEND]                     
  >> Cases_on ‘MAX_LIST (MAP LENGTH ps) - 1 ≤ i’
  >- (gvs[SNOC_APPEND]
      >> gvs[LASTN_TAKE]
      >> gvs[DROP_APPEND]
      >> Cases_on ‘MAX_LIST (MAP LENGTH ps) = i + 1’
      >- (gvs[]
          >> PURE_REWRITE_TAC[GSYM SNOC_APPEND]
          >> DEP_PURE_ONCE_REWRITE_TAC[GSYM TAKE_EL_SNOC]
          >> gvs[]
         )
      >> sg ‘MAX_LIST (MAP LENGTH ps) < i + 1’ >> gvs[]
     (*>> gvs[GSYM DROP_APPEND]
      >> PURE_REWRITE_TAC[GSYM SNOC_APPEND]
      >> DEP_PURE_ONCE_REWRITE_TAC[GSYM TAKE_EL_SNOC]*)
      >> sg ‘MAX_LIST (MAP LENGTH ps) - (i + 1) = 0’
      >- gvs[]
      >> simp[]
      >> gvs[]
      >> qmatch_goalsub_abbrev_tac ‘LHS = _’
      >> sg ‘bs = TAKE i bs ⧺ [EL i bs] ⧺ DROP (SUC i) bs’ >- gvs[TAKE_DROP_SUC]
      >> pop_assum $ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> gvs[DROP_APPEND]
      >> unabbrev_all_tac
      >> gvs[DROP_TAKE]
      >> sg ‘1 - MAX_LIST (MAP LENGTH ps) = 0’
      >- gvs[]
      >> simp[]
      >> gvs[]
      >> gvs[TAKE_DROP]
      >> sg ‘i + 1 - MAX_LIST (MAP LENGTH ps) - (i + 1) = 0’ >- gvs[]
      >> simp[]
      >> gvs[]
      >> qmatch_goalsub_abbrev_tac ‘LHS = apply_parity_equations _ cs’
      >> assume_tac (SPECL [“ps : bool list list”, “cs : bool list”, “MAX_LIST (MAP LENGTH (ps : bool list list))”] (GSYM apply_parity_equations_take_maxdeg))
      >> gvs[Excl "apply_parity_equations_take_maxdeg", Abbr ‘cs’]
      >> gvs[Excl "apply_parity_equations_take_maxdeg", TAKE_APPEND]
      >> gvs[TAKE_TAKE_MIN]
      >> rw[MIN_DEF]
     )
  >> sg ‘i + 1 < MAX_LIST (MAP LENGTH ps)’ >> gvs[]
  >> gvs[DROP_APPEND]
  >> sg ‘(i + 1) - MAX_LIST (MAP LENGTH ps) = 0’ >- gvs[]
  >> simp[]
  >> gvs[zero_extend_replicate]
  >> qmatch_goalsub_abbrev_tac ‘LHS = apply_parity_equations _ cs’
  >> assume_tac (SPECL [“ps : bool list list”,
                        “cs : bool list”,
                        “MAX_LIST (MAP LENGTH (ps : bool list list))”]
                       (GSYM apply_parity_equations_take_maxdeg))
  >> gvs[Excl "apply_parity_equations_take_maxdeg", Abbr ‘cs’]
  >> gvs[Excl "apply_parity_equations_take_maxdeg", TAKE_APPEND]
  >> unabbrev_all_tac
  >> gvs[TAKE_EL_SNOC]
  >> gvs[TAKE_REPLICATE]
  >> rw[MIN_DEF]
QED

Theorem parity_equations_to_state_machine_equivalent_window:
  ∀i ps bs.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ∧
    i + MAX_LIST (MAP LENGTH ps) - 1 < LENGTH bs ⇒
    ith_output_window i ps (convolve_parity_equations ps bs) =
    ith_output_window (i + MAX_LIST (MAP LENGTH ps) - 1) ps
                      (vd_encode (parity_equations_to_state_machine ps) bs 0)
Proof
  rpt strip_tac
  >> gvs[]
  >> gvs[DROP_APPEND]
  >> sg ‘MAX_LIST (MAP LENGTH ps) - 1 - (i + MAX_LIST (MAP LENGTH ps) - 1) = 0’
  >- gvs[]
  >> simp[]
QED

(* TODO: Rename.
   Alternative form of DIVISION theorem which I found more useful in my use
   case. The form which gvs[] simplified to in my case was the form written
   in this theorem. *)
Theorem DIVISION_2:
  ∀a b.
    0 < b ⇒
    b * (a DIV b) + a MOD b = a
Proof
  rpt strip_tac
  >> qspec_then ‘b’ assume_tac DIVISION
  >> gvs[]
  >> pop_assum $ qspec_then ‘a’ assume_tac
  >> gvs[]
QED

Theorem ith_output_window_el:
  ∀ps bs i.
    0 < LENGTH ps ∧
    i < LENGTH bs ⇒
    (EL i bs ⇔ (EL (i MOD (LENGTH ps)) (ith_output_window (i DIV (LENGTH ps)) ps bs)))
Proof
  rpt strip_tac
  >> gvs[ith_output_window_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[EL_TAKE]
  >> gvs[MOD_LESS]
  >> DEP_PURE_ONCE_REWRITE_TAC[EL_DROP]
  >> conj_tac
  >- gvs[DIVISION_2]
  >> gvs[DIVISION_2]
QED

Theorem maxdeg_valid_ps_length_nonzero[simp]:
  ∀ps.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ⇒
    0 < LENGTH ps
Proof
  rpt strip_tac
  >> Cases_on ‘ps’ >> gvs[]
QED

Theorem MULT_DIV_SUB_MOD:
  ∀a b.
    0 < b ⇒
    b * (a DIV b) = a - a MOD b
Proof
  rpt strip_tac
  >> gvs[SUB_LEFT_EQ]
  >> gvs[DIVISION_2]
QED

Theorem parity_equations_to_state_machine_equivalent_individual:
  ∀ps bs i.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ∧
    i + (MAX_LIST (MAP LENGTH ps) - 1) * LENGTH ps <  LENGTH bs * LENGTH ps ⇒
    EL i (convolve_parity_equations ps bs) =
    EL (i + (MAX_LIST (MAP LENGTH ps) - 1) * LENGTH ps)
       (vd_encode (parity_equations_to_state_machine ps) bs 0)
Proof
  rpt strip_tac
  >> qspec_then ‘ps’ assume_tac ith_output_window_el
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> gvs[convolve_parity_equations_length]
  >> Cases_on ‘0 < LENGTH bs’ >> gvs[]
  >> DEP_PURE_ONCE_REWRITE_TAC[parity_equations_to_state_machine_equivalent_window]
  >> gvs[]
  >> conj_tac
  >- (qsuff_tac ‘MAX_LIST (MAP LENGTH ps) - 1 + i DIV LENGTH ps < LENGTH bs’
      >- gvs[]
      >> qsuff_tac ‘LENGTH ps * (MAX_LIST (MAP LENGTH ps) - 1 + i DIV LENGTH ps) < LENGTH ps * LENGTH bs’
      >- gvs[]
      >> PURE_REWRITE_TAC[LEFT_ADD_DISTRIB]
      >> gvs[MULT_DIV_SUB_MOD]
     )
  >> qmatch_goalsub_abbrev_tac ‘LHS = _’
  >> qspec_then ‘ps’ assume_tac ith_output_window_el
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> gvs[]
  >> unabbrev_all_tac
  >> DEP_PURE_ONCE_REWRITE_TAC[ADD_DIV_RWT]
  >> gvs[]
  >> gvs[MULT_TO_DIV]
QED

(* TODO: is there a pre-existing theorem along these lines? *)
Theorem LIST_TRANSLATE:
  ∀ls ks d.
    LENGTH ls + d ≤ LENGTH ks ⇒
    ((∀n. n < LENGTH ls ⇒ EL n ls = EL (n + d) ks) ⇔
       TAKE (LENGTH ls) (DROP d ks) = ls)
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (rpt strip_tac
      >> irule LIST_EQ (* TODO: Idea: It can be hard to search for this
                          theorem. Perhaps we need to work out a better way
                          of searching for such a theorem, if we don't know
                          the precise statement it has. For example, I was
                          expecting it to use an iff, and I forgot that it
                          would require the precondition x < LENGTH l1. *)
      >> conj_tac
      >- (rpt strip_tac
          >> gvs[EL_TAKE, EL_DROP]
         )
      >> gvs[LENGTH_TAKE]
     )
  >> rpt strip_tac
  >> qmatch_asmsub_abbrev_tac ‘TAKE m _’
  >> gvs[]
  >> gvs[EL_TAKE, EL_DROP]
QED

(* Unsure what name to give this *)
Theorem ADD_LEQ_IFF_ZERO_RIGHT[simp]:
  ∀a b.
    a + b ≤ a ⇔ b = 0
Proof
  rpt strip_tac
  >> Cases_on ‘b’ >> gvs[]
QED

(* Perhaps this should be done in a more general way. In particular, maybe
   the length of parity_equations_to_state_machine should be added as a simp
     rule, and TAKE of the exact length should be added as a simp rule. *)
Theorem take_exact_length_encode[simp]:
  ∀ps bs.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ⇒
    TAKE (LENGTH bs * LENGTH ps)
         (vd_encode (parity_equations_to_state_machine ps) bs 0) =
    vd_encode (parity_equations_to_state_machine ps) bs 0
Proof
  rpt strip_tac
  >> DEP_PURE_ONCE_REWRITE_TAC[TAKE_LENGTH_TOO_LONG]
  >> gvs[vd_encode_length]
QED

(* -------------------------------------------------------------------------- *)
(* Prove that the state machine representation of a convolutional code is     *)
(* equivalent to the parity equations representation                          *)
(* -------------------------------------------------------------------------- *)
Theorem parity_equations_to_state_machine_equivalent:
  ∀ps bs.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ⇒
    let
      max_degree = MAX_LIST (MAP LENGTH ps);
      num_to_drop = (LENGTH ps) * (max_degree - 1);
    in
      TAKE ((LENGTH ps) * (LENGTH bs) - num_to_drop)
           (convolve_parity_equations ps bs) =
      DROP num_to_drop (vd_encode (parity_equations_to_state_machine ps) bs 0)
Proof
  rpt strip_tac
  >> gvs[]
  (* Handle the special case where we are dropping all elements.
     First line is the total number of elements
     Second line is num_to_drop *)
  >> Cases_on ‘(LENGTH ps) * (LENGTH bs) ≤
               (LENGTH ps) * (MAX_LIST (MAP LENGTH ps) - 1)’
  >- (qmatch_goalsub_abbrev_tac ‘TAKE take_num _’
      >> sg ‘take_num = 0’
      >- (gvs[Abbr ‘take_num’]
          >> PURE_REWRITE_TAC[Once MULT_COMM]
          >> gvs[]
         )
      >> gvs[]
     )
  >> gvs[NOT_LESS_EQUAL]
  (* This theorem is essentially an instance of LIST_TRANSLATE, so
     apply that theorem. *)      
  >> qspecl_then [‘TAKE ((LENGTH ps) * (LENGTH bs) -
                         (LENGTH ps) * (MAX_LIST (MAP LENGTH ps) - 1))
                   (convolve_parity_equations ps bs)’,
                  ‘vd_encode (parity_equations_to_state_machine ps) bs 0’,
                  ‘(MAX_LIST (MAP LENGTH ps) - 1) * LENGTH ps’]
                 assume_tac LIST_TRANSLATE
  >> qmatch_asmsub_abbrev_tac ‘P1 ⇒ (P2 ⇔ P3)’
  >> sg ‘P1’
  >- (gvs[Abbr ‘P1’]
      >> DEP_PURE_ONCE_REWRITE_TAC[LENGTH_TAKE]
      >> gvs[convolve_parity_equations_length]
      >> DEP_PURE_ONCE_REWRITE_TAC[SUB_ADD]
      >> gvs[]
      >> PURE_REWRITE_TAC[Once MULT_COMM]
      >> gvs[]
     )
  >> first_x_assum drule >> disch_tac
  >> qpat_x_assum ‘P1’ kall_tac
  >> qpat_x_assum ‘Abbrev (P1 ⇔ _)’ kall_tac
  >> sg ‘P3’
  >- (qpat_x_assum ‘Abbrev (P3 ⇔ _)’ kall_tac
      >> pop_assum (fn th => irule (iffLR th))
      >> unabbrev_all_tac
      >> rpt strip_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[LENGTH_TAKE]
      >> gvs[convolve_parity_equations_length]
      >> gvs[EL_TAKE]
      (* Important step: use
          parity_equations_to_state_machine_equivalent_individual
          to prove that the lists are equivalent on each relevant index*)
      >> gvs[parity_equations_to_state_machine_equivalent_individual]
     )
  >> qpat_x_assum ‘P2 ⇔ P3’ kall_tac
  >> qpat_x_assum ‘Abbrev (P2 ⇔ _)’ kall_tac
  >> gvs[Abbr ‘P3’]
  >> gvs[LENGTH_TAKE, convolve_parity_equations_length]
  >> gvs[GSYM DROP_TAKE]
QED

(* This definition is simply used in order to avoid infinite loops when
   applying gvs. It is equivalent to APPEND, but cannot be treated by HOL
   as APPEND, which means, amongst other things, it cannot be used in
   rewrite rules that require an APPEND. Thus, if a rewrite rule takes an
   APPEND as input and produces an APPEND as output, using this version will
   prevent infinite loops where the outputted value is used as input to the
   next iteration. *)
Definition APPEND_DONOTEXPAND_DEF:
  APPEND_DONOTEXPAND = APPEND
End

Theorem APPEND_DONOTEXPAND_APPEND_ASSOC:
  ∀bs cs ds.
    APPEND_DONOTEXPAND (bs ⧺ cs) ds = bs ⧺ APPEND_DONOTEXPAND cs ds 
Proof
  gvs[APPEND_DONOTEXPAND_DEF]
QED

(* TODO: Is there a better way of avoiding infintie loops rather than using
   APPEND_DONOTEXPAND? *)
Theorem convolve_parity_equations_append:
  ∀ps bs cs.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ⇒
    convolve_parity_equations ps (bs ⧺ cs) =
    TAKE (LENGTH ps * LENGTH bs) (convolve_parity_equations ps (APPEND_DONOTEXPAND bs cs)) ⧺ convolve_parity_equations ps cs
Proof
  gvs[APPEND_DONOTEXPAND_DEF]
  >> Induct_on ‘bs’ >> gvs[]
  >> rpt strip_tac
  >> gvs[convolve_parity_equations_def]
  >> PURE_ONCE_REWRITE_TAC[MULT_COMM]
  >> gvs[MULT]        
  >> gvs[TAKE_SUM]
  >> gvs[TAKE_APPEND]
  >> gvs[TAKE_LENGTH_TOO_LONG]                
QED

(* TODO: can this be generalized somehow to a more general state machine?
         On the other hand, do we even want to bother? *) 
Theorem vd_encode_state_replicate_f[simp]:
  ∀ps n.
    vd_encode_state (parity_equations_to_state_machine ps) (REPLICATE n F) 0 = 0
Proof
  Induct_on ‘n’ >> gvs[]
  >> rpt strip_tac
  >> gvs[vd_encode_state_def]
  >> gvs[parity_equations_to_state_machine_def]
  >> gvs[GSYM SNOC_APPEND]
QED

Theorem vd_encode_state_append:
  ∀m bs cs i.
    vd_encode_state m (bs ⧺ cs) i =
    vd_encode_state m cs (vd_encode_state m bs i)
Proof
  Induct_on ‘bs’ >> gvs[vd_encode_state_def]
QED

(* See comment for vd_encode_state_replicate_f *)
Theorem vd_encode_state_replicate_f_append[simp]:
  ∀ps bs n.
    vd_encode_state (parity_equations_to_state_machine ps)
                    (REPLICATE n F ⧺ bs) 0 =
    vd_encode_state (parity_equations_to_state_machine ps) bs 0
Proof
  gvs[vd_encode_state_append]
QED

Theorem convolve_parity_equations_snoc:
  ∀ps bs b.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ⇒
    convolve_parity_equations ps (SNOC b bs) =
    TAKE (LENGTH ps * LENGTH bs) (convolve_parity_equations ps (SNOC b bs)) ⧺
         convolve_parity_equations ps [b]
Proof
  rpt strip_tac
  >> gvs[convolve_parity_equations_append, SNOC_APPEND]
  >> gvs[APPEND_DONOTEXPAND_DEF]
  >> Induct_on ‘LENGTH bs’ >> gvs[] >> rpt strip_tac
  >> Cases_on ‘bs’ >> gvs[]
  >> gvs[convolve_parity_equations_def, TAKE_APPEND, ADD1]
  >> gvs[TAKE_LENGTH_TOO_LONG, apply_parity_equations_length, convolve_parity_equations_length]
QED

Theorem convolve_parity_equations_replicate_f[simp]:
  ∀ps n.
    convolve_parity_equations ps (REPLICATE n F) =
    REPLICATE (LENGTH ps * n) F
Proof
  Induct_on ‘n’ >> gvs[]
  >> rpt strip_tac
  >> gvs[ADD1, convolve_parity_equations_def]
  >> PURE_REWRITE_TAC[GSYM (cj 2 REPLICATE)]
  >> PURE_REWRITE_TAC[apply_parity_equations_replicate_f]
  >> gvs[REPLICATE_APPEND]
  >> AP_THM_TAC
  >> AP_TERM_TAC
  >> decide_tac
QED

Theorem apply_parity_equation_append_replicate_f[simp]:
  ∀ps bs n.
    apply_parity_equation ps (bs ⧺ REPLICATE n F) =
    apply_parity_equation ps bs
Proof
  Induct_on ‘bs’ >> gvs[] >> rpt strip_tac
  >> Cases_on ‘ps’ >> gvs[apply_parity_equation_def]
QED

Theorem apply_parity_equations_append_replicate_f[simp]:
  ∀ps bs n.
    apply_parity_equations ps (bs ⧺ REPLICATE n F) =
    apply_parity_equations ps bs
Proof
  Induct_on ‘ps’ >> gvs[apply_parity_equations_def]
QED

Theorem convolve_parity_equations_append_replicate_f[simp]:
  ∀ps bs n.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ⇒
    convolve_parity_equations ps (bs ⧺ REPLICATE n F) =
    convolve_parity_equations ps bs ⧺ REPLICATE (n * LENGTH ps) F
Proof
  rpt strip_tac
  >> Induct_on ‘bs’ >> gvs[] >> rpt strip_tac
  >> gvs[convolve_parity_equations_def]
  >> PURE_REWRITE_TAC[GSYM (cj 2 APPEND)]
  >> PURE_REWRITE_TAC[apply_parity_equations_def]
  >> irule apply_parity_equations_append_replicate_f
  >> PURE_REWRITE_TAC[apply_parity_equations_replicate_f]
QED

(* I found using this theorem more convienient than mucking around with
   other theorems and stuff, although it's not a particularly insightful
   theorem *)
Theorem EQ_IMP_LEQ:
  ∀a b : num.
    a = b ⇒ a ≤ b
Proof
  gvs[]
QED

Theorem parity_equations_to_state_machine_equivalent_with_padding:
  ∀ps bs.
    0 < MAX_LIST (MAP LENGTH ps) - 1 ⇒
    convolve_parity_equations_padded ps bs =
    vd_encode_padded (parity_equations_to_state_machine ps) bs 0
Proof
  (* Simplify *)
  rpt strip_tac
  >> gvs[LOG2_2_EXP]
  (* This is an instance of parity_equations_to_state_machine_equivalent when
     applied to the bitstring with padding on both sides. For one side, the
     padding will be shaved off in one direciton, and for the other side, the
     padding will be shaved off in the other direction. *)
  >> qmatch_goalsub_abbrev_tac ‘convolve_parity_equations _ (APPEND padding _)’
  >> qspecl_then [‘ps’, ‘padding ⧺ bs ⧺ padding’] assume_tac parity_equations_to_state_machine_equivalent
  (* Simplify assumption *)
  >> gvs[]
  (* Split DROP side by appends, so we have 3 appended strings.
     We will later split the TAKE side by appends, and we will get 3
     corresponding appended strings. One appended string on each side
     will be reduced to the empty string, and the remaining two will
     correspond to two in the goal. *)
  >> gvs[vd_encode_append]
  >> gvs[DROP_APPEND]
  >> qmatch_asmsub_abbrev_tac ‘DROP l1 _ ⧺ DROP l2 _ ⧺ DROP l3 _’
  >> sg ‘l2 = 0’
  >- gvs[Abbr ‘l2’, Abbr ‘padding’, LENGTH_REPLICATE]
  >> sg ‘l3 = 0’
  >- gvs[Abbr ‘l3’, LENGTH_REPLICATE]
  >> gvs[]
  >> qmatch_asmsub_abbrev_tac ‘DROP l1 cs’
  >> sg ‘DROP l1 cs = []’
  >- gvs[Abbr ‘l1’, Abbr ‘cs’, Abbr ‘padding’]
  >> gvs[]
  >> gvs[Abbr ‘padding’]
  >> qmatch_goalsub_abbrev_tac ‘convolve_parity_equations ps (padding ⧺ bs)’
  >> qpat_x_assum ‘LENGTH cs ≤ l1’ kall_tac (* not sure if I should remove this
                                               assumption *)
  >> gvs[Abbr ‘cs’, Abbr ‘l1’]
  (* Split TAKE side by appends *)
  >> gvs[convolve_parity_equations_append, APPEND_DONOTEXPAND_APPEND_ASSOC]
  >> gvs[APPEND_DONOTEXPAND_DEF]
  >> rpt (pop_assum mp_tac)
  >> PURE_REWRITE_TAC[TAKE_APPEND]
  >> rpt strip_tac
  >> qmatch_asmsub_abbrev_tac ‘TAKE l1 _ ⧺ TAKE l2 _ ⧺ TAKE l3 _’
  >> gvs[GEN_ALL TAKE_TAKE_MIN]
  >> sg ‘l3 = 0’
  >- (unabbrev_all_tac
      >> pop_assum kall_tac
      >> simp_tac (srw_ss()) [] (* gvs is too strong and gets stuck trying to
                                   prove things *)
      >> rw[MIN_DEF]
      >> rw[LENGTH_TAKE, convolve_parity_equations_length]
      >> irule EQ_IMP_LEQ
      >> qmatch_goalsub_abbrev_tac ‘ps_len * (bs_len + 2 * maxdeg) = _’
      >> decide_tac (* Idea: decide_tac really ought to be able to work even
          before ensuring the functions are all represented as variables.
          Just make sure that all functions returning numbers are abbreviated
          to their num form, as I did manually above. *)
     )
  >> qpat_x_assum ‘Abbrev (l3 = _)’ kall_tac
  >> gvs[]
  >> sg ‘l1 = LENGTH ps * (LENGTH bs + MAX_LIST (MAP LENGTH ps) - 1)’
  >- (unabbrev_all_tac
      >> pop_assum kall_tac
      >> gvs[GSYM LEFT_SUB_DISTRIB]
     )
  >> qpat_x_assum ‘Abbrev (l1 = _)’ kall_tac
  >> gvs[]
  >> sg ‘l2 = LENGTH bs * LENGTH ps’
  >- (unabbrev_all_tac
      >> pop_assum kall_tac
      >> simp_tac (srw_ss()) [LENGTH_TAKE_2, convolve_parity_equations_length]
      >> rw[MIN_DEF]
      >> gvs[GSYM LEFT_SUB_DISTRIB]
     )
  >> qpat_x_assum ‘Abbrev (l2 = _)’ kall_tac
  >> gvs[]
  >> qmatch_asmsub_abbrev_tac ‘TAKE l1 _ ⧺ TAKE l2 _’
  >> sg ‘l1 = LENGTH ps * (MAX_LIST (MAP LENGTH ps) - 1)’
  >- (unabbrev_all_tac
      >> pop_assum kall_tac
      >> rw[MIN_DEF]
     )
  >> qpat_x_assum ‘Abbrev (l1 = _)’ kall_tac
  >> gvs[]
  >> sg ‘l2 = LENGTH bs * LENGTH ps’
  >- (unabbrev_all_tac
      >> pop_assum kall_tac
      >> rw[LENGTH_TAKE, LENGTH_REPLICATE, convolve_parity_equations_length]
      >> rw[MIN_DEF]
      >> rw[GSYM LEFT_SUB_DISTRIB]
     )
  >> qpat_x_assum ‘Abbrev (l2 = _)’ kall_tac
  >> gvs[]
  >> qpat_x_assum ‘_ = vd_encode _ _ _ ⧺ vd_encode _ _ _’
                  (fn th => gvs[GSYM th])
  >> gvs[Abbr ‘padding’, convolve_parity_equations_length]
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
(* We want to be sure that n2v is evaluable                                 *)
(* -------------------------------------------------------------------------- *)
Theorem n2v_test:
  n2v 22 = [T; F; T; T; F]
Proof
  EVAL_TAC
QED

Theorem parity_equations_to_state_machine_vd_encode_test:
  vd_encode (parity_equations_to_state_machine test_parity_equations)
  test_parity_equations_input 0 = [T; T; T; T; T; F; F; F; T; T; F; F; T; F; T; F; F; T; F; T; T; T; F; T]
Proof
  EVAL_TAC
QED

(* Test that convolve_parity_equations_padded corresponds with the behaviour we
   would expect it to have and that it corresponds to the behaviour of
   vd_encode_padded (parity_equations_to_state_machine ps) *)
Theorem convolve_parity_equations_padded_test:
  convolve_parity_equations_padded test_parity_equations test_parity_equations_input = [T; T; T; T; T; F; F; F; T; T; F; F; T; F; T; F; F; T; F; T; T; T; F; T; T; T; T; F] ∧
  convolve_parity_equations_padded test_parity_equations test_parity_equations_input = vd_encode_padded (parity_equations_to_state_machine test_parity_equations) test_parity_equations_input 0
Proof
  EVAL_TAC
QED

Theorem parity_equations_to_state_machine_equivalent_test:
  ∀bs.
    LENGTH bs < 7 ⇒
    convolve_parity_equations_padded test_parity_equations bs =
    vd_encode_padded (parity_equations_to_state_machine test_parity_equations) bs 0
Proof
  rpt strip_tac
  >> Cases_on ‘bs’
  >- EVAL_TAC
  >> Cases_on ‘t’
  >- (Cases_on ‘h’ >> EVAL_TAC)
  >> Cases_on ‘t'’
  >- (Cases_on ‘h’ >> Cases_on ‘h'’ >> EVAL_TAC)
  >> Cases_on ‘t’
  >- (Cases_on ‘h’ >> Cases_on ‘h'’ >> Cases_on ‘h''’ >> EVAL_TAC)
  >> Cases_on ‘t'’
  >- (Cases_on ‘h’ >> Cases_on ‘h'’ >> Cases_on ‘h''’ >> Cases_on ‘h'''’
      >> EVAL_TAC)
  >> Cases_on ‘t’
  >- (Cases_on ‘h’ >> Cases_on ‘h'’ >> Cases_on ‘h''’ >> Cases_on ‘h'''’
      >> Cases_on ‘h''''’ >> EVAL_TAC)
  >> Cases_on ‘t'’
  >- (Cases_on ‘h’ >> Cases_on ‘h'’ >> Cases_on ‘h''’ >> Cases_on ‘h'''’
      >> Cases_on ‘h''''’ >> Cases_on ‘h'''''’ >> EVAL_TAC)
  >> qsuff_tac ‘F’ >> gvs[LENGTH]
QED

val _ = export_theory();
