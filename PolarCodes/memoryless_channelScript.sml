(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory memoryless_channel

Ancestors arithmetic extreal lifting pred_set real measure sigma_algebra transfer probability

Libs dep_rewrite liftLib transferLib realLib;

(* -------------------------------------------------------------------------- *)
(* A channel underlyingly has the representation:                             *)
(* α -> β m_space                                                             *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* A memoryless channel                                                       *)
(* - Takes an input                                                           *)
(* - Returns a probability distribution over output bits.                     *)
(*                                                                            *)
(* We express this as                                                         *)
(*   α -> β m_space                                                           *)
(* -------------------------------------------------------------------------- *)
Definition wf_memoryless_channel_def:
  wf_memoryless_channel (W : α -> β m_space) =
  (∀x. (FINITE (m_space (W x)) ⇒ measurable_sets (W x) = POW (m_space (W x))) ∧
       prob_space (W x))
End

Theorem wf_memoryless_channels_exist[local]:
  ∃x. wf_memoryless_channel x
Proof
  qexists ‘λx. ({ARB}, {{};{ARB}}, λs. if s = {ARB} then 1 else 0)’
  >> simp[wf_memoryless_channel_def]
  >> sg ‘POW {ARB : β} = {∅; {ARB}}’
  >- (irule EQ_SYM
      >> simp[POW_DEF, EXTENSION]
      >> gen_tac >> EQ_TAC >> strip_tac
      >- (Cases_on ‘x’ >> gvs[] >> metis_tac[])
      >- (Cases_on ‘x’ >> gvs[]
          >> Cases_on ‘t’ >> gvs[]
          >> Cases_on ‘t'’ >> gvs[]
          >> metis_tac[])
      >> Cases_on ‘x’ >> gvs[])
  >> simp[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_on_finite_set]
  >> simp[]
  >> rpt conj_tac
  >- (simp[positive_def]
      >> gen_tac
      >> Cases_on ‘s’ >> gvs[])
  >- rw[prob_def, p_space_def]
  >> simp[additive_def]
  >> rpt gen_tac
  >> Cases_on ‘s’ >> simp[]
  >> REVERSE $ Cases_on ‘x = ARB’
  >- (sg ‘x INSERT t' ≠ {ARB}’
      >- (CCONTR_TAC >> gvs[]
          >> sg ‘x ∈ {ARB}’
          >- ASM_SET_TAC[]
          >> gvs[])
      >> simp[]
     )
  >> simp[]
  >> REVERSE $ Cases_on ‘t'’
  >- (Cases_on ‘x' = ARB’
      >- (‘F’ suffices_by strip_tac >> gvs[])
      >> sg ‘ARB INSERT x' INSERT t'' ≠ {ARB}’
      >- (simp[EXTENSION]
          >> qexists ‘x'’
          >> simp[])
      >> simp[]
     )
  >> simp[]
  >> Cases_on ‘t’ >> simp[]
  >> strip_tac
  >> ‘F’ suffices_by strip_tac
  >> sg ‘x' = ARB’
  >- (pop_assum mp_tac
      >> rpt $ pop_assum kall_tac
      >> simp[EXTENSION]
      >> disch_then $ qspec_then ‘x'’ assume_tac
      >> gvs[])
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* Create new abstract type consisting of well-formed state machines          *)
(* -------------------------------------------------------------------------- *)
val tydefrec = newtypeTools.rich_new_type { tyname = "memoryless_channel",
exthm  = wf_memoryless_channels_exist,
ABS = "memoryless_channel_ABS",
REP = "memoryless_channel_REP"};

(* -------------------------------------------------------------------------- *)
(* Something used in the lifting process, not sure about the details.         *)
(*                                                                            *)
(* Tells us whether two state machines are equivalent when considered as      *)
(* their abstract counterpart: thus, non-well-formed state machines are not   *)
(* equivalent, as they cannot be considered to be their abstract counterpart  *)
(* -------------------------------------------------------------------------- *)
Definition memoryless_channelequiv_def:
  memoryless_channelequiv m1 m2 ⇔ m1 = m2 ∧ wf_memoryless_channel m2
End

(* -------------------------------------------------------------------------- *)
(* A relation which relates a well-formed representative of a state machine   *)
(* to its corresponding abstract value.                                       *)
(* -------------------------------------------------------------------------- *)
Definition memoryless_channel_AR_def:
  memoryless_channel_AR r a ⇔ wf_memoryless_channel r ∧ r = memoryless_channel_REP a
End

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem memoryless_channel_relates[transfer_rule]:
  (memoryless_channel_AR ===> (=)) wf_memoryless_channel (K T)
Proof
  simp[FUN_REL_def, memoryless_channel_AR_def]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem memoryless_channel_AReq_relates[transfer_rule]:
  (memoryless_channel_AR ===> memoryless_channel_AR ===> (=)) (=) (=)
Proof
  simp[memoryless_channel_AR_def, FUN_REL_def, #termP_term_REP tydefrec, #term_REP_11 tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem right_unique_memoryless_channel_AR[transfer_simp]:
  right_unique memoryless_channel_AR
Proof
  simp[right_unique_def, memoryless_channel_AR_def, #term_REP_11 tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem surj_memoryless_channel_AR[transfer_simp]:
  surj memoryless_channel_AR
Proof
  simp[surj_def, memoryless_channel_AR_def, #termP_term_REP tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem RDOM_memoryless_channel_AR[transfer_simp]:
  RDOM memoryless_channel_AR = {gr | wf_memoryless_channel gr}
Proof
  simp[relationTheory.RDOM_DEF, Once FUN_EQ_THM, memoryless_channel_AR_def, SF CONJ_ss, #termP_term_REP tydefrec] >>
  metis_tac[#termP_term_REP tydefrec, #repabs_pseudo_id tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem Qt_memoryless_channel[liftQt]:
  Qt memoryless_channelequiv memoryless_channel_ABS memoryless_channel_REP memoryless_channel_AR
Proof
  simp[Qt_alt, memoryless_channel_AR_def, #absrep_id tydefrec, memoryless_channelequiv_def, #termP_term_REP tydefrec] >>
  simp[SF CONJ_ss, #term_ABS_pseudo11 tydefrec] >>
  simp[SF CONJ_ss, FUN_EQ_THM, memoryless_channel_AR_def, #termP_term_REP tydefrec, CONJ_COMM]
  (* Because our representation type is a function, FUN_EQ_THM was accidentally
     applied to the function, breaking the old working from genericGraphScript.
     So I patch it up here by unapplying FUN_EQ_THM where it isn't needed. *)
  >> rpt gen_tac
  >> simp[GSYM FUN_EQ_THM]
  >> ‘c = (λx. memoryless_channel_REP a x) ⇔ c = memoryless_channel_REP a’ by simp[FUN_EQ_THM]
  >> simp[]
  >> pop_assum kall_tac
  (* Continue with old working *)
  >> simp[EQ_IMP_THM, #termP_term_REP tydefrec, #absrep_id tydefrec,
          #repabs_pseudo_id tydefrec]
  (* For some reason, undoing FUN_EQ_THM wasn't quite enough, although it did
     help with one direction, so I patch it up by proving this myself *)
  >> strip_tac
  >> gvs[]
  >> simp[#repabs_pseudo_id tydefrec]
QED

Datatype:
  erasure_bit = E_T | E_F | Erasure
End

Definition bool_to_erasure_bit_def:
  bool_to_erasure_bit b = if b then E_T else E_F
End

Definition binary_erasure_channel_rep_def:
  binary_erasure_channel_rep (p : extreal) : bool -> erasure_bit m_space =
  (λinput.
     (𝕌(:erasure_bit),
      POW (𝕌(:erasure_bit)),
      EXTREAL_SUM_IMAGE (λoutput. if output = Erasure
                                  then p
                                  else
                                    if output = bool_to_erasure_bit input
                                    then 1 - p
                                    else 0)))
End

Definition binary_erasure_channel_def:
  erasure_channel p : (bool, erasure_bit) memoryless_channel =
  memoryless_channel_ABS (binary_erasure_channel_rep p)
End

Definition binary_symmetric_channel_rep_def:
  binary_symmetric_channel_rep (p : extreal) : bool -> bool m_space =
  (λinput.
     (𝕌(:bool),
      POW (𝕌(:bool)),
      EXTREAL_SUM_IMAGE (λoutput. if output ≠ input
                                  then p
                                  else 1 - p
                        )
     )
  )
End

Definition binary_symmetric_channel_def:
  binary_symmetric_channel p : (bool, bool) memoryless_channel =
  memoryless_channel_ABS (binary_symmetric_channel_rep p)
End

(* mathcal_2 represents {T;F} *)
Theorem POW_mathcal_2:
  POW 𝟚 = {∅; {T}; {F}; {T; F}}
Proof
  simp[EXTENSION]
  >> gen_tac
  >> simp[POW_DEF, SUBSET_DEF]
  >> Cases_on ‘x’ >> simp[]
  >> Cases_on ‘x'’ >> simp[]
  >> (Cases_on ‘t’ >> simp[]
      >> Cases_on ‘x’ >> simp[]
      >> ASM_SET_TAC[])
QED

Theorem finite_mathcal_2:
  FINITE 𝟚
Proof
  simp[]
QED

Theorem UNIV_ERASURE_BIT[simp]:
  𝕌(:erasure_bit) = {E_T;E_F;Erasure}
Proof
  simp[EXTENSION]
  >> gen_tac
  >> Cases_on ‘x’ >> simp[]
QED

Theorem FINITE_UNIV_ERASURE_BIT:
  FINITE (𝕌(:erasure_bit))
Proof
  simp[]
QED

Theorem FINITE_UNIV_ERASURE_BIT_ALT:
  FINITE {E_T;E_F;Erasure}
Proof
  simp[]
QED

Theorem wf_binary_erasure_channel:
  ∀p.
    0 ≤ p ∧ p ≤ 1 ⇒
    wf_memoryless_channel (binary_erasure_channel_rep p)
Proof  
  gen_tac >> strip_tac
  >> Cases_on ‘p’ >> gvs[]
  >> simp[wf_memoryless_channel_def]
  >> gen_tac >> strip_tac >> simp[binary_erasure_channel_rep_def]
  >> simp[prob_space_def]
  >> REVERSE conj_tac             
  >- (qmatch_abbrev_tac ‘EXTREAL_SUM_IMAGE f _ = _’
      >> sg ‘(∀x. f x ≠ +∞)’
      >- (gen_tac >> simp[Abbr ‘f’] >> rw[]
          >> irule (cj 2 sub_not_infty)
          >> simp[])
      >> simp[EXTREAL_SUM_IMAGE_INSERT, DELETE_NON_ELEMENT_RWT]
      >> Q.UNABBREV_TAC ‘f’
      >> simp[]
      >> Cases_on ‘x’ >> simp[bool_to_erasure_bit_def]
     )
  >> irule finite_additivity_sufficient_for_finite_spaces2
  >> simp[m_space_def]
  >> rpt conj_tac
  >- (simp[additive_def]
      >> rpt gen_tac >> strip_tac
      >> sg ‘FINITE s ∧ FINITE t’
      >- (gvs[POW_DEF]
          >> metis_tac[SUBSET_FINITE, FINITE_UNIV_ERASURE_BIT_ALT])
      >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_DISJOINT_UNION]
      >> conj_tac
      >- (simp[]
          >> disj2_tac
          >> gen_tac >> strip_tac
          >> rw[]
          >> irule (cj 2 sub_not_infty)
          >> simp[])
      >> rw[])     
  >- (simp[positive_def]
      >> gen_tac >> strip_tac
      >> irule EXTREAL_SUM_IMAGE_POS
      >> gvs[POW_DEF]
      >> REVERSE conj_tac
      >- metis_tac[SUBSET_FINITE, FINITE_UNIV_ERASURE_BIT_ALT]
      >> gen_tac >> strip_tac
      >> rw[]
      >> simp[GSYM normal_1, GSYM normal_0, extreal_sub_def]
      >> simp[REAL_SUB_LE]
     )
  >> irule POW_SIGMA_ALGEBRA
QED

Theorem wf_binary_symmetric_channel:
  ∀p.
    0 ≤ p ∧ p ≤ 1 ⇒
    wf_memoryless_channel (binary_symmetric_channel_rep p)
Proof
  gen_tac >> strip_tac
  >> Cases_on ‘p’ >> gvs[]
  >> simp[wf_memoryless_channel_def]
  >> gen_tac >> strip_tac >> simp[binary_symmetric_channel_rep_def]
  >> simp[prob_space_def]
  >> REVERSE conj_tac
  >- (qmatch_abbrev_tac ‘EXTREAL_SUM_IMAGE f _ = _’
      >> sg ‘(∀x. f x ≠ +∞)’
      >- (gen_tac >> simp[Abbr ‘f’] >> rw[]
          >> irule (cj 2 sub_not_infty)
          >> simp[])
      >> simp[EXTREAL_SUM_IMAGE_INSERT]
      >> simp[DELETE_NON_ELEMENT_RWT]
      >> Q.UNABBREV_TAC ‘f’
      >> simp[]
      >> rw[]
      >> simp[sub_add2]
     )
  >> irule finite_additivity_sufficient_for_finite_spaces2
  >> simp[m_space_def]
  >> rpt conj_tac         
  >- (simp[additive_def]
      >> rpt gen_tac >> strip_tac
      >> sg ‘FINITE s ∧ FINITE t’
      >- (gvs[POW_DEF]
          >> metis_tac[SUBSET_FINITE, finite_mathcal_2])
      >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_DISJOINT_UNION]
      >> conj_tac
      >- (simp[]
          >> disj2_tac
          >> gen_tac >> strip_tac
          >> rw[]
          >> irule (cj 2 sub_not_infty)
          >> simp[])
      >> rw[]
      >> irule (cj 2 sub_not_infty)
      >> simp[]
     )
  >- (simp[positive_def]
      >> gen_tac >> strip_tac
      >> irule EXTREAL_SUM_IMAGE_POS
      >> gvs[POW_DEF]
      >> REVERSE conj_tac
      >- metis_tac[SUBSET_FINITE, finite_mathcal_2]
      >> gen_tac >> strip_tac
      >> rw[]
      >> simp[GSYM normal_1, GSYM normal_0, extreal_sub_def]
      >> simp[REAL_SUB_LE]
     )
  >> irule POW_SIGMA_ALGEBRA
QED


