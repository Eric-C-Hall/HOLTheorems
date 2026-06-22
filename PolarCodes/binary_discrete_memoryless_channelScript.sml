(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory binary_discrete_memoryless_channel

Ancestors arithmetic lifting pred_set measure sigma_algebra transfer probability

Libs liftLib transferLib;

(* -------------------------------------------------------------------------- *)
(* Possible improvement: extract this to library                              *)
(* -------------------------------------------------------------------------- *)
Theorem finite_countably_additive_finite_additive:
  ∀m.
    FINITE (m_space m) ∧
    positive m ∧
    ∅ ∈ measurable_sets m ⇒
    (countably_additive m ⇔ finite_additive m)

Proof

  gen_tac >> strip_tac
  >> EQ_TAC
  >- (strip_tac
      >> irule COUNTABLY_ADDITIVE_FINITE_ADDITIVE
      >> simp[])
  >> strip_tac
  >> gvs[finite_additive_def]
  >> simp[countably_additive_def]
  >> gen_tac >> strip_tac
  >> gvs[FUNSET]
  >> cheat (* TODO Ask Chun *)
  
QED

(* -------------------------------------------------------------------------- *)
(* Possible improvement: extract this to library                              *)
(* -------------------------------------------------------------------------- *)
Theorem finite_countably_additive:
  ∀m.
    FINITE (m_space m) ∧
    (∀S T. S ∈ measurable_sets m ∧
           T ∈ measurable_sets m ∧
           DISJOINT S T ⇒
           measure m S + measure m T = measure m (S ∪ T)) ⇒
    countably_additive m
                       
Proof
  
  gen_tac >> strip_tac
  >> simp[countably_additive_def] 
  >> gen_tac >> strip_tac
  
  >> cheat (* TODO Ask Chun *)
QED

(* -------------------------------------------------------------------------- *)
(* A binary discrete memoryless channel                                       *)
(* - Takes a bit as input                                                     *)
(* - Returns a discrete value (with type α) as output                         *)
(* - For each input bit, the distribution over output bits is a probability   *)
(*   distribution.                                                            *)
(*                                                                            *)
(* We express this as                                                         *)
(*   bool -> α m_space                                                        *)
(* Where we output a probability space, denoting the distribution over output *)
(* bits                                                                       *)
(* -------------------------------------------------------------------------- *)
Definition wf_bdmc_def:
  wf_bdmc (W : bool -> α m_space) = ∀b. prob_space (W b)
End

Theorem wf_bdmcs_exist[local]:
  ∃x. wf_bdmc x
Proof  
  qexists ‘λb. ({ARB}, {{};{ARB}}, λs. if s = {ARB} then 1 else 0)’
  >> simp[wf_bdmc_def]
  >> simp[prob_space_def]
  >> simp[measure_space_def]
  >> rpt conj_tac         
  >- (simp[sigma_algebra_def]
      >> conj_tac         
      >- (simp[algebra_def]
          >> rpt conj_tac
          >- (simp[subset_class_def]
              >> gen_tac >> disch_tac
              >> gvs[])
          >> rpt gen_tac
          >> disch_tac
          >> gvs[]
         )
      >> rpt strip_tac
      >> gvs[SUBSET_DEF]
      >> Cases_on ‘c’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[]     
      >> Cases_on ‘t'’ >> gvs[]
     >- (last_assum $ qspec_then ‘x'’ assume_tac
         >> last_x_assum $ qspec_then ‘x’ assume_tac
         >> gvs[]
        )
      (* We have 3 distinct elements, but {∅;{ARB}} only has 2 *)
      >> last_assum $ qspec_then ‘x’ assume_tac
      >> last_assum $ qspec_then ‘x'’ assume_tac
      >> last_x_assum $ qspec_then ‘x''’ assume_tac
      >> gvs[]
     )
  >- (simp[positive_def]
      >> gen_tac
      >> disch_tac
      >> gvs[])
  >> irule finite_countably_additive
  >> REVERSE conj_tac
  >- simp[]
  >> rpt gen_tac >> strip_tac
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Create new abstract type consisting of well-formed state machines          *)
(* -------------------------------------------------------------------------- *)
val tydefrec = newtypeTools.rich_new_type { tyname = "bdmc",
exthm  = wf_bdmcs_exist,
ABS = "bdmc_ABS",
REP = "bdmc_REP"};

(* -------------------------------------------------------------------------- *)
(* Something used in the lifting process, not sure about the details.         *)
(*                                                                            *)
(* Tells us whether two state machines are equivalent when considered as      *)
(* their abstract counterpart: thus, non-well-formed state machines are not   *)
(* equivalent, as they cannot be considered to be their abstract counterpart  *)
(* -------------------------------------------------------------------------- *)
Definition bdmcequiv_def:
  bdmcequiv m1 m2 ⇔ m1 = m2 ∧ wf_bdmc m2
End

(* -------------------------------------------------------------------------- *)
(* A relation which relates a well-formed representative of a state machine   *)
(* to its corresponding abstract value.                                       *)
(* -------------------------------------------------------------------------- *)
Definition bdmc_AR_def:
  bdmc_AR r a ⇔ wf_bdmc r ∧ r = bdmc_REP a
End

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem bdmc_relates[transfer_rule]:
  (bdmc_AR ===> (=)) wf_bdmc (K T)
Proof
  simp[FUN_REL_def, bdmc_AR_def]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem bdmc_AReq_relates[transfer_rule]:
  (bdmc_AR ===> bdmc_AR ===> (=)) (=) (=)
Proof
  simp[bdmc_AR_def, FUN_REL_def, #termP_term_REP tydefrec, #term_REP_11 tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem right_unique_bdmc_AR[transfer_simp]:
  right_unique bdmc_AR
Proof
  simp[right_unique_def, bdmc_AR_def, #term_REP_11 tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem surj_bdmc_AR[transfer_simp]:
  surj bdmc_AR
Proof
  simp[surj_def, bdmc_AR_def, #termP_term_REP tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem RDOM_bdmc_AR[transfer_simp]:
  RDOM bdmc_AR = {gr | wf_bdmc gr}
Proof
  simp[relationTheory.RDOM_DEF, Once FUN_EQ_THM, bdmc_AR_def, SF CONJ_ss,
       #termP_term_REP tydefrec] >>
  metis_tac[#termP_term_REP tydefrec, #repabs_pseudo_id tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem Qt_bdmc[liftQt]:
  Qt bdmcequiv bdmc_ABS bdmc_REP bdmc_AR
Proof
  simp[Qt_alt, bdmc_AR_def, #absrep_id tydefrec, bdmcequiv_def, #termP_term_REP tydefrec] >>
  simp[SF CONJ_ss, #term_ABS_pseudo11 tydefrec] >>
  simp[SF CONJ_ss, FUN_EQ_THM, bdmc_AR_def, #termP_term_REP tydefrec,
       CONJ_COMM]
  (* Because our representation type is a function, FUN_EQ_THM was accidentally
     applied to the function, breaking the old working from genericGraphScript.
     So I patch it up here by unapplying FUN_EQ_THM where it isn't needed. *)
  >> rpt gen_tac
  >> simp[GSYM FUN_EQ_THM]
  >> ‘c = (λx. bdmc_REP a x) ⇔ c = bdmc_REP a’ by simp[FUN_EQ_THM]
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



