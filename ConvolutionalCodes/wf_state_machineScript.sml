(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

(* Lifting and transfer libraries *)
open liftLib liftingTheory transferLib transferTheory;

open state_machineTheory;

val _ = new_theory "wf_state_machine";

Theorem wf_state_machines_exist[local]:
  ∃x. wfmachine x
Proof
  metis_tac[wfmachine_example_state_machine]
QED

(* -------------------------------------------------------------------------- *)
(* Create new abstract type consisting of well-formed state machines          *)
(* -------------------------------------------------------------------------- *)
val tydefrec = newtypeTools.rich_new_type { tyname = "wf_state_machine",
exthm  = wf_state_machines_exist,
ABS = "wf_state_machine_ABS",
REP = "wf_state_machine_REP"};

(* -------------------------------------------------------------------------- *)
(* Something used in the lifting process, not sure about the details.         *)
(*                                                                            *)
(* Tells us whether two state machines are equivalent when considered as      *)
(* their abstract counterpart: thus, non-well-formed state machines are not   *)
(* equivalent, as they cannot be considered to be their abstract counterpart  *)
(* -------------------------------------------------------------------------- *)
Definition smequiv_def:
  smequiv m1 m2 ⇔ m1 = m2 ∧ wfmachine m2
End

(* -------------------------------------------------------------------------- *)
(* A relation which relates a well-formed representative of a state machine   *)
(* to its corresponding abstract value.                                       *)
(* -------------------------------------------------------------------------- *)
Definition sm_AR_def:
  sm_AR r a ⇔ wfmachine r ∧ r = wf_state_machine_REP a
End

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem wfmachine_relates[transfer_rule]:
  (sm_AR ===> (=)) wfmachine (K T)
Proof
  simp[FUN_REL_def, sm_AR_def]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem sm_AReq_relates[transfer_rule]:
  (sm_AR ===> sm_AR ===> (=)) (=) (=)
Proof
  simp[sm_AR_def, FUN_REL_def, #termP_term_REP tydefrec, #term_REP_11 tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem right_unique_sm_AR[transfer_simp]:
  right_unique sm_AR
Proof
  simp[right_unique_def, sm_AR_def, #term_REP_11 tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem surj_sm_AR[transfer_simp]:
  surj sm_AR
Proof
  simp[surj_def, sm_AR_def, #termP_term_REP tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem RDOM_sm_AR[transfer_simp]:
  RDOM sm_AR = {gr | wfmachine gr}
Proof
  simp[relationTheory.RDOM_DEF, Once FUN_EQ_THM, sm_AR_def, SF CONJ_ss,
       #termP_term_REP tydefrec] >>
  metis_tac[#termP_term_REP tydefrec, #repabs_pseudo_id tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem Qt_machines[liftQt]:
  Qt smequiv wf_state_machine_ABS wf_state_machine_REP sm_AR
Proof
  simp[Qt_alt, sm_AR_def, #absrep_id tydefrec, smequiv_def, #termP_term_REP tydefrec]>>
  simp[SF CONJ_ss, #term_ABS_pseudo11 tydefrec] >>
  simp[SF CONJ_ss, FUN_EQ_THM, sm_AR_def, #termP_term_REP tydefrec,
       CONJ_COMM] >>
  simp[EQ_IMP_THM, #termP_term_REP tydefrec, #absrep_id tydefrec,
       #repabs_pseudo_id tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Get the transition function associated with the underlying representation  *)
(* -------------------------------------------------------------------------- *)
Definition wfm_transition_fn_def:
  wfm_transition_fn m = (wf_state_machine_REP m).transition_fn
End

(* -------------------------------------------------------------------------- *)
(* Find the state/input pairs that lead directly to a particular state        *)
(* -------------------------------------------------------------------------- *)
Definition wfm_transition_inverse_def:
  wfm_transition_inverse m s =
  {(s', b) | FST ((wfm_transition_fn m) (s', b)) = s}
End




val _ = export_theory();
