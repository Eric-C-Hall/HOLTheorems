open HolKernel Parse boolLib bossLib;

open pred_setTheory;
open prim_recTheory;
open relationTheory;

val _ = new_theory "WFTheorems";

(* From memory, I think some of these theorems might actually already exist somewhere, perhaps? *)

(* WF_inv_image *)

(* Apparently it's a better idea to do something along the lines of WF_REL_TAC `measure (LENGTH o SND)` *)

Theorem WF_LENGTH:
  WF (λbs cs : α list. LENGTH bs < LENGTH cs)
Proof
  gvs[WF_DEF]
  >> rpt strip_tac
  >> assume_tac WF_LESS
  >> drule $ iffLR WF_DEF >> strip_tac
  >> first_x_assum $ qspec_then ‘IMAGE (λbs. LENGTH bs) B’ assume_tac
  >> gvs[]
  >> rpt strip_tac
  >> qmatch_asmsub_abbrev_tac ‘p ⇒ g’
  >> sg ‘p’
  >- (unabbrev_all_tac >> qexists ‘w’ >> gvs[IN_DEF])
  >> gvs[]
  >> pop_assum kall_tac
  >> qexists ‘bs’
  >> gvs[IN_DEF]
QED

Theorem WF_IMAGE:
  ∀R f. WF R ⇒ WF (λx y. R (f x) (f y))
Proof
  rpt strip_tac
  >> gvs[WF_DEF]
  >> rpt strip_tac
  >> first_x_assum $ qspec_then ‘IMAGE f B’ assume_tac
  >> qmatch_asmsub_abbrev_tac ‘p ⇒ g’
  >> sg ‘p’
  >- (unabbrev_all_tac >> qexists ‘f w’ >> gvs[IMAGE_DEF] >> qexists ‘w’ >> gvs[IN_DEF])
  >> gvs[]
  >> pop_assum kall_tac
  >> qexists ‘x’
  >> conj_tac
  >- gvs[IN_DEF]
  >> gen_tac
  >> disch_tac
  >> first_x_assum $ qspec_then ‘f x'’ assume_tac
  >> gvs[]
  >> first_x_assum $ qspec_then ‘x'’ assume_tac
  >> gvs[IN_DEF]
QED

val _ = export_theory();
