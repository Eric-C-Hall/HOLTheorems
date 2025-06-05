open HolKernel Parse boolLib bossLib;

val _ = new_theory "donotexpand";

(* TODO: Find better way to do this *)
Definition donotexpand_def:
  donotexpand P = P
End

Theorem donotexpand_thm:
  donotexpand P ⇔ P
Proof
  gvs[donotexpand_def]
QED

Definition MEM_DONOTEXPAND_def:
  MEM_DONOTEXPAND = $MEM
End

Theorem MEM_DONOTEXPAND_thm:
  ∀l ls.
  MEM_DONOTEXPAND l ls = MEM l ls
Proof
  rpt strip_tac >> EVAL_TAC
QED

val _ = export_theory();
