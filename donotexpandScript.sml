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

val _ = export_theory();
