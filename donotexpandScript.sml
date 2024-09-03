open HolKernel Parse boolLib bossLib;

open simpLib

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

(* tactic that allows you to tell HOL4 to not expand the top theorem *)
val donotexpand_tac =
(* abbreviate relevant assumption *)
qmatch_asmsub_abbrev_tac ‘donotexpand_var’
(* Ignore top assumption (Abbrev), apply donotexpand to second assumption *)
>> pop_assum (fn th => drule $ iffRL donotexpand_thm >> assume_tac th)
(* expand abbreviation *)
>> simp_tac empty_ss [Abbr ‘donotexpand_var’]
(* remove original assumption without donotexpand *)
>> pop_assum kall_tac
(* discharge donotexpand-ed assumption to assumptions *)
>> disch_tac

(* Tactic that undoes the effect of donotexpand_tac *)
val doexpand_tac =
(* abbreviate assumption to expand *)
qmatch_asmsub_abbrev_tac ‘donotexpand donotexpand_var’
(* move assumption to expand to top *)
>> qpat_x_assum ‘donotexpand donotexpand_var’ assume_tac
(* expand assumption*)
>> ‘donotexpand_var’ by (irule $ iffLR donotexpand_thm >> simp[])
(* remove unexpanded assumption *)
>> qpat_x_assum ‘donotexpand donotexpand_var’ kall_tac
(* unabbreviate assumption *)
>> simp_tac empty_ss [Abbr ‘donotexpand_var’]

val _ = export_theory();
