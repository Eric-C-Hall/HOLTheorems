open HolKernel Parse boolLib bossLib;

val _ = new_theory "interleave";

open listTheory;
open arithmeticTheory;

(* -------------------------------------------------------------------------- *)
(* Takes a list of lists. Interleaves these lists.                            *)
(*                                                                            *)
(* e.g. [[a;a;a];[b;b;b];[c;c;c]] becomes [a;b;c;a;b;c;a;b;c]                 *)
(*                                                                            *)
(* If any list is shorter than the others, truncates the remaining lists to   *)
(* match.                                                                     *)
(* -------------------------------------------------------------------------- *)
Definition interleave_def:
  interleave ls = if MEM [] ls ∨ ls = []
                  then
                    []
                  else
                    (MAP HD ls) ++ interleave (MAP TL ls)
Termination
  WF_REL_TAC ‘measure (λls. MIN_LIST (MAP LENGTH ls))’
  >> rw[]
  >> Induct_on ‘ls’ >> rw[]
  >> qabbrev_tac ‘l=h’ >> qpat_x_assum ‘Abbrev _’ kall_tac
  >> gvs[]
  >> ‘0 < LENGTH l’ by gvs[LENGTH_NON_NIL]
  >> Cases_on ‘ls’ >> gvs[LENGTH_TL]
  >> qabbrev_tac ‘l2=h’ >> qpat_x_assum ‘Abbrev _’ kall_tac
  >> gvs[MIN_DEF]
End

val _ = export_theory();
