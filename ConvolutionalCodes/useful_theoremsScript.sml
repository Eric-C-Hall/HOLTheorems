open HolKernel Parse boolLib bossLib;

open arithmeticTheory;

val _ = new_theory "useful_theorems";

open listTheory;
open rich_listTheory;

(* One of the more useful theorems in this file *)
Theorem MAX_SUC:
  ∀n m. MAX (SUC n) (SUC m) = SUC (MAX n m)
Proof
  rpt strip_tac
  >> gvs[MAX_DEF]
QED

Theorem FILTER_EXISTS:
  ∀f bs.
  FILTER f bs ≠ [] ⇔ EXISTS f bs
Proof
  rpt strip_tac 
  >> Induct_on ‘bs’
  >- gvs[]
  >> rpt strip_tac
  >> gvs[FILTER]
  >> Cases_on ‘f h’ >> gvs[]
QED

Theorem FILTER_EXISTS2:
  ∀f bs.
  FILTER f bs = [] ⇔ ¬(EXISTS f bs)
Proof
  PURE_REWRITE_TAC[GSYM FILTER_EXISTS]
  >> gvs[]
QED

Theorem length_suc_nonempty[simp]:
  ∀ls n.
  LENGTH ls = SUC n ⇒ ls ≠ []
Proof
  Cases_on ‘ls’ >> gvs[]  
QED

Theorem HD_SNOC:
  ∀l ls.
  HD (SNOC l ls) = if ls = [] then l else HD ls
Proof
  rpt strip_tac
  >> Cases_on ‘ls’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Copy of EL_REPLICATE, but added to the simpset so it is automatically      *)
(* applied, because this seems like a sensible simplification rule.           *)
(* -------------------------------------------------------------------------- *)
Theorem EL_REPLICATE_AUTO[simp]:
  ∀n1 n2 x.
  n1 < n2 ⇒ EL n1 (REPLICATE n2 x) = x
Proof
  gvs[EL_REPLICATE]
QED

val _ = export_theory();
