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

Theorem COUNT_LIST_EMPTY[simp]:
  ∀n.
    COUNT_LIST n = [] ⇔ n = 0
Proof
  rpt strip_tac
  >> Cases_on ‘n’ >> gvs[COUNT_LIST_def]
QED

Theorem MEM_ZERO_MAP_SUC[simp]:
  ∀ls.
    MEM 0 (MAP SUC ls) ⇔ F
Proof
  rpt strip_tac
  >> Induct_on ‘ls’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* This comes up frequently, so it's nice to automatically simplify it.       *)
(* -------------------------------------------------------------------------- *)
Theorem MULT_LR_CANCEL[simp]:
  ∀a b c : num.
    0 < a ⇒
    (a * b = c * a ⇔ b = c)
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[Once MULT_COMM]
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* This comes up frequently, so it's nice to automatically simplify it.       *)
(* -------------------------------------------------------------------------- *)
Theorem MULT_RL_CANCEL[simp]:
  ∀a b c : num.
    0 < a ⇒
    (b * a = a * c ⇔ b = c)
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[Once MULT_COMM]
  >> gvs[]
QED

(* I'm surprised this doesn't exist already *)
Theorem MIN_SUC:
  ∀a b.
    MIN (SUC a) (SUC b) = SUC (MIN a b)
Proof
  rpt strip_tac
  >> gvs[MIN_DEF]
QED

(* I'm surprised this doesn't exist already *)
Theorem TAKE_REPLICATE:
  ∀l n v.
    TAKE l (REPLICATE n v) = REPLICATE (MIN l n) v
Proof
  Induct_on ‘l’ >> gvs[]
  >> Cases_on ‘n’ >> gvs[]
  >> rpt strip_tac
  >> gvs[MIN_SUC]
  >> gvs[TAKE]
QED

val _ = export_theory();
