open HolKernel Parse boolLib bossLib;

val _ = new_theory "interleave";

open listTheory;
open rich_listTheory;
open arithmeticTheory;
open dividesTheory;

open ConseqConv; (* SPEC_ALL_TAC *)

(* -------------------------------------------------------------------------- *)
(* Takes a list of lists. Interleaves these lists.                            *)
(*                                                                            *)
(* e.g. [[a;a;a];[b;b;b];[c;c;c]] becomes [a;b;c;a;b;c;a;b;c]                 *)
(*                                                                            *)
(* If any list is shorter than the others, truncates the remaining lists to   *)
(* match.                                                                     *)
(*                                                                            *)
(* Note: not easy to use as a rewrite rule because it has the LHS within the  *)
(*       RHS. Perhaps there's a better definition?                            *)
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

(* -------------------------------------------------------------------------- *)
(* Gets every nth element of a list                                           *)
(*                                                                            *)
(* ls: the list to get every nth element from                                 *)
(* n: the value of n to get every nth element for                             *)
(* i: an offset to start getting every nth element from. 0 if we want to      *)
(*    include the 0th element of the list, 1 if we want to start from the     *)
(*    1st element of the list, and so on.                                     *)
(* -------------------------------------------------------------------------- *)
Definition get_every_nth_element_def:
  get_every_nth_element [] _ _ = [] ∧
  get_every_nth_element (l::ls) n 0 = l::(get_every_nth_element ls n (n - 1)) ∧
  get_every_nth_element (l::ls) (n) (SUC i) = get_every_nth_element ls n i
End


(* -------------------------------------------------------------------------- *)
(* Takes an interleaved list, and the number of lists that it is comprised    *)
(* of, and returns the original, deinterleaved lists.                         *)
(*                                                                            *)
(* e.g. deinterleave 3 [[a;a;a];[b;b;b];[c;c;c]] returns [a;b;c;a;b;c;a;b;c]  *)
(*                                                                            *)
(* If the length of the list is not a multiple of the number of lists, then   *)
(* the output lists may be of different lengths to each other.                *)
(* -------------------------------------------------------------------------- *)
Definition deinterleave_def:
  deinterleave n ls =
  MAP (get_every_nth_element ls n) (COUNT_LIST n)
End

Theorem interleave_empty[simp]:
  interleave [] = []
Proof
  gvs[Once interleave_def]
QED

Theorem get_every_nth_element_empty[simp]:
  ∀n i.
    get_every_nth_element [] n i = []
Proof
  gvs[get_every_nth_element_def]
QED

Theorem MAP_REPLICATE_FORALL:
  ∀f ls n x.
    MAP f ls = REPLICATE n x ⇔ (∀l. MEM l ls ⇒ f l = x) ∧ LENGTH ls = n
Proof
  rw[]
  >> EQ_TAC
  >- (disch_tac
      >> sg ‘LENGTH ls = n’
      >- (rpt $ pop_assum mp_tac >> SPEC_ALL_TAC
          >> Induct_on ‘n’ >- gvs[]
          >> rw[]
          >> Cases_on ‘ls’ >> gvs[]
          >> metis_tac[]
         )
      >> gvs[]
      >> rpt $ pop_assum mp_tac >> SPEC_ALL_TAC
      >> Induct_on ‘ls’ >- gvs[]
      >> rw[]
      >> metis_tac[]
     )
  >> rw[]
  >> rpt $ pop_assum mp_tac >> SPEC_ALL_TAC
  >> Induct_on ‘ls’ >- gvs[]
  >> rw[]
QED

Theorem deinterleave_empty[simp]:
  ∀n.
    deinterleave n [] = REPLICATE n []
Proof
  rw[deinterleave_def]
  >> gvs[MAP_REPLICATE_FORALL]
  >> gvs[LENGTH_COUNT_LIST]
QED

Theorem interleave_replicate_empty[simp]:
  ∀n.
    interleave (REPLICATE n []) = []
Proof
  rw[Once interleave_def]
QED

Theorem COUNT_LIST_EMPTY[simp]:
  ∀n.
    COUNT_LIST n = [] ⇔ n = 0
Proof
  rw[]
  >> Cases_on ‘n’
  >> gvs[COUNT_LIST_def]
QED

(* -------------------------------------------------------------------------- *)
(* Deinterleaving followed by interleaving is the identity.                   *)
(* -------------------------------------------------------------------------- *)
(*Theorem interleave_deinterleave:
  ∀n ls.
    divides n (LENGTH ls) ⇒
    interleave (deinterleave n ls) = ls
Proof
  rw[]
  >> gvs[divides_def]
  >> pop_assum mp_tac >> SPEC_ALL_TAC
  >> Induct_on ‘q’ >- rw[]
  >> rw[]
  >> PURE_REWRITE_TAC[deinterleave_def]
  >> PURE_REWRITE_TAC[Once interleave_def]
  >> gvs[]
QED*)

(* -------------------------------------------------------------------------- *)
(* Interleaving followed by deinterleaving is the identity                    *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(*Theorem deinterleave_interleave:

Proof
QED*)

val _ = export_theory();
