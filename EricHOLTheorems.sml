(* Written by Eric Hall, with edits by Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "EricHOLTheorems";

open arithmeticTheory;
open dividesTheory; (* prime *)
open whileTheory; (* LEAST *)
open numLib; (* LEAST_ELIM_TAC *)
open realTheory;
open gcdTheory;
open listTheory;

(* Copied from tutorial  *)
Theorem less_add_1:
  ∀n:num. n < n + 1
Proof
  decide_tac
QED

(* Copied from tutorial *)
Theorem less_eq_mult:
  ∀n:num. n <= n * n
Proof
  Induct_on ‘n’ >> simp[]
QED

(* How does arithmetic work *)
Theorem the_meaning_of_life:
  6n * 7 = 42
Proof
  simp[]
QED

(* How does arithmetic work *)
Theorem one_plus_one:
  1 + 1 = 2
Proof
  simp[]
QED

(* Implication test *)
Theorem implication_test:
  ∀n:num. (n > 3 ⇒ n + 1 > 4)
Proof
  simp[]
QED

(***************************************************************************)
(* Testing how HOL works with regards to formatting nested >- operators    *)
(* Apparently you need to use parentheses to help format the >- operators  *)
(* Otherwise the following theorem doesn't compile                         *)
(***************************************************************************)
Theorem test_subgoals:
  T
Proof
  sg ‘T’
    >- (sg ‘T’
      >- decide_tac)
QED

Theorem all_numbers_above_eight_constructible:
  ∀n:num. n >= 8 ⇒ ∃a. ∃b. a * 3 + b * 5 = n
Proof
  Induct_on ‘n’ >- gvs[] >>
  strip_tac
  >> Cases_on ‘n >= 9’
  >- (gs[] >>
      Cases_on ‘b = 0’ >> gvs[]
      >- (‘3 ≤ a’ by simp[] >>
          qexists ‘a - 3’ >> qexists ‘2’ >> simp[]) >>
      qexistsl [‘a + 2’, ‘b - 1’] >> simp[]) >>
  ‘n = 7 ∨ n = 8’ by simp[] >> gvs[] >>
  qexistsl [‘1’, ‘1’] >> simp[]
QED

Theorem cancel_mult_both_sides:
  ∀a b c. ¬(c = 0n) ⇒ (c * a = c * b ⇒ a = b)
Proof
  full_simp_tac arith_ss []
QED

Definition sum_first_n_def:
  (sum_first_n 0 = 0n) ∧
  (sum_first_n (SUC n) = (SUC n) + sum_first_n n)
End

Theorem sum_of_natural_numbers:
  ∀n. sum_first_n n = (n * (n + 1)) DIV 2
Proof
  Induct_on ‘n’ >> asm_simp_tac arith_ss [sum_first_n_def] >>
  pop_assum kall_tac >>
  ‘(n + 1) + n * (n + 1) DIV 2 = (n + 1) * (n + 2) DIV 2’
    suffices_by simp[ADD1] >>
  ‘(2 * n + 2) DIV 2 + n * (n + 1) DIV 2 = (n + 1) * (n + 2) DIV 2’
    suffices_by full_simp_tac arith_ss [] >>
  ‘(2 * n + 2 + n * (n + 1)) DIV 2 = (n + 1) * (n + 2) DIV 2’
    suffices_by full_simp_tac arith_ss [ADD_DIV_RWT] >>
  ‘2 * n + 2 + n * (n + 1) = (n + 1) * (n + 2)’ by full_simp_tac arith_ss [] >>
  simp[]
QED

(* Based on pre-existing prime functionality/theorems, which did most of the work for me*)
Theorem exists_arbitrarily_large_primes:
  ∀n. ∃p. prime p ∧ p > n
Proof
  rpt strip_tac
  >> qspec_then ‘n’ assume_tac NEXT_LARGER_PRIME
  >> full_simp_tac arith_ss []
  >> pop_assum kall_tac
  >> qexists ‘PRIMES i’
  >> full_simp_tac arith_ss []
  >> pop_assum kall_tac
  >> full_simp_tac arith_ss [primePRIMES]
QED

Theorem triangle_inequality:
  ∀x y. ABS_DIFF (x + y) 0 <= ABS_DIFF x 0 + ABS_DIFF y 0
Proof
  full_simp_tac arith_ss []
QED

(* simple theorem about the real numbers *)
Theorem test_real_theorem:
  ∀x: real. 2 * x = x + x
Proof
  rpt strip_tac
  >> ‘2 = 1 + 1’ by full_simp_tac arith_ss [REAL_ADD]
  >> ‘2 * x = 1 * x + 1 * x’ by full_simp_tac arith_ss [REAL_RDISTRIB, REAL_ADD_RDISTRIB]
  >> full_simp_tac arith_ss [REAL_ADD, REAL_RDISTRIB, REAL_ADD_RDISTRIB, REAL_MUL_LID]
QED

Theorem power_test:
  2 EXP 3 = 8
Proof
  full_simp_tac arith_ss []
QED

Theorem mod_test:
  11 MOD 7 = 4
Proof
  full_simp_tac arith_ss []
QED

Theorem factorial_test:
  FACT 5 = 120
Proof
  EVAL_TAC
QED

assume_tac NPRODUCT_FACT

(*Theorem nproduct_test:
  nproduct (1n .. 3n) (λm. m) = 6
Proof
  EVAL_TAC
QED*)

Theorem tuple_test:
  el 1 (1, 2) = 1
Proof
  simp[el_DEF]
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* This proof of Fermat's little theorem is based on the proof given in       *)
(* Discrete Mathematics with Applications by Susanna Epp, fourth edition,     *)
(* page 494 Theorem 8.4.10                                                    *)
(*                                                                            *)
(* Goal: for p prime, for a not divisible by p, a ^ p mod p = 1               *)
(*                                                                            *)
(* Proof sketch:                                                              *)
(*                                                                            *)
(* Consider l1 = [a mod p, 2a mod p, 3a mod p, ... (p-1)a mod p]              *)
(*                                                                            *)
(* By Lemma 1 (below), no two elements of this list are equal                 *)
(*                                                                            *)
(* By Lemma 2 (below), this function is a reordering of [1, 2, ..., (p-1)]    *)
(*                                                                            *)
(* Therefore, the product of the elements in l1 is equal to the product of    *)
(* the elements in l2 (See Lemma 3)                                           *)
(*                                                                            *)
(* Therefore a^(p-1) * (p-1)! mod p = (p-1)! mod p                            *)
(*                                                                            *)
(* Therefore a^(p-1) mod p = 1                                                *)
(*                                                                            *)
(* QED                                                                        *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* Lemma 1:                                                                   *)
(* (r * a) mod p = (s * a) mod p, p prime, p does not divide a,               *)
(*    and 1 <= s <= r <= (p - 1) ==> s = r                                    *)
(*                                                                            *)
(* Proof:                                                                     *)
(* ((r * a) - (s * a)) mod p = 0                                              *)
(* (r - s) * a mod p = 0                                                      *)
(* p divides ((r - s) * a)                                                    *)
(* p divides (r - s) by assumption p prime, p does not divide a               *)
(* s mod p = r mod p                                                          *)
(* s = r by assumption 1 <= s <= r <= (p - 1)                                 *)
(*                                                                            *)
(* Definition                                                                 *)
(*   is_reordering l1 l2 = (len l1 = len l2 /\                                *)
(*   ∃f.∀i. 1 <= i <= size l1 ==> el i l1 = el (f i) l2)                     *)
(* End                                                                        *)
(*                                                                            *)
(* Definition                                                                 *)
(*                                                                            *)
(* End                                                                        *)
(*                                                                            *)
(* Lemma 2:                                                                   *)
(* if each element of a list l is unique and within [1, len l],               *)
(* then it is a reordering of [1, 2, 3, ..., len l]                           *)
(*                                                                            *)
(* Proof:                                                                     *)
(* Induct on the list                                                         *)
(* Base case: empty list is trivially a reordering of the empty list          *)
(* Inductive step: Consider all elements in the list smaller than len l.      *)
(*   Only at most one element will be removed. Thus we obtain a sublist       *)
(*   of length (l - 1) with all elements within [1, len l - 1], and we can    *)
(*   use the inductive hypothesis.                                            *)
(*                                                                            *)
(* Thus, we have a map from every element except one to [1, len l - 1], and   *)
(*   the element we did not map can be mapped to len l.                       *)
(*                                                                            *)
(* Thus, we have obtained a mapping from the list to [1, len l]               *)
(*                                                                            *)
(* QED                                                                        *)
(*                                                                            *)
(* Lemma 3:                                                                   *)
(*                                                                            *)
(* if two lists are a reordering of each other, then their product is equal   *)
(*                                                                            *)
(* Proof                                                                      *)
(*                                                                            *)
(* Induct on elements of list 1                                               *)
(* Base case: if both lists are empty, trivial                                *)
(* Inductive case: Move the first element of list 1 out the front, and move   *)
(* the corresponding element of list 2 out the front (the ability to do this  *)
(* is itself a lemma)                                                         *)
(*                                                                            *)
(* The remainder of the list is a reordering, so the remaining product is     *)
(* equal                                                                      *)
(*                                                                            *)
(* Thus the product as a whole is equal.                                      *)
(*                                                                            *)
(* QED                                                                        *)
(*                                                                            *)
(* Lemma 1 has an issue where it requires a subtraction, but dealing with     *)
(*   subtraction in the natural numbers can be tricky. This motivates the     *)
(*   following, reworked proof sketch                                         *)
(*                                                                            *)
(* Lemma 1:                                                                   *)
(* (r * a) mod p = (s * a) mod p, p prime, p does not divide a,               *)
(*    and 1 <= s <= r <= (p - 1) ==> s = r                                    *)
(*                                                                            *)
(* Proof:                                                                     *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* r * a - s * a = 0                                                          *)
(*                                                                            *)
(* p |                                                                        *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* No two choices of a, 2a, 3a ... (p - 1)a are congruent modulo op*)

Theorem DIVIDES_MOD0:
  ∀a b : num. 0 < b ⇒ a MOD b = 0 ⇒ divides b a
Proof
  rpt strip_tac
  >> gvs[MOD_EQ_0_DIVISOR, divides_def]
QED

Theorem DIV_MOD_ADD:
  ∀a b: num. 0 < b ⇒ (a DIV b) * b + a MOD b = a
Proof
  rpt strip_tac
  >> gvs[DIVISION]
QED

Theorem MOD_MUL_ADD:
  ∀a m r : num. 0 < m ⇒ a MOD m = r ⇒ ∃b. a = b * m + r
Proof
  rpt strip_tac
  >> qexists `a DIV m`
  >> gvs[DIV_MOD_ADD]
QED

(* Is there an easier way to split an iff than creating my own helper thorem? I tried using irule [EQ_IMP_THM] and looking in the documentation for the relevant tactic but I didn't find anything.*)
Theorem IMP_IMP_IMP_IFF:
  ∀a b : bool. ((a ⇒ b) ∧ (b ⇒ a)) ⇒ (a ⇔ b)
Proof
  gvs[EQ_IMP_THM]
QED

(* MODEQ_INTRO_CONG *)

Theorem MOD_SIMPLIFY:
  ∀a m : num. 0 < m ⇒ ∃a'. a' < m ∧ (a MOD m) = (a' MOD m)
Proof
  rpt strip_tac
  >> qspecl_then [`a`, `m`] assume_tac DA
  >> gs[]
  >> qexists `r`
  >> gs[]
QED

Theorem MOD_ADDITIVE_INVERSE:
  ∀a m : num. 0 < m ⇒ ∃a'. (a + a') MOD m = 0 ∧ a' < m
Proof
  rpt strip_tac
  >> qspecl_then [`a`, `m`] assume_tac DA
  >> gs[]
  >> Cases_on `r = 0`
  >- (qexists `0` >> gs[])
  >> (qexists `m - r` >> gs[])
QED

Theorem MUL_GREATER_EQ:
  ∀a a' b : num. a' >= a ⇒ a' * b >= a * b
Proof
  rpt strip_tac
  >> Induct_on `b`
  >- gvs[]
  >> `(a' : num) * b + a' >= a * b + a` suffices_by gvs[MULT_CLAUSES]
  >> gvs[]
QED

Theorem MOD_ADDITIVE_INVERSE_UNIQUE:
  ∀ a a' a'' m : num. 0 < m ⇒ a' < m ⇒ a'' < m ⇒ (a + a') MOD m = 0 ⇒ (a + a'') MOD m = 0 ⇒ a' = a''
Proof
  rpt strip_tac
  >> qspecl_then [`a`, `m`] assume_tac DA
  >> pop_assum drule >> strip_tac
  >> gvs[]
  >> qspecl_then [`a' + r`, `m`, `0`] assume_tac MOD_MUL_ADD
  >> gvs[]
  >> qspecl_then [`a'' + r`, `m`, `0`] assume_tac MOD_MUL_ADD
  >> gvs[]
  >> sg `∀a r b m : num. a < m ⇒ r < m ⇒ a + r = b * m ⇒ b = 1 ∨ (a = 0 ∧ r = 0 ∧ b = 0)`
  >- (rpt $ pop_assum kall_tac
      >> rpt strip_tac
      >> Cases_on `b >= 2`
      >- (CCONTR_TAC >> pop_assum kall_tac
          >> `a + r >= 2 * m` by
             (last_x_assum kall_tac >> last_x_assum kall_tac
              >> `b : num * m >= 2 * m` suffices_by gvs[]
              >> last_x_assum kall_tac
              >> gvs[MUL_GREATER_EQ])
          >> qpat_x_assum `_ = b * m` kall_tac
          >> gvs[])
      >> Cases_on `b = 0`
      >> gvs[])
  >> first_assum $ qspecl_then [`a'`, `r`, `b`, `m`] assume_tac
  >> first_x_assum $ qspecl_then [`a''`, `r`, `b'`, `m`] assume_tac
  >> rpt (first_x_assum drule >> rpt strip_tac)
  >> gvs[]
QED

n ``_ MOD (m : num) = _ ⇔ _``

(* converse of MODEQ_INTRO_CONG *)
(* I have found in the past that irule doesn't work with an iff but does      *)
(* work with an implication, which is why I wrote this.                       *)
(*                                                                            *)
(* Looking at the documentation, I think maybe I should try using             *)
(* iff{LR,RL} theorem. Maybe this would avoid having to write this new        *)
(* theorem. Upon further inspection, this function is of the form             *)
(* _ => (_ <=> _), and I think this is why it isn't discovering the inner iff.*)
(* My attempts to use iffLR and iffRL didn't work, but maybe there's a way    *)
Theorem MODEQ_ELIM_CONG:
  ∀n e0 e1. 0 < n ⇒ e0 MOD n = e1 MOD n ⇒ MODEQ n e0 e1
Proof
  rpt strip_tac
  >> simp[MODEQ_NONZERO_MODEQUALITY]
QED

Theorem MODEQ_SUB:
  ∀a b m : num. 0 < m ⇒ MODEQ m a b ⇒ MODEQ m (a - b) 0
Proof
  rpt strip_tac
  >> Cases_on `b >= a`
  >- (`a - b = 0` by gvs[]
      >> simp[MODEQ_REFL])
  >> `a > b` by gvs[]
  >> gvs[]
  >> irule MODEQ_ELIM_CONG
  >> gvs[]
  >> drule MODEQ_INTRO_CONG
  >> strip_tac
  >> pop_assum $ qspecl_then [`b`, `a`] assume_tac
  >> pop_assum drule
  >> strip_tac
  >> qpat_x_assum `MODEQ _ _ _` kall_tac
  >> qspecl_then [`b`, `m`] assume_tac MOD_ADDITIVE_INVERSE
  >> pop_assum drule
  >> strip_tac
  >> qabbrev_tac `b'=a'`
  >> pop_assum kall_tac
  >> `a MOD m + b' MOD m = b MOD m + b' MOD m` by gvs[]
  >> qpat_x_assum `_ MOD _ = _ MOD _` kall_tac
  >> qspecl_then [`m`] assume_tac MOD_PLUS
  >> pop_assum drule >> strip_tac
  >> last_assum $ qspecl_then [`a`, `b'`] assume_tac
  >> first_x_assum $ qspecl_then [`b`, `b'`] assume_tac
  >> `(a + b') MOD m = 0` by metis_tac[]
  >> qpat_x_assum `(_ MOD _ + _ MOD _) = _` kall_tac
  >> rpt $ qpat_x_assum `(_ MOD _ + _ MOD _) MOD _ = _` kall_tac

assume_tac MOD_PLUS
  >> PURE_REWRITE_TAC[MOD_PLUS]

n ``$MOD``

  Either: b >= a, in which case trivial
  Or: a > b. Then we have:
  a + mk = b + nk
  a + mk = b WLOG
  (a + mk) - b = 0
  (a - b) + mk = 0 by LESS_EQ_ADD_SUB
  


  a + mk = b + nk

  a + mk = b WLOG

  (a + mk) - b = 0
  
QED

n ``_ =_ ⇒ (_ - _) = 0n``

Theorem fermats_little_theorem_lemma1:
  ∀ s r p a : num.
    prime p ∧ ¬divides p a ∧ 1 <= s ∧ s <= r ∧ r <= (p - 1) ∧
    (s * a) MOD p = (r * a) MOD p ⇒ s = r
Proof
  rpt strip_tac
  (* Here I want to prove that ((r - s) * a) MOD p = 0. It seems like
     there should be an easy way to do this, but I have to go through
     a whole bunch of steps to do this. How should I do this? *)
  >> `((s * a) MOD p) - ((r * a) MOD p) = 0` by gvs[]
  >> qspecl_then [``] assume_tac MOD_SUB 
  >> sg `((s * a) - (r * a)) MOD p = 0`
  >> sg `((r - s) * a) MOD p = 0`
  >> metis_tac[MOD_SUB, ADD_MOD, ADD_MODULUS_LEFT, ADD_MODULUS_RIGHT]
  >> qpat_x_assum `_ MOD _ = _ MOD _` kall_tac
  >> `divides p (s - r)` by gvs[DIVIDES_MOD0] (* DIVIDES_MOD0 defined above *)
  >> drule DIVIDES_LEQ_OR_ZERO
  >> strip_tac
  >> gvs[]
  >> drule SUB_EQ_0
QED

print_match [] ``_ MOD _``

irule MOD_SUB

Definition FLT_Product_Def:
  FLT_Product a 0 = 1 ∧ FLT_Product a (SUC n) = a * (SUC n) * FLT_Product a n
End

Theorem fermats_little_theorem_lemma2:
  ∀ p a n : num.
    FLT_Product a (p-1) = FACT (p - 1)
Proof
  rpt strip_tac
  >> Induct_on `p`
  >- EVAL_TAC
  >- simp[]
    >> 

Cases_on `p - 1 = 0`
  >- `p = 1 ∨ p = 0` by (simp[] >> metis_tac [NOT_PRIME_1, NOT_PRIME_0])
  >- gvs[]

gvs[NOT_PRIME_1, NOT_PRIME_0]
QED

Theorem fermats_little_theorem:
  ∀a p :num. (prime p ∧ ¬(divides p a) ⇒ (a ** p) MOD p = 1)
Proof
  rpt strip_tac
  sg ‘2 * x = 1 * x + 1 * x’

  full_simp_tac arith_ss []
QED

(* Suppose we have a function which maps pigeons to pigeonholes.              *)
(* Suppose there are more pigeons than pigeonholes.                           *)
(* Then there is at least one pigeonhole which is mapped to by at least two   *)
(* pigeons.                                                                   *)
Theorem pigeonhole_principle:
  ???
Proof
QED

val _ = export_theory();
