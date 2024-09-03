(* Written by Eric Hall, with edits by Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "fermats_little_theorem";

open arithmeticTheory;
open dividesTheory; (* prime *)
open whileTheory; (* LEAST *)
open numLib; (* LEAST_ELIM_TAC *)
open realTheory;
open gcdTheory;
open listTheory;
open sortingTheory;
open pred_setTheory;
open rich_listTheory;
open combinTheory;

Definition length_def[simp]:
  length [] = 0 ∧
  length (h::t) = SUC (length t)
End

Definition sublist_def[simp]:
  (sublist x [] ⇔ x = []) ∧
  (sublist [] y ⇔ T) ∧
  (sublist (xh::xt) (yh::yt) ⇔ 
     (xh = yh ∧ sublist xt yt) ∨
     (sublist (xh::xt) yt)
  )
End

(*Theorem sublist_cons:
  ∀h t l.
    sublist (h::t) l ⇒ sublist t l
Proof
  Induct_on ‘l’ >> gvs[]
  >> rpt gen_tac
  >> strip_tac
      
  >> Cases_on ‘l’ >> gvs[]
  >> 
  >> gvs[sublist_def]
QED

Theorem sublist_not_longer:
  ∀l1 l2. sublist l1 l2 ⇒ length l1 ≤ length l2
Proof
  Induct_on ‘l2’ >> gvs[]
  >> Cases_on ‘l1’ >> gvs[]
  >> rw[sublist_def] >> gvs[]
  >> 

                           
  >> rw[sublist_def]
       \first_x_assum (fn th => assume_tac $ SPEC “(h::t)” th)
                      first_x_assum $ qspec_then ‘h::t’ assume_tac
                      ‘sublist (h::t) l2 ⇒ length (h::t) ≤ length l2’ by
         qpat_x_assum ‘∀l1. sublist l1 l2 ⇒ length l1 ≤ length l2’
                      (fn th => REWRITE_TAC [SPEC “(h::t)” th]) >>
        gvs[]
           ‘length t ≤ length (h::t)’ by simp [] >>
        metis_tac [LESS_EQ_TRANS]
QED*)

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
  1n + 1n = 2n
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
  >> ‘2r = 1r + 1r’ by gvs[REAL_ADD]
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

(* Unnecessary: we already have DIVIDES_MOD_0*)
Theorem MOD0_DIVIDES:
  ∀a b : num. 0 < b ⇒ a MOD b = 0 ⇒ divides b a
Proof
  rpt strip_tac
  >> gvs[MOD_EQ_0_DIVISOR, divides_def]
QED

(* Unnecessary: we already have DIVIDES_MOD_0 *)
Theorem DIVIDES_MOD0:
  ∀a b : num. 0 < b ⇒ divides b a ⇒ a MOD b = 0
Proof
  rpt strip_tac
  >> gvs[compute_divides]
QED

(* Unnecessary: we already have DIVISION, although this form may be more convenient? *)
Theorem DIV_MOD_ADD:
  ∀a b: num. 0 < b ⇒ (a DIV b) * b + a MOD b = a
Proof
  rpt strip_tac
  >> gvs[DIVISION]
QED

(* Unnecessary: we already have DIVISION, although it may be hard to search for this theorem, because it isn't in the form given here? *)        
Theorem MOD_MUL_ADD:
  ∀a m r : num. 0 < m ⇒ a MOD m = r ⇒ ∃b. a = b * m + r
Proof
  rpt strip_tac
  >> qexists `a DIV m`
  >> gvs[DIV_MOD_ADD]
QED

(* Is there an easier way to split an iff than creating my own helper thorem? I tried using irule [EQ_IMP_THM] and looking in the documentation for the relevant tactic but I didn't find anything.*)
(* Yes, use EQ_TAC or IFF_TAC instead *)
Theorem IMP_IMP_IMP_IFF:
  ∀a b : bool. ((a ⇒ b) ∧ (b ⇒ a)) ⇒ (a ⇔ b)
Proof
  gvs[EQ_IMP_THM]
QED

(* converse of MODEQ_INTRO_CONG. I feel like the name should be the opposite  *)
(* of what it is, but I chose the name I chose for consistency  *)
(* I have found in the past that irule doesn't work with an iff but does      *)
(* work with an implication, which is why I wrote this.                       *)
(*                                                                            *)
(* Looking at the documentation, I think maybe I should try using             *)
(* iff{LR,RL} theorem. Maybe this would avoid having to write this new        *)
(* theorem. Upon further inspection, this function is of the form             *)
(* _ => (_ <=> _), and I think this is why it isn't discovering the inner iff.*)
(* My attempts to use iffLR and iffRL didn't work, but maybe there's a way    *)
(*                                                                            *)
(* ----                                                                       *)
(*                                                                            *)
(* It should, in fact, be possible to use iffLR/iffRL                         *)
Theorem MODEQ_ELIM_CONG:
  ∀n e0 e1. 0 < n ⇒ e0 MOD n = e1 MOD n ⇒ MODEQ n e0 e1
Proof
  rpt strip_tac
  >> simp[MODEQ_NONZERO_MODEQUALITY]
QED

(*  *)
Theorem MOD_SIMPLIFY:
  ∀a m : num. 0 < m ⇒ ∃a'. a' < m ∧ (a MOD m) = (a' MOD m)
Proof
  rpt strip_tac
  >> qexists ‘a MOD m’
  >> gvs[]
QED

Theorem MOD_ADDITIVE_INVERSE_EXISTS:
  ∀a m : num. 0 < m ⇒ ∃a'. a' < m ∧ (a + a') MOD m = 0
Proof
  rpt strip_tac
  >> qspecl_then [`a`, `m`] assume_tac DA
  >> gs[]
  >> Cases_on `r = 0`
  >- (qexists `0` >> gs[])
  >> (qexists `m - r` >> gs[])
QED

Theorem MODEQ_ADDITIVE_INVERSE_EXISTS:
  ∀a m : num. 0 < m ⇒ ∃a'. a' < m ∧ MODEQ m (a + a') 0
Proof
  rpt strip_tac
  >> qspecl_then [`a`, `m`] assume_tac MOD_ADDITIVE_INVERSE_EXISTS
  >> gvs[]
  >> qexists `a'`
  >> gvs[]
  >> irule MODEQ_ELIM_CONG
  >> gvs[]
QED

Theorem MUL_GREATER_EQ:
  ∀a a' b : num. a' >= a ⇒ a' * b >= a * b
Proof
  rpt strip_tac
  >> irule $ iffRL GREATER_EQ
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

Theorem MODEQ_SUB_lemma:
  ∀a b m : num. a < m ⇒ b < m ⇒ MODEQ m a b ⇒ MODEQ m (a - b) 0
Proof
  rpt strip_tac
  >> irule MODEQ_ELIM_CONG
  >> simp[]
  >> `a MOD m = b MOD m` by simp[MODEQ_INTRO_CONG]
  >> qpat_x_assum `MODEQ _ _ _` kall_tac
  >> gvs[LESS_MOD]
QED

Theorem MOD_MODEQ_LEFT:
  ∀a b m a' : num. 0 < m ∧ MODEQ m a b ∧ a MOD m = a' MOD m ⇒ MODEQ m a' b
Proof
  rpt strip_tac
  >> drule_all MODEQ_ELIM_CONG >> strip_tac
  >> metis_tac[MODEQ_REFL, MODEQ_SYM, MODEQ_TRANS]
QED

Theorem MOD_MODEQ_RIGHT:
  ∀a b m b' : num. 0 < m ∧ MODEQ m a b ∧ b MOD m = b' MOD m ⇒ MODEQ m a b'
Proof
  rpt strip_tac
  >> metis_tac[MOD_MODEQ_LEFT, MODEQ_REFL, MODEQ_SYM, MODEQ_TRANS]
QED

Theorem MODEQ_SIMPLIFY_LEFT:
  ∀a b m : num. 0 < m ⇒ MODEQ m a b ⇒ ∃a'. a' < m ∧ (a MOD m) = (a' MOD m) ∧ MODEQ m a' b
Proof
  rpt strip_tac
  >> drule_all MODEQ_INTRO_CONG >> strip_tac
  >> drule_all MOD_SIMPLIFY >> strip_tac
  >> pop_assum $ qspec_then `a` assume_tac
  >> qpat_x_assum `_ MOD _ = _ MOD _` kall_tac
  >> gs[]
  >> qexists `a'`
  >> gs[]
  >> `a MOD m = a'` by gs[]
  >> qpat_x_assum `b MOD _ = _` kall_tac
  >> irule MOD_MODEQ_LEFT
  >> gs[]
  >> qexists `a`
  >> gs[]
QED

Theorem MODEQ_SIMPLIFY_RIGHT:
  ∀a b m : num. 0 < m ⇒ MODEQ m a b ⇒ ∃b'. b' < m ∧ (b MOD m) = (b' MOD m) ∧ MODEQ m b' b
Proof
  rpt strip_tac
  >> `MODEQ m b a` by simp[MODEQ_SYM]
  >> qpat_x_assum `MODEQ m a b` kall_tac
  >> drule_all MODEQ_SIMPLIFY_LEFT >> strip_tac
  >> qabbrev_tac `b'=a'` >> pop_assum kall_tac
  >> qexists `b'`
  >> gs[]
  >> irule MOD_MODEQ_LEFT
  >> gs[]
  >> qexists `b`
  >> gs[MODEQ_REFL]
QED

Theorem MODEQ_SUC:
  ∀ a b m : num.
    0 < m ⇒
    MODEQ m (SUC a) (SUC b) ⇒
    MODEQ m a b
Proof
  rpt strip_tac
  >> irule MODEQ_ELIM_CONG
  >> gs[]
  >> drule_all MODEQ_INTRO_CONG >> strip_tac
  >> metis_tac[SUC_MOD]
QED

Theorem MODEQ_ADD_LCANCEL:
  ∀ a b c m : num.
    0 < m ⇒
    (MODEQ m (c + a) (c + b) ⇔ MODEQ m a b)
Proof
  rpt strip_tac
  >> irule IMP_IMP_IMP_IFF
  >> conj_tac
  >- (Induct_on `c`
      >- gs[]
      >> strip_tac
      >> drule MODEQ_SUC >> strip_tac
      >> `∀n. SUC c + n = SUC (c + n)` by gvs[]
           >> metis_tac[])
  >> rpt strip_tac
  >> gvs[MODEQ_THM, ADD_MOD]
QED

(*
  Proof sketch of following theorem:
  (b + b') MOD m = (b - b) MOD m
  Can add same amount to both sides:
  (a + (b + b')) MOD m = (a + (b - b)) MOD m
  ((a + b) + b') MOD m = ((a + b) - b) MOD m
  (b + (a + b')) MOD m = ((b + a) - b) MOD m
  (b + (a + b')) MOD m = (b + (a - b)) MOD m (since a > b)
  Can remove the same amount from both sides: 
*)
Theorem MODEQ_SUB_ADDITIVE_INVERSE:
  ∀a b b' m : num.
    0 < m ⇒
    a > b ⇒
    b' < m ⇒
    MODEQ m (b + b') 0 ⇒
    MODEQ m (a - b) (a + b')
Proof
  rpt strip_tac
  >> `(b + (a - b)) MOD m = (b + (a + b')) MOD m` by gs[]
  >> qspecl_then [`a - b`, `a + b'`, `b`, `m`] assume_tac (iffLR MODEQ_ADD_LCANCEL)
  >> pop_assum $ drule >> strip_tac
  >> drule_all MODEQ_ELIM_CONG >> strip_tac
  >> metis_tac[]
QED

Theorem MODEQ_UNSIMPLIFY:
  ∀a b a' b' m : num. 0 < m ⇒ a MOD m = a' MOD m ⇒ b MOD m = b' MOD m ⇒ MODEQ m a' b' ⇒ MODEQ m a b
Proof
  rpt strip_tac
  >> irule MODEQ_ELIM_CONG
  >> gvs[]
QED

Theorem MODEQ_SUB:
  ∀a b m : num. 0 < m ⇒ MODEQ m a b ⇒ MODEQ m (a - b) 0
Proof
  rpt strip_tac
  >> qspecl_then [`b`, `m`] assume_tac MODEQ_ADDITIVE_INVERSE_EXISTS
  >> gs[]
  >> qabbrev_tac `bInv = a'` >> pop_assum kall_tac
  >> Cases_on `a > b`
  >- (`MODEQ m (a + bInv) (b + bInv)` by (irule MODEQ_PLUS_CONG >> gvs[MODEQ_REFL])
      >> `MODEQ m (a + bInv) 0` by metis_tac[MODEQ_TRANS, MODEQ_SYM, MODEQ_REFL, MODEQ_SUB_ADDITIVE_INVERSE, ADD_COMM]
      >> qspecl_then [`a`, `b`, `bInv`, `m`] assume_tac MODEQ_SUB_ADDITIVE_INVERSE
      >> gvs[]
      >> metis_tac[MODEQ_TRANS, MODEQ_SYM, MODEQ_REFL, MODEQ_SUB_ADDITIVE_INVERSE, ADD_COMM])
  >> `a - b = 0` by gvs[]
  >> metis_tac[MODEQ_REFL]
QED

Theorem MODEQ_0_DIVIDES:
  ∀ a m : num.
    0 < m ⇒
    MODEQ m a 0 ⇒
    divides m a
Proof
  rpt strip_tac
  >> drule_all MODEQ_INTRO_CONG >> pop_assum kall_tac >> strip_tac
  >> gvs[]
  >> irule MOD0_DIVIDES
  >> gvs[]
QED

Theorem DIVIDES_MODEQ_0:
  ∀ a m : num.
    0 < m ⇒
    divides m a ⇒
    MODEQ m a 0
Proof
  rpt strip_tac
  >> qspecl_then [`m`, `a`] assume_tac divides_def
  >> gvs[]
  >> irule MODEQ_ELIM_CONG
  >> gvs[]
QED

Theorem fermats_little_theorem_lemma1_helper:
  ∀ s r p a : num.
    prime p ∧ ¬divides p a ∧
    s < r ∧ r <= (p - 1) ∧
    MODEQ p (s * a) (r * a) ⇒ s = r
Proof
  rpt strip_tac
  >> qspecl_then [`r*a`, `s*a`, `p`] assume_tac MODEQ_SUB
  >> gvs[MODEQ_SYM]
  >> qpat_x_assum `MODEQ p (a * r) _` kall_tac
  >> `MODEQ p (a * r - a * s) 0` by gvs[MODEQ_SYM]
  >> qpat_x_assum `MODEQ p 0 _` kall_tac
  >> `0 < p` by gvs[]
  >> drule_all MODEQ_0_DIVIDES >> pop_assum kall_tac >> pop_assum kall_tac >> strip_tac
  >> `divides p (a * (r - s))` by gvs[LEFT_SUB_DISTRIB]
  >> drule_all P_EUCLIDES >> pop_assum kall_tac >> pop_assum kall_tac >> strip_tac
  >> `0 < p` by gvs[] >> drule_all DIVIDES_MODEQ_0
  >> pop_assum kall_tac >> pop_assum kall_tac >> strip_tac
  >> `0 < p` by gvs[] >> drule_all MODEQ_INTRO_CONG
  >> pop_assum kall_tac >> pop_assum kall_tac >> strip_tac
  >> `r - s < p` by gvs[] >> drule LESS_MOD
  >> pop_assum kall_tac >> strip_tac
  >> `r - s = 0` by gvs[]
  >> gvs[]
QED

Theorem fermats_little_theorem_lemma1:
  ∀ s r p a : num.
    prime p ∧ ¬divides p a ∧
    s <= (p - 1) ∧
    r <= (p - 1) ∧
    MODEQ p (s * a) (r * a) ⇒
    s = r
Proof
  rpt strip_tac
  >> Cases_on `s < r`
  >- (qspecl_then [`s`, `r`, `p`, `a`] assume_tac fermats_little_theorem_lemma1_helper
      >> gvs[])
  >> Cases_on `s > r`
  >- (qspecl_then [`r`, `s`, `p`, `a`] assume_tac fermats_little_theorem_lemma1_helper
      >> gvs[MODEQ_SYM])
  >> gvs[]
QED

Theorem MODEQ_PRIME_NOT_DIVIDES:
  ∀s p a : num.
    prime p ∧ ¬(divides p a) ∧
    MODEQ p (s * a) 0 ⇒
    MODEQ p s 0
Proof
  rpt strip_tac
  >> `¬(p = 0)` by metis_tac[NOT_PRIME_0]
  >> `0 < p` by gvs[]
  >> drule_all MODEQ_0_DIVIDES >> strip_tac
  >> drule_all P_EUCLIDES >> strip_tac
  >> gvs[DIVIDES_MODEQ_0]
QED

Theorem FOLDL_MUL_FROM_HEAD_TO_FRONT:
  ∀n i : num. ∀l : num list.
                FOLDL ($*) i (n::l) = n * FOLDL ($*) i l
Proof
  `∀l : num list. ∀n i : num. FOLDL ($*) i (n::l) = n * FOLDL ($*) i l` suffices_by
                              (rpt strip_tac
                               >> pop_assum $ qspecl_then [`l`, `n`, `i`] assume_tac
                               >> gvs[])
    >> strip_tac
    >> Induct_on `l` >> rpt strip_tac >> gvs[]
QED

(* ---------------------------------------------------------------------------*)
(* Initially I was using FOLDL, but as suggested by Michael Norrish, FOLDR    *)
(* is often  more convenient for proofs because                               *)
(* FOLDR ($* ) i (l::ls) = l * FOLDR ($* ) i ls, whereas                      *)
(* FOLDL ($* ) i (l::ls) = FOLDL ($* ) (l*i) ls,                              *)
(* and so in the case of FOLDL, calculation is performed inside an argument   *)
(* to the FOLDL function, where it is trapped, whereas in the case of         *)
(* FOLDR, calculation is done outside the FOLDR function, which is often      *)
(* more convenient                                                            *)
(* ---------------------------------------------------------------------------*)
Theorem FOLDL_MUL_TO_FRONT:
  ∀l1 l2 : num list. ∀n : num.
                       FOLDL ($*) 1 (l1 ⧺ n::l2) = n * FOLDL ($*) 1 (l1 ⧺ l2)
Proof
  rpt strip_tac
  >> Induct_on `l1`
  >- gvs[FOLDL_MUL_FROM_HEAD_TO_FRONT]
  >> rpt strip_tac
  >> simp[FOLDL_MUL_FROM_HEAD_TO_FRONT]
QED

Theorem FOLDL_FOLDR_MUL:
  ∀l1 : num list. ∀i : num.
                    FOLDL ($*) i l1 = FOLDR ($*) i l1
Proof
  strip_tac
  >> Induct_on `l1`
  >- gvs[]
  >> rpt strip_tac
  >> gvs[FOLDL_MUL_FROM_HEAD_TO_FRONT]
QED

Theorem PERM_FOLDR_MUL:
  ∀l1 l2 : num list. PERM l1 l2 ⇒
                     FOLDR $* 1 l1 = FOLDR $* 1 l2
Proof
  Induct_on ‘PERM’ >> rpt strip_tac >> simp[]
QED 

(* PERM_TO_APPEND_SIMPS *)

Theorem FILTER_IDENTITY_IMPLIES_INVERSE_FILTER_EMPTY:
  ∀l1 : α list.
    ∀ f : α -> bool.
      FILTER f l1 = l1 ⇒ FILTER (λx. ¬(f x)) l1 = []
Proof
  rpt strip_tac
  >> Induct_on `l1`
  >- gvs[FILTER]
  >> rpt strip_tac
  >> gvs[FILTER]
  >> Cases_on `f h` >> gvs[FILTER, LENGTH_FILTER_LESS]
  >> `LENGTH (FILTER f (h::l1)) < LENGTH (h::l1)` by gvs[LENGTH_FILTER_LESS]
  >> gvs[]
QED

Theorem EVERY_WEAKEN:
  ∀P Q : α -> bool.
    ∀ls : α list.
      (∀a : α. P a ⇒ Q a) ⇒
      EVERY P ls ⇒
      EVERY Q ls
Proof
  rpt strip_tac
  >> Induct_on `ls` >> gvs[]
QED  

Theorem FILTER_COUNT_LIST:
  ∀x l : num.
    FILTER ($= x) (COUNT_LIST l) = if x < l then [x] else []
Proof
  rpt strip_tac
  >> Induct_on `l`
  >- gvs[COUNT_LIST_def]
  >> Cases_on `x < SUC l` >> gvs[COUNT_LIST_SNOC, FILTER_SNOC]
  >> Cases_on `x = l` >> gvs[]
QED

Theorem FINITE_SURJ_BIJ_EXISTS:
  ∀s : α -> bool.
    ∀t : β -> bool.
      FINITE s ⇒
      CARD s = CARD t ⇒
      (∃ f : α -> β. SURJ f s t) ⇒
      ∃ g : α -> β.
        BIJ g s t
Proof
  rpt strip_tac
  >> drule FINITE_SURJ_BIJ >> strip_tac
  >> pop_assum $ qspecl_then [`t`, `f`] assume_tac
  >> gvs[]
  >> qexists `f`
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* If two finite sets have the same cardinality, than if there is an          *)
(* injection between them, there must be a bijection between them.            *)
(*                                                                            *)
(* Proof sketch:                                                              *)
(* By BIJ_SYM, it is sufficient to show the existence of a bijection in the   *)
(*   opposite direction.                                                      *)
(* By FINITE_SURJ_BIJ, it is sufficient to show that there is a surjection    *)
(*   in the opposite direction                                                *)
(* By inj_surj, if there is an injection in one direction then there is a     *)
(*   surjection in the opposite direction                                     *)
(* QED.                                                                       *)
(* -------------------------------------------------------------------------- *)
Theorem FINITE_INJ_BIJ_EXISTS:
  ∀f : α -> β.
    ∀s : α -> bool.
      ∀t : β -> bool.
        FINITE s ⇒
        FINITE t ⇒
        CARD s = CARD t ⇒
        INJ f s t ⇒
        (∃g : α -> β. BIJ g s t)
Proof
  rpt strip_tac
  >> qspecl_then [`s`, `t`] irule (iffRL BIJ_SYM)
  >> irule FINITE_SURJ_BIJ_EXISTS
  >> gvs[]
  >> drule inj_surj
  >> strip_tac
  >- (qexists `arb` >> gvs[SURJ_EMPTY])
  >> qexists `f'` >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Unfortunately, FINITE_INJ_BIJ_EXISTS turned out not to be good enough      *)
(* because we needed that the initial injective function was bijective, not   *)
(* just that there existed a bijective function. Thus, we use a different     *)
(* method of proof that allows us to prove that the initial injective         *)
(* function is bijective, not just that there exists a bijection.             *)
(* -------------------------------------------------------------------------- *)
(* Proof sketch:                                                              *)
(* By INJ_IMAGE_BIJ, f is bijective on its image.                             *)
(* Its image has CARD s = CARD t, and is a finite subset of t, therefore it   *)
(* equals t. QED.                                                             *)
(* -------------------------------------------------------------------------- *)

Theorem FINITE_INJ_BIJ:
  ∀f : α -> β.
    ∀s : α -> bool.
      ∀t : β -> bool.
        FINITE s ⇒
        FINITE t ⇒
        CARD s = CARD t ⇒
        INJ f s t ⇒
        BIJ f s t
Proof
  rpt strip_tac
  >> sg `BIJ f s (IMAGE f s)`
  >- (qspecl_then [`s`, `f`] assume_tac INJ_IMAGE_BIJ
      >> pop_assum irule
      >> qexists `t`
      >> gvs[])
  >> sg `(IMAGE f s) ⊆ t`
  >- (drule $ iffLR INJ_DEF >> strip_tac
      >> pop_assum kall_tac
      >> irule $ iffRL SUBSET_DEF
      >> rpt strip_tac
      >> gvs[IMAGE_DEF])
  >> qspecl_then [`(IMAGE f s)`] assume_tac SUBSET_EQ_CARD
  >> `FINITE (IMAGE f s)` by gvs[IMAGE_FINITE]
  >> gvs[]
  >> pop_assum $ qspec_then `t` assume_tac
  >> gvs[]
  >> sg `IMAGE f s = t`
  >- (pop_assum irule
      >> drule_all INJ_CARD_IMAGE_EQ >> strip_tac
      >> gvs[])
  >> gvs[]
QED

Theorem MAP_EL_COUNT_LIST:
  ∀ls : α list.
    MAP (λn. EL n ls) (COUNT_LIST (LENGTH ls)) = ls
Proof
  gvs[GENLIST_ID, MAP_COUNT_LIST]
QED

Theorem LESS_LENGTH_PERM_COUNT_LIST:
  ∀l1 : num list.
    EVERY (λn. n < (LENGTH l1)) l1 ⇒
    ALL_DISTINCT l1 ⇒
    PERM l1 (COUNT_LIST (LENGTH l1))
Proof
  rpt strip_tac
  >> sg `INJ (λn. EL n l1) (count (LENGTH l1)) (count (LENGTH l1))`
  >- (gvs[INJ_DEF]
      >- (conj_tac
          >- (rpt strip_tac
              >> drule $ iffLR EVERY_EL >> rpt strip_tac
              >> pop_assum $ qspec_then `n` assume_tac
              >> gvs[])
          >- (rpt strip_tac
              >> qspecl_then [`l1`] assume_tac EL_ALL_DISTINCT_EL_EQ
              >> gvs[])))
  >> `FINITE (count (LENGTH l1))` by gvs[FINITE_COUNT]
  >> qspecl_then [`λn. EL n l1`, `count (LENGTH l1)`, `count (LENGTH l1)`] assume_tac FINITE_INJ_BIJ
  >> gvs[]
  >> qspecl_then [`λn. EL n l1`, `count (LENGTH l1)`, `count (LENGTH l1)`] assume_tac PERM_BIJ_SET_TO_LIST
  >> gvs[]
  >> `PERM (SET_TO_LIST (count (LENGTH l1))) (COUNT_LIST (LENGTH l1))` by gvs[PERM_SET_TO_LIST_count_COUNT_LIST]
  >> `PERM (MAP (λn. EL n l1) (SET_TO_LIST (count (LENGTH l1)))) (MAP (λn. EL n l1) (COUNT_LIST (LENGTH l1)))` by gvs[PERM_MAP]
  >>metis_tac[PERM_REFL, PERM_SYM, PERM_TRANS, MAP_EL_COUNT_LIST]
QED

(* --- Old proof attempt for LESS_LENTH_PERM_COUNT_LIST
  >> sg `∃f : num -> num. INJ f (count (LENGTH l1)) (set l1)` 
  >- (qexists `λn. EL n l1`
      >> irule $ iffRL INJ_DEF
      >> rpt strip_tac
      >- gvs[ALL_DISTINCT_EL_IMP]
      >> gvs[MEM_EL]
      >> qexists `x`
      >> gvs[])
  >> `FINITE (count (LENGTH l1))` by gvs[FINITE_COUNT]
  >> `FINITE (set l1)` by gvs[FINITE_LIST_TO_SET]
  >> `CARD (set l1) = CARD(count (LENGTH l1))` by gvs[CARD_COUNT, ALL_DISTINCT_CARD_LIST_TO_SET]
  >> qspecl_then [`f`, `count (LENGTH l1)`, `set l1`] assume_tac FINITE_INJ_BIJ
  >> gvs[]
  >> qspecl_then [`f`, `count (LENGTH l1)`, `count (LENGTH l1)`] assume_tac PERM_BIJ_SET_TO_LIST
  >> gvs[]*)

(* Not sure what the best way to handle the contrapositive is, but this works.*)
(* Identical to MONO_NOT and NOT_IMPLIES *)
Theorem contrapositive:
  ∀a b : bool.
    (a ⇒ b) ⇒ (¬b ⇒ ¬a)
Proof
  gvs[]
QED

(* MODEQ_THM doesn't use a forall which makes qspecl_then not work on it.
   This version has a forall. *)
Theorem MODEQ_THM_FORALL:
  ∀n m1 m2 : num.
    MODEQ n m1 m2 ⇔ (n = 0 ∧ m1 = m2) ∨ (0 < n ∧ m1 MOD n = m2 MOD n)
Proof
  rpt strip_tac
  >> gvs[MODEQ_THM]
QED

Theorem fermats_little_theorem_lemma2:
  ∀ p a : num.
    prime p ⇒
    ¬(divides p a) ⇒
    PERM (GENLIST (λn. (a * (SUC n)) MOD p) (p - 1)) (GENLIST SUC (p - 1))
Proof
  rpt strip_tac
  >> `GENLIST SUC (p - 1) = MAP SUC (COUNT_LIST (p - 1))` by gvs[MAP_COUNT_LIST]
  >> sg `EVERY (λn. n < p) (GENLIST (λn. (a * (SUC n)) MOD p) (p - 1))`
  >- (irule $ iffRL EVERY_EL >> rpt strip_tac >> gvs[])
  >> sg `ALL_DISTINCT (GENLIST (λn. (a * (SUC n)) MOD p) (p - 1))`
  >- (irule $ iffRL EL_ALL_DISTINCT_EL_EQ
      >> rpt strip_tac
      >> gvs[]
      >> irule IMP_ANTISYM_AX
      >> conj_tac >> gvs[]
      >> qspecl_then [`SUC n1`, `SUC n2`, `p`, `a`] assume_tac fermats_little_theorem_lemma1
      >> gvs[]
      >> strip_tac
      >> first_x_assum irule
      >> gvs[MODEQ_THM])
  >> qmatch_goalsub_abbrev_tac `PERM l1 l2`
  >> `PERM (MAP (λx : num. x - 1) l1) (MAP (λx : num. x - 1) l2)` suffices_by
    (strip_tac
     >>qspecl_then [`λx : num. x + 1`] drule PERM_MAP
     >> pop_assum kall_tac >> strip_tac
     >> gvs[(Ntimes MAP_MAP_o 2)]
     >> qmatch_goalsub_abbrev_tac `PERM l1 l2`
     >> `∀l : num list. ¬(MEM 0 l) ⇒ MAP ((λx : num. x + 1) ∘ (λx. x - 1)) l = l` by (rpt strip_tac >> Induct_on `l` >> gvs[])
          >> sg `¬(MEM 0 l1)`
          >- (qspecl_then [`l1`, `0`] assume_tac (iffLR MEM_EL)
              >> drule contrapositive >> pop_assum kall_tac
              >> strip_tac >> pop_assum irule
              >> rpt strip_tac
              >> unabbrev_all_tac
              >> simp[EL_GENLIST]
              >> rfs[EL_GENLIST]
              >> `MODEQ p (a * SUC n) 0` by gvs[MODEQ_THM]
              >> qspecl_then [`SUC n`, `p`, `a`] assume_tac MODEQ_PRIME_NOT_DIVIDES
              >> gvs[]
              >> drule $ iffLR MODEQ_THM
              >> rpt strip_tac
              >- gvs[NOT_PRIME_0]
              >> `SUC n < p` by gvs[]
              >> gvs[LESS_MOD])
          >> sg `¬(MEM 0 l2)`
          >- (qspecl_then [`l2`, `0`] assume_tac (iffLR MEM_EL)
              >> drule contrapositive >> pop_assum kall_tac
              >> strip_tac >> pop_assum irule
              >> rpt strip_tac
              >> unabbrev_all_tac
              >> `n < (p - 1)` by gvs[LENGTH_COUNT_LIST]
              >> gvs[el_map_count])
          >> metis_tac[])
  >> `MAP (λx : num. x - 1) l2 = COUNT_LIST (p - 1)` by gvs[MAP_MAP_o, o_DEF]
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac `PERM l3 _`
  >> `PERM l3 (COUNT_LIST (LENGTH l3))` suffices_by
    (`LENGTH l3 = p - 1` suffices_by metis_tac[]
     >> unabbrev_all_tac
     >> gvs[LENGTH_MAP, LENGTH_GENLIST])
  >> irule LESS_LENGTH_PERM_COUNT_LIST
  >> sg `EVERY (λn. n > 0) l1`
  >- (irule $ iffRL EVERY_EL
      >> rpt strip_tac
      >> simp[Abbr `l1`]
      >> gvs[EL_GENLIST]
      >> `¬(MODEQ p (a * SUC n) 0)` suffices_by
        (strip_tac
         >> qspecl_then [`p`, `(a * SUC n)`, `0`] assume_tac (iffRL MODEQ_THM_FORALL)
         >> drule contrapositive >> pop_assum kall_tac >> strip_tac
         >> gvs[])
      >> CCONTR_TAC
      >> gvs[]
      >> `MODEQ p (SUC n) 0` by metis_tac[MODEQ_PRIME_NOT_DIVIDES, MULT_COMM]
      >> `SUC n < p` by gvs[]
      >> gvs[MODEQ_THM, LESS_MOD])
  >> conj_tac
  >- (simp[Abbr `l3`]
      >> irule ALL_DISTINCT_MAP_INJ
      >> gvs[]
      >> rpt strip_tac
      >> `∀n : num. MEM n l1 ⇒ n > 0` by gvs[EVERY_MEM]
           >> `x > 0 ∧ y > 0` by gvs[]
           >> gvs[CANCEL_SUB])
  >> gvs[Abbr `l3`]
  >> gvs[EVERY_MAP]
  >> sg `LENGTH l1 = (p - 1)`
  >- (unabbrev_all_tac
      >> gvs[LENGTH_GENLIST])
  >> gvs[]
  >> `¬(p = 0) ∧ ¬(p = 1)` by metis_tac[NOT_PRIME_0, NOT_PRIME_1]
  >> gvs[]
QED

Theorem FOLDR_MUL_GENLIST_FACT:
  ∀n : num.
    FOLDR ($* ) 1n (GENLIST SUC n) = FACT n
Proof
  rpt strip_tac
  >> Induct_on `n` >> gvs[]
  >- EVAL_TAC
  >> qmatch_goalsub_abbrev_tac `FOLDR _ _ l1`
  >> `FOLDL $* 1 l1 = FACT (SUC n)` suffices_by gvs[FOLDL_FOLDR_MUL]
  >> unabbrev_all_tac
  >> gvs[GENLIST]
  >> gvs[FOLDL_SNOC]
  >> gvs[FOLDL_FOLDR_MUL]
  >> gvs[FACT, MULT_COMM]
QED

Theorem FOLDR_MUL_GENLIST_POW:
  ∀a len : num.
    FOLDR ($* ) 1n (GENLIST (λn. a) len) = a ** len
Proof
  rpt strip_tac
  >> Induct_on `len` >> gvs[EXP]
  >> gvs[GENLIST]
  >> qmatch_goalsub_abbrev_tac `FOLDR $* 1 ls = RHS`
  >> `FOLDL $* 1n ls = RHS` suffices_by gvs[FOLDL_FOLDR_MUL]
  >> unabbrev_all_tac
  >> gvs[FOLDL_SNOC]
  >> Cases_on `a = 0` >> gvs[FOLDL_FOLDR_MUL]
QED

Theorem MODEQ_MUL:
  ∀p a a' b b' : num.
    MODEQ p a a' ⇒
    MODEQ p b b' ⇒
    MODEQ p (a * b) (a' * b')
Proof
  rpt strip_tac
  >> Cases_on `p = 0`
  >- gvs[MODEQ_DEF]
  >> gvs[MODEQ_THM]
  >> `0 < p` by gvs[]
  >> drule MOD_TIMES2 >> strip_tac
  >> pop_assum $ qspecl_then [`a`, `b`] assume_tac
  >> gvs[]
QED

(* If we take the modulo both before and after multiplying a list of numbers
   together, this is equivalent to just taking the modulo after multiplying
   the numbers together *)
Theorem mod_list_product:
  ∀p : num.
    ∀l1 : num list.
      p > 0 ⇒
      MODEQ p (FOLDR $* 1 (MAP (λn : num. n MOD p) l1)) (FOLDR $* 1 l1) 
Proof
  rpt strip_tac
  >> gvs[MODEQ_THM]
  >> Induct_on `l1` >> rpt strip_tac >> gvs[]
  >> qmatch_goalsub_abbrev_tac `(h * a1) MOD p = (h * a2) MOD p`
  >> `((h MOD p) * (a1 MOD p)) MOD p = ((h MOD p) * (a2 MOD p)) MOD p` suffices_by gvs[MOD_TIMES2]
  >> gvs[]
QED

Theorem split_list_product_of_products:
  ∀f g : α -> num.
    ∀ l1 : α list.
      FOLDR $* 1n (MAP (λa : α. f a *  g a) l1) = (FOLDR $* 1n (MAP (λa : α. f a) l1)) * (FOLDR $* 1n (MAP (λa : α. g a) l1))
Proof
  rpt strip_tac
  >> Induct_on `l1` >> rpt strip_tac >> gvs[]
QED

Theorem MODEQ_MUL_0_CANCEL:
  ∀a b p : num.
  prime p ∧ ¬(divides p b) ∧ MODEQ p (a * b) 0 ⇒
  MODEQ p a 0
Proof
  rpt strip_tac
  >> `¬(p = 0)` by metis_tac[NOT_PRIME_0]
  >> `0 < p` by gvs[]
  >> gvs[]
  >> gvs[MODEQ_THM]
  >> irule DIVIDES_MOD0
  >> gvs[]
  >> drule_all MOD0_DIVIDES >> strip_tac
  >> metis_tac[P_EUCLIDES]
QED

Theorem MOD_MUL_0_CANCEL:
  ∀a b p : num.
  prime p ∧ ¬(divides p b) ∧ (a * b) MOD p = 0 ⇒
  a MOD p = 0
Proof
  rpt strip_tac
  >> `¬(p = 0)` by metis_tac[NOT_PRIME_0]
  >> `0 < p` by gvs[]
  >> gvs[]
  >> `MODEQ p (a * b) 0` by metis_tac[LESS_MOD, MODEQ_THM]
  >> drule_all MODEQ_MUL_0_CANCEL >> strip_tac
  >>  gvs[MODEQ_THM]
QED

Theorem MODEQ_ADD_RCANCEL:
  ∀a b c m : num.
  0 < m ⇒
  (MODEQ m (a + c) (b + c) ⇔ MODEQ m a b)
Proof
  rpt strip_tac
  >> metis_tac[iffLR MODEQ_ADD_LCANCEL, iffRL MODEQ_ADD_LCANCEL, ADD_SYM]
QED

Theorem MODEQ_SUB2:
  ∀a b m.
  0 < m ⇒
  b < a ⇒
  MODEQ m (a - b) 0 ⇒
  MODEQ m a b
Proof
  rpt strip_tac
  >> `MODEQ m ((a - b) + b) (0 + b)` by gvs[MODEQ_ADD_RCANCEL]
  >> gvs[]
QED

Theorem MODEQ_MUL_CANCEL:
  ∀a b c p : num.
  prime p ⇒
  ¬(divides p c) ⇒
  MODEQ p (a * c) (b * c) ⇒
  MODEQ p a b
Proof
  rpt strip_tac
  >> `¬(p = 0)` by metis_tac[NOT_PRIME_0]
  >> `0 < p` by gvs[]
  >> gvs[]
  >> sg `∀n m : num. n > m ⇒ MODEQ p (n * c) (m * c) ⇒ MODEQ p n m`
  >- (rpt strip_tac
      >> `MODEQ p ((n * c) - (m * c)) 0` by gvs[MODEQ_SUB]
      >> gvs[MODEQ_THM]
      >> `((n - m) * c) MOD p = 0` by gvs[RIGHT_SUB_DISTRIB]
      >> `(n - m) MOD p = 0` by metis_tac[MOD_MUL_0_CANCEL]
      >> `MODEQ p (n - m) 0` by gvs[MODEQ_THM]
      >> `m < n` by gvs[]
      >> drule_all MODEQ_SUB2
      >> gvs[MODEQ_THM])
  >> Cases_on `a > b` >> gvs[]
  >> Cases_on `b > a` >> gvs[MULT_COMM, MODEQ_SYM]
  >> `a = b` by gvs[]
  >> gvs[MODEQ_REFL]
QED

Theorem PRIME_LESS_NOT_DIVIDES:
  ∀p n : num.
  prime p ⇒
  n < p ⇒
  ¬(n = 1) ⇒
  ¬(divides n p)
Proof
  rpt strip_tac
  >> qspecl_then [`n`] assume_tac PRIME_FACTOR
  >> gvs[]
  >> `divides p' p` by metis_tac[DIVIDES_TRANS]
  >> Cases_on `n = 0`
  >- gvs[ZERO_DIVIDES] 
  >> `p' <= n` by gvs[DIVIDES_LE, ONE_LT_PRIME]
  >> sg `p' < p`
  >- gvs[]
  >> qspecl_then [`p'`, `p`] assume_tac prime_divides_only_self
  >> gvs[]
QED

Theorem PRIME_LESS_FACT_NOT_DIVIDES:
  ∀p n : num.
  prime p ⇒
  n < p ⇒
  ¬(n = 1) ⇒
  ¬(divides p (FACT n))
Proof
  rpt strip_tac
  >> Induct_on `n` >> gvs[FACT] >> rpt strip_tac >> gvs[ONE_LT_PRIME]
  >> qspecl_then [`p`, `FACT n`, `SUC n`] assume_tac P_EUCLIDES
  >> gvs[]
  >- (`FACT 1 = 1` by EVAL_TAC
      >> gvs[])
  >> Cases_on `n = 1` >> gvs[]
  >- (`p = 2` by gvs[PRIME_2, prime_divides_only_self] >> gvs[])
  >> gvs[NOT_LT_DIVIDES]
QED

Theorem fermats_little_theorem:
  ∀a p :num. (prime p ∧ ¬(divides p a) ⇒ (a ** (p - 1)) MOD p = 1)
Proof
  rpt strip_tac
  >> drule_all fermats_little_theorem_lemma2
  >> qmatch_goalsub_abbrev_tac `PERM l1 l2 ⇒ _`
  >> strip_tac
  >> `FOLDR ($* ) 1 l1 = FOLDR ($* ) 1 l2` by gvs[PERM_FOLDR_MUL]
  >> qpat_x_assum `PERM _ _` kall_tac
  >> qmatch_asmsub_abbrev_tac `m1 = m2`
  >> `m2 = FACT (p - 1)` by gvs[Abbr `m2`, Abbr `l2`, FOLDR_MUL_GENLIST_FACT]
  >> sg `MODEQ p m1 (a ** (p - 1) * FACT (p - 1))`
  >- (qpat_x_assum `m1 = m2` kall_tac
      >> qpat_x_assum `m2 = FACT _` kall_tac
      >> simp[Abbr `l2`, Abbr `m2`]
      >> `(λn : num. (a * SUC n) MOD p) = (λn : num. n MOD p) ∘ (λn : num. (a * SUC n))` by gvs[o_DEF]
      >> gvs[]
      >> pop_assum kall_tac
      >> qmatch_asmsub_abbrev_tac `GENLIST (f2 ∘ f1) _`
      >> `l1 = MAP f2 (GENLIST f1 (p - 1))` by gvs[MAP_GENLIST]
      >> qpat_x_assum `Abbrev (l1 = (GENLIST _ _))` kall_tac
      >> `MODEQ p m1 (FOLDR $* 1 (GENLIST f1 (p - 1)))` by
         (`¬(p = 0)` by metis_tac[NOT_PRIME_0]
          >> gvs[Abbr `m1`, Abbr `f2`]
          >> gvs[mod_list_product])
      >> qpat_x_assum `Abbrev (m1 = _)` kall_tac
      >> `MODEQ p m1 (FOLDR $* 1 (MAP f1 (COUNT_LIST (p - 1))))` by gvs[MAP_COUNT_LIST]
      >> qpat_x_assum `MODEQ _ _ (FOLDR _ _ (GENLIST _ _))` kall_tac
      >> qmatch_asmsub_abbrev_tac `MAP f1 cl`
      >> `FOLDR $* 1n (MAP f1 cl) = (FOLDR $* 1n (MAP (λn : num. a) cl)) * (FOLDR $* 1n (MAP (λn : num. SUC n) cl))` by gvs[Abbr `f1`, split_list_product_of_products]
      >> gvs[]
      >> pop_assum kall_tac
      >> qmatch_asmsub_abbrev_tac `MODEQ p m1 (fold1 * fold2)`
      >> sg `MODEQ p fold1 (a ** (p - 1))`
      >- (qpat_x_assum `MODEQ p m1 _` kall_tac
          >> unabbrev_all_tac
          >> gvs[FOLDR_MUL_GENLIST_POW, MAP_COUNT_LIST, MODEQ_REFL])
      >> sg `MODEQ p fold2 (FACT (p - 1))`
      >- (qpat_x_assum `MODEQ p m1 _` kall_tac
          >> unabbrev_all_tac
          >> `(λn : num. SUC n) = SUC` by (EVAL_TAC >> gvs[])
          >> gvs[FOLDR_MUL_GENLIST_FACT, MAP_COUNT_LIST, MODEQ_REFL])
      >> qmatch_goalsub_abbrev_tac `MODEQ p m1 (n1 * n2)`
      >> qspecl_then [`p`, `n2`, `fold1`, `n1`, `fold2`] assume_tac MODEQ_MUL
      >> gvs[]
      >> metis_tac[MODEQ_MUL, MODEQ_SYM, MULT_COMM, MODEQ_TRANS]
      )
  >> `MODEQ p (1 * FACT (p - 1)) (a ** (p - 1) * FACT(p - 1))` by gvs[]
  >> sg `MODEQ p 1 (a ** (p - 1))`
  >- (qspecl_then [`1`, `a ** (p - 1)`, `FACT (p - 1)`, `p`] assume_tac MODEQ_MUL_CANCEL
      >> gvs[]
      >> `¬(divides p (FACT (p - 1)))` suffices_by gvs[]
      >> pop_assum kall_tac >> pop_assum kall_tac >> pop_assum kall_tac >> pop_assum kall_tac >> pop_assum kall_tac >> pop_assum kall_tac >> pop_assum kall_tac
      >>`p - 1 < p` by (Cases_on `p = 0` >> gvs[ONE_LT_PRIME])
      >>Cases_on `p = 2` >> gvs[]
      >- (`FACT 1 = 1` by EVAL_TAC >> gvs[DIVIDES_ONE])
      >> `p - 1 ≠ 1` by gvs[]
      >> gvs[PRIME_LESS_FACT_NOT_DIVIDES]
      )
  >> gvs[MODEQ_THM, EQ_SYM, LESS_MOD, ONE_LT_PRIME]
QED

val _ = export_theory();
