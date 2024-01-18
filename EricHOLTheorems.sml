(* Written by Eric Hall, with edits by Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "EricHOLTheorems";

open arithmeticTheory;
open dividesTheory; (* prime *)
open whileTheory; (* LEAST *)
open numLib; (* LEAST_ELIM_TAC *)
open realTheory;
open gcdTheory;
open pairTheory;

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
(* Thus, we have                                                              *)
(*                                                                            *)
(*                                                                            *)
(* Thus the identity function is an injection from this list to               *)
(*   l2 = [1, 2, 3, ..., p-1]                                                 *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* Since these lists are finite and the same size as each other, this         *)
(*   function is a bijection.  (See Lemma 2)                                  *)
(*                                                                            *)
(* Therefore the product of the elements in l1 is equal to the product of the *)
(* elements in l2 (See Lemma 3)                                               *)
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
(* Defintion:                                                                 *)
(*   is_injection f l1 l2 <=>                                                 *)
(* End                                                                        *)
(*                                                                            *)
(* Definition                                                                 *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* Lemma 2:                                                                   *)
(*                                                                            *)
(* if there is an injection from a finite list to another list of the same    *)
(*   size, then there is a bijection between them                             *)
(*                                                                            *)
(* Proof:                                                                     *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* QED                                                                        *)
(*                                                                            *)
(* Lemma 3:                                                                   *)
(*                                                                            *)
(* if there is a bijection between two lists, then their product is equal     *)
(*                                                                            *)
(* Proof                                                                      *)
(*                                                                            *)
(* Induct on elements of list 1                                               *)
(* Base case: if both lists are empty, trivial                                *)
(* Inductive case: The first element of list 1 is in bijection with some      *)
(* element of list 2.                                                         *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* QED                                                                        *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)


(* No two choices of a, 2a, 3a ... (p - 1)a are congruent modulo op*)

Theorem fermats_little_theorem_lemma1:
  ∀ s r p a : num.
    prime p ∧ ¬divides p a ∧ 1 <= s ∧ s <= r ∧ r <= (p - 1) ∧
    (s * a) MOD p = (r * a) MOD p ⇒ s = r
Proof
  rpt strip_tac >> gvs[compute_divides]
QED


Definition FLT_Product_Def:
  FLT_Product a 0 = 1 ∧ FLT_Product a (SUC n) = a * (SUC n) * FLT_Product a n
End

(* nproduct (1 .. n) (λm. a * m) = nproduct (1 .. n) (λm. m) *)


(*For every factor of FACT (p - 1), this is a factor of  FLT_Product

(* The terms are exactly the same but reordered *
(* For each term in FLT_Product, there is exactly one term in FACT it is equal to*)
(* For each term in FACT, there is exactly one term in FLT_Product it is equal to *)

(*WTP: Prime factors are exactly the same *)
(* *)

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
