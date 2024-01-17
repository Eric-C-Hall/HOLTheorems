(* Written by Eric Hall, with edits by Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "EricHOLTheorems";

open arithmeticTheory;
open dividesTheory; (* prime *)
open whileTheory; (* LEAST *)
open numLib; (* LEAST_ELIM_TAC *)
open realTheory;
open gcdTheory;

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


(* -------------------------------------------------------------------------- *)
(* This proof of Fermat's little theorem is based on the proof given in       *)
(* Discrete Mathematics with Applications by Susanna Epp, fourth edition,     *)
(* page 494 Theorem 8.4.10                                                    *)
(* -------------------------------------------------------------------------- *)

(* No two choices of a, 2a, 3a ... (p - 1)a are congruent modulo op*)


print_match [] “1 MOD n”

Theorem fermats_little_theorem_lemma1:
  ∀ s r p : num.
    prime p ∧ ¬divides p a ∧ 1 <= s ∧ s <= r ∧ r <= (p - 1) ∧
    s * a MOD p = r * a MOD p ⇒ s = r
Proof:
  rpt strip_tac
  >> ‘(s - r) * a MOD p = 0’ by asm_simp_tac arith_ss []
  >> ‘divides p a ∨ gcd p a = 1’ by metis_tac [P_EUCLIDES, PRIME_GCD]
  >> full_simp_tac arith_ss [] (* 2 *) >> simp []
  >- (
  >> sg ‘divides p a’
  >> asm_simp_tac arith_ss [compute_divides]
  >- CCONTR_TAC
  >> sg ‘divides p (s - r)’ CCONTR_TAC

metis_tac [P_EUCLIDES, PRIME_GCD]
  sg ‘(s - r) MOD P = 0’
  sg ‘gcd a p = 1’
  metis_tac [P_EUCLIDES, PRIME_GCD]
QED


Theorem fermats_little_theorem_lemma1:
  ∀a p : num. prime p ⇒ 0 < a ∧ a < p ⇒

Theorem fermats_little_theorem_lemma2:
  ∀p : num. prime p ⇒ (FACT (p - 1)) MOD p = 1
Proof
  rpt strip_tac
  >> Induct_on ‘(p - 1) : num’
  >- (rpt strip_tac >> CCONTR_TAC
    >> ‘p = 0 ∨ p = 1’ by asm_simp_tac arith_ss []
    >- assume_tac NOT_PRIME_0
    >> metis_tac []
    >- assume_tac NOT_PRIME_1

>> metis_tac [])
  >- rpt strip_tac
  >> ‘FACT 0 = 1’ by EVAL_TAC
  >> ‘FACT (p - 1) = 1’ by metis_tac []
  >> metis_tac [ONE_MOD]
  >> sg ‘1 < p’ full_simp_tac arith_ss []
  >>
  >> sg ‘1 MOD p = 1’ by EVAL_TAC
  >> metis_tac

>>
>> asm_simp_tac arith_ss [] EVAL_TAC
  >- rpt strip_tac
  >> full_simp_tac arith_ss []
QED


Theorem fermats_little_theorem:
  ∀a p :num. (prime p ⇒ ¬(divides p a) ⇒ (a ** p) MOD p = a)
Proof
  rpt strip_tac
  sg ‘2 * x = 1 * x + 1 * x’

  full_simp_tac arith_ss []
QED

val _ = export_theory();
