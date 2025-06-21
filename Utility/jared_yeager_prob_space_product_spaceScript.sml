(* This code was written by Jared Yeager *)
(* Extremely minor modifications by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "jared_yeager_prob_space_product_space";

open HolKernel Parse boolLib bossLib;
open simpLib;
open monadsyntax;
open markerTheory;
open combinTheory;
open pairTheory;
open arithmeticTheory;
open pred_setTheory;
open listTheory;
open rich_listTheory;
open finite_mapTheory;
open realTheory;
open realLib;
open limTheory;
open transcTheory;
open real_sigmaTheory;
open binary_ieeeTheory;
open extrealTheory;
open sigma_algebraTheory;
open measureTheory;
open borelTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;

Theorem pos_fn_integral_cmul_indicator':
    ∀m s c.  measure_space m ∧ s ∈ measurable_sets m ∧ 0 ≤ c ⇒ ∫⁺ m (λx. c * 𝟙 s x) = c * measure m s
Proof
    rw[] >> Cases_on `c` >> fs[pos_fn_integral_cmul_indicator,pos_fn_integral_cmul_infty]
QED

Theorem m_space_prod_measure_space:
    ∀m0 m1. m_space (m0 × m1) = m_space m0 × m_space m1
Proof
    simp[prod_measure_space_def]
QED

Theorem prod_measure_cross:
    ∀m0 m1 s0 s1. measure_space m0 ∧ measure_space m1 ∧ s0 ∈ measurable_sets m0 ∧ s1 ∈ measurable_sets m1 ⇒
        measure (m0 × m1) (s0 × s1) = measure m0 s0 * measure m1 s1
Proof
    rw[prod_measure_space_def,prod_measure_def,INDICATOR_FN_CROSS] >>
    irule EQ_TRANS >> qexists_tac `∫⁺ m1 (λy. measure m0 s0 * 𝟙 s1 y)` >>
    irule_at Any pos_fn_integral_cmul_indicator' >> simp[MEASURE_POSITIVE] >>
    irule_at Any pos_fn_integral_cong >> simp[] >>
    simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >> qx_gen_tac `y` >> strip_tac >>
    irule_at Any pos_fn_integral_pos >> irule_at Any le_mul >>
    simp[MEASURE_POSITIVE,INDICATOR_FN_POS,le_mul] >>
    `∫⁺ m0 (λx. 𝟙 s1 y * 𝟙 s0 x) = 𝟙 s1 y * measure m0 s0` suffices_by simp[mul_comm] >>
    irule_at Any pos_fn_integral_cmul_indicator' >> simp[INDICATOR_FN_POS]
QED

Theorem prob_space_sigma_finite_measure_space:
    ∀p. prob_space p ⇒ sigma_finite_measure_space p
Proof
    rw[prob_space_def,sigma_finite_measure_space_def,sigma_finite_def] >>
    qexists ‘K (m_space p)’ >> simp[FUNSET,EXTENSION,MEASURE_SPACE_SPACE] >>
    metis_tac[]
QED

Theorem prob_space_product_space:
    ∀p0 p1. prob_space p0 ∧ prob_space p1 ⇒ prob_space (p0 × p1)
Proof
    rw[] >> simp[prob_space_def] >> irule_at Any measure_space_prod_measure >>
    simp[prob_space_sigma_finite_measure_space,m_space_prod_measure_space] >>
    qspecl_then [‘p0’,‘p1’,‘m_space p0’,‘m_space p1’] mp_tac prod_measure_cross >>
    gs[prob_space_def,MEASURE_SPACE_SPACE]
QED

val _ = export_theory();
