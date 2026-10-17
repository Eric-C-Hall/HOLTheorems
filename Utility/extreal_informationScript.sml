(* ========================================================================= *)
(*   Information Theory (KL divergence, mutual information and entropy)      *)
(*                                                                           *)
(*   Ported from examples/diningcryptos/informationScript.sml (by Aaron R.   *)
(*   Coble, 2010), which was based on the legacy, real-valued probability    *)
(*   theory (examples/probability/legacy), to the extreal-based measure and  *)
(*   probability theories in src/probability.                                *)
(*                                                                           *)
(*   This file was written by Claude, with close supervision by Eric Hall.   *)
(*                                                                           *)
(*   Only some parts of this file have been validated by a human, indicated  *)
(*   explicitly where this is the case.                                      *)
(* ========================================================================= *)

Theory extreal_information
Ancestors
  combin arithmetic pred_set pair real real_sigma transc
  sigma_algebra extreal_base extreal measure borel lebesgue
  martingale probability
Libs
  hurdUtils realLib

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)

(* The KL divergence D_{KL}(P||Q) of a pair of discrete distributions
.
   b: the base of the logarithm
   A: the finite alphabet (set of outcomes) over which P and Q are defined
   P: the first mass function (extreal-valued)
   Q: the second mass function (extreal-valued)
.
   Manually validated by Eric Hall: definition matches that provided in
   "Information Theory, Inference and Learning Algorithms" by David J. C.
   MacKay, assuming validity of components such as logr.
.        
   Written by Claude with supervision by Eric Hall *)
Definition KL_divergence_discrete_def:
    KL_divergence_discrete b A (P : α -> extreal) (Q : α -> extreal) =
      if ∃x. x ∈ A ∧ Q x = 0 ∧ P x ≠ 0 then PosInf
      else ∑ (λx. P x * logr b (P x / Q x)) A
End

(* The entropy H(P) of a discrete distribution
.
   b: the base of the logarithm
   A: the finite alphabet (set of outcomes) over which P is defined
   P: the mass function (extreal-valued)
.
   Written by Claude *)
Definition entropy_discrete_def:
    entropy_discrete b A (P : α -> extreal) = ∑ (λx. P x * logr b (1 / P x)) A
End
        
(* Non-discrete version of the KL divergence
   D_b(u||v) = ∫ log_b (du/dv) du (measure-theoretic)
.
   b: the base of the logarithm
   s: the sigma-algebra shared by both measures
   u: the first measure, e.g. ‘distribution p X’
   v: the second measure
.
   ‘RN_deriv u m’ (also written ‘u / m’) is the Radon-Nikodym derivative du/dm.
   Only meaningful when u ≪ v and v is sigma-finite (otherwise du/dv does not
   exist and the value is unspecified, not +∞), and when the integral is not
   +∞ - +∞ (never the case for probability measures).
.
   Has not been validated by a human. KL_divergence_discrete_eq will likely
   help in validation.
.
   Written by Claude *)
Definition KL_divergence_def:
    KL_divergence b s u v =
    ∫ (space s,subsets s,u)
             (λx. logr b (RN_deriv u (space s,subsets s,v) x))
End

(* Non-discrete version of the mutual information
.
  Written by Claude *)
Definition mutual_information_def:
    mutual_information b p s1 s2 X Y =
      let prod_space =
            prod_measure_space (space s1,subsets s1,distribution p X)
                               (space s2,subsets s2,distribution p Y)
      in
        KL_divergence b (m_space prod_space,measurable_sets prod_space)
                        (joint_distribution p X Y)
                        (measure prod_space)
End

(* entropy_discrete_eq may be helpful in validation.
.
  Written by Claude *)
Definition entropy_def:
    entropy b p s X = mutual_information b p s s X X
End

(* Written by Claude *)
Definition conditional_mutual_information_def:
    conditional_mutual_information b p s1 s2 s3 X Y Z =
      let prod_space =
            prod_measure_space (space s2,subsets s2,distribution p Y)
                               (space s3,subsets s3,distribution p Z)
      in
        mutual_information b p s1
                           (m_space prod_space,measurable_sets prod_space)
                           X (λx. (Y x,Z x)) -
        mutual_information b p s1 s3 X Z
End

(* ************************************************************************* *)
(* Auxiliary lemmas                                                          *)
(* ************************************************************************* *)

(* Written by Claude *)
Theorem IN_MEASURABLE_BOREL_POW[local]:
    ∀sp (f :'a -> extreal). f ∈ Borel_measurable (sp,POW sp)
Proof
    rw [IN_MEASURABLE_BOREL, POW_SIGMA_ALGEBRA, IN_FUNSET, space_def,
        subsets_def, IN_POW, INTER_SUBSET]
QED

(* Written by Claude *)
Theorem prod_sigma_POW:
    ∀s1 s2. FINITE s1 ∧ FINITE s2 ⇒
            subsets ((s1,POW s1) × (s2,POW s2)) = POW (s1 × s2)
Proof
    rw [prod_sigma_def, space_def, subsets_def]
 >> ‘subset_class (s1 × s2) (prod_sets (POW s1) (POW s2))’
       by (rw [subset_class_def, prod_sets_def, IN_POW] \\
           fs [SUBSET_DEF, IN_CROSS])
 >> ‘sigma_algebra (sigma (s1 × s2) (prod_sets (POW s1) (POW s2)))’
       by rw [SIGMA_ALGEBRA_SIGMA]
 >> irule SUBSET_ANTISYM
 >> CONJ_TAC
 >- (rw [SUBSET_DEF, IN_POW] \\
     drule SIGMA_ALGEBRA_SUBSET_CLASS \\
     rw [subset_class_def, SPACE_SIGMA] \\
     METIS_TAC [SUBSET_DEF, IN_CROSS])
 >> rw [Once SUBSET_DEF, IN_POW]
 >> ‘FINITE x’ by METIS_TAC [SUBSET_FINITE, FINITE_CROSS]
 >> qpat_x_assum ‘x ⊆ _’ MP_TAC
 >> qpat_x_assum ‘FINITE x’ MP_TAC
 >> Q.SPEC_TAC (‘x’, ‘A’)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> rw [SIGMA_ALGEBRA_EMPTY]
 >> ‘e INSERT A = {e} ∪ A’ by SET_TAC []
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> rw []
 >> MATCH_MP_TAC (REWRITE_RULE [SUBSET_DEF] SIGMA_SUBSET_SUBSETS)
 >> rw [prod_sets_def, IN_POW]
 >> qexistsl_tac [‘{FST e}’, ‘{SND e}’]
 >> fs [IN_CROSS, SUBSET_DEF, EXTENSION, FORALL_PROD]
 >> Cases_on ‘e’ >> rw []
 >> METIS_TAC []
QED

(* The bridge between extreal terms ‘x * logr b (x / y)’ and real ones.
.
   Written by Claude *)
Theorem mul_logr_normal[local]:
    ∀b x y. (y = 0 ⇒ x = 0) ⇒
            Normal x * logr b (Normal x / Normal y) =
            Normal (x * logr b (x / y))
Proof
    rpt STRIP_TAC
 >> Cases_on ‘y = 0’
 >- fs [GSYM extreal_of_num_def, mul_lzero]
 >> rw [extreal_div_eq, extreal_logr_def, extreal_mul_def]
QED

(* For finite measures on a finite space with all subsets measurable.
.
   Written by Claude *)
Theorem finite_POW_measure_normal[local]:
    ∀sp m s. measure_space (sp,POW sp,m) ∧ m sp ≠ PosInf ∧ s ⊆ sp ⇒
             ∃r. 0 ≤ r ∧ m s = Normal r
Proof
    rpt STRIP_TAC
 >> ‘0 ≤ m s’
      by (Q.ISPECL_THEN [‘(sp,POW sp,m)’, ‘s’] MP_TAC MEASURE_POSITIVE \\
          rw [IN_POW])
 >> ‘m s ≤ m sp’
      by (Q.ISPECL_THEN [‘(sp,POW sp,m)’, ‘s’, ‘sp’] MP_TAC
                        MEASURE_INCREASING \\
          rw [IN_POW])
 >> Cases_on ‘m s’ >> fs [extreal_of_num_def, extreal_le_eq]
 >> fs [GSYM lt_infty]
 >> METIS_TAC [let_trans, lt_infty]
QED

(* ************************************************************************* *)
(* KL divergence on finite spaces                                            *)
(* ************************************************************************* *)

(* Written by Claude *)
Theorem KL_divergence_finite_POW:
    ∀b sp u v.
       FINITE sp ∧ measure_space (sp,POW sp,u) ∧
       measure_space (sp,POW sp,v) ∧ u sp ≠ +∞ ∧ v sp ≠ +∞ ∧
       (∀x. x ∈ sp ∧ v {x} = 0 ⇒ u {x} = 0) ⇒
       KL_divergence b (sp,POW sp) u v =
       ∑ (λx. u {x} * logr b (u {x} / v {x})) sp
Proof
    rw [KL_divergence_def, space_def, subsets_def]
 >> qabbrev_tac ‘M = (sp,POW sp,v)’
 >> ‘∀x. x ∈ sp ⇒ {x} ⊆ sp’ by rw [SUBSET_DEF]
 >> ‘∃a. ∀x. x ∈ sp ⇒ 0 ≤ a x ∧ u {x} = Normal (a x)’
      by (Q.EXISTS_TAC ‘λx. real (u {x})’ >> rw [] \\
          Q.ISPECL_THEN [‘sp’, ‘u’, ‘{x}’] MP_TAC finite_POW_measure_normal \\
          rw [] >> rw [real_normal])
 >> ‘∃c. ∀x. x ∈ sp ⇒ 0 ≤ c x ∧ v {x} = Normal (c x)’
      by (Q.EXISTS_TAC ‘λx. real (v {x})’ >> rw [] \\
          Q.ISPECL_THEN [‘sp’, ‘v’, ‘{x}’] MP_TAC finite_POW_measure_normal \\
          rw [] >> rw [real_normal])
 >> ‘∀x. x ∈ sp ∧ c x = 0 ⇒ a x = 0’
      by (rpt STRIP_TAC \\
          Q.PAT_X_ASSUM ‘∀x. x ∈ sp ∧ v {x} = 0 ⇒ u {x} = 0’
            (Q.ISPEC_THEN ‘x’ MP_TAC) \\
          rw [extreal_of_num_def])
 (* the density of a nonnegative function on singletons *)
 >> Know ‘∀h x. x ∈ sp ∧ (∀y. y ∈ sp ⇒ 0 ≤ h y) ⇒
                (h * M) {x} = h x * v {x}’
 >- (rw [density_measure, Abbr ‘M’] \\
     ‘(λy. h y * indicator_fn {x} y) = (λy. h x * indicator_fn {x} y)’
        by (rw [FUN_EQ_THM, indicator_fn_def] \\
            Cases_on ‘y = x’ >> rw []) >> POP_ORW \\
     ‘0 ≤ h x’ by fs [] \\
     ‘{x} ∈ measurable_sets (sp,POW sp,v)’ by rw [IN_POW] \\
     Cases_on ‘h x’
     >- fs [le_infty, extreal_of_num_def]
     >- (Q.ISPECL_THEN [‘(sp,POW sp,v)’, ‘{x}’] MP_TAC
                       pos_fn_integral_cmul_infty \\
         rw []) \\
     fs [extreal_of_num_def, extreal_le_eq] \\
     Q.ISPECL_THEN [‘(sp,POW sp,v)’, ‘{x}’, ‘r’] MP_TAC
                     pos_fn_integral_cmul_indicator >> rw [])
 >> DISCH_TAC
 (* the density of a nonnegative function on all measurable sets *)
 >> Know ‘∀h s. s ⊆ sp ∧ (∀y. y ∈ sp ⇒ 0 ≤ h y) ⇒
                (h * M) s = ∑ (λx. h x * v {x}) s’
 >- (rpt STRIP_TAC \\
     ‘measure_space (density M h)’
        by (MATCH_MP_TAC measure_space_density \\
            fs [Abbr ‘M’, IN_MEASURABLE_BOREL_POW]) \\
     ‘FINITE s’ by METIS_TAC [SUBSET_FINITE] \\
     Q.ISPECL_THEN [‘density M h’, ‘s’] MP_TAC MEASURE_EXTREAL_SUM_IMAGE \\
     simp [density_def, Abbr ‘M’, IN_POW] \\
     impl_tac >- fs [SUBSET_DEF] >> Rewr \\
     irule EXTREAL_SUM_IMAGE_EQ' >> fs [SUBSET_DEF])
 >> DISCH_TAC
 (* the Radon-Nikodym derivative is u{x} / v{x} where v{x} <> 0 *)
 >> Know ‘∀x. x ∈ sp ∧ c x ≠ (0 :real) ⇒ RN_deriv u M x = u {x} / v {x}’
 >- (rw [RN_deriv_def] \\
     SELECT_ELIM_TAC \\
     CONJ_TAC
     >- (qabbrev_tac ‘f = λx. if c x = (0 :real) then 0 else u {x} / v {x}’ \\
         Q.EXISTS_TAC ‘f’ \\
         ‘∀x. x ∈ sp ⇒ 0 ≤ f x’
            by (rw [Abbr ‘f’] >> MATCH_MP_TAC le_div \\
                rw [extreal_of_num_def, extreal_le_eq] \\
                fs [REAL_LT_LE]) \\
         simp [Abbr ‘M’, IN_MEASURABLE_BOREL_POW] \\
         rw [IN_POW] \\
         ‘FINITE s’ by METIS_TAC [SUBSET_FINITE] \\
         ‘(f * (sp,POW sp,v)) s = ∑ (λx. f x * v {x}) s’
            by (FIRST_X_ASSUM MATCH_MP_TAC >> fs []) \\
         POP_ORW \\
         Q.ISPECL_THEN [‘(sp,POW sp,u)’, ‘s’] MP_TAC
                       MEASURE_EXTREAL_SUM_IMAGE \\
         simp [IN_POW] \\
         impl_tac >- fs [SUBSET_DEF] >> Rewr \\
         irule EXTREAL_SUM_IMAGE_EQ' >> rw [Abbr ‘f’] \\
         ‘x' ∈ sp’ by fs [SUBSET_DEF] \\
         fs [extreal_div_eq, extreal_mul_def, REAL_DIV_RMUL]) \\
     Q.X_GEN_TAC ‘g’ >> rw [Abbr ‘M’] \\
     Q.PAT_X_ASSUM ‘∀s. s ∈ POW sp ⇒ _’ (Q.ISPEC_THEN ‘{x}’ MP_TAC) \\
     rw [IN_POW] \\
     Q.PAT_X_ASSUM ‘∀h x. _ ⇒ (h * M) {x} = _’
       (Q.ISPECL_THEN [‘g’, ‘x’] MP_TAC) \\
     impl_tac >- fs [] >> rw [] \\
     ‘g x = g x * Normal (c x) / Normal (c x)’ by rw [mul_div_refl] \\
     POP_ORW >> rw [])
 >> DISCH_TAC
 >> Know ‘integral (sp,POW sp,u) (λx. logr b (RN_deriv u M x)) =
          integral (sp,POW sp,u)
                   (λx. if a x = (0 :real) then 0 else logr b (u {x} / v {x}))’
 >- (irule integral_cong_AE >> rw [AE_DEF] \\
     Q.EXISTS_TAC ‘{x | x ∈ sp ∧ a x = (0 :real)}’ \\
     ‘FINITE {x | x ∈ sp ∧ a x = (0 :real)}’
        by (MATCH_MP_TAC SUBSET_FINITE_I >> Q.EXISTS_TAC ‘sp’ \\
            rw [SUBSET_DEF]) \\
     rw [null_set_def, IN_POW, SUBSET_DEF]
     >- (Q.ISPECL_THEN [‘(sp,POW sp,u)’,
                        ‘{x | x ∈ sp ∧ a x = (0 :real)}’] MP_TAC
                         MEASURE_EXTREAL_SUM_IMAGE \\
         rw [IN_POW, SUBSET_DEF] \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 >> rw [extreal_of_num_def]) \\
     ‘c x ≠ (0 :real)’
      by (Q.PAT_X_ASSUM ‘∀x. x ∈ sp ∧ c x = 0 ⇒ a x = 0’
            (Q.ISPEC_THEN ‘x’ MP_TAC) >> fs []) >> rw [])
 >> Rewr
 >> ‘∀x. x ∈ sp ⇒
         (if a x = (0 :real) then 0 else logr b (u {x} / v {x})) =
         Normal (if a x = (0 :real) then 0 else logr b (a x / c x))’
      by (rw [extreal_of_num_def] \\
          ‘c x ≠ (0 :real)’
      by (Q.PAT_X_ASSUM ‘∀x. x ∈ sp ∧ c x = 0 ⇒ a x = 0’
            (Q.ISPEC_THEN ‘x’ MP_TAC) >> fs []) \\
          rw [extreal_div_eq, extreal_logr_def])
 >> Q.ISPECL_THEN [‘(sp,POW sp,u)’,
                     ‘λx. if a x = (0 :real) then 0
                          else logr b (u {x} / v {x})’] MP_TAC
                    finite_space_POW_integral_reduce
 >> simp []
 >> impl_tac
 >- (rw [GSYM lt_infty] >> rw [])
 >> Rewr
 >> irule EXTREAL_SUM_IMAGE_EQ' >> rw []
 >- rw [GSYM extreal_of_num_def, mul_lzero]
 >> ‘c x ≠ (0 :real)’
      by (Q.PAT_X_ASSUM ‘∀x. x ∈ sp ∧ c x = 0 ⇒ a x = 0’
            (Q.ISPEC_THEN ‘x’ MP_TAC) >> fs [])
 >> rw [extreal_div_eq, extreal_logr_def, extreal_mul_def, REAL_MUL_COMM]
QED

(* The measure induced by a nonnegative mass function on a finite alphabet.
.
   Written by Claude *)
Theorem measure_space_pmf_POW[local]:
    ∀sp P. FINITE sp ∧ (∀x. x ∈ sp ⇒ 0 ≤ P x) ⇒
           measure_space (sp,POW sp,λs. ∑ (λx. Normal (P x)) s)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces2
 >> rw [m_space_def, measurable_sets_def, POW_SIGMA_ALGEBRA, positive_def,
        additive_def, measure_def, IN_POW]
 >> ‘FINITE s’ by METIS_TAC [SUBSET_FINITE]
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS \\
     fs [SUBSET_DEF, extreal_of_num_def, extreal_le_eq])
 >> ‘FINITE t’ by METIS_TAC [SUBSET_FINITE]
 >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION
 >> rw []
QED

(* The measure induced by a nonnegative extreal mass function on a finite
   alphabet.
.
   Written by Claude *)
Theorem measure_space_extreal_pmf_POW[local]:
    ∀sp (P :α -> extreal). FINITE sp ∧ (∀x. x ∈ sp ⇒ 0 ≤ P x) ⇒
                          measure_space (sp,POW sp,λs. ∑ P s)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces2
 >> rw [m_space_def, measurable_sets_def, POW_SIGMA_ALGEBRA, positive_def,
        additive_def, measure_def, IN_POW]
 >> ‘FINITE s’ by METIS_TAC [SUBSET_FINITE]
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS \\
     fs [SUBSET_DEF])
 >> ‘FINITE t’ by METIS_TAC [SUBSET_FINITE]
 >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION
 >> rw [] >> DISJ1_TAC
 >> rw [] >> MATCH_MP_TAC pos_not_neginf >> fs [SUBSET_DEF]
QED

(* The KL divergence agrees with the textbook definition (e.g. MacKay,
   "Information Theory, Inference, and Learning Algorithms", eq. 2.45):
.
     D_KL(P||Q) = SUM_x P(x) log (P(x) / Q(x))
.
   where P and Q are probability distributions over the same finite alphabet
   ‘sp’, viewed as (real) mass functions. The measures used by
   ‘KL_divergence’ are the ones these mass functions induce on (sp,POW sp).
   The condition ‘Q x = 0 ==> P x = 0’ (P is absolutely continuous w.r.t. Q)
   is needed for D_KL(P||Q) to be finite. Note that the theorem does not need
   P and Q to sum to 1.
.
   Written by Claude *)
Theorem KL_divergence_pmf:
    ∀b sp P Q.
       FINITE sp ∧ (∀x. x ∈ sp ⇒ 0 ≤ P x ∧ 0 ≤ Q x) ∧
       (∀x. x ∈ sp ∧ Q x = 0 ⇒ P x = 0) ⇒
       KL_divergence b (sp,POW sp) (λs. ∑ (λx. Normal (P x)) s)
                                   (λs. ∑ (λx. Normal (Q x)) s) =
       Normal (∑ (λx. P x * logr b (P x / Q x)) sp)
Proof
    rpt STRIP_TAC
 >> qmatch_goalsub_abbrev_tac ‘KL_divergence b (sp,POW sp) u v’
 >> Know ‘KL_divergence b (sp,POW sp) u v =
          ∑ (λx. u {x} * logr b (u {x} / v {x})) sp’
 >- (MATCH_MP_TAC KL_divergence_finite_POW \\
     simp [Abbr ‘u’, Abbr ‘v’, EXTREAL_SUM_IMAGE_NORMAL] \\
     rw [measure_space_pmf_POW, GSYM extreal_of_num_def] \\
     fs [extreal_of_num_def])
 >> Rewr
 >> simp [Abbr ‘u’, Abbr ‘v’, GSYM EXTREAL_SUM_IMAGE_NORMAL]
 >> irule EXTREAL_SUM_IMAGE_EQ' >> rw []
 >> MATCH_MP_TAC mul_logr_normal >> rw []
QED

(* [KL_divergence_def] agrees with [KL_divergence_discrete_def] on the
   measures induced by ‘P’ and ‘Q’, when P is absolutely continuous w.r.t. Q.
.
   Written by Claude *)
Theorem KL_divergence_discrete_eq:
    ∀b A (P :α -> extreal) Q.
       FINITE A ∧
       (∀x. x ∈ A ⇒ 0 ≤ P x ∧ P x ≠ +∞ ∧ 0 ≤ Q x ∧ Q x ≠ +∞) ∧
       (∀x. x ∈ A ∧ Q x = 0 ⇒ P x = 0) ⇒
       KL_divergence b (A,POW A) (λs. ∑ P s) (λs. ∑ Q s) =
       KL_divergence_discrete b A P Q
Proof
    rpt STRIP_TAC
 >> ‘¬∃x. x ∈ A ∧ Q x = 0 ∧ P x ≠ 0’ by METIS_TAC []
 >> simp [KL_divergence_discrete_def]
 >> qmatch_goalsub_abbrev_tac ‘KL_divergence b (A,POW A) u v’
 >> Know ‘KL_divergence b (A,POW A) u v =
          ∑ (λx. u {x} * logr b (u {x} / v {x})) A’
 >- (MATCH_MP_TAC KL_divergence_finite_POW \\
     simp [Abbr ‘u’, Abbr ‘v’, measure_space_extreal_pmf_POW] \\
     rw [EXTREAL_SUM_IMAGE_NOT_POSINF])
 >> Rewr
 >> simp [Abbr ‘u’, Abbr ‘v’]
QED

(* ************************************************************************* *)
(* Mutual information on finite spaces                                       *)
(* ************************************************************************* *)

(* Written by Claude *)
Theorem random_variable_POW[local]:
    ∀p X s. prob_space p ∧ POW (p_space p) = events p ∧
            (∀x. x ∈ p_space p ⇒ X x ∈ s) ⇒
            random_variable X p (s,POW s)
Proof
    rw [random_variable_def, IN_MEASURABLE, IN_FUNSET, space_def,
        subsets_def]
 >> Q.PAT_X_ASSUM ‘_ = events p’ (REWRITE_TAC o wrap o GSYM)
 >> rw [IN_POW, INTER_SUBSET]
QED

(* Written by Claude *)
Theorem random_variable_POW_IN[local]:
    ∀p X s x. random_variable X p (s,POW s) ∧ x ∈ p_space p ⇒ X x ∈ s
Proof
    rw [random_variable_def, IN_MEASURABLE, IN_FUNSET, space_def]
QED

(* Written by Claude *)
Theorem finite_POW_prob_normal[local]:
    ∀p e. prob_space p ∧ POW (p_space p) = events p ∧
          e ⊆ p_space p ⇒ ∃r. 0 ≤ r ∧ r ≤ 1 ∧ prob p e = Normal r
Proof
    rpt STRIP_TAC
 >> ‘e ∈ events p’ by METIS_TAC [IN_POW]
 >> METIS_TAC [prob_normal]
QED

(* Written by Claude *)
Theorem distribution_normal[local]:
    ∀p X x. prob_space p ∧ POW (p_space p) = events p ⇒
            ∃r. 0 ≤ r ∧ r ≤ 1 ∧ distribution p X {x} = Normal r
Proof
    rw [distribution_def]
 >> MATCH_MP_TAC finite_POW_prob_normal >> rw [INTER_SUBSET]
QED

(* Written by Claude *)
Theorem joint_distribution_normal[local]:
    ∀p X Y x. prob_space p ∧ POW (p_space p) = events p ⇒
              ∃r. 0 ≤ r ∧ r ≤ 1 ∧ joint_distribution p X Y {x} = Normal r
Proof
    rw [joint_distribution_def]
 >> MATCH_MP_TAC finite_POW_prob_normal >> rw [INTER_SUBSET]
QED

(* Written by Claude *)
Theorem joint_distribution_le_distribution[local]:
    ∀p X Y x y. prob_space p ∧ POW (p_space p) = events p ⇒
                joint_distribution p X Y {(x,y)} ≤ distribution p X {x} ∧
                joint_distribution p X Y {(x,y)} ≤ distribution p Y {y}
Proof
    rw [joint_distribution_def, distribution_def]
 >> MATCH_MP_TAC PROB_INCREASING
 >> Q.PAT_X_ASSUM ‘_ = events p’ (REWRITE_TAC o wrap o GSYM)
 >> rw [IN_POW, INTER_SUBSET, SUBSET_DEF, IN_PREIMAGE]
QED

(* Written by Claude *)
Theorem joint_distribution_eq_0[local]:
    ∀p X Y x y. prob_space p ∧ POW (p_space p) = events p ∧
                (distribution p X {x} = 0 ∨ distribution p Y {y} = 0) ⇒
                joint_distribution p X Y {(x,y)} = 0
Proof
    rpt STRIP_TAC
 >> (REWRITE_TAC [GSYM le_antisym] \\
     CONJ_TAC >- METIS_TAC [joint_distribution_le_distribution] \\
     rw [joint_distribution_def] \\
     MATCH_MP_TAC PROB_POSITIVE \\
     Q.PAT_X_ASSUM ‘_ = events p’ (REWRITE_TAC o wrap o GSYM) \\
     rw [IN_POW, INTER_SUBSET])
QED

(* The general form of [finite_mutual_information_reduce].
.
   Written by Claude *)
Theorem finite_mutual_information_reduce_POW:
    ∀b p s1 s2 X Y.
       prob_space p ∧ FINITE (p_space p) ∧ POW (p_space p) = events p ∧
       random_variable X p (s1,POW s1) ∧ random_variable Y p (s2,POW s2) ∧
       FINITE s1 ∧ FINITE s2 ⇒
       mutual_information b p (s1,POW s1) (s2,POW s2) X Y =
       ∑ (λ(x,y). joint_distribution p X Y {(x,y)} *
                      logr b (joint_distribution p X Y {(x,y)} /
                              (distribution p X {x} * distribution p Y {y})))
             (s1 × s2)
Proof
    rw [mutual_information_def, space_def, subsets_def,
        prod_measure_space_def, prod_sigma_POW]
 >> ‘prob_space (s1,POW s1,distribution p X) ∧
     prob_space (s2,POW s2,distribution p Y)’
      by (CONJ_TAC
          >- (Q.ISPECL_THEN [‘p’, ‘X’, ‘(s1,POW s1)’] MP_TAC
                              distribution_prob_space \\
              rw [POW_SIGMA_ALGEBRA, space_def, subsets_def]) \\
          Q.ISPECL_THEN [‘p’, ‘Y’, ‘(s2,POW s2)’] MP_TAC
                        distribution_prob_space \\
          rw [POW_SIGMA_ALGEBRA, space_def, subsets_def])
 >> qabbrev_tac ‘M1 = (s1,POW s1,distribution p X)’
 >> qabbrev_tac ‘M2 = (s2,POW s2,distribution p Y)’
 >> ‘∀x y. x ∈ s1 ∧ y ∈ s2 ⇒
           prod_measure M1 M2 {(x,y)} =
           distribution p X {x} * distribution p Y {y}’
      by (rpt STRIP_TAC \\
          REWRITE_TAC [GSYM CROSS_SINGS] \\
          Q.ISPECL_THEN [‘M1’, ‘M2’, ‘{x}’, ‘{y}’] MP_TAC PROD_MEASURE_CROSS \\
          fs [prob_space_def, Abbr ‘M1’, Abbr ‘M2’, IN_POW])
 >> Know ‘KL_divergence b (s1 × s2,POW (s1 × s2))
            (joint_distribution p X Y) (prod_measure M1 M2) =
          ∑ (λz. joint_distribution p X Y {z} *
                     logr b (joint_distribution p X Y {z} /
                             prod_measure M1 M2 {z})) (s1 × s2)’
 >- (MATCH_MP_TAC KL_divergence_finite_POW \\
     rw [FINITE_CROSS]
     >- (MATCH_MP_TAC finite_marginal_product_space_POW2 >> rw [])
     >- (‘sigma_finite_measure_space M1 ∧ sigma_finite_measure_space M2’
           by (fs [sigma_finite_measure_space_def, prob_space_def] \\
               rw [] >> MATCH_MP_TAC FINITE_IMP_SIGMA_FINITE \\
               rw [extreal_of_num_def]) \\
         Q.ISPECL_THEN [‘M1’, ‘M2’] MP_TAC measure_space_prod_measure \\
         rw [prod_measure_space_def, Abbr ‘M1’, Abbr ‘M2’, prod_sigma_POW])
     >- (rw [joint_distribution_def] \\
         ‘PREIMAGE (λx. (X x,Y x)) (s1 × s2) ∩ p_space p ∈ events p’
            by (Q.PAT_X_ASSUM ‘_ = events p’ (REWRITE_TAC o wrap o GSYM) \\
                rw [IN_POW, INTER_SUBSET]) \\
         METIS_TAC [PROB_FINITE])
     >- (Q.ISPECL_THEN [‘M1’, ‘M2’, ‘s1’, ‘s2’] MP_TAC PROD_MEASURE_CROSS \\
         fs [prob_space_def, Abbr ‘M1’, Abbr ‘M2’, IN_POW] \\
         rw [mul_lone, extreal_of_num_def]) \\
     Cases_on ‘x’ >> fs [] \\
     MATCH_MP_TAC joint_distribution_eq_0 >> rw [] \\
     METIS_TAC [entire])
 >> Rewr
 >> irule EXTREAL_SUM_IMAGE_EQ'
 >> (simp [FORALL_PROD, FINITE_CROSS] >> rw [])
QED

(* Written by Claude *)
Theorem finite_mutual_information_reduce:
    ∀b p X Y.
       prob_space p ∧ POW (p_space p) = events p ∧
       random_variable X p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
       random_variable Y p (IMAGE Y (p_space p),POW (IMAGE Y (p_space p))) ∧
       FINITE (p_space p) ⇒
      (mutual_information b p (IMAGE X (p_space p),POW (IMAGE X (p_space p)))
                              (IMAGE Y (p_space p),POW (IMAGE Y (p_space p)))
                              X Y =
       ∑ (λ(x,y). joint_distribution p X Y {(x,y)} *
                      logr b (joint_distribution p X Y {(x,y)} /
                              (distribution p X {x} * distribution p Y {y})))
             (IMAGE X (p_space p) × IMAGE Y (p_space p)))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC finite_mutual_information_reduce_POW
 >> rw [IMAGE_FINITE]
QED

(* Written by Claude *)
Theorem finite_mutual_information_reduce2:
    ∀b p X Y Z.
       prob_space p ∧ POW (p_space p) = events p ∧
       random_variable X p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
       random_variable Y p (IMAGE Y (p_space p),POW (IMAGE Y (p_space p))) ∧
       random_variable Z p (IMAGE Z (p_space p),POW (IMAGE Z (p_space p))) ∧
       FINITE (p_space p) ⇒
      (mutual_information b p
         (IMAGE X (p_space p),POW (IMAGE X (p_space p)))
         (IMAGE Y (p_space p) × IMAGE Z (p_space p),
          POW (IMAGE Y (p_space p) × IMAGE Z (p_space p)))
         X (λx. (Y x,Z x)) =
       ∑ (λ(x,(y,z)).
                joint_distribution p X (λx. (Y x,Z x)) {(x,(y,z))} *
                logr b (joint_distribution p X (λx. (Y x,Z x)) {(x,(y,z))} /
                        (distribution p X {x} *
                         distribution p (λx. (Y x,Z x)) {(y,z)})))
             (IMAGE X (p_space p) ×
              (IMAGE Y (p_space p) × IMAGE Z (p_space p))))
Proof
    rpt STRIP_TAC
 >> Q.ISPECL_THEN [‘b’, ‘p’, ‘IMAGE X (p_space p)’,
                     ‘IMAGE Y (p_space p) × IMAGE Z (p_space p)’,
                     ‘X’, ‘λx. (Y x,Z x)’] MP_TAC
                    finite_mutual_information_reduce_POW
 >> impl_tac
 >- (rw [IMAGE_FINITE, FINITE_CROSS] \\
     MATCH_MP_TAC random_variable_POW >> rw [IN_CROSS] \\
     METIS_TAC [])
 >> Rewr
 >> irule EXTREAL_SUM_IMAGE_EQ'
 >> (simp [FORALL_PROD, IMAGE_FINITE, FINITE_CROSS] >> rw [])
QED

(* ************************************************************************* *)
(* Entropy on finite spaces                                                  *)
(* ************************************************************************* *)

(* Written by Claude *)
Theorem finite_entropy_reduce:
    ∀b p X.
       prob_space p ∧ POW (p_space p) = events p ∧
       random_variable X p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
       FINITE (p_space p) ⇒
      (entropy b p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) X =
       -∑ (λx. distribution p X {x} * logr b (distribution p X {x}))
              (IMAGE X (p_space p)))
Proof
    rw [entropy_def, finite_mutual_information_reduce]
 >> qabbrev_tac ‘sX = IMAGE X (p_space p)’
 >> ‘FINITE sX’ by rw [Abbr ‘sX’, IMAGE_FINITE]
 >> ‘∀x y. joint_distribution p X X {(x,y)} =
           if x = y then distribution p X {x} else 0’
      by (rw [joint_distribution_def, distribution_def]
          >- (AP_TERM_TAC >> rw [EXTENSION, IN_PREIMAGE]) \\
          ‘PREIMAGE (λx. (X x,X x)) {(x,y)} ∩ p_space p = {}’
             by rw [EXTENSION, IN_PREIMAGE] \\
          rw [PROB_EMPTY])
 >> ‘∃q. ∀x. 0 ≤ q x ∧ q x ≤ 1 ∧ distribution p X {x} = Normal (q x)’
      by (Q.EXISTS_TAC ‘λx. real (distribution p X {x})’ >> rw [] \\
          Q.ISPECL_THEN [‘p’, ‘X’, ‘x’] MP_TAC distribution_normal \\
          rw [] >> rw [real_normal])
 >> qabbrev_tac ‘tt = λx. q x * logr b (q x / (q x * q x))’
 >> Know ‘∑ (λ(x,y). joint_distribution p X X {(x,y)} *
                         logr b (joint_distribution p X X {(x,y)} /
                                 (distribution p X {x} *
                                  distribution p X {y}))) (sX × sX) =
          ∑ (λ(x,y). Normal (if x = y then tt x else 0)) (sX × sX)’
 >- (irule EXTREAL_SUM_IMAGE_EQ' \\
     (simp [FORALL_PROD, FINITE_CROSS, extreal_mul_def, Abbr ‘tt’] >> rw [])
     >- (MATCH_MP_TAC mul_logr_normal >> rw []) \\
     rw [GSYM extreal_of_num_def, mul_lzero])
 >> Rewr
 >> Know ‘∑ (λ(x,y). Normal (if x = y then tt x else 0)) (sX × sX) =
          ∑ (λx. ∑ (λy. Normal (if x = y then tt x else 0)) sX) sX’
 >- (Q.ISPECL_THEN [‘sX’, ‘sX’,
                       ‘λx y. Normal (if x = y then tt x else 0)’] MP_TAC
                      EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     rw [extreal_not_infty] \\
     irule EXTREAL_SUM_IMAGE_EQ' \\
     (simp [FORALL_PROD, FINITE_CROSS] >> rw []))
 >> Rewr
 >> Know ‘∀x. x ∈ sX ⇒
              ∑ (λy. Normal (if x = y then tt x else 0)) sX = Normal (tt x)’
 >- (rw [EXTREAL_SUM_IMAGE_NORMAL, extreal_11] \\
     ‘sX = x INSERT (sX DELETE x)’ by (rw [EXTENSION] >> METIS_TAC []) \\
     POP_ORW >> rw [REAL_SUM_IMAGE_THM, FINITE_DELETE] \\
     ‘sX DELETE x DELETE x = sX DELETE x’ by SET_TAC [] >> POP_ORW \\
     qmatch_goalsub_abbrev_tac ‘∑ f (sX DELETE x)’ \\
     ‘∑ f (sX DELETE x) = ∑ (λy. 0) (sX DELETE x)’
        by (irule REAL_SUM_IMAGE_EQ >> rw [Abbr ‘f’, FINITE_DELETE]) \\
     rw [REAL_SUM_IMAGE_0, FINITE_DELETE])
 >> DISCH_TAC
 >> ‘∑ (λx. ∑ (λy. Normal (if x = y then tt x else 0)) sX) sX =
     ∑ (λx. Normal (tt x)) sX’
      by (irule EXTREAL_SUM_IMAGE_EQ' >> rw [])
 >> POP_ORW
 >> ‘∑ (λx. distribution p X {x} * logr b (distribution p X {x})) sX =
     ∑ (λx. Normal (q x * logr b (q x))) sX’
      by (irule EXTREAL_SUM_IMAGE_EQ' >>
          rw [extreal_logr_def, extreal_mul_def])
 >> POP_ORW
 >> rw [EXTREAL_SUM_IMAGE_NORMAL, extreal_ainv_def, extreal_11,
        GSYM REAL_SUM_IMAGE_NEG]
 >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ
 >> rw [Abbr ‘tt’]
 >> Cases_on ‘q x = 0’ >- rw []
 >> ‘0 < q x’ by METIS_TAC [REAL_LT_LE]
 >> ‘q x / (q x * q x) = inv (q x)’
      by (rw [real_div, REAL_INV_MUL] \\
          rw [REAL_MUL_ASSOC, REAL_MUL_RINV])
 >> DISJ2_TAC
 >> ‘q x / (q x) pow 2 = inv (q x)’ by rw [POW_2]
 >> rw [logr_inv]
QED

(* [entropy_def] agrees with [entropy_discrete_def] applied to the mass
   function of X on its (finite) range.
.
   Written by Claude *)
Theorem entropy_discrete_eq:
    ∀b p X.
       prob_space p ∧ POW (p_space p) = events p ∧
       random_variable X p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
       FINITE (p_space p) ⇒
       entropy b p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) X =
       entropy_discrete b (IMAGE X (p_space p)) (λx. distribution p X {x})
Proof
    rw [entropy_discrete_def, finite_entropy_reduce]
 >> qabbrev_tac ‘sX = IMAGE X (p_space p)’
 >> ‘FINITE sX’ by rw [Abbr ‘sX’, IMAGE_FINITE]
 >> ‘∃q. ∀x. 0 ≤ q x ∧ q x ≤ 1 ∧ distribution p X {x} = Normal (q x)’
      by (Q.EXISTS_TAC ‘λx. real (distribution p X {x})’ >> rw [] \\
          Q.ISPECL_THEN [‘p’, ‘X’, ‘x’] MP_TAC distribution_normal \\
          rw [] >> rw [real_normal])
 >> ‘∑ (λx. distribution p X {x} * logr b (distribution p X {x})) sX =
     ∑ (λx. Normal (q x * logr b (q x))) sX’
      by (irule EXTREAL_SUM_IMAGE_EQ' >>
          rw [extreal_logr_def, extreal_mul_def])
 >> POP_ORW
 >> ‘∑ (λx. distribution p X {x} * logr b (1 / distribution p X {x})) sX =
     ∑ (λx. Normal (q x * logr b (1 / q x))) sX’
      by (irule EXTREAL_SUM_IMAGE_EQ' >> rw [] \\
          Cases_on ‘q x = 0’
          >- rw [GSYM extreal_of_num_def, mul_lzero] \\
          ‘(1 :extreal) / Normal (q x) = Normal (1 / q x)’
             by rw [extreal_of_num_def, extreal_div_eq] \\
          rw [extreal_logr_def, extreal_mul_def])
 >> POP_ORW
 >> rw [EXTREAL_SUM_IMAGE_NORMAL, extreal_ainv_def, extreal_11,
        GSYM REAL_SUM_IMAGE_NEG]
 >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ
 >> rw []
 >> Cases_on ‘q x = 0’ >- rw []
 >> ‘0 < q x’ by METIS_TAC [REAL_LT_LE]
 >> rw [real_div, logr_inv]
QED

(* ************************************************************************* *)
(* Conditional mutual information on finite spaces                           *)
(* ************************************************************************* *)

(* Written by Claude *)
Theorem marginal_distribution_POW[local]:
    ∀p X Y s2 x.
       prob_space p ∧ POW (p_space p) = events p ∧
       random_variable Y p (s2,POW s2) ∧ FINITE s2 ⇒
       distribution p X {x} =
       ∑ (λy. joint_distribution p X Y {(x,y)}) s2
Proof
    rw [distribution_def, joint_distribution_def]
 >> Q.ISPECL_THEN [‘p’, ‘λy. PREIMAGE Y {y}’,
                     ‘PREIMAGE X {x} ∩ p_space p’, ‘s2’] MP_TAC
                    PROB_EXTREAL_SUM_IMAGE_FN
 >> Q.PAT_X_ASSUM ‘_ = events p’ (REWRITE_TAC o wrap o GSYM)
 >> impl_tac
 >- (rw [IN_POW, INTER_SUBSET]
     >- rw [SUBSET_DEF]
     >- (rw [DISJOINT_DEF, EXTENSION, IN_PREIMAGE] \\
         Cases_on ‘Y x' = x’ >> rw []) \\
     rw [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE] \\
     EQ_TAC >> rw [] \\
     MATCH_MP_TAC random_variable_POW_IN \\
     Q.EXISTS_TAC ‘p’ >> rw [])
 >> Rewr
 >> irule EXTREAL_SUM_IMAGE_EQ' >> rw []
 >> AP_TERM_TAC
 >> rw [EXTENSION, IN_PREIMAGE, IN_INTER]
 >> EQ_TAC >> rw []
QED

(* I(X;Y) = SIGMA p(x,y) log (p(x,y) / p(y)) - SIGMA p(x) log p(x).
.
   Written by Claude *)
Theorem finite_mutual_information_split[local]:
    ∀b p s1 s2 X Y.
       prob_space p ∧ FINITE (p_space p) ∧ POW (p_space p) = events p ∧
       random_variable X p (s1,POW s1) ∧ random_variable Y p (s2,POW s2) ∧
       FINITE s1 ∧ FINITE s2 ⇒
       mutual_information b p (s1,POW s1) (s2,POW s2) X Y =
       ∑ (λ(x,y). joint_distribution p X Y {(x,y)} *
                      logr b (joint_distribution p X Y {(x,y)} /
                              distribution p Y {y})) (s1 × s2) -
       ∑ (λx. distribution p X {x} * logr b (distribution p X {x})) s1
Proof
    rw [finite_mutual_information_reduce_POW]
 >> ‘∃px. ∀x. 0 ≤ px x ∧ distribution p X {x} = Normal (px x)’
      by (Q.EXISTS_TAC ‘λx. real (distribution p X {x})’ >> rw [] \\
          Q.ISPECL_THEN [‘p’, ‘X’, ‘x’] MP_TAC distribution_normal \\
          rw [] >> rw [real_normal])
 >> ‘∃py. ∀y. 0 ≤ py y ∧ distribution p Y {y} = Normal (py y)’
      by (Q.EXISTS_TAC ‘λy. real (distribution p Y {y})’ >> rw [] \\
          Q.ISPECL_THEN [‘p’, ‘Y’, ‘y’] MP_TAC distribution_normal \\
          rw [] >> rw [real_normal])
 >> ‘∃j. ∀x y. 0 ≤ j x y ∧ joint_distribution p X Y {(x,y)} = Normal (j x y)’
      by (Q.EXISTS_TAC ‘λx y. real (joint_distribution p X Y {(x,y)})’ \\
          rw [] \\
          Q.ISPECL_THEN [‘p’, ‘X’, ‘Y’, ‘(x,y)’] MP_TAC
                          joint_distribution_normal \\
          rw [] >> rw [real_normal])
 >> ‘∀x y. px x = 0 ∨ py y = 0 ⇒ j x y = 0’
      by (rpt STRIP_TAC \\
          Q.ISPECL_THEN [‘p’, ‘X’, ‘Y’, ‘x’, ‘y’] MP_TAC
                        joint_distribution_eq_0 \\
          rw [extreal_of_num_def])
 >> ‘∀x. ∑ (λy. j x y) s2 = px x’
      by (GEN_TAC \\
          Q.ISPECL_THEN [‘p’, ‘X’, ‘Y’, ‘s2’, ‘x’] MP_TAC
                          marginal_distribution_POW \\
          rw [EXTREAL_SUM_IMAGE_NORMAL])
 >> ‘FINITE (s1 × s2)’ by rw [FINITE_CROSS]
 >> (simp [FORALL_PROD] >> rw [])
 >> ‘∑ (λ(x,y). Normal (j x y) *
                    logr b (Normal (j x y) / (Normal (px x) * Normal (py y))))
           (s1 × s2) =
     Normal (∑ (λ(x,y). j x y * logr b (j x y / (px x * py y)))
                   (s1 × s2))’
      by (rw [GSYM EXTREAL_SUM_IMAGE_NORMAL] \\
          irule EXTREAL_SUM_IMAGE_EQ' \\
          (simp [FORALL_PROD, extreal_mul_def] >> rw []) \\
          MATCH_MP_TAC mul_logr_normal >> rw [] \\
          fs [REAL_ENTIRE])
 >> POP_ORW
 >> ‘∑ (λ(x,y). Normal (j x y) * logr b (Normal (j x y) / Normal (py y)))
           (s1 × s2) =
     Normal (∑ (λ(x,y). j x y * logr b (j x y / py y)) (s1 × s2))’
      by (rw [GSYM EXTREAL_SUM_IMAGE_NORMAL] \\
          irule EXTREAL_SUM_IMAGE_EQ' \\
          (simp [FORALL_PROD] >> rw []) \\
          MATCH_MP_TAC mul_logr_normal >> rw [])
 >> POP_ORW
 >> ‘∑ (λx. Normal (px x) * logr b (Normal (px x))) s1 =
     Normal (∑ (λx. px x * logr b (px x)) s1)’
      by (rw [GSYM EXTREAL_SUM_IMAGE_NORMAL] \\
          irule EXTREAL_SUM_IMAGE_EQ' \\
          rw [extreal_logr_def, extreal_mul_def])
 >> POP_ORW
 >> rw [extreal_sub_def, extreal_11]
 (* the rest is in real *)
 >> ‘∑ (λ(x,y). j x y * logr b (j x y / (px x * py y))) (s1 × s2) =
     ∑ (λ(x,y). j x y * logr b (j x y / py y) -
                    j x y * logr b (px x)) (s1 × s2)’
      by (irule REAL_SUM_IMAGE_EQ >> (simp [FORALL_PROD] >> rw []) \\
          Cases_on ‘j p_1 p_2 = 0’ >- rw [] \\
          ‘0 < j p_1 p_2 ∧ 0 < px p_1 ∧ 0 < py p_2’
             by METIS_TAC [REAL_LT_LE] \\
          rw [GSYM REAL_SUB_LDISTRIB, REAL_EQ_LMUL] \\
          rw [logr_div, logr_mul, REAL_LT_MUL] \\
          REAL_ARITH_TAC)
 >> POP_ORW
 >> ‘∑ (λ(x,y). j x y * logr b (j x y / py y) - j x y * logr b (px x))
           (s1 × s2) =
     ∑ (λ(x,y). j x y * logr b (j x y / py y)) (s1 × s2) -
     ∑ (λ(x,y). j x y * logr b (px x)) (s1 × s2)’
      by (rw [GSYM REAL_SUM_IMAGE_SUB] \\
          irule REAL_SUM_IMAGE_EQ >> (simp [FORALL_PROD] >> rw []))
 >> POP_ORW
 >> Suff ‘∑ (λ(x,y). j x y * logr b (px x)) (s1 × s2) =
          ∑ (λx. px x * logr b (px x)) s1’ >- rw []
 (* nested sums *)
 >> Know ‘Normal (∑ (λ(x,y). j x y * logr b (px x)) (s1 × s2)) =
          ∑ (λx. ∑ (λy. Normal (j x y * logr b (px x))) s2) s1’
 >- (rw [GSYM EXTREAL_SUM_IMAGE_NORMAL] \\
     Q.ISPECL_THEN [‘s1’, ‘s2’,
                       ‘λx y. Normal (j x y * logr b (px x))’] MP_TAC
                      EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     rw [extreal_not_infty] \\
     irule EXTREAL_SUM_IMAGE_EQ' >> (simp [FORALL_PROD] >> rw []))
 >> ‘∀x. ∑ (λy. j x y * logr b (px x)) s2 = px x * logr b (px x)’
      by (GEN_TAC \\
          ‘(λy. j x y * logr b (px x)) = (λy. logr b (px x) * j x y)’
             by simp [FUN_EQ_THM, Once REAL_MUL_COMM] >> POP_ORW \\
          simp [REAL_SUM_IMAGE_CMUL])
 >> ‘∑ (λx. ∑ (λy. Normal (j x y * logr b (px x))) s2) s1 =
     Normal (∑ (λx. px x * logr b (px x)) s1)’
      by simp [EXTREAL_SUM_IMAGE_NORMAL]
 >> POP_ORW
 >> simp [extreal_11]
QED

(* Written by Claude *)
Theorem EXTREAL_SUM_IMAGE_NORMAL_EXISTS[local]:
    ∀f s. FINITE s ∧ (∀x. x ∈ s ⇒ ∃r. f x = Normal r) ⇒
          ∃r. ∑ f s = Normal r
Proof
    rpt STRIP_TAC
 >> ‘∑ f s ≠ −∞ ∧ ∑ f s ≠ +∞’
      by (CONJ_TAC
          >- (MATCH_MP_TAC
                (CONJUNCT1 (SPEC_ALL EXTREAL_SUM_IMAGE_NOT_INFTY)) \\
              METIS_TAC [extreal_not_infty]) \\
          MATCH_MP_TAC (CONJUNCT2 (SPEC_ALL EXTREAL_SUM_IMAGE_NOT_INFTY)) \\
          METIS_TAC [extreal_not_infty])
 >> METIS_TAC [extreal_cases]
QED

(* Written by Claude *)
Theorem joint_logr_normal[local]:
    ∀b p X Y x y.
       prob_space p ∧ POW (p_space p) = events p ⇒
       ∃r. joint_distribution p X Y {(x,y)} *
           logr b (joint_distribution p X Y {(x,y)} / distribution p Y {y}) =
           Normal r
Proof
    rpt STRIP_TAC
 >> ‘∃j. joint_distribution p X Y {(x,y)} = Normal j’
      by METIS_TAC [joint_distribution_normal]
 >> ‘∃d. distribution p Y {y} = Normal d’
      by METIS_TAC [distribution_normal]
 >> ‘d = 0 ⇒ j = 0’
      by (rpt STRIP_TAC \\
          ‘joint_distribution p X Y {(x,y)} = 0’
             by (MATCH_MP_TAC joint_distribution_eq_0 \\
                 fs [extreal_of_num_def]) \\
          fs [extreal_of_num_def])
 >> Q.EXISTS_TAC ‘j * logr b (j / d)’
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC mul_logr_normal >> art []
QED

(* Written by Claude *)
Theorem finite_conditional_mutual_information_reduce:
    ∀b p X Y Z.
       prob_space p ∧ POW (p_space p) = events p ∧
       random_variable X p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
       random_variable Y p (IMAGE Y (p_space p),POW (IMAGE Y (p_space p))) ∧
       random_variable Z p (IMAGE Z (p_space p),POW (IMAGE Z (p_space p))) ∧
       FINITE (p_space p) ⇒
      (conditional_mutual_information b p
         (IMAGE X (p_space p),POW (IMAGE X (p_space p)))
         (IMAGE Y (p_space p),POW (IMAGE Y (p_space p)))
         (IMAGE Z (p_space p),POW (IMAGE Z (p_space p))) X Y Z =
       -∑ (λ(x,z). joint_distribution p X Z {(x,z)} *
                       logr b (joint_distribution p X Z {(x,z)} /
                               distribution p Z {z}))
              (IMAGE X (p_space p) × IMAGE Z (p_space p)) -
       -∑ (λ(x,(y,z)).
                 joint_distribution p X (λx. (Y x,Z x)) {(x,(y,z))} *
                 logr b (joint_distribution p X (λx. (Y x,Z x)) {(x,(y,z))} /
                         distribution p (λx. (Y x,Z x)) {(y,z)}))
              (IMAGE X (p_space p) × IMAGE (λx. (Y x,Z x)) (p_space p)))
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘S1 = IMAGE X (p_space p)’
 >> qabbrev_tac ‘S2 = IMAGE Y (p_space p)’
 >> qabbrev_tac ‘S3 = IMAGE Z (p_space p)’
 >> qabbrev_tac ‘YZ = λx. (Y x,Z x)’
 >> ‘FINITE S1 ∧ FINITE S2 ∧ FINITE S3’
      by rw [Abbr ‘S1’, Abbr ‘S2’, Abbr ‘S3’, IMAGE_FINITE]
 >> ‘random_variable YZ p (S2 × S3,POW (S2 × S3))’
      by (MATCH_MP_TAC random_variable_POW \\
          rw [Abbr ‘YZ’, Abbr ‘S2’, Abbr ‘S3’, IN_CROSS] >> METIS_TAC [])
 >> rw [conditional_mutual_information_def, prod_measure_space_def,
        space_def, subsets_def, prod_sigma_POW]
 >> Q.ISPECL_THEN [‘b’, ‘p’, ‘S1’, ‘S2 × S3’, ‘X’, ‘YZ’] MP_TAC
                    finite_mutual_information_split
 >> impl_tac >- rw [FINITE_CROSS]
 >> Rewr
 >> Q.ISPECL_THEN [‘b’, ‘p’, ‘S1’, ‘S3’, ‘X’, ‘Z’] MP_TAC
                    finite_mutual_information_split
 >> impl_tac >- rw []
 >> Rewr
 (* restrict the sum over S1 CROSS (S2 CROSS S3) to S1 CROSS (IMAGE YZ) *)
 >> qmatch_abbrev_tac ‘A - H - (B - H) = -B - -A'’
 >> Know ‘A = A'’
 >- (qunabbrevl_tac [‘A’, ‘A'’] \\
     qmatch_abbrev_tac ‘(∑ f s :extreal) = ∑ g t’ \\
     ‘FINITE s’ by rw [Abbr ‘s’, FINITE_CROSS] \\
     ‘t ⊆ s’
        by ((simp [Abbr ‘s’, Abbr ‘t’, SUBSET_DEF, Abbr ‘YZ’, Abbr ‘S2’,
                   Abbr ‘S3’, FORALL_PROD] >> rw []) >> METIS_TAC []) \\
     ‘∀x w. joint_distribution p X YZ {(x,w)} *
            logr b (joint_distribution p X YZ {(x,w)} /
                    distribution p YZ {w}) ≠ −∞’
        by (rpt GEN_TAC \\
            Q.ISPECL_THEN [‘b’, ‘p’, ‘X’, ‘YZ’, ‘x’, ‘w’] MP_TAC
                          joint_logr_normal \\
            rw [] >> rw [extreal_not_infty]) \\
     ‘∑ f s = ∑ f (s DIFF (s DIFF t))’
        by (irule EXTREAL_SUM_IMAGE_ZERO_DIFF \\
            rpt CONJ_TAC
            >- (simp [Abbr ‘f’, Abbr ‘s’, Abbr ‘t’, FORALL_PROD] \\
                rw [] >> DISJ1_TAC \\
                rw [joint_distribution_def] \\
                qmatch_abbrev_tac ‘prob p E = 0’ \\
                ‘E = {}’ by (rw [Abbr ‘E’, EXTENSION, IN_PREIMAGE] \\
                             METIS_TAC []) \\
                rw [PROB_EMPTY])
            >- art [] \\
            DISJ1_TAC >> simp [Abbr ‘f’, FORALL_PROD]) \\
     POP_ORW \\
     ‘s DIFF (s DIFF t) = t’
        by (fs [EXTENSION, SUBSET_DEF] >> METIS_TAC []) >> POP_ORW \\
     irule EXTREAL_SUM_IMAGE_EQ' \\
     simp [Abbr ‘f’, Abbr ‘g’, Abbr ‘t’, FORALL_PROD, FINITE_CROSS,
           IMAGE_FINITE])
 >> Rewr
 >> ‘∃a. A' = Normal a’
      by (qunabbrev_tac ‘A'’ \\
          MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL_EXISTS \\
          (simp [FORALL_PROD, FINITE_CROSS, IMAGE_FINITE, joint_logr_normal] \\
           rw []))
 >> ‘∃c. B = Normal c’
      by (qunabbrev_tac ‘B’ \\
          MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL_EXISTS \\
          (simp [FORALL_PROD, FINITE_CROSS, joint_logr_normal] >> rw []))
 >> ‘∃h. H = Normal h’
      by (qunabbrev_tac ‘H’ \\
          MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL_EXISTS >> rw [] \\
          Q.ISPECL_THEN [‘p’, ‘X’, ‘x’] MP_TAC distribution_normal \\
          rw [] >> rw [extreal_logr_def, extreal_mul_def])
 >> rw [extreal_sub_def, extreal_ainv_def, extreal_11]
 >> REAL_ARITH_TAC
QED

(* ************************************************************************* *)
(* Bounds on entropy                                                         *)
(* ************************************************************************* *)

(* Written by Claude *)
Theorem finite_entropy_certainty_eq_0:
    ∀b p X. prob_space p ∧ POW (p_space p) = events p ∧
            random_variable X p
              (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
            FINITE (p_space p) ∧
            (∃x. x ∈ IMAGE X (p_space p) ∧ distribution p X {x} = 1) ⇒
            entropy b p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) X = 0
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘∀y. y ≠ x ⇒ distribution p X {y} = 0’
      by METIS_TAC [distribution_x_eq_1_imp_distribution_y_eq_0]
 >> rw [finite_entropy_reduce]
 >> Suff ‘∑ (λx. distribution p X {x} * logr b (distribution p X {x}))
                (IMAGE X (p_space p)) = 0’ >- rw [neg_0]
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
 >> rw [IMAGE_FINITE]
 >> rename1 ‘distribution p X {X z}’
 >> Cases_on ‘X z = x’
 >- (‘distribution p X {X z} = 1’ by METIS_TAC [] >> POP_ORW \\
     rw [extreal_of_num_def, extreal_logr_def, logr_1, extreal_mul_def])
 >> ‘distribution p X {X z} = 0’ by METIS_TAC [] >> POP_ORW
 >> rw [mul_lzero]
QED

(* Written by Claude *)
Theorem finite_entropy_le_card_real[local]:
    ∀b s (q :'a -> real). 1 ≤ b ∧ FINITE s ∧ ∑ q s = 1 ∧
            (∀x. x ∈ s ⇒ 0 ≤ q x ∧ q x ≤ 1) ⇒
            -∑ (λx. q x * logr b (q x)) s ≤
            logr b (&CARD (s ∩ {x | q x ≠ 0}))
Proof
    rpt STRIP_TAC
 >> ‘-∑ (λx. q x * logr b (q x)) s =
     ∑ (λx. q x * logr b (inv (q x))) s’
      by (rw [GSYM REAL_SUM_IMAGE_NEG] \\
          irule REAL_SUM_IMAGE_EQ >> rw [] \\
          Cases_on ‘q x = 0’ >- rw [] \\
          ‘0 < q x’ by METIS_TAC [REAL_LT_LE] \\
          rw [logr_inv])
 >> POP_ORW
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC ‘logr b (∑ (λx. q x * inv (q x)) s)’
 >> CONJ_TAC
 >- (Q.ISPECL_THEN [‘logr b’, ‘q’, ‘λx. inv (q x)’] MP_TAC
                     (MATCH_MP jensen_pos_concave_SIGMA
                               (ASSUME “FINITE (s :'a set)”)) \\
     rw [pos_concave_logr, REAL_LT_INV_EQ])
 >> Suff ‘∑ (λx. q x * inv (q x)) s = &CARD (s ∩ {x | q x ≠ 0})’
 >- rw [REAL_LE_REFL]
 >> ‘∑ (λx. q x * inv (q x)) s =
     ∑ (λx. q x * inv (q x)) (s ∩ {x | q x ≠ 0})’
      by (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
          irule REAL_SUM_IMAGE_INTER_ELIM >> rw [])
 >> POP_ORW
 >> ‘FINITE (s ∩ {x | q x ≠ 0})’ by rw [INTER_FINITE]
 >> ‘∑ (λx. q x * inv (q x)) (s ∩ {x | q x ≠ 0}) =
     ∑ (λx. 1) (s ∩ {x | q x ≠ 0})’
      by (irule REAL_SUM_IMAGE_EQ >> rw [REAL_MUL_RINV])
 >> POP_ORW
 >> ‘∑ (λx. (1 :real)) (s ∩ {x | q x ≠ 0}) =
     &CARD (s ∩ {x | q x ≠ 0}) * 1’
      by (irule REAL_SUM_IMAGE_FINITE_CONST >> fs [])
 >> rw []
QED

(* Written by Claude *)
Theorem finite_distribution_sum_1[local]:
    ∀p X. prob_space p ∧ POW (p_space p) = events p ∧
          random_variable X p
            (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
          FINITE (p_space p) ⇒
          ∑ (λx. distribution p X {x}) (IMAGE X (p_space p)) = 1
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘sX = IMAGE X (p_space p)’
 >> ‘FINITE sX’ by rw [Abbr ‘sX’, IMAGE_FINITE]
 >> Q.ISPECL_THEN [‘p’, ‘X’, ‘(sX,POW sX)’] MP_TAC distribution_prob_space
 >> rw [POW_SIGMA_ALGEBRA, space_def, subsets_def]
 >> Q.ISPEC_THEN ‘(sX,POW sX,distribution p X)’ MP_TAC
                  PROB_EXTREAL_SUM_IMAGE_SPACE
 >> rw [p_space_def, events_def, prob_def, IN_POW]
QED

(* Written by Claude *)
Theorem finite_entropy_le_card:
    ∀b p X. 1 ≤ b ∧ prob_space p ∧ POW (p_space p) = events p ∧
            random_variable X p
              (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
            FINITE (p_space p) ⇒
            entropy b p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) X ≤
            logr b (&CARD (IMAGE X (p_space p) ∩
                           {x | distribution p X {x} ≠ 0}))
Proof
    rw [finite_entropy_reduce]
 >> qabbrev_tac ‘sX = IMAGE X (p_space p)’
 >> ‘FINITE sX’ by rw [Abbr ‘sX’, IMAGE_FINITE]
 >> ‘∃q. ∀x. 0 ≤ q x ∧ q x ≤ 1 ∧ distribution p X {x} = Normal (q x)’
      by (Q.EXISTS_TAC ‘λx. real (distribution p X {x})’ >> rw [] \\
          Q.ISPECL_THEN [‘p’, ‘X’, ‘x’] MP_TAC distribution_normal \\
          rw [] >> rw [real_normal])
 >> ‘∑ q sX = 1’
      by (Q.ISPECL_THEN [‘p’, ‘X’] MP_TAC finite_distribution_sum_1 \\
          rw [EXTREAL_SUM_IMAGE_NORMAL, extreal_of_num_def])
 >> ‘∑ (λx. distribution p X {x} * logr b (distribution p X {x})) sX =
     Normal (∑ (λx. q x * logr b (q x)) sX)’
      by (rw [GSYM EXTREAL_SUM_IMAGE_NORMAL] \\
          irule EXTREAL_SUM_IMAGE_EQ' >>
          rw [extreal_logr_def, extreal_mul_def])
 >> POP_ORW
 >> rw [extreal_of_num_def, extreal_logr_def, extreal_ainv_def,
        extreal_le_eq, extreal_11]
 >> MATCH_MP_TAC finite_entropy_le_card_real >> rw []
QED

(* Written by Claude *)
Theorem finite_entropy_uniform_max:
    ∀b p X. prob_space p ∧ POW (p_space p) = events p ∧
            random_variable X p
              (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
            FINITE (p_space p) ∧
            (∀x y. x ∈ IMAGE X (p_space p) ∧ y ∈ IMAGE X (p_space p) ⇒
                   distribution p X {x} = distribution p X {y}) ⇒
            entropy b p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) X =
            logr b (&CARD (IMAGE X (p_space p)))
Proof
    rw [finite_entropy_reduce]
 >> qabbrev_tac ‘sX = IMAGE X (p_space p)’
 >> ‘FINITE sX’ by rw [Abbr ‘sX’, IMAGE_FINITE]
 >> ‘∃q. ∀x. 0 ≤ q x ∧ q x ≤ 1 ∧ distribution p X {x} = Normal (q x)’
      by (Q.EXISTS_TAC ‘λx. real (distribution p X {x})’ >> rw [] \\
          Q.ISPECL_THEN [‘p’, ‘X’, ‘x’] MP_TAC distribution_normal \\
          rw [] >> rw [real_normal])
 >> ‘∑ q sX = 1’
      by (Q.ISPECL_THEN [‘p’, ‘X’] MP_TAC finite_distribution_sum_1 \\
          rw [EXTREAL_SUM_IMAGE_NORMAL, extreal_of_num_def])
 >> ‘∑ (λx. distribution p X {x} * logr b (distribution p X {x})) sX =
     Normal (∑ (λx. q x * logr b (q x)) sX)’
      by (rw [GSYM EXTREAL_SUM_IMAGE_NORMAL] \\
          irule EXTREAL_SUM_IMAGE_EQ' >>
          rw [extreal_logr_def, extreal_mul_def])
 >> POP_ORW
 >> rw [extreal_of_num_def, extreal_logr_def, extreal_ainv_def, extreal_11]
 >> ‘∀x. x ∈ sX ⇒ q x = inv (&CARD sX)’
      by (rpt strip_tac \\
          Q.ISPEC_THEN ‘sX’ MP_TAC REAL_SUM_IMAGE_CONST_EQ_1_EQ_INV_CARD \\
          rw [] >> first_x_assum irule >> rw [] \\
          fs [Abbr ‘sX’] >> METIS_TAC [extreal_11])
 >> ‘sX ≠ {}’ by (CCONTR_TAC >> fs [REAL_SUM_IMAGE_THM])
 >> ‘(0 :real) < &CARD sX’ by rw [GSYM REAL_LT_NZ, CARD_EQ_0]
 >> ‘∑ (λx. q x * logr b (q x)) sX =
     ∑ (λx. inv (&CARD sX) * logr b (inv (&CARD sX))) sX’
      by (irule REAL_SUM_IMAGE_EQ >> rw [])
 >> POP_ORW
 >> Q.ISPEC_THEN ‘sX’ MP_TAC REAL_SUM_IMAGE_FINITE_CONST >> rw []
 >> pop_assum (qspecl_then [‘λx. inv (&CARD sX) * logr b (inv (&CARD sX))’,
                            ‘inv (&CARD sX) * logr b (inv (&CARD sX))’] mp_tac)
 >> rw []
 >> rw [REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NE, logr_inv]
QED
