(* ========================================================================= *)
(*   Single-Step & Multi-Step Polar Channel Recursion:                       *)
(*   Propositions 4, 5 (and Lemma 4), 6, and 7                               *)
(*   (Erdal Arıkan, 2009, arXiv:0807.3917, Section III & Appendices C-E).    *)
(*                                                                           *)
(*   Written by Gemini (Google DeepMind AI agent).                           *)
(* ========================================================================= *)

Theory channel_recursion

Ancestors
  combin arithmetic pair list rich_list pred_set real real_sigma transc
  sigma_algebra extreal_base extreal measure probability
  fundamental extreal_information
  memoryless_channel bhattacharyya capacity bdmc
  polar_encode combine_channel split_channel

Libs
  dep_rewrite realLib;

val _ = hide "W";
val _ = hide "S";
val _ = hide "K";

local
  val zero_tm = realSyntax.zero_tm
  fun has_strict_sign asl x =
    List.exists (fn a =>
      aconv a (realSyntax.mk_less (zero_tm, x)) orelse
      aconv a (realSyntax.mk_less (x, zero_tm))) asl
  fun is_real_prop tm =
    if is_conj tm then
      let val (c1, c2) = dest_conj tm in
        is_real_prop c1 andalso is_real_prop c2
      end
    else if is_disj tm then
      let val (c1, c2) = dest_disj tm in
        is_real_prop c1 andalso is_real_prop c2
      end
    else if is_neg tm then
      is_real_prop (dest_neg tm)
    else
      (realSyntax.is_leq tm orelse realSyntax.is_less tm orelse
       (is_eq tm andalso type_of (lhs tm) = realSyntax.real_ty))
      handle HOL_ERR _ => false
  fun drop_redundant_neq asl tm =
    is_neg tm andalso is_eq (dest_neg tm) andalso
    (let val (l, r) = dest_eq (dest_neg tm) in
       (aconv r zero_tm andalso has_strict_sign asl l) orelse
       (aconv l zero_tm andalso has_strict_sign asl r)
     end handle HOL_ERR _ => false)
in
  val REAL_ASM_ARITH_TAC : tactic = fn (asl, w) =>
    (realLib.REAL_ARITH_TAC ORELSE
     (REPEAT (WEAKEN_TAC (not o is_real_prop)) >>
      REPEAT (FIRST_X_ASSUM (fn th =>
        if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th else NO_TAC)) >>
      (fn (asl2, w2) =>
        (REPEAT (WEAKEN_TAC (drop_redundant_neq asl2)) >>
         realLib.REAL_ASM_ARITH_TAC) (asl2, w2)))) (asl, w)
end;

(* ------------------------------------------------------------------------- *)
(* Block 1: Shared Finite Real-Sum Helpers                                   *)
(* ------------------------------------------------------------------------- *)

(* Two-point expansion of REAL_SUM_IMAGE over UNIV(:bool).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_BOOL[local]:
  ∀f : bool -> real. REAL_SUM_IMAGE f 𝕌(:bool) = f F + f T
Proof
  gen_tac >>
  ‘𝕌(:bool) = {F; T}’ by (rw[Once EXTENSION] >> Cases_on ‘x’ >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT]
QED

(* A non-negative real sum over a finite set vanishes iff every summand vanishes.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_POS_EQ_0[local]:
  ∀s (f : α -> real).
    FINITE s ∧ (∀x. x ∈ s ⇒ 0 ≤ f x) ∧ REAL_SUM_IMAGE f s = 0 ⇒
    ∀x. x ∈ s ⇒ f x = 0
Proof
  Induct_on ‘FINITE’ >>
  rw[REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT]
  >- (‘0 ≤ REAL_SUM_IMAGE f s’ by (irule REAL_SUM_IMAGE_POS >> simp[]) >>
      ‘0 ≤ f e’ by simp[] >>
      REAL_ASM_ARITH_TAC)
  >- (‘0 ≤ REAL_SUM_IMAGE f s’ by (irule REAL_SUM_IMAGE_POS >> simp[]) >>
      ‘0 ≤ f e’ by simp[] >>
      ‘REAL_SUM_IMAGE f s = 0’ by REAL_ASM_ARITH_TAC >>
      first_x_assum irule >> simp[])
QED

(* Factorization of REAL_SUM_IMAGE of a separable product over s × t.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_CROSS_MUL[local]:
  ∀(s : α -> bool) (t : β -> bool) (f : α -> real) (g : β -> real).
    FINITE s ∧ FINITE t ⇒
    REAL_SUM_IMAGE (λz. f (FST z) * g (SND z)) (s × t) =
      REAL_SUM_IMAGE f s * REAL_SUM_IMAGE g t
Proof
  rpt strip_tac >>
  simp[GSYM REAL_SUM_IMAGE_REAL_SUM_IMAGE, REAL_SUM_IMAGE_CMUL] >>
  ‘REAL_SUM_IMAGE (λx. f x * REAL_SUM_IMAGE g t) s =
   REAL_SUM_IMAGE (λx. REAL_SUM_IMAGE g t * f x) s’
    by (irule REAL_SUM_IMAGE_EQ >> simp[REAL_MUL_COMM]) >>
  pop_assum SUBST1_TAC >>
  simp[REAL_SUM_IMAGE_CMUL, REAL_MUL_COMM]
QED

(* Equality of finite real sums under a pointwise upper bound holds iff
   equality holds at every element of the domain.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_EQ_IFF_POINTWISE_LE[local]:
  ∀(s : α -> bool) (f : α -> real) (g : α -> real).
    FINITE s ∧ (∀x. x ∈ s ⇒ f x ≤ g x) ⇒
    (REAL_SUM_IMAGE f s = REAL_SUM_IMAGE g s ⇔
     ∀x. x ∈ s ⇒ f x = g x)
Proof
  rpt strip_tac >> eq_tac >> rpt strip_tac
  >- (‘REAL_SUM_IMAGE (λy. g y - f y) s = 0’
        by (simp[REAL_SUM_IMAGE_SUB] >> REAL_ASM_ARITH_TAC) >>
      qspecl_then [‘s’, ‘λy. g y - f y’] mp_tac REAL_SUM_IMAGE_POS_EQ_0 >>
      impl_tac
      >- (simp[] >> qx_gen_tac ‘y’ >> strip_tac >>
          first_x_assum (drule_then mp_tac) >> REAL_ASM_ARITH_TAC) >>
      disch_then (drule_then mp_tac) >> simp[] >> REAL_ASM_ARITH_TAC)
  >- (irule REAL_SUM_IMAGE_EQ >> simp[])
QED

(* Non-looping real PMF bounds and sum-to-one property for simp/gvs contexts.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_real_pmf_safe[local]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    (∀x y. y ∈ mccodomain W ⇒
           0 ≤ real (mcchannel W x {y}) ∧
           real (mcchannel W x {y}) ≤ 1) ∧
    (∀x. REAL_SUM_IMAGE (λy. real (mcchannel W x {y})) (mccodomain W) = 1)
Proof
  gen_tac >> strip_tac >> drule wf_bdmc_real_pmf >> simp[]
QED

(* Targeted Normal (real ...) extraction for a single transition mass.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_mcchannel_eq_normal[local]:
  ∀(W : (bool, β) memoryless_channel) x y.
    wf_bdmc W ∧ y ∈ mccodomain W ⇒
    mcchannel W x {y} = Normal (real (mcchannel W x {y}))
Proof
  rpt strip_tac >> drule wf_bdmc_real_pmf >> simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Block 2: Strict Log-Sum Inequality, cap_term Algebra & Proposition 4      *)
(* ------------------------------------------------------------------------- *)

(* Strict exponential tangent inequality 1 + x < exp x for all x ≠ 0,
   proved algebraically via EXP_LE_X_FULL at x / 2.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem exp_lt_x_ne[local]:
  ∀x : real. x ≠ 0 ⇒ 1 + x < exp x
Proof
  rpt strip_tac >>
  Cases_on ‘1 + x ≤ 0’
  >- (mp_tac (Q.SPEC ‘x’ EXP_POS_LT) >> REAL_ASM_ARITH_TAC) >>
  ‘0 ≤ 1 + x / 2’ by REAL_ASM_ARITH_TAC >>
  mp_tac (Q.SPEC ‘x / 2’ EXP_LE_X_FULL) >> strip_tac >>
  ‘(1 + x / 2) * (1 + x / 2) ≤ exp (x / 2) * exp (x / 2)’
    by (irule REAL_LE_MUL2 >> simp[]) >>
  ‘exp (x / 2) * exp (x / 2) = exp x’
    by (‘x / 2 + x / 2 = x’ by REAL_ASM_ARITH_TAC >>
        metis_tac[EXP_ADD]) >>
  ‘0 < (x / 2) * (x / 2)’
    by (‘x / 2 < 0 ∨ 0 < x / 2’ by REAL_ASM_ARITH_TAC
        >- (‘0 < -(x / 2) * -(x / 2)’
              by (irule REAL_LT_MUL >> REAL_ASM_ARITH_TAC) >>
            fs[REAL_NEG_MUL2])
        >- (irule REAL_LT_MUL >> simp[])) >>
  ‘(1 + x / 2) * (1 + x / 2) = 1 + x + (x / 2) * (x / 2)’
    by REAL_ASM_ARITH_TAC >>
  REAL_ASM_ARITH_TAC
QED

(* Fundamental logarithm inequality ln u ≤ u - 1 on (0, +infty) with strict
   equality characterization (ln u = u - 1 ⇔ u = 1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem ln_le_sub_1_eq[local]:
  ∀u : real. 0 < u ⇒ ln u ≤ u - 1 ∧ (ln u = u - 1 ⇔ u = 1)
Proof
  gen_tac >> strip_tac >>
  ‘exp (ln u) = u’ by simp[EXP_LN] >>
  conj_tac
  >- (mp_tac (Q.SPEC ‘ln u’ EXP_LE_X_FULL) >> REAL_ASM_ARITH_TAC) >>
  EQ_TAC >> strip_tac >-
  (CCONTR_TAC >>
   ‘ln u ≠ 0’
     by (strip_tac >>
         ‘ln u = ln 1’ by simp[LN_1] >>
         metis_tac[LN_INJ, REAL_LT_01]) >>
   mp_tac (Q.SPEC ‘ln u’ exp_lt_x_ne) >> simp[] >> REAL_ASM_ARITH_TAC) >>
  simp[LN_1]
QED

(* Two-point log-sum inequality (a1 + a2) log_2 ((a1 + a2)/(s1 + s2)) ≤
   a1 log_2 (a1/s1) + a2 log_2 (a2/s2) with exact proportionality condition
   for equality (a1 * s2 = a2 * s1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem log_sum_2_real[local]:
  ∀(a1 : real) (a2 : real) (s1 : real) (s2 : real).
    0 ≤ a1 ∧ 0 ≤ a2 ∧ 0 < s1 ∧ 0 < s2 ⇒
    (a1 + a2) * logr 2 ((a1 + a2) / (s1 + s2)) ≤
      a1 * logr 2 (a1 / s1) + a2 * logr 2 (a2 / s2) ∧
    ((a1 + a2) * logr 2 ((a1 + a2) / (s1 + s2)) =
       a1 * logr 2 (a1 / s1) + a2 * logr 2 (a2 / s2) ⇔
     a1 * s2 = a2 * s1)
Proof
  rpt gen_tac >> strip_tac >>
  ‘0 < s1 + s2 ∧ s1 ≠ 0 ∧ s2 ≠ 0 ∧ s1 + s2 ≠ 0’ by REAL_ASM_ARITH_TAC >>
  Cases_on ‘a1 = 0’
  >- (Cases_on ‘a2 = 0’ >- simp[] >>
      ‘0 < a2 ∧ 0 < a2 * s1’
        by (conj_tac >- REAL_ASM_ARITH_TAC >>
            irule REAL_LT_MUL >> REAL_ASM_ARITH_TAC) >>
      ‘0 < a2 / (s1 + s2) ∧ 0 < a2 / s2’ by simp[REAL_LT_DIV] >>
      ‘a2 / (s1 + s2) < a2 / s2’
        by (simp[REAL_LT_LDIV_EQ, REAL_ADD_LDISTRIB, REAL_DIV_RMUL] >>
            irule REAL_LT_MUL >> simp[]) >>
      ‘logr 2 (a2 / (s1 + s2)) < logr 2 (a2 / s2)’
        by (qspecl_then [‘a2 / (s1 + s2)’, ‘a2 / s2’, ‘2’] mp_tac LOGR_MONO_LT >>
            simp[]) >>
      ‘a2 * logr 2 (a2 / (s1 + s2)) < a2 * logr 2 (a2 / s2)’
        by (irule REAL_LT_LMUL_IMP >> simp[]) >>
      ‘a2 * logr 2 (a2 / (s1 + s2)) ≤ a2 * logr 2 (a2 / s2) ∧
       a2 * logr 2 (a2 / (s1 + s2)) ≠ a2 * logr 2 (a2 / s2) ∧
       0 ≠ a2 * s1’
        by REAL_ASM_ARITH_TAC >>
      simp[]) >>
  Cases_on ‘a2 = 0’
  >- (‘0 < a1 ∧ 0 < a1 * s2’
        by (conj_tac >- REAL_ASM_ARITH_TAC >>
            irule REAL_LT_MUL >> REAL_ASM_ARITH_TAC) >>
      ‘0 < a1 / (s1 + s2) ∧ 0 < a1 / s1’ by simp[REAL_LT_DIV] >>
      ‘a1 / (s1 + s2) < a1 / s1’
        by (simp[REAL_LT_LDIV_EQ, REAL_ADD_LDISTRIB, REAL_DIV_RMUL] >>
            irule REAL_LT_MUL >> simp[]) >>
      ‘logr 2 (a1 / (s1 + s2)) < logr 2 (a1 / s1)’
        by (qspecl_then [‘a1 / (s1 + s2)’, ‘a1 / s1’, ‘2’] mp_tac LOGR_MONO_LT >>
            simp[]) >>
      ‘a1 * logr 2 (a1 / (s1 + s2)) < a1 * logr 2 (a1 / s1)’
        by (irule REAL_LT_LMUL_IMP >> simp[]) >>
      ‘a1 * logr 2 (a1 / (s1 + s2)) ≤ a1 * logr 2 (a1 / s1) ∧
       a1 * logr 2 (a1 / (s1 + s2)) ≠ a1 * logr 2 (a1 / s1) ∧
       a1 * s2 ≠ 0’
        by REAL_ASM_ARITH_TAC >>
      simp[]) >>
  ‘0 < a1 ∧ 0 < a2’ by REAL_ASM_ARITH_TAC >>
  qabbrev_tac ‘a = a1 + a2’ >>
  qabbrev_tac ‘s = s1 + s2’ >>
  ‘0 < a ∧ a ≠ 0 ∧ 0 < s ∧ s ≠ 0’
    by (simp[Abbr ‘a’, Abbr ‘s’] >> REAL_ASM_ARITH_TAC) >>
  qabbrev_tac ‘x1 = (a * s1) / (s * a1)’ >>
  qabbrev_tac ‘x2 = (a * s2) / (s * a2)’ >>
  ‘0 < x1 ∧ 0 < x2 ∧ 0 < a1 / s1 ∧ 0 < a2 / s2 ∧ 0 < a / s’
    by (unabbrev_all_tac >> rpt conj_tac >>
        irule REAL_LT_DIV >> conj_tac >>
        TRY (irule REAL_LT_MUL) >> REAL_ASM_ARITH_TAC) >>
  ‘(a1 / s1) * x1 = a / s ∧ (a2 / s2) * x2 = a / s’
    by (conj_tac
        >- (qspecl_then [‘a1’, ‘s1’, ‘s’, ‘a’] mp_tac
              (RealField.REAL_FIELD
                 “∀(a1 : real) s1 s a.
                    a1 ≠ 0 ∧ s1 ≠ 0 ∧ s ≠ 0 ⇒
                    (a1 / s1) * ((a * s1) / (s * a1)) = a / s”) >>
            simp[Abbr ‘x1’])
        >- (qspecl_then [‘a2’, ‘s2’, ‘s’, ‘a’] mp_tac
              (RealField.REAL_FIELD
                 “∀(a2 : real) s2 s a.
                    a2 ≠ 0 ∧ s2 ≠ 0 ∧ s ≠ 0 ⇒
                    (a2 / s2) * ((a * s2) / (s * a2)) = a / s”) >>
            simp[Abbr ‘x2’])) >>
  ‘logr 2 (a / s) = logr 2 (a1 / s1) + logr 2 x1 ∧
   logr 2 (a / s) = logr 2 (a2 / s2) + logr 2 x2’
    by (conj_tac
        >- (‘logr 2 ((a1 / s1) * x1) = logr 2 (a1 / s1) + logr 2 x1’
              by (irule logr_mul >> simp[]) >> metis_tac[])
        >- (‘logr 2 ((a2 / s2) * x2) = logr 2 (a2 / s2) + logr 2 x2’
              by (irule logr_mul >> simp[]) >> metis_tac[])) >>
  ‘a * logr 2 (a / s) - (a1 * logr 2 (a1 / s1) + a2 * logr 2 (a2 / s2)) =
   (a1 * ln x1 + a2 * ln x2) / ln 2’
    by (‘a * logr 2 (a / s) = a1 * logr 2 (a / s) + a2 * logr 2 (a / s)’
          by (qpat_assum ‘Abbrev (a = a1 + a2)’
                (fn th => CONV_TAC (LAND_CONV (LAND_CONV
                            (REWR_CONV (REWRITE_RULE [markerTheory.Abbrev_def] th))))) >>
              realLib.REAL_ARITH_TAC) >>
        pop_assum SUBST1_TAC >>
        ‘a1 * logr 2 (a / s) = a1 * (logr 2 (a1 / s1) + logr 2 x1) ∧
         a2 * logr 2 (a / s) = a2 * (logr 2 (a2 / s2) + logr 2 x2)’
          by (conj_tac
              >- (qpat_x_assum ‘logr 2 (a / s) = logr 2 (a1 / s1) + logr 2 x1’
                    (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
                  REFL_TAC)
              >- (qpat_x_assum ‘logr 2 (a / s) = logr 2 (a2 / s2) + logr 2 x2’
                    (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
                  REFL_TAC)) >>
        ntac 2 (pop_assum SUBST1_TAC) >>
        ‘(a1 * (logr 2 (a1 / s1) + logr 2 x1) +
          a2 * (logr 2 (a2 / s2) + logr 2 x2)) -
         (a1 * logr 2 (a1 / s1) + a2 * logr 2 (a2 / s2)) =
         a1 * logr 2 x1 + a2 * logr 2 x2’
          by realLib.REAL_ARITH_TAC >>
        pop_assum SUBST1_TAC >>
        simp[logr_def, real_div] >> realLib.REAL_ARITH_TAC) >>
  ‘a1 * (x1 - 1) + a2 * (x2 - 1) = 0’
    by (qspecl_then [‘a1’, ‘a2’, ‘s1’, ‘s2’] mp_tac
          (RealField.REAL_FIELD
             “∀(a1 : real) a2 s1 s2.
                a1 ≠ 0 ∧ a2 ≠ 0 ∧ s1 + s2 ≠ 0 ⇒
                a1 * (((a1 + a2) * s1) / ((s1 + s2) * a1) - 1) +
                a2 * (((a1 + a2) * s2) / ((s1 + s2) * a2) - 1) = 0”) >>
        simp[Abbr ‘x1’, Abbr ‘x2’, Abbr ‘a’, Abbr ‘s’]) >>
  ‘0 < ln (2 : real) ∧ ln (2 : real) ≠ 0 ∧ 0 < inv (ln (2 : real))’
    by (‘0 < ln (2 : real)’ by (irule LN_POS_LT >> simp[]) >>
        simp[REAL_LT_INV_EQ] >> REAL_ASM_ARITH_TAC) >>
  qspec_then ‘x1’ mp_tac ln_le_sub_1_eq >> impl_tac >- simp[] >> strip_tac >>
  qspec_then ‘x2’ mp_tac ln_le_sub_1_eq >> impl_tac >- simp[] >> strip_tac >>
  ‘a1 * ln x1 ≤ a1 * (x1 - 1) ∧ a2 * ln x2 ≤ a2 * (x2 - 1)’
    by (conj_tac >> irule REAL_LE_LMUL_IMP >> simp[] >> REAL_ASM_ARITH_TAC) >>
  ‘a1 * ln x1 + a2 * ln x2 ≤ 0’ by REAL_ASM_ARITH_TAC >>
  conj_tac
  >- (‘(a1 * ln x1 + a2 * ln x2) / ln 2 ≤ 0’
        by (simp[real_div] >>
            ‘0 ≤ -(a1 * ln x1 + a2 * ln x2) * inv (ln 2)’
              by (irule REAL_LE_MUL >> REAL_ASM_ARITH_TAC) >>
            REAL_ASM_ARITH_TAC) >>
      REAL_ASM_ARITH_TAC)
  >- (‘a * logr 2 (a / s) = a1 * logr 2 (a1 / s1) + a2 * logr 2 (a2 / s2) ⇔
       (a1 * ln x1 + a2 * ln x2) / ln 2 = 0’
        by REAL_ASM_ARITH_TAC >>
      pop_assum SUBST1_TAC >>
      simp[real_div, REAL_ENTIRE, REAL_INV_EQ_0] >>
      ‘a1 * ln x1 + a2 * ln x2 = 0 ⇔
       a1 * ln x1 = a1 * (x1 - 1) ∧ a2 * ln x2 = a2 * (x2 - 1)’
        by REAL_ASM_ARITH_TAC >>
      pop_assum SUBST1_TAC >>
      simp[REAL_EQ_LMUL] >>
      ‘x1 = 1 ∧ x2 = 1 ⇔ a1 * s2 = a2 * s1’
        by (‘0 < s * a1 ∧ 0 < s * a2’ by (conj_tac >> irule REAL_LT_MUL >> simp[]) >>
            simp[Abbr ‘x1’, Abbr ‘x2’, REAL_EQ_LDIV_EQ, Abbr ‘a’, Abbr ‘s’] >>
            realLib.REAL_ARITH_TAC) >>
      simp[])
QED

(* Special values and symmetry of cap_term on non-negative arguments.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem cap_term_special[local]:
  (cap_term 0 0 = 0) ∧
  (∀a b : real. cap_term a b = cap_term b a) ∧
  (∀a : real. 0 ≤ a ⇒ cap_term a a = 0) ∧
  (∀a : real. 0 ≤ a ⇒ cap_term a 0 = (1 / 2) * a) ∧
  (∀b : real. 0 ≤ b ⇒ cap_term 0 b = (1 / 2) * b)
Proof
  rpt conj_tac
  >- simp[cap_term_def]
  >- (rpt gen_tac >>
      ‘(1 / 2 : real) * a + (1 / 2) * b = (1 / 2) * b + (1 / 2) * a’
        by realLib.REAL_ARITH_TAC >>
      PURE_REWRITE_TAC[cap_term_def] >> pop_assum SUBST1_TAC >>
      realLib.REAL_ARITH_TAC)
  >- (gen_tac >> strip_tac >> Cases_on ‘a = 0’ >- simp[cap_term_def] >>
      ‘(1 / 2 : real) * a + (1 / 2) * a = a’ by realLib.REAL_ARITH_TAC >>
      PURE_REWRITE_TAC[cap_term_def] >> pop_assum SUBST1_TAC >>
      simp[REAL_DIV_REFL, logr_1])
  >- (gen_tac >> strip_tac >> Cases_on ‘a = 0’ >- simp[cap_term_def] >>
      ‘0 < (1 / 2 : real) * a’ by REAL_ASM_ARITH_TAC >>
      ‘a / ((1 / 2 : real) * a) = 2’
        by (simp[REAL_EQ_LDIV_EQ] >> realLib.REAL_ARITH_TAC) >>
      PURE_REWRITE_TAC[cap_term_def] >> simp[])
  >- (gen_tac >> strip_tac >> Cases_on ‘b = 0’ >- simp[cap_term_def] >>
      ‘0 < (1 / 2 : real) * b’ by REAL_ASM_ARITH_TAC >>
      ‘b / ((1 / 2 : real) * b) = 2’
        by (simp[REAL_EQ_LDIV_EQ] >> realLib.REAL_ARITH_TAC) >>
      PURE_REWRITE_TAC[cap_term_def] >> simp[])
QED

(* Positive 1-homogeneity of cap_term: cap_term (c * a) (c * b) = c * cap_term a b.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem cap_term_cmul[local]:
  ∀(c : real) (a : real) (b : real).
    0 ≤ c ∧ 0 ≤ a ∧ 0 ≤ b ⇒
    cap_term (c * a) (c * b) = c * cap_term a b
Proof
  rpt strip_tac >>
  Cases_on ‘c = 0’ >- simp[cap_term_def] >>
  Cases_on ‘a = 0 ∧ b = 0’ >- simp[cap_term_def] >>
  qabbrev_tac ‘m = (1 / 2 : real) * a + (1 / 2) * b’ >>
  ‘m ≠ 0’ by (simp[Abbr ‘m’] >> REAL_ASM_ARITH_TAC) >>
  ‘(c * a) / (c * m) = a / m ∧ (c * b) / (c * m) = b / m’
    by (conj_tac
        >- (qspecl_then [‘c’, ‘m’, ‘a’] mp_tac
              (RealField.REAL_FIELD
                 “∀(c : real) m x. c ≠ 0 ∧ m ≠ 0 ⇒ (c * x) / (c * m) = x / m”) >>
            simp[])
        >- (qspecl_then [‘c’, ‘m’, ‘b’] mp_tac
              (RealField.REAL_FIELD
                 “∀(c : real) m x. c ≠ 0 ∧ m ≠ 0 ⇒ (c * x) / (c * m) = x / m”) >>
            simp[])) >>
  ‘(1 / 2 : real) * (c * a) + (1 / 2) * (c * b) = c * m ∧
   (1 / 2 : real) * a + (1 / 2) * b = m’
    by (simp[Abbr ‘m’] >> realLib.REAL_ARITH_TAC) >>
  PURE_REWRITE_TAC[cap_term_def] >>
  ntac 4 (pop_assum SUBST1_TAC) >>
  realLib.REAL_ARITH_TAC
QED

(* Subadditivity of cap_term on [0, +infty)^2 with exact determinant equality
   condition (u1 * v2 = u2 * v1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem cap_term_subadd[local]:
  ∀(u1 : real) (v1 : real) (u2 : real) (v2 : real).
    0 ≤ u1 ∧ 0 ≤ v1 ∧ 0 ≤ u2 ∧ 0 ≤ v2 ⇒
    cap_term (u1 + u2) (v1 + v2) ≤ cap_term u1 v1 + cap_term u2 v2 ∧
    (cap_term (u1 + u2) (v1 + v2) = cap_term u1 v1 + cap_term u2 v2 ⇔
     u1 * v2 = u2 * v1)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on ‘u1 = 0 ∧ v1 = 0’ >- simp[cap_term_special] >>
  Cases_on ‘u2 = 0 ∧ v2 = 0’ >- simp[cap_term_special] >>
  qabbrev_tac ‘s1 = (1 / 2 : real) * u1 + (1 / 2) * v1’ >>
  qabbrev_tac ‘s2 = (1 / 2 : real) * u2 + (1 / 2) * v2’ >>
  ‘0 < s1 ∧ 0 < s2’ by (simp[Abbr ‘s1’, Abbr ‘s2’] >> REAL_ASM_ARITH_TAC) >>
  qspecl_then [‘u1’, ‘u2’, ‘s1’, ‘s2’] mp_tac log_sum_2_real >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [‘v1’, ‘v2’, ‘s1’, ‘s2’] mp_tac log_sum_2_real >>
  impl_tac >- simp[] >> strip_tac >>
  ‘(1 / 2 : real) * (u1 + u2) + (1 / 2) * (v1 + v2) = s1 + s2 ∧
   (1 / 2 : real) * u1 + (1 / 2) * v1 = s1 ∧
   (1 / 2 : real) * u2 + (1 / 2) * v2 = s2’
    by (simp[Abbr ‘s1’, Abbr ‘s2’] >> realLib.REAL_ARITH_TAC) >>
  pop_assum (fn th3 =>
    pop_assum (fn th2 =>
      pop_assum (fn th1 =>
        conj_tac
        >- (PURE_REWRITE_TAC[cap_term_def, th1, th2, th3] >> REAL_ASM_ARITH_TAC)
        >- (‘cap_term (u1 + u2) (v1 + v2) = cap_term u1 v1 + cap_term u2 v2 ⇔
             (u1 + u2) * logr 2 ((u1 + u2) / (s1 + s2)) =
               u1 * logr 2 (u1 / s1) + u2 * logr 2 (u2 / s2) ∧
             (v1 + v2) * logr 2 ((v1 + v2) / (s1 + s2)) =
               v1 * logr 2 (v1 / s1) + v2 * logr 2 (v2 / s2)’
              by (PURE_REWRITE_TAC[cap_term_def, th1, th2, th3] >>
                  REAL_ASM_ARITH_TAC) >>
            pop_assum SUBST1_TAC >>
            simp[] >>
            simp[Abbr ‘s1’, Abbr ‘s2’] >>
            realLib.REAL_ARITH_TAC))))
QED

(* Pointwise W_plus >= W inequality & Arıkan Eq. (87) equality condition
   b * g * (a - d) = 0 for 4 non-negative transition masses.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_cap_term_plus_ge[local]:
  ∀(a : real) (d : real) (b : real) (g : real).
    0 ≤ a ∧ 0 ≤ d ∧ 0 ≤ b ∧ 0 ≤ g ⇒
    ((1 / 2) * a + (1 / 2) * d) * cap_term b g ≤
      cap_term ((1 / 2) * (a * b)) ((1 / 2) * (d * g)) +
      cap_term ((1 / 2) * (d * b)) ((1 / 2) * (a * g)) ∧
    (((1 / 2) * a + (1 / 2) * d) * cap_term b g =
       cap_term ((1 / 2) * (a * b)) ((1 / 2) * (d * g)) +
       cap_term ((1 / 2) * (d * b)) ((1 / 2) * (a * g)) ⇔
     b * g * (a - d) = 0)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac ‘m1 = (1 / 2 : real) * a + (1 / 2) * d’ >>
  ‘0 ≤ m1’ by (simp[Abbr ‘m1’] >> REAL_ASM_ARITH_TAC) >>
  ‘m1 * cap_term b g = cap_term (m1 * b) (m1 * g)’
    by (CONV_TAC SYM_CONV >> irule cap_term_cmul >> simp[]) >>
  ‘m1 * b = (1 / 2) * (a * b) + (1 / 2) * (d * b) ∧
   m1 * g = (1 / 2) * (d * g) + (1 / 2) * (a * g)’
    by (simp[Abbr ‘m1’] >> realLib.REAL_ARITH_TAC) >>
  ‘0 ≤ (1 / 2) * (a * b) ∧ 0 ≤ (1 / 2) * (d * g) ∧
   0 ≤ (1 / 2) * (d * b) ∧ 0 ≤ (1 / 2) * (a * g)’
    by (rpt conj_tac >> irule REAL_LE_MUL >> simp[REAL_LE_MUL] >>
        realLib.REAL_ARITH_TAC) >>
  qspecl_then [‘(1 / 2) * (a * b)’, ‘(1 / 2) * (d * g)’,
               ‘(1 / 2) * (d * b)’, ‘(1 / 2) * (a * g)’]
    mp_tac cap_term_subadd >>
  impl_tac >- simp[] >> strip_tac >>
  ‘((1 / 2 : real) * (a * b)) * ((1 / 2) * (a * g)) =
   ((1 / 2) * (d * b)) * ((1 / 2) * (d * g)) ⇔
   b * g * (a - d) = 0’
    by (‘((1 / 2 : real) * (a * b)) * ((1 / 2) * (a * g)) =
         ((1 / 2) * (d * b)) * ((1 / 2) * (d * g)) ⇔
         ((1 / 2 : real) * (a * b)) * ((1 / 2) * (a * g)) -
         ((1 / 2) * (d * b)) * ((1 / 2) * (d * g)) = 0’
          by realLib.REAL_ARITH_TAC >>
        pop_assum SUBST1_TAC >>
        ‘((1 / 2 : real) * (a * b)) * ((1 / 2) * (a * g)) -
         ((1 / 2) * (d * b)) * ((1 / 2) * (d * g)) =
         (1 / 4) * (b * g * ((a + d) * (a - d)))’
          by realLib.REAL_ARITH_TAC >>
        pop_assum SUBST1_TAC >>
        ‘(1 / 4 : real) ≠ 0’ by realLib.REAL_ARITH_TAC >>
        simp[REAL_ENTIRE, REAL_SUB_0] >>
        ‘a + d = 0 ⇒ a = d’ by REAL_ASM_ARITH_TAC >>
        metis_tac[]) >>
  gvs[]
QED

(* Product-logarithm splitting identity for non-negative x, y (handling zeros).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mul_logr_split[local]:
  ∀(x : real) (y : real) (m1 : real) (m2 : real).
    0 ≤ x ∧ 0 ≤ y ∧ 0 < m1 ∧ 0 < m2 ⇒
    (x * y) * logr 2 ((x * y) / (m1 * m2)) =
      y * (x * logr 2 (x / m1)) + x * (y * logr 2 (y / m2))
Proof
  rpt strip_tac >>
  Cases_on ‘x = 0’ >- simp[] >>
  Cases_on ‘y = 0’ >- simp[] >>
  ‘0 < x ∧ 0 < y’ by REAL_ASM_ARITH_TAC >>
  ‘0 < x / m1 ∧ 0 < y / m2’ by simp[REAL_LT_DIV] >>
  ‘(x * y) / (m1 * m2) = (x / m1) * (y / m2)’
    by (simp[real_div, REAL_INV_MUL'] >> realLib.REAL_ARITH_TAC) >>
  pop_assum SUBST1_TAC >>
  simp[logr_mul] >>
  realLib.REAL_ARITH_TAC
QED

(* Telescoping chain-rule helper combining one half of W_minus with one branch of W_plus.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem cap_term_split_pair[local]:
  ∀(u : real) (v : real) (M : real).
    0 ≤ u ∧ 0 ≤ v ∧ 0 < M ⇒
    (1 / 2) * ((1 / 2) * (u + v)) * logr 2 (((1 / 2) * (u + v)) / M) +
    cap_term ((1 / 2) * u) ((1 / 2) * v) =
      (1 / 4) * (u * logr 2 (u / M)) + (1 / 4) * (v * logr 2 (v / M))
Proof
  rpt strip_tac >>
  ‘M ≠ 0’ by REAL_ASM_ARITH_TAC >>
  Cases_on ‘u = 0’
  >- (Cases_on ‘v = 0’ >- simp[cap_term_special] >>
      qpat_x_assum ‘u = 0’ SUBST1_TAC >>
      ‘0 < v ∧ 0 < ((1 / 2) * v) / M’
        by (conj_tac >- REAL_ASM_ARITH_TAC >>
            irule REAL_LT_DIV >> REAL_ASM_ARITH_TAC) >>
      ‘logr 2 (v / M) = logr 2 (((1 / 2) * v) / M) + 1’
        by (‘v / M = (((1 / 2) * v) / M) * 2’
              by (simp[real_div] >> realLib.REAL_ARITH_TAC) >>
            pop_assum SUBST1_TAC >>
            qspecl_then [‘2’, ‘((1 / 2) * v) / M’, ‘2’] mp_tac logr_mul >>
            simp[]) >>
      ‘cap_term ((1 / 2) * 0) ((1 / 2) * v) = (1 / 4) * v’
        by (‘(1 / 2 : real) * 0 = 0 ∧ 0 ≤ (1 / 2 : real) * v’
              by REAL_ASM_ARITH_TAC >>
            drule (cj 5 cap_term_special) >> simp[] >> REAL_ASM_ARITH_TAC) >>
      ‘(1 / 2 : real) * (0 + v) = (1 / 2) * v ∧ (1 / 4 : real) * 0 = 0’
        by realLib.REAL_ARITH_TAC >>
      ntac 4 (pop_assum SUBST1_TAC) >>
      realLib.REAL_ARITH_TAC) >>
  Cases_on ‘v = 0’
  >- (qpat_x_assum ‘v = 0’ SUBST1_TAC >>
      ‘0 < u ∧ 0 < ((1 / 2) * u) / M’
        by (conj_tac >- REAL_ASM_ARITH_TAC >>
            irule REAL_LT_DIV >> REAL_ASM_ARITH_TAC) >>
      ‘logr 2 (u / M) = logr 2 (((1 / 2) * u) / M) + 1’
        by (‘u / M = (((1 / 2) * u) / M) * 2’
              by (simp[real_div] >> realLib.REAL_ARITH_TAC) >>
            pop_assum SUBST1_TAC >>
            qspecl_then [‘2’, ‘((1 / 2) * u) / M’, ‘2’] mp_tac logr_mul >>
            simp[]) >>
      ‘cap_term ((1 / 2) * u) ((1 / 2) * 0) = (1 / 4) * u’
        by (‘(1 / 2 : real) * 0 = 0 ∧ 0 ≤ (1 / 2 : real) * u’
              by REAL_ASM_ARITH_TAC >>
            drule (cj 4 cap_term_special) >> simp[] >> REAL_ASM_ARITH_TAC) >>
      ‘(1 / 2 : real) * (u + 0) = (1 / 2) * u ∧ (1 / 4 : real) * 0 = 0’
        by realLib.REAL_ARITH_TAC >>
      ntac 4 (pop_assum SUBST1_TAC) >>
      realLib.REAL_ARITH_TAC) >>
  ‘0 < u ∧ 0 < v ∧ 0 < u + v’ by REAL_ASM_ARITH_TAC >>
  qabbrev_tac ‘A = (1 / 2 : real) * (u + v)’ >>
  ‘0 < A ∧ A ≠ 0 ∧ 0 < (1 / 2) * A ∧ (1 / 2) * A ≠ 0’
    by (simp[Abbr ‘A’] >> REAL_ASM_ARITH_TAC) >>
  ‘0 < A / M ∧ 0 < ((1 / 2) * u) / ((1 / 2) * A) ∧
   0 < ((1 / 2) * v) / ((1 / 2) * A)’
    by (rpt conj_tac >> irule REAL_LT_DIV >> REAL_ASM_ARITH_TAC) >>
  ‘logr 2 ((A / M) * (((1 / 2) * u) / ((1 / 2) * A))) =
     logr 2 (A / M) + logr 2 (((1 / 2) * u) / ((1 / 2) * A)) ∧
   logr 2 ((A / M) * (((1 / 2) * v) / ((1 / 2) * A))) =
     logr 2 (A / M) + logr 2 (((1 / 2) * v) / ((1 / 2) * A))’
    by (conj_tac >> irule logr_mul >> simp[]) >>
  ‘u / M = (A / M) * (((1 / 2) * u) / ((1 / 2) * A)) ∧
   v / M = (A / M) * (((1 / 2) * v) / ((1 / 2) * A))’
    by (conj_tac
        >- (qspecl_then [‘A’, ‘M’, ‘u’] mp_tac
              (RealField.REAL_FIELD
                 “∀(A : real) M x.
                    A ≠ 0 ∧ M ≠ 0 ⇒
                    x / M = (A / M) * (((1 / 2) * x) / ((1 / 2) * A))”) >>
            simp[])
        >- (qspecl_then [‘A’, ‘M’, ‘v’] mp_tac
              (RealField.REAL_FIELD
                 “∀(A : real) M x.
                    A ≠ 0 ∧ M ≠ 0 ⇒
                    x / M = (A / M) * (((1 / 2) * x) / ((1 / 2) * A))”) >>
            simp[])) >>
  ‘(1 / 2 : real) * ((1 / 2) * u) + (1 / 2) * ((1 / 2) * v) = (1 / 2) * A’
    by (simp[Abbr ‘A’] >> realLib.REAL_ARITH_TAC) >>
  ‘(1 / 2 : real) * (u + v) = A’ by simp[Abbr ‘A’] >>
  pop_assum SUBST1_TAC >>
  PURE_REWRITE_TAC[cap_term_def] >>
  ntac 5 (pop_assum SUBST1_TAC) >>
  ‘(1 / 2 : real) * A = (1 / 4) * u + (1 / 4) * v’
    by (simp[Abbr ‘A’] >> realLib.REAL_ARITH_TAC) >>
  pop_assum SUBST1_TAC >>
  realLib.REAL_ARITH_TAC
QED

(* Pointwise 4-mass rate conservation identity underlying Arıkan Eq. (24).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_cap_term_conservation[local]:
  ∀(a : real) (d : real) (b : real) (g : real).
    0 ≤ a ∧ 0 ≤ d ∧ 0 ≤ b ∧ 0 ≤ g ⇒
    cap_term ((1 / 2) * (a * b + d * g)) ((1 / 2) * (d * b + a * g)) +
    (cap_term ((1 / 2) * (a * b)) ((1 / 2) * (d * g)) +
     cap_term ((1 / 2) * (d * b)) ((1 / 2) * (a * g))) =
    ((1 / 2) * b + (1 / 2) * g) * cap_term a d +
    ((1 / 2) * a + (1 / 2) * d) * cap_term b g
Proof
  rpt strip_tac >>
  Cases_on ‘a = 0 ∧ d = 0’ >- simp[cap_term_special] >>
  Cases_on ‘b = 0 ∧ g = 0’ >- simp[cap_term_special] >>
  qabbrev_tac ‘m1 = (1 / 2 : real) * a + (1 / 2) * d’ >>
  qabbrev_tac ‘m2 = (1 / 2 : real) * b + (1 / 2) * g’ >>
  ‘0 < m1 ∧ 0 < m2’
    by (simp[Abbr ‘m1’, Abbr ‘m2’] >> REAL_ASM_ARITH_TAC) >>
  ‘0 < m1 * m2’ by (irule REAL_LT_MUL >> simp[]) >>
  ‘(1 / 2 : real) * ((1 / 2) * (a * b + d * g)) +
   (1 / 2) * ((1 / 2) * (d * b + a * g)) = m1 * m2’
    by (simp[Abbr ‘m1’, Abbr ‘m2’] >> realLib.REAL_ARITH_TAC) >>
  ‘0 ≤ a * b ∧ 0 ≤ d * g ∧ 0 ≤ d * b ∧ 0 ≤ a * g’
    by simp[REAL_LE_MUL] >>
  qspecl_then [‘a * b’, ‘d * g’, ‘m1 * m2’] mp_tac cap_term_split_pair >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [‘d * b’, ‘a * g’, ‘m1 * m2’] mp_tac cap_term_split_pair >>
  impl_tac >- simp[] >> strip_tac >>
  ‘cap_term ((1 / 2) * (a * b + d * g)) ((1 / 2) * (d * b + a * g)) +
   (cap_term ((1 / 2) * (a * b)) ((1 / 2) * (d * g)) +
    cap_term ((1 / 2) * (d * b)) ((1 / 2) * (a * g))) =
   (1 / 4) * ((a * b) * logr 2 ((a * b) / (m1 * m2))) +
   (1 / 4) * ((d * g) * logr 2 ((d * g) / (m1 * m2))) +
   (1 / 4) * ((d * b) * logr 2 ((d * b) / (m1 * m2))) +
   (1 / 4) * ((a * g) * logr 2 ((a * g) / (m1 * m2)))’
    by (CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV cap_term_def))) >>
        qpat_x_assum ‘_ = m1 * m2’ SUBST1_TAC >>
        qpat_x_assum ‘_ + cap_term ((1 / 2) * (d * b)) _ = _’ mp_tac >>
        qpat_x_assum ‘_ + cap_term ((1 / 2) * (a * b)) _ = _’ mp_tac >>
        realLib.REAL_ARITH_TAC) >>
  pop_assum SUBST1_TAC >>
  ‘(a * b) * logr 2 ((a * b) / (m1 * m2)) =
     b * (a * logr 2 (a / m1)) + a * (b * logr 2 (b / m2)) ∧
   (d * g) * logr 2 ((d * g) / (m1 * m2)) =
     g * (d * logr 2 (d / m1)) + d * (g * logr 2 (g / m2)) ∧
   (d * b) * logr 2 ((d * b) / (m1 * m2)) =
     b * (d * logr 2 (d / m1)) + d * (b * logr 2 (b / m2)) ∧
   (a * g) * logr 2 ((a * g) / (m1 * m2)) =
     g * (a * logr 2 (a / m1)) + a * (g * logr 2 (g / m2))’
    by (rpt conj_tac >> irule mul_logr_split >> simp[]) >>
  ntac 4 (pop_assum SUBST1_TAC) >>
  PURE_REWRITE_TAC[cap_term_def] >>
  ‘(1 / 2 : real) * a + (1 / 2) * d = m1 ∧
   (1 / 2 : real) * b + (1 / 2) * g = m2’
    by simp[Abbr ‘m1’, Abbr ‘m2’] >>
  ntac 2 (pop_assum SUBST1_TAC) >>
  qpat_x_assum ‘Abbrev (m2 = _)’
    (fn th => CONV_TAC (RAND_CONV (LAND_CONV (LAND_CONV
                (REWR_CONV (REWRITE_RULE [markerTheory.Abbrev_def] th)))))) >>
  qpat_x_assum ‘Abbrev (m1 = _)’
    (fn th => CONV_TAC (RAND_CONV (RAND_CONV (LAND_CONV
                (REWR_CONV (REWRITE_RULE [markerTheory.Abbrev_def] th)))))) >>
  realLib.REAL_ARITH_TAC
QED

(* Real-sum representations of I(W), I(W_minus), and I(W_plus) over
   mccodomain W × mccodomain W under single_step_polar W W_minus W_plus.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem single_step_polar_cap_sums[local]:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    (let Y = mccodomain W;
         p0 = λy. real (mcchannel W F {y});
         p1 = λy. real (mcchannel W T {y}) in
       symmetric_capacity W =
         Normal (REAL_SUM_IMAGE (λy. cap_term (p0 y) (p1 y)) Y) ∧
       symmetric_capacity W_minus =
         Normal (REAL_SUM_IMAGE
                   (λz. cap_term
                          ((1 / 2) * (p0 (FST z) * p0 (SND z) +
                                      p1 (FST z) * p1 (SND z)))
                          ((1 / 2) * (p1 (FST z) * p0 (SND z) +
                                      p0 (FST z) * p1 (SND z))))
                   (Y × Y)) ∧
       symmetric_capacity W_plus =
         Normal (REAL_SUM_IMAGE
                   (λz. cap_term
                          ((1 / 2) * (p0 (FST z) * p0 (SND z)))
                          ((1 / 2) * (p1 (FST z) * p1 (SND z))) +
                        cap_term
                          ((1 / 2) * (p1 (FST z) * p0 (SND z)))
                          ((1 / 2) * (p0 (FST z) * p1 (SND z))))
                   (Y × Y)))
Proof
  rw[single_step_polar_def, LET_THM]
  >- (irule symmetric_capacity_real_sum >> simp[])
  >- (qpat_x_assum ‘wf_bdmc W_minus’
        (SUBST1_TAC o MATCH_MP symmetric_capacity_real_sum) >>
      AP_TERM_TAC >>
      ‘FINITE (mccodomain W × mccodomain W)’ by (fs[wf_bdmc_def, FINITE_CROSS]) >>
      qspecl_then [‘mccodomain W × mccodomain W’, ‘mccodomain W_minus’, ‘f’]
        mp_tac REAL_SUM_IMAGE_BIJ >>
      simp[] >> disch_then (fn th => ONCE_REWRITE_TAC[th]) >>
      irule REAL_SUM_IMAGE_EQ >> simp[FORALL_PROD, o_DEF] >>
      qx_genl_tac [‘y1’, ‘y2’] >> strip_tac >>
      qabbrev_tac ‘a = real (mcchannel W F {y1})’ >>
      qabbrev_tac ‘d = real (mcchannel W T {y1})’ >>
      qabbrev_tac ‘b = real (mcchannel W F {y2})’ >>
      qabbrev_tac ‘g = real (mcchannel W T {y2})’ >>
      ‘mcchannel W F {y1} = Normal a ∧
       mcchannel W T {y1} = Normal d ∧
       mcchannel W F {y2} = Normal b ∧
       mcchannel W T {y2} = Normal g’
        by (simp[Abbr ‘a’, Abbr ‘d’, Abbr ‘b’, Abbr ‘g’] >>
            rpt conj_tac >> irule wf_bdmc_mcchannel_eq_normal >> simp[]) >>
      qpat_x_assum ‘∀y1 y2 u1. _ ⇒ mcchannel W_minus _ _ = _’
        (fn th =>
          mp_tac (Q.SPECL [‘y1’, ‘y2’, ‘F’] th) >>
          mp_tac (Q.SPECL [‘y1’, ‘y2’, ‘T’] th)) >>
      simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq,
           extreal_add_eq, real_normal] >>
      ntac 2 (disch_then SUBST1_TAC) >>
      simp[real_normal] >>
      BINOP_TAC >> realLib.REAL_ARITH_TAC)
  >- (qpat_x_assum ‘wf_bdmc W_plus’
        (SUBST1_TAC o MATCH_MP symmetric_capacity_real_sum) >>
      AP_TERM_TAC >>
      ‘FINITE (mccodomain W) ∧ FINITE (mccodomain W_minus) ∧ FINITE 𝕌(:bool)’
        by (fs[wf_bdmc_def] >> simp[UNIV_BOOL]) >>
      ‘FINITE (mccodomain W × mccodomain W) ∧
       FINITE (mccodomain W_minus × 𝕌(:bool))’
        by simp[FINITE_CROSS] >>
      qabbrev_tac ‘gp = λyp. cap_term (real (mcchannel W_plus F {yp}))
                                      (real (mcchannel W_plus T {yp}))’ >>
      qspecl_then [‘mccodomain W_minus × 𝕌(:bool)’, ‘mccodomain W_plus’, ‘h’]
        mp_tac REAL_SUM_IMAGE_BIJ >>
      simp[] >> disch_then (fn th => ONCE_REWRITE_TAC[th]) >>
      ‘gp ∘ h = λp. gp (h (FST p, SND p))’
        by simp[FUN_EQ_THM, FORALL_PROD, o_DEF] >>
      pop_assum SUBST1_TAC >>
      simp[SimpLHS, GSYM REAL_SUM_IMAGE_REAL_SUM_IMAGE] >>
      qspecl_then [‘mccodomain W × mccodomain W’, ‘mccodomain W_minus’, ‘f’]
        mp_tac REAL_SUM_IMAGE_BIJ >>
      simp[] >> disch_then (fn th => ONCE_REWRITE_TAC[th]) >>
      irule REAL_SUM_IMAGE_EQ >>
      simp[FORALL_PROD, o_DEF, REAL_SUM_IMAGE_BOOL,
           REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT] >>
      qx_genl_tac [‘y1’, ‘y2’] >> strip_tac >>
      qabbrev_tac ‘a = real (mcchannel W F {y1})’ >>
      qabbrev_tac ‘d = real (mcchannel W T {y1})’ >>
      qabbrev_tac ‘b = real (mcchannel W F {y2})’ >>
      qabbrev_tac ‘g = real (mcchannel W T {y2})’ >>
      ‘mcchannel W F {y1} = Normal a ∧
       mcchannel W T {y1} = Normal d ∧
       mcchannel W F {y2} = Normal b ∧
       mcchannel W T {y2} = Normal g’
        by (simp[Abbr ‘a’, Abbr ‘d’, Abbr ‘b’, Abbr ‘g’] >>
            rpt conj_tac >> irule wf_bdmc_mcchannel_eq_normal >> simp[]) >>
      qpat_x_assum ‘∀y1 y2 u1 u2. _ ⇒ mcchannel W_plus _ _ = _’
        (fn th =>
          mp_tac (Q.SPECL [‘y1’, ‘y2’, ‘F’, ‘F’] th) >>
          mp_tac (Q.SPECL [‘y1’, ‘y2’, ‘F’, ‘T’] th) >>
          mp_tac (Q.SPECL [‘y1’, ‘y2’, ‘T’, ‘F’] th) >>
          mp_tac (Q.SPECL [‘y1’, ‘y2’, ‘T’, ‘T’] th)) >>
      simp[Abbr ‘gp’, extreal_of_num_def, extreal_div_eq, extreal_mul_eq] >>
      ntac 4 (disch_then SUBST1_TAC) >>
      simp[real_normal] >>
      realLib.REAL_ARITH_TAC)
QED

(* Proposition 4 (Erdal Arıkan, 2009, arXiv:0807.3917, Section III-A Eqs. (24)-(25)
   & Appendix C Eqs. (86)-(87)): Single-step symmetric capacity conservation,
   ordering, [0, 1] bounds, and extremal fixed-point characterization.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_4:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    symmetric_capacity W_minus + symmetric_capacity W_plus =
      2 * symmetric_capacity W ∧
    0 ≤ symmetric_capacity W_minus ∧
    symmetric_capacity W_minus ≤ symmetric_capacity W ∧
    symmetric_capacity W ≤ symmetric_capacity W_plus ∧
    symmetric_capacity W_minus ≤ symmetric_capacity W_plus ∧
    symmetric_capacity W_plus ≤ 1 ∧
    (symmetric_capacity W_minus = symmetric_capacity W_plus ⇔
       symmetric_capacity W = 0 ∨ symmetric_capacity W = 1)
Proof
  rpt gen_tac >> strip_tac >>
  ‘wf_bdmc W ∧ wf_bdmc W_minus ∧ wf_bdmc W_plus’
    by fs[single_step_polar_def] >>
  ‘FINITE (mccodomain W) ∧ FINITE (mccodomain W × mccodomain W)’
    by (fs[wf_bdmc_def, FINITE_CROSS]) >>
  qpat_assum ‘wf_bdmc W’ (strip_assume_tac o MATCH_MP wf_bdmc_real_pmf_safe) >>
  qabbrev_tac ‘Y = mccodomain W’ >>
  qabbrev_tac ‘p0 = λy. real (mcchannel W F {y})’ >>
  qabbrev_tac ‘p1 = λy. real (mcchannel W T {y})’ >>
  qabbrev_tac ‘m = λy. (1 / 2 : real) * p0 y + (1 / 2) * p1 y’ >>
  qabbrev_tac ‘c = REAL_SUM_IMAGE (λy. cap_term (p0 y) (p1 y)) Y’ >>
  qabbrev_tac ‘fm = λz : α # α.
    cap_term ((1 / 2) * (p0 (FST z) * p0 (SND z) + p1 (FST z) * p1 (SND z)))
             ((1 / 2) * (p0 (SND z) * p1 (FST z) + p0 (FST z) * p1 (SND z)))’ >>
  qabbrev_tac ‘fp = λz : α # α.
    cap_term ((1 / 2) * (p0 (FST z) * p0 (SND z)))
             ((1 / 2) * (p1 (FST z) * p1 (SND z))) +
    cap_term ((1 / 2) * (p0 (SND z) * p1 (FST z)))
             ((1 / 2) * (p0 (FST z) * p1 (SND z)))’ >>
  qabbrev_tac ‘cm = REAL_SUM_IMAGE fm (Y × Y)’ >>
  qabbrev_tac ‘cp = REAL_SUM_IMAGE fp (Y × Y)’ >>
  ‘symmetric_capacity W = Normal c ∧
   symmetric_capacity W_minus = Normal cm ∧
   symmetric_capacity W_plus = Normal cp’
    by (drule single_step_polar_cap_sums >>
        simp[LET_THM, Abbr ‘c’, Abbr ‘cm’, Abbr ‘cp’, Abbr ‘fm’, Abbr ‘fp’,
             Abbr ‘p0’, Abbr ‘p1’, Abbr ‘Y’]) >>
  ‘0 ≤ c ∧ c ≤ 1 ∧ 0 ≤ cm ∧ cm ≤ 1 ∧ 0 ≤ cp ∧ cp ≤ 1’
    by (qpat_assum ‘wf_bdmc W’
          (mp_tac o MATCH_MP symmetric_capacity_bounds) >>
        qpat_x_assum ‘wf_bdmc W_minus’
          (mp_tac o MATCH_MP symmetric_capacity_bounds) >>
        qpat_x_assum ‘wf_bdmc W_plus’
          (mp_tac o MATCH_MP symmetric_capacity_bounds) >>
        gvs[extreal_of_num_def, extreal_le_eq]) >>
  ‘REAL_SUM_IMAGE m Y = 1’
    by (simp[Abbr ‘m’, REAL_SUM_IMAGE_ADD, REAL_SUM_IMAGE_CMUL] >>
        ‘REAL_SUM_IMAGE p0 Y = 1 ∧ REAL_SUM_IMAGE p1 Y = 1’
          by simp[Abbr ‘p0’, Abbr ‘p1’, Abbr ‘Y’] >>
        REAL_ASM_ARITH_TAC) >>
  ‘REAL_SUM_IMAGE (λz. cap_term (p0 (FST z)) (p1 (FST z)) * m (SND z)) (Y × Y) = c ∧
   REAL_SUM_IMAGE (λz. m (FST z) * cap_term (p0 (SND z)) (p1 (SND z))) (Y × Y) = c’
    by (simp[REAL_SUM_IMAGE_CROSS_MUL, Abbr ‘c’]) >>
  ‘cm + cp = 2 * c’
    by (‘cm + cp = REAL_SUM_IMAGE (λz. fm z + fp z) (Y × Y)’
          by simp[Abbr ‘cm’, Abbr ‘cp’, REAL_SUM_IMAGE_ADD] >>
        pop_assum SUBST1_TAC >>
        ‘REAL_SUM_IMAGE (λz. fm z + fp z) (Y × Y) =
         REAL_SUM_IMAGE
           (λz. cap_term (p0 (FST z)) (p1 (FST z)) * m (SND z) +
                m (FST z) * cap_term (p0 (SND z)) (p1 (SND z)))
           (Y × Y)’
          by (irule REAL_SUM_IMAGE_EQ >> simp[FORALL_PROD] >>
              qx_genl_tac [‘y1’, ‘y2’] >> strip_tac >>
              ‘0 ≤ p0 y1 ∧ 0 ≤ p1 y1 ∧ 0 ≤ p0 y2 ∧ 0 ≤ p1 y2’
                by simp[Abbr ‘p0’, Abbr ‘p1’, Abbr ‘Y’] >>
              qspecl_then [‘p0 y1’, ‘p1 y1’, ‘p0 y2’, ‘p1 y2’]
                mp_tac polar_cap_term_conservation >>
              simp[Abbr ‘fm’, Abbr ‘fp’, Abbr ‘m’] >> REAL_ASM_ARITH_TAC) >>
        pop_assum SUBST1_TAC >>
        simp[REAL_SUM_IMAGE_ADD] >> REAL_ASM_ARITH_TAC) >>
  ‘∀z. z ∈ Y × Y ⇒ m (FST z) * cap_term (p0 (SND z)) (p1 (SND z)) ≤ fp z’
    by (simp[FORALL_PROD] >> qx_genl_tac [‘y1’, ‘y2’] >> strip_tac >>
        ‘0 ≤ p0 y1 ∧ 0 ≤ p1 y1 ∧ 0 ≤ p0 y2 ∧ 0 ≤ p1 y2’
          by simp[Abbr ‘p0’, Abbr ‘p1’, Abbr ‘Y’] >>
        qspecl_then [‘p0 y1’, ‘p1 y1’, ‘p0 y2’, ‘p1 y2’]
          mp_tac polar_cap_term_plus_ge >>
        simp[Abbr ‘fp’, Abbr ‘m’]) >>
  ‘c ≤ cp’
    by (‘REAL_SUM_IMAGE (λz. m (FST z) * cap_term (p0 (SND z)) (p1 (SND z))) (Y × Y) ≤
         REAL_SUM_IMAGE fp (Y × Y)’
          by (irule REAL_SUM_IMAGE_MONO >> simp[]) >>
        gvs[Abbr ‘cp’]) >>
  ‘cm ≤ c ∧ cm ≤ cp’ by REAL_ASM_ARITH_TAC >>
  ‘cm = cp ⇔ c = 0 ∨ c = 1’
    by (EQ_TAC >> strip_tac
        >- (‘cp = c’ by REAL_ASM_ARITH_TAC >>
            ‘REAL_SUM_IMAGE (λz. fp z - m (FST z) * cap_term (p0 (SND z)) (p1 (SND z))) (Y × Y) = 0’
              by (simp[REAL_SUM_IMAGE_SUB, Abbr ‘cp’] >> REAL_ASM_ARITH_TAC) >>
            ‘∀y1 y2. y1 ∈ Y ∧ y2 ∈ Y ⇒
                     m y1 * cap_term (p0 y2) (p1 y2) = fp (y1, y2)’
              by (rpt strip_tac >>
                  qspecl_then [‘Y × Y’,
                               ‘λz. fp z - m (FST z) * cap_term (p0 (SND z)) (p1 (SND z))’]
                    mp_tac REAL_SUM_IMAGE_POS_EQ_0 >>
                  impl_tac
                  >- (simp[] >> qx_gen_tac ‘z’ >> strip_tac >>
                      qpat_x_assum ‘∀z. z ∈ Y × Y ⇒ _ ≤ fp z’
                        (qspec_then ‘z’ mp_tac) >>
                      simp[] >> REAL_ASM_ARITH_TAC) >>
                  disch_then (qspec_then ‘(y1, y2)’ mp_tac) >>
                  simp[] >> REAL_ASM_ARITH_TAC) >>
            ‘∀y1 y2. y1 ∈ Y ∧ y2 ∈ Y ⇒ p0 y2 * p1 y2 * (p0 y1 - p1 y1) = 0’
              by (rpt strip_tac >>
                  ‘0 ≤ p0 y1 ∧ 0 ≤ p1 y1 ∧ 0 ≤ p0 y2 ∧ 0 ≤ p1 y2’
                    by simp[Abbr ‘p0’, Abbr ‘p1’, Abbr ‘Y’] >>
                  qspecl_then [‘p0 y1’, ‘p1 y1’, ‘p0 y2’, ‘p1 y2’]
                    mp_tac polar_cap_term_plus_ge >>
                  first_x_assum (qspecl_then [‘y1’, ‘y2’] mp_tac) >>
                  simp[Abbr ‘fp’, Abbr ‘m’]) >>
            Cases_on ‘∃y2. y2 ∈ Y ∧ p0 y2 * p1 y2 ≠ 0’
            >- (disj1_tac >> fs[REAL_ENTIRE] >>
                ‘∀y1. y1 ∈ Y ⇒ p0 y1 = p1 y1’
                  by (qx_gen_tac ‘y1’ >> strip_tac >>
                      first_x_assum (qspecl_then [‘y1’, ‘y2’] mp_tac) >>
                      simp[REAL_ENTIRE] >> REAL_ASM_ARITH_TAC) >>
                simp[Abbr ‘c’] >> irule REAL_SUM_IMAGE_EQ_0 >> simp[] >>
                qx_gen_tac ‘y1’ >> strip_tac >>
                ‘0 ≤ p1 y1’ by simp[Abbr ‘p1’, Abbr ‘Y’] >>
                simp[cap_term_special])
            >- (disj2_tac >>
                ‘REAL_SUM_IMAGE (λy. cap_term (p0 y) (p1 y)) Y =
                 REAL_SUM_IMAGE m Y’
                  by (irule REAL_SUM_IMAGE_EQ >> simp[] >>
                      qx_gen_tac ‘y’ >> strip_tac >>
                      ‘0 ≤ p0 y ∧ 0 ≤ p1 y’
                        by simp[Abbr ‘p0’, Abbr ‘p1’, Abbr ‘Y’] >>
                      ‘p0 y = 0 ∨ p1 y = 0’ by metis_tac[REAL_ENTIRE] >>
                      pop_assum strip_assume_tac >>
                      simp[Abbr ‘m’, cap_term_special]) >>
                gvs[Abbr ‘c’]))
        >- REAL_ASM_ARITH_TAC
        >- REAL_ASM_ARITH_TAC) >>
  simp[extreal_of_num_def, extreal_add_eq, extreal_mul_eq, extreal_le_eq]
QED

(* Strict interior capacity polarization corollary of Proposition 4:
   0 < I(W) < 1 implies I(W_minus) < I(W) < I(W_plus).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_4_strict:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ∧
    0 < symmetric_capacity W ∧ symmetric_capacity W < 1 ⇒
    symmetric_capacity W_minus < symmetric_capacity W ∧
    symmetric_capacity W < symmetric_capacity W_plus
Proof
  rpt gen_tac >> strip_tac >>
  drule proposition_4 >> strip_tac >>
  ‘wf_bdmc W ∧ wf_bdmc W_minus ∧ wf_bdmc W_plus’ by fs[single_step_polar_def] >>
  ‘∃c. 0 ≤ c ∧ c ≤ 1 ∧ symmetric_capacity W = Normal c’
    by metis_tac[symmetric_capacity_bounds] >>
  ‘∃cm. 0 ≤ cm ∧ cm ≤ 1 ∧ symmetric_capacity W_minus = Normal cm’
    by metis_tac[symmetric_capacity_bounds] >>
  ‘∃cp. 0 ≤ cp ∧ cp ≤ 1 ∧ symmetric_capacity W_plus = Normal cp’
    by metis_tac[symmetric_capacity_bounds] >>
  ‘symmetric_capacity W_minus ≠ symmetric_capacity W_plus’
    by (strip_tac >>
        gvs[extreal_of_num_def, extreal_lt_eq] >> REAL_ASM_ARITH_TAC) >>
  gvs[extreal_of_num_def, extreal_add_eq, extreal_mul_eq,
      extreal_le_eq, extreal_lt_eq] >>
  REAL_ASM_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Block 3: Lemma 4 & Proposition 5 (Single-Step Bhattacharyya Relations)    *)
(* ------------------------------------------------------------------------- *)

(* Real-sum form of Arıkan Lemma 4 (Appendix D, Eq. (88), p. 22): concavity
   of the Bhattacharyya functional across any finite non-negative mixture,
   proved via finite Cauchy-Schwarz (bdmcTheory.REAL_SUM_IMAGE_CAUCHY_SCHWARZ).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem lemma_4_bhattacharyya_concave_real[local]:
  ∀(J : α -> bool) (Y : β -> bool) (q : α -> real)
   (pF : α -> β -> real) (pT : α -> β -> real).
    FINITE J ∧ FINITE Y ∧
    (∀j. j ∈ J ⇒ 0 ≤ q j) ∧
    (∀j y. j ∈ J ∧ y ∈ Y ⇒ 0 ≤ pF j y ∧ 0 ≤ pT j y) ⇒
    REAL_SUM_IMAGE
      (λj. q j * REAL_SUM_IMAGE (λy. sqrt (pF j y * pT j y)) Y) J ≤
    REAL_SUM_IMAGE
      (λy. sqrt (REAL_SUM_IMAGE (λj. q j * pF j y) J *
                 REAL_SUM_IMAGE (λj. q j * pT j y) J)) Y
Proof
  rpt strip_tac >>
  ‘REAL_SUM_IMAGE
     (λj. q j * REAL_SUM_IMAGE (λy. sqrt (pF j y * pT j y)) Y) J =
   REAL_SUM_IMAGE
     (λj. REAL_SUM_IMAGE (λy. q j * sqrt (pF j y * pT j y)) Y) J’
    by (irule REAL_SUM_IMAGE_EQ >> simp[REAL_SUM_IMAGE_CMUL]) >>
  pop_assum SUBST1_TAC >>
  simp[Once NESTED_REAL_SUM_IMAGE_REVERSE] >>
  irule REAL_SUM_IMAGE_MONO >> simp[] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  qabbrev_tac ‘Sy = REAL_SUM_IMAGE (λj. q j * sqrt (pF j y * pT j y)) J’ >>
  ‘0 ≤ Sy’
    by (simp[Abbr ‘Sy’] >> irule REAL_SUM_IMAGE_POS >> simp[] >>
        qx_gen_tac ‘j’ >> strip_tac >>
        irule REAL_LE_MUL >> simp[] >>
        irule realTheory.SQRT_POS_LE >> irule REAL_LE_MUL >> simp[]) >>
  ‘Sy =
   REAL_SUM_IMAGE
     (λj. sqrt (q j * pF j y) * sqrt (q j * pT j y)) J’
    by (simp[Abbr ‘Sy’] >> irule REAL_SUM_IMAGE_EQ >> simp[] >>
        qx_gen_tac ‘j’ >> strip_tac >>
        ‘0 ≤ q j ∧ 0 ≤ pF j y ∧ 0 ≤ pT j y’ by simp[] >>
        simp[realTheory.SQRT_MUL] >>
        ‘sqrt (q j) * sqrt (pF j y) * (sqrt (q j) * sqrt (pT j y)) =
         (sqrt (q j) pow 2) * (sqrt (pF j y) * sqrt (pT j y))’
          by REAL_ASM_ARITH_TAC >>
        pop_assum SUBST1_TAC >>
        simp[realTheory.SQRT_POW_2]) >>
  ‘Sy pow 2 ≤
   REAL_SUM_IMAGE (λj. (sqrt (q j * pF j y)) pow 2) J *
   REAL_SUM_IMAGE (λj. (sqrt (q j * pT j y)) pow 2) J’
    by (qpat_x_assum ‘Sy = _’ SUBST1_TAC >>
        ho_match_mp_tac REAL_SUM_IMAGE_CAUCHY_SCHWARZ >> simp[]) >>
  ‘REAL_SUM_IMAGE (λj. (sqrt (q j * pF j y)) pow 2) J =
   REAL_SUM_IMAGE (λj. q j * pF j y) J ∧
   REAL_SUM_IMAGE (λj. (sqrt (q j * pT j y)) pow 2) J =
   REAL_SUM_IMAGE (λj. q j * pT j y) J’
    by (conj_tac >> irule REAL_SUM_IMAGE_EQ >> simp[] >>
        qx_gen_tac ‘j’ >> strip_tac >>
        irule realTheory.SQRT_POW_2 >> irule REAL_LE_MUL >> simp[]) >>
  ‘Sy pow 2 ≤
   REAL_SUM_IMAGE (λj. q j * pF j y) J *
   REAL_SUM_IMAGE (λj. q j * pT j y) J’
    by gvs[] >>
  ‘0 ≤ Sy pow 2’ by simp[REAL_LE_POW2] >>
  ‘Sy = sqrt (Sy pow 2)’
    by (CONV_TAC SYM_CONV >> irule (GEN_ALL realTheory.POW_2_SQRT) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule realTheory.SQRT_MONO_LE >> simp[]
QED

(* Lemma 4 (Erdal Arıkan, 2009, Appendix D, Eq. (88), p. 22):
   Concavity of the Bhattacharyya parameter Z(W) in the channel transition
   probabilities across any finite mixture W(y|x) = ∑_{j ∈ J} Q(j) W_j(y|x).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem lemma_4_bhattacharyya_concave:
  ∀(J : α -> bool) (Q : α -> extreal)
   (Ws : α -> (bool, β) memoryless_channel)
   (W : (bool, β) memoryless_channel).
    FINITE J ∧ wf_bdmc W ∧
    (∀j. j ∈ J ⇒
         wf_bdmc (Ws j) ∧ mccodomain (Ws j) = mccodomain W ∧
         0 ≤ Q j ∧ Q j ≠ +∞) ∧
    (∀x y. y ∈ mccodomain W ⇒
           mcchannel W x {y} =
             ∑ (λj. Q j * mcchannel (Ws j) x {y}) J) ⇒
    ∑ (λj. Q j * bhattacharyya (Ws j)) J ≤ bhattacharyya W
Proof
  rpt strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  ‘∀j. j ∈ J ⇒ Q j = Normal (real (Q j)) ∧ 0 ≤ real (Q j)’
    by (qx_gen_tac ‘j’ >> strip_tac >>
        first_x_assum (drule_then strip_assume_tac) >>
        Cases_on ‘Q j’ >> gvs[extreal_of_num_def, extreal_le_eq]) >>
  ‘∑ (λj. Q j * bhattacharyya (Ws j)) J =
   Normal (REAL_SUM_IMAGE
             (λj. real (Q j) *
                  REAL_SUM_IMAGE
                    (λy. sqrt (real (mcchannel (Ws j) F {y}) *
                               real (mcchannel (Ws j) T {y})))
                    (mccodomain W))
             J)’
    by (simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
        irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
        qx_gen_tac ‘j’ >> strip_tac >>
        ‘wf_bdmc (Ws j) ∧ mccodomain (Ws j) = mccodomain W’ by simp[] >>
        drule bhattacharyya_real_sum >> simp[] >> strip_tac >>
        ‘Q j = Normal (real (Q j))’ by simp[] >>
        pop_assum SUBST1_TAC >>
        simp[extreal_mul_eq]) >>
  pop_assum SUBST1_TAC >>
  drule_then SUBST1_TAC bhattacharyya_real_sum >>
  ‘∀x y. y ∈ mccodomain W ⇒
         real (mcchannel W x {y}) =
         REAL_SUM_IMAGE
           (λj. real (Q j) * real (mcchannel (Ws j) x {y})) J’
    by (qx_genl_tac [‘x’, ‘y’] >> strip_tac >>
        ‘mcchannel W x {y} =
         Normal (REAL_SUM_IMAGE
                   (λj. real (Q j) * real (mcchannel (Ws j) x {y})) J)’
          by (first_x_assum (qspecl_then [‘x’, ‘y’] mp_tac) >> simp[] >>
              disch_then SUBST1_TAC >>
              simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
              irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
              qx_gen_tac ‘j’ >> strip_tac >>
              ‘wf_bdmc (Ws j) ∧ mccodomain (Ws j) = mccodomain W’ by simp[] >>
              ‘Q j = Normal (real (Q j))’ by simp[] >>
              ‘mcchannel (Ws j) x {y} =
                 Normal (real (mcchannel (Ws j) x {y}))’
                by (irule wf_bdmc_mcchannel_eq_normal >> simp[]) >>
              ntac 2 (pop_assum SUBST1_TAC) >>
              simp[extreal_mul_eq]) >>
        simp[]) >>
  simp[extreal_le_eq] >>
  ‘REAL_SUM_IMAGE
     (λy. sqrt (real (mcchannel W F {y}) * real (mcchannel W T {y})))
     (mccodomain W) =
   REAL_SUM_IMAGE
     (λy. sqrt (REAL_SUM_IMAGE
                  (λj. real (Q j) * real (mcchannel (Ws j) F {y})) J *
                REAL_SUM_IMAGE
                  (λj. real (Q j) * real (mcchannel (Ws j) T {y})) J))
     (mccodomain W)’
    by (irule REAL_SUM_IMAGE_EQ >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘J’, ‘mccodomain W’, ‘λj. real (Q j)’,
               ‘λj y. real (mcchannel (Ws j) F {y})’,
               ‘λj y. real (mcchannel (Ws j) T {y})’]
    mp_tac lemma_4_bhattacharyya_concave_real >>
  impl_tac
  >- (simp[] >> qx_genl_tac [‘j’, ‘y’] >> strip_tac >>
      ‘wf_bdmc (Ws j) ∧ mccodomain (Ws j) = mccodomain W’ by simp[] >>
      drule wf_bdmc_real_pmf_safe >> simp[]) >>
  simp[]
QED

(* Real-sum reduction of Z(W_minus) onto mccodomain W × mccodomain W across
   the output bijection f under single_step_polar W W_minus W_plus.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem single_step_bhattacharyya_minus_real_sum[local]:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    bhattacharyya W_minus =
      Normal (REAL_SUM_IMAGE
                (λp. (1 / 2) *
                     sqrt ((real (mcchannel W F {FST p}) *
                            real (mcchannel W F {SND p}) +
                            real (mcchannel W T {FST p}) *
                            real (mcchannel W T {SND p})) *
                           (real (mcchannel W F {FST p}) *
                            real (mcchannel W T {SND p}) +
                            real (mcchannel W T {FST p}) *
                            real (mcchannel W F {SND p}))))
                (mccodomain W × mccodomain W))
Proof
  rw[single_step_polar_def] >>
  qpat_x_assum ‘wf_bdmc W_minus’
    (SUBST1_TAC o MATCH_MP bhattacharyya_real_sum) >>
  AP_TERM_TAC >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  ‘FINITE (mccodomain W × mccodomain W)’ by simp[FINITE_CROSS] >>
  qpat_assum ‘wf_bdmc W’ (strip_assume_tac o MATCH_MP wf_bdmc_real_pmf_safe) >>
  qspecl_then [‘mccodomain W × mccodomain W’, ‘mccodomain W_minus’, ‘f’]
    mp_tac REAL_SUM_IMAGE_BIJ >>
  simp[] >> disch_then (fn th => ONCE_REWRITE_TAC[th]) >>
  irule REAL_SUM_IMAGE_EQ >> simp[FORALL_PROD, o_DEF] >>
  qx_genl_tac [‘y1’, ‘y2’] >> strip_tac >>
  qabbrev_tac ‘a = real (mcchannel W F {y1})’ >>
  qabbrev_tac ‘d = real (mcchannel W T {y1})’ >>
  qabbrev_tac ‘b = real (mcchannel W F {y2})’ >>
  qabbrev_tac ‘g = real (mcchannel W T {y2})’ >>
  ‘0 ≤ a ∧ 0 ≤ d ∧ 0 ≤ b ∧ 0 ≤ g’
    by simp[Abbr ‘a’, Abbr ‘d’, Abbr ‘b’, Abbr ‘g’] >>
  ‘mcchannel W F {y1} = Normal a ∧
   mcchannel W T {y1} = Normal d ∧
   mcchannel W F {y2} = Normal b ∧
   mcchannel W T {y2} = Normal g’
    by (simp[Abbr ‘a’, Abbr ‘d’, Abbr ‘b’, Abbr ‘g’] >>
        rpt conj_tac >> irule wf_bdmc_mcchannel_eq_normal >> simp[]) >>
  ‘mcchannel W_minus F {f (y1, y2)} =
     Normal ((1 / 2) * (a * b + d * g)) ∧
   mcchannel W_minus T {f (y1, y2)} =
     Normal ((1 / 2) * (a * g + d * b))’
    by (conj_tac >>
        qpat_x_assum ‘∀y1 y2 u1. _ ⇒ mcchannel W_minus _ _ = _’
          (fn th =>
            mp_tac (Q.SPECL [‘y1’, ‘y2’, ‘F’] th) >>
            mp_tac (Q.SPECL [‘y1’, ‘y2’, ‘T’] th)) >>
        simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq,
             extreal_add_eq, REAL_ADD_COMM]) >>
  simp[real_normal, extreal_of_num_def, extreal_div_eq, extreal_mul_eq,
       extreal_add_eq] >>
  ‘0 ≤ a * b + d * g ∧ 0 ≤ a * g + d * b ∧ 0 ≤ b * d + a * g ∧
   0 ≤ (a * b + d * g) * (a * g + b * d) ∧
   0 ≤ (a * b + d * g) * (b * d + a * g)’
    by (rpt conj_tac >>
        TRY (irule REAL_LE_ADD) >> TRY (irule REAL_LE_MUL) >>
        simp[REAL_LE_ADD, REAL_LE_MUL]) >>
  ‘sqrt ((1 / 4) * ((a * b + d * g) * (b * d + a * g))) =
   (1 / 2) * sqrt ((a * b + d * g) * (a * g + b * d))’
    by (MATCH_MP_TAC realTheory.SQRT_POS_UNIQ >>
        rpt conj_tac
        >- (irule REAL_LE_MUL >> simp[])
        >- (irule REAL_LE_MUL >> simp[realTheory.SQRT_POS_LE])
        >- (simp[POW_MUL, realTheory.SQRT_POW_2] >>
            realLib.REAL_ARITH_TAC)) >>
  simp[]
QED

(* Proposition 5, Eq. (26) (Erdal Arıkan, 2009, Section III-A & Appendix D):
   Exact squaring relation Z(W_plus) = Z(W)^2 under single_step_polar.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_5_plus_sq:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    bhattacharyya W_plus = (bhattacharyya W) pow 2
Proof
  rw[single_step_polar_def] >>
  qpat_x_assum ‘wf_bdmc W_plus’
    (SUBST1_TAC o MATCH_MP bhattacharyya_real_sum) >>
  qpat_assum ‘wf_bdmc W’
    (SUBST1_TAC o MATCH_MP bhattacharyya_real_sum) >>
  simp[extreal_pow_def] >>
  ‘FINITE (mccodomain W) ∧ FINITE (mccodomain W_minus) ∧ FINITE 𝕌(:bool)’
    by (fs[wf_bdmc_def] >> simp[UNIV_BOOL]) >>
  ‘FINITE (mccodomain W × mccodomain W) ∧
   FINITE (mccodomain W_minus × 𝕌(:bool))’
    by simp[FINITE_CROSS] >>
  qpat_assum ‘wf_bdmc W’ (strip_assume_tac o MATCH_MP wf_bdmc_real_pmf_safe) >>
  qabbrev_tac ‘gp = λyp. sqrt (real (mcchannel W_plus F {yp}) *
                               real (mcchannel W_plus T {yp}))’ >>
  qspecl_then [‘mccodomain W_minus × 𝕌(:bool)’, ‘mccodomain W_plus’, ‘h’]
    mp_tac REAL_SUM_IMAGE_BIJ >>
  simp[] >> disch_then (fn th => ONCE_REWRITE_TAC[th]) >>
  ‘gp ∘ h = λp. gp (h (FST p, SND p))’
    by simp[FUN_EQ_THM, FORALL_PROD, o_DEF] >>
  pop_assum SUBST1_TAC >>
  simp[GSYM REAL_SUM_IMAGE_REAL_SUM_IMAGE] >>
  qspecl_then [‘mccodomain W × mccodomain W’, ‘mccodomain W_minus’, ‘f’]
    mp_tac REAL_SUM_IMAGE_BIJ >>
  simp[] >> disch_then (fn th => ONCE_REWRITE_TAC[th]) >>
  simp[REAL_SUM_IMAGE_POW] >>
  irule REAL_SUM_IMAGE_EQ >>
  simp[FORALL_PROD, o_DEF, REAL_SUM_IMAGE_BOOL,
       REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT] >>
  qx_genl_tac [‘y1’, ‘y2’] >> strip_tac >>
  qabbrev_tac ‘a = real (mcchannel W F {y1})’ >>
  qabbrev_tac ‘d = real (mcchannel W T {y1})’ >>
  qabbrev_tac ‘b = real (mcchannel W F {y2})’ >>
  qabbrev_tac ‘g = real (mcchannel W T {y2})’ >>
  ‘0 ≤ a ∧ 0 ≤ d ∧ 0 ≤ b ∧ 0 ≤ g’
    by simp[Abbr ‘a’, Abbr ‘d’, Abbr ‘b’, Abbr ‘g’] >>
  ‘mcchannel W F {y1} = Normal a ∧
   mcchannel W T {y1} = Normal d ∧
   mcchannel W F {y2} = Normal b ∧
   mcchannel W T {y2} = Normal g’
    by (simp[Abbr ‘a’, Abbr ‘d’, Abbr ‘b’, Abbr ‘g’] >>
        rpt conj_tac >> irule wf_bdmc_mcchannel_eq_normal >> simp[]) >>
  ‘mcchannel W_plus F {h (f (y1, y2), T)} = Normal ((1 / 2) * d * b) ∧
   mcchannel W_plus T {h (f (y1, y2), T)} = Normal ((1 / 2) * a * g) ∧
   mcchannel W_plus F {h (f (y1, y2), F)} = Normal ((1 / 2) * a * b) ∧
   mcchannel W_plus T {h (f (y1, y2), F)} = Normal ((1 / 2) * d * g)’
    by (rpt conj_tac >>
        qpat_x_assum ‘∀y1 y2 u1 u2. _ ⇒ mcchannel W_plus _ _ = _’
          (qspecl_then [‘y1’, ‘y2’] mp_tac) >>
        simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq]) >>
  simp[Abbr ‘gp’, real_normal] >>
  ‘sqrt ((1 / 4) * (a * b * d * g)) =
   (1 / 2) * (sqrt a * sqrt b * sqrt d * sqrt g)’
    by (MATCH_MP_TAC realTheory.SQRT_POS_UNIQ >>
        rpt conj_tac
        >- (ntac 4 (irule REAL_LE_MUL >> simp[]))
        >- (ntac 4 (irule REAL_LE_MUL >> simp[realTheory.SQRT_POS_LE]))
        >- (simp[POW_MUL, realTheory.SQRT_POW_2] >>
            realLib.REAL_ARITH_TAC)) >>
  simp[realTheory.SQRT_MUL] >>
  realLib.REAL_ARITH_TAC
QED

(* Arıkan's Appendix D polynomial identity (arXiv:0807.3917, p. 22) expressed
   in square-root coordinates u = sqrt a, v = sqrt d, r = sqrt b, s = sqrt g.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem arikan_prop5_poly_identity[local]:
  ∀(u : real) v r s.
    (u pow 2 * r pow 2 + v pow 2 * s pow 2) *
    (u pow 2 * s pow 2 + v pow 2 * r pow 2) +
    2 * (u * v * r * s) * (u - v) pow 2 * (r - s) pow 2 =
    ((u pow 2 + v pow 2) * (r * s) + (r pow 2 + s pow 2) * (u * v) -
     2 * (u * v * r * s)) pow 2 ∧
    (u pow 2 + v pow 2) * (r * s) + (r pow 2 + s pow 2) * (u * v) -
    2 * (u * v * r * s) =
    (r * s) * (u - v) pow 2 + (u * v) * (r - s) pow 2 + 2 * (u * v * r * s)
Proof
  rpt gen_tac >> realLib.REAL_ARITH_TAC
QED

(* Pointwise Arıkan Appendix D inequality and exact equality condition for
   Eq. (27) on non-negative transition masses a, d, b, g.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem arikan_prop5_pointwise_real[local]:
  ∀(a : real) d b g.
    0 ≤ a ∧ 0 ≤ d ∧ 0 ≤ b ∧ 0 ≤ g ⇒
    (1 / 2) * sqrt ((a * b + d * g) * (a * g + d * b)) ≤
      (1 / 2) * ((a + d) * sqrt (b * g) + (b + g) * sqrt (a * d)) -
      sqrt (a * d) * sqrt (b * g) ∧
    ((1 / 2) * sqrt ((a * b + d * g) * (a * g + d * b)) =
       (1 / 2) * ((a + d) * sqrt (b * g) + (b + g) * sqrt (a * d)) -
       sqrt (a * d) * sqrt (b * g) ⇔
     a * d = 0 ∨ b * g = 0 ∨ a = d ∨ b = g)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac ‘u = sqrt a’ >>
  qabbrev_tac ‘v = sqrt d’ >>
  qabbrev_tac ‘r = sqrt b’ >>
  qabbrev_tac ‘s = sqrt g’ >>
  ‘0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ r ∧ 0 ≤ s’
    by (simp[Abbr ‘u’, Abbr ‘v’, Abbr ‘r’, Abbr ‘s’, realTheory.SQRT_POS_LE]) >>
  ‘u pow 2 = a ∧ v pow 2 = d ∧ r pow 2 = b ∧ s pow 2 = g’
    by (simp[Abbr ‘u’, Abbr ‘v’, Abbr ‘r’, Abbr ‘s’, realTheory.SQRT_POW_2]) >>
  ‘sqrt (a * d) = u * v ∧ sqrt (b * g) = r * s’
    by (simp[Abbr ‘u’, Abbr ‘v’, Abbr ‘r’, Abbr ‘s’, realTheory.SQRT_MUL]) >>
  qabbrev_tac ‘P = (a * b + d * g) * (a * g + d * b)’ >>
  qabbrev_tac ‘D = 2 * (u * v * r * s) * (u - v) pow 2 * (r - s) pow 2’ >>
  qabbrev_tac ‘R = (a + d) * (r * s) + (b + g) * (u * v) - 2 * (u * v * r * s)’ >>
  ‘P + D = R pow 2 ∧
   R = (r * s) * (u - v) pow 2 + (u * v) * (r - s) pow 2 + 2 * (u * v * r * s)’
    by (qspecl_then [‘u’, ‘v’, ‘r’, ‘s’] mp_tac arikan_prop5_poly_identity >>
        simp[Abbr ‘P’, Abbr ‘D’, Abbr ‘R’]) >>
  ‘0 ≤ P’
    by (simp[Abbr ‘P’] >> irule REAL_LE_MUL >>
        conj_tac >> irule REAL_LE_ADD >> conj_tac >> irule REAL_LE_MUL >>
        simp[]) >>
  ‘0 ≤ D’
    by (simp[Abbr ‘D’] >>
        irule REAL_LE_MUL >> simp[REAL_LE_POW2] >>
        irule REAL_LE_MUL >> simp[REAL_LE_POW2] >>
        irule REAL_LE_MUL >> simp[] >>
        rpt (irule REAL_LE_MUL >> simp[])) >>
  ‘0 ≤ R’
    by (qpat_x_assum ‘R = _’ SUBST1_TAC >>
        irule REAL_LE_ADD >> conj_tac
        >- (irule REAL_LE_ADD >> conj_tac >>
            irule REAL_LE_MUL >> simp[REAL_LE_POW2, REAL_LE_MUL])
        >- (rpt (irule REAL_LE_MUL >> simp[]))) >>
  ‘sqrt (R pow 2) = R’
    by (irule (GEN_ALL realTheory.POW_2_SQRT) >> simp[]) >>
  ‘P ≤ R pow 2’
    by (qpat_assum ‘P + D = R pow 2’ mp_tac >>
        qpat_assum ‘0 ≤ D’ mp_tac >>
        realLib.REAL_ARITH_TAC) >>
  ‘sqrt P ≤ R’
    by (‘sqrt P ≤ sqrt (R pow 2)’
          by (irule realTheory.SQRT_MONO_LE >> simp[]) >>
        pop_assum mp_tac >> simp[]) >>
  qpat_x_assum ‘sqrt (a * d) = u * v’ SUBST1_TAC >>
  qpat_x_assum ‘sqrt (b * g) = r * s’ SUBST1_TAC >>
  conj_tac
  >- (qpat_assum ‘sqrt P ≤ R’ mp_tac >>
      qpat_assum ‘Abbrev (R = _)’
        (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      realLib.REAL_ARITH_TAC)
  >- (‘((1 / 2 : real) * sqrt P =
        (1 / 2) * ((a + d) * (r * s) + (b + g) * (u * v)) -
        (u * v) * (r * s)) ⇔
       sqrt P = R’
        by (qpat_assum ‘Abbrev (R = _)’
              (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
            realLib.REAL_ARITH_TAC) >>
      pop_assum SUBST1_TAC >>
      ‘(sqrt P = R) ⇔ (D = 0)’
        by (eq_tac >> strip_tac
            >- (‘(sqrt P) pow 2 = P’ by simp[realTheory.SQRT_POW_2] >>
                ‘R pow 2 = P’ by (pop_assum (SUBST1_TAC o SYM) >> simp[]) >>
                qpat_assum ‘P + D = R pow 2’ mp_tac >>
                pop_assum mp_tac >> realLib.REAL_ARITH_TAC)
            >- (‘P = R pow 2’
                  by (qpat_assum ‘P + D = R pow 2’ mp_tac >>
                      qpat_assum ‘D = 0’ mp_tac >> realLib.REAL_ARITH_TAC) >>
                pop_assum SUBST1_TAC >> simp[])) >>
      pop_assum SUBST1_TAC >>
      ‘(D = 0) ⇔ (u * v = 0 ∨ r * s = 0 ∨ u = v ∨ r = s)’
        by (simp[Abbr ‘D’, REAL_ENTIRE, REAL_POW_EQ_0, REAL_SUB_0] >>
            eq_tac >> strip_tac >> simp[]) >>
      pop_assum SUBST1_TAC >>
      ‘(u * v = 0 ⇔ a * d = 0) ∧
       (r * s = 0 ⇔ b * g = 0) ∧
       (u = v ⇔ a = d) ∧
       (r = s ⇔ b = g)’
        by (rpt conj_tac
            >- (qpat_assum ‘u pow 2 = a’ mp_tac >>
                qpat_assum ‘v pow 2 = d’ mp_tac >>
                rpt (pop_assum kall_tac) >>
                rw[REAL_ENTIRE, REAL_POW_EQ_0] >> gvs[REAL_POW_EQ_0])
            >- (qpat_assum ‘r pow 2 = b’ mp_tac >>
                qpat_assum ‘s pow 2 = g’ mp_tac >>
                rpt (pop_assum kall_tac) >>
                rw[REAL_ENTIRE, REAL_POW_EQ_0] >> gvs[REAL_POW_EQ_0])
            >- (qpat_assum ‘u pow 2 = a’ mp_tac >>
                qpat_assum ‘v pow 2 = d’ mp_tac >>
                qpat_assum ‘Abbrev (u = _)’ mp_tac >>
                qpat_assum ‘Abbrev (v = _)’ mp_tac >>
                rpt (pop_assum kall_tac) >> rw[markerTheory.Abbrev_def] >>
                metis_tac[])
            >- (qpat_assum ‘r pow 2 = b’ mp_tac >>
                qpat_assum ‘s pow 2 = g’ mp_tac >>
                qpat_assum ‘Abbrev (r = _)’ mp_tac >>
                qpat_assum ‘Abbrev (s = _)’ mp_tac >>
                rpt (pop_assum kall_tac) >> rw[markerTheory.Abbrev_def] >>
                metis_tac[])) >>
      simp[])
QED

(* Real-PMF characterization of is_bec for any well-formed B-DMC W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_bec_real_iff[local]:
  ∀W : (bool, α) memoryless_channel.
    wf_bdmc W ⇒
    (is_bec W ⇔
     ∀y. y ∈ mccodomain W ⇒
         real (mcchannel W F {y}) * real (mcchannel W T {y}) = 0 ∨
         real (mcchannel W F {y}) = real (mcchannel W T {y}))
Proof
  gen_tac >> strip_tac >>
  ASM_REWRITE_TAC [is_bec_def] >>
  AP_TERM_TAC >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> qx_gen_tac ‘y’ >> BETA_TAC >>
  Cases_on ‘y ∈ mccodomain W’ >> ASM_REWRITE_TAC [] >>
  qabbrev_tac ‘a = real (mcchannel W F {y})’ >>
  qabbrev_tac ‘b = real (mcchannel W T {y})’ >>
  ‘mcchannel W F {y} = Normal a’
    by (UNABBREV_ALL_TAC >> irule wf_bdmc_mcchannel_eq_normal >>
        ASM_REWRITE_TAC []) >>
  ‘mcchannel W T {y} = Normal b’
    by (UNABBREV_ALL_TAC >> irule wf_bdmc_mcchannel_eq_normal >>
        ASM_REWRITE_TAC []) >>
  ntac 2 (pop_assum SUBST1_TAC) >>
  REWRITE_TAC [extreal_mul_eq, extreal_of_num_def, extreal_11]
QED

(* Proposition 5, Eq. (27) and exact BEC equality characterization
   (Erdal Arıkan, 2009, Section III-A Eq. (27) & Appendix D, p. 22).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_5_minus_upper_bec:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    bhattacharyya W_minus ≤ 2 * bhattacharyya W - (bhattacharyya W) pow 2 ∧
    (bhattacharyya W_minus = 2 * bhattacharyya W - (bhattacharyya W) pow 2 ⇔
     is_bec W)
Proof
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac single_step_bhattacharyya_minus_real_sum >>
  ‘wf_bdmc W’ by fs[single_step_polar_def] >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  ‘FINITE (mccodomain W × mccodomain W)’ by simp[FINITE_CROSS] >>
  drule_then assume_tac bhattacharyya_real_sum >>
  drule_then strip_assume_tac wf_bdmc_real_pmf_safe >>
  qabbrev_tac ‘Y = mccodomain W’ >>
  qabbrev_tac ‘pF = λy. real (mcchannel W F {y})’ >>
  qabbrev_tac ‘pT = λy. real (mcchannel W T {y})’ >>
  qabbrev_tac ‘zt = λy. sqrt (pF y * pT y)’ >>
  qabbrev_tac ‘z = REAL_SUM_IMAGE zt Y’ >>
  qabbrev_tac ‘lhs_f = λp : α # α.
                         (1 / 2) *
                         sqrt ((pF (FST p) * pF (SND p) +
                                pT (FST p) * pT (SND p)) *
                               (pF (FST p) * pT (SND p) +
                                pT (FST p) * pF (SND p)))’ >>
  qabbrev_tac ‘rhs_f = λp : α # α.
                         (1 / 2) *
                         ((pF (FST p) + pT (FST p)) * zt (SND p) +
                          (pF (SND p) + pT (SND p)) * zt (FST p)) -
                         zt (FST p) * zt (SND p)’ >>
  ‘bhattacharyya W_minus = Normal (REAL_SUM_IMAGE lhs_f (Y × Y)) ∧
   2 * bhattacharyya W - (bhattacharyya W) pow 2 = Normal (2 * z - z pow 2)’
    by (conj_tac
        >- (simp[Abbr ‘lhs_f’, Abbr ‘pF’, Abbr ‘pT’, Abbr ‘Y’])
        >- (‘bhattacharyya W = Normal z’
              by simp[Abbr ‘z’, Abbr ‘zt’, Abbr ‘pF’, Abbr ‘pT’, Abbr ‘Y’] >>
            pop_assum SUBST1_TAC >>
            simp[extreal_of_num_def, extreal_mul_eq, extreal_pow_def,
                 extreal_sub_eq])) >>
  ‘∀p. p ∈ Y × Y ⇒
       lhs_f p ≤ rhs_f p ∧
       (lhs_f p = rhs_f p ⇔
        pF (FST p) * pT (FST p) = 0 ∨
        pF (SND p) * pT (SND p) = 0 ∨
        pF (FST p) = pT (FST p) ∨
        pF (SND p) = pT (SND p))’
    by (simp[FORALL_PROD] >> qx_genl_tac [‘y1’, ‘y2’] >> strip_tac >>
        ‘0 ≤ pF y1 ∧ 0 ≤ pT y1 ∧ 0 ≤ pF y2 ∧ 0 ≤ pT y2’
          by simp[Abbr ‘pF’, Abbr ‘pT’, Abbr ‘Y’] >>
        qspecl_then [‘pF y1’, ‘pT y1’, ‘pF y2’, ‘pT y2’] mp_tac
          arikan_prop5_pointwise_real >>
        simp[Abbr ‘lhs_f’, Abbr ‘rhs_f’, Abbr ‘zt’]) >>
  ‘REAL_SUM_IMAGE rhs_f (Y × Y) = 2 * z - z pow 2’
    by (‘REAL_SUM_IMAGE rhs_f (Y × Y) =
         REAL_SUM_IMAGE
           (λp. ((1 / 2) * ((pF (FST p) + pT (FST p)) * zt (SND p)) +
                 (1 / 2) * (zt (FST p) * (pF (SND p) + pT (SND p)))) -
                zt (FST p) * zt (SND p))
           (Y × Y)’
          by (irule REAL_SUM_IMAGE_EQ >> simp[Abbr ‘rhs_f’] >>
              gen_tac >> strip_tac >> realLib.REAL_ARITH_TAC) >>
        pop_assum SUBST1_TAC >>
        simp[REAL_SUM_IMAGE_SUB, REAL_SUM_IMAGE_ADD, REAL_SUM_IMAGE_CMUL,
             REAL_SUM_IMAGE_CROSS_MUL] >>
        ‘REAL_SUM_IMAGE pF Y = 1 ∧ REAL_SUM_IMAGE pT Y = 1’
          by simp[Abbr ‘pF’, Abbr ‘pT’, Abbr ‘Y’] >>
        simp[Abbr ‘z’] >> REAL_ASM_ARITH_TAC) >>
  conj_tac
  >- (simp[extreal_le_eq] >>
      qpat_assum ‘REAL_SUM_IMAGE rhs_f _ = _’ (SUBST1_TAC o SYM) >>
      irule REAL_SUM_IMAGE_MONO >> simp[])
  >- (simp[] >>
      ‘(REAL_SUM_IMAGE lhs_f (Y × Y) = 2 * z - z pow 2) ⇔
       (REAL_SUM_IMAGE lhs_f (Y × Y) = REAL_SUM_IMAGE rhs_f (Y × Y))’
        by simp[] >>
      pop_assum SUBST1_TAC >>
      qspecl_then [‘Y × Y’, ‘lhs_f’, ‘rhs_f’] mp_tac
        REAL_SUM_IMAGE_EQ_IFF_POINTWISE_LE >>
      simp[] >> disch_then SUBST1_TAC >>
      ‘is_bec W ⇔ ∀y. y ∈ Y ⇒ pF y * pT y = 0 ∨ pF y = pT y’
        by (drule_then SUBST1_TAC is_bec_real_iff >>
            simp[Abbr ‘Y’, Abbr ‘pF’, Abbr ‘pT’]) >>
      pop_assum SUBST1_TAC >>
      qpat_x_assum ‘∀p. p ∈ Y × Y ⇒ _’
        (assume_tac o SIMP_RULE (srw_ss()) [FORALL_PROD]) >>
      simp[FORALL_PROD] >>
      metis_tac[])
QED

(* Factorization of sqrt ((a * b) * (d * b)) and sqrt ((d * b) * (a * b))
   for non-negative reals a, d, b.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sqrt_pair_factor[local]:
  ∀(a : real) d b.
    0 ≤ a ∧ 0 ≤ d ∧ 0 ≤ b ⇒
    sqrt ((a * b) * (d * b)) = sqrt (a * d) * b ∧
    sqrt ((d * b) * (a * b)) = sqrt (a * d) * b
Proof
  rpt gen_tac >> strip_tac >>
  ‘0 ≤ a * d’ by (irule REAL_LE_MUL >> simp[]) >>
  conj_tac >>
  (MATCH_MP_TAC realTheory.SQRT_POS_UNIQ >> rpt conj_tac
   >- (irule REAL_LE_MUL >> conj_tac >> irule REAL_LE_MUL >> simp[])
   >- (irule REAL_LE_MUL >> simp[realTheory.SQRT_POS_LE])
   >- (simp[POW_MUL, realTheory.SQRT_POW_2] >> realLib.REAL_ARITH_TAC))
QED

(* Proposition 5, Eq. (28) (Erdal Arıkan, 2009, Section III-A & Appendix D):
   Centrifugal ordering Z(W_plus) ≤ Z(W) ≤ Z(W_minus) via Lemma 4 concavity.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_5_ordering:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    bhattacharyya W_plus ≤ bhattacharyya W ∧
    bhattacharyya W ≤ bhattacharyya W_minus
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_then assume_tac proposition_5_plus_sq >>
      ‘wf_bdmc W’ by fs[single_step_polar_def] >>
      drule_then strip_assume_tac bhattacharyya_bounds >>
      simp[extreal_pow_def, extreal_le_eq] >>
      ‘0 ≤ z * (1 - z)’ by (irule REAL_LE_MUL >> REAL_ASM_ARITH_TAC) >>
      REAL_ASM_ARITH_TAC)
  >- (drule_then assume_tac single_step_bhattacharyya_minus_real_sum >>
      ‘wf_bdmc W’ by fs[single_step_polar_def] >>
      ‘FINITE (mccodomain W) ∧ FINITE 𝕌(:bool)’
        by (fs[wf_bdmc_def] >> simp[UNIV_BOOL]) >>
      ‘FINITE (mccodomain W × mccodomain W)’ by simp[FINITE_CROSS] >>
      drule_then assume_tac bhattacharyya_real_sum >>
      drule_then strip_assume_tac wf_bdmc_real_pmf_safe >>
      simp[extreal_le_eq] >>
      qabbrev_tac ‘Y = mccodomain W’ >>
      qabbrev_tac ‘pF = λy. real (mcchannel W F {y})’ >>
      qabbrev_tac ‘pT = λy. real (mcchannel W T {y})’ >>
      qabbrev_tac ‘z = REAL_SUM_IMAGE (λy. sqrt (pF y * pT y)) Y’ >>
      qabbrev_tac ‘wF = λ(j : bool) (p : α # α).
                          if j then pT (FST p) * pT (SND p)
                          else pF (FST p) * pF (SND p)’ >>
      qabbrev_tac ‘wT = λ(j : bool) (p : α # α).
                          if j then pF (FST p) * pT (SND p)
                          else pT (FST p) * pF (SND p)’ >>
      qspecl_then [‘𝕌(:bool)’, ‘Y × Y’, ‘λj : bool. (1 / 2 : real)’, ‘wF’, ‘wT’]
        mp_tac lemma_4_bhattacharyya_concave_real >>
      impl_tac
      >- (simp[FORALL_PROD, Abbr ‘wF’, Abbr ‘wT’, Abbr ‘pF’, Abbr ‘pT’, Abbr ‘Y’] >>
          rpt strip_tac >> rw[] >> irule REAL_LE_MUL >> simp[]) >>
      ‘REAL_SUM_IMAGE
         (λj. (1 / 2) * REAL_SUM_IMAGE (λp. sqrt (wF j p * wT j p)) (Y × Y))
         𝕌(:bool) = z’
        by (simp[REAL_SUM_IMAGE_BOOL, REAL_SUM_IMAGE_THM,
                 DELETE_NON_ELEMENT_RWT] >>
            ‘REAL_SUM_IMAGE (λp. sqrt (wF F p * wT F p)) (Y × Y) = z ∧
             REAL_SUM_IMAGE (λp. sqrt (wF T p * wT T p)) (Y × Y) = z’
              by (conj_tac
                  >- (‘REAL_SUM_IMAGE (λp. sqrt (wF F p * wT F p)) (Y × Y) =
                       REAL_SUM_IMAGE
                         (λp. sqrt (pF (FST p) * pT (FST p)) * pF (SND p))
                         (Y × Y)’
                        by (irule REAL_SUM_IMAGE_EQ >> simp[FORALL_PROD] >>
                            qx_genl_tac [‘y1’, ‘y2’] >> strip_tac >>
                            qspecl_then [‘pF y1’, ‘pT y1’, ‘pF y2’] mp_tac
                              sqrt_pair_factor >>
                            impl_tac
                            >- simp[Abbr ‘pF’, Abbr ‘pT’, Abbr ‘Y’] >>
                            strip_tac >>
                            qpat_assum ‘Abbrev (wF = _)’
                              (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
                            qpat_assum ‘Abbrev (wT = _)’
                              (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
                            BETA_TAC >>
                            ASM_REWRITE_TAC [FST, SND, COND_CLAUSES] >>
                            realLib.REAL_ARITH_TAC) >>
                      pop_assum SUBST1_TAC >>
                      qspecl_then [‘Y’, ‘Y’, ‘λy. sqrt (pF y * pT y)’, ‘pF’]
                        mp_tac REAL_SUM_IMAGE_CROSS_MUL >>
                      impl_tac >- simp[] >>
                      disch_then
                        (SUBST1_TAC o CONV_RULE (DEPTH_CONV BETA_CONV)) >>
                      simp[Abbr ‘z’, Abbr ‘pF’, Abbr ‘Y’])
                  >- (‘REAL_SUM_IMAGE (λp. sqrt (wF T p * wT T p)) (Y × Y) =
                       REAL_SUM_IMAGE
                         (λp. sqrt (pF (FST p) * pT (FST p)) * pT (SND p))
                         (Y × Y)’
                        by (irule REAL_SUM_IMAGE_EQ >> simp[FORALL_PROD] >>
                            qx_genl_tac [‘y1’, ‘y2’] >> strip_tac >>
                            qspecl_then [‘pF y1’, ‘pT y1’, ‘pT y2’] mp_tac
                              sqrt_pair_factor >>
                            impl_tac
                            >- simp[Abbr ‘pF’, Abbr ‘pT’, Abbr ‘Y’] >>
                            strip_tac >>
                            qpat_assum ‘Abbrev (wF = _)’
                              (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
                            qpat_assum ‘Abbrev (wT = _)’
                              (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
                            BETA_TAC >>
                            ASM_REWRITE_TAC [FST, SND, COND_CLAUSES] >>
                            realLib.REAL_ARITH_TAC) >>
                      pop_assum SUBST1_TAC >>
                      qspecl_then [‘Y’, ‘Y’, ‘λy. sqrt (pF y * pT y)’, ‘pT’]
                        mp_tac REAL_SUM_IMAGE_CROSS_MUL >>
                      impl_tac >- simp[] >>
                      disch_then
                        (SUBST1_TAC o CONV_RULE (DEPTH_CONV BETA_CONV)) >>
                      simp[Abbr ‘z’, Abbr ‘pT’, Abbr ‘Y’])) >>
            simp[] >> realLib.REAL_ARITH_TAC) >>
      ‘REAL_SUM_IMAGE
         (λp. sqrt (REAL_SUM_IMAGE (λj. (1 / 2) * wF j p) 𝕌(:bool) *
                    REAL_SUM_IMAGE (λj. (1 / 2) * wT j p) 𝕌(:bool)))
         (Y × Y) =
       REAL_SUM_IMAGE
         (λp. (1 / 2) *
              sqrt ((pF (FST p) * pF (SND p) + pT (FST p) * pT (SND p)) *
                    (pF (FST p) * pT (SND p) + pT (FST p) * pF (SND p))))
         (Y × Y)’
        by (irule REAL_SUM_IMAGE_EQ >> simp[FORALL_PROD] >>
            qx_genl_tac [‘y1’, ‘y2’] >> strip_tac >>
            ‘0 ≤ pF y1 ∧ 0 ≤ pT y1 ∧ 0 ≤ pF y2 ∧ 0 ≤ pT y2’
              by simp[Abbr ‘pF’, Abbr ‘pT’, Abbr ‘Y’] >>
            ‘0 ≤ (pF y1 * pF y2 + pT y1 * pT y2) *
                 (pF y1 * pT y2 + pF y2 * pT y1)’
              by (irule REAL_LE_MUL >> conj_tac >>
                  irule REAL_LE_ADD >> conj_tac >>
                  irule REAL_LE_MUL >> simp[]) >>
            ‘sqrt (((1 / 2) * (pF y1 * pT y2) + (1 / 2) * (pF y2 * pT y1)) *
                   ((1 / 2) * (pT y1 * pT y2) + (1 / 2) * (pF y1 * pF y2))) =
             (1 / 2) *
             sqrt ((pF y1 * pF y2 + pT y1 * pT y2) *
                   (pF y1 * pT y2 + pF y2 * pT y1))’
              by (MATCH_MP_TAC realTheory.SQRT_POS_UNIQ >> rpt conj_tac
                  >- (irule REAL_LE_MUL >> conj_tac >>
                      irule REAL_LE_ADD >> conj_tac >>
                      ntac 2 (irule REAL_LE_MUL >> simp[REAL_LE_POW2]))
                  >- (irule REAL_LE_MUL >> simp[realTheory.SQRT_POS_LE])
                  >- (simp[POW_MUL, realTheory.SQRT_POW_2] >>
                      realLib.REAL_ARITH_TAC)) >>
            simp[Abbr ‘wF’, Abbr ‘wT’, REAL_SUM_IMAGE_BOOL,
                 REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT]) >>
      ntac 2 (pop_assum (fn th => REWRITE_TAC[th])) >>
      simp[])
QED

(* Proposition 5 (Erdal Arıkan, 2009, Section III-A Eqs. (26)-(29) & Appendix D):
   Complete single-step Bhattacharyya reliability transformation under
   single_step_polar W W_minus W_plus:
   (1) Eq. (26): Z(W_plus) = Z(W)^2
   (2) Eq. (27): Z(W_minus) ≤ 2 Z(W) - Z(W)^2
   (3) Equality in Eq. (27) iff W is a BEC
   (4)-(5) Eq. (28): Z(W_plus) ≤ Z(W) ∧ Z(W) ≤ Z(W_minus)
   (6) Eq. (29): Z(W_minus) + Z(W_plus) ≤ 2 Z(W)
   (7) Extremal equality: Z(W_minus) = Z(W_plus) ⇔ Z(W) = 0 ∨ Z(W) = 1.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_5:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    bhattacharyya W_plus = (bhattacharyya W) pow 2 ∧
    bhattacharyya W_minus ≤ 2 * bhattacharyya W - (bhattacharyya W) pow 2 ∧
    (bhattacharyya W_minus = 2 * bhattacharyya W - (bhattacharyya W) pow 2 ⇔
     is_bec W) ∧
    bhattacharyya W_plus ≤ bhattacharyya W ∧
    bhattacharyya W ≤ bhattacharyya W_minus ∧
    bhattacharyya W_minus + bhattacharyya W_plus ≤ 2 * bhattacharyya W ∧
    (bhattacharyya W_minus = bhattacharyya W_plus ⇔
     bhattacharyya W = 0 ∨ bhattacharyya W = 1)
Proof
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac proposition_5_plus_sq >>
  drule_then strip_assume_tac proposition_5_minus_upper_bec >>
  drule_then strip_assume_tac proposition_5_ordering >>
  ‘wf_bdmc W ∧ wf_bdmc W_minus ∧ wf_bdmc W_plus’
    by fs[single_step_polar_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘_ ⇔ is_bec W’ kall_tac >>
  qpat_x_assum ‘wf_bdmc W’ (strip_assume_tac o MATCH_MP bhattacharyya_bounds) >>
  qpat_x_assum ‘wf_bdmc W_minus’
    (strip_assume_tac o MATCH_MP bhattacharyya_bounds) >>
  qpat_x_assum ‘wf_bdmc W_plus’
    (strip_assume_tac o MATCH_MP bhattacharyya_bounds)
  >- (gvs[extreal_of_num_def, extreal_add_eq, extreal_sub_eq, extreal_mul_eq,
          extreal_pow_def, extreal_le_eq] >>
      REAL_ASM_ARITH_TAC)
  >- (gvs[extreal_of_num_def, extreal_add_eq, extreal_sub_eq, extreal_mul_eq,
          extreal_pow_def, extreal_le_eq] >>
      eq_tac >> strip_tac
      >- (‘z pow 2 = z’ by REAL_ASM_ARITH_TAC >>
          ‘z * (z - 1) = 0’ by (pop_assum mp_tac >> realLib.REAL_ARITH_TAC) >>
          fs[REAL_ENTIRE, REAL_SUB_0])
      >- (gvs[] >> REAL_ASM_ARITH_TAC)
      >- (gvs[] >> REAL_ASM_ARITH_TAC))
QED

(* Equality in Proposition 5 Eq. (29) holds iff W is a BEC
   (used directly in Proposition 7 Eq. (31)).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_5_sum_eq_bec:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    (bhattacharyya W_minus + bhattacharyya W_plus = 2 * bhattacharyya W ⇔
     is_bec W)
Proof
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac proposition_5_plus_sq >>
  drule_then strip_assume_tac proposition_5_minus_upper_bec >>
  ‘wf_bdmc W ∧ wf_bdmc W_minus’ by fs[single_step_polar_def] >>
  qpat_x_assum ‘wf_bdmc W’ (strip_assume_tac o MATCH_MP bhattacharyya_bounds) >>
  qpat_x_assum ‘wf_bdmc W_minus’
    (strip_assume_tac o MATCH_MP bhattacharyya_bounds) >>
  qpat_x_assum ‘_ ⇔ is_bec W’ (SUBST1_TAC o SYM) >>
  gvs[extreal_of_num_def, extreal_add_eq, extreal_sub_eq, extreal_mul_eq,
      extreal_pow_def] >>
  REAL_ASM_ARITH_TAC
QED

(* Extremal equivalence between Z(W) ∈ {0, 1} and I(W) ∈ {1, 0} for any B-DMC W,
   derived directly from Proposition 1 (used in Propositions 4, 5, and 7).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bdmc_extremal_z_iff_i:
  ∀W : (bool, α) memoryless_channel.
    wf_bdmc W ⇒
    (bhattacharyya W = 0 ⇔ symmetric_capacity W = 1) ∧
    (bhattacharyya W = 1 ⇔ symmetric_capacity W = 0)
Proof
  gen_tac >> strip_tac >>
  drule_then strip_assume_tac bhattacharyya_bounds >>
  drule_then strip_assume_tac symmetric_capacity_bounds >>
  ‘0 < 1 + z ∧ 1 + z ≠ 0’
    by (qpat_assum ‘0 ≤ z’ mp_tac >> realLib.REAL_ARITH_TAC) >>
  ‘0 < 2 / (1 + z)’ by (irule REAL_LT_DIV >> simp[]) >>
  ‘0 ≤ 1 - z pow 2’
    by (‘0 ≤ (1 - z) * (1 + z)’
          by (irule REAL_LE_MUL >> qpat_assum ‘0 ≤ z’ mp_tac >>
              qpat_assum ‘z ≤ 1’ mp_tac >> realLib.REAL_ARITH_TAC) >>
        pop_assum mp_tac >> realLib.REAL_ARITH_TAC) >>
  drule_then mp_tac proposition_1 >>
  simp[extreal_of_num_def, extreal_add_eq, extreal_sub_eq, extreal_div_eq,
       extreal_pow_def, extreal_logr_def, extreal_sqrt_def, extreal_le_eq] >>
  strip_tac >> conj_tac
  >- (eq_tac >> strip_tac
      >- (qpat_x_assum ‘transc$logr 2 _ ≤ (c : real)’ mp_tac >>
          qpat_x_assum ‘c ≤ 1’ mp_tac >>
          simp[logr_2_2] >> realLib.REAL_ARITH_TAC)
      >- (‘1 ≤ sqrt (1 - z pow 2)’ by gvs[] >>
          ‘1 * 1 ≤ sqrt (1 - z pow 2) * sqrt (1 - z pow 2)’
            by (irule REAL_LE_MUL2 >> simp[]) >>
          ‘sqrt (1 - z pow 2) * sqrt (1 - z pow 2) = 1 - z pow 2’
            by (ONCE_REWRITE_TAC[GSYM realTheory.POW_2] >>
                simp[realTheory.SQRT_POW_2]) >>
          ‘0 ≤ z pow 2’ by simp[REAL_LE_POW2] >>
          ‘z pow 2 = 0’
            by (ntac 3 (pop_assum mp_tac) >> realLib.REAL_ARITH_TAC) >>
          fs[REAL_POW_EQ_0]))
  >- (eq_tac >> strip_tac
      >- (qpat_x_assum ‘(c : real) ≤ sqrt _’ mp_tac >>
          qpat_x_assum ‘0 ≤ c’ mp_tac >>
          simp[realTheory.SQRT_0] >> realLib.REAL_ARITH_TAC)
      >- (gvs[] >>
          qspecl_then [‘2 / (1 + z)’, ‘1’, ‘2’] mp_tac LOGR_MONO_LE >>
          simp[logr_1, REAL_LE_LDIV_EQ] >>
          qpat_x_assum ‘z ≤ 1’ mp_tac >> realLib.REAL_ARITH_TAC))
QED

(* Companion extremal capacity characterization for Proposition 5
   (Erdal Arıkan, 2009, Section III-A, p. 7):
   Z(W_minus) = Z(W_plus) ⇔ I(W) = 1 ∨ I(W) = 0.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_5_extremal_capacity:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    (bhattacharyya W_minus = bhattacharyya W_plus ⇔
     symmetric_capacity W = 1 ∨ symmetric_capacity W = 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac proposition_5 >>
  ‘wf_bdmc W’ by fs[single_step_polar_def] >>
  drule_then strip_assume_tac bdmc_extremal_z_iff_i >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Block 4: Proposition 6 — BEC Closure & Exact Erasure Recursion            *)
(* ------------------------------------------------------------------------- *)

(* Proposition 6 (Erdal Arıkan, 2009, Section III-A, p. 7 & Appendix E,
   pp. 22-23): Closure and converse closure of Binary Erasure Channels under
   any single-step polar channel transformation, with exact erasure
   probabilities 2 * eps - eps^2 and eps^2.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_6:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    (is_bec W ⇒
     is_bec W_minus ∧
     is_bec W_plus ∧
     bec_erasure_prob W_minus =
       2 * bec_erasure_prob W - (bec_erasure_prob W) pow 2 ∧
     bec_erasure_prob W_plus = (bec_erasure_prob W) pow 2) ∧
    ((is_bec W_minus ∨ is_bec W_plus) ⇒ is_bec W)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum ‘single_step_polar W W_minus W_plus’
    (strip_assume_tac o REWRITE_RULE [single_step_polar_def]) >>
  conj_tac
  >- (strip_tac >>
      ‘is_bec W_minus’
        by (simp[is_bec_real_iff] >>
            qx_gen_tac ‘z’ >> strip_tac >>
            ‘∃y1 y2. y1 ∈ mccodomain W ∧ y2 ∈ mccodomain W ∧ z = f (y1, y2)’
              by (fs[BIJ_DEF, SURJ_DEF, EXISTS_PROD] >> metis_tac[]) >>
            gvs[] >>
            qabbrev_tac ‘a1 = real (mcchannel W F {y1})’ >>
            qabbrev_tac ‘b1 = real (mcchannel W T {y1})’ >>
            qabbrev_tac ‘a2 = real (mcchannel W F {y2})’ >>
            qabbrev_tac ‘b2 = real (mcchannel W T {y2})’ >>
            ‘(a1 * b1 = 0 ∨ a1 = b1) ∧ (a2 * b2 = 0 ∨ a2 = b2)’
              by (qpat_x_assum ‘is_bec W’ mp_tac >>
                  simp[is_bec_real_iff] >> metis_tac[]) >>
            ‘mcchannel W F {y1} = Normal a1 ∧
             mcchannel W T {y1} = Normal b1 ∧
             mcchannel W F {y2} = Normal a2 ∧
             mcchannel W T {y2} = Normal b2’
              by simp[Abbr ‘a1’, Abbr ‘b1’, Abbr ‘a2’, Abbr ‘b2’,
                      wf_bdmc_mcchannel_eq_normal] >>
            simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq,
                 extreal_add_eq, real_normal] >>
            gvs[REAL_ENTIRE] >>
            TRY (disj2_tac >> realLib.REAL_ARITH_TAC)) >>
      ‘is_bec W_plus’
        by (simp[is_bec_real_iff] >>
            qx_gen_tac ‘w’ >> strip_tac >>
            ‘∃z u1. z ∈ mccodomain W_minus ∧ w = h (z, u1)’
              by (fs[BIJ_DEF, SURJ_DEF, EXISTS_PROD] >> metis_tac[]) >>
            ‘∃y1 y2. y1 ∈ mccodomain W ∧ y2 ∈ mccodomain W ∧ z = f (y1, y2)’
              by (fs[BIJ_DEF, SURJ_DEF, EXISTS_PROD] >> metis_tac[]) >>
            gvs[] >>
            qabbrev_tac ‘a1 = real (mcchannel W F {y1})’ >>
            qabbrev_tac ‘b1 = real (mcchannel W T {y1})’ >>
            qabbrev_tac ‘a2 = real (mcchannel W F {y2})’ >>
            qabbrev_tac ‘b2 = real (mcchannel W T {y2})’ >>
            ‘(a1 * b1 = 0 ∨ a1 = b1) ∧ (a2 * b2 = 0 ∨ a2 = b2)’
              by (qpat_x_assum ‘is_bec W’ mp_tac >>
                  simp[is_bec_real_iff] >> metis_tac[]) >>
            ‘mcchannel W F {y1} = Normal a1 ∧
             mcchannel W T {y1} = Normal b1 ∧
             mcchannel W F {y2} = Normal a2 ∧
             mcchannel W T {y2} = Normal b2’
              by simp[Abbr ‘a1’, Abbr ‘b1’, Abbr ‘a2’, Abbr ‘b2’,
                      wf_bdmc_mcchannel_eq_normal] >>
            Cases_on ‘u1’ >>
            simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq,
                 real_normal] >>
            gvs[REAL_ENTIRE]) >>
      simp[] >>
      drule_then strip_assume_tac proposition_5 >>
      gvs[is_bec_bhattacharyya])
  >- (strip_tac >> simp[is_bec_real_iff] >>
      qx_gen_tac ‘y1’ >> strip_tac >>
      qpat_assum ‘wf_bdmc W’
        (strip_assume_tac o MATCH_MP wf_bdmc_real_pmf_safe) >>
      ‘f (y1, y1) ∈ mccodomain W_minus’
        by (fs[BIJ_DEF, INJ_DEF] >> first_x_assum irule >> simp[]) >>
      ‘h (f (y1, y1), F) ∈ mccodomain W_plus’
        by (fs[BIJ_DEF, INJ_DEF] >> first_x_assum irule >> simp[]) >>
      qabbrev_tac ‘a1 = real (mcchannel W F {y1})’ >>
      qabbrev_tac ‘b1 = real (mcchannel W T {y1})’ >>
      ‘0 ≤ a1 ∧ 0 ≤ b1’
        by (simp[Abbr ‘a1’, Abbr ‘b1’] >> metis_tac[]) >>
      ‘mcchannel W F {y1} = Normal a1 ∧ mcchannel W T {y1} = Normal b1’
        by simp[Abbr ‘a1’, Abbr ‘b1’, wf_bdmc_mcchannel_eq_normal]
      >- (qpat_x_assum ‘is_bec W_minus’ mp_tac >>
          simp[is_bec_def] >>
          disch_then (drule_then mp_tac) >>
          simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq,
               extreal_add_eq, extreal_11] >>
          strip_tac
          >- (‘0 ≤ a1 pow 2 ∧ 0 ≤ b1 pow 2’ by simp[REAL_LE_POW2] >>
              ‘a1 pow 2 = 0’ by REAL_ASM_ARITH_TAC >>
              gvs[REAL_POW_EQ_0])
          >- (‘a1 * b1 = 0’ by REAL_ASM_ARITH_TAC >>
              gvs[REAL_ENTIRE])
          >- (disj2_tac >> pop_assum mp_tac >>
              (fn (asl, w) => ACCEPT_TAC (RealField.REAL_RING w) (asl, w))))
      >- (qpat_x_assum ‘is_bec W_plus’ mp_tac >>
          simp[is_bec_def] >>
          disch_then (drule_then mp_tac) >>
          simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq, extreal_11] >>
          strip_tac
          >- simp[]
          >- simp[]
          >- (‘(a1 - b1) * (a1 + b1) = 0’
                by (pop_assum mp_tac >>
                    (fn (asl, w) => ACCEPT_TAC (RealField.REAL_RING w) (asl, w))) >>
              fs[REAL_ENTIRE] >>
              disj2_tac >> REAL_ASM_ARITH_TAC)))
QED

(* Specialization of Proposition 6 to concrete binary_erasure_channel p.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_6_binary_erasure_channel:
  ∀p (W_minus : (bool, γ) memoryless_channel)
     (W_plus : (bool, δ) memoryless_channel).
    0 ≤ p ∧ p ≤ 1 ∧
    single_step_polar (binary_erasure_channel p) W_minus W_plus ⇒
    is_bec W_minus ∧
    is_bec W_plus ∧
    bec_erasure_prob W_minus = 2 * p - p pow 2 ∧
    bec_erasure_prob W_plus = p pow 2
Proof
  rpt strip_tac >>
  drule proposition_6 >>
  simp[is_bec_binary_erasure_channel, bec_erasure_prob_binary_erasure_channel]
QED

(* ------------------------------------------------------------------------- *)
(* Block 5: Base N = 1 Simp Bridges, Tree Invariants & Proposition 7         *)
(* ------------------------------------------------------------------------- *)

(* Left and right multiplication by Normal 1 on all extreals.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem normal_1_mul[simp]:
  ∀x : extreal. Normal 1 * x = x ∧ x * Normal 1 = x
Proof
  Cases >> simp[extreal_mul_def]
QED

(* Well-formedness of the N = 1, i = 0 base split channel.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_split_channel_1_0[simp]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒ wf_bdmc (split_channel W 1 0)
Proof
  rpt strip_tac >>
  qspecl_then [‘W’, ‘0’, ‘0’] mp_tac wf_bdmc_split_channel >>
  simp[]
QED

(* Simp export for base N = 1 Bhattacharyya identity Z(W_1^(0)) = Z(W).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bhattacharyya_split_channel_1_0_simp[simp]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒ bhattacharyya (split_channel W 1 0) = bhattacharyya W
Proof
  rw[bhattacharyya_split_channel_1_0]
QED

(* Base N = 1 Bhattacharyya identity directly under is_bec W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bhattacharyya_split_channel_1_0_bec[simp]:
  ∀W : (bool, β) memoryless_channel.
    is_bec W ⇒ bhattacharyya (split_channel W 1 0) = bhattacharyya W
Proof
  rw[is_bec_def, bhattacharyya_split_channel_1_0]
QED

(* Simp export for base N = 1 symmetric capacity identity I(W_1^(0)) = I(W).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem symmetric_capacity_split_channel_1_0_simp[simp]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    symmetric_capacity (split_channel W 1 0) = symmetric_capacity W
Proof
  rw[symmetric_capacity_split_channel_1_0]
QED

(* Base N = 1 symmetric capacity identity directly under is_bec W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem symmetric_capacity_split_channel_1_0_bec[simp]:
  ∀W : (bool, β) memoryless_channel.
    is_bec W ⇒
    symmetric_capacity (split_channel W 1 0) = symmetric_capacity W
Proof
  rw[is_bec_def, symmetric_capacity_split_channel_1_0]
QED

(* Simp export for base N = 1 BEC equivalence is_bec (W_1^(0)) <=> is_bec W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_bec_split_channel_1_0_simp[simp]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒ (is_bec (split_channel W 1 0) ⇔ is_bec W)
Proof
  rw[is_bec_split_channel_1_0]
QED

(* Base N = 1 BEC closure directly under is_bec W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_bec_split_channel_1_0_bec[simp]:
  ∀W : (bool, β) memoryless_channel.
    is_bec W ⇒ is_bec (split_channel W 1 0)
Proof
  rpt strip_tac >>
  ‘wf_bdmc W’ by fs[is_bec_def] >>
  simp[is_bec_split_channel_1_0]
QED

(* Simp export for base N = 1 erasure probability identity eps(W_1^(0)) = eps(W).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_erasure_prob_split_channel_1_0_simp[simp]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒ bec_erasure_prob (split_channel W 1 0) = bec_erasure_prob W
Proof
  rw[bec_erasure_prob_split_channel_1_0]
QED

(* Base N = 1 erasure probability identity directly under is_bec W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_erasure_prob_split_channel_1_0_bec[simp]:
  ∀W : (bool, β) memoryless_channel.
    is_bec W ⇒ bec_erasure_prob (split_channel W 1 0) = bec_erasure_prob W
Proof
  rw[is_bec_def, bec_erasure_prob_split_channel_1_0]
QED

(* Extremal parameter characterizations from Proposition 1:
   I(C) = 0 <=> Z(C) = 1 and I(C) = 1 <=> Z(C) = 0 for any wf_bdmc C.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bdmc_extremal_capacity_bhattacharyya:
  ∀C : (bool, β) memoryless_channel.
    wf_bdmc C ⇒
    (symmetric_capacity C = 0 ⇔ bhattacharyya C = 1) ∧
    (symmetric_capacity C = 1 ⇔ bhattacharyya C = 0)
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac bdmc_extremal_z_iff_i >>
  metis_tac[]
QED

(* Single-step invariance of extremal capacity/Bhattacharyya values {0, 1}.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem single_step_polar_extremal_iff[local]:
  ∀(W : (bool, α) memoryless_channel)
   (W_minus : (bool, γ) memoryless_channel)
   (W_plus : (bool, δ) memoryless_channel).
    single_step_polar W W_minus W_plus ⇒
    (symmetric_capacity W_minus = 0 ⇔ symmetric_capacity W = 0) ∧
    (symmetric_capacity W_minus = 1 ⇔ symmetric_capacity W = 1) ∧
    (symmetric_capacity W_plus = 0 ⇔ symmetric_capacity W = 0) ∧
    (symmetric_capacity W_plus = 1 ⇔ symmetric_capacity W = 1)
Proof
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac proposition_5 >>
  ‘wf_bdmc W ∧ wf_bdmc W_minus ∧ wf_bdmc W_plus’
    by fs[single_step_polar_def] >>
  qpat_assum ‘wf_bdmc W’
    (fn th => REWRITE_TAC [GSYM (MATCH_MP bdmc_extremal_z_iff_i th)]) >>
  qpat_assum ‘wf_bdmc W_minus’
    (fn th => REWRITE_TAC [GSYM (MATCH_MP bdmc_extremal_z_iff_i th)]) >>
  qpat_assum ‘wf_bdmc W_plus’
    (fn th => REWRITE_TAC [GSYM (MATCH_MP bdmc_extremal_z_iff_i th)]) >>
  qpat_x_assum ‘_ ⇔ is_bec W’ kall_tac >>
  qpat_x_assum ‘bhattacharyya W_minus = bhattacharyya W_plus ⇔ _’ kall_tac >>
  qpat_assum ‘wf_bdmc W’
    (qx_choose_then ‘z’ strip_assume_tac o
     CONJUNCT2 o CONJUNCT2 o MATCH_MP bhattacharyya_bounds) >>
  qpat_assum ‘wf_bdmc W_minus’
    (qx_choose_then ‘zm’ strip_assume_tac o
     CONJUNCT2 o CONJUNCT2 o MATCH_MP bhattacharyya_bounds) >>
  qpat_assum ‘wf_bdmc W_plus’
    (qx_choose_then ‘zp’ strip_assume_tac o
     CONJUNCT2 o CONJUNCT2 o MATCH_MP bhattacharyya_bounds) >>
  gvs[extreal_of_num_def, extreal_add_eq, extreal_sub_eq, extreal_mul_eq,
      extreal_pow_def, extreal_le_eq, extreal_11, REAL_POW_EQ_0] >>
  rpt conj_tac
  >- (eq_tac >> strip_tac >> gvs[]
      >- (‘(1 - z) * (1 - z) ≤ 0’
            by (qpat_x_assum ‘1 ≤ 2 * z - z pow 2’ mp_tac >>
                realLib.REAL_ARITH_TAC) >>
          ‘0 ≤ (1 - z) * (1 - z)’
            by (irule REAL_LE_MUL >> REAL_ASM_ARITH_TAC) >>
          ‘(1 - z) * (1 - z) = 0’ by REAL_ASM_ARITH_TAC >>
          fs[REAL_ENTIRE] >> REAL_ASM_ARITH_TAC)
      >- REAL_ASM_ARITH_TAC)
  >- (eq_tac >> strip_tac >> gvs[] >> REAL_ASM_ARITH_TAC)
  >- (eq_tac >> strip_tac >> gvs[] >>
      ‘(z - 1) * (z + 1) = 0’
        by (qpat_x_assum ‘z pow 2 = 1’ mp_tac >>
            (fn (asl, w) => ACCEPT_TAC (RealField.REAL_RING w) (asl, w))) >>
      fs[REAL_ENTIRE] >> REAL_ASM_ARITH_TAC)
QED

(* Tree-wide BEC and extremal-capacity invariance across all split channels
   W_{2^n}^(i) (Erdal Arıkan, 2009, Section III-B, p. 8).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem split_channel_invariants:
  ∀(W : (bool, β) memoryless_channel) n i.
    wf_bdmc W ∧ i < 2 ** n ⇒
    (is_bec (split_channel W (2 ** n) i) ⇔ is_bec W) ∧
    (symmetric_capacity (split_channel W (2 ** n) i) = 0 ⇔
     symmetric_capacity W = 0) ∧
    (symmetric_capacity (split_channel W (2 ** n) i) = 1 ⇔
     symmetric_capacity W = 1)
Proof
  gen_tac >> Induct_on ‘n’
  >- (rw[] >> ‘i = 0’ by decide_tac >> simp[])
  >- (qx_gen_tac ‘k’ >> strip_tac >>
      gvs[EXP] >>
      ‘k = 2 * (k DIV 2) ∨ k = 2 * (k DIV 2) + 1’
        by (qspec_then ‘2’ mp_tac DIVISION >> impl_tac >- decide_tac >>
            disch_then (qspec_then ‘k’ strip_assume_tac) >> decide_tac) >>
      ‘k DIV 2 < 2 ** n’ by decide_tac >>
      first_x_assum (qspec_then ‘k DIV 2’ mp_tac) >> simp[] >> strip_tac >>
      qspecl_then [‘W’, ‘n’, ‘k DIV 2’] mp_tac proposition_3_single_step >>
      simp[] >> strip_tac >>
      drule proposition_6 >>
      drule single_step_polar_extremal_iff >>
      rpt strip_tac >>
      gvs[] >> metis_tac[])
QED

(* Disjoint even/odd partition of count (2 * N).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem count_double_even_odd_partition[local]:
  ∀N : num.
    count (2 * N) =
      IMAGE (λi. 2 * i) (count N) ∪ IMAGE (λi. 2 * i + 1) (count N) ∧
    DISJOINT (IMAGE (λi. 2 * i) (count N))
             (IMAGE (λi. 2 * i + 1) (count N)) ∧
    INJ (λi. 2 * i) (count N) 𝕌(:num) ∧
    INJ (λi. 2 * i + 1) (count N) 𝕌(:num)
Proof
  gen_tac >> rpt conj_tac
  >- (rw[Once EXTENSION, EQ_IMP_THM] >>
      qspec_then ‘2’ mp_tac DIVISION >> impl_tac >- decide_tac >>
      disch_then (qspec_then ‘x’ strip_assume_tac) >>
      ‘x MOD 2 = 0 ∨ x MOD 2 = 1’ by decide_tac
      >- (disj1_tac >> qexists_tac ‘x DIV 2’ >> decide_tac)
      >- (disj2_tac >> qexists_tac ‘x DIV 2’ >> decide_tac))
  >- (PURE_REWRITE_TAC[IN_DISJOINT] >> CCONTR_TAC >> gvs[] >>
      ‘EVEN (2 * i)’ by simp[EVEN_DOUBLE] >>
      qpat_x_assum ‘_ = 2 * i’ (SUBST_ALL_TAC o SYM) >>
      gvs[EVEN_ADD, EVEN_DOUBLE])
  >- rw[INJ_DEF]
  >- rw[INJ_DEF]
QED

(* Even/odd pairing identity for REAL_SUM_IMAGE over count (2 * N).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_COUNT_DOUBLE[local]:
  ∀N (f : num -> real).
    REAL_SUM_IMAGE f (count (2 * N)) =
    REAL_SUM_IMAGE (λi. f (2 * i) + f (2 * i + 1)) (count N)
Proof
  rpt gen_tac >>
  qspec_then ‘N’ strip_assume_tac count_double_even_odd_partition >>
  ‘REAL_SUM_IMAGE f (count (2 * N)) =
   REAL_SUM_IMAGE f
     (IMAGE (λi. 2 * i) (count N) ∪ IMAGE (λi. 2 * i + 1) (count N))’
    by metis_tac[] >>
  pop_assum SUBST1_TAC >>
  DEP_REWRITE_TAC[REAL_SUM_IMAGE_DISJOINT_UNION] >>
  simp[IMAGE_FINITE] >>
  ‘INJ (λi. 2 * i) (count N) (IMAGE (λi. 2 * i) (count N)) ∧
   INJ (λi. 2 * i + 1) (count N) (IMAGE (λi. 2 * i + 1) (count N))’
    by rw[INJ_DEF] >>
  simp[REAL_SUM_IMAGE_IMAGE, GSYM REAL_SUM_IMAGE_ADD] >>
  irule REAL_SUM_IMAGE_EQ >> simp[o_DEF]
QED

(* Local stepwise Proposition 7 relations (Eqs. 30-35 + equality conditions in W).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_7_step_local[local]:
  ∀(W : (bool, β) memoryless_channel) n i.
    wf_bdmc W ∧ i < 2 ** n ⇒
    symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i)) +
      symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i + 1)) =
      2 * symmetric_capacity (split_channel W (2 ** n) i) ∧
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) +
      bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) ≤
      2 * bhattacharyya (split_channel W (2 ** n) i) ∧
    (bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) +
       bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) =
       2 * bhattacharyya (split_channel W (2 ** n) i) ⇔ is_bec W) ∧
    0 ≤ symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i)) ∧
    symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i)) ≤
      symmetric_capacity (split_channel W (2 ** n) i) ∧
    symmetric_capacity (split_channel W (2 ** n) i) ≤
      symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i + 1)) ∧
    symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i + 1)) ≤ 1 ∧
    (symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i)) =
       symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i + 1)) ⇔
     symmetric_capacity W = 0 ∨ symmetric_capacity W = 1) ∧
    0 ≤ bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) ∧
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) ≤
      bhattacharyya (split_channel W (2 ** n) i) ∧
    bhattacharyya (split_channel W (2 ** n) i) ≤
      bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) ∧
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) ≤ 1 ∧
    (bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) =
       bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) ⇔
     symmetric_capacity W = 0 ∨ symmetric_capacity W = 1) ∧
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) ≤
      2 * bhattacharyya (split_channel W (2 ** n) i) -
      (bhattacharyya (split_channel W (2 ** n) i)) pow 2 ∧
    (bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) =
       2 * bhattacharyya (split_channel W (2 ** n) i) -
       (bhattacharyya (split_channel W (2 ** n) i)) pow 2 ⇔ is_bec W) ∧
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) =
      (bhattacharyya (split_channel W (2 ** n) i)) pow 2
Proof
  rpt gen_tac >> strip_tac >>
  drule_all proposition_3_single_step >> strip_tac >>
  drule_then strip_assume_tac proposition_4 >>
  drule_then strip_assume_tac proposition_5 >>
  drule_then assume_tac proposition_5_sum_eq_bec >>
  drule_then assume_tac proposition_5_extremal_capacity >>
  drule_all_then strip_assume_tac split_channel_invariants >>
  ‘wf_bdmc (split_channel W (2 * 2 ** n) (2 * i)) ∧
   wf_bdmc (split_channel W (2 * 2 ** n) (2 * i + 1))’
    by fs[single_step_polar_def] >>
  qspecl_then [‘split_channel W (2 * 2 ** n) (2 * i)’] mp_tac
    bhattacharyya_bounds >>
  qspecl_then [‘split_channel W (2 * 2 ** n) (2 * i + 1)’] mp_tac
    bhattacharyya_bounds >>
  simp[] >> ntac 2 strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]
QED

(* Normal real-sum representation of level-2^m capacity and Bhattacharyya sums.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem split_channel_sums_eq_normal[local]:
  ∀(W : (bool, β) memoryless_channel) m.
    wf_bdmc W ⇒
    ∑ (λi. symmetric_capacity (split_channel W (2 ** m) i)) (count (2 ** m)) =
      Normal (REAL_SUM_IMAGE
                (λi. real (symmetric_capacity (split_channel W (2 ** m) i)))
                (count (2 ** m))) ∧
    ∑ (λi. bhattacharyya (split_channel W (2 ** m) i)) (count (2 ** m)) =
      Normal (REAL_SUM_IMAGE
                (λi. real (bhattacharyya (split_channel W (2 ** m) i)))
                (count (2 ** m)))
Proof
  rpt strip_tac >> simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
  irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
  qx_gen_tac ‘i’ >> strip_tac >>
  qspecl_then [‘W’, ‘m’, ‘i’] mp_tac wf_bdmc_split_channel >> simp[] >>
  strip_tac
  >- (drule symmetric_capacity_bounds >> strip_tac >> simp[real_normal])
  >- (drule bhattacharyya_bounds >> strip_tac >> simp[real_normal])
QED

(* Real-valued single-step capacity conservation and Bhattacharyya relations
   across level 2^m -> 2 * 2^m.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem split_channel_real_step[local]:
  ∀(W : (bool, β) memoryless_channel) m i.
    wf_bdmc W ∧ i < 2 ** m ⇒
    real (symmetric_capacity (split_channel W (2 * 2 ** m) (2 * i))) +
      real (symmetric_capacity (split_channel W (2 * 2 ** m) (2 * i + 1))) =
      2 * real (symmetric_capacity (split_channel W (2 ** m) i)) ∧
    real (bhattacharyya (split_channel W (2 * 2 ** m) (2 * i))) +
      real (bhattacharyya (split_channel W (2 * 2 ** m) (2 * i + 1))) ≤
      2 * real (bhattacharyya (split_channel W (2 ** m) i)) ∧
    (real (bhattacharyya (split_channel W (2 * 2 ** m) (2 * i))) +
       real (bhattacharyya (split_channel W (2 * 2 ** m) (2 * i + 1))) =
       2 * real (bhattacharyya (split_channel W (2 ** m) i)) ⇔ is_bec W)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [‘W’, ‘m’, ‘i’] mp_tac proposition_7_step_local >>
  qspecl_then [‘W’, ‘m’, ‘i’] mp_tac wf_bdmc_split_channel >>
  qspecl_then [‘W’, ‘SUC m’, ‘2 * i’] mp_tac wf_bdmc_split_channel >>
  qspecl_then [‘W’, ‘SUC m’, ‘2 * i + 1’] mp_tac wf_bdmc_split_channel >>
  simp[EXP] >> ntac 4 strip_tac >>
  qspecl_then [‘split_channel W (2 ** m) i’] mp_tac symmetric_capacity_bounds >>
  qspecl_then [‘split_channel W (2 * 2 ** m) (2 * i)’] mp_tac
    symmetric_capacity_bounds >>
  qspecl_then [‘split_channel W (2 * 2 ** m) (2 * i + 1)’] mp_tac
    symmetric_capacity_bounds >>
  qspecl_then [‘split_channel W (2 ** m) i’] mp_tac bhattacharyya_bounds >>
  qspecl_then [‘split_channel W (2 * 2 ** m) (2 * i)’] mp_tac
    bhattacharyya_bounds >>
  qspecl_then [‘split_channel W (2 * 2 ** m) (2 * i + 1)’] mp_tac
    bhattacharyya_bounds >>
  simp[] >> ntac 6 strip_tac >>
  gvs[extreal_of_num_def, extreal_add_eq, extreal_mul_eq, extreal_le_eq,
      extreal_11, real_normal]
QED

(* Proposition 7, Eq. (36) (Erdal Arıkan, 2009, Section III-B, p. 7):
   Cumulative symmetric capacity conservation across all 2^n split channels.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_7_capacity_sum:
  ∀(W : (bool, β) memoryless_channel) n.
    wf_bdmc W ⇒
    ∑ (λi. symmetric_capacity (split_channel W (2 ** n) i)) (count (2 ** n)) =
    &(2 ** n) * symmetric_capacity W
Proof
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac symmetric_capacity_bounds >>
  simp[split_channel_sums_eq_normal, extreal_of_num_def, extreal_mul_eq,
       extreal_11] >>
  Induct_on ‘n’
  >- (‘count 1 = {0}’ by (rw[Once EXTENSION] >> decide_tac) >>
      simp[REAL_SUM_IMAGE_SING, real_normal])
  >- (simp[EXP, REAL_SUM_IMAGE_COUNT_DOUBLE] >>
      ‘REAL_SUM_IMAGE
         (λi. real (symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i))) +
              real (symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i + 1))))
         (count (2 ** n)) =
       REAL_SUM_IMAGE
         (λi. 2 * real (symmetric_capacity (split_channel W (2 ** n) i)))
         (count (2 ** n))’
        by (irule REAL_SUM_IMAGE_EQ >> simp[split_channel_real_step]) >>
      pop_assum SUBST1_TAC >>
      simp[REAL_SUM_IMAGE_CMUL] >>
      ONCE_REWRITE_TAC[GSYM REAL_MUL] >>
      REAL_ASM_ARITH_TAC)
QED

(* Proposition 7, Eq. (37) (Erdal Arıkan, 2009, Section III-B, p. 7):
   Cumulative Bhattacharyya upper bound across all 2^n split channels.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_7_bhattacharyya_sum:
  ∀(W : (bool, β) memoryless_channel) n.
    wf_bdmc W ⇒
    ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) (count (2 ** n)) ≤
    &(2 ** n) * bhattacharyya W
Proof
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac bhattacharyya_bounds >>
  simp[split_channel_sums_eq_normal, extreal_of_num_def, extreal_mul_eq,
       extreal_le_eq] >>
  Induct_on ‘n’
  >- (‘count 1 = {0}’ by (rw[Once EXTENSION] >> decide_tac) >>
      simp[REAL_SUM_IMAGE_SING, real_normal])
  >- (simp[EXP, REAL_SUM_IMAGE_COUNT_DOUBLE] >>
      ‘REAL_SUM_IMAGE
         (λi. real (bhattacharyya (split_channel W (2 * 2 ** n) (2 * i))) +
              real (bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1))))
         (count (2 ** n)) ≤
       REAL_SUM_IMAGE
         (λi. 2 * real (bhattacharyya (split_channel W (2 ** n) i)))
         (count (2 ** n))’
        by (irule REAL_SUM_IMAGE_MONO >> simp[split_channel_real_step]) >>
      gvs[REAL_SUM_IMAGE_CMUL] >>
      ONCE_REWRITE_TAC[GSYM REAL_MUL] >>
      REAL_ASM_ARITH_TAC)
QED

(* Forward cumulative Bhattacharyya sum equality for all n >= 0 when is_bec W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_7_bhattacharyya_sum_bec[local]:
  ∀(W : (bool, β) memoryless_channel) n.
    is_bec W ⇒
    ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) (count (2 ** n)) =
    &(2 ** n) * bhattacharyya W
Proof
  rpt gen_tac >> strip_tac >>
  ‘wf_bdmc W’ by fs[is_bec_def] >>
  drule_then strip_assume_tac bhattacharyya_bounds >>
  simp[split_channel_sums_eq_normal, extreal_of_num_def, extreal_mul_eq,
       extreal_11] >>
  Induct_on ‘n’
  >- (‘count 1 = {0}’ by (rw[Once EXTENSION] >> decide_tac) >>
      simp[REAL_SUM_IMAGE_SING, real_normal])
  >- (simp[EXP, REAL_SUM_IMAGE_COUNT_DOUBLE] >>
      ‘REAL_SUM_IMAGE
         (λi. real (bhattacharyya (split_channel W (2 * 2 ** n) (2 * i))) +
              real (bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1))))
         (count (2 ** n)) =
       REAL_SUM_IMAGE
         (λi. 2 * real (bhattacharyya (split_channel W (2 ** n) i)))
         (count (2 ** n))’
        by (irule REAL_SUM_IMAGE_EQ >> simp[split_channel_real_step]) >>
      pop_assum SUBST1_TAC >>
      simp[REAL_SUM_IMAGE_CMUL] >>
      ONCE_REWRITE_TAC[GSYM REAL_MUL] >>
      REAL_ASM_ARITH_TAC)
QED

(* Proposition 7, Eq. (37) BEC Equality Characterization:
   Forward sum equality holds for all n >= 0 when is_bec W; bidirectional
   sum equality <=> is_bec W holds for all 1 <= n (at n = 0, N = 1, equality
   holds trivially for every B-DMC).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_7_bhattacharyya_sum_eq_iff:
  ∀(W : (bool, β) memoryless_channel) n.
    wf_bdmc W ⇒
    (is_bec W ⇒
     ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) (count (2 ** n)) =
     &(2 ** n) * bhattacharyya W) ∧
    (1 ≤ n ⇒
     (∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) (count (2 ** n)) =
      &(2 ** n) * bhattacharyya W ⇔ is_bec W))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- rw[proposition_7_bhattacharyya_sum_bec]
  >- (strip_tac >> eq_tac
      >- (strip_tac >>
          ‘∃m. n = SUC m’ by (Cases_on ‘n’ >> gvs[]) >>
          drule_then strip_assume_tac bhattacharyya_bounds >>
          qabbrev_tac
            ‘f = λi. real (bhattacharyya (split_channel W (2 * 2 ** m) (2 * i))) +
                     real (bhattacharyya (split_channel W (2 * 2 ** m) (2 * i + 1)))’ >>
          qabbrev_tac
            ‘g = λi. 2 * real (bhattacharyya (split_channel W (2 ** m) i))’ >>
          ‘∀i. i ∈ count (2 ** m) ⇒ f i ≤ g i’
            by simp[Abbr ‘f’, Abbr ‘g’, split_channel_real_step] >>
          ‘REAL_SUM_IMAGE f (count (2 ** m)) ≤ REAL_SUM_IMAGE g (count (2 ** m))’
            by (irule REAL_SUM_IMAGE_MONO >> simp[]) >>
          ‘REAL_SUM_IMAGE f (count (2 ** m)) = &(2 * 2 ** m) * z’
            by (qpat_x_assum ‘∑ _ (count (2 ** n)) = _’ mp_tac >>
                gvs[split_channel_sums_eq_normal, EXP,
                    REAL_SUM_IMAGE_COUNT_DOUBLE, Abbr ‘f’,
                    extreal_of_num_def, extreal_mul_eq, extreal_11]) >>
          ‘REAL_SUM_IMAGE g (count (2 ** m)) ≤ &(2 * 2 ** m) * z’
            by (drule_then (qspec_then ‘m’ mp_tac)
                  proposition_7_bhattacharyya_sum >>
                simp[split_channel_sums_eq_normal, Abbr ‘g’,
                     REAL_SUM_IMAGE_CMUL, extreal_of_num_def, extreal_mul_eq,
                     extreal_le_eq] >>
                ONCE_REWRITE_TAC[GSYM REAL_MUL] >>
                REAL_ASM_ARITH_TAC) >>
          ‘REAL_SUM_IMAGE f (count (2 ** m)) = REAL_SUM_IMAGE g (count (2 ** m))’
            by REAL_ASM_ARITH_TAC >>
          ‘f 0 = g 0’
            by (qspecl_then [‘count (2 ** m)’, ‘f’, ‘g’] mp_tac
                  REAL_SUM_IMAGE_EQ_IFF_POINTWISE_LE >>
                simp[ZERO_LESS_EXP]) >>
          ‘0 < 2 ** m’ by simp[ZERO_LESS_EXP] >>
          qspecl_then [‘W’, ‘m’, ‘0’] mp_tac split_channel_real_step >>
          qpat_x_assum ‘f 0 = g 0’ mp_tac >>
          simp[Abbr ‘f’, Abbr ‘g’])
      >- rw[proposition_7_bhattacharyya_sum_bec])
QED

(* Proposition 7, Eq. (38) (Erdal Arıkan, 2009, Section III-B, p. 8):
   Multi-step BEC closure and exact Bhattacharyya recursion across split channels.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_7_bec_recursion:
  ∀(W : (bool, β) memoryless_channel) n i.
    is_bec W ∧ i < 2 ** n ⇒
    is_bec (split_channel W (2 ** n) i) ∧
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) =
      2 * bhattacharyya (split_channel W (2 ** n) i) -
      (bhattacharyya (split_channel W (2 ** n) i)) pow 2 ∧
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) =
      (bhattacharyya (split_channel W (2 ** n) i)) pow 2
Proof
  rpt strip_tac >>
  ‘wf_bdmc W’ by fs[is_bec_def]
  >- (drule_all split_channel_invariants >> simp[])
  >- (drule_all proposition_7_step_local >> simp[])
  >- (drule_all proposition_7_step_local >> simp[])
QED

(* Proposition 7 / Section I-B Eq. (6) (Erdal Arıkan, 2009, p. 2 & p. 8):
   Exact symmetric capacity recursion for BEC split channels.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_7_bec_capacity_recursion:
  ∀(W : (bool, β) memoryless_channel) n i.
    is_bec W ∧ i < 2 ** n ⇒
    symmetric_capacity (split_channel W 1 0) = 1 - bec_erasure_prob W ∧
    symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i)) =
      (symmetric_capacity (split_channel W (2 ** n) i)) pow 2 ∧
    symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i + 1)) =
      2 * symmetric_capacity (split_channel W (2 ** n) i) -
      (symmetric_capacity (split_channel W (2 ** n) i)) pow 2
Proof
  rpt strip_tac
  >- simp[is_bec_symmetric_capacity]
  >- (‘wf_bdmc W’ by fs[is_bec_def] >>
      ‘2 * i < 2 ** SUC n’ by simp[EXP] >>
      drule_then (qspecl_then [‘n’, ‘i’] mp_tac) split_channel_invariants >>
      drule_then (qspecl_then [‘SUC n’, ‘2 * i’] mp_tac)
        split_channel_invariants >>
      simp[EXP] >> ntac 2 strip_tac >>
      qspecl_then [‘W’, ‘n’, ‘i’] mp_tac proposition_7_bec_recursion >>
      simp[] >> strip_tac >>
      drule_then (qspecl_then [‘n’, ‘i’] assume_tac) wf_bdmc_split_channel >>
      qspecl_then [‘split_channel W (2 ** n) i’] mp_tac bhattacharyya_bounds >>
      simp[] >> strip_tac >>
      simp[is_bec_symmetric_capacity, GSYM is_bec_bhattacharyya] >>
      gvs[extreal_of_num_def, extreal_sub_eq, extreal_mul_eq, extreal_pow_def,
          extreal_11] >>
      realLib.REAL_ARITH_TAC)
  >- (‘wf_bdmc W’ by fs[is_bec_def] >>
      ‘2 * i + 1 < 2 ** SUC n’ by simp[EXP] >>
      drule_then (qspecl_then [‘n’, ‘i’] mp_tac) split_channel_invariants >>
      drule_then (qspecl_then [‘SUC n’, ‘2 * i + 1’] mp_tac)
        split_channel_invariants >>
      simp[EXP] >> ntac 2 strip_tac >>
      qspecl_then [‘W’, ‘n’, ‘i’] mp_tac proposition_7_bec_recursion >>
      simp[] >> strip_tac >>
      drule_then (qspecl_then [‘n’, ‘i’] assume_tac) wf_bdmc_split_channel >>
      qspecl_then [‘split_channel W (2 ** n) i’] mp_tac bhattacharyya_bounds >>
      simp[] >> strip_tac >>
      simp[is_bec_symmetric_capacity, GSYM is_bec_bhattacharyya] >>
      gvs[extreal_of_num_def, extreal_sub_eq, extreal_mul_eq, extreal_pow_def,
          extreal_11] >>
      realLib.REAL_ARITH_TAC)
QED

(* Master Proposition 7 (Erdal Arıkan, 2009, Section III-B, Eqs. (30)-(37)):
   All 8 local and cumulative conservation, ordering, recursive reliability,
   and equality characterizations for split_channel W (2 ** n) i.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_7:
  ∀(W : (bool, β) memoryless_channel) n i.
    wf_bdmc W ∧ i < 2 ** n ⇒
    (* Eq. (30): Local rate conservation *)
    symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i)) +
      symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i + 1)) =
      2 * symmetric_capacity (split_channel W (2 ** n) i) ∧
    (* Eq. (31) + BEC iff: Local reliability improvement *)
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) +
      bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) ≤
      2 * bhattacharyya (split_channel W (2 ** n) i) ∧
    (bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) +
       bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) =
       2 * bhattacharyya (split_channel W (2 ** n) i) ⇔ is_bec W) ∧
    (* Eq. (32) + extremal iff: Centrifugal capacity ordering *)
    symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i)) ≤
      symmetric_capacity (split_channel W (2 ** n) i) ∧
    symmetric_capacity (split_channel W (2 ** n) i) ≤
      symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i + 1)) ∧
    (symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i)) =
       symmetric_capacity (split_channel W (2 * 2 ** n) (2 * i + 1)) ⇔
     symmetric_capacity W = 0 ∨ symmetric_capacity W = 1) ∧
    (* Eq. (33) + extremal iff: Centrifugal Bhattacharyya ordering *)
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) ≤
      bhattacharyya (split_channel W (2 ** n) i) ∧
    bhattacharyya (split_channel W (2 ** n) i) ≤
      bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) ∧
    (bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) =
       bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) ⇔
     symmetric_capacity W = 0 ∨ symmetric_capacity W = 1) ∧
    (* Eq. (34) + BEC iff & Eq. (35): Recursive reliability bounds *)
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) ≤
      2 * bhattacharyya (split_channel W (2 ** n) i) -
      (bhattacharyya (split_channel W (2 ** n) i)) pow 2 ∧
    (bhattacharyya (split_channel W (2 * 2 ** n) (2 * i)) =
       2 * bhattacharyya (split_channel W (2 ** n) i) -
       (bhattacharyya (split_channel W (2 ** n) i)) pow 2 ⇔ is_bec W) ∧
    bhattacharyya (split_channel W (2 * 2 ** n) (2 * i + 1)) =
      (bhattacharyya (split_channel W (2 ** n) i)) pow 2 ∧
    (* Eq. (36): Cumulative rate conservation *)
    ∑ (λj. symmetric_capacity (split_channel W (2 ** n) j)) (count (2 ** n)) =
      &(2 ** n) * symmetric_capacity W ∧
    (* Eq. (37) + 1 <= n BEC iff: Cumulative reliability improvement *)
    ∑ (λj. bhattacharyya (split_channel W (2 ** n) j)) (count (2 ** n)) ≤
      &(2 ** n) * bhattacharyya W ∧
    (1 ≤ n ⇒
     (∑ (λj. bhattacharyya (split_channel W (2 ** n) j)) (count (2 ** n)) =
      &(2 ** n) * bhattacharyya W ⇔ is_bec W))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac proposition_7_step_local >>
  drule_then (qspec_then ‘n’ assume_tac) proposition_7_capacity_sum >>
  drule_then (qspec_then ‘n’ assume_tac) proposition_7_bhattacharyya_sum >>
  drule_then (qspec_then ‘n’ strip_assume_tac)
    proposition_7_bhattacharyya_sum_eq_iff >>
  simp[]
QED

(* Elementary characterization: any positive divisor of 2^k is a power of 2.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem divisor_of_two_exp_is_pow2[local]:
  ∀k N. 0 < N ∧ (2 ** k) MOD N = 0 ⇒ ∃n. N = 2 ** n
Proof
  Induct_on ‘k’
  >- (rpt strip_tac >>
      Cases_on ‘N = 1’ >- (qexists_tac ‘0’ >> simp[]) >>
      ‘1 < N ∧ 2 ** 0 = 1’ by simp[] >>
      ‘1 MOD N = 1’ by simp[LESS_MOD] >> gvs[])
  >- (rpt strip_tac >>
      qspec_then ‘N’ mp_tac DIVISION >> simp[] >>
      disch_then (qspec_then ‘2 ** SUC k’ strip_assume_tac) >>
      qabbrev_tac ‘q = (2 ** SUC k) DIV N’ >>
      ‘2 * 2 ** k = q * N’ by gvs[EXP] >>
      ‘EVEN (q * N)’ by (qpat_x_assum ‘2 * _ = q * N’ (SUBST1_TAC o SYM) >>
                         simp[EVEN_DOUBLE]) >>
      fs[EVEN_MULT]
      >- (fs[EVEN_EXISTS] >>
          rename1 ‘q = 2 * q1’ >>
          ‘2 * 2 ** k = 2 * (q1 * N)’
            by (qpat_x_assum ‘2 * 2 ** k = _’ mp_tac >> simp[]) >>
          ‘2 ** k = q1 * N’ by gvs[] >>
          ‘(2 ** k) MOD N = 0’ by metis_tac[MOD_EQ_0] >>
          first_x_assum drule_all >> simp[])
      >- (fs[EVEN_EXISTS] >>
          rename1 ‘N = 2 * N1’ >>
          ‘0 < N1’ by decide_tac >>
          ‘2 * 2 ** k = 2 * (q * N1)’
            by (qpat_x_assum ‘2 * 2 ** k = _’ mp_tac >> simp[]) >>
          ‘2 ** k = q * N1’ by gvs[] >>
          ‘(2 ** k) MOD N1 = 0’ by metis_tac[MOD_EQ_0] >>
          first_x_assum drule_all >> strip_tac >>
          qexists_tac ‘SUC n’ >> simp[EXP]))
QED

(* Pure REDUCE_ss-evaluatable characterization of powers of two:
   0 < N /\ (2 ** N) MOD N = 0 <=> ?n. N = 2 ** n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_pow2_mod_iff[local]:
  ∀N. (0 < N ∧ (2 ** N) MOD N = 0 ⇔ ∃n. N = 2 ** n) ∧
      (2 ≤ N ∧ (2 ** N) MOD N = 0 ⇔ ∃m. N = 2 * 2 ** m)
Proof
  ‘∀n:num. ∃d:num. 0n < d ∧ 2 ** n = d + n’
    by (Induct >- (qexists_tac ‘1n’ >> simp[]) >>
        fs[] >> Cases_on ‘d’ >> gvs[] >>
        qexists_tac ‘SUC (2 * n' + n)’ >> simp[EXP] >> decide_tac) >>
  ‘∀M. 0 < M ∧ (2 ** M) MOD M = 0 ⇔ ∃n. M = 2 ** n’
    by (gen_tac >> eq_tac >> strip_tac
        >- (qspecl_then [‘M’, ‘M’] mp_tac divisor_of_two_exp_is_pow2 >> simp[])
        >- (gvs[] >>
            first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
            qpat_assum ‘2 ** n = d + n’
              (fn th => CONV_TAC (LHS_CONV (LAND_CONV (RAND_CONV (REWR_CONV th))))) >>
            PURE_REWRITE_TAC[arithmeticTheory.EXP_ADD] >>
            qspec_then ‘2n ** n’ mp_tac MOD_EQ_0 >>
            impl_tac >- decide_tac >>
            disch_then (qspec_then ‘2n ** d’ ACCEPT_TAC))) >>
  gen_tac >> conj_tac >- first_assum (ACCEPT_TAC o Q.SPEC ‘N’) >>
  eq_tac >> strip_tac
  >- (‘0 < N’ by decide_tac >>
      ‘∃k0. N = 2 ** k0’ by metis_tac[] >>
      Cases_on ‘k0’ >> gvs[arithmeticTheory.EXP])
  >- (gvs[] >>
      ‘0n < 2 ** m’ by simp[] >>
      ‘2n ≤ 2 * 2 ** m ∧ 0n < 2 * 2 ** m’ by decide_tac >>
      ‘∃n:num. 2n * 2 ** m = 2 ** n’
        by (qexists_tac ‘SUC m’ >> simp[arithmeticTheory.EXP]) >>
      metis_tac[])
QED

(* Terminating [simp] BEC closure on power-of-2 blocklengths (e.g. N = 2, 4, 8).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_bec_split_channel_pow2[simp]:
  ∀(W : (bool, β) memoryless_channel) N k.
    is_bec W ∧ 0 < N ∧ (2 ** N) MOD N = 0 ∧ k < N ⇒
    is_bec (split_channel W N k)
Proof
  rpt strip_tac >>
  ‘∃n. N = 2 ** n’ by metis_tac[is_pow2_mod_iff] >>
  gvs[] >> drule_all proposition_7_bec_recursion >> simp[]
QED

(* Terminating [simp] BEC Bhattacharyya and erasure-probability step recursion
   for concrete power-of-2 numerals N >= 2 (halving N -> N DIV 2 down to N = 1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_split_channel_pow2_step[simp]:
  ∀(W : (bool, β) memoryless_channel) N k.
    is_bec W ∧ 2 ≤ N ∧ (2 ** N) MOD N = 0 ∧ k < N ⇒
    (EVEN k ⇒
     bhattacharyya (split_channel W N k) =
       2 * bhattacharyya (split_channel W (N DIV 2) (k DIV 2)) -
       (bhattacharyya (split_channel W (N DIV 2) (k DIV 2))) pow 2 ∧
     bec_erasure_prob (split_channel W N k) =
       2 * bec_erasure_prob (split_channel W (N DIV 2) (k DIV 2)) -
       (bec_erasure_prob (split_channel W (N DIV 2) (k DIV 2))) pow 2) ∧
    (¬EVEN k ⇒
     bhattacharyya (split_channel W N k) =
       (bhattacharyya (split_channel W (N DIV 2) (k DIV 2))) pow 2 ∧
     bec_erasure_prob (split_channel W N k) =
       (bec_erasure_prob (split_channel W (N DIV 2) (k DIV 2))) pow 2)
Proof
  rpt gen_tac >> strip_tac >>
  ‘∃m. N = 2 * 2 ** m’ by metis_tac[is_pow2_mod_iff] >>
  gvs[] >>
  ‘(2 * 2 ** m) DIV 2 = 2 ** m’
    by (irule DIV_UNIQUE >> qexists_tac ‘0n’ >> decide_tac) >>
  conj_tac >> strip_tac
  >- (fs[EVEN_EXISTS] >> rename1 ‘k = 2 * i’ >> gvs[] >>
      ‘(2 * i) DIV 2 = i’
        by (irule DIV_UNIQUE >> qexists_tac ‘0n’ >> decide_tac) >>
      ‘i < 2 ** m ∧ 2 * i < 2 ** SUC m’
        by (simp[arithmeticTheory.EXP] >> decide_tac) >>
      qspecl_then [‘W’, ‘m’, ‘i’] mp_tac proposition_7_bec_recursion >>
      qspecl_then [‘W’, ‘SUC m’, ‘2 * i’] mp_tac proposition_7_bec_recursion >>
      simp[arithmeticTheory.EXP] >> ntac 2 strip_tac >>
      simp[GSYM is_bec_bhattacharyya])
  >- (‘ODD k’ by metis_tac[EVEN_OR_ODD] >>
      gvs[ODD_EXISTS] >> rename1 ‘SUC (2 * i)’ >>
      ‘SUC (2 * i) = 2 * i + 1’ by decide_tac >>
      pop_assum SUBST_ALL_TAC >>
      ‘(2 * i + 1) DIV 2 = i’
        by (irule DIV_UNIQUE >> qexists_tac ‘1n’ >> decide_tac) >>
      ‘i < 2 ** m ∧ 2 * i + 1 < 2 ** SUC m’
        by (simp[arithmeticTheory.EXP] >> decide_tac) >>
      qspecl_then [‘W’, ‘m’, ‘i’] mp_tac proposition_7_bec_recursion >>
      qspecl_then [‘W’, ‘SUC m’, ‘2 * i + 1’] mp_tac
        proposition_7_bec_recursion >>
      simp[arithmeticTheory.EXP] >> ntac 2 strip_tac >>
      simp[GSYM is_bec_bhattacharyya])
QED

(* Terminating [simp] numeral-friendly local capacity pair conservation.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem split_channel_pow2_capacity_pair[simp]:
  ∀(W : (bool, β) memoryless_channel) N k1 k2.
    wf_bdmc W ∧ 2 ≤ N ∧ (2 ** N) MOD N = 0 ∧
    EVEN k1 ∧ k2 = k1 + 1 ∧ k2 < N ⇒
    symmetric_capacity (split_channel W N k1) +
    symmetric_capacity (split_channel W N k2) =
    2 * symmetric_capacity (split_channel W (N DIV 2) (k1 DIV 2))
Proof
  rpt strip_tac >>
  ‘∃m. N = 2 * 2 ** m’ by metis_tac[is_pow2_mod_iff] >>
  fs[EVEN_EXISTS] >>
  rename1 ‘k1 = 2 * i’ >>
  gvs[] >>
  ‘(2 * 2 ** m) DIV 2 = 2 ** m’
    by (irule DIV_UNIQUE >> qexists_tac ‘0’ >> decide_tac) >>
  ‘(2 * i) DIV 2 = i’
    by (irule DIV_UNIQUE >> qexists_tac ‘0’ >> decide_tac) >>
  ‘i < 2 ** m’ by decide_tac >>
  drule_then (qspecl_then [‘m’, ‘i’] strip_assume_tac)
    proposition_7_step_local >>
  simp[]
QED

(* Terminating [simp] extremal capacity propagation I(W) in {0, 1}.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem split_channel_pow2_extremal_capacity[simp]:
  ∀(W : (bool, β) memoryless_channel) N k.
    wf_bdmc W ∧ 0 < N ∧ (2 ** N) MOD N = 0 ∧ k < N ⇒
    (symmetric_capacity W = 0 ⇒ symmetric_capacity (split_channel W N k) = 0) ∧
    (symmetric_capacity W = 1 ⇒ symmetric_capacity (split_channel W N k) = 1)
Proof
  rpt strip_tac >>
  ‘∃n. N = 2 ** n’ by metis_tac[is_pow2_mod_iff] >>
  gvs[] >> drule_all split_channel_invariants >> simp[]
QED

(* Terminating [simp] cumulative capacity sum on power-of-2 numerals.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem symmetric_capacity_sum_pow2[simp]:
  ∀(W : (bool, β) memoryless_channel) N.
    wf_bdmc W ∧ 0 < N ∧ (2 ** N) MOD N = 0 ⇒
    ∑ (λi. symmetric_capacity (split_channel W N i)) (count N) =
    Normal (&N) * symmetric_capacity W
Proof
  rpt strip_tac >>
  ‘∃n. N = 2 ** n’ by metis_tac[is_pow2_mod_iff] >>
  gvs[GSYM extreal_of_num_def, proposition_7_capacity_sum]
QED

(* Terminating [simp] N = 1 cumulative Bhattacharyya sum.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bhattacharyya_sum_1[simp]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    ∑ (λi. bhattacharyya (split_channel W 1 i)) (count 1) = bhattacharyya W
Proof
  rpt strip_tac >>
  ‘count 1 = {0}’ by (rw[Once EXTENSION] >> decide_tac) >>
  simp[EXTREAL_SUM_IMAGE_SING]
QED

(* Terminating [simp] cumulative Bhattacharyya upper bound on power-of-2 numerals.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bhattacharyya_sum_pow2_le[simp]:
  ∀(W : (bool, β) memoryless_channel) N.
    wf_bdmc W ∧ 0 < N ∧ (2 ** N) MOD N = 0 ⇒
    ∑ (λi. bhattacharyya (split_channel W N i)) (count N) ≤
      &N * bhattacharyya W ∧
    ∑ (λi. bhattacharyya (split_channel W N i)) (count N) ≤
      Normal (&N) * bhattacharyya W
Proof
  rpt strip_tac >>
  ‘∃n. N = 2 ** n’ by metis_tac[is_pow2_mod_iff] >>
  gvs[GSYM extreal_of_num_def, proposition_7_bhattacharyya_sum]
QED

(* Terminating [simp] exact BEC cumulative Bhattacharyya sum on power-of-2 numerals.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bhattacharyya_sum_pow2_bec[simp]:
  ∀(W : (bool, β) memoryless_channel) N.
    is_bec W ∧ 0 < N ∧ (2 ** N) MOD N = 0 ⇒
    ∑ (λi. bhattacharyya (split_channel W N i)) (count N) =
      Normal (&N) * bhattacharyya W
Proof
  rpt strip_tac >>
  ‘∃n. N = 2 ** n’ by metis_tac[is_pow2_mod_iff] >>
  gvs[GSYM extreal_of_num_def, proposition_7_bhattacharyya_sum_bec]
QED

