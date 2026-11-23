(* ========================================================================= *)
(*   Asymptotic Channel Polarization and Rate of Polarization:               *)
(*   Theorem 1, Proposition 11, Lemma 1, and Theorem 2                       *)
(*   (Erdal Arıkan, 2009, arXiv:0807.3917v5, Sections I & IV & Appendix F).  *)
(*                                                                           *)
(*   Written by Gemini (Google DeepMind AI agent).                           *)
(* ========================================================================= *)

Theory channel_polarization

Ancestors
  combin arithmetic pair pred_set list rich_list logroot bitstring
  real real_sigma transc seq lim
  sigma_algebra extreal_base extreal measure probability
  fundamental extreal_information
  memoryless_channel bhattacharyya capacity bdmc
  polar_encode combine_channel split_channel channel_recursion

Libs
  dep_rewrite realLib RealField;

val _ = temp_overload_on ("-->", “seq$tends_num_real”);
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
  val REAL_ARITH_TAC : tactic = REAL_ASM_ARITH_TAC
end;

(* ------------------------------------------------------------------------- *)
(* Part 1: Asymptotic Channel Polarization (Theorem 1 & Proposition 11)      *)
(* ------------------------------------------------------------------------- *)

(* Real-valued Bhattacharyya parameter Z(W_{2^n}^{(i)}) in [0, 1].

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_Z_def:
  polar_Z (W : (bool, β) memoryless_channel) (n : num) (i : num) : real =
    real (bhattacharyya (split_channel W (2 ** n) i))
End

(* Real-valued symmetric capacity I(W_{2^n}^{(i)}) in [0, 1].

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_I_def:
  polar_I (W : (bool, β) memoryless_channel) (n : num) (i : num) : real =
    real (symmetric_capacity (split_channel W (2 ** n) i))
End

(* Positivity of 2^n in num and real.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem two_pow_pos_real[local]:
  ∀n : num. 0 < 2 ** n ∧ (0 : real) < &(2 ** n) ∧ (&(2 ** n) : real) ≠ 0
Proof
  gen_tac >>
  ‘0 < 2 ** n’ by simp[arithmeticTheory.ZERO_LESS_EXP] >>
  simp[REAL_OF_NUM_LT, REAL_OF_NUM_EQ]
QED

(* Fundamental Normal representations, [0, 1] bounds, Proposition 1 bounds,
   and single-step Proposition 7 relations for polar_Z and polar_I.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_Z_I_props:
  ∀(W : (bool, β) memoryless_channel) n i.
    wf_bdmc W ∧ i < 2 ** n ⇒
    wf_bdmc (split_channel W (2 ** n) i) ∧
    bhattacharyya (split_channel W (2 ** n) i) = Normal (polar_Z W n i) ∧
    0 ≤ polar_Z W n i ∧ polar_Z W n i ≤ 1 ∧
    symmetric_capacity (split_channel W (2 ** n) i) = Normal (polar_I W n i) ∧
    0 ≤ polar_I W n i ∧ polar_I W n i ≤ 1 ∧
    transc$logr 2 (2 / (1 + polar_Z W n i)) ≤ polar_I W n i ∧
    polar_I W n i ≤ real$sqrt (1 - (polar_Z W n i) pow 2) ∧
    polar_I W (SUC n) (2 * i) + polar_I W (SUC n) (2 * i + 1) =
      2 * polar_I W n i ∧
    polar_Z W (SUC n) (2 * i) ≤
      2 * polar_Z W n i - (polar_Z W n i) pow 2 ∧
    polar_Z W (SUC n) (2 * i + 1) = (polar_Z W n i) pow 2
Proof
  rpt strip_tac
  >- simp[wf_bdmc_split_channel]
  >- (drule_all wf_bdmc_split_channel >> strip_tac >>
      drule bhattacharyya_bounds >> strip_tac >>
      simp[polar_Z_def, real_normal])
  >- (drule_all wf_bdmc_split_channel >> strip_tac >>
      drule bhattacharyya_bounds >> strip_tac >>
      simp[polar_Z_def, real_normal])
  >- (drule_all wf_bdmc_split_channel >> strip_tac >>
      drule bhattacharyya_bounds >> strip_tac >>
      simp[polar_Z_def, real_normal])
  >- (drule_all wf_bdmc_split_channel >> strip_tac >>
      drule symmetric_capacity_bounds >> strip_tac >>
      simp[polar_I_def, real_normal])
  >- (drule_all wf_bdmc_split_channel >> strip_tac >>
      drule symmetric_capacity_bounds >> strip_tac >>
      simp[polar_I_def, real_normal])
  >- (drule_all wf_bdmc_split_channel >> strip_tac >>
      drule symmetric_capacity_bounds >> strip_tac >>
      simp[polar_I_def, real_normal])
  >- (drule_all wf_bdmc_split_channel >> strip_tac >>
      drule proposition_1_lower >>
      drule bhattacharyya_bounds >>
      drule symmetric_capacity_bounds >>
      rpt strip_tac >>
      ‘1 + z ≠ 0’ by REAL_ARITH_TAC >>
      gvs[polar_Z_def, polar_I_def, real_normal, extreal_of_num_def,
          extreal_add_eq, extreal_div_eq, extreal_logr_def, extreal_le_eq])
  >- (drule_all wf_bdmc_split_channel >> strip_tac >>
      drule proposition_1_upper >>
      drule bhattacharyya_bounds >>
      drule symmetric_capacity_bounds >>
      rpt strip_tac >>
      gvs[polar_Z_def, polar_I_def, real_normal, extreal_of_num_def,
          extreal_pow_def, extreal_sub_eq, extreal_sqrt_def, extreal_le_eq])
  >- (drule_all proposition_7 >>
      ‘2 * i < 2 ** SUC n ∧ 2 * i + 1 < 2 ** SUC n ∧ 2 ** SUC n = 2 * 2 ** n’
        by simp[arithmeticTheory.EXP] >>
      qspecl_then [‘W’, ‘n’, ‘i’] mp_tac wf_bdmc_split_channel >>
      qspecl_then [‘W’, ‘SUC n’, ‘2 * i’] mp_tac wf_bdmc_split_channel >>
      qspecl_then [‘W’, ‘SUC n’, ‘2 * i + 1’] mp_tac wf_bdmc_split_channel >>
      simp[] >> rpt strip_tac >>
      qspecl_then [‘split_channel W (2 ** n) i’] mp_tac symmetric_capacity_bounds >>
      qspecl_then [‘split_channel W (2 * 2 ** n) (2 * i)’] mp_tac symmetric_capacity_bounds >>
      qspecl_then [‘split_channel W (2 * 2 ** n) (2 * i + 1)’] mp_tac symmetric_capacity_bounds >>
      simp[] >> rpt strip_tac >>
      gvs[polar_I_def, arithmeticTheory.EXP, real_normal, extreal_of_num_def,
          extreal_add_eq, extreal_mul_eq])
  >- (drule_all proposition_7 >>
      ‘2 * i < 2 ** SUC n ∧ 2 ** SUC n = 2 * 2 ** n’
        by simp[arithmeticTheory.EXP] >>
      qspecl_then [‘W’, ‘n’, ‘i’] mp_tac wf_bdmc_split_channel >>
      qspecl_then [‘W’, ‘SUC n’, ‘2 * i’] mp_tac wf_bdmc_split_channel >>
      simp[] >> rpt strip_tac >>
      qspecl_then [‘split_channel W (2 ** n) i’] mp_tac bhattacharyya_bounds >>
      qspecl_then [‘split_channel W (2 * 2 ** n) (2 * i)’] mp_tac bhattacharyya_bounds >>
      simp[] >> rpt strip_tac >>
      gvs[polar_Z_def, arithmeticTheory.EXP, real_normal, extreal_of_num_def,
          extreal_mul_eq, extreal_pow_def, extreal_sub_eq, extreal_le_eq])
  >- (drule_all proposition_7 >>
      ‘2 * i + 1 < 2 ** SUC n ∧ 2 ** SUC n = 2 * 2 ** n’
        by simp[arithmeticTheory.EXP] >>
      qspecl_then [‘W’, ‘n’, ‘i’] mp_tac wf_bdmc_split_channel >>
      qspecl_then [‘W’, ‘SUC n’, ‘2 * i + 1’] mp_tac wf_bdmc_split_channel >>
      simp[] >> rpt strip_tac >>
      qspecl_then [‘split_channel W (2 ** n) i’] mp_tac bhattacharyya_bounds >>
      qspecl_then [‘split_channel W (2 * 2 ** n) (2 * i + 1)’] mp_tac bhattacharyya_bounds >>
      simp[] >> rpt strip_tac >>
      gvs[polar_Z_def, arithmeticTheory.EXP, real_normal, extreal_pow_def])
QED

(* Real-valued cumulative capacity conservation & Bhattacharyya upper bound
   from Proposition 7 Eqs. (36)-(37).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_Z_I_sums_real[local]:
  ∀(W : (bool, β) memoryless_channel) n.
    wf_bdmc W ⇒
    REAL_SUM_IMAGE (polar_I W n) (count (2 ** n)) =
      &(2 ** n) * real (symmetric_capacity W) ∧
    REAL_SUM_IMAGE (polar_Z W n) (count (2 ** n)) ≤
      &(2 ** n) * real (bhattacharyya W)
Proof
  rpt strip_tac
  >- (drule_then (qspec_then ‘n’ mp_tac) proposition_7_capacity_sum >>
      drule symmetric_capacity_bounds >> strip_tac >>
      ‘∑ (λi. symmetric_capacity (split_channel W (2 ** n) i)) (count (2 ** n)) =
       Normal (REAL_SUM_IMAGE (polar_I W n) (count (2 ** n)))’
        by (simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
            irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
            qx_gen_tac ‘i’ >> strip_tac >>
            drule_all polar_Z_I_props >> simp[]) >>
      pop_assum SUBST1_TAC >>
      simp[real_normal, extreal_of_num_def, extreal_mul_eq])
  >- (drule_then (qspec_then ‘n’ mp_tac) proposition_7_bhattacharyya_sum >>
      drule bhattacharyya_bounds >> strip_tac >>
      ‘∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) (count (2 ** n)) =
       Normal (REAL_SUM_IMAGE (polar_Z W n) (count (2 ** n)))’
        by (simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
            irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
            qx_gen_tac ‘i’ >> strip_tac >>
            drule_all polar_Z_I_props >> simp[]) >>
      pop_assum SUBST1_TAC >>
      simp[real_normal, extreal_of_num_def, extreal_mul_eq, extreal_le_eq])
QED

(* Even/odd pairing identity for REAL_SUM_IMAGE over count (2 * N).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_COUNT_DOUBLE_LOCAL[local]:
  ∀N (f : num -> real).
    REAL_SUM_IMAGE f (count (2 * N)) =
    REAL_SUM_IMAGE (λi. f (2 * i) + f (2 * i + 1)) (count N)
Proof
  Induct_on ‘N’ >> gen_tac
  >- simp[REAL_SUM_IMAGE_THM]
  >- (‘count (2 * SUC N) = (2 * N + 1) INSERT ((2 * N) INSERT count (2 * N))’
        by (rw[Once EXTENSION] >> decide_tac) >>
      pop_assum SUBST1_TAC >>
      simp[COUNT_SUC, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT] >>
      REAL_ARITH_TAC)
QED

(* Fundamental algebraic polarization decay inequality on [0, 1]:
     (1/2)*z + (1/2)*sqrt(2*z - z^2) <= sqrt(z) - (1/8)*sqrt(z)*(1 - z)^2.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sqrt_polar_step_ineq[local]:
  ∀z : real.
    0 ≤ z ∧ z ≤ 1 ⇒
    (1 / 2) * z + (1 / 2) * real$sqrt (2 * z - z pow 2) ≤
    real$sqrt z - (1 / 8) * (real$sqrt z * (1 - z) pow 2)
Proof
  rpt strip_tac >>
  ‘0 ≤ 2 - z ∧ 0 ≤ 1 - z ∧ 1 - z ≤ 1’ by REAL_ARITH_TAC >>
  ‘0 ≤ (1 - z) pow 2 ∧ (1 - z) pow 2 ≤ 1’
    by (conj_tac >- simp[REAL_LE_POW2] >>
        PURE_REWRITE_TAC[realTheory.POW_2] >>
        ‘(1 - z) * (1 - z) ≤ 1 * 1’ by (irule REAL_LE_MUL2 >> simp[]) >>
        REAL_ARITH_TAC) >>
  ‘0 ≤ z * (2 - z)’ by (irule REAL_LE_MUL >> simp[]) >>
  ‘2 * z - z pow 2 = z * (2 - z)’ by CONV_TAC (EQT_INTRO o REAL_RING) >>
  ‘0 ≤ real$sqrt z ∧ 0 ≤ real$sqrt (2 - z) ∧ 0 ≤ real$sqrt (z * (2 - z))’
    by simp[realTheory.SQRT_POS_LE] >>
  (* Step 1: 2 * sqrt (z * (2 - z)) <= 2 - (1 - z)^2 by squaring *)
  ‘0 ≤ 2 * real$sqrt (z * (2 - z)) ∧ 0 ≤ 2 - (1 - z) pow 2’ by REAL_ARITH_TAC >>
  ‘(2 * real$sqrt (z * (2 - z))) pow 2 ≤ (2 - (1 - z) pow 2) pow 2’
    by (‘(2 * real$sqrt (z * (2 - z))) pow 2 =
         4 * ((real$sqrt (z * (2 - z))) pow 2)’
          by CONV_TAC (EQT_INTRO o REAL_RING) >>
        pop_assum SUBST1_TAC >>
        simp[realTheory.SQRT_POW_2] >>
        ‘0 ≤ ((1 - z) pow 2) pow 2’ by simp[REAL_LE_POW2] >>
        ‘(2 - (1 - z) pow 2) pow 2 - 4 * (z * (2 - z)) =
         ((1 - z) pow 2) pow 2’
          by CONV_TAC (EQT_INTRO o REAL_RING) >>
        REAL_ARITH_TAC) >>
  ‘2 * real$sqrt (z * (2 - z)) ≤ 2 - (1 - z) pow 2’
    by (‘real$sqrt ((2 * real$sqrt (z * (2 - z))) pow 2) ≤
         real$sqrt ((2 - (1 - z) pow 2) pow 2)’
          by (irule realTheory.SQRT_MONO_LE >> simp[REAL_LE_POW2]) >>
        gvs[realTheory.POW_2_SQRT]) >>
  (* Step 2: sqrt z + sqrt (2 - z) <= 2 - (1/4)*(1 - z)^2 by squaring *)
  ‘0 ≤ real$sqrt z + real$sqrt (2 - z) ∧
   0 ≤ 2 - (1 / 4) * (1 - z) pow 2’
    by REAL_ARITH_TAC >>
  ‘(real$sqrt z + real$sqrt (2 - z)) pow 2 ≤
   (2 - (1 / 4) * (1 - z) pow 2) pow 2’
    by (‘(real$sqrt z + real$sqrt (2 - z)) pow 2 =
         (real$sqrt z) pow 2 + (real$sqrt (2 - z)) pow 2 +
         2 * (real$sqrt z * real$sqrt (2 - z))’
          by CONV_TAC (EQT_INTRO o REAL_RING) >>
        pop_assum SUBST1_TAC >>
        simp[realTheory.SQRT_POW_2, GSYM realTheory.SQRT_MUL] >>
        ‘0 ≤ ((1 - z) pow 2) pow 2’ by simp[REAL_LE_POW2] >>
        ‘(2 - (1 / 4) * (1 - z) pow 2) pow 2 - (4 - (1 - z) pow 2) =
         (1 / 16) * ((1 - z) pow 2) pow 2’
          by CONV_TAC (EQT_INTRO o REAL_RING) >>
        REAL_ARITH_TAC) >>
  ‘real$sqrt z + real$sqrt (2 - z) ≤ 2 - (1 / 4) * (1 - z) pow 2’
    by (‘real$sqrt ((real$sqrt z + real$sqrt (2 - z)) pow 2) ≤
         real$sqrt ((2 - (1 / 4) * (1 - z) pow 2) pow 2)’
          by (irule realTheory.SQRT_MONO_LE >> simp[REAL_LE_POW2]) >>
        gvs[realTheory.POW_2_SQRT]) >>
  (* Step 3: Multiply by (1/2) * sqrt z >= 0 *)
  ‘((1 / 2) * real$sqrt z) * (real$sqrt z + real$sqrt (2 - z)) ≤
   ((1 / 2) * real$sqrt z) * (2 - (1 / 4) * (1 - z) pow 2)’
    by (irule REAL_LE_LMUL_IMP >> simp[] >> REAL_ARITH_TAC) >>
  ‘((1 / 2) * real$sqrt z) * (real$sqrt z + real$sqrt (2 - z)) =
   (1 / 2) * ((real$sqrt z) pow 2) +
   (1 / 2) * (real$sqrt z * real$sqrt (2 - z))’
    by CONV_TAC (EQT_INTRO o REAL_RING) >>
  ‘((1 / 2) * real$sqrt z) * (2 - (1 / 4) * (1 - z) pow 2) =
   real$sqrt z - (1 / 8) * (real$sqrt z * (1 - z) pow 2)’
    by CONV_TAC (EQT_INTRO o REAL_RING) >>
  gvs[realTheory.SQRT_POW_2, GSYM realTheory.SQRT_MUL]
QED

(* Pointwise polynomial bound (z * (1 - z))^2 <= sqrt z * (1 - z)^2 on [0, 1].

   Written by Gemini (Google DeepMind AI agent) *)
Theorem z_one_minus_z_sq_le_sqrt[local]:
  ∀z : real.
    0 ≤ z ∧ z ≤ 1 ⇒
    (z * (1 - z)) pow 2 ≤ real$sqrt z * (1 - z) pow 2
Proof
  rpt strip_tac >>
  ‘0 ≤ real$sqrt z ∧ real$sqrt z ≤ 1’
    by (conj_tac >- simp[realTheory.SQRT_POS_LE] >>
        ‘real$sqrt z ≤ real$sqrt 1’
          by (irule realTheory.SQRT_MONO_LE >> simp[]) >>
        gvs[realTheory.SQRT_1]) >>
  ‘z ≤ real$sqrt z’
    by (‘(real$sqrt z) pow 2 ≤ 1 * real$sqrt z’
          by (PURE_REWRITE_TAC[realTheory.POW_2] >>
              irule REAL_LE_RMUL_IMP >> simp[]) >>
        gvs[realTheory.SQRT_POW_2]) >>
  ‘z pow 2 ≤ z’
    by (PURE_REWRITE_TAC[realTheory.POW_2] >>
        ‘z * z ≤ 1 * z’ by (irule REAL_LE_RMUL_IMP >> simp[]) >>
        REAL_ARITH_TAC) >>
  ‘z pow 2 ≤ real$sqrt z’ by REAL_ARITH_TAC >>
  ‘(z * (1 - z)) pow 2 = z pow 2 * (1 - z) pow 2’ by CONV_TAC (EQT_INTRO o REAL_RING) >>
  pop_assum SUBST1_TAC >>
  irule REAL_LE_RMUL_IMP >> simp[REAL_LE_POW2]
QED

(* Level-n potential S_n = 2^{-n} sum_{i < 2^n} sqrt(Z_{n,i}).

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_S_def:
  polar_S (W : (bool, β) memoryless_channel) (n : num) : real =
    REAL_SUM_IMAGE (λi. real$sqrt (polar_Z W n i)) (count (2 ** n)) / &(2 ** n)
End

(* Level-n dissipation D_n = 2^{-n} sum_{i < 2^n} sqrt(Z_{n,i})*(1 - Z_{n,i})^2.

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_D_def:
  polar_D (W : (bool, β) memoryless_channel) (n : num) : real =
    REAL_SUM_IMAGE (λi. real$sqrt (polar_Z W n i) * (1 - polar_Z W n i) pow 2)
      (count (2 ** n)) / &(2 ** n)
End

(* Level-n variance proxy M_n = 2^{-n} sum_{i < 2^n} Z_{n,i}*(1 - Z_{n,i}).

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_M_def:
  polar_M (W : (bool, β) memoryless_channel) (n : num) : real =
    REAL_SUM_IMAGE (λi. polar_Z W n i * (1 - polar_Z W n i))
      (count (2 ** n)) / &(2 ** n)
End

(* Bounds 0 <= S_n <= 1, 0 <= D_n, 0 <= M_n and one-step decay
   S_{n+1} <= S_n - (1/8) * D_n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_S_D_M_step[local]:
  ∀(W : (bool, β) memoryless_channel) n.
    wf_bdmc W ⇒
    0 ≤ polar_S W n ∧ polar_S W n ≤ 1 ∧
    0 ≤ polar_D W n ∧ 0 ≤ polar_M W n ∧
    polar_S W (SUC n) ≤ polar_S W n - (1 / 8) * polar_D W n
Proof
  rpt strip_tac >>
  qspec_then ‘n’ strip_assume_tac two_pow_pos_real >>
  qspec_then ‘SUC n’ strip_assume_tac two_pow_pos_real
  >- (simp[polar_S_def] >>
      irule REAL_SUM_IMAGE_POS >> simp[] >>
      qx_gen_tac ‘i’ >> strip_tac >>
      drule_all polar_Z_I_props >> simp[realTheory.SQRT_POS_LE])
  >- (simp[polar_S_def, REAL_LE_LDIV_EQ] >>
      ‘REAL_SUM_IMAGE (λi. real$sqrt (polar_Z W n i)) (count (2 ** n)) ≤
       REAL_SUM_IMAGE (λi : num. (1 : real)) (count (2 ** n))’
        by (irule REAL_SUM_IMAGE_MONO >> simp[] >>
            qx_gen_tac ‘i’ >> strip_tac >>
            drule_all polar_Z_I_props >> strip_tac >>
            ‘real$sqrt (polar_Z W n i) ≤ real$sqrt 1’
              by (irule realTheory.SQRT_MONO_LE >> simp[]) >>
            gvs[realTheory.SQRT_1]) >>
      gvs[REAL_SUM_IMAGE_FINITE_CONST3])
  >- (simp[polar_D_def] >>
      irule REAL_SUM_IMAGE_POS >> simp[] >>
      qx_gen_tac ‘i’ >> strip_tac >>
      drule_all polar_Z_I_props >> strip_tac >>
      irule REAL_LE_MUL >> simp[realTheory.SQRT_POS_LE, REAL_LE_POW2])
  >- (simp[polar_M_def] >>
      irule REAL_SUM_IMAGE_POS >> simp[] >>
      qx_gen_tac ‘i’ >> strip_tac >>
      drule_all polar_Z_I_props >> strip_tac >>
      irule REAL_LE_MUL >> REAL_ARITH_TAC)
  >- (‘REAL_SUM_IMAGE
         (λi. real$sqrt (polar_Z W (SUC n) (2 * i)) +
              real$sqrt (polar_Z W (SUC n) (2 * i + 1)))
         (count (2 ** n)) ≤
       REAL_SUM_IMAGE
         (λi. 2 * real$sqrt (polar_Z W n i) -
              (1 / 4) * (real$sqrt (polar_Z W n i) * (1 - polar_Z W n i) pow 2))
         (count (2 ** n))’
        by (irule REAL_SUM_IMAGE_MONO >> simp[] >>
            qx_gen_tac ‘i’ >> strip_tac >>
            drule_all polar_Z_I_props >>
            ‘2 * i < 2 ** SUC n’ by simp[arithmeticTheory.EXP] >>
            qspecl_then [‘W’, ‘SUC n’, ‘2 * i’] mp_tac polar_Z_I_props >>
            simp[] >> rpt strip_tac >>
            qabbrev_tac ‘z = polar_Z W n i’ >>
            ‘real$sqrt (polar_Z W (SUC n) (2 * i)) ≤ real$sqrt (2 * z - z pow 2)’
              by (irule realTheory.SQRT_MONO_LE >> simp[]) >>
            ‘real$sqrt (z pow 2) = z’ by simp[realTheory.POW_2_SQRT] >>
            qspec_then ‘z’ mp_tac sqrt_polar_step_ineq >>
            simp[] >> REAL_ARITH_TAC) >>
      qpat_x_assum ‘REAL_SUM_IMAGE _ _ ≤ REAL_SUM_IMAGE _ _’ mp_tac >>
      simp[polar_S_def, polar_D_def, arithmeticTheory.EXP,
           REAL_SUM_IMAGE_COUNT_DOUBLE_LOCAL, REAL_SUM_IMAGE_SUB,
           REAL_SUM_IMAGE_CMUL] >>
      qabbrev_tac ‘A = REAL_SUM_IMAGE (λi. real$sqrt (polar_Z W n i)) (count (2 ** n))’ >>
      qabbrev_tac ‘B = REAL_SUM_IMAGE
                         (λi. real$sqrt (polar_Z W n i) * (1 - polar_Z W n i) pow 2)
                         (count (2 ** n))’ >>
      qabbrev_tac ‘C = REAL_SUM_IMAGE
                         (λi. real$sqrt (polar_Z W (SUC n) (2 * i)) +
                              real$sqrt (polar_Z W (SUC n) (2 * i + 1)))
                         (count (2 ** n))’ >>
      strip_tac >>
      ‘0 < 2 * (&(2 ** n) : real)’ by REAL_ARITH_TAC >>
      ONCE_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] >>
      simp[REAL_LE_LDIV_EQ] >>
      ‘(&(2 ** n) : real) ≠ 0 ⇒
       2 * (&(2 ** n) * (A / &(2 ** n) - (1 / 8) * (B * inv (&(2 ** n))))) =
       2 * A - (1 / 4) * B’
        by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
      gvs[] >>
      REAL_ARITH_TAC)
QED

(* Telescoping sum of polar_D yields polar_D W --> 0 and polar_M W --> 0.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_D_M_tendsto_0[local]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    (polar_D W --> (0 : real)) ∧
    (polar_M W --> (0 : real))
Proof
  gen_tac >> strip_tac >>
  ‘polar_D W --> (0 : real)’
    by (irule seqTheory.SER_ZERO >>
        irule seqTheory.POS_SUMMABLE >>
        conj_tac
        >- (gen_tac >>
            drule_then (qspec_then ‘n’ strip_assume_tac) polar_S_D_M_step >>
            simp[])
        >- (qexists_tac ‘8’ >>
            ‘∀m. real$sum (0, m) (polar_D W) ≤ 8 * (polar_S W 0 - polar_S W m)’
              by (Induct_on ‘m’
                  >- simp[realTheory.sum]
                  >- (simp[realTheory.sum] >>
                      drule_then (qspec_then ‘m’ strip_assume_tac) polar_S_D_M_step >>
                      REAL_ARITH_TAC)) >>
            gen_tac >>
            first_x_assum (qspec_then ‘n’ mp_tac) >>
            drule_then (qspec_then ‘0’ strip_assume_tac) polar_S_D_M_step >>
            drule_then (qspec_then ‘n’ strip_assume_tac) polar_S_D_M_step >>
            REAL_ARITH_TAC)) >>
  conj_tac >- simp[] >>
  simp[seqTheory.SEQ] >> qx_gen_tac ‘e’ >> strip_tac >>
  ‘0 < e pow 2’ by (simp[] >> REAL_ARITH_TAC) >>
  ‘0 < (e pow 2) / 2’ by (irule REAL_LT_DIV >> simp[] >> REAL_ARITH_TAC) >>
  ‘e ≠ 0’ by REAL_ARITH_TAC >>
  qpat_x_assum ‘polar_D W --> 0’ mp_tac >> simp[seqTheory.SEQ] >>
  disch_then (qspec_then ‘(e pow 2) / 2’ mp_tac) >> simp[] >>
  disch_then (qx_choose_then ‘N0’ assume_tac) >>
  qexists_tac ‘N0’ >> qx_gen_tac ‘n’ >> strip_tac >>
  drule_then (qspec_then ‘n’ strip_assume_tac) polar_S_D_M_step >>
  qspec_then ‘n’ strip_assume_tac two_pow_pos_real >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> impl_tac >- decide_tac >>
  simp[realTheory.abs] >> strip_tac >>
  ‘REAL_SUM_IMAGE (λi. polar_Z W n i * (1 - polar_Z W n i)) (count (2 ** n)) ≤
   REAL_SUM_IMAGE
     (λi. e / 2 +
          (inv e) * (real$sqrt (polar_Z W n i) * (1 - polar_Z W n i) pow 2))
     (count (2 ** n))’
    by (irule REAL_SUM_IMAGE_MONO >> reverse conj_tac >- simp[] >>
        qx_gen_tac ‘i’ >> REWRITE_TAC[IN_COUNT] >> BETA_TAC >> strip_tac >>
        drule_all polar_Z_I_props >> strip_tac >>
        qabbrev_tac ‘z = polar_Z W n i’ >>
        ‘(z * (1 - z)) pow 2 ≤ real$sqrt z * (1 - z) pow 2’
          by (irule z_one_minus_z_sq_le_sqrt >> simp[]) >>
        ‘0 ≤ (z * (1 - z) - e / 2) pow 2 ∧ 0 ≤ (e / 2) pow 2’
          by simp[REAL_LE_POW2] >>
        ‘e * (e / 2) + (z * (1 - z)) pow 2 - e * (z * (1 - z)) =
         (z * (1 - z) - e / 2) pow 2 + (e / 2) pow 2’
          by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
        irule REAL_LE_LCANCEL_IMP >> qexists_tac ‘e’ >>
        conj_tac >- REAL_ARITH_TAC >>
        ‘e * (e / 2 + inv e * (real$sqrt z * (1 - z) pow 2)) =
         e * (e / 2) + real$sqrt z * (1 - z) pow 2’
          by (qpat_assum ‘e ≠ 0’ mp_tac >> CONV_TAC (EQT_INTRO o REAL_FIELD)) >>
        pop_assum SUBST1_TAC >>
        REAL_ARITH_TAC) >>
  ‘polar_M W n ≤ e / 2 + polar_D W n / e’
    by (qpat_x_assum ‘REAL_SUM_IMAGE _ _ ≤ REAL_SUM_IMAGE _ _’ mp_tac >>
        simp[REAL_SUM_IMAGE_ADD, REAL_SUM_IMAGE_FINITE_CONST3,
             REAL_SUM_IMAGE_CMUL, polar_M_def, polar_D_def, REAL_LE_LDIV_EQ] >>
        ‘∀B d e0 : real.
           d ≠ 0 ∧ e0 ≠ 0 ⇒
           d * (e0 / 2 + (B / d) / e0) = d * (e0 / 2) + inv e0 * B ∧
           (e0 / 2 + (B / d) / e0) * d = d * (e0 / 2) + inv e0 * B ∧
           d * (e0 / 2 + B * (inv d * inv e0)) = d * (e0 / 2) + inv e0 * B ∧
           d * (e0 / 2 + (B * inv d) * inv e0) = d * (e0 / 2) + inv e0 * B’
          by (rpt gen_tac >> CONV_TAC (EQT_INTRO o REAL_FIELD)) >>
        strip_tac >>
        first_x_assum
          (qspecl_then
             [‘REAL_SUM_IMAGE
                 (λi. real$sqrt (polar_Z W n i) * (1 - polar_Z W n i) pow 2)
                 (count (2 ** n))’,
              ‘&(2 ** n)’, ‘e’] mp_tac) >>
        ASM_REWRITE_TAC[] >> strip_tac >> ASM_REWRITE_TAC[] >>
        REAL_ARITH_TAC) >>
  ‘polar_D W n / e < e / 2’
    by (‘0 < 2 * e’ by REAL_ARITH_TAC >>
        ‘polar_D W n / e < e / 2 ⇔
         (2 * e) * (polar_D W n / e) < (2 * e) * (e / 2)’
          by simp[REAL_LT_LMUL] >>
        pop_assum SUBST1_TAC >>
        ‘e ≠ 0 ⇒
         (2 * e) * (polar_D W n / e) = 2 * polar_D W n ∧
         (2 * e) * (e / 2) = e pow 2’
          by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
        pop_assum mp_tac >> ASM_REWRITE_TAC[] >> strip_tac >>
        ASM_REWRITE_TAC[]) >>
  ‘e / 2 + e / 2 = e’ by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
  REAL_ARITH_TAC
QED

(* Middle-capacity fraction at threshold eps:
   2^{-n} * |{i < 2^n : eps <= I_{n,i} <= 1 - eps}|.

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_mid_frac_def:
  polar_mid_frac (W : (bool, β) memoryless_channel) (eps : real) (n : num) : real =
    (&(CARD {i | i < 2 ** n ∧ eps ≤ polar_I W n i ∧ polar_I W n i ≤ 1 - eps}) : real) /
    &(2 ** n)
End

(* High-capacity fraction matching Theorem 1 verbatim.

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_high_frac_def:
  polar_high_frac (W : (bool, β) memoryless_channel) (d : real) (n : num) : real =
    (&(CARD {i | i < 2 ** n ∧
                 Normal (1 - d) <
                 symmetric_capacity (split_channel W (2 ** n) i)}) : real) /
    &(2 ** n)
End

(* Low-capacity fraction matching Theorem 1 verbatim.

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_low_frac_def:
  polar_low_frac (W : (bool, β) memoryless_channel) (d : real) (n : num) : real =
    (&(CARD {i | i < 2 ** n ∧
                 symmetric_capacity (split_channel W (2 ** n) i) <
                 Normal d}) : real) /
    &(2 ** n)
End

(* Cardinality of a disjoint union of two finite sets.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_DISJOINT_UNION_LOCAL[local]:
  ∀(s : α -> bool) t.
    FINITE s ∧ FINITE t ∧ DISJOINT s t ⇒
    CARD (s ∪ t) = CARD s + CARD t
Proof
  rpt strip_tac >> qspecl_then [‘s’, ‘t’] mp_tac CARD_UNION_EQN >>
  fs[DISJOINT_DEF]
QED

(* Vanishing of the unpolarized middle capacity fraction for every eps in (0, 1/2).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_mid_frac_tendsto_0[local]:
  ∀(W : (bool, β) memoryless_channel) (eps : real).
    wf_bdmc W ∧ 0 < eps ∧ eps < 1 / 2 ⇒
    polar_mid_frac W eps --> (0 : real)
Proof
  rpt strip_tac >>
  ‘0 < transc$ln 2’
    by (irule transcTheory.LN_POS_LT >> REAL_ARITH_TAC) >>
  qabbrev_tac ‘eta = realax$min ((eps pow 2) / 4) ((eps * transc$ln 2) / 2)’ >>
  ‘0 < eta ∧ eta ≤ (eps pow 2) / 4 ∧ eta ≤ (eps * transc$ln 2) / 2 ∧ eta < 1 / 2’
    by (simp[Abbr ‘eta’, REAL_LT_MIN, REAL_MIN_LE1, REAL_MIN_LE2] >>
        ‘0 < eps pow 2 ∧ eps pow 2 < (1 / 2 : real) pow 2’
          by (conj_tac >- (simp[] >> REAL_ARITH_TAC) >>
              PURE_REWRITE_TAC[realTheory.POW_2] >>
              irule REAL_LT_MUL2 >> REAL_ARITH_TAC) >>
        ‘0 < (eps * transc$ln 2) / 2’
          by (irule REAL_LT_DIV >> simp[REAL_LT_MUL] >> REAL_ARITH_TAC) >>
        ‘realax$min ((eps pow 2) / 4) ((eps * transc$ln 2) / 2) ≤ (eps pow 2) / 4’
          by simp[REAL_MIN_LE1] >>
        qpat_x_assum ‘eps pow 2 < _’ mp_tac >>
        PURE_REWRITE_TAC[realTheory.POW_2] >> REAL_ARITH_TAC) >>
  ‘0 < eta * (1 - eta) ∧ eta * (1 - eta) ≠ 0’
    by (‘0 < eta * (1 - eta)’ by (irule REAL_LT_MUL >> REAL_ARITH_TAC) >>
        REAL_ARITH_TAC) >>
  (* Pointwise bridge: eps <= I_{n,i} <= 1 - eps ==> eta * (1 - eta) <= Z_{n,i} * (1 - Z_{n,i}) *)
  ‘∀n i.
     i < 2 ** n ∧ eps ≤ polar_I W n i ∧ polar_I W n i ≤ 1 - eps ⇒
     eta * (1 - eta) ≤ polar_Z W n i * (1 - polar_Z W n i)’
    by (rpt strip_tac >>
        drule_all polar_Z_I_props >> strip_tac >>
        qabbrev_tac ‘z = polar_Z W n i’ >>
        ‘eta < z’
          by (CCONTR_TAC >>
              ‘z ≤ eta’ by REAL_ARITH_TAC >>
              ‘transc$ln (1 + z) ≤ z’ by simp[transcTheory.LN_LE] >>
              ‘z < eps * transc$ln 2’
                by (‘0 < eps * transc$ln 2’ by simp[REAL_LT_MUL] >>
                    REAL_ARITH_TAC) >>
              ‘transc$logr 2 (1 + z) < eps’
                by (simp[transcTheory.logr_def, REAL_LT_LDIV_EQ] >>
                    REAL_ARITH_TAC) >>
              ‘0 < (2 : real) ∧ 0 < 1 + z’ by REAL_ARITH_TAC >>
              ‘transc$logr 2 (2 / (1 + z)) = 1 - transc$logr 2 (1 + z)’
                by simp[transcTheory.logr_div, logr_2_2] >>
              REAL_ARITH_TAC) >>
        ‘z < 1 - eta’
          by (CCONTR_TAC >>
              ‘1 - eta ≤ z’ by REAL_ARITH_TAC >>
              ‘0 ≤ 1 - z ∧ 1 - z ≤ eta ∧ 0 ≤ 1 + z ∧ 1 + z ≤ 2’
                by REAL_ARITH_TAC >>
              ‘1 - z pow 2 = (1 - z) * (1 + z)’ by CONV_TAC (EQT_INTRO o REAL_RING) >>
              ‘0 ≤ 1 - z pow 2 ∧ 1 - z pow 2 ≤ 2 * eta’
                by (conj_tac
                    >- (pop_assum SUBST1_TAC >> irule REAL_LE_MUL >> simp[])
                    >- (pop_assum SUBST1_TAC >>
                        ‘(1 - z) * (1 + z) ≤ eta * 2’
                          by (irule REAL_LE_MUL2 >> simp[]) >>
                        REAL_ARITH_TAC)) >>
              ‘0 < eps pow 2’ by (simp[] >> REAL_ARITH_TAC) >>
              ‘1 - z pow 2 < eps pow 2’ by REAL_ARITH_TAC >>
              ‘real$sqrt (1 - z pow 2) < real$sqrt (eps pow 2)’
                by (irule realTheory.SQRT_MONO_LT >> simp[]) >>
              ‘0 ≤ eps’ by REAL_ARITH_TAC >>
              gvs[realTheory.POW_2_SQRT] >>
              REAL_ARITH_TAC) >>
        ‘z * (1 - z) - eta * (1 - eta) = (z - eta) * (1 - eta - z)’
          by CONV_TAC (EQT_INTRO o REAL_RING) >>
        ‘0 < (z - eta) * (1 - eta - z)’
          by (irule REAL_LT_MUL >> REAL_ARITH_TAC) >>
        REAL_ARITH_TAC) >>
  (* Markov finite-sum bound + SEQ_SANDWICH *)
  ‘∀n. 0 ≤ polar_mid_frac W eps n ∧
       polar_mid_frac W eps n ≤ inv (eta * (1 - eta)) * polar_M W n’
    by (gen_tac >>
        qspec_then ‘n’ strip_assume_tac two_pow_pos_real >>
        qabbrev_tac ‘S_mid = {i | i < 2 ** n ∧ eps ≤ polar_I W n i ∧
                                  polar_I W n i ≤ 1 - eps}’ >>
        ‘S_mid ⊆ count (2 ** n) ∧ FINITE S_mid’
          by (conj_tac >- rw[Abbr ‘S_mid’, SUBSET_DEF] >>
              irule SUBSET_FINITE_I >> qexists_tac ‘count (2 ** n)’ >>
              rw[Abbr ‘S_mid’, SUBSET_DEF]) >>
        conj_tac
        >- simp[polar_mid_frac_def]
        >- (‘(&(CARD S_mid) : real) * (eta * (1 - eta)) ≤
             REAL_SUM_IMAGE (λi. polar_Z W n i * (1 - polar_Z W n i)) (count (2 ** n))’
              by (‘(&(CARD S_mid) : real) * (eta * (1 - eta)) =
                   REAL_SUM_IMAGE (λi. eta * (1 - eta)) S_mid’
                    by simp[REAL_SUM_IMAGE_FINITE_CONST3] >>
                  pop_assum SUBST1_TAC >>
                  irule REAL_LE_TRANS >>
                  qexists_tac
                    ‘REAL_SUM_IMAGE (λi. polar_Z W n i * (1 - polar_Z W n i)) S_mid’ >>
                  conj_tac
                  >- (irule REAL_SUM_IMAGE_MONO >> reverse conj_tac >- simp[] >>
                      qx_gen_tac ‘i’ >> simp[Abbr ‘S_mid’] >> strip_tac >>
                      first_x_assum drule_all >>
                      ‘eta * (1 - eta) = (1 - eta) * eta ∧
                       polar_Z W n i * (1 - polar_Z W n i) =
                         (1 - polar_Z W n i) * polar_Z W n i’
                        by CONV_TAC (EQT_INTRO o REAL_RING) >>
                      REAL_ARITH_TAC)
                  >- (irule REAL_SUM_IMAGE_MONO_SET >> simp[] >>
                      qx_gen_tac ‘i’ >> strip_tac >>
                      drule_all polar_Z_I_props >> strip_tac >>
                      irule REAL_LE_MUL >> REAL_ARITH_TAC)) >>
            REWRITE_TAC[polar_mid_frac_def, polar_M_def] >>
            qpat_assum ‘Abbrev (S_mid = _)’
              (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
            qabbrev_tac
              ‘Msum = REAL_SUM_IMAGE (λi. polar_Z W n i * (1 - polar_Z W n i))
                                     (count (2 ** n))’ >>
            irule REAL_LE_LCANCEL_IMP >>
            qexists_tac ‘(eta * (1 - eta)) * &(2 ** n)’ >>
            conj_tac >- (irule REAL_LT_MUL >> simp[two_pow_pos_real]) >>
            ‘eta * (1 - eta) ≠ 0 ∧ (&(2 ** n) : real) ≠ 0 ⇒
             ((eta * (1 - eta)) * &(2 ** n)) * (&(CARD S_mid) / &(2 ** n)) =
               &(CARD S_mid) * (eta * (1 - eta)) ∧
             ((eta * (1 - eta)) * &(2 ** n)) *
             (inv (eta * (1 - eta)) * (Msum / &(2 ** n))) = Msum’
              by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
            pop_assum mp_tac >> impl_tac >- simp[two_pow_pos_real] >>
            disch_then (fn th => REWRITE_TAC[th]) >> ASM_REWRITE_TAC[])) >>
  drule polar_D_M_tendsto_0 >> strip_tac >>
  ‘(λn : num. inv (eta * (1 - eta)) * polar_M W n) --> (0 : real)’
    by (qspecl_then [‘λn : num. inv (eta * (1 - eta))’,
                     ‘inv (eta * (1 - eta))’, ‘polar_M W’, ‘0 : real’]
          mp_tac seqTheory.SEQ_MUL >>
        BETA_TAC >> ASM_REWRITE_TAC[seqTheory.SEQ_CONST, REAL_MUL_RZERO]) >>
  irule seqTheory.SEQ_SANDWICH >>
  qexistsl_tac [‘λn : num. (0 : real)’,
                ‘λn : num. inv (eta * (1 - eta)) * polar_M W n’] >>
  ASM_REWRITE_TAC[seqTheory.SEQ_CONST] >>
  rpt strip_tac >> BETA_TAC >> ASM_REWRITE_TAC[]
QED

(* Partition and capacity-conservation bounds for any threshold eps in (0, 1/2):
     high_frac(eps) + mid_frac(eps) + low_frac(eps) = 1,
     I_0 - eps - mid_frac(eps) <= high_frac(eps) <= I_0 + eps.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_frac_conservation_bounds[local]:
  ∀(W : (bool, β) memoryless_channel) (eps : real) (n : num).
    wf_bdmc W ∧ 0 < eps ∧ eps < 1 / 2 ⇒
    0 ≤ polar_high_frac W eps n ∧
    0 ≤ polar_low_frac W eps n ∧
    polar_high_frac W eps n + polar_mid_frac W eps n + polar_low_frac W eps n = 1 ∧
    real (symmetric_capacity W) - eps - polar_mid_frac W eps n ≤
      polar_high_frac W eps n ∧
    polar_high_frac W eps n ≤ real (symmetric_capacity W) + eps
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then ‘n’ strip_assume_tac two_pow_pos_real >>
  qabbrev_tac ‘H = {i | i < 2 ** n ∧ 1 - eps < polar_I W n i}’ >>
  qabbrev_tac ‘M = {i | i < 2 ** n ∧ eps ≤ polar_I W n i ∧ polar_I W n i ≤ 1 - eps}’ >>
  qabbrev_tac ‘L = {i | i < 2 ** n ∧ polar_I W n i < eps}’ >>
  ‘H ⊆ count (2 ** n) ∧ M ⊆ count (2 ** n) ∧ L ⊆ count (2 ** n)’
    by rw[Abbr ‘H’, Abbr ‘M’, Abbr ‘L’, SUBSET_DEF] >>
  ‘FINITE H ∧ FINITE M ∧ FINITE L’
    by (rpt conj_tac >>
        (irule SUBSET_FINITE_I >> qexists_tac ‘count (2 ** n)’ >>
         rw[Abbr ‘H’, Abbr ‘M’, Abbr ‘L’, SUBSET_DEF])) >>
  ‘DISJOINT H M ∧ DISJOINT H L ∧ DISJOINT M L’
    by (rpt conj_tac
        >- (rw[Abbr ‘H’, Abbr ‘M’, DISJOINT_DEF, Once EXTENSION] >>
            CCONTR_TAC >> gvs[] >> REAL_ARITH_TAC)
        >- (rw[Abbr ‘H’, Abbr ‘L’, DISJOINT_DEF, Once EXTENSION] >>
            CCONTR_TAC >> gvs[] >> REAL_ARITH_TAC)
        >- (rw[Abbr ‘M’, Abbr ‘L’, DISJOINT_DEF, Once EXTENSION] >>
            CCONTR_TAC >> gvs[] >> REAL_ARITH_TAC)) >>
  ‘DISJOINT H (M ∪ L)’ by metis_tac[DISJOINT_UNION, DISJOINT_SYM] >>
  ‘count (2 ** n) = H ∪ (M ∪ L)’
    by (rw[Abbr ‘H’, Abbr ‘M’, Abbr ‘L’, Once EXTENSION] >>
        eq_tac >> strip_tac >> simp[] >>
        Cases_on ‘1 - eps < polar_I W n x’ >> simp[] >>
        Cases_on ‘polar_I W n x < eps’ >> simp[] >>
        REAL_ARITH_TAC) >>
  ‘CARD H + CARD M + CARD L = 2 ** n’
    by (‘CARD (H ∪ (M ∪ L)) = 2 ** n’ by metis_tac[CARD_COUNT] >>
        qpat_x_assum ‘CARD (H ∪ (M ∪ L)) = 2 ** n’ mp_tac >>
        DEP_REWRITE_TAC[CARD_DISJOINT_UNION_LOCAL] >>
        fs[] >> decide_tac) >>
  ‘{i | i < 2 ** n ∧
        Normal (1 - eps) < symmetric_capacity (split_channel W (2 ** n) i)} = H ∧
   {i | i < 2 ** n ∧
        symmetric_capacity (split_channel W (2 ** n) i) < Normal eps} = L’
    by (conj_tac
        >- (rw[Abbr ‘H’, Once EXTENSION] >> eq_tac >> strip_tac >> simp[] >>
            drule_all polar_Z_I_props >> strip_tac >> gvs[extreal_lt_eq])
        >- (rw[Abbr ‘L’, Once EXTENSION] >> eq_tac >> strip_tac >> simp[] >>
            drule_all polar_Z_I_props >> strip_tac >> gvs[extreal_lt_eq])) >>
  ‘(&(CARD H) : real) / &(2 ** n) + (&(CARD M) : real) / &(2 ** n) +
   (&(CARD L) : real) / &(2 ** n) = 1’
    by simp[REAL_DIV_ADD, REAL_OF_NUM_ADD, REAL_DIV_REFL, two_pow_pos_real] >>
  rpt conj_tac
  >- simp[polar_high_frac_def]
  >- simp[polar_low_frac_def]
  >- (REWRITE_TAC[polar_high_frac_def, polar_mid_frac_def, polar_low_frac_def] >>
      qpat_assum ‘Abbrev (M = _)’
        (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
      ASM_REWRITE_TAC[])
  >- (* Lower bound on polar_high_frac *)
     (drule_then (qspec_then ‘n’ strip_assume_tac) polar_Z_I_sums_real >>
      ‘REAL_SUM_IMAGE (polar_I W n) (count (2 ** n)) =
       REAL_SUM_IMAGE (polar_I W n) H +
       REAL_SUM_IMAGE (polar_I W n) M +
       REAL_SUM_IMAGE (polar_I W n) L’
        by (‘REAL_SUM_IMAGE (polar_I W n) (count (2 ** n)) =
             REAL_SUM_IMAGE (polar_I W n) (H ∪ (M ∪ L))’
              by metis_tac[] >>
            pop_assum SUBST1_TAC >>
            DEP_REWRITE_TAC[REAL_SUM_IMAGE_DISJOINT_UNION] >>
            gvs[] >> REAL_ARITH_TAC) >>
      ‘REAL_SUM_IMAGE (polar_I W n) H ≤ &(CARD H) * 1 ∧
       REAL_SUM_IMAGE (polar_I W n) M ≤ &(CARD M) * 1 ∧
       REAL_SUM_IMAGE (polar_I W n) L ≤ &(CARD L) * eps’
        by (rpt conj_tac
            >- (‘&(CARD H) * (1 : real) = REAL_SUM_IMAGE (λi. 1) H’
                  by gvs[REAL_SUM_IMAGE_FINITE_CONST3] >>
                pop_assum SUBST1_TAC >>
                irule REAL_SUM_IMAGE_MONO >> gvs[Abbr ‘H’] >>
                qx_gen_tac ‘i’ >> strip_tac >> drule_all polar_Z_I_props >> simp[])
            >- (‘&(CARD M) * (1 : real) = REAL_SUM_IMAGE (λi. 1) M’
                  by gvs[REAL_SUM_IMAGE_FINITE_CONST3] >>
                pop_assum SUBST1_TAC >>
                irule REAL_SUM_IMAGE_MONO >> gvs[Abbr ‘M’] >>
                qx_gen_tac ‘i’ >> strip_tac >> drule_all polar_Z_I_props >> simp[])
            >- (‘&(CARD L) * eps = REAL_SUM_IMAGE (λi. eps) L’
                  by gvs[REAL_SUM_IMAGE_FINITE_CONST3] >>
                pop_assum SUBST1_TAC >>
                irule REAL_SUM_IMAGE_MONO >> reverse conj_tac >- fs[] >>
                qx_gen_tac ‘i’ >> simp[Abbr ‘L’] >> strip_tac >> REAL_ARITH_TAC)) >>
      ‘(&(2 ** n) : real) * real (symmetric_capacity W) ≤
       &(CARD H) + &(CARD M) + &(CARD L) * eps’
        by REAL_ARITH_TAC >>
      ‘real (symmetric_capacity W) ≤
       (&(CARD H) : real) / &(2 ** n) + (&(CARD M) : real) / &(2 ** n) +
       eps * ((&(CARD L) : real) / &(2 ** n))’
        by (irule REAL_LE_LCANCEL_IMP >> qexists_tac ‘&(2 ** n)’ >>
            conj_tac >- simp[two_pow_pos_real] >>
            ‘(&(2 ** n) : real) ≠ 0 ⇒
             &(2 ** n) *
             ((&(CARD H) : real) / &(2 ** n) + (&(CARD M) : real) / &(2 ** n) +
              eps * ((&(CARD L) : real) / &(2 ** n))) =
             &(CARD H) + &(CARD M) + &(CARD L) * eps’
              by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
            pop_assum mp_tac >> impl_tac >- simp[two_pow_pos_real] >>
            disch_then (fn th => REWRITE_TAC[th]) >> ASM_REWRITE_TAC[]) >>
      ‘0 ≤ (&(CARD H) : real) / &(2 ** n) ∧
       0 ≤ (&(CARD M) : real) / &(2 ** n) ∧
       (&(CARD L) : real) / &(2 ** n) ≤ 1’
        by (‘0 ≤ (&(CARD H) : real) / &(2 ** n) ∧
             0 ≤ (&(CARD M) : real) / &(2 ** n)’
              by simp[] >>
            REAL_ARITH_TAC) >>
      ‘eps * ((&(CARD L) : real) / &(2 ** n)) ≤ eps * 1’
        by (irule REAL_LE_LMUL_IMP >> REAL_ARITH_TAC) >>
      REWRITE_TAC[polar_high_frac_def, polar_mid_frac_def] >>
      qpat_assum ‘Abbrev (M = _)’
        (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
      ASM_REWRITE_TAC[] >> REAL_ARITH_TAC)
  >- (* Upper bound on polar_high_frac *)
     (qpat_x_assum ‘count (2 ** n) = _’ kall_tac >>
      drule_then (qspec_then ‘n’ strip_assume_tac) polar_Z_I_sums_real >>
      ‘(&(CARD H) : real) * (1 - eps) ≤
       REAL_SUM_IMAGE (polar_I W n) (count (2 ** n))’
        by (‘(&(CARD H) : real) * (1 - eps) = REAL_SUM_IMAGE (λi. 1 - eps) H’
              by gvs[REAL_SUM_IMAGE_FINITE_CONST3] >>
            pop_assum SUBST1_TAC >>
            irule REAL_LE_TRANS >>
            qexists_tac ‘REAL_SUM_IMAGE (polar_I W n) H’ >>
            conj_tac
            >- (irule REAL_SUM_IMAGE_MONO >> reverse conj_tac >- fs[] >>
                qx_gen_tac ‘i’ >> simp[Abbr ‘H’] >> strip_tac >> REAL_ARITH_TAC)
            >- (irule REAL_SUM_IMAGE_MONO_SET >> fs[] >>
                qx_gen_tac ‘i’ >> strip_tac >>
                drule_all polar_Z_I_props >> simp[])) >>
      ‘((&(CARD H) : real) / &(2 ** n)) * (1 - eps) ≤
       real (symmetric_capacity W)’
        by (irule REAL_LE_LCANCEL_IMP >> qexists_tac ‘&(2 ** n)’ >>
            conj_tac >- simp[two_pow_pos_real] >>
            ‘(&(2 ** n) : real) ≠ 0 ⇒
             &(2 ** n) * (((&(CARD H) : real) / &(2 ** n)) * (1 - eps)) =
             &(CARD H) * (1 - eps)’
              by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
            pop_assum mp_tac >> impl_tac >- simp[two_pow_pos_real] >>
            disch_then (fn th => REWRITE_TAC[th]) >>
            ‘(&(2 ** n) : real) * real (symmetric_capacity W) =
             real (symmetric_capacity W) * &(2 ** n)’
              by CONV_TAC (EQT_INTRO o REAL_RING) >>
            REAL_ARITH_TAC) >>
      ‘0 ≤ (&(CARD M) : real) / &(2 ** n) ∧
       0 ≤ (&(CARD L) : real) / &(2 ** n)’
        by simp[] >>
      ‘(&(CARD H) : real) / &(2 ** n) ≤ 1’ by REAL_ARITH_TAC >>
      ‘eps * ((&(CARD H) : real) / &(2 ** n)) ≤ eps * 1’
        by (irule REAL_LE_LMUL_IMP >> REAL_ARITH_TAC) >>
      ‘((&(CARD H) : real) / &(2 ** n)) * (1 - eps) =
       (&(CARD H) : real) / &(2 ** n) - eps * ((&(CARD H) : real) / &(2 ** n))’
        by CONV_TAC (EQT_INTRO o REAL_RING) >>
      REWRITE_TAC[polar_high_frac_def] >> ASM_REWRITE_TAC[] >> REAL_ARITH_TAC)
QED

(* Theorem 1 (Erdal Arıkan, 2009, arXiv:0807.3917, Section I-B.3, p. 3 &
   Section IV-A, pp. 8-9): Asymptotic channel polarization for any B-DMC W
   and any fixed threshold delta in (0, 1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_1_channel_polarization:
  ∀(W : (bool, β) memoryless_channel) (delta : real).
    wf_bdmc W ∧ 0 < delta ∧ delta < 1 ⇒
    ((λn : num.
        (&(CARD {i | i < 2 ** n ∧
                     Normal (1 - delta) <
                     symmetric_capacity (split_channel W (2 ** n) i)}) : real) /
        &(2 ** n)) : num -> real) -->
      (real (symmetric_capacity W) : real) ∧
    ((λn : num.
        (&(CARD {i | i < 2 ** n ∧
                     symmetric_capacity (split_channel W (2 ** n) i) <
                     Normal delta}) : real) /
        &(2 ** n)) : num -> real) -->
      ((1 - real (symmetric_capacity W)) : real)
Proof
  qx_genl_tac [‘W’, ‘delta’] >> strip_tac >>
  REWRITE_TAC[GSYM polar_high_frac_def, GSYM polar_low_frac_def] >>
  (* Shared epsilon-N helper for any e > 0 *)
  ‘∀e : real.
     0 < e ⇒
     ∃N. ∀n.
       n ≥ N ⇒
       abs (polar_high_frac W delta n - real (symmetric_capacity W)) < e ∧
       abs (polar_low_frac W delta n - (1 - real (symmetric_capacity W))) < e’
    by (qx_gen_tac ‘e’ >> strip_tac >>
        qabbrev_tac ‘m0 = realax$min (1 / 2)
                            (realax$min delta (realax$min (1 - delta) e))’ >>
        qabbrev_tac ‘eps = (1 / 2) * m0’ >>
        ‘0 < m0 ∧ m0 ≤ 1 / 2 ∧ m0 ≤ delta ∧ m0 ≤ 1 - delta ∧ m0 ≤ e’
          by (qpat_assum ‘Abbrev (m0 = _)’
                (fn th => REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
              REWRITE_TAC[REAL_LT_MIN, REAL_MIN_LE] >>
              simp[] >> REAL_ARITH_TAC) >>
        ‘0 < eps ∧ eps < 1 / 2 ∧ eps < delta ∧ eps < 1 - delta ∧ 2 * eps ≤ e’
          by (simp[Abbr ‘eps’] >> REAL_ARITH_TAC) >>
        qspecl_then [‘W’, ‘eps’] mp_tac polar_mid_frac_tendsto_0 >>
        simp[seqTheory.SEQ] >>
        ‘0 < (1 / 2) * e’ by REAL_ARITH_TAC >>
        disch_then (qspec_then ‘(1 / 2) * e’ mp_tac) >> simp[] >>
        disch_then (qx_choose_then ‘N0’ assume_tac) >>
        qexists_tac ‘N0’ >> qx_gen_tac ‘n’ >> strip_tac >>
        qspec_then ‘n’ strip_assume_tac two_pow_pos_real >>
        ‘0 ≤ polar_mid_frac W eps n’ by simp[polar_mid_frac_def] >>
        first_x_assum (qspec_then ‘n’ mp_tac) >>
        impl_tac >- decide_tac >>
        simp[realTheory.abs] >> strip_tac >>
        qspecl_then [‘W’, ‘eps’, ‘n’] mp_tac polar_frac_conservation_bounds >>
        simp[] >> strip_tac >>
        (* Monotonicity & disjointness inclusions between delta and eps *)
        ‘polar_high_frac W eps n ≤ polar_high_frac W delta n ∧
         polar_high_frac W delta n ≤ 1 - polar_low_frac W eps n ∧
         polar_low_frac W eps n ≤ polar_low_frac W delta n ∧
         polar_low_frac W delta n ≤ 1 - polar_high_frac W eps n’
          by (qabbrev_tac ‘Hd = {i | i < 2 ** n ∧
                                     Normal (1 - delta) <
                                     symmetric_capacity (split_channel W (2 ** n) i)}’ >>
              qabbrev_tac ‘He = {i | i < 2 ** n ∧
                                     Normal (1 - eps) <
                                     symmetric_capacity (split_channel W (2 ** n) i)}’ >>
              qabbrev_tac ‘Ld = {i | i < 2 ** n ∧
                                     symmetric_capacity (split_channel W (2 ** n) i) <
                                     Normal delta}’ >>
              qabbrev_tac ‘Le = {i | i < 2 ** n ∧
                                     symmetric_capacity (split_channel W (2 ** n) i) <
                                     Normal eps}’ >>
              ‘He ⊆ Hd ∧ Le ⊆ Ld ∧ Hd ⊆ count (2 ** n) ∧ He ⊆ count (2 ** n) ∧
               Ld ⊆ count (2 ** n) ∧ Le ⊆ count (2 ** n) ∧
               DISJOINT Hd Le ∧ DISJOINT Ld He’
                by (rpt conj_tac
                    >- (rw[Abbr ‘Hd’, Abbr ‘He’, SUBSET_DEF] >>
                        drule_all polar_Z_I_props >> strip_tac >>
                        gvs[extreal_lt_eq] >> REAL_ARITH_TAC)
                    >- (rw[Abbr ‘Ld’, Abbr ‘Le’, SUBSET_DEF] >>
                        drule_all polar_Z_I_props >> strip_tac >>
                        gvs[extreal_lt_eq] >> REAL_ARITH_TAC)
                    >- rw[Abbr ‘Hd’, SUBSET_DEF]
                    >- rw[Abbr ‘He’, SUBSET_DEF]
                    >- rw[Abbr ‘Ld’, SUBSET_DEF]
                    >- rw[Abbr ‘Le’, SUBSET_DEF]
                    >- (rw[Abbr ‘Hd’, Abbr ‘Le’, DISJOINT_DEF, Once EXTENSION] >>
                        CCONTR_TAC >> gvs[] >>
                        drule_all polar_Z_I_props >> strip_tac >>
                        gvs[extreal_lt_eq] >> REAL_ARITH_TAC)
                    >- (rw[Abbr ‘Ld’, Abbr ‘He’, DISJOINT_DEF, Once EXTENSION] >>
                        CCONTR_TAC >> gvs[] >>
                        drule_all polar_Z_I_props >> strip_tac >>
                        gvs[extreal_lt_eq] >> REAL_ARITH_TAC)) >>
              ‘FINITE Hd ∧ FINITE He ∧ FINITE Ld ∧ FINITE Le’
                by (rpt conj_tac >>
                    (irule SUBSET_FINITE_I >> qexists_tac ‘count (2 ** n)’ >>
                     simp[])) >>
              ‘CARD He ≤ CARD Hd ∧ CARD Le ≤ CARD Ld’
                by (conj_tac >> irule CARD_SUBSET >> simp[]) >>
              ‘CARD Hd + CARD Le ≤ 2 ** n ∧ CARD Ld + CARD He ≤ 2 ** n’
                by (‘CARD (Hd ∪ Le) = CARD Hd + CARD Le ∧
                     CARD (Ld ∪ He) = CARD Ld + CARD He’
                      by (conj_tac >> irule CARD_DISJOINT_UNION_LOCAL >> simp[]) >>
                    ‘CARD (Hd ∪ Le) ≤ CARD (count (2 ** n)) ∧
                     CARD (Ld ∪ He) ≤ CARD (count (2 ** n))’
                      by (conj_tac >> irule CARD_SUBSET >> simp[]) >>
                    gvs[CARD_COUNT]) >>
              ‘(&(CARD Hd) : real) + &(CARD Le) ≤ &(2 ** n) ∧
               (&(CARD Ld) : real) + &(CARD He) ≤ &(2 ** n)’
                by simp[] >>
              REWRITE_TAC[polar_high_frac_def, polar_low_frac_def] >>
              qpat_assum ‘Abbrev (Hd = _)’
                (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
              qpat_assum ‘Abbrev (He = _)’
                (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
              qpat_assum ‘Abbrev (Ld = _)’
                (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
              qpat_assum ‘Abbrev (Le = _)’
                (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
              simp[two_pow_pos_real, REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ,
                   REAL_SUB_RDISTRIB, REAL_DIV_RMUL] >>
              REAL_ARITH_TAC) >>
        REWRITE_TAC[ABS_BOUNDS_LT] >> REAL_ARITH_TAC) >>
  conj_tac >> simp[seqTheory.SEQ, ETA_THM] >>
  qx_gen_tac ‘e’ >> strip_tac >>
  first_x_assum (drule_then (qx_choose_then ‘N0’ assume_tac)) >>
  qexists_tac ‘N0’ >> rw[]
QED

(* Bhattacharyya polarization corollary of Theorem 1: for any threshold alpha in
   (0, 1), both fractions P_n(Z_n < alpha) and P_n(Z_n <= alpha) converge to I(W).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_1_bhattacharyya_polarization:
  ∀(W : (bool, β) memoryless_channel) (alpha : real).
    wf_bdmc W ∧ 0 < alpha ∧ alpha < 1 ⇒
    ((λn : num.
        (&(CARD {i | i < 2 ** n ∧
                     bhattacharyya (split_channel W (2 ** n) i) <
                     Normal alpha}) : real) /
        &(2 ** n)) : num -> real) -->
      (real (symmetric_capacity W) : real) ∧
    ((λn : num.
        (&(CARD {i | i < 2 ** n ∧
                     bhattacharyya (split_channel W (2 ** n) i) ≤
                     Normal alpha}) : real) /
        &(2 ** n)) : num -> real) -->
      (real (symmetric_capacity W) : real)
Proof
  qx_genl_tac [‘W’, ‘alpha’] >> strip_tac >>
  qabbrev_tac ‘d1 = 1 - real$sqrt (1 - alpha pow 2)’ >>
  qabbrev_tac ‘d2 = transc$logr 2 (2 / (1 + alpha))’ >>
  ‘0 < d1 ∧ d1 < 1’
    by (simp[Abbr ‘d1’] >>
        ‘0 < alpha pow 2 ∧ alpha pow 2 < 1’
          by (conj_tac >- (simp[] >> REAL_ARITH_TAC) >>
              irule realTheory.POW_2_LT_1 >> REAL_ARITH_TAC) >>
        ‘0 < real$sqrt (1 - alpha pow 2) ∧
         real$sqrt (1 - alpha pow 2) < real$sqrt 1’
          by (conj_tac
              >- (irule realTheory.SQRT_POS_LT >> REAL_ARITH_TAC)
              >- (irule realTheory.SQRT_MONO_LT >> REAL_ARITH_TAC)) >>
        gvs[realTheory.SQRT_1] >> REAL_ARITH_TAC) >>
  ‘0 < d2 ∧ d2 < 1’
    by (simp[Abbr ‘d2’] >>
        ‘0 < 1 + alpha’ by REAL_ARITH_TAC >>
        ‘0 < (1 : real) ∧ 0 < (2 : real) ∧ 1 < (2 : real) ∧
         0 < 2 / (1 + alpha) ∧ 1 < 2 / (1 + alpha) ∧ 2 / (1 + alpha) < 2’
          by (simp[REAL_LT_RDIV_EQ, REAL_LT_LDIV_EQ] >> REAL_ARITH_TAC) >>
        ‘transc$logr 2 1 < transc$logr 2 (2 / (1 + alpha)) ∧
         transc$logr 2 (2 / (1 + alpha)) < transc$logr 2 2’
          by (conj_tac >> simp[transcTheory.LOGR_MONO_LT]) >>
        gvs[transcTheory.logr_1, logr_2_2]) >>
  (* Sandwich both Z < alpha and Z <= alpha between high_frac(d1) and 1 - low_frac(d2) *)
  ‘∀n.
     polar_high_frac W d1 n ≤
       (&(CARD {i | i < 2 ** n ∧
                    bhattacharyya (split_channel W (2 ** n) i) <
                    Normal alpha}) : real) / &(2 ** n) ∧
     (&(CARD {i | i < 2 ** n ∧
                  bhattacharyya (split_channel W (2 ** n) i) <
                  Normal alpha}) : real) / &(2 ** n) ≤
       (&(CARD {i | i < 2 ** n ∧
                    bhattacharyya (split_channel W (2 ** n) i) ≤
                    Normal alpha}) : real) / &(2 ** n) ∧
     (&(CARD {i | i < 2 ** n ∧
                  bhattacharyya (split_channel W (2 ** n) i) ≤
                  Normal alpha}) : real) / &(2 ** n) ≤
       1 - polar_low_frac W d2 n’
    by (gen_tac >>
        qspec_then ‘n’ strip_assume_tac two_pow_pos_real >>
        qabbrev_tac ‘H1 = {i | i < 2 ** n ∧
                               Normal (1 - d1) <
                               symmetric_capacity (split_channel W (2 ** n) i)}’ >>
        qabbrev_tac ‘Zlt = {i | i < 2 ** n ∧
                                bhattacharyya (split_channel W (2 ** n) i) <
                                Normal alpha}’ >>
        qabbrev_tac ‘Zle = {i | i < 2 ** n ∧
                                bhattacharyya (split_channel W (2 ** n) i) ≤
                                Normal alpha}’ >>
        qabbrev_tac ‘L2 = {i | i < 2 ** n ∧
                               symmetric_capacity (split_channel W (2 ** n) i) <
                               Normal d2}’ >>
        ‘H1 ⊆ Zlt ∧ Zlt ⊆ Zle ∧ Zle ⊆ count (2 ** n) ∧ L2 ⊆ count (2 ** n) ∧
         DISJOINT Zle L2’
          by (rpt conj_tac
              >- (simp[Abbr ‘H1’, Abbr ‘Zlt’, SUBSET_DEF] >>
                  qx_gen_tac ‘x’ >> strip_tac >>
                  drule_all polar_Z_I_props >> strip_tac >>
                  gvs[Abbr ‘d1’, extreal_lt_eq] >>
                  CCONTR_TAC >>
                  ‘alpha ≤ polar_Z W n x’ by REAL_ARITH_TAC >>
                  ‘alpha pow 2 ≤ (polar_Z W n x) pow 2’
                    by (PURE_REWRITE_TAC[realTheory.POW_2] >>
                        irule REAL_LE_MUL2 >> REAL_ARITH_TAC) >>
                  ‘0 ≤ 1 - (polar_Z W n x) pow 2’
                    by (PURE_REWRITE_TAC[realTheory.POW_2] >>
                        ‘polar_Z W n x * polar_Z W n x ≤ 1 * 1’
                          by (irule REAL_LE_MUL2 >> simp[]) >>
                        REAL_ARITH_TAC) >>
                  ‘real$sqrt (1 - (polar_Z W n x) pow 2) ≤
                   real$sqrt (1 - alpha pow 2)’
                    by (irule realTheory.SQRT_MONO_LE >> REAL_ARITH_TAC) >>
                  REAL_ARITH_TAC)
              >- (simp[Abbr ‘Zlt’, Abbr ‘Zle’, SUBSET_DEF] >>
                  qx_gen_tac ‘x’ >> strip_tac >>
                  drule_all polar_Z_I_props >> strip_tac >>
                  gvs[extreal_lt_eq, extreal_le_eq] >> REAL_ARITH_TAC)
              >- rw[Abbr ‘Zle’, SUBSET_DEF]
              >- rw[Abbr ‘L2’, SUBSET_DEF]
              >- (simp[Abbr ‘Zle’, Abbr ‘L2’, DISJOINT_DEF, EXTENSION] >>
                  qx_gen_tac ‘x’ >> CCONTR_TAC >> gvs[] >>
                  drule_all polar_Z_I_props >> strip_tac >>
                  gvs[Abbr ‘d2’, extreal_le_eq, extreal_lt_eq] >>
                  ‘0 < 1 + polar_Z W n x ∧ 0 < 1 + alpha’ by REAL_ARITH_TAC >>
                  ‘0 < 2 / (1 + alpha)’
                    by (irule REAL_LT_DIV >> REAL_ARITH_TAC) >>
                  ‘2 / (1 + alpha) ≤ 2 / (1 + polar_Z W n x)’
                    by (irule REAL_LE_LCANCEL_IMP >>
                        qexists_tac ‘(1 + alpha) * (1 + polar_Z W n x)’ >>
                        conj_tac >- (irule REAL_LT_MUL >> REAL_ARITH_TAC) >>
                        ‘1 + alpha ≠ 0 ∧ 1 + polar_Z W n x ≠ 0 ⇒
                         ((1 + alpha) * (1 + polar_Z W n x)) * (2 / (1 + alpha)) =
                           2 * (1 + polar_Z W n x) ∧
                         ((1 + alpha) * (1 + polar_Z W n x)) *
                           (2 / (1 + polar_Z W n x)) =
                           2 * (1 + alpha)’
                          by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
                        pop_assum mp_tac >> impl_tac >- REAL_ARITH_TAC >>
                        disch_then (fn th => REWRITE_TAC[th]) >>
                        REAL_ARITH_TAC) >>
                  ‘transc$logr 2 (2 / (1 + alpha)) ≤
                   transc$logr 2 (2 / (1 + polar_Z W n x))’
                    by (irule transcTheory.LOGR_MONO_LE_IMP >> simp[]) >>
                  REAL_ARITH_TAC)) >>
        ‘FINITE H1 ∧ FINITE Zlt ∧ FINITE Zle ∧ FINITE L2’
          by (rpt conj_tac >>
              (irule SUBSET_FINITE_I >> qexists_tac ‘count (2 ** n)’ >>
               rw[Abbr ‘H1’, Abbr ‘Zlt’, Abbr ‘Zle’, Abbr ‘L2’, SUBSET_DEF])) >>
        ‘CARD H1 ≤ CARD Zlt ∧ CARD Zlt ≤ CARD Zle’
          by (conj_tac >> irule CARD_SUBSET >> simp[]) >>
        ‘CARD Zle + CARD L2 ≤ 2 ** n’
          by (‘CARD (Zle ∪ L2) = CARD Zle + CARD L2’
                by (irule CARD_DISJOINT_UNION_LOCAL >> simp[]) >>
              ‘CARD (Zle ∪ L2) ≤ CARD (count (2 ** n))’
                by (irule CARD_SUBSET >> simp[]) >>
              gvs[CARD_COUNT]) >>
        ‘(&(CARD Zle) : real) + &(CARD L2) ≤ &(2 ** n)’ by simp[] >>
        REWRITE_TAC[polar_high_frac_def, polar_low_frac_def] >>
        qpat_assum ‘Abbrev (H1 = _)’
          (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        qpat_assum ‘Abbrev (L2 = _)’
          (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        qpat_assum ‘Abbrev (Zlt = _)’
          (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        qpat_assum ‘Abbrev (Zle = _)’
          (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        simp[two_pow_pos_real, REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ,
             REAL_SUB_RDISTRIB, REAL_DIV_RMUL] >>
        REAL_ARITH_TAC) >>
  qspecl_then [‘W’, ‘d1’] mp_tac theorem_1_channel_polarization >>
  qspecl_then [‘W’, ‘d2’] mp_tac theorem_1_channel_polarization >>
  REWRITE_TAC[GSYM polar_high_frac_def, GSYM polar_low_frac_def, ETA_THM] >>
  simp[] >> ntac 2 strip_tac >>
  ‘(λn : num. 1 - polar_low_frac W d2 n) --> real (symmetric_capacity W)’
    by (‘1 - (1 - real (symmetric_capacity W)) = real (symmetric_capacity W)’
          by REAL_ARITH_TAC >>
        qspecl_then [‘λn : num. (1 : real)’, ‘1 : real’,
                     ‘polar_low_frac W d2’, ‘1 - real (symmetric_capacity W)’]
          mp_tac seqTheory.SEQ_SUB >>
        BETA_TAC >> ASM_REWRITE_TAC[seqTheory.SEQ_CONST] >> simp[]) >>
  conj_tac >>
  (irule seqTheory.SEQ_SANDWICH >>
   qexistsl_tac [‘polar_high_frac W d1’, ‘λn : num. 1 - polar_low_frac W d2 n’] >>
   ASM_REWRITE_TAC[] >> rpt strip_tac >> BETA_TAC >>
   first_x_assum (qspec_then ‘n’ strip_assume_tac) >> REAL_ARITH_TAC)
QED

(* Inequality part of Proposition 11, polymorphic in the output alphabet β so
   it can be applied both to W and to split_channel W 2 {0, 1}.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_11_le[local]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒ 1 ≤ symmetric_capacity W + bhattacharyya W
Proof
  rpt strip_tac >>
  drule symmetric_capacity_bounds >>
  drule bhattacharyya_bounds >>
  rpt strip_tac >>
  simp[extreal_of_num_def, extreal_add_eq, extreal_le_eq] >>
  irule REAL_LE_EPSILON >>
  qx_gen_tac ‘e’ >> strip_tac >>
  Cases_on ‘1 ≤ e’ >- REAL_ARITH_TAC >>
  ‘0 < e ∧ e < 1’ by REAL_ARITH_TAC >>
  qabbrev_tac ‘d = transc$logr 2 (2 / (2 - e))’ >>
  ‘0 < d ∧ d < 1’
    by (simp[Abbr ‘d’] >>
        ‘0 < 2 - e’ by REAL_ARITH_TAC >>
        ‘0 < (1 : real) ∧ 0 < (2 : real) ∧ 1 < (2 : real) ∧
         0 < 2 / (2 - e) ∧ 1 < 2 / (2 - e) ∧ 2 / (2 - e) < 2’
          by (simp[REAL_LT_RDIV_EQ, REAL_LT_LDIV_EQ] >> REAL_ARITH_TAC) >>
        ‘transc$logr 2 1 < transc$logr 2 (2 / (2 - e)) ∧
         transc$logr 2 (2 / (2 - e)) < transc$logr 2 2’
          by (conj_tac >> simp[transcTheory.LOGR_MONO_LT]) >>
        gvs[transcTheory.logr_1, logr_2_2]) >>
  (* For every n, (1 - e) * polar_low_frac W d n <= z *)
  ‘∀n. (1 - e) * polar_low_frac W d n ≤ z’
    by (gen_tac >>
        qspec_then ‘n’ strip_assume_tac two_pow_pos_real >>
        drule_then (qspec_then ‘n’ strip_assume_tac) polar_Z_I_sums_real >>
        gvs[real_normal] >>
        qabbrev_tac ‘Ld = {i | i < 2 ** n ∧
                               symmetric_capacity (split_channel W (2 ** n) i) <
                               Normal d}’ >>
        ‘Ld ⊆ count (2 ** n) ∧ FINITE Ld’
          by (conj_tac >- rw[Abbr ‘Ld’, SUBSET_DEF] >>
              irule SUBSET_FINITE_I >> qexists_tac ‘count (2 ** n)’ >>
              rw[Abbr ‘Ld’, SUBSET_DEF]) >>
        ‘(&(CARD Ld) : real) * (1 - e) ≤
         REAL_SUM_IMAGE (polar_Z W n) (count (2 ** n))’
          by (‘(&(CARD Ld) : real) * (1 - e) = REAL_SUM_IMAGE (λi. 1 - e) Ld’
                by gvs[REAL_SUM_IMAGE_FINITE_CONST3] >>
              pop_assum SUBST1_TAC >>
              irule REAL_LE_TRANS >>
              qexists_tac ‘REAL_SUM_IMAGE (polar_Z W n) Ld’ >>
              conj_tac
              >- (irule REAL_SUM_IMAGE_MONO >> reverse conj_tac >- fs[] >>
                  qx_gen_tac ‘i’ >> simp[Abbr ‘Ld’] >> strip_tac >>
                  drule_all polar_Z_I_props >> strip_tac >>
                  gvs[Abbr ‘d’, extreal_lt_eq] >>
                  ‘transc$logr 2 (2 / (1 + polar_Z W n i)) <
                   transc$logr 2 (2 / (2 - e))’
                    by REAL_ARITH_TAC >>
                  ‘0 < 1 + polar_Z W n i ∧ 0 < 2 - e ∧ 1 < (2 : real)’
                    by REAL_ARITH_TAC >>
                  ‘0 < 2 / (1 + polar_Z W n i) ∧ 0 < 2 / (2 - e)’
                    by (conj_tac >> irule REAL_LT_DIV >> REAL_ARITH_TAC) >>
                  ‘2 / (1 + polar_Z W n i) < 2 / (2 - e)’
                    by gvs[transcTheory.LOGR_MONO_LT] >>
                  ‘0 < (1 + polar_Z W n i) * (2 - e)’
                    by (irule REAL_LT_MUL >> REAL_ARITH_TAC) >>
                  ‘((1 + polar_Z W n i) * (2 - e)) * (2 / (1 + polar_Z W n i)) <
                   ((1 + polar_Z W n i) * (2 - e)) * (2 / (2 - e))’
                    by (irule REAL_LT_LMUL_IMP >> ASM_REWRITE_TAC[]) >>
                  ‘1 + polar_Z W n i ≠ 0 ∧ 2 - e ≠ 0 ⇒
                   ((1 + polar_Z W n i) * (2 - e)) * (2 / (1 + polar_Z W n i)) =
                     2 * (2 - e) ∧
                   ((1 + polar_Z W n i) * (2 - e)) * (2 / (2 - e)) =
                     2 * (1 + polar_Z W n i)’
                    by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
                  pop_assum mp_tac >> impl_tac >- REAL_ARITH_TAC >>
                  disch_then (fn th => FULL_SIMP_TAC std_ss [th]) >>
                  REAL_ARITH_TAC)
              >- (irule REAL_SUM_IMAGE_MONO_SET >> fs[] >>
                  qx_gen_tac ‘i’ >> strip_tac >>
                  drule_all polar_Z_I_props >> simp[])) >>
        REWRITE_TAC[polar_low_frac_def] >>
        qpat_assum ‘Abbrev (Ld = _)’
          (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        irule REAL_LE_LCANCEL_IMP >> qexists_tac ‘&(2 ** n)’ >>
        conj_tac >- simp[two_pow_pos_real] >>
        ‘(&(2 ** n) : real) ≠ 0 ⇒
         &(2 ** n) * ((1 - e) * ((&(CARD Ld) : real) / &(2 ** n))) =
         &(CARD Ld) * (1 - e)’
          by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
        pop_assum mp_tac >> impl_tac >- simp[two_pow_pos_real] >>
        disch_then (fn th => REWRITE_TAC[th]) >>
        ‘(&(2 ** n) : real) * z = z * &(2 ** n)’
          by CONV_TAC (EQT_INTRO o REAL_RING) >>
        REAL_ARITH_TAC) >>
  qspecl_then [‘W’, ‘d’] mp_tac theorem_1_channel_polarization >>
  REWRITE_TAC[GSYM polar_low_frac_def, ETA_THM] >>
  simp[real_normal] >> strip_tac >>
  ‘(λn : num. (1 - e) * polar_low_frac W d n) --> ((1 - e) * (1 - c))’
    by (qspecl_then [‘λn : num. 1 - e’, ‘1 - e’, ‘polar_low_frac W d’, ‘1 - c’]
          mp_tac seqTheory.SEQ_MUL >>
        BETA_TAC >> ASM_REWRITE_TAC[seqTheory.SEQ_CONST] >> simp[]) >>
  ‘(1 - e) * (1 - c) ≤ z’
    by (irule seqTheory.SEQ_LE_IMP_LIM_LE >>
        qexists_tac ‘λn : num. (1 - e) * polar_low_frac W d n’ >>
        ASM_REWRITE_TAC[] >> rpt strip_tac >> BETA_TAC >> ASM_REWRITE_TAC[]) >>
  ‘1 - c ≤ 1 ∧ e * (1 - c) ≤ e * 1’
    by (conj_tac >- REAL_ARITH_TAC >>
        irule REAL_LE_LMUL_IMP >> REAL_ARITH_TAC) >>
  ‘(1 - c) - e ≤ (1 - e) * (1 - c)’
    by (‘(1 - e) * (1 - c) = (1 - c) - e * (1 - c)’
          by CONV_TAC (EQT_INTRO o REAL_RING) >>
        REAL_ARITH_TAC) >>
  REAL_ARITH_TAC
QED

(* Proposition 11 (Erdal Arıkan, 2009, arXiv:0807.3917, Section IV-A, p. 9):
   For any B-DMC W, I(W) + Z(W) >= 1, with equality if and only if W is a BEC.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_11:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    1 ≤ symmetric_capacity W + bhattacharyya W ∧
    (symmetric_capacity W + bhattacharyya W = 1 ⇔ is_bec W)
Proof
  rpt strip_tac
  >- simp[proposition_11_le]
  >- (eq_tac >> strip_tac
      >- (* I(W) + Z(W) = 1 ==> is_bec W via single-step split_channel W 2 {0, 1} *)
         (qspecl_then [‘W’, ‘1’, ‘0’] mp_tac polar_Z_I_props >>
          qspecl_then [‘W’, ‘1’, ‘1’] mp_tac polar_Z_I_props >>
          qspecl_then [‘W’, ‘1’] mp_tac polar_Z_I_sums_real >>
          simp[] >> ntac 3 strip_tac >>
          ‘1 ≤ symmetric_capacity (split_channel W 2 0) +
               bhattacharyya (split_channel W 2 0) ∧
           1 ≤ symmetric_capacity (split_channel W 2 1) +
               bhattacharyya (split_channel W 2 1)’
            by (conj_tac >> irule proposition_11_le >> simp[]) >>
          ‘∑ (λj. bhattacharyya (split_channel W 2 j)) (count 2) =
           Normal (REAL_SUM_IMAGE (polar_Z W 1) (count 2))’
            by (simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
                irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
                qx_gen_tac ‘j’ >> strip_tac >>
                qspecl_then [‘W’, ‘1’, ‘j’] mp_tac polar_Z_I_props >> simp[]) >>
          ‘count 2 = 1 INSERT (0 INSERT ∅)’
            by (CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (DECIDE “2 = SUC (SUC 0)”)))) >>
                simp[COUNT_SUC]) >>
          qspecl_then [‘W’, ‘1’, ‘0’] mp_tac proposition_7 >>
          qspecl_then [‘W’] mp_tac symmetric_capacity_bounds >>
          qspecl_then [‘W’] mp_tac bhattacharyya_bounds >>
          simp[] >> ntac 3 strip_tac >>
          gvs[REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT, real_normal,
              extreal_of_num_def, extreal_add_eq, extreal_mul_eq, extreal_le_eq] >>
          ‘polar_Z W 1 1 + polar_Z W 1 0 = 2 * z’ by REAL_ARITH_TAC >>
          metis_tac[REAL_ADD_COMM])
      >- (* is_bec W ==> I(W) + Z(W) = (1 - eps) + eps = 1 *)
         (drule is_bec_symmetric_capacity >>
          drule is_bec_bhattacharyya >>
          drule bec_erasure_prob_bounds >>
          rpt strip_tac >>
          gvs[extreal_of_num_def, extreal_sub_eq, extreal_add_eq] >>
          REAL_ARITH_TAC))
QED

(* ------------------------------------------------------------------------- *)
(* Part 2: Finite-Horizon Lemma 1 and Rate of Polarization (Theorem 2)       *)
(* ------------------------------------------------------------------------- *)

(* Cardinality of u INTER s expressed as a real indicator sum over u.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_INTER_AS_REAL_SUM[local]:
  ∀(u : α -> bool) s.
    FINITE u ⇒
    &(CARD (u ∩ s)) = REAL_SUM_IMAGE (λx. if x ∈ s then (1 : real) else 0) u
Proof
  ntac 2 gen_tac >> qid_spec_tac ‘u’ >>
  ho_match_mp_tac FINITE_INDUCT >> (conj_tac >- simp[REAL_SUM_IMAGE_THM]) >> qx_gen_tac ‘u’ >> strip_tac >> qx_gen_tac ‘e’ >> strip_tac >>
     simp[REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT, INSERT_INTER] >>
     Cases_on ‘e ∈ s’ >> simp[]
     >- (REWRITE_TAC[realTheory.REAL] >> REAL_ARITH_TAC)
QED

(* Cardinality of any subset of count N as a real indicator sum over count N.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_SUBSET_COUNT_AS_SUM[local]:
  ∀N (s : num -> bool).
    s ⊆ count N ⇒
    &(CARD s) = REAL_SUM_IMAGE (λi. if i ∈ s then (1 : real) else 0) (count N)
Proof
  rpt strip_tac >>
  ‘count N ∩ s = s’
    by (fs[SUBSET_DEF, Once EXTENSION] >> metis_tac[]) >>
  qspecl_then [‘count N’, ‘s’] mp_tac CARD_INTER_AS_REAL_SUM >>
  simp[]
QED

(* Set-difference cardinality lower bound: |s| <= |s \ t| + |t|.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_DIFF_LOWER_BOUND[local]:
  ∀(s : α -> bool) t.
    FINITE s ∧ FINITE t ⇒
    CARD s ≤ CARD (s DIFF t) + CARD t ∧
    &(CARD s) - &(CARD t) ≤ (&(CARD (s DIFF t)) : real)
Proof
  rpt gen_tac >> strip_tac >>
  ‘CARD (s ∩ t) ≤ CARD t’ by (irule CARD_SUBSET >> simp[]) >>
  ‘CARD s ≤ CARD (s DIFF t) + CARD t’ by (simp[] >> decide_tac) >>
  (conj_tac >- gvs[]) >>
  ‘(&(CARD s) : real) ≤ &(CARD (s DIFF t) + CARD t)’
    by ASM_REWRITE_TAC[realTheory.REAL_OF_NUM_LE] >>
  qpat_x_assum ‘(&(CARD s) : real) ≤ _’ mp_tac >>
  REWRITE_TAC[GSYM realTheory.REAL_OF_NUM_ADD] >>
  REAL_ARITH_TAC
QED

(* Euclidean division bijection count M x count D -> count (M * D).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem BIJ_COUNT_MUL_ADD[local]:
  ∀M D : num.
    0 < D ⇒
    BIJ (λ(j, r). j * D + r) (count M × count D) (count (M * D))
Proof
  rpt strip_tac >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_PROD, EXISTS_PROD] >>
  rpt conj_tac
  >- (qx_genl_tac [‘j’, ‘r’] >> strip_tac >>
      ‘(j + 1) * D ≤ M * D’ by simp[] >>
      ‘(j + 1) * D = j * D + D’ by simp[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >>
      decide_tac)
  >- (qx_genl_tac [‘j1’, ‘r1’, ‘j2’, ‘r2’] >> ntac 2 strip_tac >>
      ‘(j1 * D + r1) DIV D = j1 ∧ (j1 * D + r1) MOD D = r1’
        by (irule DIVMOD_UNIQ >> simp[]) >>
      ‘(j2 * D + r2) DIV D = j2 ∧ (j2 * D + r2) MOD D = r2’
        by (irule DIVMOD_UNIQ >> simp[]) >>
      ‘j1 * D + r1 = j2 * D + r2’ by decide_tac >>
      metis_tac[])
  >- (qx_genl_tac [‘j’, ‘r’] >> strip_tac >>
      ‘(j + 1) * D ≤ M * D’ by simp[] >>
      ‘(j + 1) * D = j * D + D’ by simp[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >>
      decide_tac)
  >- (qx_gen_tac ‘i’ >> strip_tac >>
      qexistsl_tac [‘i DIV D’, ‘i MOD D’] >>
      qspec_then ‘D’ mp_tac DIVISION >> simp[] >>
      disch_then (qspec_then ‘i’ strip_assume_tac) >>
      simp[] >>
      CCONTR_TAC >> ‘M ≤ i DIV D’ by decide_tac >>
      ‘M * D ≤ (i DIV D) * D’ by simp[] >>
      decide_tac)
QED

(* Fubini decomposition of REAL_SUM_IMAGE over count (M * D) via Euclidean
   division i = j * D + r.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_COUNT_MUL[local]:
  ∀M D (f : num -> real).
    0 < D ⇒
    REAL_SUM_IMAGE f (count (M * D)) =
    REAL_SUM_IMAGE (λj. REAL_SUM_IMAGE (λr. f (j * D + r)) (count D)) (count M)
Proof
  rpt strip_tac >>
  drule BIJ_COUNT_MUL_ADD >>
  disch_then (qspec_then ‘M’ assume_tac) >>
  ‘FINITE (count M × count D)’ by simp[] >>
  drule_all REAL_SUM_IMAGE_BIJ >>
  disch_then (qspec_then ‘f’ SUBST1_TAC) >>
  qspecl_then [‘count M’, ‘count D’, ‘λj r. (f ∘ (λ(j, r). j * D + r)) (j, r)’]
    mp_tac (GSYM REAL_SUM_IMAGE_REAL_SUM_IMAGE) >>
  simp[o_DEF] >>
  disch_then (SUBST1_TAC o SYM) >>
  irule REAL_SUM_IMAGE_EQ >> simp[FORALL_PROD]
QED

(* Ancestor bound: for m <= n and i < 2 ** n, i DIV (2 ** (n - m)) < 2 ** m.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem div_pow2_lt[local]:
  ∀i m n : num.
    m ≤ n ∧ i < 2 ** n ⇒ i DIV (2 ** (n - m)) < 2 ** m
Proof
  rpt strip_tac >>
  irule (iffRL arithmeticTheory.DIV_LT_X) >>
  simp[GSYM arithmeticTheory.EXP_ADD]
QED

(* Helper: DIV and upper-bound identities across AC variants of j * 2 ** d + r.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mul_add_pow2_props[local]:
  ∀m d j r : num.
    j < 2 ** m ∧ r < 2 ** d ⇒
    (j * 2 ** d + r) DIV (2 ** d) = j ∧
    (r + j * 2 ** d) DIV (2 ** d) = j ∧
    (2 ** d * j + r) DIV (2 ** d) = j ∧
    (r + 2 ** d * j) DIV (2 ** d) = j ∧
    j * 2 ** d + r < 2 ** (m + d) ∧
    r + j * 2 ** d < 2 ** (m + d) ∧
    2 ** d * j + r < 2 ** (m + d) ∧
    r + 2 ** d * j < 2 ** (m + d) ∧
    j * 2 ** d + r < 2 ** (d + m) ∧
    r + j * 2 ** d < 2 ** (d + m) ∧
    2 ** d * j + r < 2 ** (d + m) ∧
    r + 2 ** d * j < 2 ** (d + m)
Proof
  rpt gen_tac >> strip_tac >>
  ‘(j * 2 ** d + r) DIV (2 ** d) = j’
    by (irule DIV_UNIQUE >> qexists_tac ‘r’ >> simp[]) >>
  ‘j * 2 ** d + r < 2 ** (m + d)’
    by (‘0 < 2 ** d’ by simp[] >>
        qspecl_then [‘2 ** m’, ‘2 ** d’] mp_tac BIJ_COUNT_MUL_ADD >>
        simp[BIJ_DEF, INJ_DEF, FORALL_PROD, GSYM arithmeticTheory.EXP_ADD] >>
        strip_tac >> first_x_assum (qspecl_then [‘j’, ‘r’] mp_tac) >>
        simp[] >> decide_tac) >>
  ‘r + j * 2 ** d = j * 2 ** d + r ∧
   2 ** d * j + r = j * 2 ** d + r ∧
   r + 2 ** d * j = j * 2 ** d + r ∧
   d + m = m + d’
    by simp[] >>
  ASM_REWRITE_TAC[]
QED

(* Exact cardinality scaling when lifting a level-m predicate P along
   i |-> i DIV (2 ** d) to level m + d.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_LIFT_DIV_POW2[local]:
  ∀m d (P : num -> bool).
    (&(CARD {i | i < 2 ** (m + d) ∧ P (i DIV (2 ** d))}) : real) =
    &(2 ** d) * &(CARD {j | j < 2 ** m ∧ P j})
Proof
  rpt gen_tac >>
  qabbrev_tac ‘S_hi = {i | i < 2 ** (m + d) ∧ P (i DIV (2 ** d))}’ >>
  qabbrev_tac ‘S_lo = {j | j < 2 ** m ∧ P j}’ >>
  ‘S_hi ⊆ count (2 ** (m + d)) ∧ S_lo ⊆ count (2 ** m)’
    by simp[Abbr ‘S_hi’, Abbr ‘S_lo’, SUBSET_DEF] >>
  drule_then SUBST1_TAC CARD_SUBSET_COUNT_AS_SUM >>
  qpat_x_assum ‘S_hi ⊆ _’
    (SUBST1_TAC o MATCH_MP CARD_SUBSET_COUNT_AS_SUM) >>
  REWRITE_TAC[arithmeticTheory.EXP_ADD] >>
  qspecl_then [‘2 ** m’, ‘2 ** d’,
               ‘λi. if i ∈ S_hi then (1 : real) else 0’]
    mp_tac REAL_SUM_IMAGE_COUNT_MUL >>
  (impl_tac >- simp[]) >> disch_then SUBST1_TAC >> BETA_TAC >>
  simp[GSYM REAL_SUM_IMAGE_CMUL] >>
  irule REAL_SUM_IMAGE_EQ >> simp[] >>
  qx_gen_tac ‘j’ >> strip_tac >>
  ‘(&(2 ** d) : real) * (if j ∈ S_lo then 1 else 0) =
   REAL_SUM_IMAGE (λr. if j ∈ S_lo then (1 : real) else 0) (count (2 ** d))’
    by simp[REAL_SUM_IMAGE_FINITE_CONST3] >>
  pop_assum SUBST1_TAC >>
  irule REAL_SUM_IMAGE_EQ >> simp[] >>
  qx_gen_tac ‘r’ >> strip_tac >>
  qspecl_then [‘m’, ‘d’, ‘j’, ‘r’] mp_tac mul_add_pow2_props >>
  simp[Abbr ‘S_hi’, Abbr ‘S_lo’]
QED

(* Real-valued Bhattacharyya parameter of the j-th split channel at level m.

   Written by Gemini (Google DeepMind AI agent) *)
Definition z_node_def:
  z_node (W : (bool, β) memoryless_channel) (m : num) (j : num) : real =
    real (bhattacharyya (split_channel W (2 ** m) j))
End

(* Range bounds [0, 1] and Normal lifting for z_node W m j.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem z_node_bounds:
  ∀(W : (bool, β) memoryless_channel) m j.
    wf_bdmc W ∧ j < 2 ** m ⇒
    0 ≤ z_node W m j ∧
    z_node W m j ≤ 1 ∧
    bhattacharyya (split_channel W (2 ** m) j) = Normal (z_node W m j)
Proof
  rpt strip_tac >>
  drule_all polar_Z_I_props >>
  simp[z_node_def, polar_Z_def]
QED

(* Single-step Bhattacharyya recursion and supermartingale inequality on z_node.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem z_node_step:
  ∀(W : (bool, β) memoryless_channel) m j.
    wf_bdmc W ∧ j < 2 ** m ⇒
    z_node W (SUC m) (2 * j + 1) = (z_node W m j) pow 2 ∧
    z_node W (SUC m) (2 * j) ≤ 2 * z_node W m j - (z_node W m j) pow 2 ∧
    z_node W (SUC m) (2 * j) ≤ 2 * z_node W m j ∧
    z_node W (SUC m) (2 * j) + z_node W (SUC m) (2 * j + 1) ≤
      2 * z_node W m j
Proof
  rpt gen_tac >> strip_tac >>
  drule_all polar_Z_I_props >>
  REWRITE_TAC[z_node_def, GSYM polar_Z_def] >>
  strip_tac >>
  gvs[] >>
  ‘0 ≤ (polar_Z W m j) pow 2’ by simp[REAL_LE_POW2] >>
  REAL_ARITH_TAC
QED

(* Recursive count of d-step descendant paths from node (m, j) whose
   z_node trajectory exceeds threshold zeta at some time t in [0, d].

   Written by Gemini (Google DeepMind AI agent) *)
Definition bad_count_def:
  bad_count (W : (bool, β) memoryless_channel) (zeta : real) 0 m j =
    (if zeta < z_node W m j then 1n else 0n) ∧
  bad_count W zeta (SUC d) m j =
    (if zeta < z_node W m j then 2 ** (SUC d)
     else bad_count W zeta d (SUC m) (2 * j) +
          bad_count W zeta d (SUC m) (2 * j + 1))
End

(* Ville's finite-horizon supermartingale maximal inequality for bad_count
   starting from an arbitrary node (m, j).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bad_count_ville_bound[local]:
  ∀(W : (bool, β) memoryless_channel) (zeta : real) d m j.
    wf_bdmc W ∧ 0 ≤ zeta ∧ j < 2 ** m ⇒
    zeta * &(bad_count W zeta d m j) ≤ &(2 ** d) * z_node W m j
Proof
  ntac 2 gen_tac >> Induct_on ‘d’
  >- (rpt strip_tac >> simp[bad_count_def] >>
      drule_all z_node_bounds >> strip_tac >>
      rw[] >> REAL_ARITH_TAC)
  >> rpt strip_tac >> simp[bad_count_def] >>
     Cases_on ‘zeta < z_node W m j’ >> simp[]
     >- (‘zeta ≤ z_node W m j ∧ 0 ≤ (&(2 ** SUC d) : real)’
           by (simp[] >> REAL_ARITH_TAC) >>
         ‘zeta * &(2 ** SUC d) ≤ z_node W m j * &(2 ** SUC d)’
           by (irule realTheory.REAL_LE_RMUL_IMP >> simp[]) >>
         REAL_ARITH_TAC)
     >- (‘2 * j < 2 ** SUC m ∧ 2 * j + 1 < 2 ** SUC m’
           by simp[arithmeticTheory.EXP] >>
         first_assum (qspecl_then [‘SUC m’, ‘2 * j’] mp_tac) >>
         first_x_assum (qspecl_then [‘SUC m’, ‘2 * j + 1’] mp_tac) >>
         qspecl_then [‘W’, ‘m’, ‘j’] mp_tac z_node_step >>
         simp[] >> REWRITE_TAC[GSYM realTheory.REAL_OF_NUM_ADD, realTheory.REAL_LDISTRIB] >>
         ntac 3 strip_tac >>
         ‘zeta * &(bad_count W zeta d (SUC m) (2 * j)) +
          zeta * &(bad_count W zeta d (SUC m) (2 * j + 1)) ≤
          &(2 ** d) * (z_node W (SUC m) (2 * j) +
                       z_node W (SUC m) (2 * j + 1))’
           by (ASM_REWRITE_TAC[realTheory.REAL_LDISTRIB] >> REAL_ARITH_TAC) >>
         ‘&(2 ** d) * (z_node W (SUC m) (2 * j) +
                       z_node W (SUC m) (2 * j + 1)) ≤
          &(2 ** d) * (2 * z_node W m j)’
           by (irule realTheory.REAL_LE_LMUL_IMP >> simp[]) >>
         ‘(&(2 ** SUC d) : real) = 2 * &(2 ** d)’
           by REWRITE_TAC[arithmeticTheory.EXP, GSYM realTheory.REAL_OF_NUM_MUL] >>
         ASM_REWRITE_TAC[] >> REAL_ARITH_TAC)
QED

(* Helper: exact quotient (j * D + r) DIV D = j across all AC permutations.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem div_mul_add_ac[local]:
  ∀D j r : num.
    r < D ⇒
    (j * D + r) DIV D = j ∧
    (r + j * D) DIV D = j ∧
    (D * j + r) DIV D = j ∧
    (r + D * j) DIV D = j
Proof
  rpt strip_tac >>
  ‘(j * D + r) DIV D = j’ by (irule DIV_UNIQUE >> qexists_tac ‘r’ >> simp[]) >>
  ‘r + j * D = j * D + r ∧ D * j + r = j * D + r ∧ r + D * j = j * D + r’
    by simp[] >>
  metis_tac[]
QED

(* Identification of bad_count W zeta d m j with the exact cardinality of
   exceeding descendant suffixes r < 2 ** d of node (m, j).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bad_count_eq_fiber_card[local]:
  ∀(W : (bool, β) memoryless_channel) (zeta : real) d m j.
    (&(bad_count W zeta d m j) : real) =
    &(CARD {r | r < 2 ** d ∧
                ∃t. t ≤ d ∧
                    zeta < z_node W (m + t) ((j * 2 ** d + r) DIV (2 ** (d - t)))})
Proof
  ntac 2 gen_tac >> Induct_on ‘d’
  >- (rpt gen_tac >> simp[bad_count_def] >>
      qmatch_goalsub_abbrev_tac ‘CARD F0’ >>
      Cases_on ‘zeta < z_node W m j’ >> simp[]
      >- (‘F0 = {0}’
            by (rw[Abbr ‘F0’, Once EXTENSION] >> eq_tac >> rw[] >> decide_tac) >>
          simp[])
      >- (‘F0 = ∅’
            by (rw[Abbr ‘F0’, Once EXTENSION] >> CCONTR_TAC >> gvs[] >>
                ‘x = 0’ by decide_tac >> gvs[]) >>
          simp[]))
  >> rpt gen_tac >> REWRITE_TAC[bad_count_def] >>
     qabbrev_tac ‘F_set =
       {r | r < 2 ** SUC d ∧
            ∃t. t ≤ SUC d ∧
                zeta < z_node W (m + t)
                         ((j * 2 ** SUC d + r) DIV (2 ** (SUC d - t)))}’ >>
     Cases_on ‘zeta < z_node W m j’ >> ASM_REWRITE_TAC[]
     >- (‘F_set = count (2 ** SUC d)’
           by (rw[Abbr ‘F_set’, Once EXTENSION] >> eq_tac >> rw[] >>
               qexists_tac ‘0’ >>
               qspecl_then [‘2 ** SUC d’, ‘j’, ‘x’] mp_tac div_mul_add_ac >>
               simp[]) >>
         simp[])
     >- (‘F_set ⊆ count (2 ** SUC d)’ by simp[Abbr ‘F_set’, SUBSET_DEF] >>
         drule_then SUBST1_TAC CARD_SUBSET_COUNT_AS_SUM >>
         qspecl_then [‘2’, ‘2 ** d’,
                      ‘λr. if r ∈ F_set then (1 : real) else 0’]
           mp_tac REAL_SUM_IMAGE_COUNT_MUL >>
         ‘count (2 ** SUC d) = count (2 * 2 ** d)’
           by REWRITE_TAC[arithmeticTheory.EXP] >>
         pop_assum SUBST1_TAC >> (impl_tac >- simp[]) >>
         disch_then SUBST1_TAC >> BETA_TAC >>
         ‘count 2 = {0; 1}’ by (rw[Once EXTENSION] >> decide_tac) >>
         pop_assum SUBST1_TAC >>
         SIMP_TAC std_ss [REAL_SUM_IMAGE_THM, FINITE_INSERT, FINITE_EMPTY,
                          DELETE_NON_ELEMENT_RWT, NOT_IN_EMPTY, IN_INSERT,
                          DECIDE “0n ≠ 1n”, MULT_CLAUSES, ADD_CLAUSES, realTheory.REAL_ADD_RID] >>
         REWRITE_TAC[GSYM realTheory.REAL_OF_NUM_ADD] >>
         BINOP_TAC
         >- (first_x_assum (qspecl_then [‘SUC m’, ‘2 * j’] SUBST1_TAC) >>
             qmatch_abbrev_tac ‘(&(CARD B0) : real) = _’ >>
             ‘B0 ⊆ count (2 ** d)’ by simp[Abbr ‘B0’, SUBSET_DEF] >>
             drule_then SUBST1_TAC CARD_SUBSET_COUNT_AS_SUM >>
             irule REAL_SUM_IMAGE_EQ >> simp[] >>
             qx_gen_tac ‘r’ >> strip_tac >>
             ‘r ∈ B0 ⇔ r ∈ F_set’
               by (SIMP_TAC std_ss [Abbr ‘B0’, Abbr ‘F_set’, GSPECIFICATION] >>
                   ‘r < 2 ** SUC d’ by (simp[arithmeticTheory.EXP] >> decide_tac) >>
                   ASM_SIMP_TAC std_ss [] >>
                   eq_tac >> strip_tac
                   >- (qexists_tac ‘SUC t’ >>
                       (conj_tac >- decide_tac) >>
                       ‘m + SUC t = SUC m + t ∧
                        (j * 2 ** SUC d + r) DIV (2 ** (SUC d - SUC t)) =
                        ((2 * j) * 2 ** d + r) DIV (2 ** (d - t))’
                         by ((conj_tac >- decide_tac) >>
                             BINOP_TAC >> simp[arithmeticTheory.EXP]) >>
                       ASM_SIMP_TAC std_ss [SUB_MONO_EQ])
                   >- (Cases_on ‘t’
                       >- (‘(j * 2 ** SUC d + r) DIV (2 ** SUC d) = j’
                             by (irule DIV_UNIQUE >> qexists_tac ‘r’ >> simp[]) >>
                           FULL_SIMP_TAC std_ss [ADD_CLAUSES, SUB_0])
                       >- (qexists_tac ‘n’ >>
                           (conj_tac >- decide_tac) >>
                           ‘m + SUC n = SUC m + n ∧
                            (j * 2 ** SUC d + r) DIV (2 ** (SUC d - SUC n)) =
                            ((2 * j) * 2 ** d + r) DIV (2 ** (d - n))’
                             by ((conj_tac >- decide_tac) >>
                                 BINOP_TAC >> simp[arithmeticTheory.EXP]) >>
                           FULL_SIMP_TAC std_ss []))) >>
             ASM_REWRITE_TAC[])
         >- (first_x_assum (qspecl_then [‘SUC m’, ‘2 * j + 1’] SUBST1_TAC) >>
             qmatch_abbrev_tac ‘(&(CARD B1) : real) = _’ >>
             ‘B1 ⊆ count (2 ** d)’ by simp[Abbr ‘B1’, SUBSET_DEF] >>
             drule_then SUBST1_TAC CARD_SUBSET_COUNT_AS_SUM >>
             irule REAL_SUM_IMAGE_EQ >> simp[] >>
             qx_gen_tac ‘r’ >> strip_tac >>
             ‘r ∈ B1 ⇔ r + 2 ** d ∈ F_set’
               by (SIMP_TAC std_ss [Abbr ‘B1’, Abbr ‘F_set’, GSPECIFICATION] >>
                   ‘r + 2 ** d < 2 ** SUC d’
                     by (simp[arithmeticTheory.EXP] >> decide_tac) >>
                   ASM_SIMP_TAC std_ss [] >>
                   eq_tac >> strip_tac
                   >- (qexists_tac ‘SUC t’ >>
                       (conj_tac >- decide_tac) >>
                       ‘m + SUC t = SUC m + t ∧
                        (j * 2 ** SUC d + (r + 2 ** d)) DIV (2 ** (SUC d - SUC t)) =
                        ((2 * j + 1) * 2 ** d + r) DIV (2 ** (d - t))’
                         by ((conj_tac >- decide_tac) >>
                             BINOP_TAC >- (simp[arithmeticTheory.EXP, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]) >>
                             simp[]) >>
                       ASM_SIMP_TAC std_ss [SUB_MONO_EQ])
                   >- (Cases_on ‘t’
                       >- (‘(j * 2 ** SUC d + (r + 2 ** d)) DIV (2 ** SUC d) = j’
                             by (irule DIV_UNIQUE >> qexists_tac ‘r + 2 ** d’ >>
                                 simp[arithmeticTheory.EXP] >> decide_tac) >>
                           FULL_SIMP_TAC std_ss [ADD_CLAUSES, SUB_0])
                       >- (qexists_tac ‘n’ >>
                           (conj_tac >- decide_tac) >>
                           ‘m + SUC n = SUC m + n ∧
                            (j * 2 ** SUC d + (r + 2 ** d)) DIV (2 ** (SUC d - SUC n)) =
                            ((2 * j + 1) * 2 ** d + r) DIV (2 ** (d - n))’
                             by ((conj_tac >- decide_tac) >>
                                 BINOP_TAC >- (simp[arithmeticTheory.EXP, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]) >>
                                 simp[]) >>
                           FULL_SIMP_TAC std_ss []))) >>
             ASM_REWRITE_TAC[]))
QED

(* Finite-horizon stopped supermartingale maximal inequality across all
   level-(m + d) paths starting from level-m nodes with z_node <= alpha.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem supermartingale_maximal_ineq:
  ∀(W : (bool, β) memoryless_channel) (alpha : real) (zeta : real) m d.
    wf_bdmc W ∧ 0 ≤ alpha ∧ 0 ≤ zeta ⇒
    zeta *
    &(CARD {i | i < 2 ** (m + d) ∧
                z_node W m (i DIV (2 ** d)) ≤ alpha ∧
                ∃t. t ≤ d ∧
                    zeta < z_node W (m + t) (i DIV (2 ** (d - t)))}) ≤
    &(2 ** (m + d)) * alpha
Proof
  rpt strip_tac >>
  qabbrev_tac ‘E_set =
    {i | i < 2 ** (m + d) ∧
         z_node W m (i DIV (2 ** d)) ≤ alpha ∧
         ∃t. t ≤ d ∧ zeta < z_node W (m + t) (i DIV (2 ** (d - t)))}’ >>
  ‘E_set ⊆ count (2 ** (m + d))’ by simp[Abbr ‘E_set’, SUBSET_DEF] >>
  drule_then SUBST1_TAC CARD_SUBSET_COUNT_AS_SUM >>
  ‘count (2 ** (m + d)) = count (2 ** m * 2 ** d)’
    by REWRITE_TAC[arithmeticTheory.EXP_ADD] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘2 ** m’, ‘2 ** d’,
               ‘λi. if i ∈ E_set then (1 : real) else 0’]
    mp_tac REAL_SUM_IMAGE_COUNT_MUL >>
  (impl_tac >- simp[]) >> disch_then SUBST1_TAC >> BETA_TAC >>
  simp[GSYM REAL_SUM_IMAGE_CMUL] >>
  irule realTheory.REAL_LE_TRANS >>
  qexists_tac ‘REAL_SUM_IMAGE (λj. &(2 ** d) * alpha) (count (2 ** m))’ >>
  reverse conj_tac
  >- (simp[REAL_SUM_IMAGE_FINITE_CONST3, arithmeticTheory.EXP_ADD] >>
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] >> simp[]) >>
  irule REAL_SUM_IMAGE_MONO >> simp[] >>
  qx_gen_tac ‘j’ >> strip_tac >>
  simp[REAL_SUM_IMAGE_CMUL] >>
  qmatch_goalsub_abbrev_tac ‘zeta * S_fiber ≤ _’ >>
  Cases_on ‘z_node W m j ≤ alpha’
  >- (‘S_fiber = &(bad_count W zeta d m j)’
        by (REWRITE_TAC[bad_count_eq_fiber_card] >>
            qmatch_abbrev_tac ‘_ = (&(CARD F_j) : real)’ >>
            ‘F_j ⊆ count (2 ** d)’ by simp[Abbr ‘F_j’, SUBSET_DEF] >>
            drule_then SUBST1_TAC CARD_SUBSET_COUNT_AS_SUM >>
            SIMP_TAC std_ss [Abbr ‘S_fiber’] >>
            irule REAL_SUM_IMAGE_EQ >> simp[] >>
            qx_gen_tac ‘r’ >> strip_tac >>
            qspecl_then [‘m’, ‘d’, ‘j’, ‘r’] mp_tac mul_add_pow2_props >>
            strip_tac >>
            ‘r + j * 2 ** d = j * 2 ** d + r ∧
             2 ** d * j + r = j * 2 ** d + r ∧
             r + 2 ** d * j = j * 2 ** d + r’ by simp[] >>
            SIMP_TAC std_ss [Abbr ‘E_set’, Abbr ‘F_j’, GSPECIFICATION] >>
            ASM_SIMP_TAC std_ss []) >>
      pop_assum SUBST1_TAC >>
      qspecl_then [‘W’, ‘zeta’, ‘d’, ‘m’, ‘j’] mp_tac bad_count_ville_bound >>
      simp[] >> strip_tac >>
      ‘&(2 ** d) * z_node W m j ≤ alpha * &(2 ** d)’
        by (‘alpha * &(2 ** d) = &(2 ** d) * alpha’ by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
            pop_assum SUBST1_TAC >> irule realTheory.REAL_LE_LMUL_IMP >> simp[]) >>
      REAL_ARITH_TAC)
  >- (‘S_fiber = 0’
        by (SIMP_TAC std_ss [Abbr ‘S_fiber’] >>
            irule REAL_SUM_IMAGE_EQ_0 >> simp[] >>
            qx_gen_tac ‘r’ >> strip_tac >>
            qspecl_then [‘m’, ‘d’, ‘j’, ‘r’] mp_tac mul_add_pow2_props >>
            simp[Abbr ‘E_set’]) >>
      pop_assum SUBST1_TAC >>
      simp[] >> irule realTheory.REAL_LE_MUL >> simp[])
QED

(* Polynomial consequence of Proposition 1 Upper Bound: for 0 < alpha <= 1/2,
   I(W') > 1 - alpha^2 / 2 implies Z(W') <= alpha (zero logarithms required).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem high_capacity_imp_low_bhattacharyya[local]:
  ∀(W' : (bool, γ) memoryless_channel) (alpha : real).
    wf_bdmc W' ∧ 0 < alpha ∧ alpha ≤ 1 / 2 ∧
    Normal (1 - (alpha pow 2) / 2) < symmetric_capacity W' ⇒
    real (bhattacharyya W') ≤ alpha
Proof
  rpt strip_tac >>
  drule proposition_1_upper >>
  drule bhattacharyya_bounds >>
  drule symmetric_capacity_bounds >>
  rpt strip_tac >>
  gvs[extreal_of_num_def, extreal_pow_def, extreal_sub_eq,
      extreal_sqrt_def, extreal_le_eq, extreal_lt_eq, real_normal] >>
  ‘0 ≤ 1 - z pow 2’
    by (‘z pow 2 ≤ 1 pow 2’ by (irule realTheory.POW_LE >> simp[]) >>
        gvs[] >> REAL_ARITH_TAC) >>
  ‘c pow 2 ≤ (real$sqrt (1 - z pow 2)) pow 2’
    by (irule realTheory.POW_LE >> simp[]) >>
  ‘(real$sqrt (1 - z pow 2)) pow 2 = 1 - z pow 2’
    by simp[realTheory.SQRT_POW_2] >>
  ‘0 ≤ 1 - (alpha pow 2) / 2’
    by (‘alpha pow 2 ≤ (1 / 2 : real) pow 2’
          by (irule realTheory.POW_LE >> REAL_ARITH_TAC) >>
        qpat_x_assum ‘alpha pow 2 ≤ _’ mp_tac >>
        PURE_REWRITE_TAC[realTheory.POW_2] >> REAL_ARITH_TAC) >>
  ‘(1 - (alpha pow 2) / 2) pow 2 < c pow 2’
    by (PURE_REWRITE_TAC[realTheory.POW_2] >>
        irule realTheory.REAL_LT_MUL2 >> REAL_ARITH_TAC) >>
  ‘(1 - (alpha pow 2) / 2) pow 2 - (1 - alpha pow 2) =
   ((alpha pow 2) / 2) pow 2’
    by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
  ‘0 ≤ ((alpha pow 2) / 2) pow 2’ by simp[REAL_LE_POW2] >>
  ‘z pow 2 < alpha pow 2’ by REAL_ARITH_TAC >>
  CCONTR_TAC >> ‘alpha < z’ by REAL_ARITH_TAC >>
  ‘alpha pow 2 < z pow 2’
    by (PURE_REWRITE_TAC[realTheory.POW_2] >>
        irule realTheory.REAL_LT_MUL2 >> REAL_ARITH_TAC) >>
  REAL_ARITH_TAC
QED

(* Arıkan Lemma 1 (Section IV-B, p. 9 & Appendix F, p. 23), finite-horizon
   uniform form: for any B-DMC W and zeta, delta > 0, there exists m0 such
   that for all n >= m0, at least a fraction I(W) - delta/2 of all 2^n paths
   satisfy Z_k <= zeta at every intermediate level k in [m0, n].

   Written by Gemini (Google DeepMind AI agent) *)
Theorem lemma_1_finite_horizon:
  ∀(W : (bool, β) memoryless_channel) (zeta : real) (delta : real).
    wf_bdmc W ∧ 0 < zeta ∧ 0 < delta ⇒
    ∃m0 : num.
      ∀n : num.
        m0 ≤ n ⇒
        &(2 ** n) * (real (symmetric_capacity W) - delta / 2) ≤
        &(CARD {i | i < 2 ** n ∧
                    ∀k. m0 ≤ k ∧ k ≤ n ⇒
                        z_node W k (i DIV (2 ** (n - k))) ≤ zeta})
Proof
  rpt strip_tac >>
  qabbrev_tac ‘z_d4 = zeta * (delta / 4)’ >>
  ‘0 < z_d4’
    by (simp[Abbr ‘z_d4’] >> irule realTheory.REAL_LT_MUL >>
        simp[] >> REAL_ARITH_TAC) >>
  qabbrev_tac ‘a1 = if zeta ≤ z_d4 then zeta else z_d4’ >>
  qabbrev_tac ‘alpha = if (1 / 2 : real) ≤ a1 then (1 / 2 : real) else a1’ >>
  ‘0 < alpha ∧ alpha ≤ 1 / 2 ∧ alpha ≤ zeta ∧ alpha ≤ zeta * (delta / 4)’
    by (‘alpha ≤ z_d4 ∧ 0 < alpha ∧ alpha ≤ 1 / 2 ∧ alpha ≤ zeta’
          by (REPEAT CONJ_TAC >>
              SIMP_TAC std_ss [Abbr ‘alpha’, Abbr ‘a1’] >>
              REPEAT COND_CASES_TAC >> REAL_ARITH_TAC) >>
        FULL_SIMP_TAC std_ss [Abbr ‘z_d4’]) >>
  qabbrev_tac ‘eps_cap = (alpha pow 2) / 2’ >>
  ‘0 < eps_cap ∧ eps_cap < 1’
    by (‘0 < alpha * alpha ∧ alpha * alpha ≤ 1 * 1’
          by ((conj_tac >- (irule realTheory.REAL_LT_MUL >> simp[])) >>
              irule realTheory.REAL_LE_MUL2 >> REAL_ARITH_TAC) >>
        simp[Abbr ‘eps_cap’] >>
        PURE_REWRITE_TAC[realTheory.POW_2] >> REAL_ARITH_TAC) >>
  qspecl_then [‘W’, ‘eps_cap’] mp_tac theorem_1_channel_polarization >>
  simp[] >>
  disch_then (mp_tac o CONJUNCT1) >>
  simp[seqTheory.SEQ] >>
  disch_then (qspec_then ‘delta / 4’ mp_tac) >>
  impl_tac >- REAL_ARITH_TAC >>
  disch_then (qx_choose_then ‘m0’ assume_tac) >>
  qexists_tac ‘m0’ >>
  first_x_assum (qspec_then ‘m0’ mp_tac) >> simp[] >> strip_tac >>
  ‘&(2 ** m0) * (real (symmetric_capacity W) - delta / 4) ≤
   &(CARD {j | j < 2 ** m0 ∧ z_node W m0 j ≤ alpha})’
    by (qabbrev_tac ‘C_cap =
          {j | j < 2 ** m0 ∧
               Normal (1 - eps_cap) <
               symmetric_capacity (split_channel W (2 ** m0) j)}’ >>
        qabbrev_tac ‘C_z = {j | j < 2 ** m0 ∧ z_node W m0 j ≤ alpha}’ >>
        ‘C_cap ⊆ C_z ∧ FINITE C_z’
          by (conj_tac
              >- (rw[Abbr ‘C_cap’, Abbr ‘C_z’, SUBSET_DEF, z_node_def] >>
                  irule high_capacity_imp_low_bhattacharyya >>
                  simp[Abbr ‘eps_cap’, wf_bdmc_split_channel])
              >- (irule SUBSET_FINITE_I >> qexists_tac ‘count (2 ** m0)’ >>
                  simp[Abbr ‘C_z’, SUBSET_DEF])) >>
        ‘CARD C_cap ≤ CARD C_z’ by metis_tac[CARD_SUBSET] >>
        ‘&(CARD C_cap) ≤ (&(CARD C_z) : real)’ by simp[] >>
        ‘0 < (&(2 ** m0) : real)’ by simp[] >>
        ‘real (symmetric_capacity W) - delta / 4 < &(CARD C_cap) / &(2 ** m0)’
          by REAL_ARITH_TAC >>
        ‘&(2 ** m0) * (real (symmetric_capacity W) - delta / 4) < &(CARD C_cap)’
          by (‘(real (symmetric_capacity W) - delta / 4) * &(2 ** m0) < &(CARD C_cap)’
                by gs[realTheory.REAL_LT_RDIV_EQ] >>
              ‘&(2 ** m0) * (real (symmetric_capacity W) - delta / 4) =
               (real (symmetric_capacity W) - delta / 4) * &(2 ** m0)’
                by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
              REAL_ARITH_TAC) >>
        REAL_ARITH_TAC) >>
  qx_gen_tac ‘n’ >> strip_tac >>
  qabbrev_tac ‘d = n - m0’ >>
  ‘n = m0 + d’ by simp[Abbr ‘d’] >>
  qabbrev_tac ‘S0 = {i | i < 2 ** (m0 + d) ∧ z_node W m0 (i DIV (2 ** d)) ≤ alpha}’ >>
  qabbrev_tac ‘E =
    {i | i < 2 ** (m0 + d) ∧
         z_node W m0 (i DIV (2 ** d)) ≤ alpha ∧
         ∃t. t ≤ d ∧ zeta < z_node W (m0 + t) (i DIV (2 ** (d - t)))}’ >>
  qmatch_goalsub_abbrev_tac ‘_ ≤ &(CARD T_good)’ >>
  ‘FINITE S0 ∧ FINITE E ∧ FINITE T_good’
    by (rpt conj_tac >> irule SUBSET_FINITE_I
        >- (qexists_tac ‘count (2 ** (m0 + d))’ >> simp[Abbr ‘S0’, SUBSET_DEF])
        >- (qexists_tac ‘count (2 ** (m0 + d))’ >> simp[Abbr ‘E’, SUBSET_DEF])
        >- (qexists_tac ‘count (2 ** n)’ >> simp[Abbr ‘T_good’, SUBSET_DEF])) >>
  ‘S0 DIFF E ⊆ T_good’
    by (rw[Abbr ‘S0’, Abbr ‘E’, Abbr ‘T_good’, SUBSET_DEF] >>
        ‘k = m0 + (k - m0) ∧ k - m0 ≤ d ∧ m0 + d - k = d - (k - m0)’
          by decide_tac >>
        first_x_assum (qspec_then ‘k - m0’ mp_tac) >>
        simp[] >> REAL_ARITH_TAC) >>
  ‘CARD (S0 DIFF E) ≤ CARD T_good’ by metis_tac[CARD_SUBSET] >>
  ‘&(CARD S0) - &(CARD E) ≤ (&(CARD T_good) : real)’
    by (qspecl_then [‘S0’, ‘E’] mp_tac CARD_DIFF_LOWER_BOUND >>
        (impl_tac >- simp[]) >> strip_tac >>
        ‘&(CARD (S0 DIFF E)) ≤ (&(CARD T_good) : real)’
          by ASM_REWRITE_TAC[realTheory.REAL_OF_NUM_LE] >>
        REAL_ARITH_TAC) >>
  ‘(&(CARD S0) : real) =
   &(2 ** d) * &(CARD {j | j < 2 ** m0 ∧ z_node W m0 j ≤ alpha})’
    by simp[Abbr ‘S0’, CARD_LIFT_DIV_POW2] >>
  ‘&(2 ** (m0 + d)) * (real (symmetric_capacity W) - delta / 4) ≤ &(CARD S0)’
    by (REWRITE_TAC[arithmeticTheory.EXP_ADD, GSYM realTheory.REAL_OF_NUM_MUL] >>
        ‘(&(2 ** m0) * &(2 ** d)) * (real (symmetric_capacity W) - delta / 4) =
         &(2 ** d) * (&(2 ** m0) * (real (symmetric_capacity W) - delta / 4))’
          by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
        pop_assum SUBST1_TAC >>
        ASM_REWRITE_TAC[] >>
        irule realTheory.REAL_LE_LMUL_IMP >> (conj_tac >- simp[]) >> gvs[]) >>
  ‘&(CARD E) ≤ &(2 ** (m0 + d)) * (delta / 4)’
    by (qspecl_then [‘W’, ‘alpha’, ‘zeta’, ‘m0’, ‘d’]
          mp_tac supermartingale_maximal_ineq >>
        (impl_tac >- (simp[] >> REAL_ARITH_TAC)) >>
        qpat_assum ‘Abbrev (E = _)’
          (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        strip_tac >>
        ‘&(2 ** (m0 + d)) * alpha ≤ &(2 ** (m0 + d)) * (zeta * (delta / 4))’
          by (irule realTheory.REAL_LE_LMUL_IMP >> (conj_tac >- simp[]) >> gvs[]) >>
        ‘&(2 ** (m0 + d)) * (zeta * (delta / 4)) =
         zeta * (&(2 ** (m0 + d)) * (delta / 4))’
          by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
        ‘zeta * &(CARD E) ≤ zeta * (&(2 ** (m0 + d)) * (delta / 4))’
          by REAL_ARITH_TAC >>
        irule realTheory.REAL_LE_LCANCEL_IMP >>
        qexists_tac ‘zeta’ >> (conj_tac >- simp[]) >> gvs[]) >>
  ‘&(2 ** n) * (real (symmetric_capacity W) - delta / 2) =
   &(2 ** (m0 + d)) * (real (symmetric_capacity W) - delta / 4) -
   &(2 ** (m0 + d)) * (delta / 4)’
    by (‘&(2 ** n) = (&(2 ** (m0 + d)) : real)’ by simp[] >>
        pop_assum SUBST1_TAC >> CONV_TAC (EQT_INTRO o REAL_FIELD)) >>
  REAL_ARITH_TAC
QED

(* Popcount of 1-bits among the d least-significant binary digits of i.

   Written by Gemini (Google DeepMind AI agent) *)
Definition popcount_low_def:
  popcount_low 0 (i : num) = 0 ∧
  popcount_low (SUC d) i = (i MOD 2) + popcount_low d (i DIV 2)
End

(* Even/odd step identities for popcount_low.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem popcount_low_even_odd[local]:
  ∀d r : num.
    popcount_low (SUC d) (2 * r) = popcount_low d r ∧
    popcount_low (SUC d) (2 * r + 1) = 1 + popcount_low d r
Proof
  rpt gen_tac >> simp[popcount_low_def] >>
  ‘(2 * r) DIV 2 = r ∧ (2 * r) MOD 2 = 0’
    by (irule DIVMOD_UNIQ >> decide_tac) >>
  ‘(2 * r + 1) DIV 2 = r ∧ (2 * r + 1) MOD 2 = 1’
    by (irule DIVMOD_UNIQ >> decide_tac) >>
  simp[]
QED

(* Shift invariance of popcount_low modulo 2 ** d.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem popcount_low_add_pow2[local]:
  ∀d j r : num.
    r < 2 ** d ⇒
    popcount_low d (j * 2 ** d + r) = popcount_low d r ∧
    popcount_low d (r + j * 2 ** d) = popcount_low d r ∧
    popcount_low d (2 ** d * j + r) = popcount_low d r ∧
    popcount_low d (r + 2 ** d * j) = popcount_low d r
Proof
  gen_tac >>
  ‘∀j r : num. r < 2 ** d ⇒ popcount_low d (j * 2 ** d + r) = popcount_low d r’
    by (Induct_on ‘d’ >- simp[popcount_low_def] >>
        rpt strip_tac >> REWRITE_TAC[popcount_low_def, arithmeticTheory.EXP] >>
        ‘j * (2 * 2 ** d) + r = (j * 2 ** d + r DIV 2) * 2 + r MOD 2’
          by (qspec_then ‘2’ mp_tac DIVISION >> simp[] >>
              disch_then (qspec_then ‘r’ strip_assume_tac) >>
              ‘j * (2 * 2 ** d) = (j * 2 ** d) * 2’ by simp[] >>
              ‘(j * 2 ** d + r DIV 2) * 2 = (j * 2 ** d) * 2 + (r DIV 2) * 2’
                by REWRITE_TAC[RIGHT_ADD_DISTRIB] >>
              decide_tac) >>
        ‘r MOD 2 < 2’ by simp[] >>
        ‘(j * (2 * 2 ** d) + r) DIV 2 = j * 2 ** d + r DIV 2 ∧
         (j * (2 * 2 ** d) + r) MOD 2 = r MOD 2’
          by (irule DIVMOD_UNIQ >> simp[]) >>
        ‘r DIV 2 < 2 ** d’
          by (irule (iffRL arithmeticTheory.DIV_LT_X) >>
              fs[arithmeticTheory.EXP] >> decide_tac) >>
        ASM_SIMP_TAC (srw_ss()) []) >>
  rpt strip_tac >>
  ‘r + j * 2 ** d = j * 2 ** d + r ∧
   2 ** d * j + r = j * 2 ** d + r ∧
   r + 2 ** d * j = j * 2 ** d + r’ by simp[] >>
  ASM_REWRITE_TAC[] >> first_x_assum irule >> simp[]
QED

(* Exact binomial second-central-moment sum over count (2 ** d):
   sum_{r < 2^d} (popcount_low d r - d / 2)^2 = 2^d * (d / 4).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem popcount_low_variance_sum:
  ∀d : num.
    REAL_SUM_IMAGE (λr. (&(popcount_low d r) - &d / 2) pow 2)
                   (count (2 ** d)) =
    &(2 ** d) * (&d / 4)
Proof
  Induct_on ‘d’
  >- (‘count 1 = {0}’ by (rw[Once EXTENSION] >> decide_tac) >>
      simp[REAL_SUM_IMAGE_SING, popcount_low_def])
  >> simp[arithmeticTheory.EXP, REAL_SUM_IMAGE_COUNT_DOUBLE_LOCAL,
          popcount_low_even_odd] >>
     ‘REAL_SUM_IMAGE
        (λj. (&(popcount_low d j) - &(SUC d) / 2) pow 2 +
             (&(popcount_low d j + 1) - &(SUC d) / 2) pow 2)
        (count (2 ** d)) =
      REAL_SUM_IMAGE
        (λj. 2 * ((&(popcount_low d j) - &d / 2) pow 2) + (1 / 2 : real))
        (count (2 ** d))’
       by (irule REAL_SUM_IMAGE_EQ >> simp[] >>
           qx_gen_tac ‘j’ >> strip_tac >>
           REWRITE_TAC[ADD1] >>
           REWRITE_TAC[GSYM REAL_OF_NUM_ADD] >>
           PURE_REWRITE_TAC[realTheory.POW_2] >> REAL_ARITH_TAC) >>
     pop_assum SUBST1_TAC >>
     simp[REAL_SUM_IMAGE_ADD, REAL_SUM_IMAGE_CMUL,
          REAL_SUM_IMAGE_FINITE_CONST3] >>
     REWRITE_TAC[ADD1, GSYM REAL_OF_NUM_ADD, GSYM REAL_OF_NUM_MUL] >>
     CONV_TAC (EQT_INTRO o REAL_FIELD)
QED

(* Chebyshev upper bound on the number of d-bit suffixes with at most
   (9 / 20) * d ones (corresponding to eta_0 = 1 / 20).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem popcount_low_chebyshev_bound:
  ∀d : num.
    1 ≤ d ⇒
    (&(CARD {r | r < 2 ** d ∧ &(popcount_low d r) ≤ (9 / 20 : real) * &d}) : real) *
      &d ≤
    100 * &(2 ** d)
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac ‘(&(CARD L) : real) * &d ≤ _’ >>
  ‘0 ≤ (&d : real)’ by simp[] >>
  ‘L ⊆ count (2 ** d)’ by simp[Abbr ‘L’, SUBSET_DEF] >>
  ‘(((&d : real) / 20) pow 2) * &(CARD L) ≤
   REAL_SUM_IMAGE (λr. (&(popcount_low d r) - &d / 2) pow 2)
                  (count (2 ** d))’
    by (drule_then SUBST1_TAC CARD_SUBSET_COUNT_AS_SUM >>
        dep_rewrite.DEP_REWRITE_TAC[GSYM REAL_SUM_IMAGE_CMUL] >>
        (conj_tac >- simp[]) >>
        irule REAL_SUM_IMAGE_MONO >> (reverse conj_tac >- simp[]) >>
        qx_gen_tac ‘r’ >> BETA_TAC >> strip_tac >>
        reverse (Cases_on ‘r ∈ L’) >- simp[REAL_LE_POW2] >>
        ASM_REWRITE_TAC[realTheory.REAL_MUL_RID] >>
        FULL_SIMP_TAC (std_ss ++ pred_setSimps.PRED_SET_ss) [Abbr ‘L’] >>
        ‘0 ≤ (&d : real) / 20’ by (irule realTheory.REAL_LE_DIV >> simp[] >> REAL_ARITH_TAC) >>
        ‘(&d : real) / 20 ≤ &d / 2 - &(popcount_low d r)’
          by (‘(&d : real) / 2 - &(popcount_low d r) - &d / 20 =
               (9 / 20 : real) * &d - &(popcount_low d r)’
                by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
              REAL_ARITH_TAC) >>
        ‘((&d : real) / 20) pow 2 ≤ (&d / 2 - &(popcount_low d r)) pow 2’
          by (irule realTheory.POW_LE >> simp[]) >>
        ‘((&d : real) / 2 - &(popcount_low d r)) pow 2 =
         (&(popcount_low d r) - &d / 2) pow 2’
          by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
        REAL_ARITH_TAC) >>
  qpat_x_assum ‘_ ≤ REAL_SUM_IMAGE _ _’ mp_tac >>
  REWRITE_TAC[popcount_low_variance_sum] >>
  strip_tac >>
  ‘(400 : real) * ((((&d : real) / 20) pow 2) * &(CARD L)) ≤
   400 * (&(2 ** d) * ((&d : real) / 4))’
    by REAL_ARITH_TAC >>
  ‘(400 : real) * ((((&d : real) / 20) pow 2) * &(CARD L)) = &d * (&(CARD L) * &d)’
    by (PURE_REWRITE_TAC[realTheory.POW_2] >> CONV_TAC (EQT_INTRO o REAL_FIELD)) >>
  ‘(400 : real) * (&(2 ** d) * ((&d : real) / 4)) = &d * (100 * &(2 ** d))’
    by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
  ‘(&d : real) * (&(CARD L) * &d) ≤ &d * (100 * &(2 ** d))’ by REAL_ARITH_TAC >>
  irule realTheory.REAL_LE_LCANCEL_IMP >>
  qexists_tac ‘&d : real’ >>
  conj_tac >- simp[] >- first_assum ACCEPT_TAC
QED

(* Explicit closed-form threshold n1 = m1 + flr (200 / delta) + 1 ensuring
   fraction of i < 2^n with <= (9/20)(n - m1) ones in lower bits is <= delta/2.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem popcount_low_tail_concentration:
  ∀(delta : real) (m1 : num) (n : num).
    0 < delta ∧ m1 + flr (200 / delta) + 1 ≤ n ⇒
    (&(CARD {i | i < 2 ** n ∧
                 &(popcount_low (n - m1) i) ≤ (9 / 20 : real) * &(n - m1)}) : real) ≤
    &(2 ** n) * (delta / 2)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘d = n - m1’ >>
  ‘n = m1 + d ∧ 1 ≤ d ∧ flr (200 / delta) + 1 ≤ d’ by simp[Abbr ‘d’] >>
  qabbrev_tac ‘B_hi =
    {i | i < 2 ** (m1 + d) ∧ &(popcount_low d i) ≤ (9 / 20 : real) * &d}’ >>
  qabbrev_tac ‘B_lo =
    {r | r < 2 ** d ∧ &(popcount_low d r) ≤ (9 / 20 : real) * &d}’ >>
  ‘(&(CARD B_hi) : real) = &(2 ** m1) * &(CARD B_lo)’
    by (‘B_hi ⊆ count (2 ** (m1 + d)) ∧ B_lo ⊆ count (2 ** d)’
          by simp[Abbr ‘B_hi’, Abbr ‘B_lo’, SUBSET_DEF] >>
        qpat_x_assum ‘B_hi ⊆ _’
          (SUBST1_TAC o MATCH_MP CARD_SUBSET_COUNT_AS_SUM) >>
        qpat_x_assum ‘B_lo ⊆ _’
          (SUBST1_TAC o MATCH_MP CARD_SUBSET_COUNT_AS_SUM) >>
        ‘count (2 ** (m1 + d)) = count (2 ** m1 * 2 ** d)’
          by REWRITE_TAC[arithmeticTheory.EXP_ADD] >>
        pop_assum SUBST1_TAC >>
        qspecl_then [‘2 ** m1’, ‘2 ** d’,
                     ‘λi. if i ∈ B_hi then (1 : real) else 0’]
          mp_tac REAL_SUM_IMAGE_COUNT_MUL >>
        (impl_tac >- simp[]) >> disch_then SUBST1_TAC >> BETA_TAC >>
        ‘(&(2 ** m1) : real) *
         REAL_SUM_IMAGE (λi. if i ∈ B_lo then (1 : real) else 0) (count (2 ** d)) =
         REAL_SUM_IMAGE
           (λj. REAL_SUM_IMAGE (λr. if r ∈ B_lo then (1 : real) else 0) (count (2 ** d)))
           (count (2 ** m1))’
          by simp[REAL_SUM_IMAGE_FINITE_CONST3] >>
        pop_assum SUBST1_TAC >>
        irule REAL_SUM_IMAGE_EQ >> simp[] >>
        qx_gen_tac ‘j’ >> strip_tac >>
        irule REAL_SUM_IMAGE_EQ >> simp[] >>
        qx_gen_tac ‘r’ >> strip_tac >>
        qspecl_then [‘m1’, ‘d’, ‘j’, ‘r’] mp_tac mul_add_pow2_props >>
        qspecl_then [‘d’, ‘j’, ‘r’] mp_tac popcount_low_add_pow2 >>
        simp[Abbr ‘B_hi’, Abbr ‘B_lo’]) >>
  ‘200 / delta < &d’
    by (qspec_then ‘200 / delta’ mp_tac realTheory.NUM_FLOOR_LT >>
        ‘&(flr (200 / delta)) + 1 ≤ (&d : real)’ by simp[] >>
        REAL_ARITH_TAC) >>
  ‘200 ≤ &d * delta’
    by (‘200 < delta * &d’ by gs[realTheory.REAL_LT_LDIV_EQ] >>
        ‘delta * &d = &d * delta’ by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
        REAL_ARITH_TAC) >>
  qspec_then ‘d’ mp_tac popcount_low_chebyshev_bound >>
  (impl_tac >- simp[]) >>
  qpat_assum ‘Abbrev (B_lo = _)’
    (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  strip_tac >>
  ‘&d * (&(CARD B_hi) : real) ≤ &(2 ** m1) * (100 * &(2 ** d))’
    by (‘&d * (&(CARD B_hi) : real) = &(2 ** m1) * (&(CARD B_lo) * &d)’
          by (ASM_REWRITE_TAC[] >> CONV_TAC (EQT_INTRO o REAL_FIELD)) >>
        pop_assum SUBST1_TAC >>
        irule realTheory.REAL_LE_LMUL_IMP >>
        (conj_tac >- simp[]) >> REAL_ARITH_TAC) >>
  ‘&(2 ** m1) * (100 * &(2 ** d)) ≤ &d * (&(2 ** n) * (delta / 2))’
    by (‘&(2 ** n) = (&(2 ** m1) : real) * &(2 ** d)’
          by (‘2n ** n = 2n ** (m1 + d)’ by simp[] >>
              pop_assum SUBST1_TAC >>
              REWRITE_TAC[arithmeticTheory.EXP_ADD, GSYM realTheory.REAL_OF_NUM_MUL]) >>
        pop_assum SUBST1_TAC >>
        ‘(&(2 ** m1) : real) * (100 * &(2 ** d)) = (&(2 ** m1) * &(2 ** d)) * 100 ∧
         &d * ((&(2 ** m1) * &(2 ** d)) * (delta / 2)) =
         (&(2 ** m1) * &(2 ** d)) * ((1 / 2 : real) * (&d * delta))’
          by (conj_tac >> CONV_TAC (EQT_INTRO o REAL_FIELD)) >>
        ASM_REWRITE_TAC[] >>
        irule realTheory.REAL_LE_LMUL_IMP >>
        (reverse conj_tac >- (irule realTheory.REAL_LE_MUL >> simp[])) >> REAL_ARITH_TAC) >>
  ‘{i | i < 2 ** n ∧ &(popcount_low d i) ≤ (9 / 20 : real) * &d} = B_hi’
    by (‘2n ** n = 2n ** (m1 + d)’ by simp[] >>
        SIMP_TAC std_ss [Abbr ‘B_hi’] >> pop_assum SUBST1_TAC >> REFL_TAC) >>
  pop_assum SUBST1_TAC >>
  irule realTheory.REAL_LE_LCANCEL_IMP >>
  qexists_tac ‘&d : real’ >>
  conj_tac >- simp[] >- REAL_ARITH_TAC
QED

(* Division-free stepwise Bhattacharyya upper bound along a good tail
   T_{m, m+d}(zeta) in terms of popcount_low d i.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem z_node_good_tail_stepwise[local]:
  ∀(W : (bool, β) memoryless_channel) (zeta : real) m d i.
    wf_bdmc W ∧ 0 ≤ zeta ∧ i < 2 ** (m + d) ∧
    (∀t. t ≤ d ⇒ z_node W (m + t) (i DIV (2 ** (d - t))) ≤ zeta) ⇒
    z_node W (m + d) i ≤
      zeta * &(2 ** d) * ((zeta / 2) pow (popcount_low d i))
Proof
  ntac 3 gen_tac >> Induct_on ‘d’
  >- (rpt strip_tac >>
      first_x_assum (qspec_then ‘0’ mp_tac) >>
      simp[popcount_low_def])
  >> rpt strip_tac >>
     ‘i DIV 2 < 2 ** (m + d)’
       by (irule (iffRL arithmeticTheory.DIV_LT_X) >>
           fs[ADD_CLAUSES, arithmeticTheory.EXP] >> decide_tac) >>
     ‘∀t. t ≤ d ⇒ z_node W (m + t) ((i DIV 2) DIV (2 ** (d - t))) ≤ zeta’
       by (rpt strip_tac >>
           ‘(i DIV 2) DIV (2 ** (d - t)) = i DIV (2 * 2 ** (d - t))’
             by (irule DIV_DIV_DIV_MULT >> simp[]) >>
           ‘2n * 2n ** (d - t) = 2n ** (SUC d - t)’
             by (‘SUC d - t = SUC (d - t)’ by decide_tac >>
                 simp[arithmeticTheory.EXP]) >>
           first_x_assum (qspec_then ‘t’ mp_tac) >>
           impl_tac >- decide_tac >>
           ASM_REWRITE_TAC[]) >>
     qpat_x_assum ‘∀i. _ ∧ _ ⇒ _’ (qspec_then ‘i DIV 2’ mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     ‘z_node W (m + d) (i DIV 2) ≤ zeta’
       by (first_x_assum (qspec_then ‘d’ mp_tac) >> simp[]) >>
     qabbrev_tac ‘q = i DIV 2’ >>
     qabbrev_tac ‘md = m + d’ >>
     qspecl_then [‘W’, ‘md’, ‘q’] mp_tac z_node_bounds >>
     (impl_tac >- simp[Abbr ‘q’, Abbr ‘md’]) >> strip_tac >>
     qspecl_then [‘W’, ‘md’, ‘q’] mp_tac z_node_step >>
     (impl_tac >- simp[Abbr ‘q’, Abbr ‘md’]) >> strip_tac >>
     qspec_then ‘2’ mp_tac DIVISION >> (impl_tac >- simp[]) >>
     disch_then (qspec_then ‘i’ strip_assume_tac) >>
     ‘m + SUC d = SUC md’ by simp[Abbr ‘md’, ADD_CLAUSES] >>
     ‘(&(2 ** SUC d) : real) = 2 * &(2 ** d)’
       by REWRITE_TAC[arithmeticTheory.EXP, GSYM realTheory.REAL_OF_NUM_MUL] >>
     ‘i MOD 2 = 0 ∨ i MOD 2 = 1’ by decide_tac
     >- (‘i = 2 * q’ by (simp[Abbr ‘q’] >> decide_tac) >>
         ASM_REWRITE_TAC[popcount_low_even_odd] >>
         ‘z_node W (SUC md) (2 * q) ≤
          2 * (zeta * &(2 ** d) * (zeta / 2) pow (popcount_low d q))’
           by REAL_ARITH_TAC >>
         ‘2 * (zeta * &(2 ** d) * (zeta / 2) pow (popcount_low d q)) =
          zeta * (2 * &(2 ** d)) * (zeta / 2) pow (popcount_low d q)’
           by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
         REAL_ARITH_TAC)
     >- (‘i = 2 * q + 1’ by (simp[Abbr ‘q’] >> decide_tac) >>
         ASM_REWRITE_TAC[popcount_low_even_odd] >>
         ‘1 + popcount_low d q = SUC (popcount_low d q)’ by decide_tac >>
         pop_assum SUBST1_TAC >>
         REWRITE_TAC[realTheory.pow] >>
         ‘(z_node W md q) pow 2 ≤ zeta * z_node W md q’
           by (PURE_REWRITE_TAC[realTheory.POW_2] >>
               irule realTheory.REAL_LE_RMUL_IMP >> simp[]) >>
         ‘zeta * z_node W md q ≤
          zeta * (zeta * &(2 ** d) * (zeta / 2) pow (popcount_low d q))’
           by (irule realTheory.REAL_LE_LMUL_IMP >>
               (conj_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
         ‘zeta * (zeta * &(2 ** d) * (zeta / 2) pow (popcount_low d q)) =
          zeta * (2 * &(2 ** d)) * ((zeta / 2) * (zeta / 2) pow (popcount_low d q))’
           by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
         REAL_ARITH_TAC)
QED

(* Arıkan Eq. (45) in exact fourth-power polynomial form (zeta_0 = 1/16,
   eta_0 = 1/20, (1/2 + 1/20) - 4*(1/2 - 1/20) = -5/4):
   (z_{m+d, i})^4 * (2^{m+d})^5 <= 2^{5m}.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem arikan_eq_45_fourth_power[local]:
  ∀(W : (bool, β) memoryless_channel) m d i.
    wf_bdmc W ∧ i < 2 ** (m + d) ∧
    (∀t. t ≤ d ⇒ z_node W (m + t) (i DIV (2 ** (d - t))) ≤ (1 / 16 : real)) ∧
    (9 / 20 : real) * &d < &(popcount_low d i) ⇒
    (z_node W (m + d) i) pow 4 * &((2 ** (m + d)) ** 5) ≤ &(2 ** (5 * m))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘s = popcount_low d i’ >>
  ‘9 * d ≤ 20 * s’
    by (‘9 * (&d : real) < 20 * (&s : real)’ by REAL_ARITH_TAC >>
        qpat_x_assum ‘9 * (&d : real) < _’ mp_tac >>
        simp[] >> decide_tac) >>
  qspecl_then [‘W’, ‘1 / 16 : real’, ‘m’, ‘d’, ‘i’]
    mp_tac z_node_good_tail_stepwise >>
  (impl_tac >- simp[]) >>
  qpat_assum ‘Abbrev (s = _)’
    (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  strip_tac >>
  qspecl_then [‘W’, ‘m + d’, ‘i’] mp_tac z_node_bounds >>
  (impl_tac >- simp[]) >> strip_tac >>
  ‘(1 / 16 : real) / 2 = (1 / 2 : real) pow 5’
    by simp[] >>
  ‘z_node W (m + d) i ≤ &(2 ** d) * ((1 / 2 : real) pow (5 * s))’
    by (qpat_x_assum ‘z_node W (m + d) i ≤ _ * _’ mp_tac >>
        ASM_REWRITE_TAC[realTheory.REAL_POW_POW] >>
        strip_tac >>
        ‘0 ≤ &(2 ** d) * ((1 / 2 : real) pow (5 * s))’
          by (irule realTheory.REAL_LE_MUL >> simp[] >>
              irule realTheory.POW_POS >> REAL_ARITH_TAC) >>
        ‘(1 / 16 : real) * &(2 ** d) * ((1 / 2) pow (5 * s)) =
         (1 / 16) * (&(2 ** d) * ((1 / 2) pow (5 * s)))’
          by REWRITE_TAC[REAL_RING “∀a b c : real. (a * b) * c = a * (b * c)”] >>
        REAL_ARITH_TAC) >>
  ‘(z_node W (m + d) i) pow 4 ≤
   (&(2 ** d) * ((1 / 2 : real) pow (5 * s))) pow 4’
    by (irule realTheory.POW_LE >> simp[]) >>
  ‘(&(2 ** d) * ((1 / 2 : real) pow (5 * s))) pow 4 =
   ((2 : real) pow (4 * d)) * ((1 / 2 : real) pow (20 * s))’
    by (REWRITE_TAC[realTheory.POW_MUL, GSYM realTheory.REAL_OF_NUM_POW,
                    realTheory.REAL_POW_POW] >>
        ‘d * 4 = 4 * d ∧ 5 * s * 4 = 20 * s’ by decide_tac >>
        ASM_REWRITE_TAC[]) >>
  ‘(&((2 ** (m + d)) ** 5) : real) =
   ((2 : real) pow (5 * m)) * ((2 : real) pow (5 * d))’
    by (REWRITE_TAC[GSYM realTheory.REAL_OF_NUM_POW,
                    realTheory.REAL_POW_POW] >>
        ‘(m + d) * 5 = 5 * m + 5 * d’ by decide_tac >>
        ASM_REWRITE_TAC[realTheory.POW_ADD]) >>
  ‘(&(2 ** (5 * m)) : real) = (2 : real) pow (5 * m)’
    by REWRITE_TAC[GSYM realTheory.REAL_OF_NUM_POW] >>
  ‘0 ≤ (&((2 ** (m + d)) ** 5) : real)’ by simp[] >>
  ‘(z_node W (m + d) i) pow 4 * &((2 ** (m + d)) ** 5) ≤
   (((2 : real) pow (4 * d)) * ((1 / 2 : real) pow (20 * s))) *
   (((2 : real) pow (5 * m)) * ((2 : real) pow (5 * d)))’
    by (‘(z_node W (m + d) i) pow 4 * &((2 ** (m + d)) ** 5) ≤
         (&(2 ** d) * ((1 / 2 : real) pow (5 * s))) pow 4 * &((2 ** (m + d)) ** 5)’
          by (irule realTheory.REAL_LE_RMUL_IMP >> conj_tac >> REAL_ARITH_TAC) >>
        qpat_x_assum ‘_ ≤ (&(2 ** d) * _) pow 4 * _’ mp_tac >>
        ASM_REWRITE_TAC[] >> REAL_ARITH_TAC) >>
  ‘(((2 : real) pow (4 * d)) * ((1 / 2 : real) pow (20 * s))) *
   (((2 : real) pow (5 * m)) * ((2 : real) pow (5 * d))) =
   ((2 : real) pow (5 * m)) *
   (((2 : real) pow (9 * d)) * ((1 / 2 : real) pow (20 * s)))’
    by (‘(2 : real) pow (9 * d) =
         ((2 : real) pow (4 * d)) * ((2 : real) pow (5 * d))’
          by (‘9 * d = 4 * d + 5 * d’ by decide_tac >>
              ASM_REWRITE_TAC[realTheory.POW_ADD]) >>
        pop_assum SUBST1_TAC >>
        REWRITE_TAC[REAL_RING “∀a x b c : real. (a * x) * (b * c) = b * ((a * c) * x)”]) >>
  ‘((2 : real) pow (9 * d)) * ((1 / 2 : real) pow (20 * s)) ≤ 1’
    by (‘(2 : real) pow (9 * d) ≤ (2 : real) pow (20 * s)’
          by (dep_rewrite.DEP_REWRITE_TAC[realTheory.REAL_POW_MONO_EQ] >> simp[]) >>
        ‘0 ≤ (1 / 2 : real) pow (20 * s)’
          by (irule realTheory.POW_POS >> REAL_ARITH_TAC) >>
        ‘((2 : real) pow (9 * d)) * ((1 / 2 : real) pow (20 * s)) ≤
         ((2 : real) pow (20 * s)) * ((1 / 2 : real) pow (20 * s))’
          by (irule realTheory.REAL_LE_RMUL_IMP >> conj_tac >> REAL_ARITH_TAC) >>
        ‘((2 : real) pow (20 * s)) * ((1 / 2 : real) pow (20 * s)) = 1’
          by (REWRITE_TAC[GSYM realTheory.POW_MUL] >> ‘2 * (1 / 2 : real) = 1’ by REAL_ARITH_TAC >> ASM_REWRITE_TAC[realTheory.POW_ONE]) >>
        FULL_SIMP_TAC std_ss []) >>
  ‘0 ≤ (2 : real) pow (5 * m)’
    by (irule realTheory.POW_POS >> REAL_ARITH_TAC) >>
  ‘((2 : real) pow (5 * m)) *
   (((2 : real) pow (9 * d)) * ((1 / 2 : real) pow (20 * s))) ≤
   ((2 : real) pow (5 * m)) * 1’
    by (irule realTheory.REAL_LE_LMUL_IMP >> conj_tac >> REAL_ARITH_TAC) >>
  FULL_SIMP_TAC std_ss [realTheory.REAL_MUL_RID] >>
  metis_tac[realTheory.REAL_LE_TRANS]
QED

(* Fourth-root extraction: 0 <= z /\ 0 <= C /\ z^4 * (2^n)^5 <= C^4
   implies z <= C * inv (sqrt (sqrt (&((2 ** n) ** 5)))).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fourth_power_inv_sqrt_sqrt_le[local]:
  ∀(z : real) (C : real) (n : num).
    0 ≤ z ∧ 0 ≤ C ∧ z pow 4 * &((2 ** n) ** 5) ≤ C pow 4 ⇒
    z ≤ C * inv (sqrt (sqrt (&((2 ** n) ** 5))))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘N5 = (&((2 ** n) ** 5) : real)’ >>
  qabbrev_tac ‘u = real$sqrt (real$sqrt N5)’ >>
  ‘0 < N5 ∧ 0 ≤ N5’ by simp[Abbr ‘N5’] >>
  ‘0 < real$sqrt N5 ∧ 0 ≤ real$sqrt N5’
    by simp[realTheory.SQRT_POS_LT, realTheory.SQRT_POS_LE] >>
  ‘0 < u ∧ 0 ≤ u ∧ u ≠ 0’
    by (simp[Abbr ‘u’, realTheory.SQRT_POS_LT, realTheory.SQRT_POS_LE] >>
        ‘0 < real$sqrt (real$sqrt N5)’ by simp[realTheory.SQRT_POS_LT] >>
        REAL_ARITH_TAC) >>
  ‘u pow 4 = N5’
    by (‘4n = 2 * 2’ by decide_tac >>
        pop_assum SUBST1_TAC >>
        simp[GSYM realTheory.REAL_POW_POW, Abbr ‘u’, realTheory.SQRT_POW_2]) >>
  ‘(z * u) pow 4 ≤ C pow 4’
    by (REWRITE_TAC[realTheory.POW_MUL] >> ASM_REWRITE_TAC[]) >>
  ‘z * u ≤ C’
    by (CCONTR_TAC >> ‘C < z * u’ by REAL_ARITH_TAC >>
        ‘C pow (SUC 3) < (z * u) pow (SUC 3)’
          by (irule realTheory.POW_LT >> simp[]) >>
        ‘SUC 3 = 4’ by decide_tac >>
        gvs[] >> REAL_ARITH_TAC) >>
  ‘0 ≤ inv u’ by simp[realTheory.REAL_LE_INV] >>
  ‘(z * u) * inv u ≤ C * inv u’
    by (irule realTheory.REAL_LE_RMUL_IMP >> simp[]) >>
  ‘(z * u) * inv u = z * (u * inv u)’ by REWRITE_TAC[REAL_RING “∀a b c : real. (a * b) * c = a * (b * c)”] >>
  gvs[realTheory.REAL_MUL_RINV]
QED

(* Theorem 2 (Erdal Arıkan, 2009, arXiv:0807.3917v5, Section I-B.4 p. 3 &
   Section IV-B pp. 9-10):
   For any B-DMC W with I(W) > 0 and any fixed R < I(W), there exist C > 0
   and information sets A_seq n <= count (2^n) with |A_seq n| >= 2^n * R
   and Z(W_{2^n}^{(i)}) <= C * (2^n)^{-5/4} for all n >= 0 and i in A_seq n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_2_polarization_rate:
  ∀(W : (bool, β) memoryless_channel) (R : real).
    wf_bdmc W ∧ 0 < symmetric_capacity W ∧
    Normal R < symmetric_capacity W ⇒
    ∃(C : real) A_seq.
      0 < C ∧
      ∀n. A_seq n ⊆ count (2 ** n) ∧
          &(2 ** n) * R ≤ &(CARD (A_seq n)) ∧
          ∀i. i ∈ A_seq n ⇒
              real (bhattacharyya (split_channel W (2 ** n) i)) ≤
              C * inv (sqrt (sqrt (&((2 ** n) ** 5))))
Proof
  rpt strip_tac >>
  drule symmetric_capacity_bounds >> strip_tac >>
  qabbrev_tac ‘I0 = real (symmetric_capacity W)’ >>
  ‘0 < I0 ∧ I0 ≤ 1 ∧ R < I0 ∧ R ≤ 1’
    by (gvs[Abbr ‘I0’, extreal_of_num_def, extreal_lt_eq, real_normal] >>
        REAL_ARITH_TAC) >>
  qabbrev_tac ‘delta = if 0 < R then I0 - R else I0’ >>
  ‘0 < delta ∧ R ≤ I0 - delta’
    by (rw[Abbr ‘delta’] >> REAL_ARITH_TAC) >>
  qspecl_then [‘W’, ‘1 / 16 : real’, ‘delta’] mp_tac lemma_1_finite_horizon >>
  (impl_tac >- simp[]) >> disch_then (qx_choose_then ‘m1’ assume_tac) >>
  qabbrev_tac ‘n1 = m1 + flr (200 / delta) + 1’ >>
  ‘m1 ≤ n1’ by simp[Abbr ‘n1’] >>
  qabbrev_tac ‘C = (&(2 ** (2 * n1)) : real)’ >>
  qabbrev_tac ‘A_seq =
    λn : num.
      {i | i < 2 ** n ∧
           z_node W n i ≤ C * inv (sqrt (sqrt (&((2 ** n) ** 5))))}’ >>
  qexistsl_tac [‘C’, ‘A_seq’] >>
  (conj_tac >- simp[Abbr ‘C’]) >>
  qx_gen_tac ‘n’ >>
  (conj_tac >- simp[Abbr ‘A_seq’, SUBSET_DEF]) >>
  (reverse conj_tac >- simp[Abbr ‘A_seq’, z_node_def]) >>
  Cases_on ‘n < n1’
  >- (* Small-n regime 0 <= n < n1: C * (2^n)^{-5/4} >= 1 >= z_node W n i,
        so A_seq n = count (2^n) and &(2^n) * R <= &(2^n) * 1 = &(2^n) *)
     (‘A_seq n = count (2 ** n)’
        by (SIMP_TAC (srw_ss()) [Abbr ‘A_seq’, pred_setTheory.EXTENSION] >>
            qx_gen_tac ‘x’ >> eq_tac >> strip_tac >> simp[] >>
            drule_all z_node_bounds >> strip_tac >>
            irule fourth_power_inv_sqrt_sqrt_le >>
            ‘0 ≤ C’ by simp[Abbr ‘C’] >>
            simp[] >>
            ‘(z_node W n x) pow 4 ≤ 1 pow 4’
              by (irule realTheory.POW_LE >> simp[]) >>
            ‘(z_node W n x) pow 4 * &((2 ** n) ** 5) ≤
             1 * (&((2 ** n) ** 5) : real)’
              by (irule realTheory.REAL_LE_RMUL_IMP >> gvs[]) >>
            ‘(&((2 ** n) ** 5) : real) ≤ C pow 4’
              by simp[Abbr ‘C’, realTheory.REAL_OF_NUM_POW,
                      GSYM arithmeticTheory.EXP_EXP_MULT] >>
            REAL_ARITH_TAC) >>
      simp[] >>
      ‘&(2 ** n) * R ≤ (&(2 ** n) : real) * 1’
        by (irule realTheory.REAL_LE_LMUL_IMP >> simp[]) >>
      REAL_ARITH_TAC)
  >- (* Asymptotic regime n >= n1: combine Lemma 1 and Chebyshev concentration *)
     (‘n1 ≤ n ∧ m1 ≤ n’ by decide_tac >>
      qabbrev_tac ‘T_good =
        {i | i < 2 ** n ∧
             ∀k. m1 ≤ k ∧ k ≤ n ⇒
                 z_node W k (i DIV (2 ** (n - k))) ≤ (1 / 16 : real)}’ >>
      qabbrev_tac ‘B_ones =
        {i | i < 2 ** n ∧
             &(popcount_low (n - m1) i) ≤ (9 / 20 : real) * &(n - m1)}’ >>
      qpat_x_assum ‘∀n'. m1 ≤ n' ⇒ _’ (qspec_then ‘n’ mp_tac) >>
      (impl_tac >- simp[]) >>
      qpat_assum ‘Abbrev (T_good = _)’
        (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
      strip_tac >>
      qspecl_then [‘delta’, ‘m1’, ‘n’] mp_tac popcount_low_tail_concentration >>
      (impl_tac >- simp[Abbr ‘n1’]) >>
      qpat_assum ‘Abbrev (B_ones = _)’
        (fn th => REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
      strip_tac >>
      ‘FINITE T_good ∧ FINITE B_ones ∧ FINITE (A_seq n)’
        by (rpt conj_tac >> irule SUBSET_FINITE_I >>
            qexists_tac ‘count (2 ** n)’ >>
            simp[Abbr ‘T_good’, Abbr ‘B_ones’, Abbr ‘A_seq’, SUBSET_DEF]) >>
      ‘T_good DIFF B_ones ⊆ A_seq n’
        by (SIMP_TAC (srw_ss()) [Abbr ‘T_good’, Abbr ‘B_ones’, Abbr ‘A_seq’,
                                 SUBSET_DEF] >>
            qx_gen_tac ‘x’ >> strip_tac >> fs[] >>
            drule_all z_node_bounds >> strip_tac >>
            irule fourth_power_inv_sqrt_sqrt_le >>
            ‘0 ≤ C’ by simp[Abbr ‘C’] >>
            simp[] >>
            qabbrev_tac ‘d = n - m1’ >>
            ‘n = m1 + d’ by simp[Abbr ‘d’] >>
            qspecl_then [‘W’, ‘m1’, ‘d’, ‘x’] mp_tac arikan_eq_45_fourth_power >>
            impl_tac
            >- (gvs[] >> rpt strip_tac >>
                first_x_assum (qspec_then ‘m1 + t’ mp_tac) >>
                ‘m1 + d - (m1 + t) = d - t’ by decide_tac >>
                simp[]) >>
            strip_tac >>
            ‘(&(2 ** (5 * m1)) : real) ≤ C pow 4’
              by simp[Abbr ‘C’, realTheory.REAL_OF_NUM_POW,
                      GSYM arithmeticTheory.EXP_EXP_MULT] >>
            gvs[] >> REAL_ARITH_TAC) >>
      ‘CARD (T_good DIFF B_ones) ≤ CARD (A_seq n)’
        by (irule CARD_SUBSET >> simp[]) >>
      ‘&(CARD T_good) - &(CARD B_ones) ≤ (&(CARD (A_seq n)) : real)’
        by (qspecl_then [‘T_good’, ‘B_ones’] mp_tac CARD_DIFF_LOWER_BOUND >>
            (impl_tac >- simp[]) >> strip_tac >>
            ‘&(CARD (T_good DIFF B_ones)) ≤ (&(CARD (A_seq n)) : real)’
              by ASM_REWRITE_TAC[realTheory.REAL_OF_NUM_LE] >>
            REAL_ARITH_TAC) >>
      ‘&(2 ** n) * R ≤ &(2 ** n) * (I0 - delta)’
        by (irule realTheory.REAL_LE_LMUL_IMP >> simp[]) >>
      ‘&(2 ** n) * (I0 - delta) =
       &(2 ** n) * (I0 - delta / 2) - &(2 ** n) * (delta / 2)’
        by CONV_TAC (EQT_INTRO o REAL_FIELD) >>
      qpat_assum ‘Abbrev (I0 = _)’
        (fn th => FULL_SIMP_TAC std_ss [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
      REAL_ARITH_TAC)
QED

(* Exact algebraic equivalence between inv (sqrt (sqrt (&((2 ** n) ** 5))))
   and (&(2 ** n)) powr (-5 / 4) in transcTheory.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem inv_sqrt_sqrt_pow5_eq_powr:
  ∀n : num.
    inv (sqrt (sqrt (&((2 ** n) ** 5)))) =
    (&(2 ** n) : real) powr (-5 / 4 : real)
Proof
  gen_tac >>
  qabbrev_tac ‘N5 = (&((2 ** n) ** 5) : real)’ >>
  qabbrev_tac ‘lhs_v = inv (real$sqrt (real$sqrt N5))’ >>
  qabbrev_tac ‘rhs_v = (&(2 ** n) : real) powr (-5 / 4 : real)’ >>
  match_mp_tac transcTheory.RPOW_UNIQ_BASE >>
  qexists_tac ‘&4 : real’ >>
  ‘0 < N5 ∧ 0 ≤ N5’ by simp[Abbr ‘N5’] >>
  ‘0 < real$sqrt N5 ∧ 0 ≤ real$sqrt N5’
    by simp[realTheory.SQRT_POS_LT, realTheory.SQRT_POS_LE] >>
  ‘0 < real$sqrt (real$sqrt N5)’ by simp[realTheory.SQRT_POS_LT] >>
  ‘0 < lhs_v’ by simp[Abbr ‘lhs_v’, realTheory.REAL_INV_POS] >>
  ‘0 < rhs_v’
    by (simp[Abbr ‘rhs_v’] >> irule transcTheory.RPOW_POS_LT >> simp[]) >>
  simp[] >>
  ‘lhs_v powr (&4 : real) = inv ((&(2 ** n) : real) pow 5)’
    by (REWRITE_TAC[cj 3 transcTheory.powr_def] >>
        SIMP_TAC std_ss [Abbr ‘lhs_v’, realTheory.REAL_POW_INV] >>
        AP_TERM_TAC >>
        ‘4n = 2 * 2’ by decide_tac >>
        pop_assum SUBST1_TAC >>
        REWRITE_TAC[GSYM realTheory.REAL_POW_POW] >>
        ASM_SIMP_TAC std_ss [realTheory.SQRT_POW_2] >>
        SIMP_TAC std_ss [Abbr ‘N5’, realTheory.REAL_OF_NUM_POW]) >>
  ‘rhs_v powr (&4 : real) = inv ((&(2 ** n) : real) pow 5)’
    by (SIMP_TAC std_ss [Abbr ‘rhs_v’] >>
        dep_rewrite.DEP_REWRITE_TAC[transcTheory.RPOW_RPOW] >>
        (conj_tac >- simp[]) >>
        ‘(-5 / 4 : real) * &4 = -&5’ by REAL_ARITH_TAC >>
        pop_assum SUBST1_TAC >>
        REWRITE_TAC[cj 4 transcTheory.powr_def]) >>
  ASM_REWRITE_TAC[]
QED

(* Companion identity inv (sqrt (sqrt (&(2 ** n)))) = (&(2 ** n)) powr (-1 / 4)
   exported for Theorem 3 in polar_coding_theoremScript.sml.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem inv_sqrt_sqrt_eq_powr:
  ∀n : num.
    inv (sqrt (sqrt (&(2 ** n)))) =
    (&(2 ** n) : real) powr (-1 / 4 : real)
Proof
  gen_tac >>
  qabbrev_tac ‘N1 = (&(2 ** n) : real)’ >>
  qabbrev_tac ‘lhs_v = inv (real$sqrt (real$sqrt N1))’ >>
  qabbrev_tac ‘rhs_v = N1 powr (-1 / 4 : real)’ >>
  match_mp_tac transcTheory.RPOW_UNIQ_BASE >>
  qexists_tac ‘&4 : real’ >>
  ‘0 < N1 ∧ 0 ≤ N1’ by simp[Abbr ‘N1’] >>
  ‘0 < real$sqrt N1 ∧ 0 ≤ real$sqrt N1’
    by simp[realTheory.SQRT_POS_LT, realTheory.SQRT_POS_LE] >>
  ‘0 < real$sqrt (real$sqrt N1)’ by simp[realTheory.SQRT_POS_LT] >>
  ‘0 < lhs_v’ by simp[Abbr ‘lhs_v’, realTheory.REAL_INV_POS] >>
  ‘0 < rhs_v’
    by (simp[Abbr ‘rhs_v’] >> irule transcTheory.RPOW_POS_LT >> simp[]) >>
  simp[] >>
  ‘lhs_v powr (&4 : real) = inv N1’
    by (REWRITE_TAC[cj 3 transcTheory.powr_def] >>
        SIMP_TAC std_ss [Abbr ‘lhs_v’, realTheory.REAL_POW_INV] >>
        AP_TERM_TAC >>
        ‘4n = 2 * 2’ by decide_tac >>
        pop_assum SUBST1_TAC >>
        REWRITE_TAC[GSYM realTheory.REAL_POW_POW] >>
        ASM_SIMP_TAC std_ss [realTheory.SQRT_POW_2]) >>
  ‘rhs_v powr (&4 : real) = inv N1’
    by (SIMP_TAC std_ss [Abbr ‘rhs_v’] >>
        dep_rewrite.DEP_REWRITE_TAC[transcTheory.RPOW_RPOW] >>
        (conj_tac >- simp[]) >>
        ‘(-1 / 4 : real) * &4 = -&1’ by REAL_ARITH_TAC >>
        pop_assum SUBST1_TAC >>
        REWRITE_TAC[cj 4 transcTheory.powr_def, realTheory.POW_1]) >>
  ASM_REWRITE_TAC[]
QED

(* Real-valued asymptotic Landau Big-O class O(g(n)) on sequences num -> real.

   Written by Gemini (Google DeepMind AI agent) *)
Definition real_big_O_def:
  real_big_O (g : num -> real) =
    {f : num -> real |
     ∃N0 (C : real). 0 < C ∧ ∀n. N0 ≤ n ⇒ abs (f n) ≤ C * abs (g n)}
End

(* Membership criterion for real_big_O from a global non-negative bound.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem real_big_O_global_pos:
  ∀(f : num -> real) (g : num -> real) (C : real).
    0 < C ∧ (∀n. 0 ≤ f n ∧ 0 ≤ g n ∧ f n ≤ C * g n) ⇒
    f ∈ real_big_O g
Proof
  rw[real_big_O_def] >>
  qexistsl_tac [‘0’, ‘C’] >> simp[] >>
  qx_gen_tac ‘n’ >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  REAL_ARITH_TAC
QED

(* Theorem 2 formulated with transcTheory real power (&(2 ** n)) powr (-5 / 4).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_2_polarization_rate_powr:
  ∀(W : (bool, β) memoryless_channel) (R : real).
    wf_bdmc W ∧ 0 < symmetric_capacity W ∧
    Normal R < symmetric_capacity W ⇒
    ∃(C : real) A_seq.
      0 < C ∧
      ∀n. A_seq n ⊆ count (2 ** n) ∧
          &(2 ** n) * R ≤ &(CARD (A_seq n)) ∧
          ∀i. i ∈ A_seq n ⇒
              real (bhattacharyya (split_channel W (2 ** n) i)) ≤
              C * ((&(2 ** n) : real) powr (-5 / 4 : real))
Proof
  rpt strip_tac >>
  drule_all theorem_2_polarization_rate >> strip_tac >>
  qexistsl_tac [‘C’, ‘A_seq’] >>
  simp[GSYM inv_sqrt_sqrt_pow5_eq_powr]
QED

(* Theorem 2 formulated with real_big_O ((2^n)^{-5/4}).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_2_polarization_rate_big_O:
  ∀(W : (bool, β) memoryless_channel) (R : real).
    wf_bdmc W ∧ 0 < symmetric_capacity W ∧
    Normal R < symmetric_capacity W ⇒
    ∃A_seq (z_max : num -> real).
      z_max ∈ real_big_O (λn. (&(2 ** n) : real) powr (-5 / 4 : real)) ∧
      ∀n. A_seq n ⊆ count (2 ** n) ∧
          &(2 ** n) * R ≤ &(CARD (A_seq n)) ∧
          ∀i. i ∈ A_seq n ⇒
              real (bhattacharyya (split_channel W (2 ** n) i)) ≤ z_max n
Proof
  rpt strip_tac >>
  drule_all theorem_2_polarization_rate_powr >> strip_tac >>
  qexistsl_tac [‘A_seq’, ‘λn. C * ((&(2 ** n) : real) powr (-5 / 4 : real))’] >>
  conj_tac
  >- (irule real_big_O_global_pos >> qexists_tac ‘C’ >> simp[] >>
      qx_gen_tac ‘n’ >>
      ‘0 < (&(2 ** n) : real) powr (-5 / 4 : real)’
        by (irule transcTheory.RPOW_POS_LT >> simp[]) >>
      conj_tac
      >- (irule realTheory.REAL_LE_MUL >> REAL_ARITH_TAC)
      >- REAL_ARITH_TAC)
  >- simp[]
QED
