(* ========================================================================= *)
(*   Polar Coding Theorem: Block Error Probability Decay O(N^{-1/4}) and     *)
(*   Asymptotic Convergence to Zero under Successive Cancellation Decoding   *)
(*   (Erdal Arıkan, 2009, arXiv:0807.3917, Section I-C Theorem 3 &           *)
(*   Section V-C Eq. 54).                                                    *)
(*                                                                           *)
(*   Written by Gemini (Google DeepMind AI agent).                           *)
(* ========================================================================= *)

Theory polar_coding_theorem

Ancestors
  combin arithmetic pair list pred_set
  real real_sigma transc seq extreal_base extreal
  memoryless_channel bhattacharyya capacity bdmc
  polar_encode combine_channel split_channel
  channel_polarization successive_cancellation_decoder

Libs
  dep_rewrite realLib;

val _ = temp_overload_on ("-->", “seq$tends_num_real”);
val _ = hide "W";
val _ = hide "S";
val _ = hide "K";

(* ------------------------------------------------------------------------- *)
(* Block 1: Finite Subset Extraction, Radical Algebra, and Sequence Limit    *)
(* ------------------------------------------------------------------------- *)

(* Every finite set s admits a subset t ⊆ s of any prescribed cardinality
   k ≤ CARD s.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem finite_choose_subset[local]:
  ∀(s : α -> bool).
    FINITE s ⇒
    ∀k. k ≤ CARD s ⇒ ∃t. t ⊆ s ∧ CARD t = k
Proof
  Induct_on ‘FINITE’ >> simp[] >>
  rpt strip_tac >> Cases_on ‘k’ >> gvs[]
  >- (qexists_tac ‘∅’ >> simp[])
  >- (first_x_assum (drule_then strip_assume_tac) >>
      qexists_tac ‘e INSERT t’ >>
      ‘FINITE t’ by metis_tac[SUBSET_FINITE] >>
      ‘e ∉ t’ by (strip_tac >> fs[SUBSET_DEF]) >>
      simp[SUBSET_INSERT_RIGHT])
QED

(* Projecting an extreal upper bound e ≤ Normal u (with 0 ≤ u) to real e ≤ u.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem extreal_le_normal_imp_real_le[local]:
  ∀(e : extreal) (u : real).
    e ≤ Normal u ∧ 0 ≤ u ⇒ real e ≤ u
Proof
  Cases >> simp[extreal_le_def]
QED

(* Projecting non-negativity (0 : extreal) ≤ e to (0 : real) ≤ real e.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem extreal_pos_imp_real_pos[local]:
  ∀(e : extreal). 0 ≤ e ⇒ 0 ≤ real e
Proof
  Cases >> simp[extreal_of_num_def, extreal_le_def]
QED

(* Fourth-root factorization of (2 ** n) ** 5:
   sqrt (sqrt (&((2 ** n) ** 5))) = sqrt (sqrt (&(2 ** n))) * &(2 ** n).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sqrt_sqrt_two_pow_five[local]:
  ∀n : num.
    (sqrt (sqrt (&((2 ** n) ** 5) : real)) : real) =
    sqrt (sqrt (&(2 ** n) : real)) * (&(2 ** n) : real)
Proof
  gen_tac >>
  qabbrev_tac ‘m : num = 2 ** n’ >>
  qabbrev_tac ‘mr : real = &m’ >>
  ‘0 < m’ by simp[Abbr ‘m’] >>
  ‘0 < mr ∧ 0 ≤ mr’ by simp[Abbr ‘mr’] >>
  ‘0 ≤ mr pow 2 ∧ 0 ≤ (mr pow 2) pow 2’
    by simp[realTheory.REAL_LE_POW2] >>
  ‘0 ≤ real$sqrt mr’ by simp[realTheory.SQRT_POS_LE] >>
  ‘(&(m ** 5) : real) = mr * ((mr pow 2) pow 2)’
    by (‘(&(m ** 5) : real) = mr pow 5’
          by simp[Abbr ‘mr’, realTheory.REAL_OF_NUM_POW] >>
        pop_assum SUBST1_TAC >>
        ‘5n = 1 + 2 * 2’ by decide_tac >>
        pop_assum SUBST1_TAC >>
        REWRITE_TAC[realTheory.POW_ADD, GSYM realTheory.REAL_POW_POW,
                    realTheory.POW_1]) >>
  pop_assum SUBST1_TAC >>
  ASM_SIMP_TAC std_ss [realTheory.SQRT_MUL, realTheory.POW_2_SQRT]
QED

(* Exact exponent reduction (2^n) * (2^n)^{-5/4} = (2^n)^{-1/4} in radical form:
   &(2 ** n) * inv (sqrt (sqrt (&((2 ** n) ** 5)))) = inv (sqrt (sqrt (&(2 ** n)))).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem two_pow_mul_inv_sqrt_sqrt_five:
  ∀n : num.
    (&(2 ** n) : real) * inv (sqrt (sqrt (&((2 ** n) ** 5)))) =
    inv (sqrt (sqrt (&(2 ** n))))
Proof
  gen_tac >>
  REWRITE_TAC[sqrt_sqrt_two_pow_five] >>
  qabbrev_tac ‘x : real = &((2 ** n) : num)’ >>
  ‘0 < x’ by simp[Abbr ‘x’] >>
  ‘0 < real$sqrt x’ by simp[realTheory.SQRT_POS_LT] >>
  ‘0 < real$sqrt (real$sqrt x)’ by simp[realTheory.SQRT_POS_LT] >>
  ‘real$sqrt (real$sqrt x) ≠ 0 ∧ x ≠ 0’ by REAL_ASM_ARITH_TAC >>
  ‘inv (real$sqrt (real$sqrt x) * x) = inv (real$sqrt (real$sqrt x)) * inv x’
    by (irule realTheory.REAL_INV_MUL >> simp[]) >>
  pop_assum SUBST1_TAC >>
  ‘x * (inv (real$sqrt (real$sqrt x)) * inv x) =
   (x * inv x) * inv (real$sqrt (real$sqrt x))’
    by REAL_ARITH_TAC >>
  pop_assum SUBST1_TAC >>
  simp[realTheory.REAL_MUL_RINV]
QED

(* Positivity of inv (sqrt (sqrt (&(2 ** n)))) for all n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem inv_sqrt_sqrt_two_pow_pos[local]:
  ∀n : num.
    0 < inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real))) ∧
    0 ≤ inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real))) ∧
    0 < inv (real$sqrt (real$sqrt (&(((2 ** n) ** 5) : num) : real))) ∧
    0 ≤ inv (real$sqrt (real$sqrt (&(((2 ** n) ** 5) : num) : real)))
Proof
  gen_tac >>
  qabbrev_tac ‘x1 : real = &((2 ** n) : num)’ >>
  qabbrev_tac ‘x5 : real = &(((2 ** n) ** 5) : num)’ >>
  ‘0 < x1 ∧ 0 < x5’ by simp[Abbr ‘x1’, Abbr ‘x5’] >>
  ‘0 < real$sqrt x1 ∧ 0 < real$sqrt x5’ by simp[realTheory.SQRT_POS_LT] >>
  ‘0 < real$sqrt (real$sqrt x1) ∧ 0 < real$sqrt (real$sqrt x5)’
    by simp[realTheory.SQRT_POS_LT] >>
  ‘0 < inv (real$sqrt (real$sqrt x1)) ∧ 0 < inv (real$sqrt (real$sqrt x5))’
    by simp[realTheory.REAL_INV_POS] >>
  REAL_ASM_ARITH_TAC
QED

(* Strict exponential growth k < 2 ** k on natural numbers.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem lt_two_pow[local]:
  ∀k : num. k < 2 ** k
Proof
  Induct >> simp[arithmeticTheory.EXP] >> decide_tac
QED

(* Asymptotic decay of (2^n)^{-1/4} = inv (sqrt (sqrt (&(2 ** n)))) to 0
   as n -> infty.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem inv_sqrt_sqrt_two_pow_tendsto_zero:
  ((λn : num. inv (sqrt (sqrt (&(2 ** n))))) : num -> real) --> (0 : real)
Proof
  ho_match_mp_tac seqTheory.SEQ_INV0 >>
  qx_gen_tac ‘y’ >>
  qabbrev_tac ‘a : real = if y < 0 then 1 else y + 1’ >>
  ‘0 ≤ a ∧ y < a’ by (simp[Abbr ‘a’] >> REAL_ARITH_TAC) >>
  ‘0 ≤ a pow 2 ∧ 0 ≤ (a pow 2) pow 2’ by simp[realTheory.REAL_LE_POW2] >>
  qspec_then ‘(a pow 2) pow 2’ strip_assume_tac realTheory.REAL_BIGNUM >>
  qexists_tac ‘n’ >>
  qx_gen_tac ‘m’ >> simp[arithmeticTheory.GREATER_EQ] >> strip_tac >>
  ‘n < (2 ** m : num)’
    by (‘m < (2 ** m : num)’ by simp[lt_two_pow] >> decide_tac) >>
  qabbrev_tac ‘xm : real = &((2 ** m) : num)’ >>
  ‘(a pow 2) pow 2 < xm’
    by (‘(&n : real) < xm’ by simp[Abbr ‘xm’] >> REAL_ASM_ARITH_TAC) >>
  ‘real$sqrt ((a pow 2) pow 2) < real$sqrt xm’
    by (irule realTheory.SQRT_MONO_LT >> simp[]) >>
  ‘0 ≤ real$sqrt ((a pow 2) pow 2)’
    by (irule realTheory.SQRT_POS_LE >> simp[]) >>
  ‘real$sqrt (real$sqrt ((a pow 2) pow 2)) < real$sqrt (real$sqrt xm)’
    by (irule realTheory.SQRT_MONO_LT >> simp[]) >>
  ‘real$sqrt ((a pow 2) pow 2) = a pow 2’ by ASM_SIMP_TAC std_ss [realTheory.POW_2_SQRT] >>
  ‘real$sqrt (a pow 2) = a’ by ASM_SIMP_TAC std_ss [realTheory.POW_2_SQRT] >>
  gvs[realTheory.real_gt] >> REAL_ASM_ARITH_TAC
QED

(* Equivalence between inv (sqrt (sqrt (&(2 ** n)))) and powr (-1 / 4),
   re-exporting channel_polarizationTheory.inv_sqrt_sqrt_eq_powr.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem inv_sqrt_sqrt_two_pow_eq_powr:
  ∀n : num.
    inv (sqrt (sqrt (&(2 ** n)))) =
    (&(2 ** n) : real) powr (-1 / 4 : real)
Proof
  ACCEPT_TAC inv_sqrt_sqrt_eq_powr
QED

(* ------------------------------------------------------------------------- *)
(* Block 2: Non-Negativity of Block Error Probabilities                      *)
(* ------------------------------------------------------------------------- *)

(* Non-negativity of fixed-frozen and ensemble-averaged block error
   probabilities for any well-formed B-DMC W at block-length 2 ** n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_nonneg[local]:
  ∀(W : (bool, β) memoryless_channel) n A.
    wf_bdmc W ⇒
    0 ≤ block_error_prob_avg W (2 ** n) A ∧
    0 ≤ real (block_error_prob_avg W (2 ** n) A) ∧
    ∀u_frozen.
      0 ≤ block_error_prob_fixed W (2 ** n) A u_frozen ∧
      0 ≤ real (block_error_prob_fixed W (2 ** n) A u_frozen)
Proof
  rpt strip_tac
  >- (drule block_error_prob_avg_normal >> simp[])
  >- (drule block_error_prob_avg_normal >> simp[])
  >- (irule block_error_prob_fixed_pos >> simp[])
  >- (irule extreal_pos_imp_real_pos >>
      irule block_error_prob_fixed_pos >> simp[])
QED

(* ------------------------------------------------------------------------- *)
(* Block 3: Core Polar Coding Sum Bound (Arıkan Section V-C Eq. 54)          *)
(* ------------------------------------------------------------------------- *)

(* Master Bhattacharyya sum bound for polar information sets (Arıkan Eq. 54):
   given wf_bdmc W, 0 ≤ R, and Normal R < symmetric_capacity W, there exists
   C > 0 such that for every n and every polar information set A of dimension
   K = flr (&(2 ** n) * R), the extreal sum of Z(W_{2^n}^{(i)}) over i ∈ A is
   at most Normal (C * inv (sqrt (sqrt (&(2 ** n))))).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_info_set_bhattacharyya_sum_bound:
  ∀(W : (bool, β) memoryless_channel) (R : real).
    wf_bdmc W ∧ 0 ≤ R ∧ Normal R < symmetric_capacity W ⇒
    ∃(C : real).
      0 < C ∧
      ∀n A.
        is_polar_info_set W (2 ** n) (flr (&(2 ** n) * R)) A ⇒
        ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) A ≤
        Normal (C * inv (sqrt (sqrt (&(2 ** n)))))
Proof
  rpt strip_tac >>
  (* Step 1: Deduce 0 < symmetric_capacity W from 0 ≤ R < I(W) *)
  drule symmetric_capacity_bounds >> strip_tac >>
  ‘0 < c’ by (gvs[extreal_lt_eq] >> REAL_ASM_ARITH_TAC) >>
  (* Step 2: Instantiate Theorem 2 to obtain C > 0 and B_seq *)
  qspecl_then [‘W’, ‘R’] mp_tac theorem_2_polarization_rate >>
  (impl_tac >- simp[extreal_of_num_def, extreal_lt_eq]) >>
  disch_then (qx_choosel_then [‘C’, ‘B_seq’] strip_assume_tac) >>
  qexists_tac ‘C’ >> simp[] >>
  qx_genl_tac [‘n’, ‘A’] >> strip_tac >>
  (* Step 3: Floor and cardinality bounds for K = flr (R * &(2 ** n)) *)
  qabbrev_tac ‘K : num = flr (R * (&((2 ** n) : num) : real))’ >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  ‘FINITE (B_seq n)’ by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
  ‘0 ≤ R * (&((2 ** n) : num) : real)’
    by (irule realTheory.REAL_LE_MUL >> simp[]) >>
  ‘(&K : real) ≤ R * (&((2 ** n) : num) : real)’
    by (simp[Abbr ‘K’] >> irule realTheory.NUM_FLOOR_LE >> simp[]) >>
  ‘(&K : real) ≤ &(CARD (B_seq n))’ by REAL_ASM_ARITH_TAC >>
  ‘K ≤ CARD (B_seq n)’ by gvs[] >>
  ‘CARD (B_seq n) ≤ (2 ** n : num)’
    by (‘CARD (B_seq n) ≤ CARD (count (2 ** n))’
          by (irule CARD_SUBSET >> simp[]) >>
        gvs[]) >>
  ‘K ≤ (2 ** n : num)’ by decide_tac >>
  (* Step 4: Extract K-element subset B' ⊆ B_seq n ⊆ count (2 ** n) *)
  drule finite_choose_subset >>
  disch_then (qspec_then ‘K’ mp_tac) >> simp[] >>
  disch_then (qx_choose_then ‘B'’ strip_assume_tac) >>
  ‘B' ⊆ count (2 ** n)’ by metis_tac[SUBSET_TRANS] >>
  ‘FINITE B'’ by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
  (* Step 5: Apply polar_info_set_minimal: ∑ Z A ≤ ∑ Z B' *)
  ‘∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) A ≤
   ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) B'’
    by (qspecl_then [‘W’, ‘n’, ‘K’, ‘A’, ‘B'’] mp_tac polar_info_set_minimal >>
        simp[Abbr ‘K’]) >>
  irule le_trans >>
  first_x_assum (irule_at (Pos hd)) >>
  (* Step 6: Convert ∑ Z B' to Normal (REAL_SUM_IMAGE ...) and bound by K * C * N^{-5/4} *)
  ‘∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) B' =
   Normal (REAL_SUM_IMAGE
             (λi. real (bhattacharyya (split_channel W (2 ** n) i))) B')’
    by (‘∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) B' =
         ∑ (λi. Normal (real (bhattacharyya (split_channel W (2 ** n) i)))) B'’
          by (ho_match_mp_tac EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
              qx_gen_tac ‘i’ >> strip_tac >>
              ‘i < (2 ** n : num)’
                by (qpat_x_assum ‘B' ⊆ count (2 ** n)’ mp_tac >>
                    simp[SUBSET_DEF]) >>
              ‘wf_bdmc (split_channel W (2 ** n) i)’
                by simp[wf_bdmc_split_channel] >>
              drule bhattacharyya_bounds >> strip_tac >> gvs[]) >>
        pop_assum SUBST1_TAC >>
        simp[EXTREAL_SUM_IMAGE_NORMAL]) >>
  pop_assum SUBST1_TAC >>
  simp[extreal_le_eq] >>
  qabbrev_tac ‘u5 : real = C * inv (real$sqrt (real$sqrt (&(((2 ** n) ** 5) : num) : real)))’ >>
  ‘REAL_SUM_IMAGE
     (λi. real (bhattacharyya (split_channel W (2 ** n) i))) B' ≤
   REAL_SUM_IMAGE (λi. u5) B'’
    by (qspec_then ‘B'’ mp_tac REAL_SUM_IMAGE_MONO >> simp[] >>
        disch_then ho_match_mp_tac >>
        qx_gen_tac ‘i’ >> strip_tac >>
        ‘i ∈ B_seq n’
          by (qpat_x_assum ‘B' ⊆ B_seq n’ mp_tac >> simp[SUBSET_DEF]) >>
        simp[Abbr ‘u5’]) >>
  ‘REAL_SUM_IMAGE (λi. u5) B' = (&K : real) * u5’
    by simp[REAL_SUM_IMAGE_FINITE_CONST3] >>
  ‘0 ≤ u5’
    by (simp[Abbr ‘u5’] >> irule realTheory.REAL_LE_MUL >>
        simp[inv_sqrt_sqrt_two_pow_pos] >> REAL_ASM_ARITH_TAC) >>
  ‘(&K : real) * u5 ≤ (&((2 ** n) : num) : real) * u5’
    by (irule realTheory.REAL_LE_RMUL_IMP >> simp[]) >>
  ‘(&((2 ** n) : num) : real) * u5 = C * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’
    by (simp[Abbr ‘u5’] >>
        ‘(&((2 ** n) : num) : real) *
           (C * inv (real$sqrt (real$sqrt (&(((2 ** n) ** 5) : num) : real)))) =
         C * ((&((2 ** n) : num) : real) *
           inv (real$sqrt (real$sqrt (&(((2 ** n) ** 5) : num) : real))))’
          by REAL_ARITH_TAC >>
        pop_assum SUBST1_TAC >>
        simp[two_pow_mul_inv_sqrt_sqrt_five]) >>
  REAL_ASM_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Block 4: Theorem 3 (O(N^{-1/4}) Bound, Convergence -> 0, & Fixed Frozen)  *)
(* ------------------------------------------------------------------------- *)

(* Theorem 3 (Erdal Arıkan, 2009, arXiv:0807.3917, Section I-C Eq. 15 &
   Section V-C Eq. 54): for any well-formed B-DMC W and fixed rate 0 ≤ R < I(W),
   there exists C > 0 such that for every level n and every polar information
   set A of dimension flr (&(2 ** n) * R), the ensemble-averaged block error
   probability under SC decoding is at most C * (2^n)^{-1/4}.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_3_polar_coding:
  ∀(W : (bool, β) memoryless_channel) (R : real).
    wf_bdmc W ∧ 0 ≤ R ∧ Normal R < symmetric_capacity W ⇒
    ∃(C : real).
      0 < C ∧
      ∀n A.
        is_polar_info_set W (2 ** n) (flr (&(2 ** n) * R)) A ⇒
        real (block_error_prob_avg W (2 ** n) A) ≤
        C * inv (sqrt (sqrt (&(2 ** n))))
Proof
  rpt strip_tac >>
  drule_all polar_info_set_bhattacharyya_sum_bound >>
  disch_then (qx_choose_then ‘C’ strip_assume_tac) >>
  qexists_tac ‘C’ >> ASM_REWRITE_TAC[] >>
  qx_genl_tac [‘n’, ‘A’] >> strip_tac >>
  first_x_assum (qspecl_then [‘n’, ‘A’] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  ‘A ⊆ count (2 ** n)’ by fs[is_polar_info_set_def] >>
  drule_all proposition_2_avg >> strip_tac >>
  ‘block_error_prob_avg W (2 ** n) A ≤
   Normal (C * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real))))’
    by (irule le_trans >>
        first_x_assum (irule_at (Pos hd)) >>
        first_assum ACCEPT_TAC) >>
  irule extreal_le_normal_imp_real_le >> simp[] >>
  irule realTheory.REAL_LE_MUL >>
  simp[inv_sqrt_sqrt_two_pow_pos] >> REAL_ASM_ARITH_TAC
QED

(* Theorem 3 asymptotic convergence corollary (Erdal Arıkan, 2009, Section I-C
   & Section V-C): for any well-formed B-DMC W, fixed rate 0 ≤ R < I(W), and
   sequence A_seq of polar information sets of dimension flr (&(2 ** n) * R),
   the SC block error probability converges to 0 as n -> infty.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_3_polar_coding_tendsto_zero:
  ∀(W : (bool, β) memoryless_channel) (R : real) (A_seq : num -> num -> bool).
    wf_bdmc W ∧ 0 ≤ R ∧ Normal R < symmetric_capacity W ∧
    (∀n. is_polar_info_set W (2 ** n) (flr (&(2 ** n) * R)) (A_seq n)) ⇒
    ((λn : num. real (block_error_prob_avg W (2 ** n) (A_seq n))) : num -> real) -->
    (0 : real)
Proof
  rpt strip_tac >>
  qspecl_then [‘W’, ‘R’] mp_tac theorem_3_polar_coding >>
  (impl_tac >- fs[]) >>
  disch_then (qx_choose_then ‘C’ strip_assume_tac) >>
  qspecl_then
    [‘λn : num. (0 : real)’,
     ‘λn : num. real (block_error_prob_avg W (2 ** n) (A_seq n))’,
     ‘λn : num. C * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’,
     ‘0 : real’]
    mp_tac seqTheory.SEQ_SANDWICH >>
  impl_tac
  >- (rpt conj_tac
      >- REWRITE_TAC[seqTheory.SEQ_CONST]
      >- (‘(0 : real) = C * 0’ by REAL_ARITH_TAC >>
          pop_assum SUBST1_TAC >>
          ho_match_mp_tac seqTheory.SEQ_MUL >>
          REWRITE_TAC[seqTheory.SEQ_CONST, inv_sqrt_sqrt_two_pow_tendsto_zero])
      >- (qx_gen_tac ‘n’ >>
          conj_tac
          >- simp[block_error_prob_nonneg]
          >- (qpat_x_assum ‘∀n A. _ ⇒ _’ (qspecl_then [‘n’, ‘A_seq n’] mp_tac) >>
              fs[])))
  >- simp[]
QED

(* Theorem 3 existential fixed-frozen-vector O(N^{-1/4}) corollary
   (Erdal Arıkan, 2009, combining Eq. 14 of Proposition 2 with Theorem 3):
   for any well-formed B-DMC W (without assuming channel symmetry) and
   0 ≤ R < I(W), there exists C > 0 such that for every n and polar
   information set A of dimension flr (&(2 ** n) * R), there exists a
   deterministic frozen vector u_frozen of length 2 ** n achieving fixed-coset
   block error probability at most C * (2^n)^{-1/4}.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_3_polar_coding_fixed:
  ∀(W : (bool, β) memoryless_channel) (R : real).
    wf_bdmc W ∧ 0 ≤ R ∧ Normal R < symmetric_capacity W ⇒
    ∃(C : real).
      0 < C ∧
      ∀n A.
        is_polar_info_set W (2 ** n) (flr (&(2 ** n) * R)) A ⇒
        ∃u_frozen.
          LENGTH u_frozen = 2 ** n ∧
          real (block_error_prob_fixed W (2 ** n) A u_frozen) ≤
          C * inv (sqrt (sqrt (&(2 ** n))))
Proof
  rpt strip_tac >>
  drule_all polar_info_set_bhattacharyya_sum_bound >>
  disch_then (qx_choose_then ‘C’ strip_assume_tac) >>
  qexists_tac ‘C’ >> ASM_REWRITE_TAC[] >>
  qx_genl_tac [‘n’, ‘A’] >> strip_tac >>
  first_x_assum (qspecl_then [‘n’, ‘A’] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  ‘A ⊆ count (2 ** n)’ by fs[is_polar_info_set_def] >>
  drule_all proposition_2_exists_frozen >> strip_tac >>
  qexists_tac ‘u_frozen’ >> simp[] >>
  ‘block_error_prob_fixed W (2 ** n) A u_frozen ≤
   Normal (C * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real))))’
    by (irule le_trans >>
        first_x_assum (irule_at (Pos hd)) >>
        first_assum ACCEPT_TAC) >>
  irule extreal_le_normal_imp_real_le >> simp[] >>
  irule realTheory.REAL_LE_MUL >>
  simp[inv_sqrt_sqrt_two_pow_pos] >> REAL_ASM_ARITH_TAC
QED

(* Theorem 3 existential fixed-frozen-vector asymptotic convergence corollary:
   for any well-formed B-DMC W, fixed rate 0 ≤ R < I(W), and sequence A_seq of
   polar information sets of dimension flr (&(2 ** n) * R), there exists a
   sequence u_frozen_seq of deterministic frozen vectors of length 2 ** n whose
   fixed-coset SC block error probability converges to 0 as n -> infty.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_3_polar_coding_fixed_tendsto_zero:
  ∀(W : (bool, β) memoryless_channel) (R : real) (A_seq : num -> num -> bool).
    wf_bdmc W ∧ 0 ≤ R ∧ Normal R < symmetric_capacity W ∧
    (∀n. is_polar_info_set W (2 ** n) (flr (&(2 ** n) * R)) (A_seq n)) ⇒
    ∃(u_frozen_seq : num -> bool list).
      (∀n. LENGTH (u_frozen_seq n) = 2 ** n) ∧
      ((λn : num. real (block_error_prob_fixed W (2 ** n) (A_seq n) (u_frozen_seq n))) : num -> real) -->
      (0 : real)
Proof
  rpt strip_tac >>
  qspecl_then [‘W’, ‘R’] mp_tac theorem_3_polar_coding_fixed >>
  (impl_tac >- fs[]) >>
  disch_then (qx_choose_then ‘C’ strip_assume_tac) >>
  qabbrev_tac ‘u_frozen_seq : num -> bool list =
    λn. @u. LENGTH u = (2 ** n : num) ∧
            real (block_error_prob_fixed W (2 ** n) (A_seq n) u) ≤
            C * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’ >>
  ‘∀n. LENGTH (u_frozen_seq n) = (2 ** n : num) ∧
       real (block_error_prob_fixed W (2 ** n) (A_seq n) (u_frozen_seq n)) ≤
       C * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’
    by (qx_gen_tac ‘n’ >> simp[Abbr ‘u_frozen_seq’] >>
        SELECT_ELIM_TAC >> conj_tac
        >- (qpat_x_assum ‘∀n A. _ ⇒ ∃u_frozen. _’
              (qspecl_then [‘n’, ‘A_seq n’] mp_tac) >> fs[])
        >- simp[]) >>
  qexists_tac ‘u_frozen_seq’ >>
  conj_tac >- simp[] >>
  qspecl_then
    [‘λn : num. (0 : real)’,
     ‘λn : num. real (block_error_prob_fixed W (2 ** n) (A_seq n) (u_frozen_seq n))’,
     ‘λn : num. C * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’,
     ‘0 : real’]
    mp_tac seqTheory.SEQ_SANDWICH >>
  impl_tac
  >- (rpt conj_tac
      >- REWRITE_TAC[seqTheory.SEQ_CONST]
      >- (‘(0 : real) = C * 0’ by REAL_ARITH_TAC >>
          pop_assum SUBST1_TAC >>
          ho_match_mp_tac seqTheory.SEQ_MUL >>
          REWRITE_TAC[seqTheory.SEQ_CONST, inv_sqrt_sqrt_two_pow_tendsto_zero])
      >- (qx_gen_tac ‘n’ >>
          conj_tac
          >- simp[block_error_prob_nonneg]
          >- simp[]))
  >- simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Block 5: powr (-1 / 4), real_big_O, and End-to-End Existence Corollaries  *)
(* ------------------------------------------------------------------------- *)

(* Theorem 3 formulated with transcTheory.powr (-1 / 4).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_3_polar_coding_powr:
  ∀(W : (bool, β) memoryless_channel) (R : real).
    wf_bdmc W ∧ 0 ≤ R ∧ Normal R < symmetric_capacity W ⇒
    ∃(C : real).
      0 < C ∧
      ∀n A.
        is_polar_info_set W (2 ** n) (flr (&(2 ** n) * R)) A ⇒
        real (block_error_prob_avg W (2 ** n) A) ≤
        C * ((&(2 ** n) : real) powr (-1 / 4 : real))
Proof
  rpt strip_tac >>
  drule_all theorem_3_polar_coding >>
  disch_then (qx_choose_then ‘C’ strip_assume_tac) >>
  qexists_tac ‘C’ >> ASM_REWRITE_TAC[GSYM inv_sqrt_sqrt_eq_powr]
QED

(* Theorem 3 formulated via channel_polarizationTheory.real_big_O ((2^n)^{-1/4})
   (Arıkan Eq. 15: P_e(N, R) = O(N^{-1/4})).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_3_polar_coding_big_O:
  ∀(W : (bool, β) memoryless_channel) (R : real) (A_seq : num -> num -> bool).
    wf_bdmc W ∧ 0 ≤ R ∧ Normal R < symmetric_capacity W ∧
    (∀n. is_polar_info_set W (2 ** n) (flr (&(2 ** n) * R)) (A_seq n)) ⇒
    (λn. real (block_error_prob_avg W (2 ** n) (A_seq n))) ∈
      real_big_O (λn. (&(2 ** n) : real) powr (-1 / 4 : real))
Proof
  rpt strip_tac >>
  qspecl_then [‘W’, ‘R’] mp_tac theorem_3_polar_coding >>
  (impl_tac >- fs[]) >>
  disch_then (qx_choose_then ‘C’ strip_assume_tac) >>
  irule real_big_O_global_pos >>
  qexists_tac ‘C’ >> ASM_REWRITE_TAC[] >>
  qx_gen_tac ‘n’ >> rpt conj_tac
  >- simp[block_error_prob_nonneg]
  >- simp[GSYM inv_sqrt_sqrt_eq_powr, inv_sqrt_sqrt_two_pow_pos]
  >- (REWRITE_TAC[GSYM inv_sqrt_sqrt_eq_powr] >>
      qpat_x_assum ‘∀n A. _ ⇒ _’ (qspecl_then [‘n’, ‘A_seq n’] mp_tac) >>
      fs[])
QED

(* Self-contained existential Polar Coding Theorem: for any B-DMC W and fixed
   rate 0 ≤ R < I(W), constructively exhibits a sequence of polar information
   sets A_seq and deterministic frozen vectors u_frozen_seq achieving
   O((2^n)^{-1/4}) block error decay to 0 as n -> infty.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem theorem_3_polar_coding_canonical_exists:
  ∀(W : (bool, β) memoryless_channel) (R : real).
    wf_bdmc W ∧ 0 ≤ R ∧ Normal R < symmetric_capacity W ⇒
    ∃(C : real) (A_seq : num -> num -> bool) (u_frozen_seq : num -> bool list).
      0 < C ∧
      (∀n.
         is_polar_info_set W (2 ** n) (flr (&(2 ** n) * R)) (A_seq n) ∧
         LENGTH (u_frozen_seq n) = 2 ** n ∧
         real (block_error_prob_avg W (2 ** n) (A_seq n)) ≤
           C * inv (sqrt (sqrt (&(2 ** n)))) ∧
         real (block_error_prob_fixed W (2 ** n) (A_seq n) (u_frozen_seq n)) ≤
           C * inv (sqrt (sqrt (&(2 ** n))))) ∧
      ((λn : num. real (block_error_prob_avg W (2 ** n) (A_seq n))) : num -> real) -->
        (0 : real) ∧
      ((λn : num. real (block_error_prob_fixed W (2 ** n) (A_seq n) (u_frozen_seq n))) : num -> real) -->
        (0 : real)
Proof
  rpt strip_tac >>
  drule symmetric_capacity_bounds >> strip_tac >>
  ‘R < 1’ by (gvs[extreal_lt_eq] >> REAL_ASM_ARITH_TAC) >>
  ‘∀n. (flr ((&((2 ** n) : num) : real) * R) : num) ≤ ((2 ** n) : num)’
    by (gen_tac >>
        REWRITE_TAC[GSYM realTheory.REAL_OF_NUM_LE] >>
        irule realTheory.REAL_LE_TRANS >>
        qexists_tac ‘(&((2 ** n) : num) : real) * R’ >>
        conj_tac
        >- (irule (GEN_ALL realTheory.NUM_FLOOR_LE) >>
            irule realTheory.REAL_LE_MUL >> simp[])
        >- (irule realTheory.REAL_LE_TRANS >>
            qexists_tac ‘(&((2 ** n) : num) : real) * 1’ >>
            conj_tac
            >- (irule realTheory.REAL_LE_LMUL_IMP >>
                simp[] >> REAL_ASM_ARITH_TAC)
            >- REAL_ARITH_TAC)) >>
  qabbrev_tac ‘A_seq : num -> num -> bool =
    λn. polar_info_set W ((2 ** n) : num) (flr ((&((2 ** n) : num) : real) * R))’ >>
  ‘∀n. is_polar_info_set W ((2 ** n) : num) (flr ((&((2 ** n) : num) : real) * R)) (A_seq n)’
    by (qx_gen_tac ‘n’ >> simp[Abbr ‘A_seq’] >>
        irule is_polar_info_set_polar_info_set >> fs[]) >>
  qspecl_then [‘W’, ‘R’] mp_tac theorem_3_polar_coding >>
  (impl_tac >- simp[extreal_lt_eq]) >>
  disch_then (qx_choose_then ‘C1’ strip_assume_tac) >>
  qspecl_then [‘W’, ‘R’] mp_tac theorem_3_polar_coding_fixed >>
  (impl_tac >- simp[extreal_lt_eq]) >>
  disch_then (qx_choose_then ‘C2’ strip_assume_tac) >>
  qabbrev_tac ‘C : real = if C1 ≤ C2 then C2 else C1’ >>
  ‘0 < C ∧ C1 ≤ C ∧ C2 ≤ C’
    by (simp[Abbr ‘C’] >> REAL_ASM_ARITH_TAC) >>
  qabbrev_tac ‘u_frozen_seq : num -> bool list =
    λn. @u. LENGTH u = ((2 ** n) : num) ∧
            real (block_error_prob_fixed W ((2 ** n) : num) (A_seq n) u) ≤
            C2 * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’ >>
  ‘∀n. LENGTH (u_frozen_seq n) = ((2 ** n) : num) ∧
       real (block_error_prob_fixed W ((2 ** n) : num) (A_seq n) (u_frozen_seq n)) ≤
       C2 * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’
    by (qx_gen_tac ‘n’ >> simp[Abbr ‘u_frozen_seq’] >>
        SELECT_ELIM_TAC >> conj_tac
        >- (qpat_x_assum ‘∀n A. _ ⇒ ∃u_frozen. _’
              (qspecl_then [‘n’, ‘A_seq n’] mp_tac) >> fs[])
        >- simp[]) >>
  qexistsl_tac [‘C’, ‘A_seq’, ‘u_frozen_seq’] >>
  ‘∀n. C1 * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real))) ≤
         C * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real))) ∧
       C2 * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real))) ≤
         C * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’
    by (gen_tac >> conj_tac >> irule realTheory.REAL_LE_RMUL_IMP >>
        simp[inv_sqrt_sqrt_two_pow_pos]) >>
  rpt conj_tac
  >- ASM_REWRITE_TAC[]
  >- (qx_gen_tac ‘n’ >> ASM_REWRITE_TAC[] >> conj_tac
      >- (irule realTheory.REAL_LE_TRANS >>
          qexists_tac ‘C1 * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’ >>
          conj_tac
          >- (qpat_x_assum ‘∀n A. is_polar_info_set _ _ _ A ⇒ _’
                (qspecl_then [‘n’, ‘A_seq n’] mp_tac) >> fs[])
          >- ASM_REWRITE_TAC[])
      >- (irule realTheory.REAL_LE_TRANS >>
          qexists_tac ‘C2 * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’ >>
          ASM_REWRITE_TAC[]))
  >- (qspecl_then [‘W’, ‘R’, ‘A_seq’] mp_tac theorem_3_polar_coding_tendsto_zero >>
      fs[extreal_lt_eq])
  >- (qspecl_then
        [‘λn : num. (0 : real)’,
         ‘λn : num. real (block_error_prob_fixed W ((2 ** n) : num) (A_seq n) (u_frozen_seq n))’,
         ‘λn : num. C2 * inv (real$sqrt (real$sqrt (&((2 ** n) : num) : real)))’,
         ‘0 : real’]
        mp_tac seqTheory.SEQ_SANDWICH >>
      impl_tac
      >- (rpt conj_tac
          >- REWRITE_TAC[seqTheory.SEQ_CONST]
          >- (‘(0 : real) = C2 * 0’ by REAL_ARITH_TAC >>
              pop_assum SUBST1_TAC >>
              ho_match_mp_tac seqTheory.SEQ_MUL >>
              REWRITE_TAC[seqTheory.SEQ_CONST, inv_sqrt_sqrt_two_pow_tendsto_zero])
          >- (qx_gen_tac ‘n’ >> conj_tac
              >- simp[block_error_prob_nonneg]
              >- simp[]))
      >- simp[])
QED
