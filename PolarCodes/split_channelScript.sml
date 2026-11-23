(* ========================================================================= *)
(*   Split-channel well-formedness, abstract lifting, single-step polar      *)
(*   channel transformation, and Proposition 3 of Arıkan (arXiv:0807.3917).  *)
(*                                                                           *)
(*   Original split_channel0_def, mcdomain0_split_channel0, and              *)
(*   mcchannel0_split_channel0 by Eric Hall (preserved byte-for-byte).       *)
(*   Edited and extended by Gemini (Google DeepMind AI agent): expanded      *)
(*   Ancestors for B-DMC and measure/sigma-algebra lemmas, removed           *)
(*   commented-out draft stubs, proved wf_memoryless_channel_split_channel0, *)
(*   defined split_channel and single_step_polar, and proved                 *)
(*   wf_bdmc_split_channel, mcchannel_split_channel_singleton, root N = 1    *)
(*   identities, adjacent marginalization, and Proposition 3.                *)
(* ========================================================================= *)

Theory split_channel

Ancestors
  arithmetic bdmc bhattacharyya bitstring bxor_lemmas capacity
  combine_channel ecc_prob_space extreal extreal_information
  fundamental interleave jared_yeager_prod_list lebesgue lifting list
  martingale measure memoryless_channel pair polar_encode pred_set
  probability real real_sigma rich_list sigma_algebra transfer

Libs dep_rewrite hurdUtils realLib;

val _ = hide "W";
val _ = hide "S";

(* -------------------------------------------------------------------------- *)
(* Based on "Channel polarization: A method for constructing                  *)
(* capacity-achieving codes for symmetric binary-input memoryless channels    *)
(* by Erdal Arıkan                                                            *)
(*                                                                            *)
(* Based on "Polar Codes: from theory to practice" by Mohammad Rowshan and    *)
(* Emanuele Viterbo                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* The split channel step in Polar Coding                                     *)
(*                                                                            *)
(* Not produced through straightforward operations on simpler channels so we  *)
(* need to define it using the underlying representation type.                *)
(*                                                                            *)
(* Initial channel input: bool                                                *)
(* Initial channel output: β                                                  *)
(*                                                                            *)
(* Split channel input: bool                                                  *)
(* Split channel output: β list # bool list                                   *)
(*                                                                            *)
(* Channel is a (domain, transition function) pair.                           *)
(*                                                                            *)
(* Split channel domain: {T;F}                                                *)
(* Split channel transition function:                                         *)
(* - Takes the current input bit                                              *)
(* - Returns a probability distribution over the outputs and the prior inputs *)
(* - Averages over the future inputs.                                         *)
(*                                                                            *)
(* We use the fact that the input channel's domain is finite (as we take      *)
(* bools as input, so that we may use the power set of the domain as the      *)
(* sigma algebra.                                                             *)
(*                                                                            *)
(* We assume that the output's sigma algebra includes any singleton set       *)
(* containing an output, so that we may determine the probability of any      *)
(* individual output.                                                         *)
(*                                                                            *)
(* Inputs:                                                                    *)
(* - W: the underlying channel                                                *)
(* - num_inputs: the combined channel size N                                  *)
(* - i: the index of the current split channel                                *)
(* -------------------------------------------------------------------------- *)
Definition split_channel0_def:
  split_channel0 (W : (bool, β) memoryless_channel)
  (num_inputs : num) (i : num) =
    (𝕌(:bool),
     (sigma_list (REPLICATE num_inputs (mccodomain W, mcevents W))
                 × sigma_list (REPLICATE i (mcdomain W, POW (mcdomain W)))
     )
     : (β list # bool list) algebra,
     λcurrent_chosen_value.
       EXTREAL_SUM_IMAGE
       (λ(output, prior_chosen_values).
          EXTREAL_SUM_IMAGE
          (λlater_chosen_values.
             (1 / 2 pow (num_inputs - 1)) *
             (mcchannel (combine_channel W num_inputs)
                        (prior_chosen_values ++ [current_chosen_value] ++
                         later_chosen_values)
                        {output}
          )
       ) (cross_list (REPLICATE (num_inputs - i - 1) (mcdomain W)))
       ) : (β list # bool list) measure
    ) : (bool -> bool)
        # ((β list # bool list) algebra)
        # (bool -> (β list # bool list) measure)
End

Theorem mcdomain0_split_channel0[simp]:
  ∀W : (bool,β) memoryless_channel n i.
    mcdomain0 (split_channel0 W n i) = {T;F}
Proof
  rpt gen_tac
  >> simp[split_channel0_def, mcdomain0_def]
  >> qmatch_abbrev_tac ‘FST (_ argument) = _’
  >> Cases_on ‘argument’
  >> simp[]
QED

Theorem mcchannel0_split_channel0:
  ∀W n i.
    mcchannel0 (split_channel0 W n i) =
    λcurrent_chosen_value.
      EXTREAL_SUM_IMAGE
      (λ(output, prior_chosen_values).
         EXTREAL_SUM_IMAGE
         (λlater_chosen_values.
            (1 / 2 pow (n - 1)) *
            (mcchannel (combine_channel W n)
                       (prior_chosen_values ++ [current_chosen_value] ++
                        later_chosen_values)
                       {output}
            )
         ) (cross_list (REPLICATE (n - i - 1) (mcdomain W)))
      ) : (β list # bool list) measure
Proof
  rpt gen_tac
  >> simp[mcchannel0_def, split_channel0_def]
QED

(* -------------------------------------------------------------------------- *)
(* Block 1: Finite Powerset Product Sigma-Algebras & Representation Collapse  *)
(* -------------------------------------------------------------------------- *)

(* Finiteness of cross_list when every component set is finite.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem FINITE_cross_list:
  ∀(ds : (α -> bool) list). EVERY FINITE ds ⇒ FINITE (cross_list ds)
Proof
  simp[finite_cross_list]
QED

(* Base case of length_n_codes at length 0.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem length_n_codes_0[simp]:
  length_n_codes 0 = {[]}
Proof
  rw[Once EXTENSION] >> Cases_on ‘x’ >> simp[]
QED

(* Full algebra equality for prod_sigma of two finite powerset sigma-algebras.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem prod_sigma_POW_eq:
  ∀(A : α -> bool) (B : γ -> bool).
    FINITE A ∧ FINITE B ⇒
    (((A, POW A) × (B, POW B)) : (α # γ) algebra) = (A × B, POW (A × B))
Proof
  rw[ALGEBRA_CONG_ALT, SPACE_PROD_SIGMA, prod_sigma_POW]
QED

(* Specialization of cross_list (REPLICATE k {T; F}) to length_n_codes k
   after UNIV_BOOL normalization.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem cross_list_replicate_bool[local]:
  ∀k. cross_list (REPLICATE k {T; F}) = length_n_codes k
Proof
  gen_tac >>
  PURE_REWRITE_TAC[GSYM UNIV_BOOL, cross_list_replicate_univ_bool] >>
  REFL_TAC
QED

(* Exact powerset sigma-algebra collapse of mcsigma0 (split_channel0 W N i)
   for any well-formed B-DMC W.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcsigma0_split_channel0_bdmc:
  ∀(W : (bool, β) memoryless_channel) N i.
    wf_bdmc W ⇒
    mcsigma0 (split_channel0 W N i) =
      (cross_list (REPLICATE N (mccodomain W)) × length_n_codes i,
       POW (cross_list (REPLICATE N (mccodomain W)) × length_n_codes i))
Proof
  rw[wf_bdmc_def, split_channel0_def, mcsigma0_def] >>
  DEP_REWRITE_TAC[sigma_list_replicate_pow, prod_sigma_POW_eq] >>
  simp[finite_cross_list_replicate, cross_list_replicate_bool]
QED

(* -------------------------------------------------------------------------- *)
(* Block 2: Power-of-Two Arithmetic & Well-Formedness of split_channel0       *)
(* -------------------------------------------------------------------------- *)

(* Normalization of 2 ** k and 1 / 2 pow k across num, real, and extreal.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem extreal_two_pow_props[local]:
  ∀k. (&(2 ** k) : real) = (2 : real) pow k ∧
      (0 : real) < (2 : real) pow k ∧
      (2 : real) pow k ≠ 0 ∧
      0 ≤ (1 / (2 : real) pow k) ∧
      ((2 : extreal) pow k = Normal ((2 : real) pow k)) ∧
      (((1 / 2 pow k) : extreal) = Normal (1 / (2 : real) pow k)) ∧
      ((0 : extreal) ≤ 1 / 2 pow k) ∧
      (&(2 ** k) : real) * (1 / (2 : real) pow k) = 1
Proof
  gen_tac >>
  ‘(&(2 ** k) : real) = (2 : real) pow k’
    by simp[GSYM REAL_OF_NUM_POW] >>
  ‘(0 : real) < (2 : real) pow k’
    by (irule REAL_POW_LT >> REAL_ARITH_TAC) >>
  ‘(2 : real) pow k ≠ 0’ by REAL_ASM_ARITH_TAC >>
  ‘0 ≤ (1 / (2 : real) pow k)’
    by (simp[real_div, REAL_LE_INV_EQ] >> REAL_ASM_ARITH_TAC) >>
  simp[extreal_of_num_def, extreal_pow_def, extreal_div_eq, extreal_le_eq,
       real_div, REAL_MUL_RINV]
QED

(* Real exponent doubling identity 1 / 2^(2N - 1) = (1/2) * (1 / 2^(N - 1))^2.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem real_inv_two_pow_double[local]:
  ∀N. 0n < N ⇒
      (1 / (2 : real) pow (2 * N - 1)) =
        (1 / 2) * (1 / (2 : real) pow (N - 1)) * (1 / (2 : real) pow (N - 1))
Proof
  rpt strip_tac >>
  ‘2 * N - 1 = SUC ((N - 1) + (N - 1))’ by decide_tac >>
  pop_assum SUBST1_TAC >>
  ‘(2 : real) ≠ 0 ∧ (2 : real) pow (N - 1) ≠ 0’
    by simp[extreal_two_pow_props] >>
  simp[pow, POW_ADD, real_div, REAL_INV_MUL, REAL_MUL_ASSOC]
QED

(* Constant-summand collapse for REAL_SUM_IMAGE over a finite set.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_EQ_CONST[local]:
  ∀s (f : α -> real) c.
    FINITE s ∧ (∀x. x ∈ s ⇒ f x = c) ⇒
    REAL_SUM_IMAGE f s = &(CARD s) * c
Proof
  rpt strip_tac >>
  ‘REAL_SUM_IMAGE f s = REAL_SUM_IMAGE (λx. c) s’
    by (irule REAL_SUM_IMAGE_EQ >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule REAL_SUM_IMAGE_FINITE_CONST >> simp[]
QED

(* Real-valued singleton PMF sum-to-one property for combine_channel W N.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem combine_channel_real_pmf_sum_1[local]:
  ∀(W : (bool, β) memoryless_channel) N u.
    wf_bdmc W ∧ LENGTH u = N ⇒
    REAL_SUM_IMAGE
      (λy. real (mcchannel (combine_channel W N) u {y}))
      (cross_list (REPLICATE N (mccodomain W))) = 1
Proof
  rpt strip_tac >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  drule_all prob_space_combine_channel >> strip_tac >>
  drule PROB_EXTREAL_SUM_IMAGE_SPACE >>
  simp[p_space_def, m_space_def, events_def, measurable_sets_def,
       prob_def, measure_def, IN_POW, SUBSET_DEF] >>
  qpat_x_assum ‘Abbrev (Y_N = _)’
    (fn th => assume_tac th >> mp_tac (REWRITE_RULE [markerTheory.Abbrev_def] th)) >>
  disch_then (fn eq => simp[GSYM eq]) >>
  Know ‘∑ (λx. mcchannel (combine_channel W N) u {x}) Y_N =
        ∑ (λx. Normal (real (mcchannel (combine_channel W N) u {x}))) Y_N’
  >- (irule EXTREAL_SUM_IMAGE_EQ' >>
      simp[Abbr ‘Y_N’, in_cross_list_replicate] >>
      qx_gen_tac ‘y’ >> strip_tac >>
      drule_all mcchannel_combine_channel_singleton_normal_gen >>
      strip_tac >> simp[]) >>
  disch_then SUBST1_TAC >>
  simp[EXTREAL_SUM_IMAGE_NORMAL, extreal_of_num_def, Abbr ‘Y_N’]
QED

(* General well-formedness of split_channel0 W N i for any wf_bdmc W and i < N.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_memoryless_channel_split_channel0_gen:
  ∀(W : (bool, β) memoryless_channel) N i.
    wf_bdmc W ∧ i < N ⇒
    wf_memoryless_channel (split_channel0 W N i)
Proof
  rpt strip_tac >>
  ho_match_mp_tac wf_memoryless_channel_nonempty >>
  conj_tac >- simp[mcdomain0_split_channel0] >>
  qx_gen_tac ‘b’ >> disch_then kall_tac >>
  drule mcsigma0_split_channel0_bdmc >>
  disch_then (qspecl_then [‘N’, ‘i’] assume_tac) >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  qabbrev_tac ‘U_prev = length_n_codes i’ >>
  qabbrev_tac ‘U_later = length_n_codes (N - (i + 1))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  ‘FINITE U_prev ∧ FINITE U_later’ by simp[Abbr ‘U_prev’, Abbr ‘U_later’] >>
  ‘mcprob_space0 (split_channel0 W N i) b =
   (Y_N × U_prev, POW (Y_N × U_prev), mcchannel0 (split_channel0 W N i) b)’
    by simp[mcprob_space0_def, mccodomain0_def, mcevents0_def] >>
  pop_assum SUBST1_TAC >>
  DEP_REWRITE_TAC[prob_on_finite_set] >>
  simp[FINITE_CROSS, p_space_def, m_space_def, measurable_sets_def,
       prob_def, measure_def] >>
  ‘mcdomain W = 𝕌(:bool)’ by fs[wf_bdmc_def] >>
  simp[mcchannel0_split_channel0, cross_list_replicate_bool] >>
  qpat_x_assum ‘Abbrev (U_later = _)’
    (fn th => assume_tac th >> mp_tac (REWRITE_RULE [markerTheory.Abbrev_def] th)) >>
  disch_then (fn eq => PURE_REWRITE_TAC[GSYM eq]) >>
  qabbrev_tac
    ‘g = λ(output : β list, prior_chosen_values : bool list).
           ∑ (λlater_chosen_values.
                (1 / 2 pow (N - 1)) *
                mcchannel (combine_channel W N)
                  (prior_chosen_values ++ [b] ++ later_chosen_values)
                  {output})
             U_later’ >>
  ‘∀z. 0 ≤ g z ∧ g z ≠ −∞’
    by (Cases >> simp[Abbr ‘g’] >>
        conj_tac >> TRY (irule pos_not_neginf) >>
        irule EXTREAL_SUM_IMAGE_POS >> simp[Abbr ‘U_later’] >>
        rw[] >> irule le_mul >>
        simp[extreal_two_pow_props, mcchannel_combine_channel_pos]) >>
  rpt conj_tac
  >- (simp[positive_def, measure_def, measurable_sets_def, IN_POW,
           EXTREAL_SUM_IMAGE_EMPTY] >>
      qx_gen_tac ‘s’ >> strip_tac >>
      irule EXTREAL_SUM_IMAGE_POS >> simp[] >>
      irule SUBSET_FINITE >> qexists_tac ‘Y_N × U_prev’ >> simp[FINITE_CROSS])
  >- (Know
        ‘∑ g (Y_N × U_prev) =
         ∑ (λz. Normal
                  (REAL_SUM_IMAGE
                     (λu_lat.
                        (1 / (2 : real) pow (N - 1)) *
                        real (mcchannel (combine_channel W N)
                                (SND z ++ [b] ++ u_lat) {FST z}))
                     U_later))
           (Y_N × U_prev)’
      >- (irule EXTREAL_SUM_IMAGE_EQ' >> simp[FINITE_CROSS] >>
          Cases >> simp[Abbr ‘g’, Abbr ‘U_prev’, in_cross_list_replicate, Abbr ‘Y_N’] >>
          strip_tac >>
          Know
            ‘∑ (λu_lat.
                  (1 / 2 pow (N - 1)) *
                  mcchannel (combine_channel W N) (r ++ [b] ++ u_lat) {q})
               U_later =
             ∑ (λu_lat.
                  Normal
                    ((1 / (2 : real) pow (N - 1)) *
                     real (mcchannel (combine_channel W N)
                             (r ++ [b] ++ u_lat) {q})))
               U_later’
          >- (irule EXTREAL_SUM_IMAGE_EQ' >> simp[Abbr ‘U_later’] >>
              qx_gen_tac ‘u_lat’ >> simp[] >> strip_tac >>
              ‘LENGTH (r ++ [b] ++ u_lat) = N’ by simp[] >>
              drule_all mcchannel_combine_channel_singleton_normal_gen >>
              strip_tac >>
              simp[extreal_two_pow_props, extreal_mul_eq]) >>
          disch_then SUBST1_TAC >>
          simp[EXTREAL_SUM_IMAGE_NORMAL]) >>
      disch_then SUBST1_TAC >>
      simp[FINITE_CROSS, EXTREAL_SUM_IMAGE_NORMAL, extreal_of_num_def] >>
      simp[GSYM REAL_SUM_IMAGE_REAL_SUM_IMAGE] >>
      DEP_ONCE_REWRITE_TAC[NESTED_REAL_SUM_IMAGE_REVERSE] >> simp[] >>
      ‘(&(CARD U_prev) : real) * (&(CARD U_later) * (1 / (2 : real) pow (N - 1))) = 1’
        by (simp[Abbr ‘U_prev’, Abbr ‘U_later’, REAL_MUL_ASSOC] >>
            ‘2n ** i * 2n ** (N - (i + 1)) = 2n ** (N - 1)’
              by (PURE_ONCE_REWRITE_TAC[GSYM EXP_ADD] >>
                  AP_TERM_TAC >> decide_tac) >>
            pop_assum SUBST1_TAC >>
            simp[GSYM REAL_OF_NUM_POW, extreal_two_pow_props]) >>
      pop_assum (CONV_TAC o RHS_CONV o K o SYM) >>
      ho_match_mp_tac REAL_SUM_IMAGE_EQ_CONST >> conj_tac >- simp[] >>
      qx_gen_tac ‘u_prev’ >> strip_tac >>
      DEP_ONCE_REWRITE_TAC[NESTED_REAL_SUM_IMAGE_REVERSE] >>
      conj_tac >- simp[] >>
      ho_match_mp_tac REAL_SUM_IMAGE_EQ_CONST >> conj_tac >- simp[] >>
      qx_gen_tac ‘u_lat’ >> strip_tac >>
      ‘(λz. real (mcchannel (combine_channel W N)
                    (u_prev ++ [b] ++ u_lat) {z}) *
            ((2 : real) pow (N - 1))⁻¹) =
       (λz. ((2 : real) pow (N - 1))⁻¹ *
            real (mcchannel (combine_channel W N)
                    (u_prev ++ [b] ++ u_lat) {z}))’
        by simp[FUN_EQ_THM, REAL_MUL_COMM] >>
      pop_assum SUBST1_TAC >>
      DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_CMUL] >>
      conj_tac >- simp[] >>
      ‘LENGTH (u_prev ++ [b] ++ u_lat) = N’
        by (qpat_x_assum ‘u_prev ∈ U_prev’ mp_tac >>
            qpat_x_assum ‘u_lat ∈ U_later’ mp_tac >>
            simp[Abbr ‘U_prev’, Abbr ‘U_later’]) >>
      drule_all combine_channel_real_pmf_sum_1 >>
      qpat_x_assum ‘Abbrev (Y_N = _)’
        (fn th => mp_tac (REWRITE_RULE [markerTheory.Abbrev_def] th)) >>
      disch_then (fn eq => PURE_REWRITE_TAC[GSYM eq]) >>
      disch_then SUBST1_TAC >>
      simp[real_div])
  >- (simp[additive_def, measure_def, measurable_sets_def, IN_POW] >>
      qx_genl_tac [‘s’, ‘t’] >> strip_tac >>
      ‘FINITE s ∧ FINITE t’
        by (conj_tac >> irule SUBSET_FINITE >>
            qexists_tac ‘Y_N × U_prev’ >> simp[FINITE_CROSS]) >>
      irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> simp[])
QED

(* Contract theorem: split_channel0 W (2 ** n) i is a well-formed memoryless
   channel whenever wf_bdmc W and i < 2 ** n.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_memoryless_channel_split_channel0:
  ∀(W : (bool, β) memoryless_channel) n i.
    wf_bdmc W ∧ i < 2 ** n ⇒
    wf_memoryless_channel (split_channel0 W (2 ** n) i)
Proof
  rw[wf_memoryless_channel_split_channel0_gen]
QED

(* -------------------------------------------------------------------------- *)
(* Block 3: Abstract split_channel, Accessors, Singleton Eq. (5) & Base N = 1 *)
(* -------------------------------------------------------------------------- *)

(* Abstract coordinate split channel W_N^(i) lifted via memoryless_channel_ABS.
   Written by Gemini (Google DeepMind AI agent) *)
Definition split_channel_def:
  split_channel (W : (bool, β) memoryless_channel) (num_inputs : num) (i : num)
    : (bool, β list # bool list) memoryless_channel =
    memoryless_channel_ABS (split_channel0 W num_inputs i)
End

(* Combined lifted accessors of split_channel W N i under wf_bdmc W and i < N.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem split_channel_accessors_gen:
  ∀(W : (bool, β) memoryless_channel) N i.
    wf_bdmc W ∧ i < N ⇒
    mcdomain (split_channel W N i) = 𝕌(:bool) ∧
    mcsigma (split_channel W N i) =
      (cross_list (REPLICATE N (mccodomain W)) × length_n_codes i,
       POW (cross_list (REPLICATE N (mccodomain W)) × length_n_codes i)) ∧
    mccodomain (split_channel W N i) =
      cross_list (REPLICATE N (mccodomain W)) × length_n_codes i ∧
    mcevents (split_channel W N i) =
      POW (cross_list (REPLICATE N (mccodomain W)) × length_n_codes i) ∧
    mcchannel (split_channel W N i) = mcchannel0 (split_channel0 W N i)
Proof
  rpt strip_tac >>
  drule_all wf_memoryless_channel_split_channel0_gen >> strip_tac >>
  drule mcsigma0_split_channel0_bdmc >>
  disch_then (qspecl_then [‘N’, ‘i’] assume_tac) >>
  simp[split_channel_def, memoryless_channel_ABS_accessors,
       mccodomain0_def, mcevents0_def] >>
  rw[Once EXTENSION] >> Cases_on ‘x’ >> simp[]
QED

(* Domain of split_channel W N i under wf_bdmc W and i < N.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcdomain_split_channel:
  ∀(W : (bool, β) memoryless_channel) N i.
    wf_bdmc W ∧ i < N ⇒
    mcdomain (split_channel W N i) = 𝕌(:bool)
Proof
  rw[split_channel_accessors_gen]
QED

(* Output alphabet (codomain) of split_channel W N i under wf_bdmc W and i < N.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mccodomain_split_channel:
  ∀(W : (bool, β) memoryless_channel) N i.
    wf_bdmc W ∧ i < N ⇒
    mccodomain (split_channel W N i) =
      cross_list (REPLICATE N (mccodomain W)) × length_n_codes i
Proof
  rw[split_channel_accessors_gen]
QED

(* Event sigma-algebra subsets of split_channel W N i under wf_bdmc W and i < N.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcevents_split_channel:
  ∀(W : (bool, β) memoryless_channel) N i.
    wf_bdmc W ∧ i < N ⇒
    mcevents (split_channel W N i) =
      POW (cross_list (REPLICATE N (mccodomain W)) × length_n_codes i)
Proof
  rw[split_channel_accessors_gen]
QED

(* Explicit pair-membership characterization of mccodomain (split_channel W N i).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mccodomain_split_channel_alt:
  ∀(W : (bool, β) memoryless_channel) N i y u_prev.
    wf_bdmc W ∧ i < N ⇒
    ((y, u_prev) ∈ mccodomain (split_channel W N i) ⇔
     LENGTH y = N ∧ EVERY (λyi. yi ∈ mccodomain W) y ∧ LENGTH u_prev = i)
Proof
  simp[split_channel_accessors_gen, in_cross_list_replicate, CONJ_ASSOC]
QED

(* General B-DMC preservation of split_channel W N i for i < N.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_split_channel_gen:
  ∀(W : (bool, β) memoryless_channel) N i.
    wf_bdmc W ∧ i < N ⇒ wf_bdmc (split_channel W N i)
Proof
  rpt strip_tac >>
  drule_all split_channel_accessors_gen >> strip_tac >>
  fs[wf_bdmc_def, FINITE_CROSS, finite_cross_list_replicate]
QED

(* Contract theorem: split_channel W (2 ** n) i is a well-formed B-DMC.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_split_channel:
  ∀(W : (bool, β) memoryless_channel) n i.
    wf_bdmc W ∧ i < 2 ** n ⇒ wf_bdmc (split_channel W (2 ** n) i)
Proof
  rw[wf_bdmc_split_channel_gen]
QED

(* General Eq. (5) singleton transition probability formula for split_channel W N i
   without side conditions on (y, u_prev).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_split_channel_singleton_gen:
  ∀(W : (bool, β) memoryless_channel) N i u_i y u_prev.
    wf_bdmc W ∧ i < N ⇒
    mcchannel (split_channel W N i) u_i {(y, u_prev)} =
      (1 / 2 pow (N - 1)) *
      ∑ (λu_later.
           mcchannel (combine_channel W N)
                     (u_prev ++ [u_i] ++ u_later)
                     {y})
        (length_n_codes (N - i - 1))
Proof
  rpt strip_tac >>
  drule_all split_channel_accessors_gen >> strip_tac >>
  ‘mcdomain W = 𝕌(:bool)’ by fs[wf_bdmc_def] >>
  simp[mcchannel0_split_channel0, cross_list_replicate_bool,
       extreal_two_pow_props] >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_CMUL] >>
  simp[] >> disj1_tac >> rw[] >>
  irule pos_not_neginf >> simp[mcchannel_combine_channel_pos]
QED

(* Unconditional power-of-two Eq. (5) singleton transition formula.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_split_channel_singleton_uncond:
  ∀(W : (bool, β) memoryless_channel) n i u_i y u_prev.
    wf_bdmc W ∧ i < 2 ** n ⇒
    mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)} =
      (1 / 2 pow (2 ** n - 1)) *
      ∑ (λu_later.
           mcchannel (combine_channel W (2 ** n))
                     (u_prev ++ [u_i] ++ u_later)
                     {y})
        (length_n_codes (2 ** n - i - 1))
Proof
  rw[mcchannel_split_channel_singleton_gen]
QED

(* Contract theorem (Arıkan Eq. 5): singleton transition probability formula for
   split_channel W (2 ** n) i on valid output/history pairs (y, u_prev).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_split_channel_singleton:
  ∀(W : (bool, β) memoryless_channel) n i u_i y u_prev.
    wf_bdmc W ∧ i < 2 ** n ∧
    LENGTH y = 2 ** n ∧ EVERY (λyi. yi ∈ mccodomain W) y ∧
    LENGTH u_prev = i ⇒
    mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)} =
      (1 / 2 pow (2 ** n - 1)) *
      ∑ (λu_fut.
           mcchannel (combine_channel W (2 ** n))
                     (u_prev ++ [u_i] ++ u_fut)
                     {y})
        (length_n_codes (2 ** n - i - 1))
Proof
  rw[mcchannel_split_channel_singleton_gen]
QED

(* Real-valued Normal representation of split_channel W N i singleton transitions.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_split_channel_singleton_real:
  ∀(W : (bool, β) memoryless_channel) N i u_i y u_prev.
    wf_bdmc W ∧ i < N ∧
    LENGTH y = N ∧ EVERY (λyi. yi ∈ mccodomain W) y ∧
    LENGTH u_prev = i ⇒
    mcchannel (split_channel W N i) u_i {(y, u_prev)} =
      Normal
        ((1 / (2 : real) pow (N - 1)) *
         REAL_SUM_IMAGE
           (λu_later.
              real (mcchannel (combine_channel W N)
                              (u_prev ++ [u_i] ++ u_later) {y}))
           (length_n_codes (N - i - 1)))
Proof
  rpt strip_tac >>
  drule_all mcchannel_split_channel_singleton_gen >>
  disch_then (qspecl_then [‘u_i’, ‘y’, ‘u_prev’] SUBST1_TAC) >>
  Know
    ‘∑ (λu_later.
          mcchannel (combine_channel W N) (u_prev ++ [u_i] ++ u_later) {y})
       (length_n_codes (N - i - 1)) =
     ∑ (λu_later.
          Normal (real (mcchannel (combine_channel W N)
                                  (u_prev ++ [u_i] ++ u_later) {y})))
       (length_n_codes (N - i - 1))’
  >- (irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
      qx_gen_tac ‘u_later’ >> simp[] >> strip_tac >>
      ‘LENGTH (u_prev ++ [u_i] ++ u_later) = N’ by simp[] >>
      drule_all mcchannel_combine_channel_singleton_normal_gen >>
      strip_tac >> simp[]) >>
  disch_then SUBST1_TAC >>
  simp[EXTREAL_SUM_IMAGE_NORMAL, extreal_two_pow_props, extreal_mul_eq]
QED

(* Singleton transition probabilities of split_channel W (2 ** n) i lie in [0, 1]
   and are Normal.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_split_channel_singleton_normal:
  ∀(W : (bool, β) memoryless_channel) n i u_i y u_prev.
    wf_bdmc W ∧ i < 2 ** n ∧
    LENGTH y = 2 ** n ∧ EVERY (λyi. yi ∈ mccodomain W) y ∧
    LENGTH u_prev = i ⇒
    0 ≤ mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)} ∧
    mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)} ≤ 1 ∧
    ∃r. 0 ≤ r ∧ r ≤ 1 ∧
        mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)} = Normal r
Proof
  rpt strip_tac >>
  drule_all wf_bdmc_split_channel >> strip_tac >>
  ‘(y, u_prev) ∈ mccodomain (split_channel W (2 ** n) i)’
    by simp[mccodomain_split_channel_alt] >>
  drule_all wf_bdmc_mcchannel_singleton_normal >>
  disch_then (qspec_then ‘u_i’ strip_assume_tac) >>
  simp[] >> qexists_tac ‘r’ >> simp[]
QED

(* Exact marginalization identity between adjacent split channels j and j + 1:
   W_N^[j](y, u_prev | b0) = W_N^[j+1](y, u_prev ++ [b0] | F) +
                             W_N^[j+1](y, u_prev ++ [b0] | T).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_split_channel_marginalize:
  ∀(W : (bool, β) memoryless_channel) N j b0 y u_prev.
    wf_bdmc W ∧ j + 1 < N ⇒
    mcchannel (split_channel W N j) b0 {(y, u_prev)} =
      mcchannel (split_channel W N (j + 1)) F {(y, u_prev ++ [b0])} +
      mcchannel (split_channel W N (j + 1)) T {(y, u_prev ++ [b0])}
Proof
  rpt strip_tac >>
  ‘j < N’ by decide_tac >>
  simp[mcchannel_split_channel_singleton_gen] >>
  qabbrev_tac ‘m = N - (j + 2)’ >>
  ‘N - (j + 1) = SUC m’ by (simp[Abbr ‘m’] >> decide_tac) >>
  pop_assum SUBST1_TAC >>
  ‘length_n_codes (SUC m) =
   IMAGE (CONS F) (length_n_codes m) ∪ IMAGE (CONS T) (length_n_codes m)’
    by (rw[Once EXTENSION] >> Cases_on ‘x’ >> simp[] >> Cases_on ‘h’ >> simp[]) >>
  ‘DISJOINT (IMAGE (CONS F) (length_n_codes m))
            (IMAGE (CONS T) (length_n_codes m))’
    by rw[DISJOINT_ALT] >>
  pop_assum mp_tac >> pop_assum SUBST1_TAC >> strip_tac >>
  DEP_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_DISJOINT_UNION] >>
  conj_tac
  >- (simp[] >> disj1_tac >> rw[] >> irule pos_not_neginf >>
      simp[mcchannel_combine_channel_pos]) >>
  DEP_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_IMAGE] >>
  conj_tac
  >- (simp[INJ_DEF] >> disj1_tac >> rw[] >> irule pos_not_neginf >>
      simp[mcchannel_combine_channel_pos]) >>
  DEP_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_IMAGE] >>
  conj_tac
  >- (simp[INJ_DEF] >> disj1_tac >> rw[] >> irule pos_not_neginf >>
      simp[mcchannel_combine_channel_pos]) >>
  simp[combinTheory.o_DEF, extreal_two_pow_props, Abbr ‘m’] >>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  irule add_ldistrib_normal >>
  disj2_tac >> conj_tac >> irule pos_not_neginf >>
  irule EXTREAL_SUM_IMAGE_POS >> simp[mcchannel_combine_channel_pos]
QED

(* Base N = 1 (n = 0, i = 0) split channel codomain characterization.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mccodomain_split_channel_1_0:
  ∀(W : (bool, β) memoryless_channel).
    wf_bdmc W ⇒
    mccodomain (split_channel W 1 0) =
      IMAGE (λy. ([y], [] : bool list)) (mccodomain W)
Proof
  rpt strip_tac >>
  ‘0n < 1’ by decide_tac >>
  drule_all mccodomain_split_channel >> simp[] >> disch_then kall_tac >>
  rw[Once EXTENSION, in_cross_list_replicate] >>
  Cases_on ‘x’ >> simp[] >>
  Cases_on ‘q’ >> simp[] >>
  Cases_on ‘t’ >> simp[] >>
  metis_tac[]
QED

(* Base N = 1 (n = 0, i = 0) split channel singleton transition identity.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_split_channel_1_0:
  ∀(W : (bool, β) memoryless_channel) u0 y.
    wf_bdmc W ∧ y ∈ mccodomain W ⇒
    mcchannel (split_channel W 1 0) u0 {([y], [])} = mcchannel W u0 {y}
Proof
  rpt strip_tac >>
  qspecl_then [‘W’, ‘0’, ‘0’, ‘u0’, ‘[y]’, ‘[]’] mp_tac
    mcchannel_split_channel_singleton >>
  simp[] >> disch_then kall_tac >>
  qspecl_then [‘W’, ‘0’, ‘[u0]’, ‘[y]’] mp_tac
    mcchannel_combine_channel_singleton >>
  ‘count 1 = {0}’ by (rw[Once EXTENSION] >> decide_tac) >>
  simp[Once polar_encode_def]
QED

(* Output-alphabet bijection between W and split_channel W 1 0.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bdmc_output_bij_split_channel_1_0:
  ∀(W : (bool, β) memoryless_channel).
    wf_bdmc W ⇒
    bdmc_output_bij (λy. ([y], [] : bool list)) W (split_channel W 1 0)
Proof
  rpt strip_tac >>
  simp[bdmc_output_bij_def] >>
  ‘0n < 1’ by decide_tac >>
  simp[wf_bdmc_split_channel_gen, mcchannel_split_channel_1_0,
       mccodomain_split_channel_1_0] >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  metis_tac[]
QED

(* Base N = 1 Bhattacharyya parameter identity Z(W_1^(0)) = Z(W).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bhattacharyya_split_channel_1_0:
  ∀(W : (bool, β) memoryless_channel).
    wf_bdmc W ⇒ bhattacharyya (split_channel W 1 0) = bhattacharyya W
Proof
  rpt strip_tac >>
  drule bdmc_output_bij_split_channel_1_0 >> strip_tac >>
  drule bdmc_output_bij_invariance >> simp[]
QED

(* Base N = 1 symmetric capacity identity I(W_1^(0)) = I(W).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem symmetric_capacity_split_channel_1_0:
  ∀(W : (bool, β) memoryless_channel).
    wf_bdmc W ⇒ symmetric_capacity (split_channel W 1 0) = symmetric_capacity W
Proof
  rpt strip_tac >>
  drule bdmc_output_bij_split_channel_1_0 >> strip_tac >>
  drule bdmc_output_bij_invariance >> simp[]
QED

(* Base N = 1 BEC predicate equivalence is_bec (W_1^(0)) <=> is_bec W.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_bec_split_channel_1_0:
  ∀(W : (bool, β) memoryless_channel).
    wf_bdmc W ⇒ (is_bec (split_channel W 1 0) ⇔ is_bec W)
Proof
  rpt strip_tac >>
  drule bdmc_output_bij_split_channel_1_0 >> strip_tac >>
  drule bdmc_output_bij_invariance >> simp[]
QED

(* Base N = 1 erasure probability identity bec_erasure_prob (W_1^(0)) = bec_erasure_prob W.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_erasure_prob_split_channel_1_0:
  ∀(W : (bool, β) memoryless_channel).
    wf_bdmc W ⇒ bec_erasure_prob (split_channel W 1 0) = bec_erasure_prob W
Proof
  rpt strip_tac >>
  drule bdmc_output_bij_split_channel_1_0 >> strip_tac >>
  drule bdmc_output_bij_invariance >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* Block 4: single_step_polar & Proposition 3 (Arıkan Section II Eqs. 22-23)  *)
(* -------------------------------------------------------------------------- *)

(* Polymorphic single-step polar channel transformation (W, W) |-> (W_minus, W_plus)
   corresponding to Arıkan Section II Eqs. (17)-(18), parameterized with general
   codomain bijections f : Y x Y -> Y_minus and h : Y_minus x bool -> Y_plus.
   Written by Gemini (Google DeepMind AI agent) *)
Definition single_step_polar_def:
  single_step_polar (W : (bool, α) memoryless_channel)
                    (W_minus : (bool, γ) memoryless_channel)
                    (W_plus : (bool, δ) memoryless_channel) ⇔
    wf_bdmc W ∧ wf_bdmc W_minus ∧ wf_bdmc W_plus ∧
    ∃f h.
      BIJ f (mccodomain W × mccodomain W) (mccodomain W_minus) ∧
      BIJ h (mccodomain W_minus × 𝕌(:bool)) (mccodomain W_plus) ∧
      (∀y1 y2 u1.
         y1 ∈ mccodomain W ∧ y2 ∈ mccodomain W ⇒
         mcchannel W_minus u1 {f (y1, y2)} =
           (1 / 2) * (mcchannel W u1 {y1} * mcchannel W F {y2} +
                      mcchannel W (¬u1) {y1} * mcchannel W T {y2})) ∧
      (∀y1 y2 u1 u2.
         y1 ∈ mccodomain W ∧ y2 ∈ mccodomain W ⇒
         mcchannel W_plus u2 {h (f (y1, y2), u1)} =
           (1 / 2) * mcchannel W (u1 ⇎ u2) {y1} * mcchannel W u2 {y2})
End

(* 2-step recurrence for get_every_nth_element with stride 2.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem get_every_2nd_cons2:
  ∀(x : α) y rest.
    get_every_nth_element (x :: y :: rest) 2 0 =
      x :: get_every_nth_element rest 2 0 ∧
    get_every_nth_element (x :: y :: rest) 2 1 =
      y :: get_every_nth_element rest 2 1
Proof
  simp[get_every_2nd_cons]
QED

(* Deinterleaving interleave [l0; l1] recovers l0 and l1 when LENGTH l0 = LENGTH l1.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem deinterleave_2_interleave_two:
  ∀(l0 : α list) l1.
    LENGTH l0 = LENGTH l1 ⇒
    EL 0 (deinterleave 2 (interleave [l0; l1])) = l0 ∧
    EL 1 (deinterleave 2 (interleave [l0; l1])) = l1
Proof
  simp[]
QED

(* Right-XOR translation is a permutation on length_n_codes k.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bxor_right_permutes:
  ∀k v_odd.
    LENGTH v_odd = k ⇒
    (λv. bxor v v_odd) PERMUTES (length_n_codes k)
Proof
  simp[bxor_right_bij]
QED

(* Bitwise XOR distributes over list append for equal-length prefixes and suffixes.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bxor_append_eq[local]:
  ∀a1 a2 b1 b2.
    LENGTH a1 = LENGTH b1 ∧ LENGTH a2 = LENGTH b2 ⇒
    bxor (a1 ++ a2) (b1 ++ b2) = bxor a1 b1 ++ bxor a2 b2
Proof
  simp[bxor_append]
QED

(* Bitwise XOR on singleton boolean lists.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bxor_sing[local]:
  ∀x y. bxor [x] [y] = [x ⇎ y]
Proof
  Cases >> Cases >> EVAL_TAC
QED

(* Right-constant multiplication factoring for REAL_SUM_IMAGE over a finite set.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_CMUL_R[local]:
  ∀s (f : α -> real) c.
    FINITE s ⇒
    REAL_SUM_IMAGE (λx. f x * c) s = REAL_SUM_IMAGE f s * c
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[REAL_MUL_SYM] >>
  irule REAL_SUM_IMAGE_CMUL >> simp[]
QED

(* Proposition 3 (Odd index 2 * i + 1, corresponding to Arıkan 1-indexed Eq. 23):
   Exact recursive expression of W_{2N}^{[2i+1]} in terms of W_N^{[i]}.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_3_odd:
  ∀(W : (bool, β) memoryless_channel) n i y1 y2 u_prev u1 u2.
    wf_bdmc W ∧ i < 2 ** n ∧
    LENGTH y1 = 2 ** n ∧ LENGTH y2 = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y1 ∧
    EVERY (λyi. yi ∈ mccodomain W) y2 ∧
    LENGTH u_prev = 2 * i ⇒
    mcchannel (split_channel W (2 * 2 ** n) (2 * i + 1)) u2
              {(y1 ++ y2, u_prev ++ [u1])} =
      (1 / 2) *
      mcchannel (split_channel W (2 ** n) i) (u1 ⇎ u2)
                {(y1, bxor (EL 0 (deinterleave 2 u_prev))
                           (EL 1 (deinterleave 2 u_prev)))} *
      mcchannel (split_channel W (2 ** n) i) u2
                {(y2, EL 1 (deinterleave 2 u_prev))}
Proof
  rpt strip_tac >>
  qabbrev_tac ‘N = 2n ** n’ >>
  ‘0n < N’ by simp[Abbr ‘N’] >>
  ‘2 * i + 1 < 2 * N’ by (simp[Abbr ‘N’] >> decide_tac) >>
  qabbrev_tac ‘k = N - i - 1’ >>
  ‘2 * N - (2 * i + 1) - 1 = 2 * k’ by (simp[Abbr ‘N’, Abbr ‘k’] >> decide_tac) >>
  drule length_deinterleave_2_half >>
  simp[deinterleave_2_eq] >> strip_tac >>
  qabbrev_tac ‘u_even = get_every_nth_element u_prev 2 0’ >>
  qabbrev_tac ‘u_odd = get_every_nth_element u_prev 2 1’ >>
  ‘LENGTH (bxor u_even u_odd) = i’ by simp[bxor_length] >>
  ‘LENGTH (y1 ++ y2) = 2 * N ∧ EVERY (λyi. yi ∈ mccodomain W) (y1 ++ y2)’
    by simp[] >>
  ‘LENGTH (u_prev ++ [u1]) = 2 * i + 1’ by simp[] >>
  qspecl_then [‘W’, ‘2 * N’, ‘2 * i + 1’, ‘u2’, ‘y1 ++ y2’, ‘u_prev ++ [u1]’]
    mp_tac mcchannel_split_channel_singleton_real >>
  simp[] >> disch_then SUBST1_TAC >>
  qspecl_then [‘W’, ‘N’, ‘i’, ‘u1 ⇎ u2’, ‘y1’, ‘bxor u_even u_odd’]
    mp_tac mcchannel_split_channel_singleton_real >>
  simp[] >> disch_then SUBST1_TAC >>
  qspecl_then [‘W’, ‘N’, ‘i’, ‘u2’, ‘y2’, ‘u_odd’]
    mp_tac mcchannel_split_channel_singleton_real >>
  simp[] >> disch_then SUBST1_TAC >>
  ‘((1 / 2) : extreal) = Normal (1 / 2)’
    by simp[extreal_of_num_def, extreal_div_eq] >>
  pop_assum SUBST1_TAC >>
  simp[extreal_mul_eq] >>
  qspecl_then
    [‘length_n_codes k × length_n_codes k’,
     ‘length_n_codes (2 * k)’,
     ‘λ(v_even : bool list, v_odd : bool list). interleave [v_even; v_odd]’,
     ‘λu_rest : bool list.
        real (mcchannel (combine_channel W (2 * N))
                        (u_prev ++ [u1] ++ [u2] ++ u_rest) {y1 ++ y2})’]
    mp_tac REAL_SUM_IMAGE_BIJ >>
  simp[FINITE_CROSS, BIJ_interleave_two] >>
  disch_then SUBST1_TAC >>
  simp[combinTheory.o_DEF, pairTheory.UNCURRY] >>
  qspecl_then
    [‘length_n_codes k’,
     ‘length_n_codes k’,
     ‘λ(v_even : bool list) (v_odd : bool list).
        real (mcchannel (combine_channel W (2 * N))
                (u_prev ++ [u1] ++ [u2] ++ interleave [v_even; v_odd])
                {y1 ++ y2})’]
    mp_tac (GSYM REAL_SUM_IMAGE_REAL_SUM_IMAGE) >>
  simp[] >> disch_then SUBST1_TAC >>
  DEP_ONCE_REWRITE_TAC[NESTED_REAL_SUM_IMAGE_REVERSE] >> simp[] >>
  qabbrev_tac
    ‘S1 = REAL_SUM_IMAGE
            (λw. real (mcchannel (combine_channel W N)
                                 (bxor u_even u_odd ++ [u1 ⇎ u2] ++ w) {y1}))
            (length_n_codes k)’ >>
  qabbrev_tac
    ‘S2 = REAL_SUM_IMAGE
            (λv_odd. real (mcchannel (combine_channel W N)
                                     (u_odd ++ [u2] ++ v_odd) {y2}))
            (length_n_codes k)’ >>
  Know
    ‘REAL_SUM_IMAGE
       (λv_odd.
          REAL_SUM_IMAGE
            (λv_even.
               real (mcchannel (combine_channel W (2 * N))
                       (u_prev ++ [u1] ++ [u2] ++ interleave [v_even; v_odd])
                       {y1 ++ y2}))
            (length_n_codes k))
       (length_n_codes k) =
     REAL_SUM_IMAGE
       (λv_odd.
          real (mcchannel (combine_channel W N)
                          (u_odd ++ [u2] ++ v_odd) {y2}) * S1)
       (length_n_codes k)’
  >- (irule REAL_SUM_IMAGE_EQ >> simp[] >>
      qx_gen_tac ‘v_odd’ >> simp[] >> strip_tac >>
      Know
        ‘REAL_SUM_IMAGE
           (λv_even.
              real (mcchannel (combine_channel W (2 * N))
                      (u_prev ++ [u1] ++ [u2] ++ interleave [v_even; v_odd])
                      {y1 ++ y2}))
           (length_n_codes k) =
         REAL_SUM_IMAGE
           (λv_even.
              real (mcchannel (combine_channel W N)
                      (bxor u_even u_odd ++ [u1 ⇎ u2] ++ bxor v_even v_odd)
                      {y1}) *
              real (mcchannel (combine_channel W N)
                              (u_odd ++ [u2] ++ v_odd) {y2}))
           (length_n_codes k)’
      >- (irule REAL_SUM_IMAGE_EQ >> simp[] >>
          qx_gen_tac ‘v_even’ >> simp[] >> strip_tac >>
          ‘N = 2n ** n’ by simp[Abbr ‘N’] >>
          pop_assum SUBST_ALL_TAC >>
          qabbrev_tac ‘u_full = u_prev ++ [u1] ++ [u2] ++ interleave [v_even; v_odd]’ >>
          ‘LENGTH (interleave [v_even; v_odd]) = 2 * k’
            by simp[length_interleave_two] >>
          ‘LENGTH u_full = 2 * 2 ** n’
            by (simp[Abbr ‘u_full’, Abbr ‘k’] >> decide_tac) >>
          ‘u_full = u_prev ++ (u1 :: u2 :: interleave [v_even; v_odd])’
            by simp[Abbr ‘u_full’] >>
          ‘EVEN (LENGTH u_prev)’ by (simp[] >> metis_tac[EVEN_DOUBLE]) >>
          ‘get_every_nth_element u_full 2 0 = (u_even ++ [u1]) ++ v_even ∧
           get_every_nth_element u_full 2 1 = (u_odd ++ [u2]) ++ v_odd’
            by (qpat_x_assum ‘u_full = u_prev ++ _’ SUBST1_TAC >>
                qspecl_then [‘u_prev’, ‘u1 :: u2 :: interleave [v_even; v_odd]’]
                  mp_tac get_every_2nd_append_even >>
                simp[Abbr ‘u_even’, Abbr ‘u_odd’]) >>
          ‘bxor ((u_even ++ [u1]) ++ v_even) ((u_odd ++ [u2]) ++ v_odd) =
           (bxor u_even u_odd ++ [u1 ⇎ u2]) ++ bxor v_even v_odd’
            by simp[bxor_append_eq, bxor_sing] >>
          qspecl_then [‘W’, ‘n’, ‘u_full’, ‘y1’, ‘y2’] mp_tac
            mcchannel_combine_channel_step >>
          simp[deinterleave_2_eq] >>
          disch_then SUBST1_TAC >>
          ‘LENGTH (bxor u_even u_odd ++ [u1 ⇎ u2] ++ bxor v_even v_odd) = 2 ** n ∧
           LENGTH (u_odd ++ [u2] ++ v_odd) = 2 ** n’
            by (simp[bxor_length, Abbr ‘k’] >> decide_tac) >>
          qspecl_then
            [‘W’, ‘n’, ‘bxor u_even u_odd ++ [u1 ⇎ u2] ++ bxor v_even v_odd’, ‘y1’]
            mp_tac mcchannel_combine_channel_singleton_normal >>
          qspecl_then [‘W’, ‘n’, ‘u_odd ++ [u2] ++ v_odd’, ‘y2’]
            mp_tac mcchannel_combine_channel_singleton_normal >>
          simp[] >>
          rpt strip_tac >>
          simp[extreal_mul_eq, real_normal]) >>
      disch_then SUBST1_TAC >>
      qspecl_then
        [‘length_n_codes k’,
         ‘λv_even : bool list.
            real (mcchannel (combine_channel W N)
                    (bxor u_even u_odd ++ [u1 ⇎ u2] ++ bxor v_even v_odd)
                    {y1})’,
         ‘real (mcchannel (combine_channel W N)
                          (u_odd ++ [u2] ++ v_odd) {y2})’]
        mp_tac REAL_SUM_IMAGE_CMUL_R >>
      simp[] >> disch_then SUBST1_TAC >>
      ‘REAL_SUM_IMAGE
         (λv_even.
            real (mcchannel (combine_channel W N)
                    (bxor u_even u_odd ++ [u1 ⇎ u2] ++ bxor v_even v_odd)
                    {y1}))
         (length_n_codes k) = S1’
        by (qspecl_then
              [‘length_n_codes k’,
               ‘length_n_codes k’,
               ‘λv : bool list. bxor v v_odd’,
               ‘λw : bool list.
                  real (mcchannel (combine_channel W N)
                          (bxor u_even u_odd ++ [u1 ⇎ u2] ++ w) {y1})’]
              mp_tac REAL_SUM_IMAGE_BIJ >>
            simp[bxor_right_bij, combinTheory.o_DEF, Abbr ‘S1’]) >>
      pop_assum SUBST1_TAC >>
      (fn (asl, w) => ACCEPT_TAC (RealField.REAL_RING w) (asl, w))) >>
  disch_then SUBST1_TAC >>
  qspecl_then
    [‘length_n_codes k’,
     ‘λv_odd : bool list.
        real (mcchannel (combine_channel W N)
                        (u_odd ++ [u2] ++ v_odd) {y2})’,
     ‘S1’]
    mp_tac REAL_SUM_IMAGE_CMUL_R >>
  simp[] >> disch_then SUBST1_TAC >>
  ‘(2 : real) pow (2 * N - 1) = 2 * ((2 : real) pow (N - 1)) pow 2’
    by (‘2 * N - 1 = SUC ((N - 1) + (N - 1))’ by decide_tac >>
        pop_assum SUBST1_TAC >>
        REWRITE_TAC[pow, POW_ADD, POW_2] >>
        (fn (asl, w) => ACCEPT_TAC (RealField.REAL_RING w) (asl, w))) >>
  pop_assum SUBST1_TAC >>
  simp[Abbr ‘S1’, Abbr ‘S2’]
QED

(* Proposition 3 (Even index 2 * i, corresponding to Arıkan 1-indexed Eq. 22):
   Exact recursive expression of W_{2N}^{[2i]} in terms of W_N^{[i]}.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_3_even:
  ∀(W : (bool, β) memoryless_channel) n i y1 y2 u_prev u1.
    wf_bdmc W ∧ i < 2 ** n ∧
    LENGTH y1 = 2 ** n ∧ LENGTH y2 = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y1 ∧
    EVERY (λyi. yi ∈ mccodomain W) y2 ∧
    LENGTH u_prev = 2 * i ⇒
    mcchannel (split_channel W (2 * 2 ** n) (2 * i)) u1
              {(y1 ++ y2, u_prev)} =
      (1 / 2) *
      (mcchannel (split_channel W (2 ** n) i) u1
                 {(y1, bxor (EL 0 (deinterleave 2 u_prev))
                            (EL 1 (deinterleave 2 u_prev)))} *
       mcchannel (split_channel W (2 ** n) i) F
                 {(y2, EL 1 (deinterleave 2 u_prev))} +
       mcchannel (split_channel W (2 ** n) i) (¬u1)
                 {(y1, bxor (EL 0 (deinterleave 2 u_prev))
                            (EL 1 (deinterleave 2 u_prev)))} *
       mcchannel (split_channel W (2 ** n) i) T
                 {(y2, EL 1 (deinterleave 2 u_prev))})
Proof
  rpt strip_tac >>
  ‘2 * i + 1 < 2 * 2 ** n’ by decide_tac >>
  drule_all mcchannel_split_channel_marginalize >>
  disch_then (qspecl_then [‘u1’, ‘y1 ++ y2’, ‘u_prev’] SUBST1_TAC) >>
  qspecl_then [‘W’, ‘n’, ‘i’, ‘y1’, ‘y2’, ‘u_prev’, ‘u1’, ‘F’]
    mp_tac proposition_3_odd >>
  qspecl_then [‘W’, ‘n’, ‘i’, ‘y1’, ‘y2’, ‘u_prev’, ‘u1’, ‘T’]
    mp_tac proposition_3_odd >>
  ‘(u1 ⇎ F) = u1 ∧ (u1 ⇎ T) = ¬u1’ by (Cases_on ‘u1’ >> simp[]) >>
  simp[deinterleave_2_eq] >>
  ntac 2 (disch_then kall_tac) >>
  drule length_deinterleave_2_half >>
  simp[deinterleave_2_eq] >> strip_tac >>
  qabbrev_tac ‘a = bxor (get_every_nth_element u_prev 2 0)
                        (get_every_nth_element u_prev 2 1)’ >>
  qabbrev_tac ‘b = get_every_nth_element u_prev 2 1’ >>
  ‘LENGTH a = i’ by simp[Abbr ‘a’, bxor_length] >>
  qspecl_then [‘W’, ‘n’, ‘i’, ‘u1’, ‘y1’, ‘a’]
    mp_tac mcchannel_split_channel_singleton_normal >>
  qspecl_then [‘W’, ‘n’, ‘i’, ‘¬u1’, ‘y1’, ‘a’]
    mp_tac mcchannel_split_channel_singleton_normal >>
  qspecl_then [‘W’, ‘n’, ‘i’, ‘F’, ‘y2’, ‘b’]
    mp_tac mcchannel_split_channel_singleton_normal >>
  qspecl_then [‘W’, ‘n’, ‘i’, ‘T’, ‘y2’, ‘b’]
    mp_tac mcchannel_split_channel_singleton_normal >>
  simp[] >> rpt strip_tac >>
  ‘((1 / 2) : extreal) = Normal (1 / 2)’
    by simp[extreal_of_num_def, extreal_div_eq] >>
  pop_assum SUBST1_TAC >>
  simp[extreal_mul_eq, extreal_add_eq] >>
  (fn (asl, w) => ACCEPT_TAC (RealField.REAL_RING w) (asl, w))
QED

(* Bundled Proposition 3 combining even (Eq. 22) and odd (Eq. 23) recurrences.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_3:
  (∀(W : (bool, β) memoryless_channel) n i y1 y2 u_prev u1.
     wf_bdmc W ∧ i < 2 ** n ∧
     LENGTH y1 = 2 ** n ∧ LENGTH y2 = 2 ** n ∧
     EVERY (λyi. yi ∈ mccodomain W) y1 ∧
     EVERY (λyi. yi ∈ mccodomain W) y2 ∧
     LENGTH u_prev = 2 * i ⇒
     mcchannel (split_channel W (2 * 2 ** n) (2 * i)) u1
               {(y1 ++ y2, u_prev)} =
       (1 / 2) *
       (mcchannel (split_channel W (2 ** n) i) u1
                  {(y1, bxor (EL 0 (deinterleave 2 u_prev))
                             (EL 1 (deinterleave 2 u_prev)))} *
        mcchannel (split_channel W (2 ** n) i) F
                  {(y2, EL 1 (deinterleave 2 u_prev))} +
        mcchannel (split_channel W (2 ** n) i) (¬u1)
                  {(y1, bxor (EL 0 (deinterleave 2 u_prev))
                             (EL 1 (deinterleave 2 u_prev)))} *
        mcchannel (split_channel W (2 ** n) i) T
                  {(y2, EL 1 (deinterleave 2 u_prev))})) ∧
  (∀(W : (bool, β) memoryless_channel) n i y1 y2 u_prev u1 u2.
     wf_bdmc W ∧ i < 2 ** n ∧
     LENGTH y1 = 2 ** n ∧ LENGTH y2 = 2 ** n ∧
     EVERY (λyi. yi ∈ mccodomain W) y1 ∧
     EVERY (λyi. yi ∈ mccodomain W) y2 ∧
     LENGTH u_prev = 2 * i ⇒
     mcchannel (split_channel W (2 * 2 ** n) (2 * i + 1)) u2
               {(y1 ++ y2, u_prev ++ [u1])} =
       (1 / 2) *
       mcchannel (split_channel W (2 ** n) i) (u1 ⇎ u2)
                 {(y1, bxor (EL 0 (deinterleave 2 u_prev))
                            (EL 1 (deinterleave 2 u_prev)))} *
       mcchannel (split_channel W (2 ** n) i) u2
                 {(y2, EL 1 (deinterleave 2 u_prev))})
Proof
  simp[proposition_3_even, proposition_3_odd]
QED

(* Explicit output bijection f for Proposition 3 single-step channel transformation:
   ((y1, a), (y2, b)) |-> (y1 ++ y2, interleave [bxor a b; b]).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem BIJ_split_step_f:
  ∀(Y : β -> bool) N i.
    BIJ (λ((y1, a), (y2, b)). (y1 ++ y2, interleave [bxor a b; b]))
        ((cross_list (REPLICATE N Y) × length_n_codes i) ×
         (cross_list (REPLICATE N Y) × length_n_codes i))
        (cross_list (REPLICATE (2 * N) Y) × length_n_codes (2 * i))
Proof
  rpt gen_tac >>
  simp[BIJ_IFF_INV, in_cross_list_replicate] >>
  conj_tac
  >- (Cases >> Cases_on ‘q’ >> Cases_on ‘r’ >> simp[EVERY_APPEND] >>
      strip_tac >> DEP_REWRITE_TAC[length_interleave_two] >> simp[bxor_length]) >>
  qexists_tac
    ‘λ(y, u_prev).
       ((TAKE N y, bxor (EL 0 (deinterleave 2 u_prev))
                        (EL 1 (deinterleave 2 u_prev))),
        (DROP N y, EL 1 (deinterleave 2 u_prev)))’ >>
  conj_tac
  >- (Cases >> rename1 ‘(y, u_prev)’ >> simp[] >> strip_tac >>
      ‘TAKE N y ++ DROP N y = y’ by simp[TAKE_DROP] >>
      ‘EVERY (λx. x ∈ Y) (TAKE N y) ∧ EVERY (λx. x ∈ Y) (DROP N y)’
        by metis_tac[EVERY_APPEND] >>
      drule length_deinterleave_2_half >>
      simp[deinterleave_2_eq] >> strip_tac >>
      simp[LENGTH_TAKE, LENGTH_DROP, bxor_length]) >>
  conj_tac
  >- (Cases >> Cases_on ‘q’ >> Cases_on ‘r’ >>
      rename1 ‘((y1, a), (y2, b))’ >> simp[] >> strip_tac >>
      ‘LENGTH (bxor a b) = LENGTH b’ by simp[bxor_length] >>
      simp[deinterleave_2_eq, TAKE_APPEND1, DROP_APPEND2, bxor_inv_right]) >>
  Cases >> rename1 ‘(y, u_prev)’ >> simp[] >> strip_tac >>
  simp[TAKE_DROP] >>
  drule length_deinterleave_2_half >>
  simp[deinterleave_2_eq] >> strip_tac >>
  ‘EVEN (2 * i)’ by metis_tac[EVEN_DOUBLE] >>
  ‘EVEN (LENGTH u_prev)’ by simp[] >>
  simp[deinterleave_2_eq, bxor_inv_right, interleave_get_every_2nd]
QED

(* Explicit output bijection h for Proposition 3 single-step channel transformation:
   ((ys, us), u1) |-> (ys, us ++ [u1]).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem BIJ_split_step_h:
  ∀(S_y : β list -> bool) k.
    BIJ (λ((ys, us), u1 : bool). (ys, us ++ [u1]))
        ((S_y × length_n_codes k) × 𝕌(:bool))
        (S_y × length_n_codes (k + 1))
Proof
  rpt gen_tac >>
  simp[BIJ_IFF_INV] >>
  conj_tac
  >- (Cases >> Cases_on ‘q’ >> simp[]) >>
  qexists_tac ‘λ(ys, us). ((ys, FRONT us), LAST us)’ >>
  conj_tac
  >- (Cases >> rename1 ‘(ys, us)’ >> simp[] >> strip_tac >>
      ‘us ≠ []’ by (Cases_on ‘us’ >> gvs[]) >>
      qspec_then ‘us’ strip_assume_tac SNOC_CASES >>
      gvs[] >>
      PURE_REWRITE_TAC[GSYM SNOC_APPEND, FRONT_SNOC, LAST_SNOC] >>
      Cases_on ‘x’ >> simp[]) >>
  conj_tac
  >- (Cases >> Cases_on ‘q’ >> simp[] >> strip_tac >>
      PURE_REWRITE_TAC[GSYM SNOC_APPEND, FRONT_SNOC, LAST_SNOC] >>
      simp[]) >>
  Cases >> rename1 ‘(ys, us)’ >> simp[] >> strip_tac >>
  ‘us ≠ []’ by (Cases_on ‘us’ >> gvs[]) >>
  qspec_then ‘us’ strip_assume_tac SNOC_CASES >>
  gvs[] >>
  PURE_REWRITE_TAC[GSYM SNOC_APPEND, FRONT_SNOC, LAST_SNOC] >>
  simp[]
QED

(* Contract theorem: Proposition 3 instantiated as single_step_polar between
   level 2**n channel i and level 2 * 2**n channels 2*i and 2*i + 1.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_3_single_step:
  ∀(W : (bool, β) memoryless_channel) n i.
    wf_bdmc W ∧ i < 2 ** n ⇒
    single_step_polar
      (split_channel W (2 ** n) i)
      (split_channel W (2 * 2 ** n) (2 * i))
      (split_channel W (2 * 2 ** n) (2 * i + 1))
Proof
  rpt strip_tac >>
  simp[single_step_polar_def] >>
  ‘2 * i < 2 * 2 ** n ∧ 2 * i + 1 < 2 * 2 ** n’ by decide_tac >>
  simp[wf_bdmc_split_channel_gen] >>
  qexistsl_tac [
    ‘λ((y1, a), (y2, b)). (y1 ++ y2, interleave [bxor a b; b])’,
    ‘λ((ys, us), u1). (ys, us ++ [u1])’
  ] >>
  simp[mccodomain_split_channel] >>
  conj_tac
  >- (qspecl_then [‘mccodomain W’, ‘2 ** n’, ‘i’] mp_tac BIJ_split_step_f >>
      simp[]) >>
  conj_tac
  >- (qspecl_then
        [‘cross_list (REPLICATE (2 * 2 ** n) (mccodomain W))’, ‘2 * i’]
        mp_tac BIJ_split_step_h >>
      simp[]) >>
  conj_tac
  >- (qx_genl_tac [‘p1’, ‘p2’, ‘u1’] >> strip_tac >>
      Cases_on ‘p1’ >> rename1 ‘(ys1, a)’ >>
      Cases_on ‘p2’ >> rename1 ‘mcchannel _ F {(ys2, b)}’ >>
      fs[in_cross_list_replicate] >>
      ‘LENGTH (bxor a b) = i’ by simp[bxor_length] >>
      ‘LENGTH (interleave [bxor a b; b]) = 2 * i’
        by (DEP_REWRITE_TAC[length_interleave_two] >> simp[]) >>
      qspecl_then
        [‘W’, ‘n’, ‘i’, ‘ys1’, ‘ys2’,
         ‘interleave [bxor a b; b]’, ‘u1’]
        mp_tac proposition_3_even >>
      simp[deinterleave_2_eq, bxor_inv_right]) >>
  qx_genl_tac [‘p1’, ‘p2’, ‘u1’, ‘u2’] >> strip_tac >>
  Cases_on ‘p1’ >> rename1 ‘(ys1, a)’ >>
  Cases_on ‘p2’ >> rename1 ‘mcchannel _ u2 {(ys2, b)}’ >>
  fs[in_cross_list_replicate] >>
  ‘LENGTH (bxor a b) = i’ by simp[bxor_length] >>
  ‘LENGTH (interleave [bxor a b; b]) = 2 * i’
    by (DEP_REWRITE_TAC[length_interleave_two] >> simp[]) >>
  qspecl_then
    [‘W’, ‘n’, ‘i’, ‘ys1’, ‘ys2’,
     ‘interleave [bxor a b; b]’, ‘u1’, ‘u2’]
    mp_tac proposition_3_odd >>
  simp[deinterleave_2_eq, bxor_inv_right]
QED

(* Root single-step polar transformation:
   (W, W) |-> (split_channel W 2 0, split_channel W 2 1).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem single_step_polar_root:
  ∀(W : (bool, β) memoryless_channel).
    wf_bdmc W ⇒
    single_step_polar W (split_channel W 2 0) (split_channel W 2 1)
Proof
  rpt strip_tac >>
  simp[single_step_polar_def] >>
  ‘0n < 2 ∧ 1n < 2’ by decide_tac >>
  simp[wf_bdmc_split_channel_gen] >>
  qexistsl_tac [
    ‘λ(y1, y2). ([y1; y2], [] : bool list)’,
    ‘λ((ys, us), u1). (ys, us ++ [u1])’
  ] >>
  simp[mccodomain_split_channel] >>
  conj_tac
  >- (simp[BIJ_IFF_INV, in_cross_list_replicate] >>
      conj_tac >- (Cases >> simp[]) >>
      qexists_tac ‘λ(ys, _). (EL 0 ys, EL 1 ys)’ >>
      conj_tac
      >- (Cases >> rename1 ‘(ys, us)’ >> simp[] >> strip_tac >>
          Cases_on ‘ys’ >> gvs[] >> Cases_on ‘t’ >> gvs[]) >>
      conj_tac
      >- (Cases >> simp[]) >>
      Cases >> rename1 ‘(ys, us)’ >> simp[] >> strip_tac >>
      Cases_on ‘ys’ >> gvs[] >> Cases_on ‘t’ >> gvs[]) >>
  conj_tac
  >- (qspecl_then [‘cross_list (REPLICATE 2 (mccodomain W))’, ‘0’] mp_tac
        BIJ_split_step_h >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qspecl_then [‘W’, ‘0’, ‘0’, ‘[y1]’, ‘[y2]’, ‘[]’, ‘u1’] mp_tac
        proposition_3_even >>
      ‘get_every_nth_element ([] : bool list) 2 0 = [] ∧
       get_every_nth_element ([] : bool list) 2 1 = [] ∧
       bxor ([] : bool list) [] = []’ by EVAL_TAC >>
      simp[deinterleave_2_eq, mcchannel_split_channel_1_0]) >>
  rpt strip_tac >>
  qspecl_then [‘W’, ‘0’, ‘0’, ‘[y1]’, ‘[y2]’, ‘[]’, ‘u1’, ‘u2’] mp_tac
    proposition_3_odd >>
  ‘get_every_nth_element ([] : bool list) 2 0 = [] ∧
   get_every_nth_element ([] : bool list) 2 1 = [] ∧
   bxor ([] : bool list) [] = []’ by EVAL_TAC >>
  simp[deinterleave_2_eq, mcchannel_split_channel_1_0]
QED

(* Exhaustiveness of erasure_bit constructors (discharging x IN UNIV(:erasure_bit)
   after UNIV_ERASURE_BIT[simp] expansion).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem erasure_bit_exhaust[simp]:
  ∀(x : erasure_bit). x = E_T ∨ x = E_F ∨ x = Erasure
Proof
  Cases >> simp[]
QED

(* Last-coordinate split channel boundary formula (i + 1 = N, zero future bits).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_split_channel_last:
  ∀(W : (bool, β) memoryless_channel) N i u_i y u_prev.
    wf_bdmc W ∧ i + 1 = N ⇒
    mcchannel (split_channel W N i) u_i {(y, u_prev)} =
      (1 / 2 pow i) * mcchannel (combine_channel W N) (u_prev ++ [u_i]) {y}
Proof
  rpt strip_tac >>
  ‘i < N ∧ N - 1 = i ∧ N - i - 1 = 0’ by decide_tac >>
  drule_all mcchannel_split_channel_singleton_gen >>
  simp[]
QED
