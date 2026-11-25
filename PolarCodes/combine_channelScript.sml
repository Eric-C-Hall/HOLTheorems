(* ========================================================================= *)
(*   Edited and extended by Gemini (Google DeepMind AI agent):               *)
(*                                                                           *)
(*   Preserved combine_channel_alt unmodified. Added Ancestors, Libs, and    *)
(*   val _ = hide "W"; / val _ = hide "S"; parser guards, defined genuine    *)
(*   recursive channel combining (recursive_combine_channel_def via          *)
(*   combine_channel_base0_def and combine_channel_step0_def), and proved    *)
(*   equivalence with combine_channel and polar_encode_channel               *)
(*   (combine_channel_eq_recursive_combine,                                  *)
(*   polar_encode_channel_eq_recursive_combine), Arikan Eq. (4) singleton    *)
(*   product transition probabilities (mcchannel_combine_channel_singleton), *)
(*   domain/codomain/events/prob_space properties, finite-powerset           *)
(*   sigma_list and prod_list append-product lemmas, and recursive step      *)
(*   factorizations (mcchannel_combine_channel_step).                        *)
(* ========================================================================= *)

Theory combine_channel

Ancestors arithmetic bdmc bitstring borel bxor_lemmas combin
          ecc_prob_space extreal fundamental interleave
          jared_yeager_prod_list lebesgue lifting list martingale
          measure memoryless_channel pair polar_encode pred_set
          probability repeat_channel rich_list sigma_algebra
          transform_input_channel trivial

Libs ConseqConv dep_rewrite hurdUtils liftLib realLib transferLib;

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
(* Combines channels as in polar encoding.                                    *)
(* -------------------------------------------------------------------------- *)
(*Definition combine_channel_def:
  combine_channel (W : (α, β) memoryless_channel) num_inputs
  = if num_inputs ≤ 1
    then
      λinputs.
        TODO TODO TODO
             Apply W to inputs here
             TODO TODO TODO
    else
      let
        recursive_channel = polar_encode_channel W (num_inputs DIV 2)
      in
        λinputs.
          let
        even_odd_inputs = deinterleave 2 inputs;
        even_inputs = EL 0 even_odd_inputs;
        odd_inputs = EL 1 even_odd_inputs;
      in
        polar_encode (bxor even_inputs odd_inputs) ++ polar_encode odd_inputs

                                                                   (λbs. )
                                                                   polar_encode_channel
End*)

(* -------------------------------------------------------------------------- *)
(* TODO: when combine_channel def has been defined, this should be a theorem  *)
(* rather than a definition                                                   *)
(* TODO: when defining combine_channel directly, can this be defined as an    *)
(* (α list, β list) memoryless_channel rather than a                          *)
(* (bool list, β list) memoryless_channel                                     *)
(* -------------------------------------------------------------------------- *)
Definition combine_channel_alt:
  combine_channel (W : (bool, β) memoryless_channel) (num_inputs : num)
  = polar_encode_channel W num_inputs
    : (bool list, β list) memoryless_channel
End

(* -------------------------------------------------------------------------- *)
(* Block 1: Unpacked Accessors for transform_input_channel & repeat_channel   *)
(* -------------------------------------------------------------------------- *)

(* Unpacked accessors for transform_input_channel.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem transform_input_channel_accessors:
  ∀(f : α -> β) (S_dom : α -> bool) (W : (β, γ) memoryless_channel).
    mcdomain (transform_input_channel f S_dom W) =
      S_dom ∩ PREIMAGE f (mcdomain W) ∧
    mcsigma (transform_input_channel f S_dom W) = mcsigma W ∧
    mccodomain (transform_input_channel f S_dom W) = mccodomain W ∧
    mcevents (transform_input_channel f S_dom W) = mcevents W ∧
    mcchannel (transform_input_channel f S_dom W) = (mcchannel W) ∘ f
Proof
  rpt gen_tac
  >> simp[transform_input_channel_def]
  >> ‘wf_memoryless_channel (transform_input_channel0 f S_dom (memoryless_channel_REP W))’
       by simp[wf_memoryless_channel_transform_input_channel0]
  >> drule memoryless_channel_ABS_accessors >> strip_tac
  >> simp[transform_input_channel0_def, memoryless_channel_REP_alt,
          mcdomain0_def, mcsigma0_def, mccodomain0_def, mcevents0_def,
          mcchannel0_def, mcsigma_alt]
QED

(* Unpacked accessors for repeat_channel.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem repeat_channel_accessors:
  ∀(W : (α, β) memoryless_channel) (N : num).
    mcdomain (repeat_channel W N) = cross_list (REPLICATE N (mcdomain W)) ∧
    mcsigma (repeat_channel W N) = sigma_list (REPLICATE N (mcsigma W)) ∧
    mccodomain (repeat_channel W N) = cross_list (REPLICATE N (mccodomain W)) ∧
    mcevents (repeat_channel W N) = subsets (sigma_list (REPLICATE N (mcsigma W))) ∧
    mcchannel (repeat_channel W N) =
      (λxs. prob (prod_list (MAP (mcprob_space W) xs)))
Proof
  rpt gen_tac
  >> simp[repeat_channel_def]
  >> ‘wf_memoryless_channel (repeat_channel0 (memoryless_channel_REP W) N)’
       by simp[wf_memoryless_channel_repeat_channel0]
  >> drule memoryless_channel_ABS_accessors >> strip_tac
  >> simp[repeat_channel0_def, memoryless_channel_REP_alt,
          mcdomain0_def, mcsigma0_def, mccodomain0_def, mcevents0_def,
          mcchannel0_def]
  >> conj_tac
  >- (simp[fst_sigma_list] >> Induct_on ‘N’ >> simp[mcsigma_alt])
  >> conj_tac
  >- (Cases_on ‘sigma_list (REPLICATE N (mcsigma W))’ >> simp[subsets_def])
  >> Know ‘mcprob_space0 (mcdomain W, mcsigma W, mcchannel W) = mcprob_space W’
  >- (simp[FUN_EQ_THM, mcprob_space0_def, mcprob_space_alt,
           mccodomain0_def, mcevents0_def, mcsigma0_def, mcchannel0_def, mcsigma_alt])
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* Block 2: cross_list, Powerset sigma_list, & repeat_channel Product Lemmas  *)
(* -------------------------------------------------------------------------- *)

(* Membership characterization for cross_list of REPLICATE.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem in_cross_list_replicate:
  ∀n (s : α -> bool) xs.
    xs ∈ cross_list (REPLICATE n s) ⇔
      LENGTH xs = n ∧ EVERY (λx. x ∈ s) xs
Proof
  Induct_on ‘n’
  >- (simp[cross_list_def] >> gen_tac >> Cases_on ‘xs’ >> simp[])
  >> rpt gen_tac
  >> simp[cross_list_def, IN_general_cross]
  >> Cases_on ‘xs’ >> simp[]
  >> metis_tac[]
QED

(* Set-comprehension equality for cross_list (REPLICATE n s).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem cross_list_replicate_alt:
  ∀n (s : α -> bool).
    cross_list (REPLICATE n s) = {xs | LENGTH xs = n ∧ EVERY (λx. x ∈ s) xs}
Proof
  rpt gen_tac >> simp[EXTENSION, in_cross_list_replicate]
QED

(* cross_list of n copies of UNIV(:bool) equals length_n_codes n.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem cross_list_replicate_univ_bool:
  ∀n. cross_list (REPLICATE n 𝕌(:bool)) = length_n_codes n
Proof
  gen_tac >> simp[EXTENSION, in_cross_list_replicate]
  >> gen_tac >> EQ_TAC >> strip_tac >> simp[EVERY_MEM]
QED

(* Appending two lists from cross_list ds1 and cross_list ds2 lands in cross_list (ds1 ++ ds2).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem append_in_cross_list:
  ∀ds1 ds2 xs ys.
    xs ∈ cross_list ds1 ∧ ys ∈ cross_list ds2 ⇒
    (xs ++ ys) ∈ cross_list (ds1 ++ ds2)
Proof
  Induct_on ‘ds1’ >- simp[cross_list_def]
  >> rpt gen_tac >> simp[cross_list_def, IN_general_cross]
  >> strip_tac >> gvs[]
  >> qexistsl [‘a’, ‘b ++ ys’] >> simp[]
QED

(* Finiteness of cross_list when every component set is finite.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem finite_cross_list:
  ∀ds : (α -> bool) list.
    EVERY FINITE ds ⇒ FINITE (cross_list ds)
Proof
  Induct_on ‘ds’ >- simp[cross_list_def]
  >> rw[cross_list_def]
  >> Know ‘general_cross CONS h (cross_list ds) =
           IMAGE (UNCURRY CONS) (h × cross_list ds)’
  >- (simp[EXTENSION, IN_general_cross, PULL_EXISTS, EXISTS_PROD])
  >> disch_then SUBST1_TAC
  >> irule IMAGE_FINITE >> simp[FINITE_CROSS]
QED

(* Finiteness of cross_list (REPLICATE n s) for finite s.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem finite_cross_list_replicate:
  ∀n (s : α -> bool).
    FINITE s ⇒ FINITE (cross_list (REPLICATE n s))
Proof
  rpt strip_tac >> irule finite_cross_list
  >> Induct_on ‘n’ >> simp[]
QED

(* Left-split recurrence for EXTREAL_PROD_IMAGE over count (SUC n).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem EXTREAL_PROD_IMAGE_COUNT_SUC_LEFT:
  ∀(f : num -> extreal) n.
    ∏ f (count (SUC n)) = f 0 * ∏ (λi. f (SUC i)) (count n)
Proof
  gen_tac >> Induct_on ‘n’
  >- simp[EXTREAL_PROD_IMAGE_COUNT_ONE, EXTREAL_PROD_IMAGE_COUNT_ZERO]
  >> simp[EXTREAL_PROD_IMAGE_COUNT_SUC, mul_assoc]
QED

(* Singleton measurability in sigma_list when each coordinate singleton is measurable.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem singleton_in_subsets_sigma_list:
  ∀sal (ys : α list).
    LENGTH ys = LENGTH sal ∧
    (∀i. i < LENGTH sal ⇒ {EL i ys} ∈ subsets (EL i sal)) ⇒
    {ys} ∈ subsets (sigma_list sal)
Proof
  Induct_on ‘sal’ >> Cases_on ‘ys’ >> simp[sigma_list_def]
  >> rpt strip_tac
  >> rename1 ‘{y :: ys} ∈ subsets (general_sigma CONS sa (sigma_list sal))’
  >> Know ‘{y :: ys} = general_cross CONS {y} {ys}’
  >- simp[EXTENSION, IN_general_cross]
  >> disch_then SUBST1_TAC
  >> simp[general_sigma_def]
  >> irule IN_SIGMA
  >> simp[IN_general_prod]
  >> qexistsl [‘{y}’, ‘{ys}’]
  >> conj_tac >- simp[]
  >> conj_tac
  >- (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[])
  >> first_x_assum irule >> simp[]
  >> rw[] >> first_x_assum (qspec_then ‘SUC i’ mp_tac) >> simp[]
QED

(* sigma_list of finite powerset sigma-algebras equals the powerset sigma-algebra on cross_list.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem sigma_list_pow:
  ∀ds : (α -> bool) list.
    EVERY FINITE ds ⇒
    sigma_list (MAP (λd. (d, POW d)) ds) =
      (cross_list ds, POW (cross_list ds))
Proof
  rpt strip_tac
  >> Know ‘sigma_algebra (sigma_list (MAP (λd. (d, POW d)) ds))’
  >- (Induct_on ‘ds’
      >- simp[sigma_list_def, GSYM fundamentalTheory.POW_SING, POW_SIGMA_ALGEBRA]
      >> rw[sigma_list_def] >> irule sigma_algebra_general_sigma
      >> simp[subset_class_POW]
      >> irule SIGMA_ALGEBRA_SUBSET_CLASS >> simp[])
  >> strip_tac
  >> irule ALGEBRA_CONG_ALT
  >> conj_tac
  >- simp[space_sigma_list, MAP_MAP_o, o_DEF]
  >> irule SUBSET_ANTISYM >> conj_tac
  >- (drule SIGMA_ALGEBRA_SUBSET_CLASS
      >> simp[subset_class_def, space_sigma_list, MAP_MAP_o, o_DEF, SUBSET_DEF, IN_POW])
  >> ONCE_REWRITE_TAC[SUBSET_DEF] >> simp[IN_POW]
  >> qx_gen_tac ‘s’ >> strip_tac
  >> ‘FINITE (cross_list ds)’ by simp[finite_cross_list]
  >> ‘FINITE s’ by metis_tac[SUBSET_FINITE]
  >> qpat_x_assum ‘s ⊆ cross_list ds’ mp_tac
  >> qpat_x_assum ‘FINITE s’ mp_tac
  >> qid_spec_tac ‘s’
  >> ho_match_mp_tac FINITE_INDUCT
  >> conj_tac
  >- (strip_tac >> irule SIGMA_ALGEBRA_EMPTY >> simp[])
  >> rpt strip_tac
  >> ‘e ∈ cross_list ds ∧ s ⊆ cross_list ds’ by gvs[INSERT_SUBSET]
  >> ‘e INSERT s = {e} ∪ s’ by simp[Once INSERT_SING_UNION]
  >> pop_assum SUBST1_TAC
  >> irule SIGMA_ALGEBRA_UNION
  >> simp[]
  >> irule singleton_in_subsets_sigma_list
  >> drule length_in_cross_list >> strip_tac >> simp[EL_MAP, IN_POW, SUBSET_DEF]
  >> rw[] >> irule in_cross_list_el >> simp[]
QED

(* Specialization of sigma_list_pow to REPLICATE n (Y, POW Y).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem sigma_list_replicate_pow:
  ∀(Y : α -> bool) n.
    FINITE Y ⇒
    sigma_list (REPLICATE n (Y, POW Y)) =
      (cross_list (REPLICATE n Y), POW (cross_list (REPLICATE n Y)))
Proof
  rpt strip_tac
  >> Know ‘REPLICATE n (Y, POW Y) = MAP (λd. (d, POW d)) (REPLICATE n Y)’
  >- (Induct_on ‘n’ >> ASM_REWRITE_TAC[REPLICATE, MAP] >> BETA_TAC >> REFL_TAC)
  >> disch_then SUBST1_TAC
  >> irule sigma_list_pow
  >> Induct_on ‘n’ >> ASM_REWRITE_TAC[REPLICATE, EVERY_DEF]
QED

(* Non-negativity of prod_list probability measure on arbitrary subsets.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem prob_prod_list_pos:
  ∀(ml : α m_space list) s.
    EVERY prob_space ml ⇒ 0 ≤ prob (prod_list ml) s
Proof
  Induct_on ‘ml’
  >- simp[prod_list_def, prob_def, INDICATOR_FN_POS]
  >> rw[prod_list_def, prob_def, general_prod_measure_space_def,
        measure_def, general_prod_measure_def]
  >> ‘prob_space (prod_list ml)’ by simp[prob_space_prod_list]
  >> ‘measure_space h ∧ measure_space (prod_list ml)’ by gvs[prob_space_def]
  >> irule pos_fn_integral_pos
  >> simp[]
  >> rw[]
  >> irule pos_fn_integral_pos
  >> simp[INDICATOR_FN_POS]
QED

(* Singleton measurability and product probability formula for prod_list.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem prob_prod_list_singleton:
  ∀(ml : α m_space list) (ys : α list).
    EVERY prob_space ml ∧
    LENGTH ys = LENGTH ml ∧
    (∀i. i < LENGTH ml ⇒ {EL i ys} ∈ events (EL i ml)) ⇒
    {ys} ∈ events (prod_list ml) ∧
    prob (prod_list ml) {ys} =
      ∏ (λi. prob (EL i ml) {EL i ys}) (count (LENGTH ml))
Proof
  Induct_on ‘ml’ >> Cases_on ‘ys’ >> simp[]
  >- simp[prod_list_def, events_def, prob_def, IN_POW, SUBSET_DEF, indicator_fn_def]
  >> rpt gen_tac >> strip_tac
  >> rename1 ‘{y :: ys} ∈ events (prod_list (m0 :: ml))’
  >> ‘{y} ∈ events m0’ by (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[])
  >> Know ‘∀i. i < LENGTH ml ⇒ {EL i ys} ∈ events (EL i ml)’
  >- (rw[] >> first_x_assum (qspec_then ‘SUC i’ mp_tac) >> simp[])
  >> strip_tac
  >> first_x_assum (qspec_then ‘ys’ mp_tac) >> simp[] >> strip_tac
  >> ‘prob_space (prod_list ml)’ by simp[prob_space_prod_list]
  >> Know ‘{y :: ys} = general_cross CONS {y} {ys}’
  >- simp[EXTENSION, IN_general_cross]
  >> strip_tac
  >> conj_tac
  >- (simp[prod_list_def, events_general_prod_measure_space, general_sigma_def]
      >> irule IN_SIGMA >> simp[IN_general_prod]
      >> qexistsl [‘{y}’, ‘{ys}’]
      >> gvs[events_def])
  >> simp[prod_list_def, EXTREAL_PROD_IMAGE_COUNT_SUC_LEFT]
  >> simp[prob_def, general_prod_measure_space]
  >> Know ‘general_prod_measure CONS m0 (prod_list ml) (general_cross CONS {y} {ys}) =
           measure m0 {y} * measure (prod_list ml) {ys}’
  >- (irule general_prod_measure_rect
      >> gvs[prob_space_def, events_def]
      >> irule_at Any pair_operation_CONS)
  >> gvs[prob_def]
QED

(* Singleton product transition probability theorem for repeat_channel.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_repeat_channel_singleton:
  ∀(W : (α, β) memoryless_channel) N xs ys.
    LENGTH xs = N ∧ LENGTH ys = N ∧
    EVERY (λx. x ∈ mcdomain W) xs ∧
    (∀i. i < N ⇒ {EL i ys} ∈ mcevents W) ⇒
    mcchannel (repeat_channel W N) xs {ys} =
      ∏ (λi. mcchannel W (EL i xs) {EL i ys}) (count N)
Proof
  rpt strip_tac
  >> simp[repeat_channel_accessors]
  >> qabbrev_tac ‘ml = MAP (mcprob_space W) xs’
  >> ‘LENGTH ml = N’ by simp[Abbr ‘ml’]
  >> Know ‘EVERY prob_space ml’
  >- (simp[Abbr ‘ml’, EVERY_MAP]
      >> gvs[EVERY_MEM, memoryless_channel_wf_prob_space_property])
  >> Know ‘∀i. i < LENGTH ml ⇒ {EL i ys} ∈ events (EL i ml)’
  >- (simp[Abbr ‘ml’, EL_MAP, mcprob_space_alt, events_def])
  >> rpt strip_tac
  >> Know ‘LENGTH ys = LENGTH ml’ >- simp[]
  >> strip_tac
  >> drule_all prob_prod_list_singleton >> strip_tac
  >> simp[]
  >> irule EXTREAL_PROD_IMAGE_EQ
  >> simp[Abbr ‘ml’, EL_MAP, mcprob_space_alt, prob_def]
QED

(* -------------------------------------------------------------------------- *)
(* Block 3: combine_channel Accessors, Arikan Eq. (4), & Step Factorizations  *)
(* -------------------------------------------------------------------------- *)

(* Input domain of combine_channel W N under wf_bdmc W.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcdomain_combine_channel:
  ∀(W : (bool, β) memoryless_channel) N.
    wf_bdmc W ⇒ mcdomain (combine_channel W N) = length_n_codes N
Proof
  rpt strip_tac
  >> drule (iffLR wf_bdmc_def) >> strip_tac
  >> simp[combine_channel_alt, polar_encode_channel_def,
          transform_input_channel_accessors, repeat_channel_accessors]
  >> simp[EXTENSION, in_cross_list_replicate, polar_encode_length_any]
  >> gen_tac >> EQ_TAC >> strip_tac >> simp[EVERY_MEM]
  >> rw[] >> qpat_x_assum ‘mcdomain W = _’ SUBST1_TAC >> simp[]
QED

(* Output sigma-algebra of combine_channel W N under wf_bdmc W.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcsigma_combine_channel:
  ∀(W : (bool, β) memoryless_channel) N.
    wf_bdmc W ⇒
    mcsigma (combine_channel W N) =
      (cross_list (REPLICATE N (mccodomain W)),
       POW (cross_list (REPLICATE N (mccodomain W))))
Proof
  rpt strip_tac
  >> drule wf_bdmc_mcsigma
  >> gvs[wf_bdmc_def, combine_channel_alt, polar_encode_channel_def,
         transform_input_channel_accessors, repeat_channel_accessors]
  >> disch_then SUBST1_TAC
  >> simp[sigma_list_replicate_pow]
QED

(* Output codomain of combine_channel W N under wf_bdmc W.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mccodomain_combine_channel:
  ∀(W : (bool, β) memoryless_channel) N.
    wf_bdmc W ⇒
    mccodomain (combine_channel W N) =
      cross_list (REPLICATE N (mccodomain W))
Proof
  rpt strip_tac
  >> gvs[combine_channel_alt, polar_encode_channel_def,
         transform_input_channel_accessors, repeat_channel_accessors]
QED

(* Output events of combine_channel W N under wf_bdmc W.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcevents_combine_channel:
  ∀(W : (bool, β) memoryless_channel) N.
    wf_bdmc W ⇒
    mcevents (combine_channel W N) =
      POW (cross_list (REPLICATE N (mccodomain W)))
Proof
  rpt strip_tac
  >> drule_then (qspec_then ‘N’ mp_tac) mcsigma_combine_channel
  >> simp[mcsigma_alt]
QED

(* Output probability space of combine_channel W N on any u of length N under wf_bdmc W.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem prob_space_combine_channel:
  ∀(W : (bool, β) memoryless_channel) N u.
    wf_bdmc W ∧ LENGTH u = N ⇒
    prob_space (cross_list (REPLICATE N (mccodomain W)),
                POW (cross_list (REPLICATE N (mccodomain W))),
                mcchannel (combine_channel W N) u)
Proof
  rpt strip_tac
  >> qspecl_then [‘combine_channel W N’, ‘u’] mp_tac
       memoryless_channel_wf_prob_space_property
  >> simp[mcdomain_combine_channel, mccodomain_combine_channel,
          mcevents_combine_channel, mcprob_space_alt]
QED

(* Non-negativity of mcchannel (combine_channel W N) u s for arbitrary u and s under wf_bdmc W.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_combine_channel_pos:
  ∀(W : (bool, β) memoryless_channel) N u s.
    wf_bdmc W ⇒ 0 ≤ mcchannel (combine_channel W N) u s
Proof
  rpt strip_tac
  >> simp[combine_channel_alt, polar_encode_channel_def,
          transform_input_channel_accessors, repeat_channel_accessors]
  >> irule prob_prod_list_pos
  >> simp[EVERY_MAP, EVERY_MEM]
  >> rpt strip_tac
  >> irule memoryless_channel_wf_prob_space_property
  >> fs[wf_bdmc_def]
QED

(* Combined structural accessors, probability space, and non-negativity for combine_channel W N.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem combine_channel_bdmc_props:
  ∀(W : (bool, β) memoryless_channel) N.
    wf_bdmc W ⇒
    mcdomain (combine_channel W N) = length_n_codes N ∧
    mccodomain (combine_channel W N) = cross_list (REPLICATE N (mccodomain W)) ∧
    mcevents (combine_channel W N) = POW (cross_list (REPLICATE N (mccodomain W))) ∧
    (∀u. LENGTH u = N ⇒
         prob_space (cross_list (REPLICATE N (mccodomain W)),
                     POW (cross_list (REPLICATE N (mccodomain W))),
                     mcchannel (combine_channel W N) u)) ∧
    (∀u s. 0 ≤ mcchannel (combine_channel W N) u s)
Proof
  rpt strip_tac
  >- simp[mcdomain_combine_channel]
  >- simp[mccodomain_combine_channel]
  >- simp[mcevents_combine_channel]
  >- simp[prob_space_combine_channel]
  >- simp[mcchannel_combine_channel_pos]
QED

(* Unpacked domain, codomain, events, and channel of combine_channel W (2 ** n) under wf_bdmc W.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem combine_channel_bdmc_accessors:
  ∀(W : (bool, β) memoryless_channel) n.
    wf_bdmc W ⇒
    mcdomain (combine_channel W (2 ** n)) = length_n_codes (2 ** n) ∧
    mcsigma (combine_channel W (2 ** n)) =
      sigma_list (REPLICATE (2 ** n) (mcsigma W)) ∧
    mccodomain (combine_channel W (2 ** n)) =
      cross_list (REPLICATE (2 ** n) (mccodomain W)) ∧
    mcevents (combine_channel W (2 ** n)) =
      POW (cross_list (REPLICATE (2 ** n) (mccodomain W))) ∧
    mcchannel (combine_channel W (2 ** n)) =
      (λu. prob (prod_list (MAP (mcprob_space W) (polar_encode u))))
Proof
  rpt strip_tac
  >- simp[mcdomain_combine_channel]
  >- simp[combine_channel_alt, polar_encode_channel_def,
          transform_input_channel_accessors, repeat_channel_accessors]
  >- simp[mccodomain_combine_channel]
  >- simp[mcevents_combine_channel]
  >- simp[combine_channel_alt, polar_encode_channel_def,
          transform_input_channel_accessors, repeat_channel_accessors, FUN_EQ_THM]
QED

(* General-N singleton product transition probability of combine_channel W N.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_combine_channel_singleton_gen:
  ∀(W : (bool, β) memoryless_channel) N u y.
    wf_bdmc W ∧ LENGTH u = N ∧ LENGTH y = N ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    mcchannel (combine_channel W N) u {y} =
      ∏ (λi. mcchannel W (EL i (polar_encode u)) {EL i y}) (count N)
Proof
  rpt strip_tac
  >> simp[combine_channel_alt, polar_encode_channel_def,
          transform_input_channel_accessors]
  >> irule mcchannel_repeat_channel_singleton
  >> gvs[wf_bdmc_def, polar_encode_length_any, EVERY_EL, IN_POW, SUBSET_DEF]
QED

(* Arikan Eq. (4): Singleton transition probability of combine_channel W (2 ** n).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_combine_channel_singleton:
  ∀(W : (bool, β) memoryless_channel) n u y.
    wf_bdmc W ∧ LENGTH u = 2 ** n ∧ LENGTH y = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    mcchannel (combine_channel W (2 ** n)) u {y} =
      ∏ (λi. mcchannel W (EL i (polar_encode u)) {EL i y}) (count (2 ** n))
Proof
  rpt strip_tac >> irule mcchannel_combine_channel_singleton_gen >> simp[]
QED

(* Singleton transition probabilities of combine_channel W N lie in [0, 1] and are Normal.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_combine_channel_singleton_normal_gen:
  ∀(W : (bool, β) memoryless_channel) N u y.
    wf_bdmc W ∧ LENGTH u = N ∧ LENGTH y = N ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    0 ≤ mcchannel (combine_channel W N) u {y} ∧
    mcchannel (combine_channel W N) u {y} ≤ 1 ∧
    ∃r. 0 ≤ r ∧ r ≤ 1 ∧ mcchannel (combine_channel W N) u {y} = Normal r
Proof
  rpt strip_tac
  >> drule_all prob_space_combine_channel >> strip_tac
  >> drule prob_normal
  >> disch_then (qspec_then ‘{y}’ mp_tac)
  >> simp[events_def, prob_def, IN_POW, SUBSET_DEF, in_cross_list_replicate]
  >> strip_tac
  >> simp[extreal_of_num_def, extreal_le_eq]
  >> qexists ‘r’ >> simp[]
QED

(* Power-of-two specialization: singleton transition probabilities of combine_channel W (2 ** n)
   lie in [0, 1] and are Normal.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_combine_channel_singleton_normal:
  ∀(W : (bool, β) memoryless_channel) n u y.
    wf_bdmc W ∧ LENGTH u = 2 ** n ∧ LENGTH y = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    0 ≤ mcchannel (combine_channel W (2 ** n)) u {y} ∧
    mcchannel (combine_channel W (2 ** n)) u {y} ≤ 1 ∧
    ∃r. 0 ≤ r ∧ r ≤ 1 ∧ mcchannel (combine_channel W (2 ** n)) u {y} = Normal r
Proof
  rpt strip_tac
  >> qspecl_then [‘W’, ‘2 ** n’, ‘u’, ‘y’] mp_tac
       mcchannel_combine_channel_singleton_normal_gen
  >> simp[]
QED

(* Recursive step factorization of combine_channel W (2 * 2 ** n) on concatenated outputs y1 ++ y2.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_combine_channel_step:
  ∀(W : (bool, β) memoryless_channel) n u y1 y2.
    wf_bdmc W ∧ LENGTH u = 2 * 2 ** n ∧
    LENGTH y1 = 2 ** n ∧ LENGTH y2 = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y1 ∧
    EVERY (λyi. yi ∈ mccodomain W) y2 ⇒
    mcchannel (combine_channel W (2 * 2 ** n)) u {y1 ++ y2} =
      mcchannel (combine_channel W (2 ** n))
        (bxor (EL 0 (deinterleave 2 u)) (EL 1 (deinterleave 2 u))) {y1} *
      mcchannel (combine_channel W (2 ** n))
        (EL 1 (deinterleave 2 u)) {y2}
Proof
  rpt strip_tac
  >> ‘0n < 2 ** n’ by simp[]
  >> ‘¬(LENGTH u ≤ 1)’ by simp[]
  >> drule length_deinterleave_2_half
  >> simp[deinterleave_2_eq] >> strip_tac
  >> qabbrev_tac ‘u_even = get_every_nth_element u 2 0’
  >> qabbrev_tac ‘u_odd = get_every_nth_element u 2 1’
  >> ‘LENGTH (bxor u_even u_odd) = 2 ** n’ by simp[bxor_length]
  >> qabbrev_tac ‘v1 = bxor u_even u_odd’
  >> qabbrev_tac ‘v2 = u_odd’
  >> Know ‘polar_encode u = polar_encode v1 ++ polar_encode v2’
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [polar_encode_def]))
      >> simp[LET_THM, deinterleave_2_eq, Abbr ‘v1’, Abbr ‘v2’, Abbr ‘u_even’, Abbr ‘u_odd’])
  >> strip_tac
  >> ‘LENGTH (polar_encode v1) = 2 ** n ∧ LENGTH (polar_encode v2) = 2 ** n’
       by simp[polar_encode_length_any]
  >> qspecl_then [‘W’, ‘SUC n’, ‘u’, ‘y1 ++ y2’] mp_tac mcchannel_combine_channel_singleton
  >> simp[EXP] >> disch_then kall_tac
  >> qspecl_then [‘W’, ‘n’, ‘v1’, ‘y1’] mp_tac mcchannel_combine_channel_singleton
  >> qspecl_then [‘W’, ‘n’, ‘v2’, ‘y2’] mp_tac mcchannel_combine_channel_singleton
  >> simp[deinterleave_2_eq]
  >> ntac 2 (disch_then kall_tac)
  >> Know ‘count (2 * 2 ** n) =
           count (2 ** n) ∪ IMAGE (λi. i + 2 ** n) (count (2 ** n))’
  >- (simp[EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac
      >- (Cases_on ‘x < 2 ** n’ >- simp[]
          >> disj2_tac >> qexists ‘x - 2 ** n’ >> simp[])
      >> simp[])
  >> disch_then SUBST1_TAC
  >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_PROD_IMAGE_DISJOINT_UNION]
  >> conj_tac >- (simp[DISJOINT_DEF, EXTENSION] >> gen_tac >> DECIDE_TAC)
  >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_PROD_IMAGE_IMAGE]
  >> conj_tac >- simp[INJ_DEF]
  >> simp[o_DEF]
  >> Know ‘∏ (λi. mcchannel W (EL i (polar_encode v1 ++ polar_encode v2))
                              {EL i (y1 ++ y2)}) (count (2 ** n)) =
           ∏ (λi. mcchannel W (EL i (polar_encode v1)) {EL i y1}) (count (2 ** n))’
  >- (irule EXTREAL_PROD_IMAGE_EQ >> simp[EL_APPEND_EQN])
  >> disch_then SUBST1_TAC
  >> Know ‘∏ (λi. mcchannel W (EL (i + 2 ** n) (polar_encode v1 ++ polar_encode v2))
                              {EL (i + 2 ** n) (y1 ++ y2)}) (count (2 ** n)) =
           ∏ (λi. mcchannel W (EL i (polar_encode v2)) {EL i y2}) (count (2 ** n))’
  >- (irule EXTREAL_PROD_IMAGE_EQ >> simp[EL_APPEND_EQN])
  >> disch_then SUBST1_TAC
  >> simp[Abbr ‘v1’, Abbr ‘v2’, Abbr ‘u_even’, Abbr ‘u_odd’]
QED

(* TAKE/DROP form of recursive step factorization for outputs y of length 2 * 2 ** n.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_combine_channel_double:
  ∀(W : (bool, β) memoryless_channel) n u y.
    wf_bdmc W ∧ LENGTH u = 2 * 2 ** n ∧ LENGTH y = 2 * 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    mcchannel (combine_channel W (2 * 2 ** n)) u {y} =
      mcchannel (combine_channel W (2 ** n))
        (bxor (EL 0 (deinterleave 2 u)) (EL 1 (deinterleave 2 u)))
        {TAKE (2 ** n) y} *
      mcchannel (combine_channel W (2 ** n))
        (EL 1 (deinterleave 2 u))
        {DROP (2 ** n) y}
Proof
  rpt strip_tac
  >> qabbrev_tac ‘y1 = TAKE (2 ** n) y’
  >> qabbrev_tac ‘y2 = DROP (2 ** n) y’
  >> ‘y = y1 ++ y2’ by simp[Abbr ‘y1’, Abbr ‘y2’, TAKE_DROP]
  >> ‘LENGTH y1 = 2 ** n ∧ LENGTH y2 = 2 ** n’
       by simp[Abbr ‘y1’, Abbr ‘y2’, LENGTH_TAKE, LENGTH_DROP]
  >> ‘EVERY (λyi. yi ∈ mccodomain W) y1 ∧ EVERY (λyi. yi ∈ mccodomain W) y2’
       by metis_tac[EVERY_APPEND]
  >> qpat_x_assum ‘y = y1 ++ y2’
       (fn th => CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [th]))))
  >> irule mcchannel_combine_channel_step >> simp[]
QED

(* Base case N = 1 (n = 0) singleton transition probability of combine_channel.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_combine_channel_1:
  ∀(W : (bool, β) memoryless_channel) b y.
    wf_bdmc W ∧ y ∈ mccodomain W ⇒
    mcchannel (combine_channel W 1) [b] {[y]} = mcchannel W b {y}
Proof
  rpt strip_tac
  >> qspecl_then [‘W’, ‘0’, ‘[b]’, ‘[y]’] mp_tac mcchannel_combine_channel_singleton
  >> simp[Once polar_encode_def]
QED

(* Arikan Eq. (3): Base step N = 2 (n = 1) singleton transition probability of combine_channel.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_combine_channel_2:
  ∀(W : (bool, β) memoryless_channel) u0 u1 y0 y1.
    wf_bdmc W ∧ y0 ∈ mccodomain W ∧ y1 ∈ mccodomain W ⇒
    mcchannel (combine_channel W 2) [u0; u1] {[y0; y1]} =
      mcchannel W (u0 ⇎ u1) {y0} * mcchannel W u1 {y1}
Proof
  rpt strip_tac
  >> qspecl_then [‘W’, ‘0’, ‘[u0; u1]’, ‘[y0]’, ‘[y1]’] mp_tac mcchannel_combine_channel_step
  >> simp[deinterleave_2_eq, get_every_nth_element_def]
  >> PURE_ONCE_REWRITE_TAC[ONE]
  >> simp[get_every_nth_element_def, mcchannel_combine_channel_1]
QED

(* -------------------------------------------------------------------------- *)
(* Block 4: Finite-Powerset Append Measure & Recursive Channel Combining      *)
(* -------------------------------------------------------------------------- *)

(* Positive-function integral over a finite powerset measure space reduces to a finite sum.
   Adapted from JY-utils/mc_taxonomyScript.sml; written and verified by Gemini (Google DeepMind AI agent) *)
Theorem finite_space_POW_pos_fn_integral_reduce:
  ∀m f.
    measure_space m ∧ POW (m_space m) = measurable_sets m ∧
    FINITE (m_space m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ⇒
    ∫⁺ m f = ∑ (λx. f x * measure m {x}) (m_space m)
Proof
  rpt strip_tac
  >> ‘∀x. x ∈ m_space m ⇒ {x} ∈ measurable_sets m’
       by (rw[] >> ‘{x} ∈ POW (m_space m)’ suffices_by metis_tac[]
           >> simp[IN_POW, SUBSET_DEF])
  >> ‘sigma_algebra (measurable_space m)’ by metis_tac[MEASURE_SPACE_SIGMA_ALGEBRA]
  >> Know ‘∀t. t ∈ m_space m ⇒
               ∑ (λx. f x * indicator_fn {x} t) (m_space m) = f t’
  >- (rpt strip_tac
      >> ‘m_space m = t INSERT (m_space m DELETE t)’ by metis_tac[INSERT_DELETE]
      >> pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th])))
      >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_PROPERTY]
      >> conj_tac
      >- (conj_tac >- simp[]
          >> disj1_tac >> rw[] >> irule pos_not_neginf >> irule le_mul
          >> simp[INDICATOR_FN_POS] >> gs[IN_INSERT, IN_DELETE])
      >> simp[DELETE_DELETE]
      >> Know ‘∑ (λx. f x * indicator_fn {x} t) (m_space m DELETE t) = 0’
      >- (irule EXTREAL_SUM_IMAGE_0 >> simp[] >> rw[]
          >> ‘indicator_fn {x} t = 0’ by (rw[indicator_fn_def] >> gs[IN_DELETE])
          >> simp[])
      >> simp[indicator_fn_def])
  >> strip_tac
  >> Know ‘∫⁺ m f = ∫⁺ m (λt. ∑ (λx. f x * indicator_fn {x} t) (m_space m))’
  >- (irule pos_fn_integral_cong >> rpt conj_tac
      >- (rw[] >> irule EXTREAL_SUM_IMAGE_POS >> rw[] >> irule le_mul
          >> simp[INDICATOR_FN_POS] >> gs[])
      >- simp[] >- (rw[] >> metis_tac[]) >- simp[])
  >> disch_then SUBST1_TAC
  >> Know ‘∫⁺ m (λt. ∑ (λx. f x * indicator_fn {x} t) (m_space m)) =
           ∑ (λx. ∫⁺ m (λt. f x * indicator_fn {x} t)) (m_space m)’
  >- (ho_match_mp_tac pos_fn_integral_sum >> rpt conj_tac
      >- gs[] >- gs[]
      >- (rw[] >> irule le_mul >> simp[INDICATOR_FN_POS] >> gs[])
      >- (rw[] >> ho_match_mp_tac IN_MEASURABLE_BOREL_MUL_INDICATOR
          >> gs[subsets_def] >> irule IN_MEASURABLE_BOREL_CONST' >> gs[]))
  >> disch_then SUBST1_TAC
  >> irule EXTREAL_SUM_IMAGE_EQ >> rpt conj_tac
  >- (rw[] >> irule pos_fn_integral_cmul_indicator_general >> gs[])
  >- gs[]
  >- (disj1_tac >> rw[]
      >- (irule pos_not_neginf >> irule pos_fn_integral_pos >> rw[]
          >> irule le_mul >> simp[INDICATOR_FN_POS] >> gs[])
      >- (irule pos_not_neginf >> irule le_mul >> gs[MEASURE_POSITIVE]))
QED

(* Predicate for a finite powerset probability space.
   Written by Gemini (Google DeepMind AI agent) *)
Definition finite_pow_prob_space_def:
  finite_pow_prob_space (m : α m_space) ⇔
    prob_space m ∧ FINITE (m_space m) ∧ measurable_sets m = POW (m_space m)
End

(* prod_list preserves finite_pow_prob_space.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem finite_pow_prob_space_prod_list:
  ∀ml : α m_space list.
    EVERY finite_pow_prob_space ml ⇒
    finite_pow_prob_space (prod_list ml)
Proof
  rw[finite_pow_prob_space_def]
  >- (irule prob_space_prod_list >> gvs[EVERY_MEM, finite_pow_prob_space_def])
  >- (simp[m_space_prod_list] >> irule finite_cross_list
      >> gvs[EVERY_MAP, EVERY_MEM, finite_pow_prob_space_def])
  >> simp[measurable_sets_prod_list, m_space_prod_list]
  >> Know ‘MAP (λl. (m_space l, measurable_sets l)) ml =
           MAP (λd. (d, POW d)) (MAP m_space ml)’
  >- (gvs[MAP_MAP_o, MAP_EQ_f, EVERY_MEM, finite_pow_prob_space_def])
  >> disch_then SUBST1_TAC
  >> DEP_PURE_ONCE_REWRITE_TAC[sigma_list_pow]
  >> gvs[EVERY_MAP, EVERY_MEM, finite_pow_prob_space_def]
QED

(* prod_list measure ignores elements outside m_space (prod_list ml).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem measure_prod_list_inter_space:
  ∀(ml : α m_space list) S.
    EVERY prob_space ml ⇒
    measure (prod_list ml) S =
      measure (prod_list ml) (S ∩ m_space (prod_list ml))
Proof
  Cases_on ‘ml’
  >- (rw[prod_list_def, measure_def, m_space_def, indicator_fn_def])
  >> rw[prod_list_def, general_prod_measure_space_def, general_prod_measure_def,
        measure_def, m_space_def]
  >> ‘prob_space (prod_list t)’ by simp[prob_space_prod_list]
  >> ‘measure_space h ∧ measure_space (prod_list t)’ by gvs[prob_space_def]
  >> ho_match_mp_tac pos_fn_integral_cong
  >> simp[]
  >> conj_tac >- (rw[] >> irule pos_fn_integral_pos >> simp[INDICATOR_FN_POS])
  >> conj_tac >- (rw[] >> irule pos_fn_integral_pos >> simp[INDICATOR_FN_POS])
  >> rw[]
  >> ho_match_mp_tac pos_fn_integral_cong
  >> simp[INDICATOR_FN_POS]
  >> rw[indicator_fn_def, IN_general_cross]
  >> gvs[]
QED

(* Integral of an arbitrary indicator function over prod_list equals measure (prod_list ml) S.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem pos_fn_integral_prod_list_indicator:
  ∀(ml : α m_space list) S.
    EVERY finite_pow_prob_space ml ⇒
    ∫⁺ (prod_list ml) (indicator_fn S) = measure (prod_list ml) S
Proof
  rpt strip_tac
  >> drule finite_pow_prob_space_prod_list
  >> simp[finite_pow_prob_space_def] >> strip_tac
  >> ‘EVERY prob_space ml’ by gvs[EVERY_MEM, finite_pow_prob_space_def]
  >> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [UNDISCH (SPEC_ALL measure_prod_list_inter_space)]))
  >> Know ‘∫⁺ (prod_list ml) (indicator_fn S) =
           ∫⁺ (prod_list ml) (indicator_fn (S ∩ m_space (prod_list ml)))’
  >- (ho_match_mp_tac pos_fn_integral_cong >> gvs[prob_space_def, INDICATOR_FN_POS, indicator_fn_def])
  >> disch_then SUBST1_TAC
  >> irule pos_fn_integral_indicator
  >> gvs[prob_space_def, IN_POW, INTER_SUBSET]
QED

(* Symmetry normalization for extreal infinity disequalities arising from CMUL lemmas.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem neq_infty_sym[local]:
  ∀x : extreal. (+∞ ≠ x ⇔ x ≠ +∞) ∧ (−∞ ≠ x ⇔ x ≠ −∞)
Proof
  metis_tac[]
QED

(* Product measure of concatenated finite powerset prod_list spaces equals general_prod_measure ($++).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem prod_list_append_measure:
  ∀(ml1 ml2 : α m_space list) S.
    EVERY finite_pow_prob_space ml1 ∧
    EVERY finite_pow_prob_space ml2 ⇒
    measure (prod_list (ml1 ++ ml2)) S =
      general_prod_measure ($++) (prod_list ml1) (prod_list ml2) S
Proof
  Induct_on ‘ml1’
  >- (rw[general_prod_measure_def]
      >> drule finite_pow_prob_space_prod_list >> strip_tac
      >> ‘measure_space (prod_list ml2)’ by gvs[finite_pow_prob_space_def, prob_space_def]
      >> Know ‘∫⁺ (prod_list ml2)
                 (λy2. ∫⁺ (prod_list []) (λy1. indicator_fn S (y1 ++ y2))) =
               ∫⁺ (prod_list ml2) (indicator_fn S)’
      >- (ho_match_mp_tac pos_fn_integral_cong
          >> simp[INDICATOR_FN_POS]
          >> conj_tac
          >- (rw[] >> irule pos_fn_integral_pos
              >> simp[INDICATOR_FN_POS]
              >> mp_tac (Q.SPEC ‘[]’ prob_space_prod_list) >> simp[prob_space_def])
          >> rw[]
          >> Know ‘finite_pow_prob_space (prod_list ([] : α m_space list))’
          >- (irule finite_pow_prob_space_prod_list >> simp[])
          >> simp[finite_pow_prob_space_def] >> strip_tac
          >> DEP_PURE_ONCE_REWRITE_TAC[finite_space_POW_pos_fn_integral_reduce]
          >> gvs[prob_space_def, INDICATOR_FN_POS]
          >> simp[prod_list_def, m_space_def, measure_def, indicator_fn_def])
      >> disch_then SUBST1_TAC
      >> simp[pos_fn_integral_prod_list_indicator])
  >> rpt gen_tac >> strip_tac
  >> gvs[]
  >> qabbrev_tac ‘M1 = prod_list ml1’
  >> qabbrev_tac ‘M2 = prod_list ml2’
  >> qabbrev_tac ‘M12 = prod_list (ml1 ++ ml2)’
  >> ‘finite_pow_prob_space h ∧ finite_pow_prob_space M1 ∧
      finite_pow_prob_space M2 ∧ finite_pow_prob_space M12’
       by (rpt conj_tac >> simp[Abbr ‘M1’, Abbr ‘M2’, Abbr ‘M12’]
           >> irule finite_pow_prob_space_prod_list >> simp[])
  >> ‘measure_space h ∧ measure_space M1 ∧ measure_space M2 ∧ measure_space M12’
       by gvs[finite_pow_prob_space_def, prob_space_def]
  >> qabbrev_tac ‘f = λz. ∫⁺ h (λyh. indicator_fn S (yh :: z))’
  >> ‘∀z. 0 ≤ f z’ by (rw[Abbr ‘f’] >> irule pos_fn_integral_pos >> simp[INDICATOR_FN_POS])
  >> Know ‘∀z. f z ≠ +∞ ∧ f z ≠ −∞’
  >- (gen_tac >> conj_tac
      >- (simp[Abbr ‘f’, lt_infty]
          >> irule let_trans >> qexists ‘∫⁺ h (λyh. Normal 1)’
          >> conj_tac
          >- (irule pos_fn_integral_mono >> simp[INDICATOR_FN_POS, normal_1, INDICATOR_FN_LE_1])
          >> DEP_PURE_ONCE_REWRITE_TAC[pos_fn_integral_const]
          >> gvs[finite_pow_prob_space_def, prob_space_def, prob_def, normal_1])
      >> irule pos_not_neginf >> simp[])
  >> strip_tac
  >> Know ‘measure (prod_list (h :: (ml1 ++ ml2))) S = ∫⁺ M12 f’
  >- simp[prod_list_def, general_prod_measure_space_def, measure_def, Abbr ‘M12’, Abbr ‘f’]
  >> disch_then SUBST1_TAC
  >> Know ‘general_prod_measure ($++) (prod_list (h :: ml1)) M2 S =
           ∫⁺ M2 (λy2. ∫⁺ M1 (λyt. f (yt ++ y2)))’
  >- (simp[general_prod_measure_def]
      >> ho_match_mp_tac pos_fn_integral_cong >> simp[]
      >> conj_tac
      >- (rw[] >> irule pos_fn_integral_pos >> simp[INDICATOR_FN_POS]
          >> Know ‘finite_pow_prob_space (prod_list (h :: ml1))’
          >- (irule finite_pow_prob_space_prod_list >> simp[finite_pow_prob_space_def])
          >> simp[finite_pow_prob_space_def, prob_space_def])
      >> conj_tac >- (rw[] >> irule pos_fn_integral_pos >> simp[])
      >> qx_gen_tac ‘y2’ >> strip_tac
      >> Know ‘(λy1. indicator_fn S (y1 ++ y2)) = indicator_fn {y1 | y1 ++ y2 ∈ S}’
      >- simp[FUN_EQ_THM, indicator_fn_def]
      >> disch_then SUBST1_TAC
      >> DEP_PURE_ONCE_REWRITE_TAC[pos_fn_integral_prod_list_indicator]
      >> conj_tac >- simp[]
      >> simp[prod_list_def, general_prod_measure_space_def, measure_def,
              Abbr ‘M1’, Abbr ‘f’, indicator_fn_def])
  >> disch_then SUBST1_TAC
  >> DEP_PURE_REWRITE_TAC[finite_space_POW_pos_fn_integral_reduce]
  >> gvs[finite_pow_prob_space_def]
  >> conj_tac >- (rw[] >> irule pos_fn_integral_pos >> simp[])
  >> Know ‘∑ (λy2. ∫⁺ M1 (λyt. f (yt ++ y2)) * measure M2 {y2}) (m_space M2) =
           ∑ (λy2. (∑ (λyt. f (yt ++ y2) * measure M1 {yt}) (m_space M1)) * measure M2 {y2}) (m_space M2)’
  >- (ho_match_mp_tac EXTREAL_SUM_IMAGE_EQ' >> simp[] >> rw[]
      >> DEP_PURE_ONCE_REWRITE_TAC[finite_space_POW_pos_fn_integral_reduce]
      >> simp[])
  >> disch_then SUBST1_TAC
  >> Know ‘∑ (λz. f z * measure M12 {z}) (m_space M12) =
           ∑ (λz. ∑ (λy2. (∑ (λyt. (f z * indicator_fn {z} (yt ++ y2)) * measure M1 {yt})
                             (m_space M1)) * measure M2 {y2}) (m_space M2)) (m_space M12)’
  >- (ho_match_mp_tac EXTREAL_SUM_IMAGE_EQ' >> simp[]
      >> qx_gen_tac ‘z’ >> strip_tac
      >> Know ‘measure M12 {z} = general_prod_measure ($++) M1 M2 {z}’
      >- simp[Abbr ‘M1’, Abbr ‘M2’, Abbr ‘M12’]
      >> disch_then SUBST1_TAC
      >> simp[general_prod_measure_def]
      >> DEP_PURE_ONCE_REWRITE_TAC[finite_space_POW_pos_fn_integral_reduce]
      >> simp[]
      >> conj_tac >- (rw[] >> irule pos_fn_integral_pos >> simp[INDICATOR_FN_POS])
      >> Know ‘∑ (λy2. ∫⁺ M1 (λy1. indicator_fn {z} (y1 ++ y2)) * measure M2 {y2}) (m_space M2) =
               ∑ (λy2. (∑ (λyt. indicator_fn {z} (yt ++ y2) * measure M1 {yt}) (m_space M1)) * measure M2 {y2}) (m_space M2)’
      >- (ho_match_mp_tac EXTREAL_SUM_IMAGE_EQ' >> simp[] >> rw[]
          >> DEP_PURE_ONCE_REWRITE_TAC[finite_space_POW_pos_fn_integral_reduce]
          >> simp[INDICATOR_FN_POS])
      >> disch_then SUBST1_TAC
      >> DEP_PURE_ONCE_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_CMUL_L_ALT]
      >> conj_tac
      >- (simp[neq_infty_sym] >> disj1_tac >> gen_tac >> disch_tac >> irule pos_not_neginf
          >> irule le_mul >> simp[MEASURE_POSITIVE, IN_POW, SUBSET_DEF]
          >> irule EXTREAL_SUM_IMAGE_POS >> simp[le_mul, INDICATOR_FN_POS, MEASURE_POSITIVE, IN_POW, SUBSET_DEF])
      >> ho_match_mp_tac EXTREAL_SUM_IMAGE_EQ' >> simp[]
      >> qx_gen_tac ‘y2’ >> strip_tac
      >> simp[mul_assoc]
      >> AP_THM_TAC >> AP_TERM_TAC
      >> DEP_PURE_ONCE_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_CMUL_L_ALT]
      >> conj_tac
      >- (simp[neq_infty_sym] >> disj1_tac >> gen_tac >> disch_tac >> irule pos_not_neginf
          >> irule le_mul >> simp[INDICATOR_FN_POS, MEASURE_POSITIVE, IN_POW, SUBSET_DEF])
      >> ho_match_mp_tac EXTREAL_SUM_IMAGE_EQ' >> simp[mul_assoc])
  >> disch_then SUBST1_TAC
  >> DEP_PURE_ONCE_REWRITE_TAC[NESTED_EXTREAL_SUM_IMAGE_REVERSE]
  >> conj_tac
  >- (simp[neq_infty_sym] >> rpt gen_tac >> disch_tac >> irule pos_not_neginf
      >> irule le_mul >> simp[MEASURE_POSITIVE, IN_POW, SUBSET_DEF]
      >> irule EXTREAL_SUM_IMAGE_POS >> rw[] >> irule le_mul >> simp[MEASURE_POSITIVE, IN_POW, SUBSET_DEF]
      >> irule le_mul >> simp[INDICATOR_FN_POS])
  >> ho_match_mp_tac EXTREAL_SUM_IMAGE_EQ' >> simp[]
  >> qx_gen_tac ‘y2’ >> strip_tac
  >> ‘measure M2 {y2} ≠ +∞ ∧ measure M2 {y2} ≠ −∞’
       by (qspecl_then [‘M2’, ‘{y2}’] mp_tac PROB_FINITE >> gvs[prob_def, events_def, IN_POW, SUBSET_DEF])
  >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_CMUL_R_ALT]
  >> conj_tac
  >- (simp[neq_infty_sym] >> disj1_tac >> gen_tac >> disch_tac >> irule pos_not_neginf
      >> irule EXTREAL_SUM_IMAGE_POS >> rw[] >> irule le_mul >> simp[MEASURE_POSITIVE, IN_POW, SUBSET_DEF]
      >> irule le_mul >> simp[INDICATOR_FN_POS])
  >> AP_THM_TAC >> AP_TERM_TAC
  >> DEP_PURE_ONCE_REWRITE_TAC[NESTED_EXTREAL_SUM_IMAGE_REVERSE]
  >> conj_tac
  >- (simp[neq_infty_sym] >> rpt gen_tac >> disch_tac >> irule pos_not_neginf
      >> irule le_mul >> simp[MEASURE_POSITIVE, IN_POW, SUBSET_DEF]
      >> irule le_mul >> simp[INDICATOR_FN_POS])
  >> ho_match_mp_tac EXTREAL_SUM_IMAGE_EQ' >> simp[]
  >> qx_gen_tac ‘yt’ >> strip_tac
  >> ‘measure M1 {yt} ≠ +∞ ∧ measure M1 {yt} ≠ −∞’
       by (qspecl_then [‘M1’, ‘{yt}’] mp_tac PROB_FINITE >> gvs[prob_def, events_def, IN_POW, SUBSET_DEF])
  >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_CMUL_R_ALT]
  >> conj_tac
  >- (simp[neq_infty_sym] >> disj1_tac >> gen_tac >> disch_tac >> irule pos_not_neginf
      >> irule le_mul >> simp[INDICATOR_FN_POS])
  >> AP_THM_TAC >> AP_TERM_TAC
  >> Know ‘yt ++ y2 ∈ m_space M12’
  >- (gvs[Abbr ‘M1’, Abbr ‘M2’, Abbr ‘M12’, m_space_prod_list, append_in_cross_list])
  >> strip_tac
  >> ‘m_space M12 = (yt ++ y2) INSERT (m_space M12 DELETE (yt ++ y2))’
       by metis_tac[INSERT_DELETE]
  >> pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th])))
  >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_PROPERTY]
  >> conj_tac
  >- (simp[neq_infty_sym] >> disj1_tac >> gen_tac >> disch_tac >> irule pos_not_neginf
      >> irule le_mul >> simp[INDICATOR_FN_POS])
  >> simp[DELETE_DELETE, indicator_fn_def]
  >> Know ‘∑ (λy. f y * if yt ++ y2 = y then 1 else 0) (m_space M12 DELETE (yt ++ y2)) = 0’
  >- (irule EXTREAL_SUM_IMAGE_0 >> simp[])
  >> simp[]
QED

(* Representation of base channel W_1 (n = 0, N = 1) for recursive channel combining.
   On valid 1-bit inputs u = [b], applies W directly without polar_encode;
   outside length_n_codes 1, aligns with polar_encode_channel W 1 for HOL4 total-function extensionality.
   Written by Gemini (Google DeepMind AI agent) *)
Definition combine_channel_base0_def:
  combine_channel_base0 (W : (bool, β) memoryless_channel) =
    (length_n_codes 1 ∩ PREIMAGE HD (mcdomain W),
     sigma_list [mcsigma W],
     λu. if LENGTH u = 1
         then prob (prod_list [mcprob_space W (HD u)])
         else mcchannel (polar_encode_channel W 1) u)
    : (bool list -> bool) # (β list algebra) # (bool list -> β list measure)
End

(* Representation of single-step recursive channel combining W_{2^{n+1}} from two copies of W_{2^n}
   (Arikan Section I-B.1, Fig. 3): splits u into even_inputs and odd_inputs, feeds
   (bxor even_inputs odd_inputs) and odd_inputs into two independent copies of W_half,
   and concatenates their output vectors via general_prod_measure ($++).
   Written by Gemini (Google DeepMind AI agent) *)
Definition combine_channel_step0_def:
  combine_channel_step0 (W : (bool, β) memoryless_channel) (n : num)
    (W_half : (bool list, β list) memoryless_channel) =
    (length_n_codes (2 ** SUC n),
     sigma_list (REPLICATE (2 ** SUC n) (mcsigma W)),
     λu. if LENGTH u = 2 ** SUC n
         then
           let
             even_odd = deinterleave 2 u;
             u_even = EL 0 even_odd;
             u_odd = EL 1 even_odd
           in
             general_prod_measure ($++)
               (mcprob_space W_half (bxor u_even u_odd))
               (mcprob_space W_half u_odd)
         else mcchannel (polar_encode_channel W (2 ** SUC n)) u)
    : (bool list -> bool) # (β list algebra) # (bool list -> β list measure)
End

(* Genuine recursive channel combining W_{2^n} : (bool list, β list) memoryless_channel.
   Written by Gemini (Google DeepMind AI agent) *)
Definition recursive_combine_channel_def:
  recursive_combine_channel (W : (bool, β) memoryless_channel) 0 =
    memoryless_channel_ABS (combine_channel_base0 W) ∧
  recursive_combine_channel (W : (bool, β) memoryless_channel) (SUC n) =
    memoryless_channel_ABS
      (combine_channel_step0 W n (recursive_combine_channel W n))
End

(* Helper: mcprob_space of combine_channel W (2 ** n) on u of length 2 ** n equals prod_list.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcprob_space_combine_channel_eq_prod_list:
  ∀(W : (bool, β) memoryless_channel) n u.
    wf_bdmc W ∧ LENGTH u = 2 ** n ⇒
    mcprob_space (combine_channel W (2 ** n)) u =
      prod_list (MAP (mcprob_space W) (polar_encode u))
Proof
  rpt strip_tac
  >> drule combine_channel_bdmc_accessors
  >> disch_then (qspec_then ‘n’ strip_assume_tac)
  >> ‘LENGTH (polar_encode u) = 2 ** n’ by simp[polar_encode_length]
  >> irule PROB_SPACE_CONG_ALT
  >> simp[mcprob_space_alt, p_space_def, events_def, prob_def,
          m_space_prod_list, measurable_sets_prod_list]
  >> conj_tac
  >- (simp[MAP_MAP_o, o_DEF, mcprob_space_alt, m_space_def, MAP_CONST])
  >> Know ‘MAP (λl. (m_space l, measurable_sets l))
             (MAP (mcprob_space W) (polar_encode u)) =
           REPLICATE (2 ** n) (mcsigma W)’
  >- (simp[MAP_MAP_o, o_DEF, mcprob_space_alt, m_space_def, measurable_sets_def,
           GSYM mcsigma_alt, MAP_CONST])
  >> disch_then SUBST1_TAC
  >> gvs[wf_bdmc_def]
  >> Know ‘mcsigma W = (mccodomain W, POW (mccodomain W))’ >- simp[mcsigma_alt]
  >> disch_then SUBST1_TAC
  >> simp[sigma_list_replicate_pow, subsets_def]
QED

(* Equivalence of combine_channel W (2 ** n) and recursive_combine_channel W n (Roadmap Item 3).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem combine_channel_eq_recursive_combine:
  ∀(W : (bool, β) memoryless_channel) n.
    wf_bdmc W ⇒ combine_channel W (2 ** n) = recursive_combine_channel W n
Proof
  gen_tac >> Induct_on ‘n’
  >- (strip_tac >> simp[recursive_combine_channel_def]
      >> ‘memoryless_channel_REP (combine_channel W 1) = combine_channel_base0 W’
           suffices_by (strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[])
      >> drule combine_channel_bdmc_accessors
      >> disch_then (qspec_then ‘0’ mp_tac) >> simp[] >> strip_tac
      >> drule (iffLR wf_bdmc_def) >> strip_tac
      >> simp[memoryless_channel_REP_alt, combine_channel_base0_def,
              EXTENSION, REPLICATE_compute]
      >> simp[FUN_EQ_THM] >> qx_gen_tac ‘u’
      >> Cases_on ‘LENGTH u = 1’
      >> simp[combine_channel_alt, polar_encode_channel_def,
              transform_input_channel_accessors, repeat_channel_accessors]
      >> Cases_on ‘u’ >> gvs[] >> simp[Once polar_encode_def])
  >> strip_tac
  >> first_x_assum (drule_then (ASSUME_TAC o SYM))
  >> simp[recursive_combine_channel_def]
  >> ‘memoryless_channel_REP (combine_channel W (2 ** SUC n)) =
      combine_channel_step0 W n (combine_channel W (2 ** n))’
       suffices_by (strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[])
  >> drule combine_channel_bdmc_accessors
  >> disch_then (qspec_then ‘SUC n’ strip_assume_tac)
  >> simp[memoryless_channel_REP_alt, combine_channel_step0_def]
  >> simp[FUN_EQ_THM] >> qx_gen_tac ‘u’
  >> ONCE_REWRITE_TAC[FUN_EQ_THM] >> qx_gen_tac ‘S’
  >> Cases_on ‘LENGTH u = 2 ** SUC n’
  >> simp[LET_THM, deinterleave_2_eq]
  >- (‘0n < 2 ** n’ by simp[]
      >> ‘LENGTH u = 2 * 2 ** n’ by simp[EXP]
      >> ‘¬(LENGTH u ≤ 1)’ by simp[]
      >> qspecl_then [‘u’, ‘2 ** n’] mp_tac length_deinterleave_2_half
      >> simp[deinterleave_2_eq] >> strip_tac
      >> qabbrev_tac ‘u_even = get_every_nth_element u 2 0’
      >> qabbrev_tac ‘u_odd = get_every_nth_element u 2 1’
      >> ‘LENGTH (bxor u_even u_odd) = 2 ** n’ by simp[bxor_length]
      >> qabbrev_tac ‘v1 = bxor u_even u_odd’
      >> qabbrev_tac ‘v2 = u_odd’
      >> Know ‘polar_encode u = polar_encode v1 ++ polar_encode v2’
      >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [polar_encode_def]))
          >> simp[LET_THM, deinterleave_2_eq, Abbr ‘v1’, Abbr ‘v2’, Abbr ‘u_even’, Abbr ‘u_odd’])
      >> disch_then SUBST1_TAC
      >> simp[MAP_APPEND, prob_def]
      >> DEP_PURE_REWRITE_TAC[mcprob_space_combine_channel_eq_prod_list]
      >> simp[]
      >> irule prod_list_append_measure
      >> Know ‘∀b. finite_pow_prob_space (mcprob_space W b)’
      >- (gen_tac >> drule_then (qspec_then ‘b’ assume_tac) wf_bdmc_prob_space
          >> gvs[wf_bdmc_def, finite_pow_prob_space_def, mcprob_space_alt,
                 m_space_def, measurable_sets_def])
      >> strip_tac
      >> simp[EVERY_MAP, EVERY_MEM])
  >> simp[polar_encode_channel_def, transform_input_channel_accessors,
          repeat_channel_accessors]
QED

(* Equivalence of polar_encode_channel W (2 ** n) and recursive_combine_channel W n.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_channel_eq_recursive_combine:
  ∀(W : (bool, β) memoryless_channel) n.
    wf_bdmc W ⇒ polar_encode_channel W (2 ** n) = recursive_combine_channel W n
Proof
  rpt strip_tac >> rewrite_tac[GSYM combine_channel_alt]
  >> irule combine_channel_eq_recursive_combine >> simp[]
QED

(* Explicit in-domain base equation for recursive_combine_channel.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_recursive_combine_channel_base:
  ∀(W : (bool, β) memoryless_channel) b y.
    wf_bdmc W ∧ y ∈ mccodomain W ⇒
    mcchannel (recursive_combine_channel W 0) [b] {[y]} = mcchannel W b {y}
Proof
  rpt strip_tac
  >> drule_then (qspec_then ‘0’ (SUBST1_TAC o SYM)) combine_channel_eq_recursive_combine
  >> simp[mcchannel_combine_channel_1]
QED

(* Arikan Fig. 3 / Section I-B.1 recursive combining identity on recursive_combine_channel.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_recursive_combine_channel_step:
  ∀(W : (bool, β) memoryless_channel) n u y1 y2.
    wf_bdmc W ∧ LENGTH u = 2 ** SUC n ∧
    LENGTH y1 = 2 ** n ∧ LENGTH y2 = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y1 ∧
    EVERY (λyi. yi ∈ mccodomain W) y2 ⇒
    mcchannel (recursive_combine_channel W (SUC n)) u {y1 ++ y2} =
      mcchannel (recursive_combine_channel W n)
        (bxor (EL 0 (deinterleave 2 u)) (EL 1 (deinterleave 2 u))) {y1} *
      mcchannel (recursive_combine_channel W n)
        (EL 1 (deinterleave 2 u)) {y2}
Proof
  rpt strip_tac
  >> drule combine_channel_eq_recursive_combine >> strip_tac
  >> pop_assum (fn th => REWRITE_TAC[GSYM th])
  >> gvs[EXP]
  >> qspecl_then [‘W’, ‘n’, ‘u’, ‘y1’, ‘y2’] mp_tac mcchannel_combine_channel_step
  >> simp[]
QED
