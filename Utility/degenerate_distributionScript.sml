Theory degenerate_distribution

Ancestors combin extreal list measure pred_set probability rich_list sigma_algebra

Libs ConseqConv dep_rewrite simpLib realLib;

Definition degenerate_distribution_def:
  degenerate_distribution (x : α) =
  (λs : α -> bool. if x ∈ s then 1 : extreal else 0 : extreal)
End

Definition degenerate_prob_space_def:
  degenerate_prob_space (x : α) (s : α -> bool) =
  (s, POW s, degenerate_distribution x) : α p_space
End

(* -------------------------------------------------------------------------- *)
(* degenerate_distribution is equivalent to dirac_measure from Jared Yeager's *)
(* pi_measure_space_list, which is combin$C 𝟙 x                               *)
(* -------------------------------------------------------------------------- *)
Theorem degenerate_distribution_dirac_measure:
  ∀x.
    degenerate_distribution x = combin$C 𝟙 x
Proof
  gen_tac
  >> simp[C_DEF, degenerate_distribution_def]
  >> simp[FUN_EQ_THM]
  >> gen_tac
  >> simp[indicator_fn_def]
QED

Theorem DISJOINT_IN:
  ∀s t : α -> bool.
    ∀x : α.
      DISJOINT s t ∧ x ∈ s ⇒ x ∉ t
Proof
  rpt strip_tac
  >> gvs[DISJOINT_DEF]
  >> gvs[INTER_DEF]
  >> drule $ iffLR EXTENSION >> strip_tac
  >> pop_assum $ qspec_then `x` assume_tac
  >> gvs[]
QED

Theorem IMAGE_CONSTANT:
  ∀s : α -> bool.
    ∀c : β.
      s ≠ ∅ ⇒ IMAGE (λx. c) s = {c}
Proof
  rpt strip_tac
  >> gvs[IMAGE_DEF]
  >> irule (iffRL EXTENSION)
  >> drule CHOICE_DEF >> strip_tac
  >> strip_tac >> gvs[]
  >> Cases_on `x = c` >> gvs[IN_DEF]
  >> qexists `CHOICE s` >> gvs[]
QED

Theorem EXTREAL_SUM_IMAGE_ZERO_ARB_FUNC:
  ∀s : α -> bool.
    ∀f : α -> extreal.
      FINITE s ∧ (∀x. x ∈ s ⇒ f x = 0) ⇒ ∑ f s = 0
Proof
  rpt strip_tac
  >> Induct_on `s` using FINITE_INDUCT
  >> rpt strip_tac >> gvs[]
  >> `∑ f (e INSERT s) = f e + ∑ f (s DELETE e)` suffices_by gvs[DELETE_NON_ELEMENT]
  >> qspecl_then [`f`] assume_tac EXTREAL_SUM_IMAGE_THM
  >> gvs[]
  >> pop_assum $ qspecl_then [`e`, `s`] assume_tac
  >> gvs[]
  >> pop_assum irule
  >> disj1_tac
  >> rpt strip_tac
  >> gvs[]
QED

Theorem degenerate_distribution_is_prob_space:
  ∀s : α -> bool.
    ∀x : α.
      x ∈ s ⇒
      prob_space (s, POW s, degenerate_distribution x)
Proof
  rpt strip_tac
  >> gvs[degenerate_distribution_def]
  >> gvs[prob_space_def]
  >> gvs[measure_space_def]
  >> conj_tac
  >- gvs[POW_SIGMA_ALGEBRA] (* Proof of sigma algebra *)
  >> conj_tac
  >- (gvs[positive_def] (* Proof of nonnegative measure *)
      >> rpt strip_tac
      >> Cases_on `x ∈ s'` >> gvs[])
  >> gvs[countably_additive_def]
  >> rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `(if c1 then _ else _) = _`
  >> qmatch_goalsub_abbrev_tac `suminf(g ∘ f)`
  >> ‘∀n. 0 ≤ (g ∘ f) n’ by (strip_tac >> Cases_on `x ∈ f n` >> gvs[o_DEF, Abbr `g`])
  >> gvs[ext_suminf_def]
  >> qmatch_goalsub_abbrev_tac `sup (IMAGE h _)`
  >> Cases_on `¬c1`
  >- (gvs[Abbr `h`]
      >> sg `∀n. 0 = (g ∘ f) n`
              >- (CCONTR_TAC
                  >> gvs[]
                  >> first_x_assum $ qspec_then `f n` assume_tac
                  >> gvs[Abbr `g`]
                  >> pop_assum $ qspec_then `n` assume_tac
                  >> gvs[])
              >> qmatch_goalsub_abbrev_tac `IMAGE h _`
              >> sg `h = λn.0` >> gvs[Abbr `h`]
                            >- (irule EQ_EXT >> strip_tac >> gvs[]
                                >> irule EXTREAL_SUM_IMAGE_0
                                >> gvs[FINITE_COUNT])
                            >> pop_assum kall_tac
                            >> gvs [IMAGE_CONSTANT]
                            >> gvs[sup_sing])
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac `r = 1`
  >> `1 ≤ r ∧ r ≤ 1` suffices_by gvs[iffLR le_antisym]
  >> conj_tac >> gvs[Abbr `r`]
  >- (`1 ≤ h (x' + 1)` suffices_by metis_tac[IN_UNIV, le_sup_imp', IMAGE_IN, le_trans]
      >> gvs[Abbr `h`]
      >> gvs[count_add1]
      >> `FINITE (count x')` by gvs[FINITE_COUNT]
      >> qspec_then `g ∘ f` assume_tac EXTREAL_SUM_IMAGE_THM
      >> gvs[]
      >> pop_assum $ qspecl_then [`x'`, `count x'`] assume_tac
      >> gvs[]
      >> qmatch_asmsub_abbrev_tac `a ⇒ b`
      >> sg `a` >> gvs[Abbr `a`, Abbr `b`]
      >- (disj2_tac >> strip_tac >> strip_tac >> gvs[Abbr `g`] >> Cases_on `x ∈ f x''` >> gvs[])
      >> (pop_assum kall_tac
          >> qmatch_goalsub_abbrev_tac `_ + q`
          >> qsuff_tac `0 ≤ q ∧ 1 ≤ g (f x')`
          >- (strip_tac >> `1 + 0 ≤ g (f x') + q` by gvs[le_add2] >> gvs[])
          >> conj_tac
          >- (gvs[Abbr `q`] >> irule EXTREAL_SUM_IMAGE_POS >> gvs[FINITE_COUNT])
          >> gvs[Abbr `g`]))
  >> ‘∀n. ∑ (g ∘ f) (count n) ≤ 1’ suffices_by
    (rpt strip_tac >> gvs[Abbr `h`]
     >> irule (iffRL sup_le')
     >> rpt strip_tac >> gvs[])
  >> strip_tac
  >> ‘∀x'' : num. x'' ≠ x' ⇒ x ∉ f x''’ by
    (rpt strip_tac
     >> last_x_assum $ qspecl_then [`x'`, `x''`] assume_tac
     >> gvs[]
     >> qspecl_then [`f x'`, `f x''`, `x`] assume_tac DISJOINT_IN
     >> gvs[])
  >> sg `∑ (g ∘ f) (count n) = ∑ (g ∘ f) ((count n) DIFF {x'}) + if n > x' then (g ∘ f) x' else 0`
  >- (Cases_on `n > x'` >> gvs[Abbr `h`]
      >- (sg `count n = (count n DIFF {x'}) ∪ {x'}`
          >- (gvs[]
              >> `x' ∈ count n` by gvs[]
              >> irule $ iffRL EXTENSION
              >> gvs[])
          >> pop_assum (fn th => PURE_REWRITE_TAC [Once th])
          >> `g (f x') = ∑ (g ∘ f) {x'}` by gvs[]
          >> pop_assum (fn th => PURE_REWRITE_TAC [Once th])
          >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION
          >> gvs[FINITE_COUNT, FINITE_DIFF, DISJOINT_DIFF]
          >> disj1_tac
          >> rpt strip_tac
          >> (first_assum $ qspec_then `x''` assume_tac >> gvs[Abbr `g`]))
      >> `n ≤ x'` by gvs[] >> gvs[]
      >> `count n DIFF {x'} = count n` suffices_by gvs[]
      >> `x' ∉ count n` by gvs[]
      >> gvs[DELETE_NON_ELEMENT, DELETE_DEF])
  >> gvs[]
  >> pop_assum kall_tac
  >> qsuff_tac `∑ (g ∘ f) (count n DIFF {x'}) = 0`
  >- (strip_tac >> gvs[]
      >> gvs[Abbr `g`] >> Cases_on `n > x'` >> gvs[])
  >> irule EXTREAL_SUM_IMAGE_ZERO_ARB_FUNC
  >> conj_tac
  >- (rpt strip_tac
          >>`x'' ≠ x'` by gvs[]
      >> first_x_assum drule >> strip_tac
      >> gvs[Abbr `g`])
  >> gvs[FINITE_COUNT]
QED

Theorem degenerate_prob_space_is_prob_space:
  ∀x s.
    x ∈ s ⇒
    prob_space (degenerate_prob_space x s)
Proof
  rpt gen_tac
  >> simp[degenerate_prob_space_def, degenerate_distribution_is_prob_space]
QED
