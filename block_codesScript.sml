(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "block_codes";

open arithmeticTheory;
open realTheory;
open listTheory;
open pred_setTheory;
open probabilityTheory;
open bitstringTheory;
open metricTheory;
open measureTheory;
open sigma_algebraTheory;
open extreal_baseTheory;
open cardinalTheory;
open extrealTheory;
open combinTheory; (* o_DEF *)
open realTheory;
open iterateTheory; (* why does this contain SUP_UNION *)
open realaxTheory;
open bitstringTheory;

(* -------------------------------------------------------------------------- *)
(* Notes on relevant theorems, etc                                            *)
(*                                                                            *)
(* UNIV_SIGMA_ALGEBRA, sigma_algebra, 𝕌                                      *)
(*                                                                            *)
(* uniform_distribution, distribution, conditional_distribution               *)
(*                                                                            *)
(* algebra                                                                    *)
(*                                                                            *)
(* subsets, space                                                             *)
(* -------------------------------------------------------------------------- *)

Definition hamming_distance_def:
  hamming_distance (l1 : α list) (l2 : α list) = FOLDR ($+) 0n (MAP (λpair. if (FST pair = SND pair) then 0n else 1n) (ZIP (l1, l2)))
End

(* The set of all codes of length n *)
Definition length_n_codes_def:
  length_n_codes n = {c : bool list | LENGTH c = n}
End

Definition length_n_codes_uniform_prob_space_def:
  length_n_codes_uniform_prob_space (n : num) =
    let s = length_n_codes n in
    let a = POW s in
    let p = uniform_distribution (s, a) in
    (s, a, p)
End

Theorem FINITE_IN_POW:
  ∀s : α -> bool.
  ∀ s' : α -> bool.
  FINITE s ⇒
  s' ∈ POW s ⇒
  FINITE s'
Proof
  rpt strip_tac
  >> gvs[POW_DEF]
  >> drule SUBSET_FINITE
  >> gvs[]
QED

Theorem uniform_distribution_finite_prob_space:
  ∀s : α -> bool.
  FINITE s ⇒
  CARD s ≠ 0 ⇒
  prob_space (s, POW s, uniform_distribution (s, POW s))
Proof
  rpt strip_tac
  >> irule $ iffRL prob_on_finite_set
  >> rpt strip_tac >> gvs[]
  >- (gvs[additive_def]
      >> rpt strip_tac
      >> gvs[uniform_distribution_def]
      >> qsuff_tac `&CARD (s' ∪ t) = &CARD(s') + &CARD(t)`
      >- (rpt strip_tac
          >> irule EQ_SYM
          >> gvs[]
          >> irule div_add
          >> gvs[extreal_of_num_def])
      >> qspecl_then [`s'`, `t`] assume_tac CARD_DISJOINT_UNION
      >> drule FINITE_IN_POW >> strip_tac
      >> gvs[DISJOINT_DEF, FINITE_IN_POW]
      >> pop_assum kall_tac >> pop_assum kall_tac
      >> gvs[REAL_ADD, extreal_of_num_def, extreal_add_eq])
  >- (gvs[positive_def]
      >> conj_tac >> gvs[uniform_distribution_def]
      >- gvs[REAL_DIV_LZERO, extreal_of_num_def, extreal_div_eq]
      >> rpt strip_tac
      >> gvs[REAL_LE_DIV, extreal_of_num_def, extreal_div_eq])
  >> gvs[prob_def, p_space_def]
  >> gvs[uniform_distribution_def]
  >> gvs[extreal_of_num_def, extreal_div_eq, REAL_DIV_REFL]
QED

(* -------------------------------------------------------------------------- *)
(* Given a binary code of length n, construct a corresponding subset of       *)
(* {0, 1, ..., n - 1}, given by including the element i if and only if the    *)
(* (n - 1 - i)th element of the binary code is true.                          *)
(* -------------------------------------------------------------------------- *)
Definition code_to_subset_def:
  code_to_subset [] = ∅ ∧
  code_to_subset (b::bs) = if b then ((LENGTH bs) INSERT (code_to_subset bs)) else (code_to_subset bs)
End

(* -------------------------------------------------------------------------- *)
(* (subset_to_code n s) is the inverse function of (code_to_subset bs) for    *)
(* length n codes                                                             *)
(* -------------------------------------------------------------------------- *)
Definition subset_to_code_def:
  subset_to_code 0 s = [] ∧
  subset_to_code (SUC i) s = (i ∈ s)::(subset_to_code i s)
End

Theorem subset_to_code_length:
  ∀n : num. ∀s : num -> bool.
  LENGTH (subset_to_code n s) = n
Proof
  strip_tac
  >> Induct_on `n` >> gvs[subset_to_code_def]
QED

Theorem subset_to_code_restrict:
  ∀n : num. ∀s : num -> bool.
  subset_to_code n s = subset_to_code n (s ∩ count n)
Proof
  strip_tac
  >> Induct_on `n`
  >- gvs[subset_to_code_def]
  >> rpt strip_tac
  >> PURE_REWRITE_TAC [subset_to_code_def]
  >> first_assum $ qspec_then `s` assume_tac
  >> pop_assum $ (fn th => PURE_REWRITE_TAC [th])
  >> pop_assum $ qspec_then `s ∩ count1 n` assume_tac
  >> pop_assum $ (fn th => PURE_REWRITE_TAC [th])
  >> gvs[]
  >> `count1 n ∩ count n = count n` by gvs[INTER_DEF, count_def, EQ_EXT]
  >> metis_tac[INTER_ASSOC]
QED

Theorem subset_to_code_is_right_inverse:
  ∀n : num. ∀s : num -> bool.
  s ∈ POW(count n) ⇒
  code_to_subset (subset_to_code n s) = s
Proof
  strip_tac
  >> Induct_on `n`
  >- gvs[POW_DEF, subset_to_code_def, code_to_subset_def]
  >> rpt strip_tac
  >> gvs[subset_to_code_def]
  >> gvs[code_to_subset_def]
  >> Cases_on `n ∈ s` >> gvs[]
  >- (gvs[subset_to_code_length]
      >> last_x_assum $ qspec_then `s ∩ count n` assume_tac
      >> gvs[POW_DEF]
      >> PURE_REWRITE_TAC [Once subset_to_code_restrict]
      >> pop_assum $ (fn th => PURE_REWRITE_TAC [th])
      >> irule $ iffRL EXTENSION
      >> rpt strip_tac
      >> Cases_on `x > n`
      >- (gvs[]
          >> CCONTR_TAC
          >> gvs[]
          >> gvs[SUBSET_DEF]
          >> first_x_assum $ qspec_then `x` assume_tac
          >> gvs[])
      >> Cases_on `x = n` >> gvs[])
  >> first_x_assum $ qspec_then `s` assume_tac
  >> gvs[POW_DEF]
  >> pop_assum irule
  >> gvs[SUBSET_DEF]
  >> rpt strip_tac
  >> first_x_assum $ qspec_then `x` assume_tac
  >> gvs[]
  >> Cases_on `x = n` >> gvs[]
QED

Theorem code_to_subset_returns_subset:
  ∀bs : bool list.
  code_to_subset bs ∈ POW (count (LENGTH bs))
Proof
  rpt strip_tac
  >> Induct_on `bs`
  >- gvs[EMPTY_IN_POW, code_to_subset_def]
  >> rpt strip_tac
  >> gvs[code_to_subset_def]
  >> Cases_on `h`
  >> gvs[]
  >> gvs[POW_DEF]
  >> gvs[SUBSET_DEF]
  >> rpt strip_tac
  >> first_x_assum $ qspecl_then [`x`] assume_tac
  >> gvs[]
QED

(* TODO: x ∉ s ∧ x ∉ t can be weakened to x ∈ s ⇔ x ∈ t *)
Theorem INSERT_INJECTIVE:
  ∀x : α. ∀s t : α -> bool.
  x ∉ s ∧ x ∉ t ⇒
  x INSERT s = x INSERT t ⇒
  s = t
Proof
  rpt strip_tac
  >> irule EQ_EXT
  >> rpt strip_tac
  >> `x' ∈ s ⇔ x' ∈ t` suffices_by gvs[IN_DEF]
  >> Cases_on `x' ∈ s`
  >- (`x' ∈ x INSERT s` by gvs[]
      >> `x' ∈ x INSERT t` by metis_tac[]
      >> Cases_on `x' = x` >> gvs[])
  >> Cases_on `x' = x` >> gvs[]
  >> `x' ∉ x INSERT s` by gvs[]
  >> `x' ∉ x INSERT t` by metis_tac[]
  >> gvs[INSERT_DEF]
QED

Theorem code_to_subset_injective:
  ∀bs cs : bool list.
  LENGTH bs = LENGTH cs ⇒
  code_to_subset bs = code_to_subset cs ⇒ bs = cs
Proof
  strip_tac
  >> Induct_on `bs`
  >- gvs[]
  >> rpt strip_tac
  >> Cases_on `cs`
  >- gvs[]
  >> first_x_assum $ qspecl_then [`t`] assume_tac
  >> gvs[]
  >> sg `h ⇔ h'`
  >- (Cases_on `h` >> Cases_on `h'` >> gvs[]
      >- (gvs[code_to_subset_def]
          >> qspecl_then [`t`] assume_tac code_to_subset_returns_subset
          >> `LENGTH t INSERT (code_to_subset bs) ∈ POW (count (LENGTH t))` by gvs[]
          >> last_x_assum kall_tac >> last_x_assum kall_tac >> last_x_assum kall_tac >> last_x_assum kall_tac
          >> gvs[POW_DEF])
      >- (gvs[code_to_subset_def]
          >> qspecl_then [`bs`] assume_tac code_to_subset_returns_subset
          >> `LENGTH t INSERT (code_to_subset t) ∈ POW (count (LENGTH t))` by gvs[]
          >> last_x_assum kall_tac >> last_x_assum kall_tac >> last_x_assum kall_tac >> last_x_assum kall_tac
          >> gvs[POW_DEF]))
  >> gvs[]
  >> gvs[code_to_subset_def]
  >> Cases_on `h` >> gvs[]
  >> qspecl_then [`bs`] assume_tac code_to_subset_returns_subset
  >> gvs[POW_DEF]
  >> sg `(LENGTH t) ∉ (code_to_subset bs)`
  >- (gvs[SUBSET_DEF]
      >> pop_assum $ qspecl_then [`LENGTH t`] assume_tac
      >> gvs[])
  >> qspecl_then [`t`] assume_tac code_to_subset_returns_subset
  >> gvs[POW_DEF]
  >> sg `LENGTH t ∉ (code_to_subset t)`
  >- (gvs[SUBSET_DEF]
      >> pop_assum $ qspecl_then [`LENGTH t`] assume_tac
      >> gvs[])
  >> drule_all INSERT_INJECTIVE >> strip_tac
  >> gvs[]
QED

Theorem code_to_subset_surjective:
  ∀n : num.
  ∀s : num -> bool.
  s ∈ POW (count n) ⇒
  ∃bs : bool list. LENGTH bs = n ∧ code_to_subset bs = s
Proof
  rpt strip_tac
  >> qexists `subset_to_code n s`
  >> gvs[subset_to_code_is_right_inverse, subset_to_code_length]
QED
  
(* -------------------------------------------------------------------------- *)
(* The set of length n codes can be viewed as corresponding to the power set  *)
(* of a set of cardinality n                                                  *)
(* -------------------------------------------------------------------------- *)
Theorem length_n_codes_power_set_bijection:
  ∀n : num.
  BIJ code_to_subset (length_n_codes n) (POW (count n))
Proof
  rpt strip_tac
  >> gvs[BIJ_DEF]
  >> conj_tac
  >- (gvs[INJ_DEF]
      >> rpt strip_tac
      >- gvs[length_n_codes_def, code_to_subset_returns_subset]
      >> gvs[length_n_codes_def, code_to_subset_injective])
  >> gvs[SURJ_DEF]
  >> rpt strip_tac
  >- gvs[length_n_codes_def, code_to_subset_returns_subset]
  >> gvs[length_n_codes_def, code_to_subset_surjective]
QED

Theorem length_n_codes_finite:
  ∀n : num.
  FINITE (length_n_codes n)
Proof
  rpt strip_tac
  >> qspec_then `n` assume_tac length_n_codes_power_set_bijection
  >> qmatch_asmsub_abbrev_tac `BIJ f s t`
  >> `∃g. BIJ g t s` by (irule $ iffLR BIJ_SYM >> qexists `f` >> gvs[])
  >> `FINITE t` suffices_by (strip_tac >> drule_all FINITE_BIJ >> gvs[])
  >> unabbrev_all_tac
  >> gvs[FINITE_COUNT, FINITE_POW]
QED

Theorem length_n_codes_cardinality:
  ∀n : num.
  CARD (length_n_codes n) = 2 ** n
Proof
  rpt strip_tac
  >> qspec_then `n` assume_tac length_n_codes_power_set_bijection
  >> qmatch_asmsub_abbrev_tac `BIJ f s t`
  >> `∃g. BIJ g t s` by (irule $ iffLR BIJ_SYM >> qexists `f` >> gvs[])
  >> `CARD t = 2 ** n` by gvs[CARD_POW, CARD_COUNT, Abbr `t`]
  >> `FINITE t` suffices_by (strip_tac >> drule_all FINITE_BIJ >> gvs[])
  >> unabbrev_all_tac
  >> gvs[FINITE_COUNT, FINITE_POW]
QED
  
(* ------------------------------------------------------- *)
(* Potentially useful here:                                *)
(* prob_on_finite_set                                      *)
(* uniform_distribution_prob_space                         *)
(* ------------------------------------------------------- *)
Theorem length_n_codes_uniform_prob_space_is_prob_space:
  ∀n : num.
  prob_space (length_n_codes_uniform_prob_space n)
Proof
  rpt strip_tac
  >> gvs[length_n_codes_uniform_prob_space_def]
  >> irule uniform_distribution_finite_prob_space
  >> qspecl_then [`n`] assume_tac length_n_codes_finite
  >> qspecl_then [`n`] assume_tac length_n_codes_cardinality
  >> qspecl_then [`n`, `1`] assume_tac ZERO_LESS_EXP
  >> asm_simp_tac arith_ss []
QED

Definition degenerate_distribution_def:
  degenerate_distribution (x : α) = (λs : α -> bool. if x ∈ s then 1 : extreal else 0 : extreal)
End

Definition length_n_codes_degenerate_prob_space_def:
  length_n_codes_degenerate_prob_space (n : num) (bs : bool list) =
    let s = length_n_codes n in
    let a = POW s in
    let p = degenerate_distribution bs in
    (s, a, p)
End

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

Theorem SET_REMOVE_ELEMENT:
  ∀s : α -> bool.
  ∀x : α.
  x ∈ s ⇒ s = {x} ∪ (s DIFF {x})
Proof
  rpt strip_tac
  >> gvs[UNION_DEF, DIFF_DEF]
  >> irule EQ_EXT
  >> rpt strip_tac
  >> gvs[IN_DEF]
  >> Cases_on `x' = x` >> gvs[]
QED

Theorem EXTREAL_SUP_POSITIVE_INFINITY:
  ∀s : extreal -> bool.
  sup s = +∞ ⇔ (∀x. ((∀y. y∈s ⇒ y ≤ x) ⇒ x = +∞))
Proof
  strip_tac
  >> Cases_on `sup s = +∞`
  >- (gvs[]
      >> gvs[extreal_sup_def]
      >> qmatch_asmsub_abbrev_tac `if c1 then _ else (if c2 then _ else _)`
      >> Cases_on `c1` >> gvs[IN_DEF]
      >> Cases_on `c2` >> gvs[])
  >> qmatch_goalsub_abbrev_tac `_ ⇔ c1`
  >> gvs[]
  >> CCONTR_TAC
  >> gvs[]
  >> sg `sup s = +∞`
  >- (PURE_REWRITE_TAC [Once extreal_sup_def]
      >> gvs[IN_DEF])
QED

Theorem EXTREAL_SUP_NEGATIVE_INFINITY:
  ∀s : extreal -> bool.
  sup s = −∞ ⇔ ∀x. x ∈s ⇒ x = −∞
Proof
  strip_tac
  >> Cases_on `sup s = −∞`
  >- (gvs[extreal_sup_def]
      >> qmatch_asmsub_abbrev_tac `if c1 then _ else (if c2 then _ else _)`
      >> Cases_on `c1` >> gvs[]
      >> Cases_on `c2` >> gvs[IN_DEF])
  >> qmatch_goalsub_abbrev_tac `_ ⇔ c1`
  >> gvs[]
  >> CCONTR_TAC
  >> gvs[]
  >> sg `sup s = −∞`
  >- (PURE_REWRITE_TAC [Once extreal_sup_def]
      >> qmatch_goalsub_abbrev_tac `if c1 then _ else (if c2 then _ else _)`
      >> Cases_on `c1`
      >- (gvs[]
          >> first_x_assum $ qspecl_then [`0 : extreal`] assume_tac
          >> gvs[]
          >> first_x_assum $ qspec_then `y` assume_tac
          >> gvs[Abbr `c2`, IN_DEF])
      >> gvs[Abbr `c2`, IN_DEF])
QED

Theorem EXTREAL_SUP_NEGATIVE_INFINITY_EMPTY_OR_SINGLETON:
  ∀s : extreal -> bool.
  sup s = −∞ ⇒ s = ∅ ∨ s = {−∞}
Proof
  rpt strip_tac
  >> CCONTR_TAC
  >> gvs[]
  >> drule (iffLR EXTREAL_SUP_NEGATIVE_INFINITY) >> strip_tac >> last_x_assum kall_tac
  >> qspecl_then [`s`, `∅`] assume_tac (iffRL EXTENSION)
  >> `s = ∅` suffices_by gvs[]
  >> gvs[]
  >> first_assum drule >> strip_tac
  >> last_x_assum kall_tac
  >> qspecl_then [`s`, `{−∞}`] assume_tac (iffRL EXTENSION)
  >> `s = {−∞}` suffices_by gvs[]
  >> gvs[]
  >> first_x_assum $ qspec_then `x` assume_tac
  >> Cases_on `x ∈ s` >> gvs[]
QED

Theorem EXTREAL_SUP_NOT_POSITIVE_INFINITY:
  ∀s : extreal -> bool.
  sup s ≠ +∞ ⇒ ∃x. (∀y. y ∈ s ⇒ y ≤ x) ∧ x ≠ +∞
Proof
  rpt strip_tac
  >> qexists `sup s + 1`
  >> conj_tac >> gvs[add_not_infty]
  >> rpt strip_tac
  >> drule le_sup_imp' >> strip_tac
  >> `0 : extreal ≤ 1` by gvs[]
  >> `y + 0 ≤ sup s + 1` by gvs[le_add2]
  >> gvs[]
QED

Theorem EXTREAL_SUP_NOT_NEGATIVE_INFINITY:
  ∀s : extreal -> bool.
  sup s ≠ −∞ ⇒ ∃x. x ∈ s ∧ x ≠ −∞
Proof
  rpt strip_tac
  >> gvs[extreal_sup_def]
  >> qmatch_asmsub_abbrev_tac `if c1 then _ else (if c2 then _ else v)`
  >> Cases_on `c1`
  >- (gvs[]
      >> first_x_assum $ qspec_then `0` assume_tac
      >> gvs[]
      >> qexists `y`
      >> CCONTR_TAC
      >> gvs[IN_DEF])
  >> gvs[]
  >> Cases_on `c2` >> gvs[]
  >> qexists `x'`
  >> gvs[IN_DEF]
QED

Theorem EXTREAL_SUP_REAL_SUP:
  ∀s : extreal -> bool.
  ∀r : real.
  sup s = Normal r ⇒ sup (PREIMAGE Normal s) = r
Proof
  rpt strip_tac
  >> gvs[extreal_sup_def]
  >> qmatch_asmsub_abbrev_tac `if c1 then _ else (if c2 then _ else v)`
  >> Cases_on `c1` >> gvs[]
  >> Cases_on `c2` >> gvs[]
  >> AP_TERM_TAC
  >> gvs[PREIMAGE_def]
  >> irule EQ_EXT
  >> rpt strip_tac
  >> gvs[IN_DEF]
QED

Theorem EXTREAL_MAX_REAL_MAX:
  ∀r r' : real.
  max (Normal r) (Normal r') = Normal (max r r')
Proof
  rpt strip_tac
  >> gvs[extreal_max_def]
  >> gvs[real_max]
  >> Cases_on `r ≤ r'` >> gvs[]
QED

Theorem EXTREAL_SUP_UNION:
  ∀s t : extreal -> bool.
  sup (s ∪ t) = max (sup s) (sup t)
Proof
  rpt strip_tac
  (* Strategy: Prove for all cases where sup s/sup t is +∞/-∞. Then in the
     case where each is finite, prove that sup (s ∪ t) is finite. Then
     convert to real and use existing proof for the real version *)
  (* Handle case where either of the supremums is infinity *)
  >> sg `∀s t : extreal -> bool. sup s = +∞ ⇒ sup (s ∪ t) = max (sup s) (sup t)`
  >- (rpt strip_tac
      >> drule (iffLR EXTREAL_SUP_POSITIVE_INFINITY)
      >> rpt strip_tac
      >> gvs[]
      >> PURE_REWRITE_TAC[Once extreal_sup_def]
      >> qmatch_goalsub_abbrev_tac `if c1 then _ else (if c2 then _ else _)`
      >> `c1` suffices_by gvs[]
      >> gvs[Abbr `c1`, Abbr `c2`]
     )
  >> Cases_on `sup s = +∞` >> gvs[]
  >> Cases_on `sup t = +∞`
  >- (first_x_assum $ qspecl_then [`t`, `s`] assume_tac >> gvs[UNION_COMM])
  >> last_x_assum kall_tac
  (* Handle case where either of the supremums is negative infinity *)
  >> sg `∀s t : extreal -> bool. sup s = −∞ ⇒ sup (s ∪ t) = max (sup s) (sup t)`
  >- (rpt (pop_assum kall_tac)
      >> rpt strip_tac
      >> gvs[]
      >> PURE_REWRITE_TAC[Ntimes extreal_sup_def 2]
      >> qmatch_goalsub_abbrev_tac `(if c1 then _ else (if c2 then _ else e1)) = (if c3 then _ else (if c4 then _ else e2))`
      >> `c1 = c3 ∧ c2 = c4 ∧ e1 = e2` suffices_by gvs[]
      >> conj_tac
      >- (unabbrev_all_tac
          >> qmatch_goalsub_abbrev_tac `b1 ⇔ b2`
          >> Cases_on `b1` >> Cases_on `b2` >> gvs[]
          >- (last_x_assum $ qspec_then `x` assume_tac
              >> gvs[]
              >> last_x_assum $ qspec_then `y` assume_tac
              >> gvs[IN_DEF]
              >> drule $ iffLR EXTREAL_SUP_NEGATIVE_INFINITY >> strip_tac
              >> pop_assum $ qspec_then `y` assume_tac
              >> gvs[IN_DEF])
          >> pop_assum $ qspec_then `x` assume_tac
          >> gvs[]
          >> first_x_assum $ qspec_then `y` assume_tac
          >> gvs[]
          >> drule $ iffLR EXTREAL_SUP_NEGATIVE_INFINITY >> strip_tac
          >> pop_assum $ qspec_then `x` assume_tac
          >> gvs[IN_DEF])
      >> conj_tac
      >- (unabbrev_all_tac
          >> qmatch_goalsub_abbrev_tac `b1 ⇔ b2`
          >> Cases_on `b1` >> Cases_on `b2` >> gvs[]
          >- (first_x_assum $ qspec_then `x` assume_tac
              >> gvs[IN_DEF])
          >- (drule $ iffLR EXTREAL_SUP_NEGATIVE_INFINITY >> strip_tac
              >> pop_assum $ qspec_then `x` assume_tac >> gvs[IN_DEF])
          >> pop_assum $ qspec_then `x` assume_tac >> gvs[IN_DEF])
      >> unabbrev_all_tac
      >> drule EXTREAL_SUP_NEGATIVE_INFINITY_EMPTY_OR_SINGLETON >> strip_tac
      >> gvs[IN_DEF])
  >> Cases_on `sup s = −∞` >> gvs[]
  >> Cases_on `sup t = −∞`
  >- (first_x_assum $ qspecl_then [`t`, `s`] assume_tac
      >> gvs[UNION_COMM])
  >> qpat_x_assum `∀a b. _` kall_tac
  >> Cases_on `sup (s ∪ t) = +∞`
  >- (drule (iffLR EXTREAL_SUP_POSITIVE_INFINITY) >> strip_tac
      >> drule EXTREAL_SUP_NOT_POSITIVE_INFINITY >> strip_tac
      >> qspec_then `s` assume_tac EXTREAL_SUP_NOT_POSITIVE_INFINITY
      >> gvs[]
      >> last_x_assum $ qspec_then `max x x'` assume_tac
      >> Cases_on `max x x' = +∞`
      >- (gvs[extreal_max_def] >> Cases_on `x ≤ x'` >> gvs[])
      >> gvs[]
      >> first_x_assum $ qspec_then `y` assume_tac
      >> first_x_assum $ qspec_then `y` assume_tac
      >> gvs[]
      >> gvs[le_max])
  >> Cases_on `sup (s ∪ t) = −∞`
  >- (drule (iffLR EXTREAL_SUP_NEGATIVE_INFINITY) >> strip_tac
      >> `sup s = −∞` suffices_by gvs[]
      >> irule (iffRL EXTREAL_SUP_NEGATIVE_INFINITY)
      >> gvs[])
  >> qmatch_goalsub_abbrev_tac `a = max b c`
  >> Cases_on `a` >> gvs[]
  >> Cases_on `b` >> gvs[]
  >> Cases_on `c` >> gvs[]
  >> qspecl_then [`s ∪ t`, `r`] assume_tac EXTREAL_SUP_REAL_SUP
  >> qspecl_then [`s`, `r'`] assume_tac EXTREAL_SUP_REAL_SUP
  >> qspecl_then [`t`, `r''`] assume_tac EXTREAL_SUP_REAL_SUP
  >> gvs[]
  >> gvs[EXTREAL_MAX_REAL_MAX]
  >> gvs[PREIMAGE_UNION]
  >> irule SUP_UNION
  >> gvs[]
  >> conj_tac
  >- (qexists `sup (PREIMAGE Normal s)`
      >> rpt strip_tac
      >> `Normal x ≤ Normal (sup (PREIMAGE Normal s))` suffices_by gvs[]
      >> `Normal x ≤ sup s` suffices_by gvs[]
      >> gvs[le_sup_imp'])
  >> conj_tac
  >- (qexists `sup (PREIMAGE Normal t)`
      >> rpt strip_tac
      >> `Normal x ≤ Normal (sup (PREIMAGE Normal t))` suffices_by gvs[]
      >> `Normal x ≤ sup t` suffices_by gvs[]
      >> gvs[le_sup_imp'])
  >> conj_tac
  >- (qspecl_then [`s`] assume_tac EXTREAL_SUP_NOT_NEGATIVE_INFINITY
      >> gvs[]
      >> qspecl_then [`s`] assume_tac EXTREAL_SUP_NOT_POSITIVE_INFINITY
      >> gvs[]
      >> first_x_assum $ qspec_then `x` assume_tac
      >> gvs[]
      >> `x ≠ +∞` by (CCONTR_TAC >> gvs[le_infty])
      >> Cases_on `x` >> gvs[]
      >> gvs[PREIMAGE_def]
      >> CCONTR_TAC
      >> gvs[]
      >> drule (iffLR EXTENSION) >> strip_tac
      >> pop_assum $ qspec_then `r` assume_tac
      >> gvs[])
  >- (qspecl_then [`t`] assume_tac EXTREAL_SUP_NOT_NEGATIVE_INFINITY
      >> gvs[]
      >> qspecl_then [`t`] assume_tac EXTREAL_SUP_NOT_POSITIVE_INFINITY
      >> gvs[]
      >> first_x_assum $ qspec_then `x` assume_tac
      >> gvs[]
      >> `x ≠ +∞` by (CCONTR_TAC >> gvs[le_infty])
      >> Cases_on `x` >> gvs[]
      >> gvs[PREIMAGE_def]
      >> CCONTR_TAC
      >> gvs[]
      >> drule (iffLR EXTENSION) >> strip_tac
      >> pop_assum $ qspec_then `r` assume_tac
      >> gvs[])
QED

Theorem SET_PARTITION:
  ∀s : α -> bool.
  ∀t : α -> bool.
  t ⊆ s ⇒ s = t ∪ (s DIFF t)
Proof
  rpt strip_tac
  >> gvs[SUBSET_DEF, UNION_DEF, DIFF_DEF]
  >> irule (iffRL EXTENSION)
  >> rpt strip_tac
  >> Cases_on `x ∈ s` >> gvs[]
  >> CCONTR_TAC
  >> gvs[]
QED
  
Theorem UNIV_PARTITION:
  ∀s : α -> bool.
  𝕌(:α) = s ∪ (𝕌(:α) DIFF s)
Proof
  gvs[SET_PARTITION]
QED

(* SUM_IMAGE_ZERO had forgotten to include a forall statement.
   This version includes the forall statement *)
Theorem SUM_IMAGE_ZERO_FORALL:
  ∀s : α -> bool.
  ∀f : α -> num.
  FINITE s ⇒
  (∑ f s = 0n ⇔ ∀x : α. x ∈ s ⇒ f x = 0n)
Proof
  gvs[SUM_IMAGE_ZERO]
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
  ∀s : α -> bool. ∀f : α -> extreal.
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
  >> `∀n. 0 ≤ (g ∘ f) n` by (strip_tac >> Cases_on `x ∈ f n` >> gvs[o_DEF, Abbr `g`])
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
  >> `∀n. ∑ (g ∘ f) (count n) ≤ 1` suffices_by
     (rpt strip_tac >> gvs[Abbr `h`]
      >> irule (iffRL sup_le')
      >> rpt strip_tac >> gvs[])
  >> strip_tac
  >> `∀x'' : num. x'' ≠ x' ⇒ x ∉ f x''` by
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
  

Theorem length_n_codes_degenerate_prob_space_is_prob_space:
  ∀n : num. ∀bs : bool list.
  bs ∈ length_n_codes n ⇒
  prob_space (length_n_codes_degenerate_prob_space n bs)
Proof
  gvs[length_n_codes_degenerate_prob_space_def, degenerate_distribution_is_prob_space]
QED
   

(* -------------------------------------------------------------------------- *)
(* Takes ns, a list of booleans that describe whether or not to apply noise   *)
(* at each position, and takes bs, the original bitstring, and returns the    *)
(* bitstring which has had noise applied in each of the appropriate positions *)
(* -------------------------------------------------------------------------- *)
Definition apply_noise_def:
  apply_noise (ns : bool list) (bs : bool list) = bxor ns bs
End

Definition m

Definition symmetric_noise_distribution_def:
  symmetric_noise_distribution (n : num) (p : extreal) (bs : bool list) = p ** LENGTH (FILTER (λx. x) bs) + (1 - p) ** 
End

(* -------------------------------------------------------------------------- *)
(* Takes an input probability distribution and returns the output probability *)
(* distribution with errors randomly added                                    *)
(* -------------------------------------------------------------------------- *)
Definition symmetric_error_channel_distribution_def:
  symmetric_error_channel_distribution (n : num) (p : extreal) (bs : bool list) (cs : bool list) =




(* Representation of the probability distribution over possible errors in 
Definition length_n_code_error_distribution_def:
  length_n_code_error_distribution (p : extreal) (bs : bool list) = 
End



val _ = export_theory();
