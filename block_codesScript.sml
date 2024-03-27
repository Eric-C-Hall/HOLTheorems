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
open rich_listTheory;
open pairTheory;
open relationTheory;
open wellorderTheory;
open martingaleTheory;
open lebesgueTheory;

open dep_rewrite

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
      FINITE s ∧
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
  ∀n : num.
    ∀s : num -> bool.
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
  ∀n : num.
    ∀s : num -> bool.
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
  ∀x : α.
    ∀s t : α -> bool.
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
(* Takes bs, an initial bitstring, and ns, a list of booleans that describe   *)
(* whether or not to apply noise at each position, and returns the bitstring  *)
(* which has had noise applied in each of the appropriate positions           *)
(* -------------------------------------------------------------------------- *)
Definition apply_noise_def:
  apply_noise = bxor
End

Definition num_errors_def:
  num_errors (ns : bool list) = LENGTH (FILTER (λx.x) ns)
End

(* Symmetric noise mass function *)
Definition sym_noise_mass_func_def:
  sym_noise_mass_func (n : num) (p : extreal) = (λns : bool list. p pow (num_errors ns) * (1 - p) pow (n - num_errors ns))
End

(* Should I include the condition 0 ≤ p ≤ 1 here somehow? *)
Definition sym_noise_dist_def:
  sym_noise_dist (n : num) (p : extreal) = ∑ (sym_noise_mass_func n p)
End

Definition sym_noise_prob_space_def:
  sym_noise_prob_space n p = (length_n_codes n, POW (length_n_codes n), sym_noise_dist n p)
End

Theorem le_not_posinf:
  ∀x y : extreal. x ≤ y ∧ y ≠ +∞ ⇒ x ≠ +∞
Proof
  rpt strip_tac >> gvs[]
  >> Cases_on ‘y’ >> gvs[]
QED

Theorem le_not_neginf:
  ∀x y : extreal. y ≤ x ∧ y ≠ −∞ ⇒ x ≠ −∞
Proof
  rpt strip_tac >> gvs[]
  >> Cases_on ‘y’ >> gvs[]
QED
        
(* It doesn't seem to me that countably_additive should be dependent on the
   measure being nonnegative everywhere, but it is, because it depends on
   suminf, which has the condition of nonnegativity everywhere. I'm not
   convinced that suminf needs the condition of nonnegativity everywhere,
   but under the current definition of suminf, which uses a supremum instead
   of a limit, it is necessary to ensure that the infinite sum has the right
   value. Ideally it would use the limit definition of an infinite sum instead,
   so that it can handle negative values.
   -------------
   
   We discussed this issue. It seems to not be such a big problem since
   a measure is always supposed to be nonnegative everywhere. Using the
   alternative definition, we would have to constantly check that the sum
   converges, which may be more of a nuisance. Using the current version of
   suminf, we can be sure that the sum converges to some value (possibly
   infinity), by the monotone convergence theorem, and the fact that the
   sum applied to positive values is monotone.

   Still, under certain circumstances, maybe it'll be useful to discuss
   countably additive functions which are not strictly positive?
 *)

Theorem le_1_not_posinf:
  ∀e : extreal. e ≤ 1 ⇒ e ≠ +∞
Proof
  rpt strip_tac
  >> Cases_on ‘e’ >> gvs[]
QED

Theorem complement_prob:
  ∀p : extreal.
    0 ≤ p ∧ p ≤ 1 ⇒ 0 ≤ (1 - p) ∧ (1 - p) ≤ 1
Proof
  rpt strip_tac
  >- (irule le_sub_imp >> gvs[le_not_infty, le_1_not_posinf])
  >> irule sub_le_imp2
  >> gvs[]
  >> ‘1 + 0 ≤ 1 + p’ suffices_by gvs[]
  >> irule $ iffRL le_ladd
  >> gvs[]
QED

Theorem sym_noise_mass_func_pos:
  ∀n p x. 0 ≤ p ∧ p ≤ 1 ⇒
          0 ≤ sym_noise_mass_func n p x
Proof
  rpt strip_tac
  >> drule_all complement_prob >> strip_tac
  >> gvs[sym_noise_mass_func_def, le_mul, pow_pos_le]   
QED

Theorem sym_noise_dist_pos:
  ∀n p s. 0 ≤ p ∧ p ≤ 1 ∧ FINITE s ⇒
          0 ≤ sym_noise_dist n p s
Proof
  rpt strip_tac
  >> drule_all complement_prob >> strip_tac
  >> gvs[sym_noise_dist_def]
  >> irule EXTREAL_SUM_IMAGE_POS
  >> rpt strip_tac
  >> gvs[sym_noise_mass_func_pos]
QED

Theorem sym_noise_dist_not_neginf:
  ∀n p s. 0 ≤ p ∧ p ≤ 1 ∧ FINITE s ⇒
          sym_noise_dist n p s ≠ −∞
Proof
  rpt strip_tac
  >> drule_all sym_noise_dist_pos >> rpt strip_tac
  >> pop_assum $ qspec_then ‘n’ assume_tac
  >> Cases_on ‘sym_noise_dist n p s’ >> gvs[]
QED

Theorem sym_noise_dist_singleton:
  ∀n p x. 0 ≤ p ∧ p ≤ 1 ⇒
          sym_noise_dist n p {x} = sym_noise_mass_func n p x
Proof
  rpt strip_tac >> gvs[sym_noise_dist_def]
QED

Theorem sym_noise_mass_func_pos:
  ∀n p x. 0 ≤ p ∧ p ≤ 1 ⇒
          0 ≤ sym_noise_mass_func n p x
Proof
  gvs[GSYM sym_noise_dist_singleton, sym_noise_dist_pos]
QED

Theorem sym_noise_mass_func_not_neginf:
  ∀n p x. 0 ≤ p ∧ p ≤ 1 ⇒
          sym_noise_mass_func n p x ≠ −∞
Proof
  gvs[GSYM sym_noise_dist_singleton, sym_noise_dist_not_neginf]
QED

Theorem sym_noise_dist_union:
  ∀n p s t.
    0 ≤ p ∧ p ≤ 1 ∧ FINITE s ∧ FINITE t ∧ DISJOINT s t ⇒
    sym_noise_dist n p (s ∪ t) = sym_noise_dist n p s + sym_noise_dist n p t
Proof
  rpt strip_tac
  >> gvs[sym_noise_dist_def]
  >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION
  >> gvs[]
  >> disj1_tac >> gvs[sym_noise_mass_func_not_neginf]
QED

Theorem sym_noise_prob_space_additive:
  ∀n p.
    0 ≤ p ∧ p ≤ 1 ⇒ additive (sym_noise_prob_space n p)
Proof
  rpt strip_tac
  >> drule_all complement_prob >> strip_tac
  >> gvs[additive_def, sym_noise_prob_space_def]
  >> rpt strip_tac
  >> DEP_REWRITE_TAC[sym_noise_dist_union]
  >> metis_tac[FINITE_IN_POW, length_n_codes_finite]
QED

Theorem sym_noise_prob_space_positive:
  ∀n p.
    0 ≤ p ∧ p ≤ 1 ⇒
    positive (sym_noise_prob_space n p)
Proof
  rpt strip_tac
  >> drule complement_prob >> strip_tac
  >> gvs[positive_def, sym_noise_prob_space_def]
  >> conj_tac >- gvs[sym_noise_dist_def]
  >> rpt strip_tac
  >> DEP_REWRITE_TAC[sym_noise_dist_pos]
  >> gvs[]
  >> metis_tac[FINITE_IN_POW, length_n_codes_finite]
QED

Theorem sym_noise_prob_space_measure_space:
  ∀n p.
    0 ≤ p ∧ p ≤ 1 ⇒
    measure_space (sym_noise_prob_space n p)
Proof
  rpt strip_tac
  >> irule finite_additivity_sufficient_for_finite_spaces2
  >> simp[sym_noise_prob_space_additive, sym_noise_prob_space_positive]
  >> simp[sym_noise_prob_space_def, length_n_codes_finite, POW_SIGMA_ALGEBRA]
QED

Theorem length_n_codes_empty:
  ∀n : num. ¬(length_n_codes n = ∅)
Proof
  rpt strip_tac
  >> gvs[length_n_codes_def]
  >> drule $ iffLR EXTENSION >> pop_assum kall_tac >> strip_tac
  >> gvs[]
  >> pop_assum $ qspec_then ‘zero_extend n []’ assume_tac
  >> gvs[length_zero_extend]
QED

Theorem length_n_codes_suc:
  ∀n : num.
    length_n_codes (SUC n) = (IMAGE (CONS T) (length_n_codes n)) ∪ (IMAGE (CONS F) (length_n_codes n))
Proof
  strip_tac
  >> irule $ iffRL EXTENSION
  >> rpt strip_tac
  >> qmatch_goalsub_abbrev_tac ‘b1 ⇔ b2’ >> Cases_on ‘b2’ >> gvs[Abbr ‘b1’]
  >- gvs[length_n_codes_def]
  >- gvs[length_n_codes_def]
  >> CCONTR_TAC
  >> Cases_on ‘x’
  >- gvs[length_n_codes_def]
  >> rpt $ first_x_assum $ qspec_then ‘t’ assume_tac
  >> gvs[]
  >> Cases_on ‘h’ >> gvs[length_n_codes_def]
QED

Theorem INSERT_UNION_EQ2:
  ∀x : α.
    ∀s t : α -> bool.
      s ∪ (x INSERT t) = x INSERT (s ∪ t)
Proof
  rpt strip_tac
  >> metis_tac[UNION_COMM, INSERT_UNION_EQ]
QED

(*Theorem extreal_sum_image_union:
  ∀f : α -> extreal.
    ∀ g h : β -> α.
      ∀s : β -> bool.
        FINITE s ∧
        DISJOINT (IMAGE g s) (IMAGE h s) ∧
        ((∀x. x ∈ IMAGE g s ∪ IMAGE h s ⇒ f x ≠ +∞) ∨ (∀x. x ∈ IMAGE g s ∪ IMAGE h s ⇒ f x ≠ −∞)) ⇒
        ∑ f ((IMAGE g s) ∪ (IMAGE h s)) = ∑ (λbs. (f ∘ g) bs + (f ∘ h) bs) s
Proof
  rpt gen_tac
  >> disch_tac >> rpt (pop_assum $ CONJUNCTS_THEN assume_tac)
  >> Induct_on ‘s’
  >> gvs[]
  >> rpt (rpt gen_tac >> disch_tac)
  >> fs[]
  >> first_x_assum $ CONJUNCTS_THEN assume_tac
  >> gvs[INSERT_UNION_EQ, INSERT_UNION_EQ2]
  >> qspec_then ‘f’ assume_tac EXTREAL_SUM_IMAGE_THM
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac ‘∑ f (g e INSERT t)’
  >> first_assum $ qspecl_then [‘g e’, ‘t’] assume_tac
  >> qmatch_asmsub_abbrev_tac ‘premises ⇒ goal’
  >> sg ‘goal’
  >- (first_x_assum irule
      >> gvs[Abbr ‘premises’]
      >> conj_tac
      >- gvs[Abbr ‘t’]
      >> disj2_tac
      >> gen_tac
      >> disch_tac
QED*)

(*Theorem extreal_sum_length_n_codes_suc:
  ∀f : bool list -> extreal.
    ∀n : num.
      (∀cs. cs ∈ (length_n_codes (SUC n)) ⇒ f cs ≠ −∞) ∨ (∀cs. cs ∈ (length_n_codes (SUC n)) ⇒ f cs ≠ +∞) ⇒
      ∑ f (length_n_codes (SUC n)) = ∑ (λbs : bool list. ∑ f {T::bs; F::bs}) (length_n_codes n)
Proof
  rpt gen_tac
  >> DISCH_TAC
  >> simp[length_n_codes_suc]
  >> qmatch_goalsub_abbrev_tac ‘u1 ∪ u2’
  >>

  
  >> sg ‘∑ f (u1 ∪ u2) = ∑ f u1 + ∑ f u2’
  >- (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION
      >> conj_tac
      >- gvs[IMAGE_FINITE, length_n_codes_finite, Abbr ‘u1’, Abbr ‘u2’]
      >> conj_tac
      >- gvs[IMAGE_FINITE, length_n_codes_finite, Abbr ‘u1’, Abbr ‘u2’]
      >> conj_tac
      >- (simp[DISJOINT_DEF, INTER_DEF]
          >> irule $ iffRL EXTENSION
          >> strip_tac
          >> Cases_on ‘x ∈ ∅’
          >- gvs[]
          >> simp[]
          >> Cases_on ‘x’
          >- (unabbrev_all_tac >> gvs[IMAGE_DEF, length_n_codes_def])
          >> Cases_on ‘h’ >> unabbrev_all_tac >> gvs[IMAGE_DEF, length_n_codes_def])
      >> gvs[]
      >- (disj1_tac
          >> gen_tac >> DISCH_TAC
          >> last_x_assum irule
          >> gvs[Abbr ‘u1’, Abbr ‘u2’, IMAGE_DEF, length_n_codes_def])
      >> disj2_tac
      >> gen_tac >> DISCH_TAC
      >> last_x_assum irule
      >> gvs[Abbr ‘u1’, Abbr ‘u2’, IMAGE_DEF, length_n_codes_def])
  >> pop_assum $ (fn th => PURE_REWRITE_TAC [th])
  >> ∑ (λx. ∑ f x) 

       unabbrev_all_tac
  >> 

  ∑ (f : α -> extreal) _ + ∑ f _
QED*)

Theorem sym_noise_dist_insert:
  ∀n p x s.
    0 ≤ p ∧ p ≤ 1 ∧ FINITE s ∧ x ∉ s ⇒
    sym_noise_dist n p (x INSERT s) = sym_noise_dist n p {x} + sym_noise_dist n p s
Proof
  rpt strip_tac
  >> gvs[Once INSERT_SING_UNION]
  >> gvs[sym_noise_dist_union]
QED

Theorem num_errors_cons:
  ∀bs.
    num_errors (T::bs) = 1 + num_errors bs∧ num_errors(F::bs) = num_errors bs
Proof
  gvs[num_errors_def]
QED

Theorem num_errors_length:
  ∀x. num_errors x ≤ LENGTH x
Proof
  rpt strip_tac
  >> gvs[num_errors_def]
  >> gvs[LENGTH_FILTER_LEQ]
QED

Theorem sym_noise_mass_func_suc:
  ∀n p x.
    0 ≤ p ∧ p ≤ 1 ∧ LENGTH x = n ⇒
    sym_noise_mass_func n p x = sym_noise_mass_func (SUC n) p (T::x) + sym_noise_mass_func (SUC n) p (F::x)
Proof
  rpt strip_tac
  >> drule_all complement_prob >> strip_tac
  >> gvs[sym_noise_mass_func_def, ADD1, num_errors_cons, pow_add]
  >> PURE_REWRITE_TAC[Once ADD_COMM]
  >> DEP_PURE_REWRITE_TAC[LESS_EQ_ADD_SUB]
  >> gvs[num_errors_length]
  >> gvs[pow_add]
  >> qmatch_goalsub_abbrev_tac ‘pow1 * pow2’
  >> qmatch_goalsub_abbrev_tac ‘_ * a1 * _ + _ * (a2 * _)’
  >> gvs[AC mul_comm mul_assoc]
  >> sg ‘a1 + a2 = 1’
  >- (gvs[Abbr ‘a2’]
      >> metis_tac[sub_add2, le_not_infty, le_1_not_posinf])
  >> metis_tac[add_rdistrib, mul_lone]
QED

Theorem EXTREAL_SUM_IMAGE_DOUB:
  ∀f : α -> extreal.
    ∀a b : α.
      a ≠ b ∧
      ¬((f a = +∞ ∧ f b = −∞) ∨ (f a = −∞ ∧ f b = +∞)) ⇒
      ∑ f {a; b} = f a + f b
Proof
  rpt strip_tac
  >> gvs[EXTREAL_SUM_IMAGE_DEF]
  >> DEP_PURE_ONCE_REWRITE_TAC[ITSET_def]
  >> gvs[REST_DEF, DELETE_DEF]
  >> Cases_on ‘CHOICE {a; b} = a’ >> gvs[]
  >- (Cases_on ‘f a’ >> Cases_on ‘f b’ >> gvs[extreal_add_def, REAL_ADD_SYM])
  >> Cases_on ‘CHOICE {a; b} = b’ >> gvs[]
  >> ‘CHOICE {a; b} ∉ {a; b}’ suffices_by gvs[CHOICE_DEF]
  >> CCONTR_TAC
  >> gvs[]
QED

Theorem sym_noise_dist_empty:
  ∀n p.
    sym_noise_dist n p ∅ = 0
Proof
  gvs[sym_noise_dist_def]
QED

Theorem sym_noise_dist_suc_singleton:
  ∀n p bs.
    0 ≤ p ∧ p ≤ 1 ∧ bs ∈ length_n_codes n ⇒
    sym_noise_dist (SUC n) p {T::bs; F::bs} = sym_noise_dist n p {bs}
Proof
  rpt strip_tac
  >> gvs[sym_noise_dist_def]
  >> DEP_PURE_REWRITE_TAC[EXTREAL_SUM_IMAGE_DOUB]
  >> rpt conj_tac
  >- gvs[]
  >- (CCONTR_TAC >> gvs[sym_noise_mass_func_not_neginf])
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM sym_noise_mass_func_suc]
  >> gvs[length_n_codes_def]
QED

Theorem sym_noise_dist_suc_general:
  ∀n p s.
    0 ≤ p ∧ p ≤ 1 ∧ s ⊆ length_n_codes n ⇒
    sym_noise_dist (SUC n) p (IMAGE (CONS T) s ∪ IMAGE (CONS F) s) = sym_noise_dist n p s
Proof
  rpt gen_tac
  >> qmatch_goalsub_abbrev_tac ‘g’
  >> qsuff_tac ‘FINITE s ⇒ g’
  >- (gvs[Abbr ‘g’]
      >> rpt strip_tac
      >> last_x_assum irule
      >> metis_tac[SUBSET_FINITE, length_n_codes_finite])
  >>unabbrev_all_tac
  >> Induct_on ‘s’ using FINITE_INDUCT
  >> gvs[]
  >> conj_tac
  >- gvs[sym_noise_dist_def]
  >> rpt strip_tac
  >> gvs[INSERT_UNION]
  >> DEP_PURE_ONCE_REWRITE_TAC[sym_noise_dist_insert]
  >> gvs[]
  >> PURE_REWRITE_TAC[Once UNION_COMM]
  >> gvs[INSERT_UNION]
  >> DEP_PURE_ONCE_REWRITE_TAC[add_comm]
  >> gvs[sym_noise_dist_not_neginf]
  >> DEP_PURE_ONCE_REWRITE_TAC[sym_noise_dist_insert]
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac ‘a + b + c = d’
  >> ‘a ≠ −∞’ by (unabbrev_all_tac >> gvs[sym_noise_dist_not_neginf])
  >> ‘b ≠ −∞’ by (unabbrev_all_tac >> gvs[sym_noise_dist_not_neginf])
  >> ‘c ≠ −∞’ by (unabbrev_all_tac >> gvs[sym_noise_dist_not_neginf])
  >> ‘d ≠ −∞’ by (unabbrev_all_tac >> gvs[sym_noise_dist_not_neginf])
  >> qsuff_tac ‘c + a + b = d’
  >- (NTAC 11 $ last_x_assum kall_tac
      >> unabbrev_all_tac >> metis_tac[add_comm, add_assoc])
  >> gvs[Abbr ‘a’, Abbr ‘c’]
  >> gvs[sym_noise_dist_singleton]
  >> DEP_PURE_REWRITE_TAC[GSYM sym_noise_mass_func_suc]
  >> gvs[]
  >> conj_tac >- gvs[length_n_codes_def]
  >> rpt $ qpat_x_assum ‘sym_noise_mass_func _ _ _ ≠ −∞’ kall_tac
  >> gvs[UNION_COMM]
  >> qpat_x_assum ‘sym_noise_dist (SUC n) _ (_ ∪ _) = _’ kall_tac
  >> gvs[Abbr ‘d’]
  >> DEP_PURE_ONCE_REWRITE_TAC[sym_noise_dist_insert]
  >> gvs[sym_noise_dist_singleton]
QED

Theorem sym_noise_dist_suc:
  ∀n p bs.
    0 ≤ p ∧ p ≤ 1 ⇒
    sym_noise_dist (SUC n) p (length_n_codes (SUC n)) = sym_noise_dist n p (length_n_codes n)
Proof
  rpt strip_tac
  >> gvs[length_n_codes_suc]
  >> irule sym_noise_dist_suc_general
  >> gvs[]
QED

Theorem sym_noise_prob_space_is_prob_space:
  ∀n p.
    0 ≤ p ∧ p ≤ 1 ⇒
    prob_space (sym_noise_prob_space n p)
Proof
  rpt strip_tac
  >> drule_all complement_prob >> strip_tac
  >> ‘p ≠ −∞’ by gvs[le_not_infty]
  >> ‘p ≠ +∞’ by gvs[le_1_not_posinf]
  >> ‘1 - p ≠ −∞’ by gvs[le_not_infty]
  >> ‘1 - p ≠ +∞’ by gvs[le_1_not_posinf]
  >> gvs[prob_space_def]
  >> gvs[sym_noise_prob_space_measure_space]
  >> gvs[sym_noise_prob_space_def]
  >> Induct_on ‘n’
  >- gvs[sym_noise_dist_def, length_n_codes_def, num_errors_def, sym_noise_mass_func_def]
  >> drule EQ_SYM >> pop_assum kall_tac >> strip_tac
  >> pop_assum $ (fn th => PURE_REWRITE_TAC [th])
  (* The probability of the two bitstrings [0, 1, 0] and [1, 1, 0]
     corresponds to the probability of the bitstring [1, 0], for example *)
  >> gvs[sym_noise_dist_suc]
QED

(* -------------------------------------------------------------------------- *)
(* Takes an input probability distribution and returns the output probability *)
(* distribution with errors randomly added                                    *)
(* ---                                                                        *)
(* Note: there was an error in the way this was defined, but it turns out to  *)
(* be equivalent and provides a simpler definition, so I kept it that way.    *)
(*                                                                            *)
(* Given an original bitstring bs, the probability of a given output          *)
(* bitstring should be calculated as the probability of choosing a noise      *)
(* bitstring such that applying the noise bitstring to the original bistring  *)
(* results in the output bitstring.                                           *)
(*                                                                            *)
(* This function instead treats the output bitstring as noise (which it isn't)*)
(* , then it applies it as noise to the original bitstring, and checks what   *)
(* the probability of the resulting bitstring being chosen as noise is.       *)
(*                                                                            *)
(* However, this is equivalent, because there is exactly one choice of noise  *)
(* that, when applied to the original bitstring, returns the output bitstring,*)
(* and this choice of noise is precisely that obtained by applying the output *)
(* bitstring to the original bitstring. This follows from the fact that       *)
(* apply_noise is its own inverse, and so if we let bs denote the original    *)
(* bitstring and we let cs denote the output bitstring, we have               *)
(* apply_noise bs (apply_noise bs cs) = cs, and so the unique choice of noise *)
(* returning the output bitstring is when applied to the original bistring is *)
(* precisely that which is obtained by applying the original bitstring to the *)
(* output bitstring.                                                          *)
(*                                                                            *)
(* The equivalence of these definitions is formally proven in                 *)
(* sym_err_chan_prob_space_apply_noise_distribution, which proves that        *)
(* sym_err_chan_prob_space is the resulting distribution when applying noise  *)
(* derived from the distribution sym_noise_dist to a certain bitstring        *)
(* -------------------------------------------------------------------------- *)
Definition sym_err_chan_mass_func_def:
  sym_err_chan_mass_func (n : num) (p : extreal) (bs : bool list) = (sym_noise_mass_func n p) ∘ (apply_noise bs)
End

Definition sym_err_chan_dist_def:
  sym_err_chan_dist n p bs = ∑ (sym_err_chan_mass_func n p bs)
End

Definition sym_err_chan_prob_space_def:
  sym_err_chan_prob_space n p bs = (length_n_codes n, POW (length_n_codes n), sym_err_chan_dist n p bs)
End

(* Provide a nicer interpretation of bitwise than its original definition *)
Theorem bitwise_el:
  ∀f bs cs x.
    LENGTH bs = LENGTH cs ∧ x < LENGTH bs ⇒
    ((EL x (bitwise f bs cs)) ⇔ f (EL x bs) (EL x cs))
Proof
  rpt strip_tac
  >> gvs[bitwise_def, EL_MAP, EL_ZIP]
QED

Theorem bitwise_length:
  ∀f bs cs.
    LENGTH (bitwise f bs cs) = MAX (LENGTH bs) (LENGTH cs)
Proof
  simp[bitwise_def]
QED

Theorem bitwise_eq:
  ∀f bs cs ds.
    LENGTH bs = LENGTH cs ∧ LENGTH cs = LENGTH ds ⇒
    (bitwise f bs cs = ds ⇔ (∀x. x < LENGTH bs ⇒ f (EL x bs) (EL x cs) = EL x ds))
Proof
  rpt strip_tac
  >> EQ_TAC >> rpt strip_tac >> gvs[]
  >- (irule EQ_SYM
      >> irule bitwise_el
      >> gvs[])
  >> irule $ iffRL LIST_EQ_REWRITE
  >> REVERSE conj_tac
  >> gvs[bitwise_length]
  >> rpt strip_tac
  >> first_x_assum $ qspec_then ‘x’ (fn th => gvs[GSYM th])
  >> irule bitwise_el
  >> gvs[]
QED

Theorem NOT_IFF_INV:
  ∀ b c.
    (b ⇎ (b ⇎ c)) ⇔ c
Proof
  rpt strip_tac
  >> Cases_on ‘b’ >> gvs[]
QED

Theorem bxor_inv:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    bxor bs (bxor bs cs) = cs
Proof
  rpt strip_tac
  >> gvs[bxor_def]
  >> irule $ iffRL bitwise_eq
  >> gvs[bitwise_length]
  >> rpt strip_tac
  >> DEP_PURE_ONCE_REWRITE_TAC [bitwise_el]
  >> gvs[NOT_IFF_INV]
QED

Theorem bxor_length:
  ∀bs cs.
    LENGTH (bxor bs cs) = MAX (LENGTH bs) (LENGTH cs)
Proof
  simp[bxor_def, bitwise_length]
QED

Theorem bxor_inj:
  ∀bs. INJ (bxor bs) (length_n_codes (LENGTH bs)) (length_n_codes (LENGTH bs))
Proof
  rpt strip_tac
  >> gvs[INJ_DEF]
  >> rpt strip_tac
  >- gvs[length_n_codes_def, bxor_length]
  >> qspecl_then [‘bs’, ‘x’] assume_tac bxor_inv
  >> qspecl_then [‘bs’, ‘y’] assume_tac bxor_inv
  >> gvs[length_n_codes_def]
QED

Theorem apply_noise_inj:
  ∀bs.
    INJ (apply_noise bs) (length_n_codes (LENGTH bs)) (length_n_codes (LENGTH bs))
Proof
  gvs[apply_noise_def, bxor_inj]
QED

Theorem apply_noise_inv:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    apply_noise bs (apply_noise bs cs) = cs
Proof
  gvs[apply_noise_def, bxor_inv]
QED

Theorem sym_err_chan_dist_sym_noise_dist:
  ∀n p bs s.
    0 ≤ p ∧ p ≤ 1 ∧ bs ∈ length_n_codes n ∧ s ⊆ length_n_codes n ⇒
    sym_err_chan_dist n p bs s = sym_noise_dist n p (IMAGE (apply_noise bs) s)
Proof
  rpt strip_tac
  >> gvs[sym_err_chan_dist_def, sym_err_chan_mass_func_def, sym_noise_dist_def]
  >> irule $ GSYM EXTREAL_SUM_IMAGE_IMAGE
  >> conj_tac
  >- metis_tac[SUBSET_FINITE, length_n_codes_finite]
  >> gvs[]
  >> rpt strip_tac
  >- (disj1_tac >> gvs[sym_noise_mass_func_not_neginf])
  >> irule INJ_IMAGE
  >> qexists ‘length_n_codes n’
  >> irule INJ_SUBSET
  >> qexistsl [‘length_n_codes n’, ‘length_n_codes n’]
  >> gvs[apply_noise_inj, length_n_codes_def]
QED

Theorem apply_noise_length:
  ∀n bs cs.
    LENGTH (apply_noise bs cs) = MAX (LENGTH bs) (LENGTH cs)
Proof
  rpt strip_tac
  >> gvs[apply_noise_def, bxor_length]
QED

Theorem apply_noise_length_n_codes:
  ∀n bs cs.
    bs ∈ length_n_codes n ∧ cs ∈ length_n_codes n ⇒
    apply_noise bs cs ∈ length_n_codes n
Proof
  simp[length_n_codes_def, apply_noise_length]
QED

Theorem apply_noise_image_length_n_codes:
  ∀n bs s.
    bs ∈ length_n_codes n ∧ s ⊆ length_n_codes n ⇒
    IMAGE (apply_noise bs) s ⊆ length_n_codes n
Proof
  rpt strip_tac
  >> gvs[IMAGE_DEF]
  >> gvs[SUBSET_DEF]
  >> rpt strip_tac
  >> gvs[apply_noise_length_n_codes]
QED

Theorem apply_noise_random_variable:
  ∀n p bs.
    LENGTH bs = n ⇒
    random_variable (apply_noise bs) (sym_noise_prob_space n p) (measurable_space (sym_err_chan_prob_space n p bs))
Proof
  rpt strip_tac
  >> gvs[random_variable_def]
  >> gvs[measurable_def]
  >> gvs[IN_DEF]
  >> rpt strip_tac
  >- gvs[sym_noise_prob_space_def, sym_err_chan_prob_space_def, p_space_def, length_n_codes_def, apply_noise_length]
  >> gvs[sym_noise_prob_space_def, sym_err_chan_prob_space_def, events_def, p_space_def]
QED

Theorem apply_noise_preimage_length_n_codes:
  ∀n bs s.
    LENGTH bs = n ∧ s ⊆ length_n_codes n ⇒
    (PREIMAGE (apply_noise bs) s) ∩ length_n_codes n = IMAGE (apply_noise bs) s
Proof
  rpt strip_tac
  >> irule $ iffRL EXTENSION
  >> rpt strip_tac
  >> EQ_TAC >> strip_tac
  >- (gvs[PREIMAGE_def]
      >> qexists ‘apply_noise bs x’
      >> gvs[]
      >> DEP_PURE_REWRITE_TAC[apply_noise_inv]
      >> gvs[length_n_codes_def])
  >> gvs[PREIMAGE_def]
  >> conj_tac
  >- (DEP_PURE_REWRITE_TAC[apply_noise_inv]
      >> gvs[length_n_codes_def, SUBSET_DEF])
  >> gvs[SUBSET_DEF]
  >> last_x_assum $ qspec_then ‘x'’ assume_tac
  >> gvs[]
  >> DEP_PURE_REWRITE_TAC[apply_noise_length_n_codes]
  >> gvs[length_n_codes_def]
QED

Theorem sym_err_chan_prob_space_apply_noise_distribution:
  ∀n p bs s.
    0 ≤ p ∧ p ≤ 1 ∧ LENGTH bs = n ∧ s ⊆ length_n_codes n ⇒
    distribution (sym_noise_prob_space n p) (apply_noise bs) s = sym_err_chan_dist n p bs s
Proof
  rpt strip_tac
  >> gs[distribution_def, sym_noise_prob_space_def, prob_def, p_space_def]
  >> DEP_PURE_REWRITE_TAC[sym_err_chan_dist_sym_noise_dist]
  >> gs[]
  >> conj_tac >- gs[length_n_codes_def]
  >> AP_TERM_TAC
  >> gvs[apply_noise_preimage_length_n_codes]
QED

(* measure_preserving *)
(* distribution_def
   distr_def
   measure_space_distr
   distribution_prob_space
 *)

Theorem algebra_space_in_subsets:
  ∀a. algebra a ⇒ space a ∈ subsets a
Proof
  rpt strip_tac
  >> gvs[algebra_def]
  >> last_x_assum $ qspec_then ‘∅’ assume_tac
  >> gvs[]
QED

Theorem measure_space_is_measurable:
  ∀s a p.
    measure_space (s, a, p) ⇒ s ∈ a
Proof
  rpt strip_tac
  >> gvs[measure_space_def, sigma_algebra_def]
  >> drule algebra_space_in_subsets
  >> gvs[]
QED

Theorem sample_space_is_event:
  ∀s a p.
    prob_space (s, a, p) ⇒ s ∈ a
Proof
  rpt strip_tac
  >> drule EVENTS_ALGEBRA >> strip_tac
  >> gvs[p_space_def, events_def]
  >> drule algebra_space_in_subsets
  >> gvs[]
QED

(* similar in spirit to measure_space_cong *)
Theorem prob_space_cong:
  ∀s a p1 p2.
    (∀x. x ∈ a ⇒ p1 x = p2 x) ⇒
    (prob_space (s, a, p1) ⇔ prob_space (s, a, p2))
Proof
  rpt strip_tac
  >> gvs[prob_space_def]
  >> irule AND_CONG
  >> conj_tac
  >- (disch_tac
      >> first_x_assum $ qspec_then ‘s’ assume_tac
      >> drule measure_space_is_measurable
      >> gvs[])
  >> disch_tac
  >> irule measure_space_cong
  >> gvs[]
QED

Theorem sym_err_chan_prob_space_is_prob_space:
  ∀n p bs.
    0 ≤ p ∧ p ≤ 1 ∧
    bs ∈ length_n_codes n ⇒
    prob_space (sym_err_chan_prob_space n p bs)
Proof
  rpt strip_tac
  >> gvs[sym_err_chan_prob_space_def]
  >> qmatch_goalsub_abbrev_tac ‘prob_space (s, a, p1)’
  >> qspecl_then [‘s’, ‘a’, ‘p1’, ‘distribution (sym_noise_prob_space n p) (apply_noise bs)’] assume_tac prob_space_cong
  >> pop_assum $ (fn th => DEP_PURE_REWRITE_TAC [th])
  >> rpt strip_tac
  >- (unabbrev_all_tac
      >> irule $ GSYM sym_err_chan_prob_space_apply_noise_distribution
      >> gvs[POW_DEF, length_n_codes_def])
  >> gvs[Abbr ‘p1’]
  >> qspecl_then [‘sym_noise_prob_space n p’, ‘apply_noise bs’, ‘measurable_space (sym_err_chan_prob_space n p bs)’] assume_tac distribution_prob_space
  >> gvs[sym_err_chan_prob_space_def]
  >> pop_assum irule
  >> conj_tac
  >- gvs[sym_noise_prob_space_is_prob_space]
  >> conj_tac
  >- (unabbrev_all_tac >> gvs[POW_SIGMA_ALGEBRA])
  >> unabbrev_all_tac
  >> gs[length_n_codes_def]
  >> drule apply_noise_random_variable
  >> rpt strip_tac
  >> gvs[sym_err_chan_prob_space_def, length_n_codes_def]
QED

(* ----------------------------------------------- *)

Definition n_repetition_bit_def:
  n_repetition_bit 0 b = [] ∧
  n_repetition_bit (SUC n) b = b::(n_repetition_bit n b)
End

Definition n_repetition_code_def:
  n_repetition_code n [] = [] ∧
  n_repetition_code n (b::bs) = (n_repetition_bit n b) ⧺ (n_repetition_code n bs)
End

(*Definition valid_codes_def:
  valid_codes n code_fn = IMAGE code_fn (length_n_codes n)
End*)


Definition decode_nearest_neighbour_def:
  decode_nearest_neighbour 
End

(* What if there are multiple nearest codes? Should we have an is_nearest_code
   function which returns true for each choice of nearest code? *)
Definition nearest_code_def:
  nearest_code n code_fn bs =
  @cs. (cs ∈ length_n_codes n ∧
        ∀ds. ds ∈ length_n_codes n ⇒ hamming_distance (code_fn bs cs ≤ hamming_distance bs ds)
        End

Definition n_repetition_bit_inverse_def:
  (n_repetition_bit_inverse (nT : num) (nF : num) ([] : bool list) = if nT ≤ nF then F else T) ∧
  n_repetition_bit_inverse nT nF (T::bs) = n_repetition_bit_inverse (nT + 1) nF bs ∧ 
  n_repetition_bit_inverse nT nF (F::bs) = n_repetition_bit_inverse nT (nF + 1) bs
End

Theorem WF_LENGTH:
  WF (λbs cs : α list. LENGTH bs < LENGTH cs)
Proof
  gvs[WF_DEF]
  >> rpt strip_tac
  >> assume_tac WF_num
  >> drule $ iffLR WF_DEF >> strip_tac
  >> first_x_assum $ qspec_then ‘IMAGE (λbs. LENGTH bs) B’ assume_tac
  >> gvs[]
  >> rpt strip_tac
  >> qmatch_asmsub_abbrev_tac ‘p ⇒ g’
  >> sg ‘p’
  >- (unabbrev_all_tac >> qexists ‘w’ >> gvs[IN_DEF])
  >> gvs[]
  >> pop_assum kall_tac
  >> qexists ‘bs’
  >> gvs[IN_DEF]
QED

Theorem WF_IMAGE:
  ∀R f. WF R ⇒ WF (λx y. R (f x) (f y))
Proof
  rpt strip_tac
  >> gvs[WF_DEF]
  >> rpt strip_tac
  >> first_x_assum $ qspec_then ‘IMAGE f B’ assume_tac
  >> qmatch_asmsub_abbrev_tac ‘p ⇒ g’
  >> sg ‘p’
  >- (unabbrev_all_tac >> qexists ‘f w’ >> gvs[IMAGE_DEF] >> qexists ‘w’ >> gvs[IN_DEF])
  >> gvs[]
  >> pop_assum kall_tac
  >> qexists ‘x’
  >> conj_tac
  >- gvs[IN_DEF]
  >> gen_tac
  >> disch_tac
  >> first_x_assum $ qspec_then ‘f x'’ assume_tac
  >> gvs[]
  >> first_x_assum $ qspec_then ‘x'’ assume_tac
  >> gvs[IN_DEF]
QED

Definition n_repetition_code_inverse_def:
  n_repetition_code_inverse n ([] : bool list) = [] ∧
  n_repetition_code_inverse 0 bs = [] ∧
  n_repetition_code_inverse (SUC n) bs = (n_repetition_bit_inverse 0 0 (TAKE (SUC n) bs))::(n_repetition_code_inverse (SUC n) (DROP (SUC n) bs))
Termination
  qexists ‘(λbs cs. (LENGTH (SND bs) < LENGTH (SND cs)))’
  >> conj_tac
  >- (qspecl_then [‘$< : num -> num -> bool’, ‘(LENGTH ∘ SND) : num # bool list -> num’] assume_tac WF_IMAGE >> gvs[WF_num])
  >> rpt strip_tac
  >> gvs[]
End

Definition q2_sym_prob_space_def:
  q2_sym_prob_space p = ((length_n_codes_uniform_prob_space 1) × (sym_noise_prob_space 3 p))
End

(* Check that after encoding a bitstring, applying a specific choice of
   noise, and then decoding the bitstring, we get the correct result *)
Definition code_decodes_correctly_def:
  code_decodes_correctly (n : num) (bs : bool list) (ns : bool list) (code_fn : bool list -> bool list) : bool
  = ((nearest_code n code_fn (apply_noise ns (code_fn bs))) = bs)
End

Definition q2_sym_prob_correctly_decoded_def:
  q2_sym_prob_correctly_decoded p = (measure (q2_sym_prob_space p)) {(bs, ns) | bs ∈ length_n_codes 1 ∧ (code_decodes_correctly 1 bs ns (n_repetition_code 3))} 
End

Theorem SELECT_WEAKEN_CONDITION:
  ∀P Q. (∃x. P x) ∧ (∀x. P x ⇒ Q x) ⇒ Q (@x. P x)
Proof
  rpt strip_tac
  >> pop_assum irule
  >> irule (iffRL SELECT_THM)
  >> qexists ‘x’
  >> gvs[]      
QED

Theorem hamming_distance_cons:
  ∀b bs c cs.
    hamming_distance (b::bs) (c::cs) = (if b = c then 0 else 1) + hamming_distance bs cs
Proof
  rpt strip_tac
  >> gvs[hamming_distance_def]
QED

Theorem hamming_distance_append:
  ∀bs cs ds es.
    LENGTH bs = LENGTH ds ⇒
    hamming_distance (bs ⧺ cs) (ds ⧺ es) = hamming_distance bs ds + hamming_distance cs es
Proof
  strip_tac
  >> Induct_on ‘bs’ >> rpt strip_tac
  >- gvs[hamming_distance_def]
  >> Cases_on ‘ds’ >> gvs[]
  >> gvs[hamming_distance_cons]
QED

Theorem n_repetition_bit_hamming_distance:
  ∀b b' n.
    hamming_distance (n_repetition_bit n b) (n_repetition_bit n b') = if b = b' then 0 else n
Proof
  rpt strip_tac
  >> Induct_on ‘n’
  >- gvs[n_repetition_bit_def, hamming_distance_def]
  >> Cases_on ‘b = b'’ >> gvs[]
  >- (gvs[n_repetition_bit_def]
      >> gvs[hamming_distance_cons])
  >> gvs[n_repetition_bit_def, hamming_distance_cons]
QED

Theorem n_repetition_bit_length:
  ∀n b. LENGTH (n_repetition_bit n b) = n
Proof
  rpt strip_tac
  >> Induct_on ‘n’ >> gvs[n_repetition_bit_def]
QED

Theorem n_repetition_code_hamming_distance:
  ∀bs cs n.
          LENGTH bs = LENGTH cs ∧
          hamming_distance (n_repetition_code n bs) (n_repetition_code n cs) < n ⇒
          bs = cs
Proof
  gen_tac
  >> Induct_on ‘bs’ >> rpt strip_tac
  >- (Cases_on ‘cs’ >> gvs[])
  >> Cases_on ‘cs’ >> gvs[]
  >> gvs[n_repetition_code_def]
  >> last_x_assum $ qspecl_then [‘t’, ‘n’] assume_tac
  >> gvs[]
  >> qspecl_then [‘[h]’, ‘bs’, ‘[h']’, ‘t’] assume_tac hamming_distance_append
  >> gvs[]
  >> gvs[hamming_distance_cons]
  >> pop_assum kall_tac
  >> DEP_PURE_ONCE_ASM_REWRITE_TAC[]
  >> gvs[]
  >> pop_assum kall_tac
  >> qspecl_then [‘n_repetition_bit n h’, ‘n_repetition_code n bs’, ‘n_repetition_bit n h'’, ‘n_repetition_code n t’] assume_tac hamming_distance_append
  >> gvs[n_repetition_bit_length]
  >> pop_assum kall_tac
  >> qmatch_asmsub_abbrev_tac ‘a + b < n’
  >> ‘a < n’ by gvs[]
  >> unabbrev_all_tac
  >> qpat_x_assum ‘_ + _ < _’ kall_tac
  >> gvs[n_repetition_bit_hamming_distance]
  >> Cases_on ‘h = h'’ >> gvs[]
QED

Theorem nearest_code_n_repetition_code_3:
  ∀bs ns.
    bs ∈ length_n_codes 1 ∧
    ns ∈ length_n_codes 3 ⇒
    (nearest_code 1 (n_repetition_code 3) (apply_noise ns (n_repetition_code 3 bs)) = bs ⇔ num_errors ns ≤ 1)
Proof
  rpt strip_tac
  >> REVERSE EQ_TAC >> disch_tac
  >- (gvs[nearest_code_def]
      >> qspecl_then [‘λcs. cs ∈ valid_codes 1 (n_repetition_code 3) ∧ ∀ds. ds ∈ valid_codes 1 (n_repetition_code 3) ⇒ hamming_distance (apply_noise ns (n_repetition_code 3 bs)) cs ≤ hamming_distance (apply_noise ns (n_repetition_code 3 bs)) ds’, ‘λx. x = bs’] assume_tac SELECT_WEAKEN_CONDITION
      >> gvs[] (* TODO: This takes too long. But it works. *)
      >> pop_assum irule
      >> conj_tac
      >- (rpt strip_tac
          >> qspecl_then [‘x’, ‘bs’, ‘3’] assume_tac n_repetition_code_hamming_distance
          >> sg ‘LENGTH x = LENGTH bs’
          >- (gvs[length_n_codes_def, valid_codes_def]

              >>pop_assum irule
              >> asm_rewrite_tac [] gvs[]
              >> asm_simp_tac bool_ss []
              >> rfs[] asm_rewrite_tac bool_ss []
                    simp[]
              >> irule SELECT_WEAKEN_CONDITION
              >> sg ‘’
              >> sg ‘∀P. ((@cs. P cs) = bs ⇒ P (@cs. P cs))’
              >> gvs[SELECT_THM]

                    SELECT_THM
                    
QED

(*Theorem nearest_code_n_repetition_code:
  ∀bs ns n.
    bs ∈ length_n_codes 1 ∧
    ns ∈ length_n_codes n ⇒
    nearest_code 1 (n_repetition_code n) *)
          
Theorem code_decodes_correctly_n_repetition_code_3:
  ∀bs ns.
    ns ∈ length_n_codes 3 ⇒
    (code_decodes_correctly 1 bs ns (n_repetition_code 3) ⇔ num_errors ns ≤ 1)
Proof
  rpt strip_tac
  >> REVERSE EQ_TAC >> disch_tac
  >- (gvs[code_decodes_correctly_def]
      >> gvs[nearest_code_def]
      >> 
      >>
      >> qmatch_goalsub_abbrev_tac ‘ch = bs’
      >> sg ‘ch ∈ valid_codes 1 (n_repetition_code 3)’
      >- gvs[Abbr ‘ch’, SELECT_THM]
      >> sg ‘bs ∈ valid_codes 1 (n_repetition_code 3)’
      >> sg ‘∀ds. ds ∈ valid_codes 1 (n_repetition_code 3) ⇒
                  hamming_distance (apply_noise ns (n_repetition_code 3 bs)) cs ≤
                  hamming_distance (apply_noise ns (n_repetition_code 3 bs)) bs’
      >> gvs[]
            
QED
      
Theorem q2_sym_prob_correctly_decoded_prob:
  ∀p.
    q2_sym_prob_correctly_decoded (p : extreal) = ((1 - p) pow 2) * (2 * p + 1)
Proof
  gen_tac
  >> simp[q2_sym_prob_correctly_decoded_def, q2_sym_prob_space_def]
         
  >> simp[]
QED

(* 50% chance of 1, 50% chance of 0 *)
(* code_fn encodes this into 111 or 000 *)
(* symmetric noise corrupts this *)
(* decoded using nearest neighbour method. *)
(* probability of the result being correct*)
(*Theorem 

Proof
QED*)


(*Theorem :
  ∀n p bs.
    (measure (sym_err_chan_prob_space n p bs))
Proof
QED*)


val _ = export_theory();

