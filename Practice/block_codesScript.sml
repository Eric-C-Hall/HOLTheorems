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
open prim_recTheory;
open dividesTheory;
open bitTheory;
open RealArith;

open jared_yeager_prob_space_product_spaceTheory;
open WFTheoremsTheory;

open dep_rewrite;
open simpLib;

use "donotexpandScript.sml";

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

Definition hamming_distance_alt_def[simp]:
  hamming_distance_alt [] (l2 : α list) = 0 ∧
  hamming_distance_alt (h1::t1 : α list) (h2::t2 : α list) = (if (h1 = h2) then 0n else 1n) + hamming_distance_alt t1 t2
End

Theorem hamming_distance_empty[simp]:
  ∀cs. hamming_distance [] [] = 0
Proof
  gvs[hamming_distance_def]
QED

Theorem hamming_distance_cons[simp]:
  ∀b bs c cs.
    hamming_distance (b::bs) (c::cs) = (if b = c then 0 else 1) + hamming_distance bs cs
Proof
  rpt strip_tac
  >> gvs[hamming_distance_def]
QED

Theorem hamming_distance_alt_equivalent:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    hamming_distance bs cs = hamming_distance_alt bs cs
Proof
  strip_tac
  >> Induct_on ‘bs’ >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘cs’  >> gvs[]
QED

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
      >> qsuff_tac `&CARD (s' ∪ t) : extreal = &CARD(s') + &CARD(t)`
      >- (rpt strip_tac
          >> irule EQ_SYM
          >> pop_assum (fn th => PURE_REWRITE_TAC [th])
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
  >> sg ‘∀s t : extreal -> bool. sup s = +∞ ⇒ sup (s ∪ t) = max (sup s) (sup t)’
  >- (rpt strip_tac
      >> drule (iffLR EXTREAL_SUP_POSITIVE_INFINITY)
      >> rpt strip_tac
      >> gvs[]
      >> PURE_REWRITE_TAC[Once extreal_sup_def]
      >> qmatch_goalsub_abbrev_tac `if c1 then _ else (if c2 then _ else _)`
      >> `c1` suffices_by gvs[]
      >> gvs[Abbr `c1`, Abbr `c2`]
     )
  >> Cases_on ‘sup s = +∞’ >> gvs[]
  >> Cases_on ‘sup t = +∞’
  >- (first_x_assum $ qspecl_then [`t`, `s`] assume_tac >> gvs[UNION_COMM])
  >> last_x_assum kall_tac
  (* Handle case where either of the supremums is negative infinity *)
  >> sg ‘∀s t : extreal -> bool. sup s = −∞ ⇒ sup (s ∪ t) = max (sup s) (sup t)’
  >- (rpt (pop_assum kall_tac)
      >> rpt strip_tac
      >> gvs[]
      >> PURE_REWRITE_TAC[Ntimes extreal_sup_def 2]
      >> qmatch_goalsub_abbrev_tac `(if c1 then _ else (if c2 then _ else e1)) = (if c3 then _ else (if c4 then _ else e2))`
      >> `c1 = c3 ∧ c2 = c4 ∧ e1 = e2` suffices_by gvs[]
      >> conj_tac
      >- (unabbrev_all_tac
          >> qmatch_goalsub_abbrev_tac `b1 ⇔ b2`
          >> Cases_on `b1` >> Cases_on `b2` >> rfs[]
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
  >> qpat_x_assum ‘∀a b. _’ kall_tac
  >> Cases_on `sup (s ∪ t) = +∞`
  >- (drule (iffLR EXTREAL_SUP_POSITIVE_INFINITY) >> strip_tac
      >> drule EXTREAL_SUP_NOT_POSITIVE_INFINITY >> strip_tac
      >> qspec_then `s` assume_tac EXTREAL_SUP_NOT_POSITIVE_INFINITY
      >> rfs[]
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
  >> Cases_on ‘c’ >> gvs[]
  >> qspecl_then [`s ∪ t`, `r`] assume_tac EXTREAL_SUP_REAL_SUP
  >> qspecl_then [`s`, `r'`] assume_tac EXTREAL_SUP_REAL_SUP
  >> qspecl_then [‘t’, ‘r''’] assume_tac EXTREAL_SUP_REAL_SUP
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
  >> qspecl_then [`t`] assume_tac EXTREAL_SUP_NOT_NEGATIVE_INFINITY
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
  >> gvs[]
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

Definition n_repetition_bit_def[simp]:
  n_repetition_bit 0 b = [] ∧
  n_repetition_bit (SUC n) b = b::(n_repetition_bit n b)
End

Definition n_repetition_code_def[simp]:
  n_repetition_code n [] = [] ∧
  n_repetition_code n (b::bs) = (n_repetition_bit n b) ⧺ (n_repetition_code n bs)
End

Definition is_decoded_nearest_neighbour_def:
  is_decoded_nearest_neighbour n code_fn bs cs =
  (cs ∈ length_n_codes n ∧
   ∀ds. ds ∈ length_n_codes n ⇒
        hamming_distance bs (code_fn cs) ≤ hamming_distance bs (code_fn ds))
End

(* What if there are multiple nearest neighbours? *)
Definition decode_nearest_neighbour_def:
  decode_nearest_neighbour n code_fn bs =
  @cs. is_decoded_nearest_neighbour n code_fn bs cs
End

Definition n_repetition_bit_inverse_def:
  (n_repetition_bit_inverse (nT : num) (nF : num) ([] : bool list) = if nT ≤ nF then F else T) ∧
  n_repetition_bit_inverse nT nF (T::bs) = n_repetition_bit_inverse (nT + 1) nF bs ∧ 
  n_repetition_bit_inverse nT nF (F::bs) = n_repetition_bit_inverse nT (nF + 1) bs
End

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
  = ((decode_nearest_neighbour n code_fn (apply_noise ns (code_fn bs))) = bs)
End

Definition q2_sym_prob_correctly_decoded_def:
  q2_sym_prob_correctly_decoded p = (measure (q2_sym_prob_space p)) {(bs, ns) | bs ∈ length_n_codes 1 ∧ ns ∈ length_n_codes 3 ∧ (code_decodes_correctly 1 bs ns (n_repetition_code 3))} 
End

(*Definition q2_asym_prob_space_def:
  q2_asym_prob_space p = ((length_n_codes_uniform_prob_space 1) × ()
                          End*)

(*Definition q2_asym_prob_correctly_decoded_def:
  q2_asym_prob_correctly_decoded p = (measure ()) {}
End*)

Theorem SELECT_WEAKEN_CONDITION:
  ∀P Q. (∃x. P x) ∧ (∀x. P x ⇒ Q x) ⇒ Q (@x. P x)
Proof
  rpt strip_tac
  >> pop_assum irule
  >> irule (iffRL SELECT_THM)
  >> qexists ‘x’
  >> gvs[]      
QED

Theorem hamming_distance_append[simp]:
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

Theorem n_repetition_bit_hamming_distance[simp]:
  ∀b b' n.
    hamming_distance (n_repetition_bit n b) (n_repetition_bit n b') = if b = b' then 0 else n
Proof
  rpt strip_tac
  >> Induct_on ‘n’
  >- gvs[n_repetition_bit_def, hamming_distance_def]
  >> Cases_on ‘b = b'’ >> gvs[]
QED

Theorem n_repetition_bit_length[simp]:
  ∀n b. LENGTH (n_repetition_bit n b) = n
Proof
  rpt strip_tac
  >> Induct_on ‘n’ >> gvs[n_repetition_bit_def]
QED

Theorem n_repetition_code_hamming_distance[simp]:
  ∀bs cs n.
    LENGTH bs = LENGTH cs ⇒
    hamming_distance (n_repetition_code n bs) (n_repetition_code n cs) = n * hamming_distance bs cs
Proof
  strip_tac
  >> Induct_on ‘bs’ >> Cases_on ‘cs’ >> gvs[]
  >> rpt strip_tac
  >> last_x_assum $ qspecl_then [‘t’, ‘n’] assume_tac
  >> gvs[]
  >> Cases_on ‘h' = h’ >> gvs[]
QED

Theorem n_repetition_code_hamming_distance':
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
  >> Cases_on ‘h = h'’ >> gvs[]
QED

Theorem exists_decode_nearest_neighbour_candidate:
  ∀n code_fn bs.
    ∃ds. is_decoded_nearest_neighbour n code_fn bs ds
Proof
  rpt strip_tac
  >> gvs[is_decoded_nearest_neighbour_def]
  >> sg ‘let f n = (λn. hamming_distance bs (code_fn n)) n in WF (λx y. f x < f y)’
  >- (PURE_REWRITE_TAC[Once LET_THM]
      >> CONV_TAC BETA_CONV
      >> irule WF_IMAGE
      >> gvs[WF_LESS])
  >> gvs[WF_DEF]
  >> pop_assum $ qspec_then ‘length_n_codes n’ assume_tac
  >> qmatch_asmsub_abbrev_tac ‘prem ⇒ concl’
  >> sg ‘prem’
  >- (unabbrev_all_tac
      >> qexists ‘n_repetition_bit n T’
      >> gvs[length_n_codes_def, n_repetition_bit_length])
  >> gvs[]
  >> qexists ‘y’ >> gvs[IN_DEF]
  >> rpt strip_tac
  >> first_x_assum $ qspec_then ‘ds’ assume_tac
  >> gvs[]
QED

Theorem n_repetition_code_0[simp]:
  ∀bs.
    n_repetition_code 0 bs = []
Proof
  Induct_on ‘bs’ >> gvs[n_repetition_code_def, n_repetition_bit_def]
QED

Theorem n_repetition_code_divides:
  ∀bs cs n.
    LENGTH bs = LENGTH cs ⇒
    divides n (hamming_distance (n_repetition_code n bs) (n_repetition_code n cs))
Proof
  strip_tac
  >> Induct_on ‘bs’ >> rpt strip_tac
  >- (Cases_on ‘cs’ >> gvs[n_repetition_code_def])
  >> Cases_on ‘cs’ >> gvs[]
  >> last_x_assum $ qspecl_then [‘t’, ‘n’] assume_tac
  >> gvs[n_repetition_code_def, hamming_distance_cons]
  >> DEP_PURE_ONCE_REWRITE_TAC[hamming_distance_append]
  >> gvs[n_repetition_bit_length]
  >> irule DIVIDES_ADD_1 >> gvs[]
  >> pop_assum kall_tac
  >> gvs[n_repetition_bit_hamming_distance]
  >> Cases_on ‘h = h'’ >> gvs[]
QED

Theorem hamming_distance_positivity:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    0 ≤ hamming_distance bs cs ∧
    (hamming_distance bs cs = 0 ⇔ bs = cs)
Proof
  rpt strip_tac
  >- gvs[hamming_distance_def]
  >> ‘∀cs. LENGTH bs = LENGTH cs ⇒ (hamming_distance bs cs = 0 ⇔ bs = cs)’ suffices_by gvs[]
  >> pop_assum kall_tac
  >> Induct_on ‘bs’ >> rpt strip_tac >> Cases_on ‘cs’ >> gvs[]
  >> EQ_TAC >> rpt strip_tac >> gvs[]
  >> Cases_on ‘h = h'’ >> gvs[]
QED

Theorem hamming_distance_sym:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    hamming_distance bs cs = hamming_distance cs bs
Proof
  strip_tac
  >> Induct_on ‘bs’ >> Cases_on ‘cs’ >> gvs[]
  >> rpt strip_tac
  >> first_x_assum $ qspec_then ‘t’ assume_tac
  >> Cases_on ‘h = h'’ >> gvs[EQ_SYM]
QED

Theorem hamming_distance_same[simp]:
  ∀bs. hamming_distance bs bs = 0
Proof
  rpt strip_tac
  >> assume_tac hamming_distance_positivity
  >> pop_assum $ qspecl_then [‘bs’, ‘bs’] assume_tac
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Initially I thought that the hamming distance between two points precisely *)
(* satisfied the triangle equality if and only if the middle point was one    *)
(* of the endpoints, but this is not necessarily the case.                    *)
(*                                                                            *)
(* hamming (0, 1) (1, 0) = 2                                                  *)
(* hamming (0, 1) (0, 0) + hamming (0, 0) (1, 0) = 1 + 1 = 2                  *)
(* -------------------------------------------------------------------------- *)
Theorem hamming_distance_triangle_inequality:
  ∀bs cs ds.
    (LENGTH bs = LENGTH cs ∧ LENGTH cs = LENGTH ds) ⇒
    hamming_distance bs ds ≤ hamming_distance bs cs + hamming_distance cs ds
Proof
  rpt strip_tac
  >> ‘∀bs ds. LENGTH bs = LENGTH cs ∧ LENGTH cs = LENGTH ds ⇒ hamming_distance bs ds ≤ hamming_distance bs cs + hamming_distance cs ds’ suffices_by gvs[]
  >> rpt $ pop_assum kall_tac
  >> Induct_on ‘cs’ >> rpt strip_tac >> Cases_on ‘bs’ >> Cases_on ‘ds’ >> gvs[]
  >> first_x_assum $ qspecl_then [‘t’, ‘t'’] assume_tac
  >> Cases_on ‘h = h''’ >> Cases_on ‘h' = h’ >> Cases_on ‘h' = h''’ >> gvs[]
QED

(* MODEQ_REFL has two issues: firstly, it isn't in the simpset, when it would
   make sense for it to be. Secondly, the variable n isn't bound by a
   quantifier. *)
Theorem MODEQ_REFL'[simp]:
  ∀n x. MODEQ n x x
Proof
  gvs[MODEQ_REFL]
QED

(* -------------------------------------------------------------------------- *)
(* Consider the hamming distance between two points p and q via a point r.    *)
(* Each change made will modify the result by either 1 or -1. These values    *)
(* are equivalent modulo 2. As a result, the parity of the path between p     *)
(* and q is the same as the parity of the combined paths between p and r and  *)
(* r and q.                                                                   *)
(*                                                                            *)
(* Note: this only works if the elements making up our lists can only take    *)
(* two values. If more than two values are possible, a change can be made     *)
(* which modifies the result by 0, for example, hamming_distance [1] [2]      *)
(* can be changed to hamming_distance [1] [3]. Thus, we need to specify       *)
(* our parameters to the hamming distance as "bool list" instead of "α list"  *)
(* -------------------------------------------------------------------------- *)
Theorem hamming_distance_modeq_2:
  ∀bs cs ds : bool list.
    LENGTH bs = LENGTH cs ∧ LENGTH cs = LENGTH ds ⇒
    MODEQ 2 ((hamming_distance bs cs) + (hamming_distance cs ds)) (hamming_distance bs ds)
Proof
  rpt strip_tac
  >> ‘∀bs ds. LENGTH bs = LENGTH cs ∧ LENGTH cs = LENGTH ds ⇒ MODEQ 2 ((hamming_distance bs cs) + (hamming_distance cs ds)) (hamming_distance bs ds)’ suffices_by gvs[]
  >> rpt $ pop_assum kall_tac
  >> Induct_on ‘cs’ >> rpt strip_tac >> Cases_on ‘bs’ >> Cases_on ‘ds’ >> gvs[]
  >> last_x_assum $ qspecl_then [‘t’, ‘t'’] assume_tac
  >> Cases_on ‘h = h''’ >> Cases_on ‘h' = h’ >> gvs[MODEQ_DEF]
  >- (qexistsl [‘a’, ‘b’] >> gvs[])
  >- (qexistsl [‘a’, ‘b’] >> gvs[])
  >- (qexistsl [‘a’, ‘b’] >> gvs[])
  >> Cases_on ‘h' = h''’
  >- (qexistsl [‘a’, ‘b + 1’] >> gvs[])
  >> Cases_on ‘h’ >> Cases_on ‘h'’ >> Cases_on ‘h''’ >> gvs[]
QED


Theorem length_n_repetition_code[simp]:
  ∀n bs.
    LENGTH (n_repetition_code n bs) = n * LENGTH bs
Proof
  rpt strip_tac
  >> Induct_on ‘bs’ >> gvs[]
  >> pop_assum kall_tac
  >> PURE_REWRITE_TAC[ADD1]
  >> gvs[]
QED

Theorem n_repetition_code_inj:
  ∀n bs cs.
    LENGTH bs = LENGTH cs ∧
    n ≠ 0 ∧
    n_repetition_code n bs = n_repetition_code n cs ⇒
    bs = cs
Proof
  NTAC 2 strip_tac
  >> Induct_on ‘bs’ >> Cases_on ‘cs’ >> gvs[]
  >> rpt strip_tac
  >> last_x_assum $ qspec_then ‘t’ assume_tac
  >> gvs[]
  >> Cases_on ‘n’ >> gvs[]
QED

(*Theorem is_decoded_nearest_neighbour_n_repetition_code_hamming_distance:
  ∀n m bs cs.
    is_decoded_nearest_neighbour n (n_repetition_code m) bs cs ⇒
    hamming_distance (n_repetition_code m cs) bs < m * LENGTH bs
Proof
  rpt strip_tac
  >> 
QED*)

Theorem hamming_distance_length:
  ∀bs cs.
    hamming_distance bs cs ≤ LENGTH bs
Proof
  strip_tac
  >> gvs[hamming_distance_def]
  >> Induct_on ‘bs’ >> gvs[ZIP_def]
  >> strip_tac
  >> Cases_on ‘cs’ >> gvs[ZIP_def]
  >> pop_assum $ qspec_then ‘t’ assume_tac
  >> Cases_on ‘h = h'’ >> gvs[]                            
QED

Theorem decode_nearest_neighbour_n_repetition_bit_unique:
  ∀n bs cs ds.
    ODD n ∧
    bs ∈ length_n_codes n ∧
    is_decoded_nearest_neighbour 1 (n_repetition_code n) bs cs ∧
    is_decoded_nearest_neighbour 1 (n_repetition_code n) bs ds ⇒
    cs = ds
Proof
  rpt strip_tac
  >> ‘divides n (hamming_distance (n_repetition_code n cs) (n_repetition_code n ds))’ by (irule n_repetition_code_divides >> gs[is_decoded_nearest_neighbour_def, length_n_codes_def])
  >> gs[divides_def]
  >> Cases_on ‘q = 0’
  >- (qspecl_then [‘n_repetition_code n cs’, ‘n_repetition_code n ds’] assume_tac (iffLR $ cj 2 hamming_distance_positivity)
      >> gvs[is_decoded_nearest_neighbour_def, length_n_codes_def]
      >> qspecl_then [‘LENGTH bs’, ‘cs’, ‘ds’] irule n_repetition_code_inj
      >> gvs[]
      >> qexists ‘bs’
      >> gvs[]
      >> CCONTR_TAC
      >> gvs[])
  >> Cases_on ‘q = 1’
  >- (gvs[]
      >> gvs[is_decoded_nearest_neighbour_def]
      >> first_assum $ qspec_then ‘cs’ assume_tac
      >> last_assum $ qspec_then ‘ds’ assume_tac
      >> qmatch_asmsub_abbrev_tac ‘d1 ≤ d2’
      >> ‘d1 = d2’ by gvs[]
      >> NTAC 2 $ qpat_x_assum ‘_ ⇒ _’ kall_tac
      >> unabbrev_all_tac
      >> qspecl_then [‘n_repetition_code n cs’, ‘bs’, ‘n_repetition_code n ds’] assume_tac hamming_distance_modeq_2
      >> gvs[]
      >> qmatch_asmsub_abbrev_tac ‘p ⇒ q’
      >> sg ‘p’ >> unabbrev_all_tac
      >- (gvs[length_n_codes_def])
      >> gvs[]
      >> gvs[hamming_distance_sym]
      >> drule $ iffLR MODEQ_THM >> strip_tac >> gvs[]
      >> gvs[ODD_MOD2_LEM])
  >> qspecl_then [‘n_repetition_code n cs’, ‘n_repetition_code n ds’] assume_tac hamming_distance_length
  >> gvs[]
  >> ‘q ≤ 1’ by gvs[is_decoded_nearest_neighbour_def, length_n_codes_def]
  >> gvs[]
QED

Theorem hamming_distance_latter_empty:
  ∀bs. hamming_distance bs [] = 0
Proof
  gvs[hamming_distance_def, ZIP_def]
QED

Theorem hamming_distance_former_empty:
  ∀bs. hamming_distance [] bs = 0
Proof
  gvs[hamming_distance_def, ZIP_def]
QED

Theorem is_decoded_nearest_neighbour_cons:
  ∀n bs1 bs2 c cs code_fn.
    ((∀d ds. code_fn (d::ds) = code_fn [d] ⧺ code_fn ds) ∧
     code_fn [] = [] ∧
     (∀e f. LENGTH (code_fn [e]) = LENGTH (code_fn [f])) ∧
     LENGTH bs1 = LENGTH (code_fn [c])
    ) ⇒
    (is_decoded_nearest_neighbour (SUC n) code_fn (bs1 ⧺ bs2) (c::cs) ⇔
       is_decoded_nearest_neighbour n code_fn bs2 cs ∧
       is_decoded_nearest_neighbour 1 code_fn bs1 [c])
Proof
  rpt strip_tac >> last_x_assum assume_tac >> donotexpand_tac
  >> EQ_TAC
  >- (rpt strip_tac
      >- (gvs[is_decoded_nearest_neighbour_def]
          >> rpt strip_tac
          >- gvs[length_n_codes_def]
          >> first_x_assum $ qspec_then ‘c::ds’ assume_tac
          >> gvs[length_n_codes_def]
          >> doexpand_tac
          >> first_assum $ qspecl_then [‘c’, ‘cs’] assume_tac
          >> first_x_assum $ qspecl_then [‘c’, ‘ds’] assume_tac
          >> gvs[])
      >> gvs[is_decoded_nearest_neighbour_def]
      >> rpt strip_tac
      >- gvs[length_n_codes_def]
      >> first_x_assum $ qspec_then ‘(HD ds)::cs’ assume_tac
      >> gvs[length_n_codes_def]
      >> doexpand_tac
      >> first_assum $ qspecl_then [‘c’, ‘cs’] assume_tac
      >> first_x_assum $ qspecl_then [‘HD ds’, ‘cs’] assume_tac
      >> gvs[]
      >> drule $ iffRL $ cj 2 SING_HD
      >> rpt strip_tac
      >> metis_tac[])
  >> rpt strip_tac
  >> gvs[is_decoded_nearest_neighbour_def]
  >> conj_tac
  >- gvs[length_n_codes_def]
  >> rpt strip_tac
  >> Cases_on ‘ds’
  >- (doexpand_tac
      >> pop_assum $ qspecl_then [‘T’, ‘[]’] assume_tac
      >> gvs[hamming_distance_latter_empty]
      >> gvs[length_n_codes_def])
  >> doexpand_tac
  >> first_assum $ qspecl_then [‘c’, ‘cs’] assume_tac
  >> first_x_assum $ qspecl_then [‘h’, ‘t’] assume_tac
  >> gvs[]
  >> first_x_assum $ qspec_then ‘[h]’ assume_tac
  >> first_x_assum $ qspec_then ‘t’ assume_tac
  >> ‘t ∈ length_n_codes n’ by gvs[length_n_codes_def]
  >> ‘[h] ∈ length_n_codes 1’ by gvs[length_n_codes_def]
  >> gvs[]
QED

Theorem is_decoded_nearest_neighbour_cons_n_repetition_code:
  ∀n m bs1 bs2 c cs.
    LENGTH bs1 = m ⇒
    (is_decoded_nearest_neighbour (SUC n) (n_repetition_code m) (bs1 ⧺ bs2) (c::cs) ⇔
       (is_decoded_nearest_neighbour n (n_repetition_code m) bs2 cs ∧
        is_decoded_nearest_neighbour 1 (n_repetition_code m) bs1 [c]))
Proof
  gvs[is_decoded_nearest_neighbour_cons]
QED

Theorem length_n_codes_0[simp]:
  ∀bs.
    bs ∈ length_n_codes 0 ⇔ bs = []
Proof
  rpt strip_tac
  >> EQ_TAC
  >> gvs[length_n_codes_def]
QED

Theorem is_decoded_nearest_neighbour_0[simp]:
  ∀bs cs code_fn.
    is_decoded_nearest_neighbour 0 code_fn bs cs ⇔ cs = []
Proof
  rpt strip_tac
  >> EQ_TAC
  >> gvs[is_decoded_nearest_neighbour_def, length_n_codes_def] 
QED

Theorem decode_nearest_neighbour_n_repetition_code_unique:
  ∀n m bs cs ds.
    ODD m ∧
    LENGTH bs = m * LENGTH cs ∧
    is_decoded_nearest_neighbour n (n_repetition_code m) bs cs ∧
    is_decoded_nearest_neighbour n (n_repetition_code m) bs ds ⇒
    cs = ds
Proof
  gen_tac
  >> Induct_on ‘n’ >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘cs’ >> Cases_on ‘ds’ >> gvs[]
  >- gvs[is_decoded_nearest_neighbour_def, length_n_codes_def]
  >- gvs[is_decoded_nearest_neighbour_def, length_n_codes_def]
  >> qspecl_then [‘n’, ‘m’, ‘TAKE m bs’, ‘DROP m bs’, ‘h’, ‘t’] assume_tac (iffLR is_decoded_nearest_neighbour_cons_n_repetition_code)
  >> gvs[TAKE_DROP]
  >> qspecl_then [‘n’, ‘m’, ‘TAKE m bs’, ‘DROP m bs’, ‘h'’, ‘t'’] assume_tac (iffLR is_decoded_nearest_neighbour_cons_n_repetition_code)
  >> gvs[TAKE_DROP]
  >> last_x_assum $ qspecl_then [‘m’, ‘DROP m bs’, ‘t’, ‘t'’] assume_tac
  >> gvs[]
  >> gvs[ADD1]
  >> qspecl_then [‘m’, ‘TAKE m bs’, ‘[h]’, ‘[h']’] assume_tac decode_nearest_neighbour_n_repetition_bit_unique
  >> gvs[]
  >> pop_assum irule
  >> gvs[length_n_codes_def]
QED

Theorem length_n_codes_sing_hd:
  ∀bs.
    bs ∈ length_n_codes 1 ⇔ bs = [HD bs]
Proof
  gvs[SING_HD, length_n_codes_def]
QED

Theorem bnot_cons[simp]:
  ∀b bs.
    bnot (b::bs) = (¬b)::(bnot bs)
Proof
  gvs[bnot_def]
QED

Theorem hamming_distance_bnot[simp]:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    hamming_distance (bnot bs) (bnot cs) = hamming_distance bs cs
Proof
  strip_tac
  >> Induct_on ‘bs’ >> Cases_on ‘cs’ >> gvs[]
  >> rpt strip_tac
  >> last_x_assum $ qspec_then ‘t’ assume_tac
  >> gvs[]
  >> gvs[hamming_distance_cons]
QED

Theorem bitwise_cons[simp]:
  ∀f b bs c cs.
    LENGTH bs = LENGTH cs ⇒
    bitwise f (b::bs) (c::cs) = (f b c)::(bitwise f bs cs)
Proof
  gvs[bitwise_def]
QED

Theorem bxor_cons[simp]:
  ∀b bs c cs.
    LENGTH bs = LENGTH cs ⇒
    bxor (b::bs) (c::cs) = (b ⇎ c)::(bxor bs cs)
Proof
  gvs[bxor_def]
QED

Theorem bxor_comm:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    bxor bs cs = bxor cs bs
Proof
  strip_tac
  >> Induct_on ‘bs’ >> Cases_on ‘cs’ >> gvs[]
  >> rpt strip_tac
  >- (Cases_on ‘h’ >> Cases_on ‘h'’ >> gvs[])
  >> last_x_assum $ qspec_then ‘t’ assume_tac
  >> gvs[]
QED

Theorem bnot_length[simp]:
  ∀bs.
    LENGTH (bnot bs) = LENGTH bs
Proof
  rpt strip_tac
  >> Induct_on ‘bs’ >> gvs[bnot_def]
QED

Theorem bnot_bxor_1:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    bnot (bxor bs cs) = bxor (bnot bs) cs
Proof
  strip_tac
  >> Induct_on ‘bs’
  >> gvs[bnot_def, bxor_def, bitwise_def]
  >> rpt strip_tac
  >> gvs[bnot_def]
  >> Cases_on ‘cs’ >> gvs[]
  >> Cases_on ‘h’ >> Cases_on ‘h'’ >> gvs[]
QED

Theorem bnot_bxor_2:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    bnot (bxor bs cs) = bxor bs (bnot cs)
Proof
  rpt strip_tac
  >> qspecl_then [‘bs’, ‘bnot cs’] assume_tac bxor_comm
  >> gvs[]
  >> DEP_PURE_ONCE_REWRITE_TAC[bxor_comm]
  >> gvs[bnot_bxor_1]
QED

Theorem apply_noise_bnot_1:
  ∀ns bs.
    LENGTH ns = LENGTH bs ⇒
    bnot (apply_noise ns bs) = apply_noise (bnot ns) bs
Proof
  gvs[apply_noise_def, bnot_bxor_1]
QED

Theorem apply_noise_bnot_2:
  ∀ns bs.
    LENGTH ns = LENGTH bs ⇒
    bnot (apply_noise ns bs) = apply_noise ns (bnot bs)
Proof
  gvs[apply_noise_def, bnot_bxor_2]
QED

Theorem bnot_n_repetition_bit[simp]:
  ∀n b.
    bnot (n_repetition_bit n b) = n_repetition_bit n (¬b)
Proof
  rpt strip_tac
  >> Induct_on ‘n’ >> gvs[bnot_def]
QED

Theorem num_errors_empty[simp]:
  num_errors [] = 0
Proof
  gvs[num_errors_def]
QED

Theorem num_errors_0[simp]:
  ∀ns l. ns ∈ length_n_codes l ⇒ (num_errors ns = 0 ⇔ ns = n_repetition_bit l F)
Proof
  Induct_on ‘l’ >> Cases_on ‘ns’ >> gvs[length_n_codes_def]
  >> rpt strip_tac
  >> first_x_assum $ qspec_then ‘t’ assume_tac
  >> gvs[]
  >> EQ_TAC >> rpt strip_tac >> gvs[num_errors_def]
  >> Cases_on ‘h’ >> gvs[]
QED

Theorem num_errors_eq_length:
  ∀bs. num_errors bs = LENGTH bs ⇔ bs = n_repetition_bit (LENGTH bs) T
Proof
  Induct_on ‘bs’ >> gvs[]
  >> rpt strip_tac
  >> gvs[ADD1]
  >> REVERSE $ Cases_on ‘h’ >> simp[num_errors_cons]
  >> qspec_then ‘bs’ assume_tac num_errors_length
  >> gvs[]
QED

Theorem bxor_empty[simp]:
  bxor [] [] = []
Proof
  EVAL_TAC
QED

Theorem apply_noise_n_repetition_bit_T:
  ∀bs.
    apply_noise (n_repetition_bit (LENGTH bs) T) bs = bnot bs
Proof
  Induct_on ‘bs’ >> gvs[bnot_def, apply_noise_def]
QED

Theorem bnot_empty[simp]:
  bnot [] = []
Proof
  EVAL_TAC
QED

Theorem bnot_append[simp]:
  ∀bs cs.
    bnot (bs ⧺ cs) = bnot bs ⧺ bnot cs
Proof
  Induct_on ‘bs’ >> gvs[]
QED

Theorem n_repetition_code_bnot[simp]:
  ∀bs n.
    n_repetition_code n (bnot bs) = bnot (n_repetition_code n bs)
Proof
  Induct_on ‘n’ >> gvs[]
  >> Induct_on ‘bs’ >> gvs[]
QED

Theorem NOT_IFF[simp]:
  ∀b. (¬b ⇔ b) ⇔ F
Proof
  Cases_on ‘b’ >> gvs[]
QED

Theorem hamming_distance_bnot_1[simp]:
  ∀bs.
    hamming_distance (bnot bs) bs = LENGTH bs
Proof
  Induct_on ‘bs’ >> gvs[]
QED

Theorem hamming_distance_bnot_2[simp]:
  ∀bs.
    hamming_distance bs (bnot bs) = LENGTH bs
Proof
  rpt strip_tac
  >> DEP_PURE_ONCE_REWRITE_TAC[hamming_distance_sym]
  >> gvs[]
QED

Theorem decode_nearest_neighbour_n_repetition_code_3:
  ∀bs ns.
    bs ∈ length_n_codes 1 ∧
    ns ∈ length_n_codes 3 ⇒ 
    (decode_nearest_neighbour 1 (n_repetition_code 3) (apply_noise ns (n_repetition_code 3 bs)) = bs ⇔ num_errors ns ≤ 1)
Proof
  rpt strip_tac
  >> REVERSE EQ_TAC >> disch_tac
  >- (gvs[decode_nearest_neighbour_def]
      >> SELECT_ELIM_TAC
      >> conj_tac
      >- gvs[exists_decode_nearest_neighbour_candidate]
      >> rpt strip_tac
      >> qsuff_tac ‘is_decoded_nearest_neighbour 1 (n_repetition_code 3) (apply_noise ns (n_repetition_code 3 bs)) bs’
      >- (rpt strip_tac
          >> qspecl_then [‘1’, ‘3’, ‘apply_noise ns (n_repetition_code 3 bs)’, ‘x’, ‘bs’] assume_tac decode_nearest_neighbour_n_repetition_code_unique
          >> pop_assum irule
          >> gvs[]
          >> gvs[apply_noise_length]
          >> gvs[length_n_codes_def]
          >> gvs[is_decoded_nearest_neighbour_def, length_n_codes_def])
      >> pop_assum kall_tac
      >> gvs[is_decoded_nearest_neighbour_def]
      >> rpt strip_tac
      >> Cases_on ‘bs’ >- gvs[length_n_codes_def]
      >> REVERSE $ Cases_on ‘t’ >- gvs[length_n_codes_def]
      >> Cases_on ‘ds’ >- gvs[length_n_codes_def]
      >> REVERSE $ Cases_on ‘t’ >- gvs[length_n_codes_def]
      >> Cases_on ‘h = h'’ >> gvs[]
      >> wlog_tac ‘h = T’ [‘h’, ‘h'’]
      >- (first_assum $ qspecl_then [‘h’, ‘h'’] assume_tac
          >> gvs[]
          >> DEP_PURE_ONCE_REWRITE_TAC[GSYM hamming_distance_bnot]
          >> rewrite_tac [n_repetition_bit_length, apply_noise_length, length_n_codes_def]
          >> DEP_PURE_ONCE_REWRITE_TAC [apply_noise_bnot_2]
          >> gvs[length_n_codes_def]
          >> qspecl_then [‘apply_noise ns (n_repetition_bit 3 F)’, ‘n_repetition_bit 3 T’] assume_tac (GSYM hamming_distance_bnot)
          >> gvs[apply_noise_length, (Excl "hamming_distance_bnot")]
          >> pop_assum kall_tac
          >> DEP_PURE_ONCE_REWRITE_TAC [apply_noise_bnot_2]
          >> gvs[])
      >> gvs[]
      >> rpt $ qpat_x_assum ‘_ ∈ length_n_codes 1’ kall_tac
      >> ‘n_repetition_bit 3 T = [T;T;T]’ by EVAL_TAC
      >> ‘n_repetition_bit 3 F = [F;F;F]’ by EVAL_TAC
      >> gvs[]
      >> sg ‘num_errors ns = 0 ∨ num_errors ns = 1’ >> gvs[]
      >- (drule num_errors_0 >> rpt strip_tac
          >> gvs[]
          >> EVAL_TAC)
      >> Cases_on ‘ns’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[length_n_codes_def]
      >> Cases_on ‘t'’ >> gvs[length_n_codes_def]
      >> Cases_on ‘t’ >> gvs[length_n_codes_def]
      >> Cases_on ‘h’ >> gvs[num_errors_def]
      >> Cases_on ‘h'’ >> gvs[num_errors_def]
      >> Cases_on ‘h''’ >> gvs[num_errors_def]
      >> EVAL_TAC)
  >> gvs[decode_nearest_neighbour_def]
  >> sg ‘is_decoded_nearest_neighbour 1 (n_repetition_code 3) (apply_noise ns (n_repetition_code 3 bs)) bs’
  >- (pop_assum (fn th => assume_tac (GSYM th))
      >> qmatch_goalsub_abbrev_tac ‘P bs’
      >> ‘P @cs. P cs’ by (SELECT_ELIM_TAC >> gvs[Abbr ‘P’, exists_decode_nearest_neighbour_candidate])
      >> gvs[])
  >> qpat_x_assum ‘_ = _’ kall_tac
  >> qspec_then ‘ns’ assume_tac num_errors_length
  >> gvs[length_n_codes_def]
  >> ‘num_errors ns = 3 ∨ num_errors ns ≤ 2’ by gvs[]
  >- (gvs[]
      >> qspec_then ‘ns’ assume_tac num_errors_eq_length
      >> gvs[]
      >> pop_assum kall_tac
      >> gvs[]
      >> qspec_then ‘n_repetition_code 3 bs’ assume_tac apply_noise_n_repetition_bit_T
      >> gvs[]
      >> pop_assum kall_tac
      >> gvs[is_decoded_nearest_neighbour_def]
      >> pop_assum $ qspec_then ‘bnot bs’ assume_tac
      >> gvs[length_n_codes_def])
  >> gvs[n_repetition_code_bnot]
  >> Cases_on ‘num_errors ns = 2’ >> gvs[]
  >> Cases_on ‘ns’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[]
  >> Cases_on ‘t'’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[]
  >> gvs[is_decoded_nearest_neighbour_def]
  >> Cases_on ‘bs’ >> gvs[]
  >> first_x_assum $ qspec_then ‘[¬h''']’ assume_tac
  >> gvs[length_n_codes_def]
  >> ‘n_repetition_bit 3 T = [T; T; T]’ by EVAL_TAC
  >> ‘n_repetition_bit 3 F = [F; F; F]’ by EVAL_TAC
  >> Cases_on ‘h’ >> Cases_on ‘h'’ >> Cases_on ‘h''’ >> gvs[num_errors_def]
  >> Cases_on ‘h'''’ >> gvs[]
  >> gvs[apply_noise_def]
QED

Theorem decode_nearest_neighbour_is_decoded_nearest_neighbour:
  ∀n code_fn bs.
    is_decoded_nearest_neighbour n code_fn bs (decode_nearest_neighbour n code_fn bs)
Proof
  rpt strip_tac
  >> gvs[decode_nearest_neighbour_def]
  >> SELECT_ELIM_TAC
  >> gvs[exists_decode_nearest_neighbour_candidate]
QED

Theorem code_decodes_correctly_is_decoded_nearest_neighbour:
  ∀n bs ns code_fn.
    code_decodes_correctly n bs ns code_fn ⇒ is_decoded_nearest_neighbour n code_fn (apply_noise ns (code_fn bs)) bs
Proof
  rpt strip_tac
  >> gvs[code_decodes_correctly_def]
  >> qspecl_then [‘n’, ‘code_fn’, ‘apply_noise ns (code_fn bs)’] assume_tac decode_nearest_neighbour_is_decoded_nearest_neighbour
  >> gvs[]
QED

Theorem code_decodes_correctly_n_repetition_code_3:
  ∀bs ns.
    bs ∈ length_n_codes 1 ∧
    ns ∈ length_n_codes 3 ⇒
    (code_decodes_correctly 1 bs ns (n_repetition_code 3) ⇔ num_errors ns ≤ 1)
Proof
  rpt strip_tac
  >> gvs[code_decodes_correctly_def]
  >> gvs[decode_nearest_neighbour_n_repetition_code_3]
QED

fun SUBGOAL_LIST_THEN tms thm_tac final_tac
= case tms of
    [] => final_tac
  | t::ts => SUBGOAL_THEN t (fn th => (thm_tac th >> SUBGOAL_LIST_THEN ts thm_tac final_tac))

fun UNDISCH_ALL_RETURN_TERMS_HELPER (tms : term list) (th : thm) =
let
val (cur_tm, cur_th) = UNDISCH_TM th;
val (rec_tms : term list, rec_th : thm) = UNDISCH_ALL_RETURN_TERMS_HELPER (cur_tm::tms) cur_th;
in
  (rec_tms, rec_th)
  end handle HOL_ERR _ => (tms, th);

fun UNDISCH_ALL_RETURN_TERMS th = UNDISCH_ALL_RETURN_TERMS_HELPER [] th

fun DEP_ASSUME_TAC th
= let
(*val specialised_thm = SPEC_ALL th;*)
val (undischarged_terms, undischarged_thm) = UNDISCH_ALL_RETURN_TERMS th
                                                                      (*val undischarged_thm = UNDISCH_ALL $ SPEC_ALL th;*)
                                                                      (*val uthm_hyps = hyp undischarged_thm;*)
  in
    SUBGOAL_LIST_THEN undischarged_terms assume_tac (assume_tac undischarged_thm)
                      end;

Theorem negation_not_posinf[simp]:
  ∀e. -e ≠ +∞ ⇔ e ≠ −∞
Proof
  rpt strip_tac
  >> EQ_TAC
  >> rpt strip_tac >> gvs[extreal_ainv_def]
  >> Cases_on ‘e’ >> gvs[extreal_ainv_def]
QED

Theorem negation_not_neginf[simp]:
  ∀e. -e ≠ −∞ ⇔ e ≠ +∞
Proof
  rpt strip_tac
  >> EQ_TAC
  >> rpt strip_tac >> gvs[extreal_ainv_def]
  >> Cases_on ‘e’ >> gvs[extreal_ainv_def]
QED

fun dtc' (t : term) =
let val {Thy, Name, ...} = dest_thy_const t in
  SOME (Thy, Name)
       end handle HOL_ERR _ => NONE


                               
(*
fun create_real_expression combinator term_list
                                = case term_list of
                                    t::ts =>
                                  | [] => 
                                      mk_comb combinator

val input_term =  “Normal 3 = Normal 4”
val input_term = “Normal 3 - Normal 4”
val input_term = “(Normal 1 * Normal 2) + (Normal 3 / Normal 4) + (- Normal 5) - Normal 6 = Normal 7”
val input_term = “(Normal 1 * Normal 2) + (Normal 3 / Normal 4) + (- Normal 5) - Normal 6”

        
                 mk_comb (mk_comb (“$+ : real -> real -> real”, “3 : real”), “4 : real”)

                 dest_comb “- 3 : real”
                 mk_comb (“numeric_negate : real -> real”, “3 : real”)

val input_term = “∀r : real. ”
*)

(*fun extreal_to_real input_term =
                                let
val (combinator, term_list) = strip_comb input_term
val SOME (combinator_theory, combinator_name) = dtc' combinator
val translated_term = case combinator_name of
                        "extreal_add" => mk_comb (mk_comb (“$+ : real -> real -> real”, extreal_to_real (el 1 term_list)), extreal_to_real (el 2 term_list))
                      | "extreal_div" => mk_comb (mk_comb (“$/ : real -> real -> real”, extreal_to_real (el 1 term_list)), extreal_to_real (el 2 term_list))
                      | "extreal_mul" => mk_comb (mk_comb (“$* : real -> real -> real”, extreal_to_real (el 1 term_list)), extreal_to_real (el 2 term_list))
                      | "extreal_ainv" => mk_comb (“numeric_negate : real -> real”, extreal_to_real (el 1 term_list))
                      | "extreal_sub" => mk_comb (mk_comb (“$- : real -> real -> real”, extreal_to_real (el 1 term_list)), extreal_to_real (el 2 term_list))
                      | "=" => mk_comb (mk_comb (“$= : real -> real -> bool”, extreal_to_real (el 1 term_list)), extreal_to_real (el 2 term_list))
                      (*| "!" => mk_comb (“!”, extreal_to_real (hd term_list))*)
                      (*| "?" => mk_comb (“?”, extreal_to_real (hd term_list))*)
                      | "Normal" => hd term_list
                      | _ => input_term
                                in
                                  translated_term
                                  end

fun extreal_to_real_equivalence_term input_term =
let
val translated_term = extreal_to_real input_term
in
  mk_comb (mk_comb (“$= : extreal -> extreal -> bool”, input_term), mk_comb (“Normal”, translated_term))
          end

fun prove_extreal_to_real input_term =
let 
val
in
  end
                                *)

(*
(* Given an expression of arithmetic operations where each term is of the form
   Normal r for some r, prove that this is equivalent to Normal applied to
   the same expression of arithmetic operations in the reals. *)
fun Normal_CONV input_term =
let
  
val (combinator, term_list) = strip_comb input_term
val SOME (combinator_theory, combinator_name) = dtc' combinator
val translated_term = case combinator_name of
                        "extreal_add" => DECIDE mk_comb (“$=”, )  t_term
                      | "extreal_div" => DECIDE “T”
                      | "extreal_mul" => DECIDE “T”
                      | "extreal_ainv" => DECIDE “T”
                      | "extreal_sub" => DECIDE “T”
                      | ""

                        strip_comb “Normal 2”
                        
in
  
  (*case combinator_name of
     "!" => DECIDE “T”
  | "?" => DECIDE “T”
  | _ => DECIDE “T”*)
                
  end
                               *)

(*
val Normal_CONV_test1 = “∀n : num. ∀r : real. ∃s : real. Normal s + ((- Normal r) pow n) * Normal 2 = Normal 0”
val Normal_CONV_test2 = “Normal 2 / Normal 3”
val Normal_CONV_test3 = “Normal 2 + Normal 3”
val Normal_CONV_test4 = “Normal 2 * Normal 3”
val Normal_CONV_test5 = “-Normal 1”
val Normal_CONV_test6 = “Normal 2 - Normal 3”
val Normal_CONV_test7 = “∀n : num. Normal 2 pow n = 4”
val Normal_CONV_test8 = “∀r : real. Normal r = 4”
val Normal_CONV_test9 = “∃r : real. Normal r = 4”

val input_term = “Normal 2 = Normal 3”

                        
                 dest_comb Normal_CONV_test3
          dest_comb Normal_CONV_test2
          dest_comb Normal_CONV_test1
           snd (dest_comb Normal_CONV_test1)
*)

(* TODO: make this into a reusable simpset *)
val extreal_to_real_simpset_thing = [extreal_add_eq, extreal_mul_eq, cj 3 extreal_ainv_def, cj 1 extreal_pow_def]


Theorem REAL_ADD_RIGHT:
  ∀r1 r2 : real.
    r1 * r2 + r2 = (r1 + 1) * r2
Proof
  rpt strip_tac
  >> gvs[REAL_ADD_RDISTRIB]
QED

Theorem REAL_ADD_NEG_RIGHT:
  ∀r1 r2 : real.
    r1 * r2 + -r2 = (r1 - 1) * r2
Proof
  rpt strip_tac
  >> gvs[REAL_ADD_RDISTRIB, real_sub]
  >> gvs[GSYM REAL_NEG_MINUS1]
QED

(*((1 - p) pow 2) * (2 * p + 1)*)
Theorem q2_sym_prob_correctly_decoded_prob:
  ∀p.
    0 ≤ p ∧ p ≤ 1 ⇒ q2_sym_prob_correctly_decoded (p : extreal) = 2 * p pow 3 - 3 * p pow 2 + 1
Proof
  gen_tac
  >> disch_tac
  >> simp[q2_sym_prob_correctly_decoded_def, q2_sym_prob_space_def]
  >> qmatch_goalsub_abbrev_tac ‘measure _ s = _’
  >> sg ‘s = {([T], [F;F;F]); ([F], [F;F;F]); ([T], [T;F;F]); ([F], [T;F;F]); ([T], [F;T;F]); ([F], [F;T;F]); ([T], [F;F;T]); ([F], [F;F;T]);}’
  >- (unabbrev_all_tac
      >> irule $ iffRL EXTENSION
      >> rpt strip_tac
      >> REVERSE EQ_TAC
      >- (rpt strip_tac
          >> Cases_on ‘x’
          >> gvs[IN_DEF]
          >> DEP_PURE_ONCE_REWRITE_TAC [code_decodes_correctly_n_repetition_code_3]
          >> EVAL_TAC
          >> gvs[IN_DEF])
      >> rpt strip_tac
      >> gvs[IN_DEF]
      >> gvs[length_n_codes_def]
      >> Cases_on ‘bs’ >> gvs[]
      >> Cases_on ‘ns’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[]
      >> Cases_on ‘t'’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[]
      >> qspecl_then [‘[h]’, ‘[h';h'';h''']’] assume_tac code_decodes_correctly_n_repetition_code_3
      >> gvs[length_n_codes_def]
      >> pop_assum kall_tac
      >> gvs[num_errors_def]
      >> Cases_on ‘h’ >> Cases_on ‘h'’ >> Cases_on ‘h''’ >> Cases_on ‘h'''’ >> gvs[])
  >> gvs[]
  >> pop_assum kall_tac
  >> qmatch_goalsub_abbrev_tac ‘measure _ s = _’
  >> sg ‘s = {[T]; [F]} × {[F; F; F]; [T; F; F]; [F; T; F]; [F; F; T]}’
  >- (unabbrev_all_tac
      >> EVAL_TAC)
  >> gvs[]
  >> pop_assum kall_tac
  >> qmatch_goalsub_abbrev_tac ‘measure (m0 × m1) (s0 × s1) = _’
  >> qmatch_goalsub_abbrev_tac ‘_ = RHS’
  >> qsuff_tac ‘measure m0 s0 = 1 ∧ measure m1 s1 = RHS’
  >- (rpt strip_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[prod_measure_cross]
      >> gvs[]
      >> unabbrev_all_tac
      >> conj_tac
      >- metis_tac[prob_space_def, length_n_codes_uniform_prob_space_is_prob_space]
      >> conj_tac
      >- metis_tac[prob_space_def, sym_noise_prob_space_is_prob_space]
      >> conj_tac
      >> gvs[measurable_sets_def, length_n_codes_uniform_prob_space_def, POW_DEF, length_n_codes_def, sym_noise_prob_space_def])
  >> conj_tac
  >- (unabbrev_all_tac
      >> EVAL_TAC
      >> sg ‘{c | LENGTH c = 1} = {[T]; [F;]}’
      >- (irule $ iffRL EXTENSION
          >> rpt strip_tac
          >> Cases_on ‘x’ >> gvs[]
          >> Cases_on ‘h’ >> gvs[])
      >> gvs[]
      >> qspec_then ‘Normal 2’ assume_tac div_refl
      >> gvs[])
  >> unabbrev_all_tac
  >> gvs[sym_noise_prob_space_def, sym_noise_dist_def, sym_noise_mass_func_def]
  >> qmatch_goalsub_abbrev_tac ‘∑ f (x1 INSERT x2 INSERT x3 INSERT x4 INSERT s)’
  >> sg ‘∀x. f x ≠ +∞’
  >- (gen_tac
      >> unabbrev_all_tac
      >> gvs[]
      >> irule (cj 2 mul_not_infty2)
      >> sg ‘p ≠ −∞ ∧ p ≠ +∞’
      >- (gvs[pos_not_neginf]
          >> irule le_not_posinf
          >> qexists ‘1’
          >> gvs[])
      >> NTAC 2 (last_x_assum kall_tac)
      >> ‘1 - p ≠ −∞ ∧ 1 - p ≠ +∞’ by gvs[sub_not_infty]
      >> gvs[pow_not_infty])
  >> ‘FINITE s’ by (unabbrev_all_tac >> EVAL_TAC)
  >> NTAC 4 (DEP_PURE_ONCE_REWRITE_TAC [EXTREAL_SUM_IMAGE_INSERT]
             >> gvs[]
             >> DEP_PURE_ONCE_REWRITE_TAC[iffLR DELETE_NON_ELEMENT]
             >> conj_tac >- (unabbrev_all_tac >> gvs[]))
  >> unabbrev_all_tac
  >> gvs[]
  >> EVAL_TAC
  >> gvs[pow_0]
  >> pop_assum kall_tac
  >> qmatch_goalsub_abbrev_tac ‘LHS = RHS’
  >> Cases_on ‘p’ >> gvs[]
  >> gvs[extreal_add_eq, extreal_mul_eq, cj 3 extreal_ainv_def, cj 1 extreal_pow_def]
  >> Cases_on ‘LHS’ >> gvs[]
  >- (unabbrev_all_tac >> gvs[]
      (*>> PURE_REWRITE_TAC[GSYM (EVAL “SUC 2”)]
                              >> PURE_REWRITE_TAC[GSYM (EVAL “SUC 1”)]
                              >> PURE_REWRITE_TAC[GSYM (EVAL “SUC 0”)]
                              >> PURE_REWRITE_TAC[real_pow]
                              >> gvs[]
                              >> gvs[REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB]
                              >> gvs[REAL_NEG_MUL2]
                  >> gvs[REAL_ADD_ASSOC]
      >> gvs[REAL_MUL_RNEG, GSYM REAL_MUL_LNEG]
      >> gvs[REAL_MUL_ASSOC]
      >> gvs[REAL_MUL_RNEG, GSYM REAL_MUL_LNEG]
      >> gvs[AC REAL_ADD_COMM REAL_ADD_ASSOC]
      >> gvs[GSYM REAL_NEG_LMUL]
      >> gvs[REAL_DOUBLE]
      >> gvs[REAL_ADD_ASSOC]
      >> gvs[REAL_DOUBLE]
      >> gvs[REAL_ADD_RIGHT, REAL_ADD_NEG_RIGHT]
      >> gvs[real_sub]*)
  >> REAL_ARITH_TAC)
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

