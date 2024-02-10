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

Definition length_n_codes_prob_space_def:
  length_n_codes_prob_space (n : num) =
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
  
(* ------------------------------------------------------- *)
(* Potentially useful here:                                *)
(* prob_on_finite_set                                      *)
(* uniform_distribution_prob_space                         *)
(* ------------------------------------------------------- *)
Theorem length_n_codes_prob_space_is_prob_space:
  ∀n : num.
  prob_space (length_n_codes_prob_space n)
Proof
  rpt strip_tac
  >> gvs[length_n_codes_prob_space_def]
  >> irule uniform_distribution_finite_prob_space
  >> 
QED


(* -------------------------------------------------------------------------- *)
(* Takes an input probability distribution and returns the output probability *)
(* distribution with errors randomly added                                    *)
(* -------------------------------------------------------------------------- *)
Definition symmetric_error_channel_def:
  symmetric_error_channel p

End



val _ = export_theory();

