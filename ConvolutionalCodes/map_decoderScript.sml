(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

(* My theories *)
open ecc_prob_spaceTheory;
open argmin_extrealTheory;

(* My libraries *)
open donotexpandLib;

(* Standard theories *)
open arithmeticTheory;
open bitstringTheory;
open pred_setTheory;
open probabilityTheory;
open extrealTheory;
open realTheory;
open rich_listTheory;
open sigma_algebraTheory;
open martingaleTheory;
open measureTheory;
open topologyTheory;

(* Standard libraries *)
open realLib;
open dep_rewrite;
open ConseqConv;

val _ = new_theory "map_decoder";

val _ = hide "S";

(* -------------------------------------------------------------------------- *)
(* The bitwise MAP decoder chooses each returned bit such that it has maximal *)
(* probability given the received message.                                    *)
(*                                                                            *)
(* This probability is taken with respect to a prior probability distribution *)
(* on the originally sent data and a probability distribution on the noise    *)
(* which is added to the message.                                             *)
(*                                                                            *)
(* Since P(x_i), and since the denominator is the same positive value         *)
(* regardless                                                                 *)
(*                                                                            *)
(* This implementation breaks ties by assuming a bit has the value T in the   *)
(* case of a tie.                                                             *)
(*                                                                            *)
(* enc: the encoding function                                                 *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* p: the probability of bit error in our binary symmetric channel            *)
(* ds: the string that we wish to decode                                      *)
(* -------------------------------------------------------------------------- *)
Definition map_decoder_bitwise_def:
  map_decoder_bitwise enc n m p ds =
  let
    map_decoder_bit_prob =
    λi x. cond_prob (ecc_bsc_prob_space n m p)
                    (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ EL i bs = x)
                    (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧
                                bxor (enc bs) ns = ds);
  in
    MAP (λi. map_decoder_bit_prob i F ≤ map_decoder_bit_prob i T)
        (COUNT_LIST n)
End

(* -------------------------------------------------------------------------- *)
(* Similar to ldiv_le_imp                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem ldiv_le_iff:
  ∀x y z.
    0 < z ∧ z ≠ +∞ ⇒
    (x / z ≤ y / z : extreal ⇔ x ≤ y)
Proof
  rw[]
  >> REVERSE EQ_TAC >- metis_tac[ldiv_le_imp]
  >> Cases_on ‘x’ >> Cases_on ‘y’ >> Cases_on ‘z’
  >> gvs[infty_div, le_infty, extreal_div_eq, REAL_POS_NZ]
QED

(* -------------------------------------------------------------------------- *)
(* Finding the bits that maximize the probability of receiving that bit,      *)
(* given that we received a particular message, is equivalent to finding the  *)
(* bits that maximize the probability that we both received that bit and      *)
(* received that message.                                                     *)
(*                                                                            *)
(* We require that our binary symmetric channel flips bits with a valid       *)
(* probability (between 0 and 1), that the length of the received message     *)
(* is the same as was expected, and that the encoder takes messages of the    *)
(* expected length to messages of the expected length.                        *)
(*                                                                            *)
(* We ignore the special case in which p = 0 or p = 1. This is not a          *)
(* particularly interesting case, because we have no noise in this case.      *)
(* However, it is annoying for proof. In this case, it may not be possible    *)
(* to receive the received message, because if the encoder does not allow us  *)
(* to produce it directly, a noise probability of 0 will mean that we cannot  *)
(* possibly recieve that message. This means that the probability we are      *)
(* conditioning on becomes zero, meaning that the denominator becomes zero,   *)
(* meaning that our conditional probability becomes undefined.                *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_joint:
  ∀enc n m p ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      map_decoder_bit_prob_joint =
      λi x.
        prob (ecc_bsc_prob_space n m p)
             ((λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ EL i bs = x)
              ∩ (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧
                            bxor (enc bs) ns = ds));
    in
      MAP (λi. map_decoder_bit_prob_joint i F ≤ map_decoder_bit_prob_joint i T)
          (COUNT_LIST n)
Proof
  rpt strip_tac
  >> qpat_x_assum ‘LENGTH ds = m’ assume_tac
  >> donotexpand_tac
  >> rw[]
  (* 0 ≤ p and p ≤ 1 is a more common representation for a probability than
     0 < p and p < 1. *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* It's helpful to know that we have a prob space *)
  >> qspecl_then [‘n’, ‘m’, ‘p’] assume_tac ecc_bsc_prob_space_is_prob_space
  >> gvs[]
  (* The inner lambda function is equivalent, so focus on that *)
  >> gvs[map_decoder_bitwise_def]
  >> AP_THM_TAC
  >> AP_TERM_TAC
  >> gvs[FUN_EQ_THM]
  >> gen_tac
  (* Decompose conditional probability into its component probabilities *)
  >> gvs[cond_prob_def]
  >> qmatch_goalsub_abbrev_tac ‘_ ⇔ prob1 ≤ prob2’
  (* We expect to be able to cancel out this bottom term, we just need to
     ensure that it is strictly positive and not infinity *)
  >> DEP_PURE_ONCE_REWRITE_TAC[ldiv_le_iff]
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac ‘0 < prob _ e’
  (* We are taking the probability with respect to a valid event: all events
     are valid in this probabiltiy space. *)
  >> sg ‘e ∈ events (ecc_bsc_prob_space n m p)’
  >- (gvs[events_ecc_bsc_prob_space]
      >> unabbrev_all_tac
      >> gvs[IN_DEF, SUBSET_DEF]
      >> rw[] >> Cases_on ‘x’ >> gvs[]
     )
  (* A probability is never infinity. *)
  >> gvs[PROB_FINITE]
  (* A probability is always nonnegative, so we can simplify to having to prove
     that our probability is nonzero *)
  >> REVERSE $ Cases_on ‘prob (ecc_bsc_prob_space n m p) e = 0’
  >- gvs[lt_le, PROB_POSITIVE]
  >> gvs[]
  (* Use lemma: in our probability space, a probability is zero if and only if
     the event is the empty set. *)        
  >> gvs[prob_ecc_bsc_prob_space_zero]
  (* Simplify to needing to show that there is an element in the event. *)
  >> gvs[events_ecc_bsc_prob_space]
  >> gvs[EXTENSION]
  >> qpat_x_assum ‘∀x. _’ mp_tac
  >> gvs[]
  (* There does exist such an element: simply send some initial message, and
     then choose the noise in such a way that it perfectly ends up giving us
     ds. *)
  >> qexists ‘(REPLICATE n F, bxor (enc (REPLICATE n F)) ds)’
  >> gvs[bxor_length]
  >> doexpand_tac >> gvs[]
  >> gvs[bxor_inv]
QED

(* -------------------------------------------------------------------------- *)
(* A version of map_decoder bitwise with Bayes' rule applied, so that we have *)
(* reversed the events and multiplied by the probability of the new           *)
(* denominator, cancelling out the common denominator.                        *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_bayes:
  ∀enc n m p ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      sp = ecc_bsc_prob_space n m p;
      e1 = λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ bxor (enc bs) ns = ds;
      e2 = λi x. (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ EL i bs = x);
      map_decoder_bit_prob_bayes = λi x. cond_prob sp e1 (e2 i x) *
                                         prob sp (e2 i x);
    in
      MAP
      (λi. map_decoder_bit_prob_bayes i F ≤ map_decoder_bit_prob_bayes i T)
      (COUNT_LIST n)
Proof
  (* Look at the internals *)
  rpt strip_tac
  >> gvs[map_decoder_bitwise_def]
  (* More common representation of probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* We have a prob space *)
  >> qspecl_then [‘n’, ‘(LENGTH ds)’, ‘p’] assume_tac
                 ecc_bsc_prob_space_is_prob_space
  >> gvs[]
  (* The inner bit is the bit we need to prove equivalence of. We only need
     to prove equivalence for valid i, that is, i < n *)
  >> qmatch_goalsub_abbrev_tac ‘MAP f1 (COUNT_LIST n) = MAP f2 (COUNT_LIST n)’
  >> gvs[MAP_EQ_f]
  >> rw[Abbr ‘f1’, Abbr ‘f2’]
  >> gvs[MEM_COUNT_LIST]
  (* Rename the events and prob space to something more manageable *)
  >> qmatch_goalsub_abbrev_tac ‘cond_prob sp e1 e3 ≤ cond_prob sp e2 e3’
  (* Each of the events is a valid event *)
  >> sg ‘e1 ∈ events sp ∧
         e2 ∈ events sp ∧
         e3 ∈ events sp’
  >- (rw[]
      >> (unabbrev_all_tac >> gvs[events_ecc_bsc_prob_space, POW_DEF]
          >> gvs[SUBSET_DEF] >> rw[] >> Cases_on ‘x’ >> ASM_SET_TAC[]
         )
     )
  (* Each of the events has nonzero probability *)
  >> sg ‘prob sp e1 ≠ 0 ∧
         prob sp e2 ≠ 0 ∧
         prob sp e3 ≠ 0’
  >- (rw[] >> (unabbrev_all_tac >> gvs[prob_ecc_bsc_prob_space_zero]
               >> gvs[FUN_EQ_THM] >> rw[])
      >- (qexists ‘(REPLICATE n F, REPLICATE (LENGTH ds) F)’
          >> gvs[EL_REPLICATE])
      >- (qexists ‘(REPLICATE n T, REPLICATE (LENGTH ds) F)’
          >> gvs[EL_REPLICATE])
      >- (qexists ‘(REPLICATE n F, bxor (enc (REPLICATE n F)) ds)’
          >> gvs[bxor_length, bxor_inv]
         )
     )
  (* Apply Bayes' rule*)
  >> sg ‘cond_prob sp e1 e3
         = cond_prob sp e3 e1 *
           prob sp e1 /
                prob sp e3’
  >- metis_tac[BAYES_RULE]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> sg ‘cond_prob sp e2 e3
         = cond_prob sp e3 e2 *
           prob sp e2 /
                prob sp e3’
  >- metis_tac[BAYES_RULE]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  (* Cancel out the divisions *)
  >> DEP_PURE_ONCE_REWRITE_TAC[ldiv_le_iff]
  >> conj_tac >- (gvs[PROB_FINITE] >> metis_tac[PROB_POSITIVE, le_lt])
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* The summation of the probabilities of finitely many disjoint events is the *)
(* probability of the union of these events.                                  *)
(* -------------------------------------------------------------------------- *)
Theorem prob_additive_finite:
  ∀p A x S.
    prob_space p ∧
    FINITE S ∧
    (∀x y. x ∈ S ∧ y ∈ S ∧ x ≠ y ⇒ DISJOINT (A x) (A y)) ∧
    (∀x. x ∈ S ⇒ A x ∈ events p) ⇒
    prob p (BIGUNION (IMAGE A S)) = ∑ (λx. prob p (A x)) S
Proof
  rw[]
  (* This can be proved using induction based on ADDITIVE_PROB, which works
     for two sets. There is also a version which works for a countable number
     of sets, but it has a significantly different form. *)
  >> Induct_on ‘S’ >> gvs[PROB_EMPTY]
  >> rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[iffLR ADDITIVE_PROB]
  >> rw[]
  (* Prove that the prob space is additive *)
  >- gvs[PROB_SPACE_ADDITIVE]
  (* Prove that the smaller BIGUNION (with one fewer set) is a valid event *)
  >- (irule EVENTS_COUNTABLE_UNION
      >> rw[]
      >- (irule finite_countable
          >> gvs[])
      >> gvs[SUBSET_DEF]
      >> rw[]
      >> metis_tac[]
     )
  (* Prove that the newly added A e is disjoint from any other A x *)
  >- (last_assum irule
      >> gvs[]
      >> metis_tac[]
     )
  (* Prove that the union of the newly added A e with the smaller BIGUNION
     is a valid event *)
  >- (irule EVENTS_UNION
      >> gvs[]
      >> irule EVENTS_COUNTABLE_UNION
      >> gvs[finite_countable]
      >> gvs[SUBSET_DEF] >> rw[] >> metis_tac[]
     )
  (* Prove that adding an element to a sum is equivalent to having a larger
     sum *)
  >> gvs[]
  >> DEP_PURE_ONCE_REWRITE_TAC[cj 3 EXTREAL_SUM_IMAGE_THM]
  >> gvs[DELETE_NON_ELEMENT_RWT]
  (* We need the probabilities we are adding to be finite *)
  >> disj1_tac >> rw[]
  >> (irule (cj 2 PROB_FINITE) >> gvs[])
QED

Theorem real_reverse_trichotomy:
  ∀r : real.
    r ≤ 0 ∧
    r ≠ 0 ∧
    0 ≤ r ⇒ F
Proof
  gen_tac >> strip_tac
  >> metis_tac[REAL_LT_LE, real_lte]
QED

Theorem div_not_infty_if_not_infty:
  ∀x r.
    (x ≠ +∞ ∧ 0 < r ⇒ x / Normal r ≠ +∞) ∧
    (x ≠ −∞ ∧ 0 < r ⇒ x / Normal r ≠ −∞) ∧
    (x ≠ +∞ ∧ r < 0 ⇒ x / Normal r ≠ −∞) ∧
    (x ≠ −∞ ∧ r < 0 ⇒ x / Normal r ≠ +∞)
Proof
  rw[]
  >> (gvs[REAL_LT_LE]
      >> Cases_on ‘x’
      >> gvs[extreal_div_def, GSYM normal_inv_eq, extreal_mul_def]
      >> rw[]
      >> gvs[REAL_LT_LE, real_reverse_trichotomy]
     )
QED

Theorem EXTREAL_SUM_IMAGE_DIV_RDISTRIB:
  ∀P y S.
    FINITE S ∧
    y ≠ 0 ∧
    y ≠ +∞ ∧
    y ≠ −∞ ∧
    ((∀x. x ∈ S ⇒ P x ≠ +∞) ∨ (∀x. x ∈ S ⇒ P x ≠ −∞)) ⇒
    ∑ (λx. P x / y) S = (∑ (λx. P x) S) / y : extreal
Proof
  rw[]
  (* We have two cases depending on which side of the disjunction in the
     assumptions we are in, but they generally have the same working. *)
    >> (Cases_on ‘y’ >> gvs[]
        >> Induct_on ‘S’ >> rw[zero_div]
        >> gvs[]
        >> DEP_PURE_REWRITE_TAC[cj 3 EXTREAL_SUM_IMAGE_THM]
        >> rw[]
        >- (Cases_on ‘0 ≤ r’
            >> metis_tac[REAL_LT_LE, div_not_infty_if_not_infty, REAL_NOT_LE]
           )
        >- metis_tac[]
        >> gvs[DELETE_NON_ELEMENT_RWT]
        >> DEP_PURE_ONCE_REWRITE_TAC[div_add2]
        >> REVERSE conj_tac >- gvs[]
        >> REVERSE conj_tac >- gvs[]
        >> gvs[EXTREAL_SUM_IMAGE_NOT_POSINF, EXTREAL_SUM_IMAGE_NOT_NEGINF]
       )
QED

Theorem extreal_div_cancel:
  ∀x y z.
    z ≠ 0 ∧
    z ≠ +∞ ∧
    z ≠ −∞ ⇒
    ((x / z = y / z) ⇔ x = y)
Proof
  rw[]
  >> Cases_on ‘x’ >> Cases_on ‘y’ >> Cases_on ‘z’
  >> (gvs[extreal_div_def,extreal_mul_def, GSYM normal_inv_eq]
      >> rw[])
QED

(* -------------------------------------------------------------------------- *)
(* Conditional probabilities are finite additive (and countably additive, but *)
(* this is not shown here.)                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem cond_prob_additive_finite:
  ∀p A x S B.
    prob_space p ∧
    FINITE S ∧
    (∀x y. x ∈ S ∧ y ∈ S ∧ x ≠ y ⇒ DISJOINT (A x) (A y)) ∧
    (∀x. x ∈ S ⇒ A x ∈ events p) ∧
    B ∈ events p ∧
    prob p B ≠ 0 ⇒
    cond_prob p (BIGUNION (IMAGE A S)) B = ∑ (λx. cond_prob p (A x) B) S
Proof
  rw[]
  >> gvs[cond_prob_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_DIV_RDISTRIB]
  >> gvs[PROB_FINITE, EVENTS_INTER]
  >> DEP_PURE_ONCE_REWRITE_TAC[extreal_div_cancel]
  >> gvs[PROB_FINITE]
  >> gvs[INTER_BIGUNION]
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM prob_additive_finite]
  >> rw[]
  >- gvs[DISJOINT_RESTRICT_L]
  >- gvs[EVENTS_INTER]
  >> gvs[INTER_BIGUNION]
  >> NTAC 2 AP_TERM_TAC
  >> ASM_SET_TAC[]
QED

(* -------------------------------------------------------------------------- *)
(* A version of the MAP decoder which is represented as the sum over all      *)
(* possible choices of input such that the ith element takes the appropriate  *)
(* value.                                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_sum:
  ∀enc n m p ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      map_decoder_bitstring_prob =
      λxs. cond_prob (ecc_bsc_prob_space n m p)
                     (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ bs = xs)
                     (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧
                                 bxor (enc bs) ns = ds);
      map_decoder_bit_prob =
      λi x. ∑ map_decoder_bitstring_prob {bs | EL i bs = x};
    in
      (MAP (λi. map_decoder_bit_prob i F ≤ map_decoder_bit_prob i T)
           (COUNT_LIST n))
Proof
  (* Look at the internals *)
  rpt strip_tac
  >> gvs[map_decoder_bitwise_def]
  (* More common representation of probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* We have a prob space *)
  >> qspecl_then [‘n’, ‘(LENGTH ds)’, ‘p’] assume_tac
                 ecc_bsc_prob_space_is_prob_space
  >> gvs[]
  (* The inner bit is the bit we need to prove equivalence of. We only need
     to prove equivalence for valid i, that is, i < n *)
  >> qmatch_goalsub_abbrev_tac ‘MAP f1 (COUNT_LIST n) = MAP f2 (COUNT_LIST n)’
  >> gvs[MAP_EQ_f]
  >> rw[Abbr ‘f1’, Abbr ‘f2’]
  >> gvs[MEM_COUNT_LIST]
  (* Rename the events and prob space to something more manageable *)
  >> qmatch_goalsub_abbrev_tac ‘cond_prob sp e1 e3 ≤ cond_prob sp e2 e3’
  (* Each of the events is a valid event *)
  >> sg ‘e1 ∈ events sp ∧
         e2 ∈ events sp ∧
         e3 ∈ events sp’
  >- (rw[]
      >> (unabbrev_all_tac >> gvs[events_ecc_bsc_prob_space, POW_DEF]
          >> gvs[SUBSET_DEF] >> rw[] >> Cases_on ‘x’ >> ASM_SET_TAC[]
         )
     )
  (* Each of the events has nonzero probability *)
  >> sg ‘prob sp e1 ≠ 0 ∧
         prob sp e2 ≠ 0 ∧
         prob sp e3 ≠ 0’
  >- (rw[] >> (unabbrev_all_tac >> gvs[prob_ecc_bsc_prob_space_zero]
               >> gvs[FUN_EQ_THM] >> rw[])
      >- (qexists ‘(REPLICATE n F, REPLICATE (LENGTH ds) F)’
          >> gvs[EL_REPLICATE])
      >- (qexists ‘(REPLICATE n T, REPLICATE (LENGTH ds) F)’
          >> gvs[EL_REPLICATE])
      >- (qexists ‘(REPLICATE n F, bxor (enc (REPLICATE n F)) ds)’
          >> gvs[bxor_length, bxor_inv]
         )
     )
  (* *)
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_additive_finite]
QED

(* -------------------------------------------------------------------------- *)
(* Finding the bits that maximize the probability of receiving that bit,      *)
(* given that we received a particular message, is equivalent to finding the  *)
(* bits that maximize the probably that we both received that bit and         *)
(* received that message.                                                     *)
(*                                                                            *)
(* In more generality, if we are finding an argmax over a conditional         *)
(* probability where only the first event depends on the variable we are      *)
(* applying the argmax to, then the conditional probability can be reduced    *)
(* to an intersection.                                                        *)
(*                                                                            *)
(* This theorem fails, because what if both choices of bit have an equal      *)
(* probability? Since a bit is being chosen arbitrarily, we don't know if the *)
(* bit is equialent to the other bit chosen arbitrarily.                      *)
(* -------------------------------------------------------------------------- *)
(*Theorem argmax_cond_prob:
  ∀p_space P e s.
    s ≠ ∅ ∧ FINITE s ⇒
    argmax (λx. cond_prob p_space (P x) e) s =
    argmax (λx. prob p_space ((P x) ∩ e)) s
Proof
  rw[]
  >> last_x_assum mp_tac
  >> SPEC_ALL_TAC
  >> Induct_on ‘s’
  >> rw[]
  >> Cases_on ‘s’
  >- gvs[]
  >> gvs[]
  >> 
QED*)


val _ = export_theory();
