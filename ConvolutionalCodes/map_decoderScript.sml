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
(* The main definition in this file is map_decoder_bitwise_def.               *)
(* -------------------------------------------------------------------------- *)
(* The probability space that we are working over is the one which consists   *)
(* of choosing an input uniformly at random and then choosing a sequence of   *)
(* random bit-flips to apply to the encoded string. Thus, an event in our     *)
(* probability space consists of a set of the possible (input, noise) pairs   *)
(* which satisfy that event.                                                  *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* The event where a single input takes a specific value                      *)
(*                                                                            *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* i: the index of the bit which takes a specific value                       *)
(* x: the specific value that that bit takes                                  *)
(*                                                                            *)
(* Output: the set of all possible choices of input and noise for which the   *)
(*         chosen input bit takes the chosen value.                           *)
(* -------------------------------------------------------------------------- *)
Definition event_single_input_takes_value_def:
  event_single_input_takes_value n m i x =
  (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ EL i bs = x)
End

(* -------------------------------------------------------------------------- *)
(* The event where the entire input takes a specific value                    *)
(*                                                                            *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* xs: the value that the input takes.                                        *)
(*                                                                            *)
(* Output: the set of all possible choices of input and noise for which the   *)
(*         input takes the chosen value.                                      *)
(* -------------------------------------------------------------------------- *)
Definition event_input_takes_value_def:
  event_input_takes_value n m xs =
  (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ bs = xs)
End

(* -------------------------------------------------------------------------- *)
(* Convert several disparate events which are closely related to              *)
(* event_single_input_takes_value into a form in terms of                     *)
(* event_single_input_takes_value. This allows us to apply theorems proven    *)
(* for event_single_input_takes_value to any of these events.                 *)
(* -------------------------------------------------------------------------- *)
Theorem to_event_single_input_takes_value:
  ∀n m i x.
    (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ EL i bs = x) =
    event_single_input_takes_value n m i x ∧
    (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ EL i bs ≠ x) =
    event_single_input_takes_value n m i (¬x) ∧
    (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ EL i bs) =
    event_single_input_takes_value n m i T ∧
    (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ ¬(EL i bs)) =
    event_single_input_takes_value n m i F
Proof
  rw[] >> gvs[event_single_input_takes_value_def]
  >> Cases_on ‘x’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* The event in which the initially sent string together with the added noise *)
(* produce the bitstring which was observed.                                  *)
(*                                                                            *)
(* enc: the encoding function                                                 *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* ds: the bitstring which was received                                       *)
(* -------------------------------------------------------------------------- *)
Definition event_received_string_is_correct_def:
  event_received_string_is_correct enc n m ds =
  (λ(bs, ns). LENGTH bs = n ∧ LENGTH ns = m ∧ bxor (enc bs) ns = ds)
End

(* -------------------------------------------------------------------------- *)
(* Choose the value of a bit which maximizes the value of an extreal-valued   *)
(* function.                                                                  *)
(*                                                                            *)
(* f: the function to maximize (bool -> extreal)                              *)
(* Output: the choice of bit which maximize that function                     *)
(* -------------------------------------------------------------------------- *)
Definition argmax_bool_def:
  argmax_bool f = (f F ≤ f T : extreal)
End

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
                    (event_single_input_takes_value n m i x)
                    (event_received_string_is_correct enc n m ds);
  in
    MAP (λi. argmax_bool (map_decoder_bit_prob i)) (COUNT_LIST n)
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
(* A division by a constant within an argmax_bool can be cancelled out        *)
(* -------------------------------------------------------------------------- *)
Theorem argmax_bool_div:
  ∀P c.
    0 < c ∧
    c ≠ +∞ ⇒
    argmax_bool (λb. P b / c) = argmax_bool P
Proof
  rw[]
  >> gvs[argmax_bool_def]
  >> gvs[ldiv_le_iff]
QED

(* -------------------------------------------------------------------------- *)
(* A conditional probability within an argmax_bool can be converted into an   *)
(* ordinary probability                                                       *)
(* -------------------------------------------------------------------------- *)
Theorem argmax_bool_cond_prob:
  ∀sp P B.
    prob_space sp ∧
    B ∈ events sp ∧
    prob sp B ≠ 0 ⇒
    (argmax_bool (λb. cond_prob sp (P b) B) =
     argmax_bool (λb. prob sp (P b ∩ B)))
Proof
  rw[]
  (* Decompose conditional probability into its component probabilities *)
  >> gvs[cond_prob_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[argmax_bool_div]
  >> gvs[PROB_FINITE, lt_le, PROB_POSITIVE]
QED

(* -------------------------------------------------------------------------- *)
(* event_single_input_takes_value is a valid event in the probability space   *)
(* it is designed for                                                         *)
(* -------------------------------------------------------------------------- *)
Theorem event_single_input_takes_value_is_event:
  ∀n m i x p.
    event_single_input_takes_value n m i x ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[event_single_input_takes_value_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (Cases_on ‘x'’ >> gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* event_input_takes_value is a valid event in the probability space          *)
(* it is designed for                                                         *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_takes_value_is_event:
  ∀n m xs p.
    event_input_takes_value n m xs ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[event_input_takes_value_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (Cases_on ‘x’ >> gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* event_received_string_is_correct is a valid event in the probability space *)
(* it is designed for                                                         *)
(* -------------------------------------------------------------------------- *)
Theorem event_received_string_is_correct_is_event:
  ∀enc n m ds p.
    event_received_string_is_correct enc n m ds ∈
                                     events (ecc_bsc_prob_space n m p)
Proof
  rw[event_received_string_is_correct_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (Cases_on ‘x’ >> gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* event_single_input_takes_value has a nonzero probability                   *)
(* -------------------------------------------------------------------------- *)
Theorem event_single_input_takes_value_nonzero_prob:
  ∀n m i x p.
    0 < p ∧
    p < 1 ∧
    i < n ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_single_input_takes_value n m i x) ≠ 0
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> gvs[event_single_input_takes_value_is_event]
  >> gvs[EXTENSION] >> rw[event_single_input_takes_value_def]
  >> qexists ‘(REPLICATE n x, REPLICATE m F)’
  >> gvs[EL_REPLICATE]
QED

(* -------------------------------------------------------------------------- *)
(* event_input_takes_value has a nonzero probability                   *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_takes_value_nonzero_prob:
  ∀n m xs p.
    0 < p ∧
    p < 1 ∧
    LENGTH xs = n ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_input_takes_value n m xs) ≠ 0
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> gvs[event_input_takes_value_is_event]
  >> gvs[EXTENSION] >> rw[event_input_takes_value_def]
  >> qexists ‘(xs, REPLICATE m F)’
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* event_received_string_is_correct has a nonzero probability                 *)
(* -------------------------------------------------------------------------- *)
Theorem event_received_string_is_correct_nonzero_prob:
  ∀enc n m ds p.
    0 < p ∧
    p < 1 ∧
    LENGTH ds = m ∧
    (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_received_string_is_correct enc n m ds) ≠ 0
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> gvs[event_received_string_is_correct_is_event]
  >> gvs[EXTENSION] >> rw[event_received_string_is_correct_def]
  >> qexists ‘(REPLICATE n F, bxor (enc (REPLICATE n F)) ds)’
  >> gvs[bxor_length, bxor_inv]
QED

Theorem event_input_takes_value_and_received_string_is_correct_is_event:
  ∀enc n m xs ds p.
    ((event_input_takes_value n m xs)
     ∩ (event_received_string_is_correct enc n m ds))
    ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[event_received_string_is_correct_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (Cases_on ‘x’ >> gvs[])
QED

Theorem event_input_takes_value_and_received_string_is_correct_nonzero_prob:
  ∀enc n m xs ds p.
    0 < p ∧
    p < 1 ∧
    LENGTH xs = n ∧
    LENGTH ds = m ∧
    (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
    prob (ecc_bsc_prob_space n m p)
         ((event_input_takes_value n m xs)
          ∩ (event_received_string_is_correct enc n m ds)) ≠ 0
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> rw[]
  >- (irule EVENTS_INTER
      >> gvs[ecc_bsc_prob_space_is_prob_space, le_lt,
             event_received_string_is_correct_is_event,
             event_input_takes_value_is_event]
     )
  >> gvs[EXTENSION] >> rw[]
  >> gvs[event_received_string_is_correct_def, event_input_takes_value_def]
  >> qexists ‘(xs, bxor (enc xs) ds)’
  >> gvs[bxor_length, bxor_inv]
QED

(* -------------------------------------------------------------------------- *)
(* The probability that the input is of a certain form                        *)
(* -------------------------------------------------------------------------- *)
Theorem prob_event_input_takes_value:
  ∀n m xs p.
    0 ≤ p ∧ p ≤ 1 ∧
    LENGTH xs = n ⇒
    prob (ecc_bsc_prob_space n m p) (event_input_takes_value n m xs) =
    1 / (2 pow LENGTH xs)
Proof
  (* Use the expression for the probability in this probability space to
     simplify. *)
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space]
  >> gvs[event_input_takes_value_is_event]
  (* Expand out the definition of the event we are calculating the probability
     of *)
  >> gvs[event_input_takes_value_def]
  (* Rewrite this in terms of sym_noise_dist by pushing the SND across to the
     set we are summing over. This will allow us to prove that this sum is
     equal to 1. *)
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_IMAGE]
  >> rw[]
  >- (qmatch_goalsub_abbrev_tac ‘FINITE S’
      >> sg ‘S ⊆ length_n_codes (LENGTH xs) × length_n_codes m’
      >- (unabbrev_all_tac >> gvs[SUBSET_DEF]
          >> rw[] >> (Cases_on ‘x’ >> gvs[]))
      >> metis_tac[length_n_codes_finite, FINITE_SUBSET, FINITE_CROSS]
     )
  >- (gvs[INJ_DEF]
      >> rw[]
      >> Cases_on ‘x’ >> Cases_on ‘y’ >> gvs[]
     )
  >- (disj1_tac
      >> rw[]
      >> gvs[sym_noise_mass_func_not_neginf]
     )
  >> gvs[GSYM sym_noise_dist_def]
  (* The set we are taking the distribution over is the set of all possible
     length m codes. *)
  >> qmatch_goalsub_abbrev_tac ‘sym_noise_dist _ S’
  >> sg ‘S = length_n_codes m’
  >- (unabbrev_all_tac
      >> gvs[EXTENSION] >> rw[]
      >> EQ_TAC >> rw[]
      >- (Cases_on ‘x'’ >> gvs[])
      >> qexists ‘(xs, x)’
      >> gvs[]
     )
  >> pop_assum (fn th => gvs[th])
  >> gvs[sym_noise_dist_length_n_codes]
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
             ((event_single_input_takes_value n m i x)
              ∩ (event_received_string_is_correct enc n m ds));
    in
      MAP (λi. argmax_bool (map_decoder_bit_prob_joint i)) (COUNT_LIST n)
Proof
  rw[]
  (* 0 ≤ p and p ≤ 1 is a more common representation for a probability than
     0 < p and p < 1. *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* We need to prove that the inside of the MAP is equivalent *)
  >> gvs[map_decoder_bitwise_def, MAP_EQ_f]
  >> rw[]
  >> gvs[MEM_COUNT_LIST]
  (* Use lemma which says that taking the argmax_bool of a condintional
     probability is equivalent to taking the argmax_bool of a probability *)
  >> irule argmax_bool_cond_prob
  >> gvs[ecc_bsc_prob_space_is_prob_space,
         event_received_string_is_correct_is_event,
         event_received_string_is_correct_nonzero_prob]
QED

(* -------------------------------------------------------------------------- *)
(* Apply Bayes' rule to the inside of an argmax_bool                          *)
(* -------------------------------------------------------------------------- *)
Theorem argmax_bool_bayes:
  ∀sp P B.
    prob_space sp ∧
    B ∈ events sp ∧
    prob sp B ≠ 0 ∧
    (∀b. P b ∈ events sp) ∧
    (∀b. prob sp (P b) ≠ 0) ⇒
    argmax_bool (λb. cond_prob sp (P b) B) =
    argmax_bool (λb. cond_prob sp B (P b) * prob sp (P b))
Proof
  rw[]
  >> gvs[argmax_bool_cond_prob]
  >> gvs[cond_prob_def]
  >> gvs[prob_div_mul_refl]
  >> gvs[INTER_COMM]
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
      e1 = event_received_string_is_correct enc n m ds;
      e2 = event_single_input_takes_value n m;
      map_decoder_bit_prob_bayes = λi x. cond_prob sp e1 (e2 i x) *
                                         prob sp (e2 i x);
    in
      MAP (λi. argmax_bool (map_decoder_bit_prob_bayes i)) (COUNT_LIST n)
Proof
  (* Look at the internals *)
  rpt strip_tac
  >> gvs[map_decoder_bitwise_def]
  (* More common representation of probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* The inner bit is the bit we need to prove equivalence of. We only need
     to prove equivalence for valid i, that is, i < n *)
  >> qmatch_goalsub_abbrev_tac ‘MAP f1 (COUNT_LIST n) = MAP f2 (COUNT_LIST n)’
  >> gvs[MAP_EQ_f]
  >> rw[Abbr ‘f1’, Abbr ‘f2’]
  >> gvs[MEM_COUNT_LIST]
  (* The result follows from a lemma *)
  >> irule argmax_bool_bayes
  >> gvs[ecc_bsc_prob_space_is_prob_space,
         event_received_string_is_correct_is_event,
         event_received_string_is_correct_nonzero_prob,
         event_single_input_takes_value_is_event,
         event_single_input_takes_value_nonzero_prob]
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

Theorem length_n_codes_single_input_takes_value_intersection:
  ∀n i x.
    {bs | LENGTH bs = n ∧ (EL i bs ⇔ x)} =
                          length_n_codes n ∩ {bs | EL i bs ⇔ x}
Proof
  rw[]
  >> gvs[INTER_DEF]
QED

Theorem event_input_takes_value_disjoint:
  ∀n m xs xs'.
    xs ≠ xs' ⇒
    DISJOINT (event_input_takes_value n m xs) (event_input_takes_value n m xs')
Proof
  rw[DISJOINT_DEF, event_input_takes_value_def, INTER_DEF, EXTENSION]
  >> Cases_on ‘x’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* The event where a single input takes a value can be expressed as the       *)
(* bigunion of several events where the entire input takes a specific value.  *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_takes_value_bigunion:
  ∀n m i x.
    event_single_input_takes_value n m i x =
    BIGUNION (IMAGE (event_input_takes_value n m)
                    (length_n_codes n ∩ {xs | EL i xs ⇔ x}))
Proof
  rw[]
  >> gvs[BIGUNION_IMAGE, event_single_input_takes_value_def,
         event_input_takes_value_def]
  >> rw[EXTENSION]
  >> EQ_TAC >> rw[]
  >> (Cases_on ‘x'’ >> gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* The conditional probability of a single input taking a certain value can   *)
(* be expressed as the sum of the conditional probabilities of all possible   *)
(* inputs such that the single input takes the correct value                  *)
(* -------------------------------------------------------------------------- *)
Theorem cond_prob_event_input_takes_value_sum:
  ∀enc n m p i x ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
    cond_prob
    (ecc_bsc_prob_space n m p)
    (event_single_input_takes_value n m i x)
    (event_received_string_is_correct enc n m ds) =
    ∑ (λxs.
         cond_prob (ecc_bsc_prob_space n m p)
                   (event_input_takes_value n m xs)
                   (event_received_string_is_correct enc n m ds)
      )
      {xs | LENGTH xs = n ∧ (EL i xs = x)}
Proof
  rw[]
  (* More common representation of probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  >> assume_tac ecc_bsc_prob_space_is_prob_space
  >> assume_tac event_input_takes_value_is_event
  >> assume_tac event_received_string_is_correct_is_event
  >> assume_tac event_received_string_is_correct_nonzero_prob
  (* Rewrite the set we are summing over in terms of an intersection with
     length_n_codes *)
  >> gvs[length_n_codes_single_input_takes_value_intersection]
  (* Bring the sum into the cond_prob, turning it into a union *)
  >> DEP_PURE_REWRITE_TAC[GSYM cond_prob_additive_finite]
  >> rw[]
  >- gvs[event_input_takes_value_disjoint]
  (* Now it suffices to prove that the events in the cond_prob are equivalent *)
  >> qmatch_goalsub_abbrev_tac ‘cond_prob sp e1 e3 = cond_prob sp e2 e3’
  >> ‘e1 = e2’ suffices_by gvs[]
  >> unabbrev_all_tac
  >> gvs[event_input_takes_value_bigunion]
  >> metis_tac[]
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
                     (event_input_takes_value n m xs)
                     (event_received_string_is_correct enc n m ds);
      map_decoder_bit_prob =
      λi x. ∑ map_decoder_bitstring_prob {bs | LENGTH bs = n ∧ EL i bs = x};
    in
      (MAP (λi. argmax_bool (map_decoder_bit_prob i)) (COUNT_LIST n))
Proof
  (* Look at the internals *)
  rpt strip_tac
  >> gvs[map_decoder_bitwise_def]
  (* More common representation of probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* The inner bit is the bit we need to prove equivalence of. We only need
     to prove equivalence for valid i, that is, i < n *)
  >> qmatch_goalsub_abbrev_tac ‘MAP f1 (COUNT_LIST n) = MAP f2 (COUNT_LIST n)’
  >> gvs[MAP_EQ_f]
  >> rw[Abbr ‘f1’, Abbr ‘f2’]
  >> gvs[MEM_COUNT_LIST]
  (* This follows from a lemma *)
  >>  gvs[cond_prob_event_input_takes_value_sum]
QED

Theorem argmax_bool_mul_const:
  ∀f g c.
    0 < c ∧
    c ≠ +∞ ∧
    (g = λx. c * f x)
    ⇒ (argmax_bool f ⇔ argmax_bool g)
Proof
  rw[]
  >> gvs[argmax_bool_def]
  >> gvs[le_lmul]
QED

(* -------------------------------------------------------------------------- *)
(* A version of the MAP decoder which has both been represented as the sum    *)
(* over all possible choices of input and had Bayes' rule applied to it       *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_sum_bayes:
  ∀enc n m p ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      map_decoder_bitstring_prob_bayes =
      λxs. cond_prob (ecc_bsc_prob_space n m p)
                     (event_received_string_is_correct enc n m ds)
                     (event_input_takes_value n m xs) *
           prob (ecc_bsc_prob_space n m p)
                (event_input_takes_value n m xs);
      map_decoder_bit_prob =
      λi x.
        ∑ map_decoder_bitstring_prob_bayes {bs | LENGTH bs = n ∧ EL i bs = x};
    in
      (MAP (λi. argmax_bool (map_decoder_bit_prob i)) (COUNT_LIST n))
Proof
  (* Convert to the sum version *)
  rw[]
  >> gvs[map_decoder_bitwise_sum]
  (* More common representation of probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* Useful theorems *)
  >> assume_tac ecc_bsc_prob_space_is_prob_space
  >> assume_tac event_input_takes_value_is_event
  >> assume_tac event_input_takes_value_nonzero_prob
  >> assume_tac event_received_string_is_correct_is_event
  >> assume_tac event_received_string_is_correct_nonzero_prob
  >> assume_tac event_input_takes_value_and_received_string_is_correct_is_event
  >> assume_tac
     event_input_takes_value_and_received_string_is_correct_nonzero_prob
  (* The inner bit is the bit we need to prove equivalence of. We only need
     to prove equivalence for valid i, that is, i < n *)
  >> gvs[MAP_EQ_f]
  >> rw[]
  >> gvs[MEM_COUNT_LIST]
  (* Rewrite cond_prob in terms of probabilities to make things more clear *)
  >> gvs[cond_prob_def]
  (* This follows from the fact that one of the inner bits is a nonnegative
     finite multiple of the other *)
  >> irule argmax_bool_mul_const
  >> qexists ‘prob (ecc_bsc_prob_space n (LENGTH ds) p)
              (event_received_string_is_correct enc n (LENGTH ds) ds)’
  >> gvs[PROB_FINITE]
  >> REVERSE conj_tac >- gvs[lt_le, PROB_POSITIVE]
  (* Simplify *)
  >> gvs[FUN_EQ_THM]
  >> rw[]
  (* The function in the first sum can be simplified by cancelling the
     division with the multiplication, but we need to know that the input
     is in length_n_codes n. *)
  >> qmatch_goalsub_abbrev_tac ‘∑ f S = _ * _’
  >> sg ‘∀xs.
           xs ∈ S ⇒
           f xs =
           prob (ecc_bsc_prob_space n (LENGTH ds) p)
                ((event_received_string_is_correct enc n (LENGTH ds) ds)
                       ∩ event_input_takes_value n (LENGTH ds) xs)
        ’
  >- (rw[Abbr ‘f’]
      >> gvs[Abbr ‘S’, prob_div_mul_refl])
  >> sg ‘FINITE S’
  >- gvs[Abbr ‘S’, length_n_codes_single_input_takes_value_intersection]
  >> qspecl_then
     [‘f’,
      ‘λxs. prob (ecc_bsc_prob_space n (LENGTH ds) p)
                 ((event_received_string_is_correct enc n (LENGTH ds) ds)
                  ∩ event_input_takes_value n (LENGTH ds) xs)’,
      ‘S’] assume_tac EXTREAL_SUM_IMAGE_EQ'
  >> gvs[]
  (* Remove assumptions about f because we no longer have it since we have
     replaced it with its simplified version *)
  >> qpat_x_assum ‘∑ f S = _’ kall_tac
  >> qpat_x_assum ‘∀xs. xs ∈ S ⇒ f _ = _’ kall_tac
  >> qpat_x_assum ‘Abbrev (f = _)’ kall_tac
  (* Rewrite the goal in a form which makes it easier to see what's going on.
     In particular, we have a multiplication and division by a constant. *)
  >> qmatch_goalsub_abbrev_tac ‘LHS = c * ∑ (λxs. g1 (g2 xs ∩ g3) / c) S’
  (* Move the constant into the sum. *)
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_CMUL_R_ALT]
  >> rw[]
  >- (unabbrev_all_tac >> gvs[PROB_FINITE])
  >- (unabbrev_all_tac >> gvs[PROB_FINITE])
  >- (disj2_tac >> rw[Abbr ‘g1’, Abbr ‘g2’, Abbr ‘g3’]
      >> qmatch_goalsub_abbrev_tac ‘num / c’
      >> Cases_on ‘c’ >> Cases_on ‘num’ >> gvs[extreal_div_def, PROB_FINITE]
      >> irule (cj 1 div_not_infty)
      >> metis_tac[]
     )
  (* Cancel out the constant *)
  >> unabbrev_all_tac >> gvs[prob_div_mul_refl]
  (* Intersection commutativity *)
  >> gvs[INTER_COMM]
QED



val _ = export_theory();
