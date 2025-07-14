(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

(* My theories *)
open ecc_prob_spaceTheory;
open argmin_extrealTheory;

(* My libraries *)
open donotexpandLib;
open useful_tacticsLib;

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
(* This is based on "Modern Coding Theory" by Tom Richardson and Rüdiger      *)
(* Urbanke.                                                                   *)
(*                                                                            *)
(* In particular, the guide for our proofs is the simplification of the       *)
(* generic bitwise MAP decoder on page 326 (chapter 6)                        *)
(* -------------------------------------------------------------------------- *)
             
(* -------------------------------------------------------------------------- *)
(* We define the generic bitwise MAP decoder, and transform it into a form    *)
(* which is closer to a factor graph.                                         *)
(*                                                                            *)
(* - We define a MAP decoder in map_decoder_bitwise_def                       *)
(* - We sum out all the inputs that aren't being optimized over in            *)
(*   map_decoder_bitwise_sum                                                  *)
(* - We apply Bayes' rule on top of this in map_decoder_bitwise_sum_bayes     *)
(* - We split up the probability of receiving the received bits given the     *)
(*   input bits into a product of probabilities of receiving each individual  *)
(*   bit given the bit that was initially sent in                             *)
(*   map_decoder_bitwise_sum_bayes_prod                                       *)
(*                                                                            *)
(* This gives us a sum of products, which is the kind of form which factor    *)
(* graphs can be applied to.                                                  *)
(*                                                                            *)
(* It would also be possible to simplify the prior probability of a bitstring *)
(* being sent into the indicator function on whether or not that bitstring    *)
(* is in the code (under the assumption that we have a uniform prior on the   *)
(* codewords that are initially sent), but I didn't find this necessary.      *)
(*                                                                            *)
(* We also define some useful events, prove that they are valid events and    *)
(* that they have nonzero probability, provide an expression for the          *)
(* probability of one of them, and prove other useful theorems.               *)
(*                                                                            *)
(* The probability space that we are working over is the one which consists   *)
(* of choosing an input uniformly at random and then choosing a sequence of   *)
(* random bit-flips to apply to the encoded string. Thus, an event in our     *)
(* probability space consists of a set of the possible (input, noise) pairs   *)
(* which satisfy that event.                                                  *)
(*                                                                            *)
(* Notation:                                                                  *)
(* - bs: the input bitstring                                                  *)
(* - cs: the bitstring that was sent (after encoding)                         *)
(* - ds: the bitstring that was received (after noise was applied)            *)
(* - b, c, d: individual bits in bs, cs, ds                                   *)
(* - ns: the noise added to cs in order to create ds                          *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* The event where a single input takes a specific value                      *)
(*                                                                            *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* i: the index of the bit which takes a specific value                       *)
(* b: the specific value that that bit takes                                  *)
(*                                                                            *)
(* Output: the set of all possible choices of input and noise for which the   *)
(*         chosen input bit takes the chosen value.                           *)
(* -------------------------------------------------------------------------- *)
Definition event_input_bit_takes_value_def:
  event_input_bit_takes_value n m i b =
  {(bs, ns) | LENGTH bs = n ∧ LENGTH ns = m ∧ EL i bs = b}
End

(* -------------------------------------------------------------------------- *)
(* The event where the entire input takes a specific value                    *)
(*                                                                            *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* bs: the value that the input takes.                                        *)
(*                                                                            *)
(* Output: the set of all possible choices of input and noise for which the   *)
(*         input takes the chosen value.                                      *)
(* -------------------------------------------------------------------------- *)
Definition event_input_string_takes_value_def:
  event_input_string_takes_value n m bs' =
  {(bs, ns) | LENGTH bs = n ∧ LENGTH ns = m ∧ bs = bs'}
End

(* -------------------------------------------------------------------------- *)
(* The event in which the initially sent string together with the added noise *)
(* produce a specific bitstring.                                              *)
(*                                                                            *)
(* enc: the encoding function                                                 *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* ds: the bitstring which was received                                       *)
(* -------------------------------------------------------------------------- *)
Definition event_received_string_takes_value_def:
  event_received_string_takes_value enc n m ds =
  {(bs, ns) | LENGTH bs = n ∧ LENGTH ns = m ∧ bxor (enc bs) ns = ds}
End

(* -------------------------------------------------------------------------- *)
(* The event in which the initially sent string together with the added noise *)
(* produe a specific bit at a specific index.                                 *)
(*                                                                            *)
(* enc: the encoding function                                                 *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* i: the index of the bit which takes a specific value                       *)
(* d: the bitstring which was received                                        *)
(* -------------------------------------------------------------------------- *)
Definition event_received_bit_takes_value_def:
  event_received_bit_takes_value enc n m i d =
  {(bs, ns) | LENGTH bs = n ∧ LENGTH ns = m ∧ EL i (bxor (enc bs) ns) = d}
End

(* -------------------------------------------------------------------------- *)
(* The event in which the initially sent string is a specific bitstring       *)
(*                                                                            *)
(* enc: the encoding function                                                 *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* ds: the bitstring which was sent                                           *)
(* -------------------------------------------------------------------------- *)
Definition event_sent_string_takes_value_def:
  event_sent_string_takes_value enc n m cs =
  {(bs, ns) | LENGTH bs = n ∧ LENGTH ns = m ∧ enc bs = cs}
End

(* -------------------------------------------------------------------------- *)
(* The event in which the initially sent string has a specific bit at a       *)
(* certain index                                                              *)
(*                                                                            *)
(* enc: the encoding function                                                 *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* i: the index of the bit which takes a specific value                       *)
(* d: the specific value that the bit takes                                   *)
(* -------------------------------------------------------------------------- *)
Definition event_sent_bit_takes_value_def:
  event_sent_bit_takes_value enc n m i c =
  {(bs, ns) | LENGTH bs = n ∧ LENGTH ns = m ∧ EL i (enc bs) = c}
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
                    (event_input_bit_takes_value n m i x)
                    (event_received_string_takes_value enc n m ds);
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
(* event_input_bit_takes_value is a valid event in the probability space      *)
(* it is designed for                                                         *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_bit_takes_value_is_event:
  ∀n m i b p.
    event_input_bit_takes_value n m i b ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[event_input_bit_takes_value_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* event_input_string_takes_value is a valid event in the probability space   *)
(* it is designed for                                                         *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_string_takes_value_is_event:
  ∀n m bs p.
    event_input_string_takes_value n m bs ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[event_input_string_takes_value_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* event_received_string_takes_value is a valid event in the probability      *)
(* space it is designed for                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem event_received_string_takes_value_is_event:
  ∀enc n m ds p.
    event_received_string_takes_value enc n m ds ∈
                                     events (ecc_bsc_prob_space n m p)
Proof
  rw[event_received_string_takes_value_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* event_input_bit_takes_value has a nonzero probability                      *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_bit_takes_value_nonzero_prob:
  ∀n m i b p.
    0 < p ∧
    p < 1 ∧
    i < n ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_input_bit_takes_value n m i b) ≠ 0
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> gvs[event_input_bit_takes_value_is_event]
  >> gvs[EXTENSION] >> rw[event_input_bit_takes_value_def]
  >> qexistsl [‘REPLICATE n b’, ‘REPLICATE m F’]
  >> gvs[EL_REPLICATE]
QED

(* -------------------------------------------------------------------------- *)
(* event_input_string_takes_value has a nonzero probability                   *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_string_takes_value_nonzero_prob:
  ∀n m bs p.
    0 < p ∧
    p < 1 ∧
    LENGTH bs = n ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_input_string_takes_value n m bs) ≠ 0
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> gvs[event_input_string_takes_value_is_event]
  >> gvs[EXTENSION] >> rw[event_input_string_takes_value_def]
  >> qexists ‘REPLICATE m F’
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* event_received_string_takes_value has a nonzero probability                *)
(* -------------------------------------------------------------------------- *)
Theorem event_received_string_takes_value_nonzero_prob:
  ∀enc n m ds p.
    0 < p ∧
    p < 1 ∧
    LENGTH ds = m ∧
    (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_received_string_takes_value enc n m ds) ≠ 0
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> gvs[event_received_string_takes_value_is_event]
  >> gvs[EXTENSION] >> rw[event_received_string_takes_value_def]
  >> qexistsl [‘REPLICATE n F’, ‘bxor (enc (REPLICATE n F)) ds’]
  >> gvs[bxor_length, bxor_inv]
QED

Theorem event_input_string_and_received_string_take_values_is_event:
  ∀enc n m bs ds p.
    ((event_input_string_takes_value n m bs)
     ∩ (event_received_string_takes_value enc n m ds))
    ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[event_received_string_takes_value_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (gvs[])
QED

Theorem event_input_string_and_received_string_take_values_nonzero_prob:
  ∀enc n m bs ds p.
    0 < p ∧
    p < 1 ∧
    LENGTH bs = n ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    prob (ecc_bsc_prob_space n m p)
         ((event_input_string_takes_value n m bs)
          ∩ (event_received_string_takes_value enc n m ds)) ≠ 0
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> rw[]
  >- (irule EVENTS_INTER
      >> gvs[ecc_bsc_prob_space_is_prob_space, le_lt,
             event_received_string_takes_value_is_event,
             event_input_string_takes_value_is_event]
     )
  >> gvs[EXTENSION] >> rw[]
  >> gvs[event_received_string_takes_value_def, event_input_string_takes_value_def]
  >> qexists ‘(bs, bxor (enc bs) ds)’
  >> gvs[bxor_length, bxor_inv]
QED

(* -------------------------------------------------------------------------- *)
(* The probability that the input is of a certain form                        *)
(* -------------------------------------------------------------------------- *)
Theorem prob_event_input_string_takes_value:
  ∀n m bs p.
    0 ≤ p ∧ p ≤ 1 ∧
    LENGTH bs = n ⇒
    prob (ecc_bsc_prob_space n m p) (event_input_string_takes_value n m bs) =
    1 / (2 pow LENGTH bs)
Proof
  (* Use the expression for the probability in this probability space to
     simplify. *)
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space]
  >> gvs[event_input_string_takes_value_is_event]
  (* Expand out the definition of the event we are calculating the probability
     of *)
  >> gvs[event_input_string_takes_value_def]
  (* Rewrite this in terms of sym_noise_dist by pushing the SND across to the
     set we are summing over. This will allow us to prove that this sum is
     equal to 1. *)
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_IMAGE]
  >> rw[]
  >- (qmatch_goalsub_abbrev_tac ‘FINITE S’
      >> sg ‘S ⊆ length_n_codes (LENGTH bs) × length_n_codes m’
      >- (unabbrev_all_tac >> gvs[SUBSET_DEF]
          >> rw[] >> (gvs[]))
      >> metis_tac[length_n_codes_finite, FINITE_SUBSET, FINITE_CROSS]
     )
  >- (gvs[INJ_DEF]
      >> rw[]
      >> gvs[]
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
      >- (gvs[])
      >> qexists ‘(bs, x)’
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
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      map_decoder_bit_prob_joint =
      λi b.
        prob (ecc_bsc_prob_space n m p)
             ((event_input_bit_takes_value n m i b)
              ∩ (event_received_string_takes_value enc n m ds));
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
         event_received_string_takes_value_is_event,
         event_received_string_takes_value_nonzero_prob]
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
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      sp = ecc_bsc_prob_space n m p;
      e1 = event_received_string_takes_value enc n m ds;
      e2 = event_input_bit_takes_value n m;
      map_decoder_bit_prob_bayes = λi b. cond_prob sp e1 (e2 i b) *
                                         prob sp (e2 i b);
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
         event_received_string_takes_value_is_event,
         event_received_string_takes_value_nonzero_prob,
         event_input_bit_takes_value_is_event,
         event_input_bit_takes_value_nonzero_prob]
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

Theorem event_input_string_takes_value_disjoint:
  ∀n m bs bs'.
    bs ≠ bs' ⇒
    DISJOINT (event_input_string_takes_value n m bs) (event_input_string_takes_value n m bs')
Proof
  rw[DISJOINT_DEF, event_input_string_takes_value_def, INTER_DEF, EXTENSION]
  >> Cases_on ‘x’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* The event where a single input takes a value can be expressed as the       *)
(* bigunion of several events where the entire input takes a specific value.  *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_string_takes_value_bigunion:
  ∀n m i b.
    event_input_bit_takes_value n m i b =
    BIGUNION (IMAGE (event_input_string_takes_value n m)
                    (length_n_codes n ∩ {bs | EL i bs ⇔ b}))
Proof
  rw[]
  >> gvs[BIGUNION_IMAGE, event_input_bit_takes_value_def,
         event_input_string_takes_value_def]
  >> rw[EXTENSION]
  >> EQ_TAC >> rw[]
  >> (Cases_on ‘x’ >> gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* The conditional probability of a single input taking a certain value can   *)
(* be expressed as the sum of the conditional probabilities of all possible   *)
(* inputs such that the single input takes the correct value                  *)
(* -------------------------------------------------------------------------- *)
Theorem cond_prob_event_input_string_takes_value_sum:
  ∀enc n m p i b ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    cond_prob
    (ecc_bsc_prob_space n m p)
    (event_input_bit_takes_value n m i b)
    (event_received_string_takes_value enc n m ds) =
    ∑ (λbs.
         cond_prob (ecc_bsc_prob_space n m p)
                   (event_input_string_takes_value n m bs)
                   (event_received_string_takes_value enc n m ds)
      )
      {bs | LENGTH bs = n ∧ (EL i bs = b)}
Proof
  rw[]
  (* More common representation of probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  >> assume_tac ecc_bsc_prob_space_is_prob_space
  >> assume_tac event_input_string_takes_value_is_event
  >> assume_tac event_received_string_takes_value_is_event
  >> assume_tac event_received_string_takes_value_nonzero_prob
  (* Rewrite the set we are summing over in terms of an intersection with
     length_n_codes *)
  >> gvs[length_n_codes_single_input_takes_value_intersection]
  (* Bring the sum into the cond_prob, turning it into a union *)
  >> DEP_PURE_REWRITE_TAC[GSYM cond_prob_additive_finite]
  >> rw[]
  >- gvs[event_input_string_takes_value_disjoint]
  (* Now it suffices to prove that the events in the cond_prob are equivalent *)
  >> qmatch_goalsub_abbrev_tac ‘cond_prob sp e1 e3 = cond_prob sp e2 e3’
  >> ‘e1 = e2’ suffices_by gvs[]
  >> unabbrev_all_tac
  >> gvs[event_input_string_takes_value_bigunion]
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
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      map_decoder_bitstring_prob =
      λbs. cond_prob (ecc_bsc_prob_space n m p)
                     (event_input_string_takes_value n m bs)
                     (event_received_string_takes_value enc n m ds);
      map_decoder_bit_prob =
      λi b. ∑ map_decoder_bitstring_prob {bs | LENGTH bs = n ∧ EL i bs = b};
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
  >>  gvs[cond_prob_event_input_string_takes_value_sum]
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
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      map_decoder_bitstring_prob_bayes =
      λbs. cond_prob (ecc_bsc_prob_space n m p)
                     (event_received_string_takes_value enc n m ds)
                     (event_input_string_takes_value n m bs) *
           prob (ecc_bsc_prob_space n m p)
                (event_input_string_takes_value n m bs);
      map_decoder_bit_prob =
      λi b.
        ∑ map_decoder_bitstring_prob_bayes {bs | LENGTH bs = n ∧ EL i bs = b};
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
  >> assume_tac event_input_string_takes_value_is_event
  >> assume_tac event_input_string_takes_value_nonzero_prob
  >> assume_tac event_received_string_takes_value_is_event
  >> assume_tac event_received_string_takes_value_nonzero_prob
  >> assume_tac event_input_string_and_received_string_take_values_is_event
  >> assume_tac event_input_string_and_received_string_take_values_nonzero_prob
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
              (event_received_string_takes_value enc n (LENGTH ds) ds)’
  >> gvs[PROB_FINITE]
  >> REVERSE conj_tac >- gvs[lt_le, PROB_POSITIVE]
  (* Simplify *)
  >> gvs[FUN_EQ_THM]
  >> rw[]
  (* The function in the first sum can be simplified by cancelling the
     division with the multiplication, but we need to know that the input
     is in length_n_codes n. *)
  >> qmatch_goalsub_abbrev_tac ‘∑ f S = _ * _’
  >> sg ‘∀bs.
           bs ∈ S ⇒
           f bs =
           prob (ecc_bsc_prob_space n (LENGTH ds) p)
                ((event_received_string_takes_value enc n (LENGTH ds) ds)
                 ∩ event_input_string_takes_value n (LENGTH ds) bs)
        ’
  >- (rw[Abbr ‘f’]
      >> gvs[Abbr ‘S’, prob_div_mul_refl])
  >> sg ‘FINITE S’
  >- gvs[Abbr ‘S’, length_n_codes_single_input_takes_value_intersection]
  >> qspecl_then
     [‘f’,
      ‘λbs. prob (ecc_bsc_prob_space n (LENGTH ds) p)
                 ((event_received_string_takes_value enc n (LENGTH ds) ds)
                  ∩ event_input_string_takes_value n (LENGTH ds) bs)’,
      ‘S’] assume_tac EXTREAL_SUM_IMAGE_EQ'
  >> gvs[]
  (* Remove assumptions about f because we no longer have it since we have
     replaced it with its simplified version *)
  >> qpat_x_assum ‘∑ f S = _’ kall_tac
  >> qpat_x_assum ‘∀xs. xs ∈ S ⇒ f _ = _’ kall_tac
  >> qpat_x_assum ‘Abbrev (f = _)’ kall_tac
  (* Rewrite the goal in a form which makes it easier to see what's going on.
     In particular, we have a multiplication and division by a constant. *)
  >> qmatch_goalsub_abbrev_tac ‘LHS = c * ∑ (λbs. g1 (g2 bs ∩ g3) / c) S’
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

Theorem in_lambda_conj:
  ∀P Q s.
    (s ∈ (λx. P x) ∧ s ∈ (λx. Q x)) ⇔ s ∈ (λx. P x ∧ Q x)
Proof
  rw[]
QED

(* -------------------------------------------------------------------------- *)
(* If we are summing a function over a set, and the function returns one for  *)
(* every element in the set, then the sum of the function over the set is     *)
(* simply the cardinality of the set                                          *)
(* -------------------------------------------------------------------------- *)
Theorem EXTREAL_SUM_IMAGE_FUN_EQ_ONE:
  ∀f S.
    FINITE S ∧
    (∀x. x ∈ S ⇒ f x = 1) ⇒
    ∑ f S = &CARD S : extreal
Proof
  rw[]
  >> drule_then assume_tac EXTREAL_SUM_IMAGE_EQ_CARD
  >> pop_assum (fn th => PURE_REWRITE_TAC[GSYM th])
  >> irule EXTREAL_SUM_IMAGE_EQ'
  >> rw[]
QED

(* -------------------------------------------------------------------------- *)
(* An expression for the probability in the main probability space we are     *)
(* using for the special case where the output length is 0.                   *)
(* -------------------------------------------------------------------------- *)
Theorem prob_ecc_bsc_prob_space_empty_output:
  ∀n p S.
    0 ≤ p ∧ p ≤ 1 ∧
    S ∈ events (ecc_bsc_prob_space n 0 p) ⇒
    prob (ecc_bsc_prob_space n 0 p) S =
    (1 / 2 pow n) * &CARD S
Proof
  rw[]
  (* Use the expression we have for the probability in our prob space *)
  >> gvs[prob_ecc_bsc_prob_space]
  (* Our set is finite because it is a valid event of our finite prob space *)
  >> ‘FINITE S’ by metis_tac[event_ecc_bsc_prob_space_finite]
  (* Since our function always takes the value  on S, we can simplify the sum *)
  >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_FUN_EQ_ONE]
  >> rw[]
  (* Break down the expression stating that S is an event so that we can use
     it to give us information about the elements of S, such as x *)
  >> gvs[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
  (* Use this information to arrive at our goal*)
  >> first_x_assum $ drule_then assume_tac
  >> gvs[sym_noise_mass_func_def]
QED

(* -------------------------------------------------------------------------- *)
(* An expression for the received string taking a value in the special case   *)
(* where the output length is 0.                                              *)
(* -------------------------------------------------------------------------- *)
Theorem event_received_string_takes_value_empty_output:
  ∀enc n.
    (∀xs. LENGTH xs = n ⇒ enc xs = []) ⇒
    event_received_string_takes_value enc n 0 [] =
    {(bs, []) | LENGTH bs = n}
Proof
  rw[event_received_string_takes_value_def]
  >> rw[EXTENSION]
  >> EQ_TAC >> rw[]
QED

(* -------------------------------------------------------------------------- *)
(* An expression for the event of the input string taking a value in the      *)
(* special case where the output length is 0                                  *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_string_takes_value_empty_output:
  ∀n bs.
    LENGTH bs = n ⇒
    event_input_string_takes_value n 0 bs = {(bs, [])}
Proof
  rw[event_input_string_takes_value_def]
  >> rw[EXTENSION]
QED


Theorem event_sent_string_takes_value_empty_output:
  ∀enc n.
    (∀xs. LENGTH xs = n ⇒ enc xs = []) ⇒
    event_sent_string_takes_value enc n 0 [] = {(bs, []) | bs | LENGTH bs = n}
Proof
  rw[]
  >> gvs[event_sent_string_takes_value_def]
  >> rw[EXTENSION]
  >> EQ_TAC >> rw[]
QED

(* -------------------------------------------------------------------------- *)
(* Since the noise applied to each bit is independent, the joint probability  *)
(* of receiving a string and the input taking a value is equal to the product *)
(* of probabilities of each individual bit being received and the input       *)
(* taking that value.                                                         *)
(* -------------------------------------------------------------------------- *)
(* I no longer think that this theorem is true, because the probability of    *)
(* the input string taking a value is being accounted for multiple times.     *)
(* -------------------------------------------------------------------------- *)
(*
Theorem joint_prob_string_and_input_prod:
  ∀enc n m p bs ds.
    0 ≤ p ∧ p ≤ 1 ∧
    LENGTH bs = n ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    prob (ecc_bsc_prob_space n m p)
         ((event_received_string_takes_value enc n m ds)
          ∩ (event_input_string_takes_value n m bs)) =
    ∏ (λi. prob (ecc_bsc_prob_space n m p)
                ((event_received_bit_takes_value enc n m i (EL i ds))
                 ∩ (event_input_string_takes_value n m bs)))
      (count m)
Proof
  rw[]
  >> Induct_on ‘LENGTH ds’
  >- (rw[]
      >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_empty_output]
      >> rw[]
      >- (irule EVENTS_INTER
          >> gvs[ecc_bsc_prob_space_is_prob_space,
                 event_received_string_takes_value_is_event,
                 event_input_string_takes_value_is_event]
         )
      >> gvs[event_received_string_takes_value_empty_output]
      >> gvs[event_input_string_takes_value_empty_output]
      >> gvs[INTER_DEF]
      >> qmatch_goalsub_abbrev_tac ‘CARD S’
      >> sg ‘S = {(bs,[])}’
      >- (rw[Abbr ‘S’, EXTENSION]
          >> EQ_TAC >> gvs[]
         )
      >> gvs[]
QED
 *)

(* -------------------------------------------------------------------------- *)
(* Since the noise applied to each bit is independent, the conditional        *)
(* probability of the received string taking a value is equal to the product  *)
(* of the conditional probabilities of each individual bit                    *)
(* -------------------------------------------------------------------------- *)
(* I think I'll use a different approach to prove what I need to prove        *)
(*
Theorem cond_prob_string_given_input_prod_num:
  ∀enc n m p bs ds.
    0 ≤ p ∧ p ≤ 1 ∧
    LENGTH bs = n ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    cond_prob (ecc_bsc_prob_space n m p)
              (event_received_string_takes_value enc n m ds)
              (event_input_string_takes_value n m bs) =
    ∏ (λi. cond_prob (ecc_bsc_prob_space n m p)
                     (event_received_bit_takes_value enc n m i (EL i ds))
                     (event_input_string_takes_value n m bs)
      ) (count m)
Proof
  Induct_on ‘m’
  >- (rw[]
      >> gvs[event_received_string_takes_value_empty_output,
             event_input_string_takes_value_empty_output]
      >> gvs[cond_prob_def]
      >> gvs[INTER_SING]
      >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_empty_output]
      >> rw[]
      >- gvs[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
      >> irule div_refl
      >> rw[]
      >- (‘(1 / 2) pow LENGTH bs ≠ −∞’ suffices_by gvs[pow_div]
          >> gvs[pow_not_infty]
         )
      >- (‘(1 / 2) pow LENGTH bs ≠ +∞’ suffices_by gvs[pow_div]
          >> gvs[pow_not_infty]
         )
      >> ‘(1 / 2) pow LENGTH bs ≠ 0’ suffices_by gvs[pow_div]
      >> irule (GCONTRAPOS pow_zero_imp)
      >> gvs[extreal_of_num_def]
      >> gvs[extreal_div_eq]
     )
  >> rw[]
  >> 
QED
*)

(* -------------------------------------------------------------------------- *)
(* If we have an encoding method which is injective, then the input string    *)
(* takes a certain value if and only if the sent string takes the value of    *)
(* the encoding of the input string                                           *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_string_takes_value_event_sent_string_takes_value:
  ∀(enc : bool list -> bool list) n m bs.
    (∀xs ys. enc xs = enc ys ⇒ xs = ys) ⇒
    event_input_string_takes_value n m bs =
    event_sent_string_takes_value enc n m (enc bs)
Proof
  rw[]
  >> gvs[event_input_string_takes_value_def,
         event_sent_string_takes_value_def]
  >> rw[EXTENSION]
  >> EQ_TAC >> rw[]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* Split the event of receiving a particular string given that the input      *)
(* string takes a particular value into the product of the probabilities      *)
(* that each individual bit is received given that the corresponding bit in   *)
(* the encoded version of the input is sent.                                  *)
(* -------------------------------------------------------------------------- *)
Theorem cond_prob_string_given_input_prod:
  ∀enc n m p bs ds.
    0 < p ∧ p < 1 ∧
    LENGTH bs = n ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ∧
    (∀xs ys. enc xs = enc ys ⇒ xs = ys) ⇒
    cond_prob (ecc_bsc_prob_space n m p)
              (event_received_string_takes_value enc n m ds)
              (event_input_string_takes_value n m bs) =
    let
      cs = enc bs
    in
      ∏ (λi. (if EL i ds = EL i cs then 1 - p else p))
        (count m)
Proof
  rpt strip_tac
  (* More common representation of probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* First, use the event that the sent string takes a particular value
     rather than that the input string takes a particular value. *)
  >> drule_then (fn th => PURE_REWRITE_TAC[th])
                event_input_string_takes_value_event_sent_string_takes_value
  (* It would be nice if we knew that the values of the individual bits were
     conditionally independent with respect to the event that the input string
     takes a particular value. Then, since the received string is the
     intersection of the individual bits, we would have made progress towards
     our result. However, in order to prove conditional independence, we must
     exactly prove the result that we want from conditional independence, so
     it's not really very helpful.
.
     Instead, we work by induction on the length of the encoded string. *)
  >> qpat_x_assum ‘LENGTH xs = m’ mp_tac
  >> SPEC_ALL_TAC (* We want xs to be quantified over in our induction,
                     because its length changes as m changes and we are
                     inducting over m. *)
  >> Induct_on ‘m’
  (* The base case relies on lemmas about what these functions reutrn in
     the case of a zero length output *)
  >- (rw[]
      >> gvs[event_received_string_takes_value_empty_output]
      >> gvs[event_sent_string_takes_value_empty_output]
      >> irule COND_PROB_ITSELF
      >> gvs[ecc_bsc_prob_space_is_prob_space]
      >> rw[]
      >- (DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
          >> gvs[]
          >> rw[]
          >- (rw[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
              >> (gvs[]))
          >> rw[EXTENSION]
          >> qexists ‘bs’ >> gvs[]
         )
      >> rw[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
      >> (gvs[])
     )
  (* Inductive step. We want to drag out the suc on the left hand side.
     This will hopefully give us an additional product term, and then we can
     
   *)
  >> rw[]
QED

(* -------------------------------------------------------------------------- *)
(* Split up the probability of receiving a string given the initial input     *)
(* into a product of each individual bit being received correctly given the   *)
(* information that was sent.                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_sum_bayes_prod:
  ∀enc n m p ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      (TODO: Where's the prod)
      
      map_decoder_bitstring_prob_bayes =
      λbs. cond_prob (ecc_bsc_prob_space n m p)
                     (event_received_string_takes_value enc n m ds)
                     (event_input_string_takes_value n m bs) *
           prob (ecc_bsc_prob_space n m p)
                (event_input_string_takes_value n m bs);
      map_decoder_bit_prob =
      λi b.
        ∑ map_decoder_bitstring_prob_bayes {bs | LENGTH bs = n ∧ EL i bs = b};
    in
      (MAP (λi. argmax_bool (map_decoder_bit_prob i)) (COUNT_LIST n))
Proof
QED



val _ = export_theory();
