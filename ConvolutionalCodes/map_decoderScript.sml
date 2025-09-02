(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "map_decoder";

(* My theories *)
open ecc_prob_spaceTheory;
open argmin_extrealTheory;

(* My libraries *)
open donotexpandLib;
open useful_tacticsLib;

(* Standard theories *)
open arithmeticTheory;
open bitstringTheory;
open pairTheory;
open pred_setTheory;
open probabilityTheory;
open extrealTheory;
open realTheory;
open rich_listTheory;
open sigma_algebraTheory;
open lebesgueTheory;
open listTheory;
open martingaleTheory;
open measureTheory;
open topologyTheory;

(* Standard libraries *)
open realLib;
open dep_rewrite;
open ConseqConv;

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
(* As of writing this, the most simplified version of the MAP decoder for     *)
(* binary symmetric channels and arbitrary codes is given by                  *)
(* map_decoder_bitwise_simp2.                                                 *)
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
(* regardless TODO: sentence is incomplete. What did I mean?                  *)
(*                                                                            *)
(* This implementation breaks ties by assuming a bit has the value T in the   *)
(* case of a tie.                                                             *)
(*                                                                            *)
(* enc: the encoding function                                                 *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* p: the probability of bit error in our binary symmetric channel            *)
(* ds: the string that we wish to decode                                      *)
(*                                                                            *)
(* Output: the decoded bitstring                                              *)
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
(* A maximum a posteriori decoder which calculates the most likely sent       *)
(* codeword in a bitwise manner. Ties are broken by assuming the bit is T.    *)
(*                                                                            *)
(* This was introduced due to a misunderstanding of the MAP decoder for       *)
(* convolutional codes. I no longer think this is necessary.                  *)
(*                                                                            *)
(* enc: the encoding function                                                 *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* p: the probability of bit error in our binary symmetric channel            *)
(* ds: the string that we wish to decode                                      *)
(* -------------------------------------------------------------------------- *)
Definition map_decoder_bitwise_sent_def:
  map_decoder_bitwise_sent enc n m p ds =
  let
    map_decoder_sent_bit_prob =
    λi c. cond_prob (ecc_bsc_prob_space n m p)
                    (event_sent_bit_takes_value enc n m i c)
                    (event_received_string_takes_value enc n m ds);
  in
    MAP (λi. argmax_bool (map_decoder_sent_bit_prob i)) (COUNT_LIST m)
End

(* -------------------------------------------------------------------------- *)
(* Returns the probability that the input string takes a particular value     *)
(* given that the received string takes a particular value.                   *)
(*                                                                            *)
(* enc: the encoding function                                                 *)
(* n: the input length                                                        *)
(* m: the output length                                                       *)
(* p: the probability of error                                                *)
(* bs: the input string                                                       *)
(* ds: the received string                                                    *)
(*                                                                            *)
(* Output: extreal representing the probability of the input string being     *)
(* sent given that the received string was received.                          *)
(* -------------------------------------------------------------------------- *)
Definition prob_input_string_given_received_string_def:
  prob_input_string_given_received_string enc n m p bs ds =
  cond_prob (ecc_bsc_prob_space n m p)
            (event_input_string_takes_value n m bs)
            (event_received_string_takes_value enc n m ds)
End

(* -------------------------------------------------------------------------- *)
(* Returns true if the given output bitstring is an optimal blockwise MAP     *)
(* decoding of the given input bitstring, with respect to the binary          *)
(* binary symmetric channel of probability p.                                 *)
(*                                                                            *)
(* We do this instead of defining a function which returns the optimal        *)
(* decoding because there may be multiple bitstrings which are all optimal.   *)
(*                                                                            *)
(* enc: the encoder we are using                                              *)
(* n: the input length                                                        *)
(* m: the output length                                                       *)
(* p: the probability of an error in our binary symmetric channel.            *)
(* bs: the decoded string (bs is unencoded, cs is encoded, ds has noise)      *)
(* ds: the string to decode (encoded, and with noise added)                   *)
(* -------------------------------------------------------------------------- *)
Definition is_optimal_blockwise_map_decoding_def:
  is_optimal_blockwise_map_decoding enc n m p bs ds =
  (∀bs2.
     LENGTH bs2 = n ⇒
     prob_input_string_given_received_string enc n m p bs2 ds ≤
     prob_input_string_given_received_string enc n m p bs ds
  )
End

Overload ith_eq_codes = “λi b. {bs : bool list | EL i bs = b}”;

Overload valid_inverse_codes = “λenc n.
                                  {cs | (∃bs. LENGTH bs = n ∧ enc bs = cs)}”;

(* -------------------------------------------------------------------------- *)
(* Fixing the input string and the received string will also fix the          *)
(* event we are in to a single possibility.                                   *)
(* -------------------------------------------------------------------------- *)
Theorem input_string_takes_value_inter_received_string_takes_value:
  ∀enc n m bs ds.
    LENGTH bs = n ∧
    LENGTH ds = m ∧
    (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
    (event_input_string_takes_value n m bs)
    ∩ event_received_string_takes_value enc n m ds = {(bs, bxor (enc bs) ds)}
Proof
  rw[EXTENSION, event_input_string_takes_value_def,
     event_received_string_takes_value_def]  
  >> EQ_TAC >> rw[bxor_length]
  >> (gvs[bxor_inv])
QED

(* -------------------------------------------------------------------------- *)
(* This expression is more nicely written as an intersection                  *)
(* -------------------------------------------------------------------------- *)
Theorem length_n_codes_ith_eq_codes:
  ∀n i b.
    {bs | LENGTH bs = n ∧ (EL i bs = b)} = (length_n_codes n ∩ ith_eq_codes i b)
Proof
  rw[]
  >> ASM_SET_TAC[]
QED

Theorem finite_el_i_is_b[simp]:
  ∀n i b.
    FINITE {bs | LENGTH bs = n ∧ (EL i bs ⇔ b)}
Proof
  gvs[length_n_codes_ith_eq_codes]
QED

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

Theorem le_div_alt:
  ∀y z : extreal.
    0 ≤ y ∧ 0 < z ∧ z ≠ +∞ ⇒ 0 ≤ y / z
Proof
  Cases_on ‘z’ >> rw[le_div]
QED

(* -------------------------------------------------------------------------- *)
(* A theorem for finding an explicit formula for the symmetric noise mass     *)
(*  function applied to the bitwise difference of two bitstrings              *)
(* -------------------------------------------------------------------------- *)
Theorem sym_noise_mass_func_bxor:
  ∀bs1 bs2 p.
    LENGTH bs1 = LENGTH bs2 ⇒
    sym_noise_mass_func p (bxor bs1 bs2) =
    p pow (hamming_distance bs1 bs2) *
    (1 - p) pow (LENGTH bs1 - hamming_distance bs1 bs2)
Proof
  Induct_on ‘bs1’ >> rw[sym_noise_mass_func_def]
  >> Cases_on ‘bs2’ >> gvs[sym_noise_mass_func_def]
  >> rw[]
  (* In the case where we have added a factor of p, we move the new factor
     into the power and simplify *)
  >- (gvs[mul_assoc]
      >> gvs[GSYM (cj 2 extreal_pow)]
      >> gvs[ADD1]
     )
  (* In the case where we have added a factor of 1 - p, we also move the new
     factor into the corresponding power and simplify *)
  >> PURE_ONCE_REWRITE_TAC[mul_comm]
  >> gvs[GSYM mul_assoc]
  >> gvs[mul_comm]
  >> gvs[GSYM (cj 2 extreal_pow)]
  >> gvs[ADD1]
  >> gvs[SUB_RIGHT_ADD]
  >> rw[]
  (* We now have obtained the contradiction LENGTH t ≤ hamming_distance bs1 t.
     Strengthen to LENGTH t < hamming_distance bs1 t*)
  >> Cases_on ‘hamming_distance bs1 t = LENGTH t’ >> rw[]
  >> sg ‘LENGTH t < hamming_distance bs1 t’ >> gvs[le_lt]
  (* Introduce the thing it contradicts with: hamming_distance bs1 t ≤ LENGTH t*)
  >> qspecl_then [‘bs1’, ‘t’] assume_tac hamming_distance_length
  (* It automatically solves from this point*)
  >> gvs[] 
QED

Theorem pow_leq_plus_imp[simp]:
  ∀a p x.
    1 ≤ a ⇒
    a pow x ≤ a pow (p + x)
Proof
  rw[]
  >> Induct_on ‘p’ >> gvs[]
  >> gvs[ADD1]
  >> PURE_REWRITE_TAC[ADD_ASSOC]
  >> PURE_ONCE_REWRITE_TAC[pow_add]
  >> gvs[]
  >> metis_tac[mul_rone, le_mul2, pow_pos_le, le_01, le_trans]
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
Theorem event_input_bit_takes_value_is_event[simp]:
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
Theorem event_input_string_takes_value_is_event[simp]:
  ∀n m bs p.
    event_input_string_takes_value n m bs ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[event_input_string_takes_value_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* event_sent_string_takes_value is a valid event in the probability space it *)
(* is designed for                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem event_sent_string_takes_value_is_event[simp]:
  ∀enc n m cs p.
    event_sent_string_takes_value enc n m cs ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[event_sent_string_takes_value_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* event_received_string_takes_value is a valid event in the probability      *)
(* space it is designed for                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem event_received_string_takes_value_is_event[simp]:
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
Theorem event_input_bit_takes_value_nonzero_prob[simp]:
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
Theorem event_input_string_takes_value_nonzero_prob[simp]:
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
(* event_sent_string_takes_value has a nonzero probability, assuming that     *)
(* there is a potential input string which could result in the sent string.   *)
(*                                                                            *)
(* See also event_sent_string_takes_value_nonzero_prob_explicit, which is     *)
(* easier to use as a rewrite rule. By contrast, this theorem is easier to    *)
(* use with irule or DEP_PURE_ONCE_REWRITE_TAC.                               *)
(* -------------------------------------------------------------------------- *)
Theorem event_sent_string_takes_value_nonzero_prob:
  ∀enc n m cs p.
    0 < p ∧
    p < 1 ∧
    LENGTH cs = m ∧
    (∃bs. LENGTH bs = n ∧ enc bs = cs) ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_sent_string_takes_value enc n m cs) ≠ 0
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> gvs[event_sent_string_takes_value_is_event]
  >> gvs[EXTENSION] >> rw[event_sent_string_takes_value_def]
  >> qexists ‘bs’
  >> gvs[]   
  >> qexists ‘REPLICATE (LENGTH (enc bs)) F’
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* A version of event_sent_string_takes_value_nonzero_prob which explicitly   *)
(* requires our string cs to be of the form enc bs. This makes it easier to   *)
(* use it as a rewrite rule, because we don't rely on being able to solve a   *)
(* precondition involving an exists statement. However, it also makes it      *)
(* harder to use with irule or DEP_PURE_ONCE_REWRITE_TAC, because we require  *)
(* our statement to have the explicit form where cs is represented as enc bs. *)
(* -------------------------------------------------------------------------- *)
Theorem event_sent_string_takes_value_nonzero_prob_explicit[simp]:
  ∀enc n m p bs.
    0 < p ∧
    p < 1 ∧
    LENGTH bs = n ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_sent_string_takes_value enc n m (enc bs)) ≠ 0
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> gvs[]
  >> rw[EXTENSION, event_sent_string_takes_value_def]
  >> qexists ‘bs’ >> gvs[]
  >> metis_tac[LENGTH_REPLICATE]
QED

(* -------------------------------------------------------------------------- *)
(* If there is no string which could result in the sent string, then          *)
(* event_sent_string_takes_value has a probability of zero                    *)
(* -------------------------------------------------------------------------- *)
Theorem event_sent_string_takes_value_zero_prob[simp]:
  ∀enc n m cs p.
    0 ≤ p ∧
    p ≤ 1 ∧
    (∀bs. LENGTH bs = n ⇒ enc bs ≠ cs) ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_sent_string_takes_value enc n m cs) = 0
Proof
  rw[]
  >> qmatch_goalsub_abbrev_tac ‘prob sp S = 0’
  >> sg ‘S = ∅’ >> unabbrev_all_tac
  >- (gvs[event_sent_string_takes_value_def]
      >> rw[EXTENSION]
     )
  >> metis_tac[ecc_bsc_prob_space_is_prob_space,
               PROB_EMPTY]
QED

(* -------------------------------------------------------------------------- *)
(* event_received_string_takes_value has a nonzero probability                *)
(* -------------------------------------------------------------------------- *)
Theorem event_received_string_takes_value_nonzero_prob[simp]:
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

Theorem event_input_string_and_received_string_take_values_is_event[simp]:
  ∀enc n m bs ds p.
    ((event_input_string_takes_value n m bs)
     ∩ (event_received_string_takes_value enc n m ds))
    ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[event_received_string_takes_value_def, events_ecc_bsc_prob_space,
     POW_DEF, SUBSET_DEF]
  >> (gvs[])
QED

Theorem event_input_string_and_received_string_take_values_nonzero_prob[simp]:
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
  >> gvs[prob_ecc_bsc_prob_space_zero]
  >> gvs[EXTENSION] >> rw[]
  >> gvs[event_received_string_takes_value_def, event_input_string_takes_value_def]
  >> qexists ‘(bs, bxor (enc bs) ds)’
  >> gvs[bxor_length, bxor_inv]
QED

(* -------------------------------------------------------------------------- *)
(* The probability that the input is of a certain form                        *)
(* -------------------------------------------------------------------------- *)
Theorem prob_event_input_string_takes_value[simp]:
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
(* Express the event where an input bit takes a value in terms of the cross   *)
(* product of two events: one which says that the input bit takes a given     *)
(* value, and one which says that the noise is unrestricted by the choice     *)
(* of input bit                                                               *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_bit_takes_value_length_n_codes_ith_eq_codes:
  ∀n m i b.
    event_input_bit_takes_value n m i b =
    (length_n_codes n ∩ ith_eq_codes i b) × (length_n_codes m)
Proof
  rw[]
  >> gvs[event_input_bit_takes_value_def]
  >> gvs[CROSS_DEF]
  >> ASM_SET_TAC[]
QED

(* -------------------------------------------------------------------------- *)
(* If we consider the cross of two events in the cross of two probability     *)
(* spaces, then the probability is the product of the probabilities of the    *)
(* events.                                                                    *)
(* -------------------------------------------------------------------------- *)
Theorem prob_cross:
  ∀sp1 sp2 e1 e2.
    prob_space sp1 ∧
    prob_space sp2 ∧
    e1 ∈ events sp1 ∧
    e2 ∈ events sp2 ⇒
    prob (sp1 × sp2) (e1 × e2) = prob sp1 e1 * prob sp2 e2
Proof
  rw[]
  >> gvs[prob_def, prod_measure_space_def, prob_space_def, events_def]
  >> gvs[PROD_MEASURE_CROSS]
QED

(* -------------------------------------------------------------------------- *)
(* It is often useful to apply our probability space to the cross between two *)
(* events. This allows us to calculate the probability of each of the crossed *)
(* events separately, which may sometimes be simpler.                         *)
(* -------------------------------------------------------------------------- *)
Theorem prob_ecc_bsc_prob_space_cross:
  ∀n m p e1 e2.
    0 ≤ p ∧ p ≤ 1 ∧
    e1 ∈ POW (length_n_codes n) ∧
    e2 ∈ POW (length_n_codes m) ⇒
    prob (ecc_bsc_prob_space n m p) (e1 × e2) =
    prob (length_n_codes_uniform_prob_space n) e1 *
    prob (sym_noise_prob_space m p) e2
Proof
  rw[]
  >> gvs[ecc_bsc_prob_space_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_cross]
  >> conj_tac
  >- gvs[length_n_codes_uniform_prob_space_def,
         sym_noise_prob_space_def,
         events_def]
  >> gvs[]
QED

Theorem length_n_codes_ith_eq_codes_image:
  ∀n i b.
    i < n ⇒
    length_n_codes n ∩ ith_eq_codes i b =
    IMAGE (λbs. TAKE i bs ++ [b] ++ DROP i bs) (length_n_codes (n - 1))
Proof
  rw[]
  >> rw[EXTENSION]
  >> EQ_TAC >> gvs[]
  >- (rw[]
      >> qexists ‘TAKE i x ++ DROP (i+1) x’
      (* Maybe this kind of mechanical list working can be automated? *)
      >> REVERSE conj_tac
      >- gvs[LENGTH_TAKE]
      >> gvs[TAKE_APPEND]
      >> gvs[TAKE_TAKE]
      >> gvs[DROP_APPEND]
      >> gvs[DROP_TAKE]
      >> metis_tac[TAKE_DROP_SUC, ADD1]
     )
  >> rw[]
  >- gvs[LENGTH_APPEND]
  >> gvs[EL_APPEND]
QED

Theorem card_length_n_codes_ith_eq_codes[simp]:
  ∀n i b.
    i < n ⇒
    CARD (length_n_codes n ∩ ith_eq_codes i b) = 2 ** (n - 1)
Proof
  rw[]
  >> gvs[length_n_codes_ith_eq_codes_image]
  >> DEP_PURE_ONCE_REWRITE_TAC[INJ_CARD_IMAGE_EQ]
  >> DEP_PURE_ONCE_REWRITE_TAC[CARD_IMAGE_INJ]
  >> conj_tac
  >- (rw[]
      >> gvs[APPEND_LENGTH_EQ]
      >> metis_tac[TAKE_DROP]
     )
  >> gvs[]
QED

Theorem prob_length_n_codes_uniform_prob_space_ith_eq_codes[simp]:
  ∀n i b.
    i < n ⇒
    prob (length_n_codes_uniform_prob_space n)
         (length_n_codes n ∩ ith_eq_codes i b) = 1 / 2
Proof
  rw[]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_length_n_codes_uniform_prob_space]
  >> conj_tac
  >- gvs[POW_DEF]
  >> gvs[]
  >> gvs[extreal_of_num_exp]
  >> gvs[extreal_of_num_def]
  >> gvs[extreal_div_eq, extreal_mul_eq, extreal_pow_def]
  >> gvs[REAL_POW]
  >> gvs[GSYM EXP]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: move this to ecc_prob_spaceScript, along with the relevant things it *)
(* relies on                                                                  *)
(* -------------------------------------------------------------------------- *)
Theorem prob_event_input_bit_takes_value[simp]:
  ∀n m p i b.
    0 ≤ p ∧ p ≤ 1 ∧
    i < n ⇒
    prob (ecc_bsc_prob_space n m p) (event_input_bit_takes_value n m i b) =
    1 / 2
Proof
  rw[]
  >> gvs[event_input_bit_takes_value_length_n_codes_ith_eq_codes]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_cross]
  >> conj_tac
  >- gvs[POW_DEF]
  >> gvs[]
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
  >> gvs[MEM_COUNT_LIST, Excl "prob_event_input_bit_takes_value"]
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

Theorem event_input_string_takes_value_disjoint[simp]:
  ∀n m bs bs'.
    bs ≠ bs' ⇒
    DISJOINT (event_input_string_takes_value n m bs) (event_input_string_takes_value n m bs')
Proof
  rw[DISJOINT_DEF, event_input_string_takes_value_def, INTER_DEF, EXTENSION]
  >> Cases_on ‘x’ >> gvs[]
QED

Theorem event_sent_string_takes_value_disjoint[simp]:
  ∀enc n m cs cs'.
    cs ≠ cs' ⇒
    DISJOINT (event_sent_string_takes_value enc n m cs) (event_sent_string_takes_value enc n m cs')
Proof
  rw[DISJOINT_DEF, event_sent_string_takes_value_def, INTER_DEF, EXTENSION]
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
(* A version of event_input_string_takes_value_bigunion which works for the   *)
(* sent string rather than the input string.                                  *)
(* -------------------------------------------------------------------------- *)
Theorem event_sent_string_takes_value_bigunion:
  ∀enc n m i c.
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    event_sent_bit_takes_value enc n m i c =
    BIGUNION (IMAGE (event_sent_string_takes_value enc n m)
                    (length_n_codes m ∩ {cs | EL i cs ⇔ c}))
Proof
  rw[]
  >> gvs[BIGUNION_IMAGE]
  >> gvs[event_sent_bit_takes_value_def, event_sent_string_takes_value_def]
  >> rw[EXTENSION]
  >> EQ_TAC >> rw[]
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
  (*>- gvs[event_input_string_takes_value_disjoint]*)
  (* Now it suffices to prove that the events in the cond_prob are equivalent *)
  >> qmatch_goalsub_abbrev_tac ‘cond_prob sp e1 e3 = cond_prob sp e2 e3’
  >> ‘e1 = e2’ suffices_by gvs[]
  >> unabbrev_all_tac
  >> gvs[event_input_string_takes_value_bigunion]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* A version of cond_prob_event_input_string_takes_value_sum which works      *)
(* on the sent string rather than the input string                            *)
(* -------------------------------------------------------------------------- *)
Theorem cond_prob_event_sent_string_takes_value_sum:
  ∀enc n m p i c ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ⇒
    cond_prob
    (ecc_bsc_prob_space n m p)
    (event_sent_bit_takes_value enc n m i c)
    (event_received_string_takes_value enc n m ds) =
    ∑ (λcs.
         cond_prob (ecc_bsc_prob_space n m p)
                   (event_sent_string_takes_value enc n m cs)
                   (event_received_string_takes_value enc n m ds)
      )
      {cs | LENGTH cs = m ∧ (EL i cs = c)}
Proof
  rw[]
  (* More common representation of probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* Rewrite the set we are summing over in terms of an intersection with
     length_n_codes *)
  >> gvs[length_n_codes_single_input_takes_value_intersection]
  (* Bring the sum into the cond_prob, turning it into a union *)
  >> DEP_PURE_REWRITE_TAC[GSYM cond_prob_additive_finite]
  (* Satisfy all the necessary requirements *)
  >> gvs[ecc_bsc_prob_space_is_prob_space,
         event_received_string_takes_value_is_event,
         event_sent_string_takes_value_is_event,
         event_sent_string_takes_value_disjoint,
         event_received_string_takes_value_nonzero_prob]
  (* Now it suffices to prove that the events in the cond_prob are equivalent *)
  >> qmatch_goalsub_abbrev_tac ‘cond_prob sp e1 e3 = cond_prob sp e2 e3’
  >> ‘e1 = e2’ suffices_by gvs[]
  >> unabbrev_all_tac
  >> gvs[event_sent_string_takes_value_bigunion]
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
      map_decoder_bitstring_prob =
      λbs. cond_prob (ecc_bsc_prob_space n m p)
                     (event_received_string_takes_value enc n m ds)
                     (event_input_string_takes_value n m bs) *
           prob (ecc_bsc_prob_space n m p)
                (event_input_string_takes_value n m bs);
      map_decoder_bit_prob =
      λi b.
        ∑ map_decoder_bitstring_prob {bs | LENGTH bs = n ∧ EL i bs = b};
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
      >> qpat_x_assum ‘_ = Normal r’ (fn th => PURE_REWRITE_TAC[GSYM th])
      >> gvs[]
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
Theorem prob_ecc_bsc_prob_space_empty_output[simp]:
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
Theorem event_received_string_takes_value_empty_output[simp]:
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
Theorem event_input_string_takes_value_empty_output[simp]:
  ∀n bs.
    LENGTH bs = n ⇒
    event_input_string_takes_value n 0 bs = {(bs, [])}
Proof
  rw[event_input_string_takes_value_def]
  >> rw[EXTENSION]
QED

Theorem event_sent_string_takes_value_empty_output[simp]:
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
  ∀enc n m bs.
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

Theorem lt_posinf_neq_posinf[simp]:
  ∀a.
    a < +∞ ⇔ a ≠ +∞
Proof
  Cases_on ‘a’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* An alternate version of lt_div which allows the denominator to be an       *)
(* arbitrary extreal, as long as it satisfies appropriate conditions          *)
(* -------------------------------------------------------------------------- *)
Theorem lt_div_alt:
  ∀y z.
    0 < y ∧ 0 < z ∧ z ≠ +∞ ⇒ 0 < y / z
Proof
  Cases_on ‘z’ >> gvs[lt_div]
QED

(* -------------------------------------------------------------------------- *)
(* An alternate version of lt_div which allows the denominator to be an       *)
(* arbitrary extreal, as long as it satisfies appropriate conditions.         *)
(* -------------------------------------------------------------------------- *)
Theorem div_not_infty_if_not_infty_alt:
  ∀x y.
    (x ≠ +∞ ∧ 0 < y ∧ y ≠ +∞ ⇒ x / y ≠ +∞) ∧
    (x ≠ −∞ ∧ 0 < y ∧ y ≠ +∞ ⇒ x / y ≠ −∞) ∧
    (x ≠ +∞ ∧ y < 0 ∧ y ≠ −∞ ⇒ x / y ≠ −∞) ∧
    (x ≠ −∞ ∧ y < 0 ∧ y ≠ −∞ ⇒ x / y ≠ +∞)
Proof
  Cases_on ‘x’ >> Cases_on ‘y’ >> gvs[div_not_infty_if_not_infty]
QED

(* -------------------------------------------------------------------------- *)
(* I think that it's better to have the preconditions x ≠ +∞ and x ≠ −∞ than  *)
(* to require that the extreal has the form Normal r, because then I can use  *)
(* it in situations where I have an arbitrary extreal in that position,       *)
(* rather than having to have a Normal r in that position                     *)
(* -------------------------------------------------------------------------- *)
Theorem EXTREAL_SUM_IMAGE_CMUL_ALT:
  ∀s f c.
    FINITE s ∧
    c ≠ +∞ ∧
    c ≠ −∞ ∧
    ((∀x. x ∈ s ⇒ f x ≠ −∞) ∨ (∀x. x ∈ s ⇒ f x ≠ +∞)) ⇒
    ∑ (λx. c * f x) s = c * ∑ f s
Proof
  rw[] >> Cases_on ‘c’ >> gvs[EXTREAL_SUM_IMAGE_CMUL]
QED

(* -------------------------------------------------------------------------- *)
(* See comment above EXTREAL_SUM_IMAGE_CMUL_ALT                               *)
(* -------------------------------------------------------------------------- *)
Theorem div_mul_refl_alt:
  ∀a b : extreal.
    b ≠ 0 ∧
    b ≠ +∞ ∧
    b ≠ −∞ ⇒
    a / b * b = a
Proof
  rw[] >> Cases_on ‘b’ >> gvs[div_mul_refl]
QED

(* -------------------------------------------------------------------------- *)
(* Similar to EXTREAL_SUM_IMAGE_CMUL_ALT, it is better to have the            *)
(* precondition n ≠ 0 than to require n to have the form SUC n, because then  *)
(* I can match the theorem to an arbitrary expression, rather than only being *)
(* able to match the theorem to an expression containing SUC n.               *)
(*                                                                            *)
(* Of course, the other definition has the advantage of more easily being     *)
(* usable as a rewrite rule, since it has no preconditions.                   *)
(* -------------------------------------------------------------------------- *)
Theorem pow_zero_alt:
  ∀n x.
    n ≠ 0 ⇒
    (x pow n = 0 ⇔ x = 0)
Proof
  Cases_on ‘n’ >> gvs[pow_zero]
QED

(* -------------------------------------------------------------------------- *)
(* Simplify the conditional probability of receiving a particular string      *)
(* given that the input string takes a particular value into the probability  *)
(* of the corresponding noise being the noise which was added to the string   *)
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
    sym_noise_mass_func p (bxor (enc bs) ds)
Proof
  rpt strip_tac
  (* More common representation of probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* Rewrite using the definition of conditional probabilities *)
  >> gvs[cond_prob_def]
  (* The probability of the denominator has a simple expression *)
  >> gvs[prob_event_input_string_takes_value]
  (* For the top event, it is more convenient to use the event that the sent
     string takes a particular value than the event that the input string takes
     a particular value *)
  >> drule_then (fn th => PURE_REWRITE_TAC[th])
                event_input_string_takes_value_event_sent_string_takes_value
  (* Give nice names to the probability space and event*)
  >> qmatch_abbrev_tac ‘prob sp e / _ = _’
  (* There is only one element in the event in the numerator, because we
     require a specific sent string, which fixes the input bitstring, and we
     require a specific received string, which fixes the noise. *)
  >> sg ‘e = {(bs, bxor (enc bs) ds)}’
  >- (unabbrev_all_tac
      >> gvs[event_received_string_takes_value_def,
             event_sent_string_takes_value_def,
             INTER_DEF]
      >> rw[EXTENSION]
      >> EQ_TAC >> (rw[] >> (gvs[bxor_inv] >> gvs[bxor_length]))
     )
  >> qpat_x_assum ‘Abbrev (e1 = _ ∩ _)’ kall_tac
  >> gvs[Abbr ‘sp’]
  (* Use the expression for a probability in our probability space *)
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space]
  >> rw[]
  >- gvs[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF, bxor_length]
  (* Move the division to the RHS *)
  >> DEP_PURE_ONCE_REWRITE_TAC[ldiv_eq]
  >> rw[]
  >- (irule lt_div_alt
      >> rw[pow_not_infty]
      >> gvs[pow_pos_lt]
     )
  >- (gvs[lt_posinf_neq_posinf]
      >> irule (cj 1 div_not_infty_if_not_infty_alt)
      >> gvs[pow_not_infty]
      >> gvs[pow_pos_lt]
     )
  (* Finish off the proof *)
  >> gvs[mul_comm]
QED

(* -------------------------------------------------------------------------- *)
(* A version of cond_prob_string_given_input_prod, calculated relative to the *)
(* sent string taking a particular value rather than the input string taking  *)
(* a particular value. It may be possible to remove the assumption that the   *)
(* encoder is injective.                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem cond_prob_string_given_sent_prod:
  ∀enc n m p cs ds.
    0 < p ∧ p < 1 ∧
    LENGTH cs = m ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ∧
    (∃bs. LENGTH bs = n ∧ enc bs = cs) ∧
    (∀xs ys. enc xs = enc ys ⇒ xs = ys) ⇒
    cond_prob (ecc_bsc_prob_space n m p)
              (event_received_string_takes_value enc n m ds)
              (event_sent_string_takes_value enc n m cs) =
    sym_noise_mass_func p (bxor cs ds)
Proof
  rw[]
  >> gvs[GSYM event_input_string_takes_value_event_sent_string_takes_value]
  >> metis_tac[cond_prob_string_given_input_prod]
QED

(* -------------------------------------------------------------------------- *)
(* Simplify the conditional probability from map_decoder_bitwise_sum_bayes,   *)
(* providing an explicit expression for it.                                   *)
(*                                                                            *)
(* Note that sym_noise_mass_func can be interpreted as a product of           *)
(* probabilities, so we have an expression that is nearly suitable for use in *)
(* a factor graph.                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_sum_bayes_prod:
  ∀enc n m p ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ∧
    (∀xs ys. enc xs = enc ys ⇒ xs = ys) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      map_decoder_bitstring_prob =
      λbs. (sym_noise_mass_func p (bxor (enc bs) ds)) *
           prob (ecc_bsc_prob_space n m p)
                (event_input_string_takes_value n m bs);
      map_decoder_bit_prob =
      λi b.
        ∑ map_decoder_bitstring_prob {bs | LENGTH bs = n ∧ EL i bs = b};
    in
      (MAP (λi. argmax_bool (map_decoder_bit_prob i)) (COUNT_LIST n))
Proof
  rw[]
  >> gvs[map_decoder_bitwise_sum_bayes]
  (* The inner bit is the bit we need to prove equivalence of. We only need
     to prove equivalence for valid i, that is, i < n *)
  >> gvs[MAP_EQ_f]        
  >> rw[]
  (* In this case, the thing we are taking the argmax_bool over is exactly
     equivalent *)
  >> qmatch_goalsub_abbrev_tac ‘argmax_bool f ⇔ argmax_bool g’
  >> ‘f = g’ suffices_by gvs[]
  >> gvs[Abbr ‘f’, Abbr ‘g’]
  >> rw[FUN_EQ_THM]
  (* Simplify the function we are summing over using
     cond_prob_string_given_input_prod *)
  >> irule EXTREAL_SUM_IMAGE_EQ'
  >> gvs[cond_prob_string_given_input_prod]
QED

(* -------------------------------------------------------------------------- *)
(* Simplification of the probability of the string taking a particular value  *)
(* in map_decoder_bitwise_sum_bayes_prod                                      *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_simp1:
  ∀enc n m p ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ∧
    (∀xs ys. enc xs = enc ys ⇒ xs = ys) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      map_decoder_bitstring_prob =
      λbs. (sym_noise_mass_func p (bxor (enc bs) ds)) *
           (1 / 2 pow n);
      map_decoder_bit_prob =
      λi b.
        ∑ map_decoder_bitstring_prob {bs | LENGTH bs = n ∧ EL i bs = b};
    in
      (MAP (λi. argmax_bool (map_decoder_bit_prob i)) (COUNT_LIST n))
Proof
  rw[]
  >> gvs[map_decoder_bitwise_sum_bayes_prod]
  (* The inner bit is the bit we need to prove equivalence of. *)
  >> gvs[MAP_EQ_f]
  >> rw[]
  (* In this case, the thing we are taking the argmax_bool over is exactly
     equivalent *)
  >> AP_TERM_TAC
  >> rw[FUN_EQ_THM]
  (* The inner functions are equivalent *)
  >> irule EXTREAL_SUM_IMAGE_EQ'
  >> rw[]
  >> gvs[prob_event_input_string_takes_value, lt_le]
QED

(* -------------------------------------------------------------------------- *)
(* Simplification of the probability of the string taking a particular value  *)
(* in map_decoder_bitwise_sum_bayes_prod                                      *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_simp2:
  ∀enc n m p ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ∧
    (∀xs ys. enc xs = enc ys ⇒ xs = ys) ⇒
    map_decoder_bitwise enc n m p ds =
    let
      map_decoder_bitstring_prob =
      λbs. (sym_noise_mass_func p (bxor (enc bs) ds));
      map_decoder_bit_prob =
      λi b.
        ∑ map_decoder_bitstring_prob {bs | LENGTH bs = n ∧ EL i bs = b};
    in
      (MAP (λi. argmax_bool (map_decoder_bit_prob i)) (COUNT_LIST n))
Proof
  rw[]
  >> gvs[map_decoder_bitwise_simp1]
  (* More common assumption when dealing with probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* The inner bit is the bit we need to prove equivalence of. *)
  >> gvs[MAP_EQ_f]
  >> rw[]
  (* We need to prove that the functions we are taking the argmax over are
     multiples of each other *)
  >> irule argmax_bool_mul_const
  >> qexists ‘(2 pow n) : extreal’
  >> gvs[pow_not_infty]
  >> rw[FUN_EQ_THM, pow_pos_lt]
  (* Now we bring the multiple into the sum *)
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_CMUL_ALT]
  >> rw[pow_not_infty]
  (* We prove the precondition first*)
  >- (disj2_tac
      >> rw[]
      >> irule (cj 2 mul_not_infty2)
      >> rw[sym_noise_mass_func_not_neginf, sym_noise_mass_func_not_inf]
      >> (‘1 ≠ +∞ ∧ 0 < 2 pow LENGTH bs ∧ 2 pow LENGTH bs ≠ +∞’ suffices_by
            gvs[div_not_infty_if_not_infty_alt]
          >> gvs[pow_pos_lt, pow_not_infty]
         )
     )
  (* Cancel the multiplication and division *)
  >> PURE_ONCE_REWRITE_TAC[mul_comm]
  >> gvs[GSYM mul_assoc]
  >> DEP_PURE_ONCE_REWRITE_TAC[div_mul_refl_alt]
  >> gvs[pow_pos_lt, pow_not_infty]
  >> Cases_on ‘n = 0’ >> gvs[pow_zero_alt]
QED

Theorem real_sub_plus:
  ∀a b c : real.
    a - (b + c) = a - b - c
Proof
  rw[]
  >> gvs[real_sub, REAL_NEG_ADD, REAL_ADD_ASSOC]
QED

Theorem extreal_sub_plus:
  ∀a b c : extreal.
    (a = +∞ ⇒ b ≠ +∞ ∧ c ≠ +∞) ∧
    (a = −∞ ⇒ b ≠ −∞ ∧ c ≠ −∞) ∧
    (b = +∞ ⇒ c ≠ −∞) ∧
    (b = −∞ ⇒ c ≠ +∞) ⇒
    a - (b + c) = a - b - c
Proof
  rw[]
  >> Cases_on ‘a’ >> Cases_on ‘b’ >> Cases_on ‘c’ >> gvs[extreal_add_def,
                                                         extreal_sub_def]
  >> gvs[real_sub_plus]
QED

Theorem mul_div_mul_rcancel:
  ∀a b c : extreal.
    a ≠ +∞ ∧
    a ≠ −∞ ∧
    b ≠ +∞ ∧
    b ≠ −∞ ∧
    b ≠ 0 ∧
    c ≠ +∞ ∧
    c ≠ −∞ ∧
    c ≠ 0 ⇒
    (a * c) / (b * c) = a / b
Proof
  Cases_on ‘a’ >> Cases_on ‘b’ >> Cases_on ‘c’ >> rw[]
  >> gvs[extreal_mul_eq, extreal_div_eq]
QED

Theorem pow_sub:
  ∀(a : extreal) (n : num) (m : num).
    a ≠ +∞ ∧
    a ≠ −∞ ∧
    a ≠ 0 ∧
    m ≤ n ⇒
    a pow (n - m) = a pow n / a pow m
Proof
  Induct_on ‘m’ >> rw[]
  >> Cases_on ‘n’ >> gvs[]
  >> gvs[ADD1, pow_add]
  >> DEP_PURE_ONCE_REWRITE_TAC[mul_div_mul_rcancel]
  >> gvs[pow_not_infty]
  >> Cases_on ‘m’ >> gvs[]
QED

Theorem POW_SUB:
  ∀(a : real) (n : num) (m : num).
    a ≠ 0 ∧
    m ≤ n ⇒
    a pow (n - m) = a pow n / a pow m
Proof
  Induct_on ‘m’ >> rw[]
  >> Cases_on ‘n’ >> gvs[]
  >> gvs[ADD1, POW_ADD]
QED

(* -------------------------------------------------------------------------- *)
(* Expression for what happens when we divide who powers with the same base   *)
(* -------------------------------------------------------------------------- *)
Theorem POW_DIV_SAME:
  ∀(a : real) (n : num) (m : num).
    a ≠ 0 ⇒
    a pow n / a pow m = if m ≤ n then a pow (n - m) else 1 / (a pow (m - n))
Proof
  rw[POW_SUB]
QED

Theorem POS_REAL_LEQ_RMUL:
  ∀a b : real. 
    0 < a ⇒
    (a ≤ a * b ⇔ 1 ≤ b)
Proof
  rw[]
QED

(* -------------------------------------------------------------------------- *)
(* Similar to pow_mul_sub_leq. See comment for that theorem. I happened to be *)
(* able to prove this more easily, and it's a useful step on the way to       *)
(* proving that theorem.                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem pow_mul_sub_lt_imp:
  ∀(a : extreal) (b : extreal) (n : num) (x : num) (y : num).
    0 < a ∧
    a ≠ +∞ ∧
    0 < b ∧
    b ≠ +∞ ∧
    b ≤ a ∧
    x ≤ n ∧
    y ≤ n ∧
    a pow x * b pow (n - x) < a pow y * b pow (n - y) ⇒
    x < y
Proof
  rw[]
  (* Break down our extreals a and b into Normal a and Normal b *)
  >> namedCases_on ‘a’ ["", "", "a"] >> gvs[]
  >> namedCases_on ‘b’ ["", "", "b"] >> gvs[]
  >> qabbrev_tac ‘a = a'’ >> pop_assum kall_tac
  >> qabbrev_tac ‘b = b'’ >> pop_assum kall_tac
  (* Translate into a real expression *)
  >> gvs[extreal_pow_def, extreal_mul_eq]
  (* Instead of proving x < y, assume y ≤ x and prove false. This allows us to
     write x as y + d for some d, which allows us to induct on d.*)
  >> CCONTR_TAC
  >> gvs[NOT_LESS]
  (* Write x as y + d *)
  >> qpat_x_assum ‘y ≤ x’ mp_tac >> simp[LE_EXISTS] >> rpt strip_tac >> gvs[]
  >> qabbrev_tac ‘d = p’ >> pop_assum kall_tac
  (* Induct on the variable which denotes the difference between y and x*)
  >> Induct_on ‘d’ >> rw[]
  (* Simplify *)
  >> gvs[REAL_NOT_LT]
  >> ‘a ≠ 0 ∧ b ≠ 0’ by (conj_tac >> (CCONTR_TAC >> gvs[]))
  (* Convert powers into a multiplication of terms so that we can drag the
     SUCs out of the expression, so that we can break down to the smaller case
     where we can apply the inductive hypothesis. *)
  >> gvs[ADD1, POW_ADD, POW_SUB]
  (* Complete proof automatically using Holyhammer *)
  >> metis_tac [POW_LE, REAL_LE_LT, pow]
QED

(* -------------------------------------------------------------------------- *)
(* Like POW_EQ, but doesn't require the exponent to have the structure        *)
(* "SUC n"                                                                    *)
(* -------------------------------------------------------------------------- *)
Theorem POW_EQ_ALT:
  ∀(x : real) (y : real) (n : num).
    0 ≤ x ∧ 0 ≤ y ∧ n ≠ 0n ⇒
    (x pow n = y pow n ⇔ x = y)
Proof
  rw[]
  >> Cases_on ‘n’ >> gvs[]
  >> EQ_TAC >> metis_tac[POW_EQ]
QED

(* -------------------------------------------------------------------------- *)
(* The function which takes a to the power of x and b to the power of n - x   *)
(* is injective with respect to x if a ≠ b                                    *)
(* -------------------------------------------------------------------------- *)
Theorem pow_mul_sub_inj:
  ∀(a : extreal) (b : extreal) (n : num) (x : num) (y : num).
    a ≠ +∞ ∧
    0 < a ∧
    b ≠ +∞ ∧
    0 < b ∧
    a ≠ b ∧
    x ≤ n ∧
    y ≤ n ∧
    a pow x * b pow (n - x) = a pow y * b pow (n - y) ⇒
    x = y
Proof
  rw[]
  >> ‘0 ≠ a ∧ 0 ≠ b’ by (conj_tac >> CCONTR_TAC >> gvs[])
  (* Break down our extreals a and b into Normal a and Normal b *)
  >> namedCases_on ‘a’ ["", "", "a"] >> gvs[extreal_div_def]
  >> namedCases_on ‘b’ ["", "", "b"] >> gvs[extreal_div_def]
  >> qabbrev_tac ‘a = a'’ >> pop_assum kall_tac
  >> qabbrev_tac ‘b = b'’ >> pop_assum kall_tac
  (* Translate into a real expression *)
  >> gvs[extreal_pow_def, extreal_mul_eq]
  (* Simplify *)
  >> gvs[POW_SUB]
  (* Case where x = y *)
  >> Cases_on ‘x = y’ >> gvs[]
  (* Without loss of generality, x < y*)
  >> wlog_tac ‘x < y’ [‘x’, ‘y’]
  >- (gvs[]
      (* Swap x and y, so as to use symmetry *)
      >> last_x_assum (qspecl_then [‘y’, ‘x’] assume_tac)
      >> gvs[]
     )
  >> gvs[]
  (* Collect a terms and b terms *)
  >> ‘(a pow x / a pow y) * (b pow y / b pow x) = 1’ by (gvs[] >> metis_tac[])
  (* Simplify b term *)
  >> sg ‘a pow x / a pow y * (b pow (y - x)) = 1’
  >- (pop_assum mp_tac
      >> DEP_PURE_REWRITE_TAC[POW_DIV_SAME]
      >> gvs[]
     )
  (* Simplify the a-term using holyhammer *)
  >> ‘1 / (a pow (y - x)) * b pow (y - x) = 1’ by metis_tac [NOT_LESS, POW_DIV_SAME]
  (* Simplify *)
  >> gvs[]
  (* Use injectivity of pow *)
  >> pop_assum mp_tac
  >> DEP_PURE_ONCE_REWRITE_TAC[POW_EQ_ALT]
  >> gvs[REAL_LT_LE]
QED

(* -------------------------------------------------------------------------- *)
(* Cancel on the right in the real case of a leq when the RHS is exactly      *)
(* equal to the term being cancelled                                          *)
(* -------------------------------------------------------------------------- *)
Theorem REAL_RCANCEL_LEQ_ID:
  ∀a b : real.
    0 < b ⇒
    (a * b ≤ b ⇔ a ≤ 1)
Proof
  rw[]
QED

(* -------------------------------------------------------------------------- *)
(* Suppose we have two nonnegative factors, each taken to some power. As we   *)
(* increase the number of instances of the larger factor and decrease the     *)
(* number of instances of the smaller factor, we cause an overall increase.   *)
(*                                                                            *)
(* We use x to refer to one of the exponents, and we use c - x to refer to    *)
(* the other exponent for some c. Thus we require x ≤ c. We then increase x   *)
(* to a new value y, similarly decreasing c - x to a new value c - y. We      *)
(* thus also require y ≤ c. Then our value would have experienced an increase *)
(* if and only if x increased to y.                                           *)
(* -------------------------------------------------------------------------- *)
Theorem pow_mul_sub_leq:
  ∀(a : extreal) (b : extreal) (n : num) (x : num) (y : num).
    0 < a ∧
    a ≠ +∞ ∧
    0 < b ∧
    b ≠ +∞ ∧
    b < a ∧
    x ≤ n ∧
    y ≤ n ⇒
    (a pow x * b pow (n - x) ≤ a pow y * b pow (n - y) ⇔ x ≤ y)
Proof
  rw[]
  (* Prove commonly used preconditions *)
  >> ‘0 ≤ a ∧ 0 ≤ b ∧ a ≠ 0 ∧ b ≠ 0 ∧ b ≤ a ∧ a ≠ b’ by gvs[lt_le]
  (* We can use the lemmas written above for the forwards implication in the
     case of equality and in the case of strict inequality*)
  >> EQ_TAC
  >- (simp[LE_LT, le_lt]
      (* In the case where we have less than, use the lemma for the
              less than case *)
      >> rw[]
      >- (disj1_tac
          >> irule pow_mul_sub_lt_imp
          >> qexistsl [‘a’, ‘b’, ‘n’]
          >> gvs[]
         )
      (* In the case where we have equality, use the lemma for the equality
         case. *)
      >> disj2_tac
      >> irule pow_mul_sub_inj
      >> qexistsl [‘a’, ‘b’, ‘n’]
      >> gvs[]
     )
  >> rw[]
  (* Now that we have proven the forwards implication, we need to prove the
      reverse implication. Start by proving it in the specific case where
      x = y, which is trivial. *)
  >> Cases_on ‘x = y’ >> gvs[]
  (* We now know x < y *)
  >> ‘x < y’ by gvs[lt_le]
  (* Rewrite y as x + d *)
  >> pop_assum mp_tac >> simp[LT_EXISTS]
  >> rw[]
  >> gvs[]
  (* Translate to a statement in reals rather than extreals *)
  >> namedCases_on ‘a’ ["", "", "a"] >> gvs[extreal_div_def]
  >> namedCases_on ‘b’ ["", "", "b"] >> gvs[extreal_div_def]
  >> qabbrev_tac ‘a = a'’ >> pop_assum kall_tac
  >> qabbrev_tac ‘b = b'’ >> pop_assum kall_tac
  >> gvs[extreal_pow_def, extreal_mul_eq]
  (* Induct on d, which is the difference between x and y. Break down the
     powers into a multiplication of terms *)
  >> Induct_on ‘d’ >> gvs[POW_ADD, POW_SUB, ADD1]
  (* Simplify *)
  >> rw[] >> gvs[]
  (* Make it more similar in form to the inductive hypothesis *)
  >> ‘b * (b * b pow d) ≤ a * (a * a pow d)’ suffices_by gvs[]
  (* Give names to the LHS and RHS of the inductive hypothesis *)
  >> qmatch_goalsub_abbrev_tac ‘b * LHS ≤ a * RHS’
  (* Move b and a together *)
  >> ‘(b / a) * LHS ≤ RHS’ suffices_by gvs[]
  (* It's sufficient to show that the new LHS is bounded above by the LHS from
     the inductive hypothesis *)
  >> ‘b / a * LHS ≤ LHS’ suffices_by metis_tac[REAL_LE_TRANS]
  (* It suffices that b / a ≤ 1 *)
  >> ‘0 < LHS ∧ b / a ≤ 1’ suffices_by simp[REAL_RCANCEL_LEQ_ID]
  >> conj_tac
  >- (unabbrev_all_tac
      >> gvs[GSYM (cj 2 pow)]
      >> gvs[REAL_POW_LT]
     )
  (* Simplifier now automatically proves the goal *)
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* A real version of pow_mul_sub_leq                                          *)
(* -------------------------------------------------------------------------- *)
Theorem REAL_POW_MUL_SUB_LEQ:
  ∀(a : real) (b : real) (n : num) (x : num) (y : num).
    0 < a ∧
    0 < b ∧
    b < a ∧
    x ≤ n ∧
    y ≤ n ⇒
    (a pow x * b pow (n - x) ≤ a pow y * b pow (n - y) ⇔ x ≤ y)
Proof
  rw[]
  >> qspecl_then [‘Normal a’, ‘Normal b’, ‘n’, ‘x’, ‘y’] assume_tac pow_mul_sub_leq
  >> gvs[extreal_pow_def, extreal_mul_eq]
QED

Theorem REAL_POW_MUL_SUB_LEQ_REVERSE:
  ∀(a : real) (b : real) (n : num) (x : num) (y : num).
    0 < a ∧
    0 < b ∧
    a < b ∧
    x ≤ n ∧
    y ≤ n ⇒
    (a pow x * b pow (n - x) ≤ a pow y * b pow (n - y) ⇔ y ≤ x)
Proof
  rw[]
  >> qspecl_then [‘b’, ‘a’, ‘n’, ‘(n - x)’, ‘(n - y)’] assume_tac REAL_POW_MUL_SUB_LEQ
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* A version of pow_mul_sub_le that works in the case where we have a less    *)
(* than operator rather than a less than or equal to operator.                *)
(* -------------------------------------------------------------------------- *)
Theorem pow_mul_sub_lt:
  ∀(a : extreal) (b : extreal) (n : num) (x : num) (y : num).
    0 < a ∧
    a ≠ +∞ ∧
    0 < b ∧
    b ≠ +∞ ∧
    b < a ∧
    x ≤ n ∧
    y ≤ n ⇒
    (a pow x * b pow (n - x) < a pow y * b pow (n - y) ⇔ x < y)
Proof
  rw[]
  (* In the forwards implication, we have to treat the case where x = y
     specially, but the case where x ≤ y follows from the leq version of this
     theorem. *)
  >> EQ_TAC >> rw[]
  >- (Cases_on ‘x = y’ >> gvs[]
      >> gvs[LT_LE]
      >> irule (iffLR pow_mul_sub_leq)
      >> qexistsl [‘a’, ‘b’, ‘n’]
      >> gvs[lt_le]
     )
  (* Split goal up into less than and less than or equal to *)
  >> simp[lt_le]
  (* The leq case follows directly from the leq version of this theorem. *)
  >> gvs[pow_mul_sub_leq]
  (* The equal case follows from the injectivity of this function, proven
     earlier *)
  >> CCONTR_TAC >> gvs[]
  >> ‘x = y’ suffices_by gvs[]
  >> irule pow_mul_sub_inj
  >> qexistsl [‘a’, ‘b’, ‘n’]
  >> gvs[]
  (* We may assume a = b by way of contadiction. Then the proof becomes trivial
   *)
  >> CCONTR_TAC >> gvs[]
QED

Theorem blockwise_map_decoding_hamming:
  ∀enc n m p bs ds.
    0 < p ∧ p < 1 ∧
    p < 1 - p ∧
    LENGTH bs = n ∧
    LENGTH ds = m ∧
    (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
    (is_optimal_blockwise_map_decoding enc n m p bs ds ⇔
       (∀bs2.
          LENGTH bs2 = n ⇒
          hamming_distance ds (enc bs) ≤
          hamming_distance ds (enc bs2)
       ))
Proof
  rw[]
  (* More useful expression for probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[lt_le]
  (* Expand out definitions *)
  >> gvs[is_optimal_blockwise_map_decoding_def]
  >> gvs[prob_input_string_given_received_string_def]
  >> gvs[cond_prob_def]
  >> rw[]
  (* The LHS and RHS are true at precisely the same choices of bs2, so we may
     drag the forall out of the iff without worrying that this may impact the
     provability of the statement. *)
  >> ho_match_mp_tac (METIS_PROVE[] “(∀x. P x ⇔ Q x) ⇒ ((∀x. P x) ⇔ (∀x. Q x))”)
  >> gen_tac
  (* The implication may be simplified out on both sides *)
  >> Cases_on ‘LENGTH bs2 = LENGTH bs’ >> simp[]
  (* Cancel out the divide *)
  >> DEP_PURE_ONCE_REWRITE_TAC[ldiv_le_iff]
  >> rw[]
  >- gvs[lt_le, PROB_POSITIVE, event_received_string_takes_value_is_event,
         ecc_bsc_prob_space_is_prob_space,
         event_received_string_takes_value_nonzero_prob]
  >- gvs[PROB_FINITE, ecc_bsc_prob_space_is_prob_space,
         event_received_string_takes_value_is_event]
  (* Simplify intersection which has a known value *)
  >> gvs[input_string_takes_value_inter_received_string_takes_value]
  (* Use expression for probability in our prob space *)
  >> DEP_PURE_REWRITE_TAC[prob_ecc_bsc_prob_space]
  >> gvs[events_ecc_bsc_prob_space, POW_DEF, bxor_length]
  (* Cancel out the multiplication *)
  >> DEP_PURE_ONCE_REWRITE_TAC[le_lmul]
  >> rw[]
  >- (irule lt_div_alt
      >> gvs[pow_pos_lt, pow_not_infty]
     )
  >- (irule (cj 1 div_not_infty_if_not_infty_alt)
      >> gvs[pow_not_infty, pow_pos_lt]
     )
  (* Use expression for sym_noise_mass_func of bxor *)
  >> gvs[sym_noise_mass_func_bxor]
  (* Convert extreals to reals *)
  >> namedCases_on ‘p’ ["", "", "p'"] >> gvs[]
  >> qabbrev_tac ‘p = p'’ >> pop_assum kall_tac
  >> gvs[GSYM normal_1, extreal_sub_eq, extreal_pow_def, extreal_mul_def]
  (* Use pow_mul_sub_leq, which was written to solve the current proof state *)
  >> gvs[hamming_distance_sym]
  >> irule REAL_POW_MUL_SUB_LEQ_REVERSE
  (* Solve preconditions for pow_mul_sub_leq*)
  >> gvs[hamming_distance_length]
  >> drule_all complement_prob_lt_real >> rw[] >> gvs[]
QED

Theorem prob_zero_cond_prob_zero:
  ∀sp A B.
    prob_space sp ∧
    prob sp B ≠ 0 ∧
    prob sp (A ∩ B) = 0 ⇒
    cond_prob sp A B = 0
Proof
  rw[]
  >> gvs[cond_prob_def]
  >> gvs[zero_div]
QED

Theorem length_n_codes_ith_eq_codes_valid_inverse_codes:
  ∀n m enc i x.
    {cs | LENGTH cs = m ∧
          (EL i cs = x) ∧
          (∃bs. LENGTH bs = n ∧ enc bs = cs)}
          = length_n_codes m ∩ ith_eq_codes i x ∩ valid_inverse_codes enc n
Proof
  ASM_SET_TAC[]
QED

(* -------------------------------------------------------------------------- *)
(* This expression has come up for me twice now, and gvs doesn't solve it     *)
(* automatically, so I add it to the stateful simpset to ensure that it does  *)
(* get solved automatically in the future                                     *)
(* -------------------------------------------------------------------------- *)
Theorem exists_with_length_and_enc[simp]:
  ∀enc bs.
    ∃bs2. LENGTH bs2 = LENGTH bs ∧ enc bs2 = enc bs
Proof
  metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* Simpset which collects some commonly used theorems regarding MAP decoders. *)
(*                                                                            *)
(* Based on real_SS from realSimps.sml.                                       *)
(* -------------------------------------------------------------------------- *)
val map_decoder_SS =
SSFRAG
{
name = SOME"map_decoder",
ac = [],
congs = [],
convs = [],
dprocs = [],
filter = NONE,
rewrs = map
        (fn s => (SOME {Thy = "map_decoder", Name = s},
                  DB.fetch "map_decoder" s
                 )
        )
        ["event_input_bit_takes_value_is_event",
         "event_input_string_takes_value_is_event",
         "event_sent_string_takes_value_is_event",
         "event_received_string_takes_value_is_event",
         "event_input_bit_takes_value_nonzero_prob",
         "event_input_string_takes_value_nonzero_prob",
         "event_sent_string_takes_value_nonzero_prob",
         "event_received_string_takes_value_nonzero_prob",
         "event_sent_string_takes_value_nonzero_prob_explicit",
         "event_sent_string_takes_value_zero_prob",
         "event_input_string_and_received_string_take_values_is_event",
         "event_input_string_and_received_string_take_values_nonzero_prob",
         "event_input_string_takes_value_disjoint",
         "event_sent_string_takes_value_disjoint"
        ]
};

val ecc_prob_space_SS =
SSFRAG
{
name = SOME"ecc_prob_space",
ac = [],
congs = [],
convs = [],
dprocs = [],
filter = NONE,
rewrs = map
        (fn s => (SOME {Thy = "ecc_prob_space", Name = s},
                  DB.fetch "ecc_prob_space" s
                 )
        )
        ["ecc_bsc_prob_space_is_prob_space"
        ]
};

(* -------------------------------------------------------------------------- *)
(* My rewrites relevant to error-correcting codes that you will almost always *)
(* want to use, but have a precondition so I don't want to include them in    *)
(* the stateful simpset                                                       *)
(* -------------------------------------------------------------------------- *)
val ecc_ss = (srw_ss()) ++ map_decoder_SS ++ ecc_prob_space_SS;

(* -------------------------------------------------------------------------- *)
(* Add some rewrites from other libraries that you will almost always want to *)
(* use, but have preconditions so I don't want to include them in the         *)
(* stateful simpset                                                           *)
(* -------------------------------------------------------------------------- *)
val ecc2_ss = ecc_ss ++ rewrites[PROB_POSITIVE,
                                 PROB_FINITE,
                                 COND_PROB_BOUNDS,
                                 COND_PROB_FINITE];

(* TODO: add all these things to the stateful simpset, if it would be sensible *)

(* -------------------------------------------------------------------------- *)
(* Add some more rewrites that may be a bit more time-intensive, or you may   *)
(* not always want to use.                                                    *)
(* -------------------------------------------------------------------------- *)
val ecc3_ss = ecc2_ss ++ rewrites[mul_not_infty2,
                                  prob_zero_cond_prob_zero,
                                  PROB_ZERO_INTER,
                                  length_n_codes_ith_eq_codes,
                                  length_n_codes_ith_eq_codes_valid_inverse_codes,
                                  div_mul_refl_alt];

(* -------------------------------------------------------------------------- *)
(* A theorem based on map_decoder_bitwise_simp2, but instead taking the MAP   *)
(* decoding relative to the sent string rather than the input string.         *)
(*                                                                            *)
(* Step 1: map_decoder_bitwise_sum                                            *)
(* Step 2: map_decoder_bitwise_sum_bayes                                      *)
(* Step 3: map_decoder_bitwise_sum_bayes_prod                                 *)
(* Step 4 (invalid): map_decoder_bitwise_simp1                                *)
(* Step 5 (invalid): map_decoder_bitwise_simp2                                *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_sent_sum_bayes_prod:
  ∀enc n m p ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    (∀xs. LENGTH xs = n ⇒ LENGTH (enc xs) = m) ∧
    (∀xs ys. enc xs = enc ys ⇒ xs = ys) ⇒
    map_decoder_bitwise_sent enc n m p ds =
    let
      map_decoder_bitstring_prob =
      λcs. (sym_noise_mass_func p (bxor cs ds)) *
           prob (ecc_bsc_prob_space n m p)
                (event_sent_string_takes_value enc n m cs);
      map_decoder_bit_prob =
      λi c.
        ∑ map_decoder_bitstring_prob
          {cs | LENGTH cs = m ∧ EL i cs = c
                ∧ (∃bs. LENGTH bs = n ∧ enc bs = cs)};
    in
      (MAP (λi. argmax_bool (map_decoder_bit_prob i)) (COUNT_LIST m))
Proof
  rw[]
  (* More common assumption when dealing with probabilities *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
  (* Expand out the definition we are finding an equivalent expression for *)
  >> gvs[map_decoder_bitwise_sent_def]
  (* The inner bit is the bit we need to prove equivalence of. *)
  >> gvs[MAP_EQ_f]
  >> rw[]
  (* Name the LHS and RHS *)
  >> qmatch_goalsub_abbrev_tac ‘LHS = RHS’
  (* Sum out other sent bits, like in map_decoder_bitwise_sum *)
  >> sg ‘LHS = argmax_bool
               (λc. ∑
                    (λcs. cond_prob
                          (ecc_bsc_prob_space n (LENGTH ds) p)
                          (event_sent_string_takes_value enc n (LENGTH ds) cs)
                          (event_received_string_takes_value enc n (LENGTH ds) ds)
                    )
                    {cs | LENGTH cs = LENGTH ds ∧ (EL i cs ⇔ c)}
               )’
  >- (unabbrev_all_tac
      >> irule argmax_bool_mul_const
      >> qexists ‘1’
      >> gvs[]
      >> rw[FUN_EQ_THM]
      >> gvs[cond_prob_event_sent_string_takes_value_sum]
     )
  >> qpat_x_assum ‘Abbrev (LHS ⇔ _)’ kall_tac
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac ‘LHS = RHS’
  (* Apply Bayes' rule, like in map_decoder_bitwise_sum_bayes *)
  >> sg ‘LHS = argmax_bool
               (λc. ∑
                    (λcs. cond_prob
                          (ecc_bsc_prob_space n (LENGTH ds) p)
                          (event_received_string_takes_value enc n (LENGTH ds) ds)
                          (event_sent_string_takes_value enc n (LENGTH ds) cs) *
                          prob (ecc_bsc_prob_space n (LENGTH ds) p)
                               (event_sent_string_takes_value enc n (LENGTH ds) cs)
                    )
                    {cs | LENGTH cs = LENGTH ds ∧ (EL i cs ⇔ c) ∧
                          (∃bs. LENGTH bs = n ∧ enc bs = cs)}
               )’
  >- (unabbrev_all_tac
      >> irule argmax_bool_mul_const
      >> qexists ‘prob (ecc_bsc_prob_space n (LENGTH ds) p)
                  (event_received_string_takes_value enc n (LENGTH ds) ds)’
      >> rw[]
      >- (irule (cj 2 PROB_FINITE)
          >> full_simp_tac ecc_ss []
         )
      >~ [‘0 < prob _ _’] >- full_simp_tac ecc_ss [lt_le, PROB_POSITIVE]
      >> rw[FUN_EQ_THM]
      (* Move the constant into the sum *)
      >> DEP_PURE_ONCE_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_CMUL_R_ALT]
      >> conj_tac >- full_simp_tac ecc2_ss []
      (* First, restrict the set we are summing over to ensure we don't have
         any zero probabilities, which would be an issue for Bayes' rule
         because the denominator would then have 0 in it. *)
      >> qmatch_goalsub_abbrev_tac ‘∑ f S1 = ∑ g S2’
      >> sg ‘∑ g S2 = ∑ g S1’
      >- (sg ‘S1 = S2 ∩ {cs | ∃bs. LENGTH bs = n ∧ enc bs = cs}’
          >- (unabbrev_all_tac >> ASM_SET_TAC[])
          >> pop_assum (fn th => PURE_REWRITE_TAC[th])
          (* Main lemma to restrict the set we are summing over *)
          >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_INTER_ELIM]
          >> unabbrev_all_tac
          >> full_simp_tac ecc3_ss []
         )
      >> pop_assum  (fn th => PURE_REWRITE_TAC [th])
      (* The two sums are equal because each of the functions is equal on the
         domain *)
      >> irule EXTREAL_SUM_IMAGE_EQ'
      >> unabbrev_all_tac
      >> full_simp_tac ecc3_ss []
      >> rw[]
      (* Apply Bayes' rule*)
      >> DEP_PURE_ONCE_REWRITE_TAC[BAYES_RULE]
      >> full_simp_tac ecc3_ss []
     )
  >> qpat_x_assum ‘Abbrev (LHS ⇔ _)’ kall_tac
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac ‘LHS ⇔ RHS’
  (* Simplify the conditional probability, like in
     map_decoder_bitwise_sum_bayes_prod *)
  >> sg ‘LHS = argmax_bool
               (λc. ∑
                    (λcs. sym_noise_mass_func p (bxor cs ds) *
                          prob (ecc_bsc_prob_space n (LENGTH ds) p)
                               (event_sent_string_takes_value enc n (LENGTH ds) cs))
                    {cs | LENGTH cs = LENGTH ds ∧ (EL i cs ⇔ c) ∧
                          (∃bs. LENGTH bs = n ∧ enc bs = cs)}
               )’
  >- (unabbrev_all_tac
      (* The inside of the argmax is equal *)
      >> irule argmax_bool_mul_const
      >> qexists ‘1’
      >> gvs[]
      >> rw[FUN_EQ_THM]
      (* The inner functions are equivalent *)
      >> irule EXTREAL_SUM_IMAGE_EQ'
      >> unabbrev_all_tac
      >> full_simp_tac ecc3_ss []
      >> rw[]
      (* Use lemma to simplify the conditional probability *)
      >> DEP_PURE_ONCE_REWRITE_TAC[cond_prob_string_given_sent_prod]
      >> full_simp_tac ecc3_ss []
     )
  >> qpat_x_assum ‘Abbrev (LHS ⇔ _)’ kall_tac
  >> gvs[]
QED

val _ = export_theory();
