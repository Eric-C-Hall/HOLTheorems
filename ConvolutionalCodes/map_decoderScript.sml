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
open sigma_algebraTheory;
open martingaleTheory;

(* Standard libraries *)
open realLib;
open dep_rewrite;
open ConseqConv;

val _ = new_theory "map_decoder";

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
