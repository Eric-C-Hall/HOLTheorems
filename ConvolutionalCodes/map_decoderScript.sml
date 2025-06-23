(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

(* My theories *)
open ecc_prob_spaceTheory;
open argmin_extrealTheory;

(* Standard theories *)
open bitstringTheory;
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
(* bits that maximize the probably that we both received that bit and         *)
(* received that message.                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_joint:
  ∀enc n m p ds.
    0 ≤ p ∧ p ≤ 1 ⇒
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
  rw[]
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
  >- (gvs[ecc_bsc_prob_space_def]
      >> gvs[length_n_codes_uniform_prob_space_def, sym_noise_prob_space_def]
      >> gvs[events_def]
      >> gvs[prod_measure_space_def]
      >> gvs[prod_sigma_def]
      >> gvs[sigma_def]
      >> rw[]

           gvs[ecc_bsc_prob_space_def, martingaleTheory.prod_measure_space_def,
               length_n_codes_uniform_prob_space_def,
               events_def, sym_noise_prob_space_def,
               subsets_def, prod_sigma_def]
     )

     gvs[PROB_FINITE, PROB_POSITIVE]
  )
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
