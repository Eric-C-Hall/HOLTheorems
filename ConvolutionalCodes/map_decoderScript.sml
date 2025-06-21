(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

open ecc_prob_spaceTheory;
open argmin_extrealTheory;
open bitstringTheory;
open probabilityTheory;
open ConseqConv;

open iterateTheory;

val _ = new_theory "map_decoder";

(* -------------------------------------------------------------------------- *)
(* The probability that a particular bit has a particular value, given the    *)
(* message that was received.                                                 *)
(*                                                                            *)
(* enc: the encoding function                                                 *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* p: the probability of bit error in our binary symmetric channel            *)
(* ds: the string that we wish to decode                                      *)
(* i: the index of the bit we are finding the probability for                 *)
(* x: the value we are finding the probability of                             *)
(* -------------------------------------------------------------------------- *)
Definition map_decoder_bit_prob_def:
  map_decoder_bit_prob enc n m p ds i x = cond_prob (ecc_bsc_prob_space n m p)
                                                    (λ(bs, ns).
                                                       EL i bs = x 
                                                    )
                                                    (λ(bs, ns).
                                                       bxor (enc bs) ns = ds
                                                    )
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
(* This implementation breaks ties by assuming a bit has the value F in the   *)
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
  MAP
  (λi. let
         prob_T = map_decoder_bit_prob enc n m p ds i T;
         prob_F = map_decoder_bit_prob enc n m p ds i F;
       in
         if prob_T ≤ prob_F
         then
           F
         else
           T
  )
  (COUNT_LIST n)
End

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
