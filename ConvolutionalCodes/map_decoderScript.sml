(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

open ecc_prob_spaceTheory;
open argmin_extrealTheory;
open bitstringTheory;
open probabilityTheory;

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
(* enc: the encoding function                                                 *)
(* n: the length of the initial message                                       *)
(* m: the length of the encoded message                                       *)
(* p: the probability of bit error in our binary symmetric channel            *)
(* ds: the string that we wish to decode                                      *)
(* -------------------------------------------------------------------------- *)
Definition map_decoder_bitwise_def:
  map_decoder_bitwise enc n m p ds =
  MAP
  (λi. argmax
       (λx. cond_prob (ecc_bsc_prob_space n m p)
                      (λ(bs, ns).
                         EL i bs = x 
                      )
                      (λ(bs, ns).
                         bxor (enc bs) ns = ds
                      )
       )
       ({T; F})
  )
  (COUNT_LIST n)
End

val _ = export_theory();
