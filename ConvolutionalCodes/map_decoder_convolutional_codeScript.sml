(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

(* My theories *)
open ecc_prob_spaceTheory;
open argmin_extrealTheory;
open map_decoderTheory;
open recursive_parity_equationsTheory;

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

val _ = new_theory "map_decoder_convolutional_code";

val _ = hide "S";

(* -------------------------------------------------------------------------- *)
(* TODO: simplify requirement on encoder outputting correct length for this   *)
(* special case                                                               *)
(* -------------------------------------------------------------------------- *)
Theorem temporary_name:
  ∀ps qs ts n m p ds.
    let
      enc = encode_recursive_parity_equation (ps, qs) ts;
    in
      0 < p ∧ p < 1 ∧
      LENGTH ds = m ∧
      (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
      map_decoder_bitwise enc n m p ds =
      ARB
Proof
  rw[]
  >> gvs[map_decoder_bitwise_sum_bayes]
  >> 
    
QED
  


val _ = export_theory();
