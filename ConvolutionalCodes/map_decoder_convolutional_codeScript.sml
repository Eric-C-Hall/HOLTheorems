(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

(* My theories *)
open ecc_prob_spaceTheory;
open argmin_extrealTheory;
open map_decoderTheory;
open parity_equationsTheory;
open recursive_parity_equationsTheory;
open useful_theoremsTheory;

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


(* This isn't true
Theorem apply_parity_equation_append_iff:
  ∀ps ts b1 b2.
    LENGTH ts < LENGTH ps ⇒
    ((apply_parity_equation ps (SNOC b1 ts)
      = apply_parity_equation ps (SNOC b2 ts)) ⇔ b1 = b2)
Proof
  Induct_on ‘ts’ >> rw[] >> EQ_TAC >> rw[]
  >- (Cases_on ‘ps’ >> gvs[]
      >> PURE_REWRITE_TAC[apply_parity_equation_def]

                         Cases_on ‘ps’ >> gvs[apply_parity_equation_def]
      >> Cases_on ‘h’ >> gvs[]
     )
QED*)

(* -------------------------------------------------------------------------- *)
(* An expression for when encode_recursive_parity_equation is injective,      *)
(* assuming that the length of the parity equation is appropriate             *)
(* -------------------------------------------------------------------------- *)
Theorem encode_recursive_parity_equation_injective:
  ∀ps qs ts.
    LENGTH ps = LENGTH ts + 1 ⇒
    ((INJ (encode_recursive_parity_equation (ps, qs) ts)
          𝕌(:bool list)
          𝕌(:bool list)
     ) ⇔ LAST ps = T)
Proof
  rw[]
  (* Expand definition of injective *)
  >> gvs[INJ_DEF]
  >> EQ_TAC >> rw[]
  (* Forwards implication.
     We prove the contrapositive.
     If LAST ps = T, then the output will differ on the inputs [T] and [F],
     because the most recently added input is placed at the end, therefore
     the function isn't injective. *)
  >- (first_x_assum $ qspecl_then [‘[T]’, ‘[F]’] assume_tac
      (* Simplify on this simple input *)
      >> fs[encode_recursive_parity_equation_def]
      >> gvs[apply_parity_equation_append]
      (* Remove the unnecessary bit at the start of applying the parity
      equation, because only the bit at the end differs and is thus helpful *)
      >> qmatch_asmsub_abbrev_tac ‘(x ⇔ expr1) ⇎ (x ⇔ expr2)’
      >> ‘expr1 ⇎ expr2’ by (unabbrev_all_tac >> metis_tac[])
      >> qpat_x_assum ‘(x ⇔ expr1) ⇎ (x ⇔ expr2)’ kall_tac
      >> unabbrev_all_tac
      (* Simplify DROP (LENGTH ts) ps down to an explicit expression *)
      >> sg ‘DROP (LENGTH ts) ps = [LAST ps]’
      >- (pop_assum kall_tac
          >> Induct_on ‘ps’ >> Cases_on ‘ts’ >> rw[]
          >> gvs[DROP_ALL_BUT_ONE]
          >> Cases_on ‘ps’ >> gvs[]
         )
      (* Evaluating gets us the result *)
      >> gvs[apply_parity_equation_def]
      >> metis_tac[]
     )
  (* Reverse implication.
     If the last parity bit differs, then in the first step, the *)
  >> 
QED


(* -------------------------------------------------------------------------- *)
(* TODO: simplify requirement on encoder outputting correct length for this   *)
(* special case                                                               *)
(* -------------------------------------------------------------------------- *)
Theorem temporary_name:
  ∀ps qs ts n m p ds.
    let
      enc = encode_recursive_parity_equation (ps, qs) ts;
    in
      LENGTH ps = LENGTH ts + 1 ∧
      0 < p ∧ p < 1 ∧
      LENGTH ds = m ∧
      (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
      map_decoder_bitwise enc n m p ds =
      MAP (λi. argmax_bool (λx. ARB))
          (COUNT_LIST n)
Proof
  rw[]
  (* We start from the most simplified version of the MAP decoder *)
  >> DEP_PURE_ONCE_REWRITE_TAC[map_decoder_bitwise_sum_bayes_prod]
  >> rw[]
  (* The bitwise part is the part which is equivalent *)
  >> qmatch_goalsub_abbrev_tac ‘cond_prob sp e1 (e2 _)’
  >> gvs[MAP_EQ_f]
  >> rw[]
  (* In this case, the inner functions are equivalent *)
  >> AP_TERM_TAC
  >> rw[FUN_EQ_THM]
  (* The probability of the input taking a particular value is equal to the
     probability of starting in the starting state *)
  >> 
QED
  


val _ = export_theory();
