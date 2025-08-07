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
open map_decoderLib;

(* Standard theories *)
open arithmeticTheory;
open bitstringTheory;
open extrealTheory;
open listTheory;
open pred_setTheory;
open probabilityTheory;
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
(* The event in which a particular state takes a particular value.            *)
(*                                                                            *)
(* n: The size of the input                                                   *)
(* m: The size of the output                                                  *)
(* ps: The numerator parity equation                                          *)
(* qs: The denominator parity equation                                        *)
(* ts: The initial state                                                      *)
(* i: The index of the state we expect to have a particular value             *)
(* σ: The value that we expect that state to have                             *)
(* -------------------------------------------------------------------------- *)
Definition event_state_takes_value_def:
  event_state_takes_value n m ps qs ts i σ = 
  {(bs, ns) | LENGTH bs = n ∧ LENGTH ns = m ∧
              encode_recursive_parity_equation_state (ps,qs) ts bs = σ
  }
End

(* -------------------------------------------------------------------------- *)
(* The event in which the states take a particular sequence of values         *)
(* -------------------------------------------------------------------------- *)
Definition event_state_sequence_takes_value_def:
  (event_state_sequence_takes_value n m ps qs ts [] =
   {(bs, ns) | LENGTH bs = n ∧ LENGTH ns = m})
  ∧ event_state_sequence_takes_value n m ps qs ts (σ::σs) =
    (event_state_sequence_takes_value n m ps qs ts σs)
    ∩ event_state_takes_value n m ps qs ts (LENGTH σs) σ
End

(* -------------------------------------------------------------------------- *)
(* An expression for when encode_recursive_parity_equation is injective,      *)
(* assuming that the length of the parity equation is appropriate.            *)
(* -------------------------------------------------------------------------- *)
Theorem encode_recursive_parity_equation_inj:
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
     Apply contrapositive to the definition of injectivity:
     We want to prove if x ≠ y, then encode(x) ≠ encode(y).
     Drop all information up until the point at which there is a difference in
     the strings.
     Since the last parity bit differs, then in the new first step, the
     encoded strings will differ *)
  (* Contrapositive *)
  >> CCONTR_TAC >> qpat_x_assum ‘_ _ _ x = _ _ _ y’ mp_tac >> gvs[]
  (* There is a difference between the strings *)
  >> drule_then assume_tac LIST_NEQ
  (* If the difference is in the length, then the encoded strings have
     different lengths *)
  >> Cases_on ‘LENGTH x ≠ LENGTH y’
  >- metis_tac[encode_recursive_parity_equation_length]
  >> gvs[]
  (* Split x and y *)
  >> qspecl_then [‘i’, ‘x’] assume_tac TAKE_DROP
  >> qspecl_then [‘i’, ‘y’] assume_tac TAKE_DROP
  >> NTAC 2 (pop_assum (fn th => PURE_ONCE_REWRITE_TAC[GSYM th]))
  (* Remove the front of the split x and y *)
  >> gvs[encode_recursive_parity_equation_append]
  (* Make the expression cleaner and simpler, replacing x and y by the new,
     truncated variables, and forgetting about the way in which the new state
     was constructed. *)
  >> qmatch_goalsub_abbrev_tac ‘encode_recursive_parity_equation _ ts2 _’
  >> ‘LENGTH ps = LENGTH ts2 + 1’ by (unabbrev_all_tac >>gvs[])
  >> ‘HD (DROP i x) ⇎ HD (DROP i y)’ by gvs[HD_DROP]
  >> ‘LENGTH (DROP i x) = LENGTH (DROP i y)’ by gvs[LENGTH_DROP]
  >> qpat_x_assum ‘LENGTH bs = LENGTH ts + 1’ kall_tac
  >> qpat_x_assum ‘x ≠ y’ kall_tac
  >> qpat_x_assum ‘TAKE i x = TAKE i y’ kall_tac
  >> qpat_x_assum ‘EL i x ⇎ EL i y’ kall_tac
  >> qpat_x_assum ‘LENGTH x = LENGTH y’ kall_tac
  >> qpat_x_assum ‘Abbrev (ts2 = _)’ kall_tac
  >> qpat_x_assum ‘i < LENGTH y’ kall_tac
  >> rename1 ‘_ _ _ x2 ≠ _ _ _ y2’
  (* Simplify *)
  >> Cases_on ‘x2’ >> Cases_on ‘y2’ >> gvs[encode_recursive_parity_equation_def]
  >> rw[]
  (* It's only the first element that matters, since it is the one which
     differs *)
  >> ‘F’ suffices_by gvs[]
  (* Split up the append *)
  >> gvs[apply_parity_equation_append]
  (* Ignore the start, which is the same for each string *)
  >> qmatch_asmsub_abbrev_tac ‘(x ⇔ expr1) ⇔ (x ⇔ expr2)’
  >> ‘expr1 ⇔ expr2’ by metis_tac[]
  >> qpat_x_assum ‘(x ⇔ expr1) ⇔ (x ⇔ expr2)’ kall_tac
  >> unabbrev_all_tac
  (* A simpler, explicit expression for ps with all but one of its elements
     dropped*)
  >> ‘DROP (LENGTH ts2) ps = [LAST ps]’ by gvs[DROP_ALL_BUT_ONE]
  >> gvs[]
  >> gvs[apply_parity_equation_def]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* The probability of the sent string taking a particular value can be        *)
(* calculated by taking the marginal with respect to the state sequence.      *)
(* This simplifies the calculation of the probability becuase we know the     *)
(* state sequence and thus we have more information with which to calculate   *)
(* the probability.                                                           *)
(* -------------------------------------------------------------------------- *)
Theorem ev_sent_marginal_states:
  ∀n m p ps qs ts bs.
    let
      sp = ecc_bsc_prob_space n m p;
      enc = encode_recursive_parity_equation (ps,qs) ts;
      ev_sent = event_sent_string_takes_value enc n m (enc bs);
    in
      prob sp ev_sent =
      ∑ (λσs. prob sp (ev_sent
                       ∩ event_state_sequence_takes_value n m ps qs ts σs))
        {σs : (bool list) list | LENGTH σs = LENGTH bs ∧
                                 (∀σ. MEM σ σs ⇒ LENGTH σ = LENGTH ts)}
Proof
  rw[]
QED


(* -------------------------------------------------------------------------- *)
(* Apply the chain rule to ev_sent_marginal_states, to split the probability  *)
(* of being in a particular state and sending a particular message into the   *)
(* probability of being in a particular state, and the probability of sending *)
(* a particular message given a state sequence. These are two simpler values  *)
(* to calculate.                                                              *)
(* -------------------------------------------------------------------------- *)
Theorem ev_sent_chain_states:
  ∀n m p ps qs ts bs.
    let
      sp = ecc_bsc_prob_space n m p;
      enc = encode_recursive_parity_equation (ps,qs) ts;
      ev_sent = event_sent_string_takes_value enc n m (enc bs);
    in
      prob sp ev_sent =
      ∑ (λσs. cond_prob sp ev_sent
                        (event_state_sequence_takes_value n m ps qs ts σs) *
              prob sp (event_state_sequence_takes_value n m ps qs ts σs))
        {σs : (bool list) list | LENGTH σs = LENGTH bs ∧
                                 (∀σ. MEM σ σs ⇒ LENGTH σ = LENGTH ts)}
Proof
  rw[]
  >> qmatch_goalsub_abbrev_tac ‘prob sp (_ enc _ _ _) = ∑ _ S’
  >> qmatch_goalsub_abbrev_tac ‘prob sp ev_sent = _’
  >> qspecl_then [‘sp’,
                  ‘ev_sent’,
                  ‘event_state_sequence_takes_value n m ps qs ts’,
                  ‘S’] assume_tac TOTAL_PROB_SIGMA
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> conj_tac
  >- (unabbrev_all_tac
      
     )
QED

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* Note: σs does not include the initial state, only the resulting sequence   *)
(*       of states.                                                           *)
(* -------------------------------------------------------------------------- *)
Theorem gfdjok:
  ∀n m p ps qs ts bs.
    prob (ecc_bsc_prob_space n m p)
         (event_sent_string_takes_value
          (encode_recursive_parity_equation (ps,qs) ts)
          n
          m
          (encode_recursive_parity_equation (ps, qs) ts bs)
         ) = ∑ (λσs. ARB)
               {σs : (bool list) list | LENGTH σs = LENGTH bs}
Proof
  rw[]

    TOTAL_PROB_SIGMA
QED

(* -------------------------------------------------------------------------- *)
(* TODO: simplify requirement on encoder outputting correct length for this   *)
(* special case                                                               *)
(*                                                                            *)
(* We assume that our parity equation is delayfree                            *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_sent_encode_recursive_parity_equation:
  ∀ps qs ts n m p ds.
    let
      enc = encode_recursive_parity_equation (ps, qs) ts;
    in
      LAST ps ∧
      LENGTH ps = LENGTH ts + 1 ∧
      0 < p ∧ p < 1 ∧
      LENGTH ds = m ∧
      (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
      map_decoder_bitwise_sent enc n m p ds =
      MAP (λi.
             argmax_bool
             (λx. ∑ ARB
                    {cs | LENGTH cs = m ∧
                          (EL i cs = x) ∧
                          (∃bs.
                             LENGTH bs = n ∧
                             encode_recursive_parity_equation (ps, qs) ts bs = cs)
                             }
             )
          )
          (COUNT_LIST m)
Proof
  rw[]
  (* We start from the most simplified version of the MAP decoder *)
  >> DEP_PURE_ONCE_REWRITE_TAC[map_decoder_bitwise_sent_sum_bayes_prod]
  >> rw[]
  >- metis_tac[]
  >- (drule encode_recursive_parity_equation_inj >> rpt strip_tac
      >> gvs[INJ_DEF]
      >> metis_tac[]
     )
  (* The bitwise part is the part which is equivalent *)
  >> rw[MAP_EQ_f]
  (* In this case, the inner functions are equivalent *)
  >> irule argmax_bool_mul_const
  >> qexists ‘1’
  >> gvs[]
  >> rw[FUN_EQ_THM]
  (* The function is equivalent *)
  >> irule EXTREAL_SUM_IMAGE_EQ'
  >> gvs[length_n_codes_ith_eq_codes_valid_inverse_codes]
  >> rw[]
  (*  *)
       
  
  >> full_simp_tac map_decoder.ecc3_ss []
  >> rw[]
  (* P(cs) = Σ P(cs, σ) {σ}
           = Σ (P(cs | σ))*)
  (* The probability of *)
  >> 
QED
  


val _ = export_theory();
