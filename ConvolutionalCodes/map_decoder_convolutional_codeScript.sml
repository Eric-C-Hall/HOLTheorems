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
open holyHammer;

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

Overload length_n_state_sequences = “λn. {σs : bool list list | LENGTH σs = n}”;

(* TODO: This only includes one requirement for validity. A valid sequence will
         also require, for example, each state to be reachable from the
         previous. So I should probably rename this to something *)
Overload valid_state_sequences = “λn. {σs : bool list list | ∀σ. MEM σ σs ⇒
                                                                 LENGTH σ = n}”;

Overload length_n_valid_state_sequences =
“λn l. {σs : bool list list | LENGTH σs = n ∧ (∀σ. MEM σ σs ⇒ LENGTH σ = l)}”

(* I'm no longer sure that it's better to treat these components separately,
   because finiteness of the set only holds when both components are present. *)
Theorem length_n_state_sequences_valid_state_sequences_inter:
  ∀n l.
    length_n_valid_state_sequences n l =
    length_n_state_sequences n ∩ valid_state_sequences l
Proof
  rw[]
  >> ASM_SET_TAC[]
QED

(* -------------------------------------------------------------------------- *)
(* Write the length n valid state sequences inductively in terms of the       *)
(* previous length valid state sequences.                                     *)
(* -------------------------------------------------------------------------- *)
Theorem length_n_valid_state_sequences_step:
  ∀n l.
    length_n_valid_state_sequences (SUC n) l =
    BIGUNION (IMAGE
              (λσ. IMAGE (CONS σ) (length_n_valid_state_sequences n l))
              (length_n_codes l)
             )
Proof
  rw[EXTENSION]
  >> EQ_TAC >> gvs[] >> rw[]
  >- (Cases_on ‘x’ >> gvs[]
      >> qexists ‘IMAGE (CONS h) (length_n_valid_state_sequences (LENGTH t) l)’
      >> rw[]
      >> qexists ‘h’
      >> rw[]
      >> (last_x_assum (fn th => drule (iffLR th))
          >> rw[]
          >> Cases_on ‘σ' = σ’ >> gvs[])
     )
  >- (pop_assum (fn th => drule (iffLR th))
      >> rw[]
      >> pop_assum $ qspec_then ‘σ’ assume_tac
      >> gvs[]
     )
  >- (last_x_assum (fn th => drule (iffLR th))
      >> rw[]
      >> Cases_on ‘σ' = σ’ >> gvs[]
     )
QED

(* -------------------------------------------------------------------------- *)
(* The set of valid length n state sequences, where each state has length l,  *)
(* is finite.                                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem length_n_state_sequences_finite[simp]:
  ∀n l.
    FINITE (length_n_valid_state_sequences n l)
Proof
  rw[]
  >> Induct_on ‘n’ >> gvs[]
  (* Base case *)
  >- (qmatch_goalsub_abbrev_tac ‘FINITE S’
      >> sg ‘S = {[]}’
      >- (unabbrev_all_tac
          >> rw[EXTENSION]
          >> EQ_TAC >> gvs[]
         )
      >> gvs[]
     )
  (* Inductive step *) 
  >> rw[length_n_valid_state_sequences_step]
  >> gvs[]
QED

Theorem length_n_state_sequences_card[simp]:
  ∀n l.
    CARD (length_n_valid_state_sequences n l) = 2 ** (n * l) 
Proof
  rw[]
  >> Induct_on ‘n’ >> gvs[]
  (* Base case *)
  >- (qmatch_goalsub_abbrev_tac ‘CARD S = _’
      >> sg ‘S = {[]}’
      >- (unabbrev_all_tac
          >> rw[EXTENSION]
          >> EQ_TAC >> gvs[]
         )
      >> gvs[]
     )
  (* Inductive step *) 
  >> rw[length_n_valid_state_sequences_step]
  (* Rewrite into form appropriate for CARD_BIGUNION_SAME_SIZED_SETS, so that
     we may use that theorem to calculate the cardinality *)
  >> qmatch_goalsub_abbrev_tac ‘CARD (BIGUNION S) = _’                               
  >> qsuff_tac ‘CARD (BIGUNION S) = CARD S * (2 ** (l * n))’
  >- (rw[]
      >> qsuff_tac ‘CARD S = 2 ** l’
      >- (rw[]
          >> gvs[GSYM EXP_ADD]
          >> gvs[MULT_CLAUSES]
         )
      >> unabbrev_all_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[FINITE_CARD_IMAGE]
      >> rw[]
      >> EQ_TAC >> gvs[]
      >> PURE_REWRITE_TAC[IMAGE_DEF, EXTENSION]
      >> disch_then (qspec_then ‘σ::REPLICATE n (REPLICATE l F)’ assume_tac)
      >> gvs[]
     )
  (* Use CARD_BIGUNION_SAME_SIZED_SETS *)
  >> irule CARD_BIGUNION_SAME_SIZED_SETS
  >> rw[]
  >- (unabbrev_all_tac
      >> gvs[DISJOINT_ALT]
      >> rw[]
     )
  >- (unabbrev_all_tac
      >> gvs[]
     )
  >~ [‘FINITE S’] >- (unabbrev_all_tac >> gvs[])
  (* Now we must find an expression for the cardinality of a single set from the
     union, using the inductive hypothesis *)
  >> unabbrev_all_tac
  >> gvs[]
  (* Finish off the proof using the fact that the image preserves cardinalities
     if the given function is injective. *)
  >> DEP_PURE_ONCE_REWRITE_TAC[FINITE_CARD_IMAGE]
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* The event that a particular state takes a particular value is a valid      *)
(* event in the space we are working in                                       *)
(* -------------------------------------------------------------------------- *)
Theorem event_state_takes_value_is_event[simp]:
  ∀n m p ps qs ts i σ.
    event_state_takes_value n m ps qs ts i σ ∈
                            events (ecc_bsc_prob_space n m p)
Proof
  rw[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
  >> (Cases_on ‘x’ >> gvs[event_state_takes_value_def])
QED

(* -------------------------------------------------------------------------- *)
(* The event that the state sequence takes a particular sequence of values is *)
(* a valid event in the space we are working in                               *)
(* -------------------------------------------------------------------------- *)
Theorem event_state_sequence_takes_value_is_event[simp]:
  ∀n m p ps qs ts σs.
    event_state_sequence_takes_value n m ps qs ts σs ∈
                                     events (ecc_bsc_prob_space n m p)
Proof
  rw[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
  >> (Cases_on ‘x’ >> Cases_on ‘σs’ >> gvs[event_state_sequence_takes_value_def]
      >> gvs[event_state_takes_value_def]
     )
QED

Theorem event_state_takes_value_disjoint[simp]:
  ∀n m ps qs ts i σ1 σ2.
    σ1 ≠ σ2 ⇒
    DISJOINT
    (event_state_takes_value n m ps qs ts i σ1)
    (event_state_takes_value n m ps qs ts i σ2)
Proof
  rw[]
  >> gvs[event_state_takes_value_def]
  >> gvs[DISJOINT_ALT]
  >> rw[]
  >> gvs[]
QED

Theorem event_state_sequence_takes_value_disjoint[simp]:
  ∀n m ps qs ts σs1 σs2.
    LENGTH σs1 = LENGTH σs2 ∧
    σs1 ≠ σs2 ⇒
    DISJOINT
    (event_state_sequence_takes_value n m ps qs ts σs1)
    (event_state_sequence_takes_value n m ps qs ts σs2)
Proof
  (* Induct on σs1 and split up σs2 to match *)
  Induct_on ‘σs1’ >> gvs[]
  >> rw[]
  >> Cases_on ‘σs2’ >> gvs[]
  (* Better naming *)
  >> qabbrev_tac ‘σ1 = h’ >> qpat_x_assum ‘Abbrev (σ1 = h)’ kall_tac
  >> qabbrev_tac ‘σ2 = h'’ >> qpat_x_assum ‘Abbrev (σ2 = h')’ kall_tac
  >> qabbrev_tac ‘σs2 = t’ >> qpat_x_assum ‘Abbrev (σs2 = t)’ kall_tac
  (* Expand out definition of event and alt definition of disjoint *)
  >> gvs[event_state_sequence_takes_value_def]
  >> gvs[DISJOINT_ALT]
  >> rw[]
  (* Split on the case of whether or not x is in the current state that is
     being inducted over and simplify *)
  >> Cases_on ‘x ∈ event_state_takes_value n m ps qs ts (LENGTH σs2) σ2’ >> gvs[]
  >> gvs[event_state_takes_value_def]
QED

(* -------------------------------------------------------------------------- *)
(* Add rewrites from this file                                                *)
(* -------------------------------------------------------------------------- *)
val ecc4_ss = ecc3_ss ++
              rewrites[length_n_state_sequences_finite,
                       event_state_sequence_takes_value_is_event,
                       event_state_takes_value_is_event,
                       event_state_takes_value_disjoint,
                       event_state_sequence_takes_value_disjoint
                      ]

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
(* Apply the law of total probability to the event where the sent string      *)
(* takes a particular value, to split the probability up according to what    *)
(* state sequence is observed. This makes it simpler to calculate, as it is   *)
(* helpful to know the state sequence in order to calculate the probability   *)
(* that the sent string takes a particular value.                             *)
(* -------------------------------------------------------------------------- *)
(* COMMENTED OUT BECAUSE WE ARE NO LONGER WORKING WITH THE SENT MAP DECODER 
Theorem ev_sent_law_total_prob_states:
  ∀n m p ps qs ts bs.
    0 ≤ p ∧ p ≤ 1 ⇒
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
  (* We're applying  *)
  >> qspecl_then [‘sp’,
                  ‘ev_sent’,
                  ‘event_state_sequence_takes_value n m ps qs ts’,
                  ‘S ∩ ’] assume_tac TOTAL_PROB_SIGMA
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> REVERSE conj_tac
  >- gvs[mul_comm]
  >> unabbrev_all_tac
  >> full_simp_tac ecc4_ss []
  >> rw[]
QED
*)

(* -------------------------------------------------------------------------- *)
(* TODO: simplify requirement on encoder outputting correct length for this   *)
(* special case                                                               *)
(*                                                                            *)
(* We assume that our parity equation is delayfree                            *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_encode_recursive_parity_equation:
  ∀ps qs ts n m p ds.
    let
      enc = encode_recursive_parity_equation (ps, qs) ts;
    in
      LAST ps ∧
      LENGTH ps = LENGTH ts + 1 ∧
      0 < p ∧ p < 1 ∧
      LENGTH ds = m ∧
      (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
      map_decoder_bitwise enc n m p ds =
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
