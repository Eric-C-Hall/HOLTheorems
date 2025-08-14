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
  event_state_takes_value n m (ps,qs) ts i σ = 
  {(bs, ns) | LENGTH bs = n ∧ LENGTH ns = m ∧
              encode_recursive_parity_equation_state (ps,qs) ts bs = σ
  }
End

(* -------------------------------------------------------------------------- *)
(* The event in which the states take a particular sequence of values         *)
(* -------------------------------------------------------------------------- *)
Definition event_state_sequence_takes_value_def:
  event_state_sequence_takes_value n m (ps,qs) ts σs =
  {(bs, ns) | bs, ns | LENGTH bs = n ∧
                       LENGTH ns = m ∧
                       encode_recursive_parity_equation_state_sequence
                       (ps,qs) ts bs = σs}
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
    event_state_takes_value n m (ps,qs) ts i σ ∈
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
    event_state_sequence_takes_value n m (ps,qs) ts σs ∈
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
    (event_state_takes_value n m (ps,qs) ts i σ1)
    (event_state_takes_value n m (ps,qs) ts i σ2)
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
    (event_state_sequence_takes_value n m (ps,qs) ts σs1)
    (event_state_sequence_takes_value n m (ps,qs) ts σs2)
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
  >> Cases_on ‘x ∈ event_state_takes_value n m (ps,qs) ts (LENGTH σs2) σ2’ >> gvs[]
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

Theorem encode_recursive_parity_equation_with_systematic_inj:
  ∀ps qs ts.
    INJ (encode_recursive_parity_equation_with_systematic (ps, qs) ts)
        𝕌(:bool list)
        𝕌(:bool list)
Proof
  rw[]
  >> gvs[INJ_DEF, encode_recursive_parity_equation_with_systematic_def]
  >> rpt gen_tac
  >> Cases_on ‘LENGTH x = LENGTH y’ >> gvs[]
  >- (DEP_PURE_ONCE_REWRITE_TAC[APPEND_LENGTH_EQ]
      >> rw[])
  >> rw[]
  >> ‘F’ suffices_by gvs[]
  >> qmatch_asmsub_abbrev_tac ‘LHS ++ x = RHS ++ y’
  >> ‘LENGTH (LHS ++ x) = LENGTH (RHS ++ y)’ by metis_tac[]
  >> qpat_x_assum ‘LHS ++ x = RHS ++ y’ kall_tac
  >> unabbrev_all_tac
  >> gvs[]
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
                        (event_state_sequence_takes_value n m (ps, qs) ts σs) *
              prob sp (event_state_sequence_takes_value n m (ps, qs) ts σs))
        {σs : (bool list) list | LENGTH σs = LENGTH bs ∧
                                 (∀σ. MEM σ σs ⇒ LENGTH σ = LENGTH ts)}
Proof
  rw[]
  >> qmatch_goalsub_abbrev_tac ‘prob sp (_ enc _ _ _) = ∑ _ S’
  >> qmatch_goalsub_abbrev_tac ‘prob sp ev_sent = _’
  (* We're applying  *)
  >> qspecl_then [‘sp’,
                  ‘ev_sent’,
                  ‘event_state_sequence_takes_value n m (ps, qs) ts’,
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
(* HERE, I WAS EXPLORING THE POSSIBILITY OF USING THE GENERAL MAP DECODER     *)
(* CODE TO HELP DO THE WORKING FOR THE CONVOLUTIONAL CODE MAP DECODER, BUT    *)
(* I THINK IT MIGHT ACTUALLY BE EASIER TO JUST WORK ON THE CONVOLUTIONAL CODE *)
(* MAP DECODER ITSELF.                                                        *)
(*                                                                            *)
(* Goal: map decoder is sum over p(σ_0) prod (sys_chan_prob nonsys_chan_prob  *)
(* sys_prior_prob transition_prob)                                            *)
(*                                                                            *)
(* Start 1: map decoder is sum over mass func of noise bxor encoded bitsting  *)
(* Alt 1:   - - - - - - - - - - - - cond prob of received string given input  *)
(*                                  string                                    *)
(*                                                                            *)
(* Sum out state: - - - - - - - - - cond prob of received string given input  *)
(*                                  string and state * cond prob of state     *)
(*                                  given input string                        *)
(*                                                                            *)
(* Possible improvement: Explore whether or not it is necessary to sum out    *)
(*                       the received string. Improve understanding as to why *)
(*                       this is done.                                        *)
(* Sum out sent string: - - - - - - cond prob of received string given input  *)
(*                      string and sent string and state * prob of state *    *)
(*                      prob of sent string.                                  *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* TODO: simplify requirement on encoder outputting correct length for this   *)
(* special case                                                               *)
(*                                                                            *)
(* We assume that our parity equation is delayfree                            *)
(* -------------------------------------------------------------------------- *)
(* COMMENTED OUT BECAUSE I WANT TO WORK WITH THE CONVOLUTIONAL CODE WITH
   SYSTEMATIC BITS RATHER THAN THE CONVOLUTIONAL CODE WITHOUT SYSTEMATIC BITS
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
QED*)

(* -------------------------------------------------------------------------- *)
(* General outline of plan of proof, following Chapter 6 of Modern Coding     *)
(* Theory:                                                                    *)
(*                                                                            *)
(* - MAP decoder = argmax p(b_s | ds)                                         *)
(*               = argmax Σ p(bs, cs_p, σs | ds) over bs, cs_p, σs            *)
(*               = argmax Σ p(ds | bs, cs_p, σs) p(bs, cs_p, σs) over ''      *)
(*   p(bs, cs_p, σs) = p(σ_0)p(b_1)p(c_1_p,σ_1|b_1,σ_0)p(b_2)                 *)
(*                       p(c_2_p,σ_2|b_2,σ_1)p(b_3)p(c_3_p,σ_3|b_3,σ_2)...    *)
(*   p(ds | bs, cs_p, σs) = Π P(d_i | c_i)                                    *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* A version of PROB_EMPTY which has been added to the stateful simpset       *)
(* -------------------------------------------------------------------------- *)
Theorem PROB_EMPTY_STATEFUL_SIMPSET[simp]:
  ∀p. prob_space p ⇒ prob p ∅ = 0
Proof
  gvs[PROB_EMPTY]
QED

(* -------------------------------------------------------------------------- *)
(* I'm surprised this theorem doesn't exist yet. Perhaps it could be added?   *)
(* -------------------------------------------------------------------------- *)
Theorem INTER_DIFF[simp]:
  ∀S T.
    S ∩ (S DIFF T) = S DIFF T
Proof
  ASM_SET_TAC[]
QED

Theorem INTER_INTER_L[simp]:
  ∀S T.
    S ∩ S ∩ T = S ∩ T
Proof
  ASM_SET_TAC[]
QED

Theorem INTER_INTER_R[simp]:
  ∀S T.
    S ∩ T ∩ T = S ∩ T
Proof
  ASM_SET_TAC[]
QED

Theorem COND_PROB_INTER_ID:
  ∀sp e1 e2.
    prob_space sp ∧
    e1 INTER e2 IN events sp ∧ 
    e2 IN events sp ==>
    cond_prob sp (e1 INTER e2) e2 = cond_prob sp e1 e2
Proof
  rw[]
  >> gvs[cond_prob_def]
QED

(* -------------------------------------------------------------------------- *)
(* A simpler version of COND_PROB_EXTREAL_SUM_IMAGE_FN which is easier to     *)
(* prove. In particular, this one requires us to know that                    *)
(* p ⊆ BIGUNION (IMAGE f s), which is a stronger condition than              *)
(* e2 ⊆ BIGUNION (IMAGE f s)                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem COND_PROB_EXTREAL_SUM_IMAGE_FN_SIMPLE:
  ∀p f e1 e2 s.
    prob_space p ∧
    e1 ∈ events p ∧
    e2 ∈ events p ∧
    prob p e2 ≠ 0 ∧
    (∀x. x ∈ s ⇒ e1 ∩ f x ∈ events p) ∧
    FINITE s ∧
    (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (f x) (f y)) ∧
    p_space p ⊆ BIGUNION (IMAGE f s) ⇒
    cond_prob p e1 e2 = ∑ (λx. cond_prob p (e1 ∩ f x) e2) s
Proof
  rw[]
  >> sg ‘e1 = BIGUNION (IMAGE (λx. e1 ∩ f x) s)’
  >- (rw[BIGUNION_IMAGE]
      >> rw[EXTENSION] 
      >> EQ_TAC >> rw[] >> gvs[]
      >> gvs[GSYM SUBSET_INTER_ABSORPTION, INTER_COMM]
      >> gvs[SUBSET_DEF]
      >> last_x_assum $ qspec_then ‘x’ assume_tac
      >> sg ‘x ∈ p_space p’
      >- (irule PROB_SPACE_IN_PSPACE
          >> metis_tac[]
         )
      >> gvs[]
      >> metis_tac[]
     )
  >> qmatch_goalsub_abbrev_tac ‘_ = RHS’
  >> qpat_x_assum ‘e1 = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> DEP_PURE_ONCE_REWRITE_TAC[cond_prob_additive_finite]
  >> gvs[]
  >> rw[]
  >> simp[DISJOINT_ALT]
  >> rw[]
  >> last_x_assum $ qspecl_then [‘x’, ‘x'’] assume_tac
  >> gvs[]
  >> gvs[DISJOINT_ALT]
QED

(* -------------------------------------------------------------------------- *)
(* A version of PROB_EXTREAL_SUM_IMAGE_FN for conditional probabilities       *)
(* -------------------------------------------------------------------------- *)
Theorem COND_PROB_EXTREAL_SUM_IMAGE_FN:
  ∀p f e1 e2 s.
    prob_space p ∧
    e1 ∈ events p ∧
    e2 ∈ events p ∧
    prob p e2 ≠ 0 ∧
    (∀x. x ∈ s ⇒ e1 ∩ f x ∈ events p) ∧
    FINITE s ∧
    (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (f x) (f y)) ∧
    e1 ∩ e2 ⊆ BIGUNION (IMAGE f s) ⇒
    cond_prob p e1 e2 = ∑ (λx. cond_prob p (e1 ∩ f x) e2) s
Proof
  rw[]
  (* Choose a specific choice of f x, that is, choose some in s *)
  >> REVERSE $ Cases_on ‘∃x. x ∈ s’
  >- (Cases_on ‘s’ >> gvs[]
      >- gvs[cond_prob_def, zero_div]
      >> metis_tac[]
     )
  >> gvs[]
  (* Consider the function f which has first been restricted to e1 ∩ e2, and
     then all the elements of the probability space which are not in e1 ∩ e2
     have been added to the choice of f x which was made before.
.     
     This maintains the fact that the e1 ∩ f x are events, maintains the
     disjointedness of the f x, maintains the value of the conditional
     probability of e1 ∩ f x, and strengthens from knowing that e1 ∩ e2 is in
     the BIGUNION of the choices of f x to knowing that p_space p is in the
     BIGUNION of the choices of f x.
.
     Thus, we can apply the simple version of this theorem to this function.
   *)
  >> qspecl_then [‘p’, ‘λy. if y = x
                            then (f y ∩ (e1 ∩ e2)) ∪ ((p_space p) DIFF (e1 ∩ e2))
                            else f y ∩ (e1 ∩ e2)’, ‘e1’, ‘e2’, ‘s’] assume_tac COND_PROB_EXTREAL_SUM_IMAGE_FN_SIMPLE
  (* Apply this version of the theorem *)
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  (* Simplify *)
  >> rpt conj_tac
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  (* f x is still an event*)
  >- (rw[]
      >- (gvs[UNION_OVER_INTER]
          >> irule EVENTS_UNION
          >> rw[]
          >- (PURE_ONCE_REWRITE_TAC[INTER_ASSOC]
              >> irule EVENTS_INTER >> gvs[]
              >> irule EVENTS_INTER >> gvs[])
          >> irule EVENTS_INTER >> gvs[]
          >> irule EVENTS_COMPL >> gvs[]
          >> irule EVENTS_INTER >> gvs[]
         )
      >> gvs[INTER_ASSOC]
      >> irule EVENTS_INTER >> gvs[]
      >> irule EVENTS_INTER >> gvs[]
     )
  >- simp[]
  (* f x is still disjoint *)
  >- (qx_gen_tac ‘y1’
      >> qx_gen_tac ‘y2’
      >> strip_tac
      >> PURE_REWRITE_TAC[DISJOINT_ALT]
      >> qx_gen_tac ‘n’
      >> gvs[]
      >> disch_tac
      (* - x is the special element we chose which is used to determine
         which set has had all the stuff added to it
         - y1 is the current index of the first f x we are testing for
           disjointedness of
         - y2 is the current index of the second f x we are testing for
           disjointedness of (with respect to the first)
         - n is the current element we are testing for whether or not it is in
           each of the sets *)
      (* Choose the appropriate indices for disjointedness in our assumption *)
      >> first_x_assum $ qspecl_then [‘y1’, ‘y2’] assume_tac
      >> gvs[]
      (* In the case where the first f x is the special one which has had all
         the additional stuff added to it: *)
      >> Cases_on ‘y1 = x’
      >- gvs[DISJOINT_ALT]
      >> Cases_on ‘y2 = x’
      >- gvs[DISJOINT_ALT]
      >> gvs[DISJOINT_ALT]
     )
  (* p_space p is contained in the BIGUNION of the new f x*)
  >- (simp[BIGUNION_IMAGE]
      >> gvs[SUBSET_DEF]
      >> qx_gen_tac ‘n’
      >> rw[]
      (* We want to choose the f y that our point n is contained in.
         This depends on whether n is in e1 ∩ e2. If it isn't in e1 ∩ e2, then
         it'll always be in f x for the special choice of x we made earlier *)
      >> Cases_on ‘n ∉ e1 ∩ e2’
      >- (qexists ‘x’
          >> gvs[]
         )
      (* If it is in e1 ∩ e2, then it'll be in the same choice of f x as it
         used to be before the meaning of f was changed. *)
      >> last_x_assum $ qspec_then ‘n’ assume_tac
      >> gvs[]
      >> qexists ‘x'’
      >> gvs[]
      >> rw[]
      >> gvs[]
     )
  (* The sum we arrive at after applying the simplified version of this theorem
     is equivalent to the sum in the more general version of this theorem. *)
  >> irule EXTREAL_SUM_IMAGE_EQ'
  >> rw[]
  (* Use the fact that the conditional probability will constrict the top
       probability by the event we are conditioning on *)
  >> (gvs[cond_prob_def]
      >> qmatch_goalsub_abbrev_tac ‘prob _ S1 / _ = prob _ S2 / _’
      >> ‘S1 = S2’ suffices_by gvs[]
      >> unabbrev_all_tac
      >> ASM_SET_TAC[]
     )
QED

(* -------------------------------------------------------------------------- *)
(* MDR stands for MAP Decoder Recursive, i.e. relating to the MAP decoder for *)
(* recursive convolutional codes.                                             *)
(*                                                                            *)
(* This contains the summed out values when finding the factored form of      *)
(* the MAP decoder for recursive convolutional codes.                         *)
(*                                                                            *)
(* ps: the numerator parity equation                                          *)
(* qs: the denominator parity equation                                        *)
(* n: the size of the input                                                   *)
(* ts: the initial state                                                      *)
(* i: the index of the variable which does not need to be summed out because  *)
(*    it already has a value                                                  *)
(* x: the value of the variable which does not need to be summed out          *)
(* -------------------------------------------------------------------------- *)
Definition mdr_summed_out_values_def:
  mdr_summed_out_values (ps,qs) n ts i x =
  {(bs, σs, cs_p) | LENGTH bs = n ∧
                    EL i bs = x ∧
                    σs = encode_recursive_parity_equation_state_sequence (ps,qs) ts bs ∧
                    cs_p = encode_recursive_parity_equation (ps,qs) ts bs
                     }
End

(* -------------------------------------------------------------------------- *)
(* An alternate form of mdr_summed_out_values which is written using a MAP    *)
(* -------------------------------------------------------------------------- *)
Theorem mdr_summed_out_values_alt:
  ∀ps qs n ts i x.
    mdr_summed_out_values (ps,qs) n ts i x =
    IMAGE (λbs. (bs,
                 encode_recursive_parity_equation_state_sequence (ps,qs) ts bs,
                 encode_recursive_parity_equation (ps,qs) ts bs))
          (length_n_codes n ∩ ith_eq_codes i x)
Proof
  gvs[mdr_summed_out_values_def]
  >> ASM_SET_TAC[]
QED

Theorem finite_mdr_summed_out_values[simp]:
  ∀ps qs n ts i x.
    FINITE (mdr_summed_out_values (ps,qs) n ts i x)
Proof
  rw[mdr_summed_out_values_alt]
QED

(* -------------------------------------------------------------------------- *)
(* This contains the events we sum over when finding the factored form of the *)
(* MAP decoder for convolutional codes.                                       *)
(*                                                                            *)
(* ps: the numerator parity equation                                          *)
(* qs: the denominator parity equation                                        *)
(* n: the length of the input of the encoder                                  *)
(* m: the length of the output of the encoder                                 *)
(* ts: the initial state                                                      *)
(*                                                                            *)
(* We sum over various choices of bs, σs, and cs_p                            *)
(* -------------------------------------------------------------------------- *)
Definition mdr_summed_out_events_def:
  mdr_summed_out_events (ps,qs) n m ts (bs, σs, cs_p) =
  (event_input_string_takes_value n m bs)
  ∩ (event_state_sequence_takes_value n m (ps,qs) ts σs)
  ∩ (event_sent_string_takes_value 
     (encode_recursive_parity_equation (ps, qs) ts)
     n m cs_p)
End

Theorem mdr_summed_out_events_is_event[simp]:
  ∀psqs n m p ts bsσscs_p.
    mdr_summed_out_events psqs n m ts bsσscs_p
                          ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[]
  >> namedCases_on ‘psqs’ ["ps qs"]
  >> namedCases_on ‘bsσscs_p’ ["bs σs cs_p"]
  >> rw[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
  >> gvs[mdr_summed_out_events_def,
         event_input_string_takes_value_def]
QED

(* Possible improvement: can we remove some of these assumptions, especially
   LENGTH ps = LENGTH ts + 1?*)
Theorem map_decoder_bitwise_encode_recursive_parity_equation_with_systematic:
  ∀ps qs ts n m p ds.
    let
      enc = encode_recursive_parity_equation_with_systematic (ps, qs) ts;
    in
      0 < p ∧ p < 1 ∧
      LENGTH ds = m ∧
      LENGTH ps = LENGTH ts + 1 ∧
      (∀bs. LENGTH bs = n ⇒ LENGTH (enc bs) = m) ⇒
      map_decoder_bitwise enc n m p ds =
      MAP (λi.
             argmax_bool
             (λx. ∑ ARB (mdr_summed_out_values (ps,qs) n ts i x)
             )
          )
          (COUNT_LIST n)
Proof
  rw[]
  (* More standard properties showing that p represents a probability *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[lt_le]
  (* Definition of bitwise decoder *)
  >> gvs[map_decoder_bitwise_def]
  (* We care about the inside of the MAP *)
  >> rw[MAP_EQ_f]
  >> gvs[MEM_COUNT_LIST]
  (* The function in argmax_bool differs by a multiplicative constant *)
  >> irule argmax_bool_mul_const
  (* *)
  >> qexists ‘ARB’
  (* *)
  >> conj_tac >- cheat
  >> REVERSE conj_tac >- cheat
  (* Prove function equivalence when applied to all choices of x *)
  >> rw[FUN_EQ_THM]
  (* For some reason, as I edited the theorem I was proving, this swapped
     around*)
  >> irule EQ_SYM
  (* Nicer names *)
  >> qmatch_abbrev_tac ‘C * cond_prob sp e1 e2 = RHS’
  (* We are at the stage p(b_s | ds). Take a sum over σs, cs_p, and the
      remaining elements of bs *)
  >> qspecl_then [‘sp’,
                  ‘mdr_summed_out_events (ps,qs) n (LENGTH ds) ts’,
                  ‘e1’,
                  ‘e2’,
                  ‘mdr_summed_out_values (ps,qs) n ts i x’] assume_tac COND_PROB_EXTREAL_SUM_IMAGE_FN
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> rpt conj_tac >> unabbrev_all_tac
  >- gvs[]
  >- gvs[]
  >- gvs[]
  >- gvs[]
  (* The new intersection of events is an event *)
  >- (rw[mdr_summed_out_values_def]
      >> unabbrev_all_tac
      >> irule EVENTS_INTER >> gvs[]
     )
  >- gvs[]
  (* The new events are disjoint *)
  >- (all_tac
      (* i1: index of first disjoint set
         i2: index of second disjoint set *)
      >> qx_gen_tac ‘i1’
      >> qx_gen_tac ‘i2’
      >> strip_tac
      (* Alternate definition of disjoint *)
      >> simp[DISJOINT_ALT]
      (* y: element which should not be in the other disjoint set if it is in
            the first disjoint set *)
      >> qx_gen_tac ‘y’
      >> rw[]
      (* Give good names to the components of the indexes *)
      >> namedCases_on ‘i1’ ["bs1 σs1 cs1_p"]
      >> namedCases_on ‘i2’ ["bs2 σs2 cs2_p"]
      >> gvs[]
      (* If bs1 ≠ bs2, then the first part is disjoint *)
      >> Cases_on ‘bs1 ≠ bs2’
      >- gvs[mdr_summed_out_events_def, event_input_string_takes_value_def]
      >> gvs[]
      (* If σs1 ≠ σs2, then the next part is disjoint *)
      >> Cases_on ‘σs1 ≠ σs2’
      >- gvs[mdr_summed_out_events_def, event_state_sequence_takes_value_def]
      >> gvs[]
      (* We have cs1_p ≠ cs2_p, and so the final part is disjoint *)
      >> gvs[mdr_summed_out_events_def, event_sent_string_takes_value_def]
     )
  >- (PURE_REWRITE_TAC[BIGUNION_IMAGE]
      >> gvs[SUBSET_DEF]
      >> qx_gen_tac ‘y’
      >> rw[]
      (* Apply event_received_string_takes_value_def to assumption *)
      >> pop_assum (fn th => assume_tac (SIMP_RULE bool_ss [event_received_string_takes_value_def] th))
      >> gs[]
      >> qexists ‘(bs,
                   encode_recursive_parity_equation_state_sequence (ps,qs) ts bs,
                   encode_recursive_parity_equation (ps,qs) ts bs)’
      >> gs[]
      >> rpt conj_tac
      >- (gs[mdr_summed_out_values_def]
          >> gs[event_input_bit_takes_value_def]
         )
      >> gs[mdr_summed_out_events_def,
            event_input_string_takes_value_def,
            event_state_sequence_takes_value_def,
            event_sent_string_takes_value_def]
     )
  (* Move the constant into the sum *)
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_CMUL_ALT]
  >> conj_tac
  >- (rpt conj_tac
      >- gvs[]
      >- cheat
      >- cheat
      >> disj2_tac
      >> rw[]
      >> irule (cj 1 COND_PROB_FINITE)
      >> gvs[]
      >> irule EVENTS_INTER >> gvs[]
      >> namedCases_on ‘x'’ ["bs σs cs_p"]
      >> gvs[]
      >> irule EVENTS_INTER >> gvs[]
      >> irule EVENTS_INTER >> gvs[]
     )
  (* The function in the sum is the equivalent bit *)
  >> irule EXTREAL_SUM_IMAGE_EQ'
  >> gvs[]
  >> qx_gen_tac ‘w’
  >> rw[]
  (* We are currently up to the step
     argmax Σ p(bs, cs_p, σs | ds) over bs, cs_p, σs.
     Next step:
     argmax Σ p(ds | bs, cs_p, σs) p(bs, cs_p, σs) over ''
.
     That is, we apply Bayes' rule here
   *)
  >> DEP_PURE_ONCE_REWRITE_TAC[BAYES_RULE]
  >> conj_tac
  >- (rpt conj_tac
      >- gvs[]
      >- gvs[]
      >- (irule EVENTS_INTER >> gvs[]
          >> namedCases_on ‘w’ ["bs σs cs_p"] >> gvs[]
         )
      >- gvs[]
      >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
      >> conj_tac
      >- (gvs[]
          >> irule EVENTS_INTER >> gvs[]
         )

                                  
                                  
QED

val _ = export_theory();

