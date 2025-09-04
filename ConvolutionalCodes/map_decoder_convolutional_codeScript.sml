(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "map_decoder_convolutional_code";

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
  {(bs : bool list, ns : bool list) | LENGTH bs = n ∧
                                      LENGTH ns = m ∧
                                      encode_recursive_parity_equation_state
                                      (ps,qs) ts bs = σ
  }
End

(* -------------------------------------------------------------------------- *)
(* The event in which the states take a particular sequence of values         *)
(* -------------------------------------------------------------------------- *)
Definition event_state_sequence_starts_with_def:
  event_state_sequence_starts_with n m (ps,qs) ts σs =
  {(bs : bool list, ns : bool list) |
  bs, ns | LENGTH bs = n ∧
           LENGTH ns = m ∧
           σs ≼ encode_recursive_parity_equation_state_sequence (ps,qs) ts bs}
End

Overload length_n_state_sequences = “λn. {σs : bool list list | LENGTH σs = n}”;

(* TODO: This only includes one requirement for validity. A valid sequence will
         also require, for example, each state to be reachable from the
         previous. So I should probably rename this to something *)
Overload valid_state_sequences = “λn. {σs : bool list list | ∀σ. MEM σ σs ⇒
                                                                 LENGTH σ = n}”;

Overload length_n_valid_state_sequences =
“λn l. {σs : bool list list | LENGTH σs = n ∧ (∀σ. MEM σ σs ⇒ LENGTH σ = l)}”

(* Maybe give this a less generic name to avoid conflicts? *)
Overload event_universal =
“λn m. {(bs : bool list, ns : bool list) | LENGTH bs = n ∧ LENGTH ns = m}”
    
(* I'm no longer sure that it's better to treat these components separately,
v  because finiteness of the set only holds when both components are present. *)
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
Theorem event_state_sequence_starts_with_is_event[simp]:
  ∀n m p ps qs ts σs.
    event_state_sequence_starts_with n m (ps,qs) ts σs ∈
                                     events (ecc_bsc_prob_space n m p)
Proof
  rw[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
  >> (Cases_on ‘x’ >> Cases_on ‘σs’ >> gvs[event_state_sequence_starts_with_def]
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

Theorem event_state_sequence_starts_with_disjoint[simp]:
  ∀n m ps qs ts σs1 σs2.
    LENGTH σs1 = LENGTH σs2 ∧
    σs1 ≠ σs2 ⇒
    DISJOINT
    (event_state_sequence_starts_with n m (ps,qs) ts σs1)
    (event_state_sequence_starts_with n m (ps,qs) ts σs2)
Proof
  (* Rewrite definition of DISJOINT into more usable form *)
  rw[]
  >> gvs[DISJOINT_ALT]
  >> rw[]
  >> CCONTR_TAC
  >> gvs[]
  (* Use definition of event_state_sequence_starts_with *)
  >> gvs[event_state_sequence_starts_with_def]
  (* Property follows from basic properties of prefixes *)
  >> metis_tac[IS_PREFIX_EQ_REWRITE]
QED

(* -------------------------------------------------------------------------- *)
(* Add rewrites from this file                                                *)
(* -------------------------------------------------------------------------- *)
val ecc4_ss = ecc3_ss ++
              rewrites[length_n_state_sequences_finite,
                       event_state_sequence_starts_with_is_event,
                       event_state_takes_value_is_event,
                       event_state_takes_value_disjoint,
                       event_state_sequence_starts_with_disjoint
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
      ev_sent = event_sent_string_starts_with enc n m (enc bs);
    in
      prob sp ev_sent =
      ∑ (λσs. cond_prob sp ev_sent
                        (event_state_sequence_starts_with n m (ps, qs) ts σs) *
              prob sp (event_state_sequence_starts_with n m (ps, qs) ts σs))
        {σs : (bool list) list | LENGTH σs = LENGTH bs ∧
                                 (∀σ. MEM σ σs ⇒ LENGTH σ = LENGTH ts)}
Proof
  rw[]
  >> qmatch_goalsub_abbrev_tac ‘prob sp (_ enc _ _ _) = ∑ _ S’
  >> qmatch_goalsub_abbrev_tac ‘prob sp ev_sent = _’
  (* We're applying  *)
  >> qspecl_then [‘sp’,
                  ‘ev_sent’,
                  ‘event_state_sequence_starts_with n m (ps, qs) ts’,
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
(* p_space p ⊆ BIGUNION (IMAGE f s), which is a stronger condition than      *)
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
(* An alternate form of mdr_summed_out_values which uses an IMAGE             *)
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

(* -------------------------------------------------------------------------- *)
(* A more accurate version of the values that are summed out: we sum out all  *)
(* variables other than the one which has been chosen for the ith input       *)
(*                                                                            *)
(* ps: the numerator parity equation                                          *)
(* qs: the denominator parity equation                                        *)
(* n: the size of the input                                                   *)
(* ts: the initial state                                                      *)
(* i: the index of the variable which does not need to be summed out because  *)
(*    it already has a value                                                  *)
(* x: the value of the variable which does not need to be summed out          *)
(* -------------------------------------------------------------------------- *)
Definition mdr_summed_out_values_2_def:
  mdr_summed_out_values_2 n ts i x =
  (length_n_codes n ∩ ith_eq_codes i x)
  × (length_n_valid_state_sequences (n + 1) (LENGTH ts))
  × (length_n_codes n)
End

(* -------------------------------------------------------------------------- *)
(* An alternative form of mdr_summed_out_values_2 which is expressed as a     *)
(* product of sets.                                                           *)
(*                                                                            *)
(* Note: if this is used as the definition, then our definition has a wider   *)
(* range of allowable types, which causes issues when we want to apply the    *)
(* other definition but we don't know that we have the appropriate types.     *)
(* -------------------------------------------------------------------------- *)
Theorem mdr_summed_out_values_2_alt:
  ∀n ts i x.
    mdr_summed_out_values_2 n ts i x =
    {(bs, σs, cs_p) | LENGTH bs = n ∧
                      LENGTH σs = n + 1 ∧
                      (∀σ. MEM σ σs ⇒ LENGTH σ = LENGTH ts) ∧
                      LENGTH cs_p = n ∧
                      EL i bs = x}
Proof
  rw[mdr_summed_out_values_2_def, CROSS_DEF]
  >> ASM_SET_TAC[]
QED

(* -------------------------------------------------------------------------- *)
(* Contains all values that are being summed out when using the factor graph  *)
(* method for MAP decoding of recursive convolutional codes                   *)
(*                                                                            *)
(* n: the size of the input to the encoder                                    *)
(* ts: the intial state of the encoder                                        *)
(* -------------------------------------------------------------------------- *)
Definition mdr_summed_out_values_complete_def:
  mdr_summed_out_values_complete n ts =
  (length_n_codes n)
  × (length_n_valid_state_sequences (n + 1) (LENGTH ts))
  × (length_n_codes n)
End

(* -------------------------------------------------------------------------- *)
(* An alternative form of mdr_summed_out_values_complete which is expressed   *)
(* as a product of sets                                                       *)
(*                                                                            *)
(* Note: if this is used as the definition, then our definition has a wider   *)
(* range of allowable types, which causes issues when we want to apply the    *)
(* other definition but we don't know that we have the appropriate types.     *)
(* -------------------------------------------------------------------------- *)
Theorem mdr_summed_out_values_complete_alt:
  ∀n ts.
    mdr_summed_out_values_complete n ts =
    {(bs, σs, cs_p) | LENGTH bs = n ∧
                      LENGTH σs = n + 1 ∧
                      (∀σ. MEM σ σs ⇒ LENGTH σ = LENGTH ts) ∧
                      LENGTH cs_p = n}
Proof
  rw[mdr_summed_out_values_complete_def, CROSS_DEF]
  >> ASM_SET_TAC[]
QED

(* -------------------------------------------------------------------------- *)
(* The event that the parity bits for a systematic recursive convolutional    *)
(* code (with one parity equation) start with a certain prefix.               *)
(*                                                                            *)
(* ps: the numerator parity equation                                          *)
(* qs: the denominator parity equation                                        *)
(* n: the input length                                                        *)
(* m: the output length for the systematic recursive convolutional code       *)
(*    (this will be equal to 2*n based on how the srcc works)                 *)
(* ts: the initial state for the systematic recursive convolutional code      *)
(* cs_p: the value we are expecting the parity bits to take (we have          *)
(*       bs = input bits -> cs = sent bits -> ds = received bits, and the     *)
(*       underscore p represents the fact that these are the parity bits and  *)
(*       not the systematic bits.)                                            *)
(* -------------------------------------------------------------------------- *)
Definition event_srcc_parity_string_starts_with_def:
  event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p =
  {(bs, ns) | LENGTH bs = n ∧
              LENGTH ns = m ∧
              cs_p ≼ encode_recursive_parity_equation (ps,qs) ts bs }
End

(* -------------------------------------------------------------------------- *)
(* The event that a single parity bit for a systematic recursive              *)
(* convolutional code (with one parity equation) takes a certain value.       *)
(* -------------------------------------------------------------------------- *)
Definition event_srcc_parity_bit_takes_value_def:
  event_srcc_parity_bit_takes_value (ps,qs) n m ts i c_p =
  {(bs, ns) | LENGTH bs = n ∧
              LENGTH ns = m ∧
              EL i (encode_recursive_parity_equation (ps,qs) ts bs) = c_p}
End

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
  (event_input_string_starts_with n m bs)
  ∩ (event_state_sequence_starts_with n m (ps,qs) ts σs)
  ∩ (event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p)
End

(* -------------------------------------------------------------------------- *)
(* These intersection theorems are only helpful if we don't know that our     *)
(* encoding function is injective, because otherwise we could simply use the  *)
(* fact that, for example, a particular input string corresponds exactly to   *)
(* a particular state sequence.                                               *)
(* -------------------------------------------------------------------------- *)

(* Should this be a simp rule, or is it wiser to avoid it being a simp rule
   because in some situations one event will be more useful and in other
   situations the other event will be more useful? *)
(* Possible improvement: update this to better work with change where we now
   use the event that the input starts with a prefix rather than the event that
   the input is precisely equal to a value. This involves removing assumption
   on length of bs. *)
Theorem inter_input_state_sequence_eq_input:
  ∀n m ps qs ts bs σs.
    LENGTH bs = n ∧
    σs = encode_recursive_parity_equation_state_sequence (ps,qs) ts bs ⇒
    (event_input_string_starts_with n m bs)
    ∩ (event_state_sequence_starts_with n m (ps,qs) ts σs) =
    event_input_string_starts_with n m bs
Proof
  rw[]
  >> gvs[event_input_string_starts_with_def,
         event_state_sequence_starts_with_def]
  >> rw[EXTENSION] >> EQ_TAC >> rw[] >> gvs[TAKE_LENGTH_ID_rwt]
  >> metis_tac[IS_PREFIX_LENGTH_ANTI]
QED

Theorem DROP_ALL_BUT_ONE:
  ∀bs.
    bs ≠ [] ⇒
    DROP (LENGTH bs - 1) bs = [LAST bs]
Proof
  Induct_on ‘bs’ >> rw[]
  >> rw[LAST_DEF]
  >> gvs[]
  >> Cases_on ‘LENGTH bs’ >> gvs[DROP]
QED

Theorem encode_recursive_parity_equation_prefix_mono:
  ∀ps qs ts bs bs'.
    bs ≼ bs' ⇒
    ((encode_recursive_parity_equation (ps,qs) ts bs)
     ≼ encode_recursive_parity_equation (ps,qs) ts bs')
Proof
  Induct_on ‘bs’ >> Cases_on ‘bs'’ >> rw[encode_recursive_parity_equation_def]
QED

Theorem encode_recursive_parity_equation_prefix_inj:
  ∀ps qs ts bs bs'.
    LAST ps ∧
    LENGTH ps = LENGTH ts + 1 ⇒
    (bs ≼ bs' ⇔
       ((encode_recursive_parity_equation (ps,qs) ts bs)
        ≼ encode_recursive_parity_equation (ps,qs) ts bs'))
Proof
  Induct_on ‘bs’ >> Cases_on ‘bs'’ >> rw[encode_recursive_parity_equation_def]
  >> EQ_TAC >- gvs[encode_recursive_parity_equation_prefix_mono]
  (* If enc bs ≼ enc bs', then bs ≼ bs' *)
  >> disch_tac >> gvs[]                     
  (* Inductive step: a single element at the front must be equal, because the
     front element of the output is equal, and since the last element of ps is
     true. This will also be helpful to know when proving that the tail is a
     prefix, because it means we know we'll be starting from the same state
     after reading h' as we would be after reading h. *)
  >> sg ‘h' ⇔ h’
  >- (gvs[apply_parity_equation_append]
      >> sg ‘DROP (LENGTH ts) ps = [LAST ps]’
      >- (gvs[]
          >> ‘LENGTH ts = LENGTH ps - 1’ by gvs[]
          >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
          >> Cases_on ‘ps = []’ >- gvs[]
          >> simp[DROP_ALL_BUT_ONE]
         )
      >> pop_assum (fn th => gvs[th])
      >> gvs[apply_parity_equation_def]
      >> qmatch_asmsub_abbrev_tac ‘(b1 ⇔ (b2 ⇎ h')) ⇔ (b1 ⇔ (b2 ⇎ h))’
      (* h' ⇔ h directly follows from (b1 ⇔ (b2 ⇎ h')) ⇔ (b1 ⇔ (b2 ⇎ h))
         using basic, automatically evaluable logic *)
      >> metis_tac[]
     )
  >> gvs[]
  (* By the inductive hypothesis, the tail must be a prefix, too *)
  >> qmatch_asmsub_abbrev_tac ‘encode_recursive_parity_equation (ps,qs) ts2 bs’
  >> ‘LENGTH ps = LENGTH ts2 + 1’ by gvs[Abbr ‘ts2’, LENGTH_TL]
  >> metis_tac[]
QED

Theorem IS_PREFIX_APPEND_FIRST:
  ∀l1 k1 l2 k2.
    LENGTH l1 ≤ LENGTH l2 ∧
    l1 ++ k1 ≼ l2 ++ k2 ⇒
    l1 ≼ l2
Proof
  Induct_on ‘l1’ >> Cases_on ‘l2’ >> rw[]
  >> metis_tac[]
QED

Theorem IS_PREFIX_APPEND_SECOND:
  ∀l1 k1 l2 k2.
    LENGTH l1 = LENGTH l2 ∧
    l1 ++ k1 ≼ l2 ++ k2 ⇒
    l1 = l2 ∧ k1 ≼ k2
Proof
  Induct_on ‘l1’ >> Cases_on ‘l2’ >> rw[]
  >> metis_tac[]
QED

(* Possible improvement: update this to better work with change where we now
   use the event that the input starts with a prefix rather than the event that
   the input is precisely equal to a value. This involves removing assumption
   on length of bs. *)
Theorem inter_input_parity_eq_sent:
  ∀n m ps qs ts bs cs_p.
    LENGTH bs = n ∧
    cs_p = encode_recursive_parity_equation (ps,qs) ts bs ⇒
    (event_input_string_starts_with n m bs)
    ∩ (event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p) =
    event_sent_string_starts_with
    (encode_recursive_parity_equation_with_systematic (ps,qs) ts) n m
    (encode_recursive_parity_equation_with_systematic (ps,qs) ts bs)
Proof
  rw[]
  >> gvs[event_input_string_starts_with_def,
         event_srcc_parity_string_starts_with_def,
         event_sent_string_starts_with_def]
  >> gvs[encode_recursive_parity_equation_with_systematic_def]
  >> rw[EXTENSION] >> EQ_TAC >> rw[]
  >- metis_tac[IS_PREFIX_LENGTH_ANTI]
  >- metis_tac[IS_PREFIX_APPEND_SECOND,
               encode_recursive_parity_equation_length]
  >> metis_tac[IS_PREFIX_APPEND_SECOND,
               encode_recursive_parity_equation_length,
               encode_recursive_parity_equation_prefix_mono]
QED

(* Possible improvement: remove requirement that LENGTH bs = n *)
Theorem inter_input_bit_sent_eq_sent:
  ∀enc n m psqs t bs i x.
    LENGTH bs = n ∧
    (∀xs ys. enc xs ≼ enc ys ⇔ xs ≼ ys) ∧
    EL i bs = x ⇒
    (event_input_bit_takes_value n m i x)
    ∩ (event_sent_string_starts_with enc n m (enc bs)) =
    event_sent_string_starts_with enc n m (enc bs)
Proof
  rw[]
  >> gvs[GSYM event_input_string_starts_with_event_sent_string_starts_with]
  >> gvs[event_input_bit_takes_value_def, event_input_string_starts_with_def]
  >> rw[EXTENSION] >> EQ_TAC >> rw[] >> metis_tac[IS_PREFIX_LENGTH_ANTI]
QED

Theorem event_srcc_parity_string_starts_with_is_event[simp]:
  ∀psqs n m p ts cs_p.
    event_srcc_parity_string_starts_with psqs n m ts cs_p
                                         ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[]
  >> gvs[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
  >> namedCases_on ‘psqs’ ["ps qs"] >> rw[event_srcc_parity_string_starts_with_def]
  >> gvs[]
QED

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
         event_input_string_starts_with_def]
QED

(* -------------------------------------------------------------------------- *)
(* A correspondence between the input string taking a particular value and    *)
(* the state sequence taking the sequence of values corresponding to that     *)
(* input.                                                                     *)
(* -------------------------------------------------------------------------- *)
(*Theorem event_input_string_starts_with_event_state_sequence_starts_with:
  ∀.
    event_input_string_starts_with n m bs
Proof
QED*)

Theorem mdr_summed_out_values_subset_mdr_summed_out_values_complete:
  ∀ps qs n ts i x.
    (mdr_summed_out_values (ps,qs) n ts i x) ⊆ (mdr_summed_out_values_complete n ts)
Proof
  gvs[mdr_summed_out_values_def, mdr_summed_out_values_complete_alt]
  >> rw[SUBSET_DEF]
  >> rw[]
  >> metis_tac[mem_encode_recursive_parity_equation_state_sequence_length]
QED

Theorem finite_mdr_summed_out_values[simp]:
  ∀ps qs n ts i x.
    FINITE (mdr_summed_out_values (ps,qs) n ts i x)
Proof
  rw[mdr_summed_out_values_alt]
QED

Theorem finite_mdr_summed_out_values_2[simp]:
  ∀ps qs n ts i x.
    FINITE (mdr_summed_out_values_2 n ts i x)
Proof
  rw[]
  >> gvs[mdr_summed_out_values_2_def]
QED

Theorem finite_mdr_summed_out_values_complete[simp]:
  ∀n ts.
    FINITE (mdr_summed_out_values_complete n ts)
Proof
  rw[]
  >> gvs[mdr_summed_out_values_complete_def]
QED

(* -------------------------------------------------------------------------- *)
(* A version of BAYES_RULE which does not require prob p B ≠ 0, since HOL4    *)
(* treats undefined values as having a value of the appropriate type, and so  *)
(* an undefined value multiplied by zero is equal to zero, not undefined.     *)
(* -------------------------------------------------------------------------- *)
Theorem BAYES_RULE_GENERALIZED:
  ∀p A B.
    prob_space p ∧
    A ∈ events p ∧
    B ∈ events p ∧
    prob p A ≠ 0 ⇒
    cond_prob p B A = cond_prob p A B * prob p B / prob p A
Proof
  rw[]
  >> Cases_on ‘prob p B = 0’
  >- (gvs[zero_div, cond_prob_def]
      >> gvs[PROB_ZERO_INTER]
      >> gvs[zero_div]
     )
  >> metis_tac[BAYES_RULE]
QED

(* -------------------------------------------------------------------------- *)
(* A theorem describing the relationship between the values that are summed   *)
(* out and the events that are summed out. Perhaps this is an indication that *)
(* the way we represent this needs to be improved, because the close          *)
(* relationship between these concepts indicates that maybe both of them      *)
(* could somehow be represented using the same concept, which would avoid the *)
(* need for converting between them. Maybe introducing all these definitions  *)
(* is hurting more than it's helping.                                         *)
(* -------------------------------------------------------------------------- *)
(* TODO: fix this
Theorem mdr_summed_out_values_mdr_summed_out_events:
  ∀ps qs n m ts i x bs σs cs_p.
    (bs, σs, cs_p) ∈ mdr_summed_out_values (ps,qs) n ts i x ⇔
      (event_input_bit_takes_value n m i x)
      ∩ (mdr_summed_out_events (ps,qs) n m ts (bs, σs, cs_p)) =
      {(bs, ns) | ns | LENGTH ns = m}
Proof
  (* This proof could probably be made neater *)
  rw[]
  >> EQ_TAC >> rw[]
  >- (gvs[mdr_summed_out_values_def,
          mdr_summed_out_events_def,
          event_input_bit_takes_value_def,
          event_input_string_starts_with_def,
          event_state_sequence_starts_with_def,
          event_srcc_parity_string_starts_with_def]
      >> rw[EXTENSION] >> EQ_TAC >> rw[] >> metis_tac[IS_PREFIX_LENGTH_ANTI]
     )
  >> gvs[EXTENSION]
  >> pop_assum (qspec_then ‘(bs, REPLICATE m ARB)’ assume_tac)
  >> gvs[]
  >> gvs[event_input_bit_takes_value_def]
  >> gvs[mdr_summed_out_values_def,
         mdr_summed_out_events_def,
         event_input_bit_takes_value_def,
         event_input_string_starts_with_def,
         event_state_sequence_starts_with_def,
         event_srcc_parity_string_starts_with_def]
QED*)

(* Possible improvement: remove assumption that LENGTH bs = n (also remove
   this assumption from theorems this depends on) *)
(* TODO: Fix this 
Theorem mdr_summed_out_values_mdr_summed_out_events_empty:
  ∀ps qs n m ts i x bs σs cs_p.
    LENGTH bs = n ⇒
    ((bs, σs, cs_p) ∉ mdr_summed_out_values (ps,qs) n ts i x ⇔
       (event_input_bit_takes_value n m i x)
       ∩ (mdr_summed_out_events (ps,qs) n m ts (bs, σs, cs_p)) = ∅)
Proof
  (* This proof is a little messy and could be improved *)
  rw[]
  >> qmatch_abbrev_tac ‘LHS ⇔ RHS’
  >> ‘¬LHS ⇔ ¬RHS’ suffices_by gvs[]
  >> unabbrev_all_tac
  >> qmatch_abbrev_tac ‘_ ⇔ RHS’
  >> gvs[]
  >> unabbrev_all_tac
  >> EQ_TAC
  >- (rw[]
      >> drule (iffLR mdr_summed_out_values_mdr_summed_out_events)
      >> rw[]
      >> rw[EXTENSION]
      >> metis_tac[LENGTH_REPLICATE]
     )
  >> rw[]
  >> irule (iffRL mdr_summed_out_values_mdr_summed_out_events)
  >> qexists ‘m’
  >> gvs[]
  >> gvs[EXTENSION]
  >> rw[]
  >> EQ_TAC
  >- (rw[]
      >> Cases_on ‘x''’
      >> gvs[event_input_bit_takes_value_def,
             mdr_summed_out_events_def]
      >> gvs[event_state_sequence_starts_with_def,
             event_srcc_parity_string_starts_with_def]
      >> rpt (pop_assum mp_tac)
      >> PURE_ONCE_REWRITE_TAC[event_input_string_starts_with_def]
      >> rpt disch_tac
      >> qpat_x_assum ‘(q,r) ∈ _’ mp_tac
      >> rpt (pop_assum kall_tac)
      >> rw[]
      >> metis_tac[IS_PREFIX_LENGTH_ANTI]
     )
  >> rw[]
  >> gvs[mdr_summed_out_values_def,
         mdr_summed_out_events_def,
         event_input_bit_takes_value_def,
         event_input_string_starts_with_def,
         event_state_sequence_starts_with_def,
         event_srcc_parity_string_starts_with_def]
  >> metis_tac[IS_PREFIX_LENGTH_ANTI]
QED*)

(* Possible improvement: remove assumption that LENGTH bs = n (also remove
   this assumption from theorems this depends on) *)
Theorem event_input_bit_takes_value_mdr_summed_out_events_el_i_x:
  ∀n m i x ps qs ts bs σs cs_p.
    LENGTH bs = n ∧
    EL i bs = x ⇒
    (event_input_bit_takes_value n m i x)
    ∩ (mdr_summed_out_events (ps,qs) n m ts (bs,σs,cs_p)) =
    mdr_summed_out_events (ps,qs) n m ts (bs,σs,cs_p)
Proof
  rw[]
  >> gvs[event_input_bit_takes_value_def,
         mdr_summed_out_events_def,
         event_input_string_starts_with_def,
         event_state_sequence_starts_with_def,
         event_srcc_parity_string_starts_with_def]
  >> rw[EXTENSION] >> EQ_TAC >> rw[] >> metis_tac[IS_PREFIX_LENGTH_ANTI]
QED

Theorem mdr_summed_out_values_2_el_i_x:
  ∀n ts i x bs σs cs_p.
    (bs, σs, cs_p) ∈ mdr_summed_out_values_2 n ts i x ⇒
    EL i bs = x
Proof
  rw[]
  >> gvs[mdr_summed_out_values_2_def]
QED

Theorem EXTREAL_PROD_IMAGE_POW:
  ∀f S (x : extreal).
    FINITE S ∧
    (∀s. s ∈ S ⇒ f s = x) ⇒
    ∏ f S = x pow (CARD S)
Proof
  rw[]
  >> Induct_on ‘S’ using FINITE_INDUCT
  >> rw[] >> gvs[]
  >> gvs[EXTREAL_PROD_IMAGE_THM]
  >> gvs[DELETE_NON_ELEMENT_RWT]
  >> gvs[extreal_pow]
QED

Theorem prob_event_input_string_starts_with_decompose:
  ∀n m p bs.
    0 ≤ p ∧
    p ≤ 1 ∧
    LENGTH bs = n ⇒
    prob (ecc_bsc_prob_space n m p) (event_input_string_starts_with n m bs) =
    ∏ (λi.
         prob (ecc_bsc_prob_space n m p)
              (event_input_bit_takes_value n m i (EL i bs))
      ) (count n)
Proof
  rw[]
  >> qmatch_goalsub_abbrev_tac ‘∏ f S’
  >> qspecl_then [‘f’, ‘S’, ‘1/2’] assume_tac EXTREAL_PROD_IMAGE_POW
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> unabbrev_all_tac >> gvs[]
  >> rw[]
  >> gvs[pow_div]
QED

Theorem event_state_sequence_starts_with_sing:
  ∀n m ps qs ts x.
    event_state_sequence_starts_with n m (ps,qs) ts [x] =
    if ts = x then
      event_universal n m
    else
      ∅
Proof
  rw[event_state_sequence_starts_with_def]
  >- (rw[EXTENSION] >> EQ_TAC >> rw[]
      >> Cases_on ‘encode_recursive_parity_equation_state_sequence (ps,qs) ts bs’
      >> gvs[]
      >> Cases_on ‘bs’ >> gvs[encode_recursive_parity_equation_state_sequence_def])
  >> rw[EXTENSION]
  >> Cases_on ‘encode_recursive_parity_equation_state_sequence (ps,qs) ts bs’
  >> gvs[]
  >> Cases_on ‘bs’ >> gvs[encode_recursive_parity_equation_state_sequence_def]
QED
        
(* -------------------------------------------------------------------------- *)
(* We want to prove:                                                          *)
(* P(bs,σs,cs) = P(σ_0)P(b_0)P(σ_1c_0|σ_0b_0)P(b_1)P(σ_2c_1|σ_1b_1)...        *)
(*                                                                            *)
(* 1. Inductively prove that P(bs) = P(b_0)P(b_1)...P(b_{n-1})                *)
(* 2. Inductively add σs, so we get                                           *)
(*                     P(bs,σs) = P(bs)P(σ_0)P(σ_1|σ_0b_0)P(σ_2|σ_1b_1)...    *)
(*    - P(bs,σ_0) = 0 if σ_0 is valid and P(bs) otherwise = P(bs)P(σ_0)       *)
(*    - P(bs,σ_0^kσ_{k+1}) = P(bs,σ_0^k,σ_k,b_k,σ_{k+1})                      *)
(*       notice that combining the events σ_k, b_k, σ_{k+1}, we get the       *)
(*       empty event if σ_{k+1} is invalid and we get σ_k, b_k otherwise.     *)
(*                      = P(bs,σ_0^k,σ_k,b_k)Indicator(σ_{k+1} is valid)      *)
(*                         = P(bs,σ_0^k)P(σ_{k+1}|σ_{k}b_k)                   *)
(*       (this second step can be performed by applying the same observation  *)
(*        as previously mentioned again, this time to the new probability)    *)
(* 3. Inductively add cs, so we get                                           *)
(*                P(bs,σs,cs) = P(bs,σs)P(c_0|σ_0b_0)P(c_1|σ_1b_1)...         *)
(*    - We can use the same logic as in part 2 during each inductive step,    *)
(*      because the events σ_k, b_k, c_k reduce to σ_k, b_k if c_k is valid   *)
(*      and to 0 otherwise.                                                   *)
(* 4. If desired, we can combine P(c_i|σ_ib_i) with P(σ_{i+1}|σ_ib_i), but    *)
(*    this may not be helpful and may be a waste of time.                     *)
(* -------------------------------------------------------------------------- *)
Theorem split_mdr_events_prob:
  ∀n m p ps qs ts bs σs cs_p.
    LENGTH bs = n ∧
    LENGTH σs = n + 1 ∧
    LENGTH cs_p = n ⇒
    prob (ecc_bsc_prob_space n m p)
         (mdr_summed_out_events (ps,qs) n m ts (bs,σs,cs_p)) =
    ∏ (λi.
         prob (ecc_bsc_prob_space n m p)
              (event_input_bit_takes_value n m i (EL i bs))
      ) (count n) *
    prob (ecc_bsc_prob_space n m p)
         (event_state_takes_value n m (ps,qs) ts 0 (EL 0 σs)) *
    ∏ (λi.
         cond_prob (ecc_bsc_prob_space n m p)
                   (event_state_takes_value n m (ps,qs) ts (i+1) (EL (i+1) σs))
                   ((event_state_takes_value n m (ps,qs) ts i (EL i σs))
                    ∩ (event_input_bit_takes_value n m i (EL i bs)))
      ) (count n) *
    ∏ (λi.
         cond_prob (ecc_bsc_prob_space n m p)
                   (event_srcc_parity_bit_takes_value (ps,qs) n m ts i (EL i cs_p))
                   ((event_state_takes_value n m (ps,qs) ts i (EL i σs))
                    ∩ (event_input_bit_takes_value n m i (EL i bs)))
      ) (count n)
Proof
  (* Step 1: Split P(bs) up *)
  kall_tac prob_event_input_string_starts_with_decompose
  (* Step 2: Split σs away from P(bs,σs) *)
  >> sg ‘LENGTH bs = n ∧
         σs ≠ [] ⇒
         prob (ecc_bsc_prob_space n m p)
         ((event_input_string_starts_with n m bs)
          ∩ (event_state_sequence_starts_with n m (ps,qs) ts σs))
         = prob (ecc_bsc_prob_space n m p)
                (event_input_string_starts_with n m bs) *
           prob (ecc_bsc_prob_space n m p)
                (event_state_takes_value n m (ps,qs) ts 0 (EL 0 σs)) *
           ∏ (λi.
                cond_prob (ecc_bsc_prob_space n m p)
                          (event_state_takes_value n m (ps,qs) ts (i+1) (EL (i+1) σs))
                          ((event_state_takes_value n m (ps,qs) ts i (EL i σs))
                           ∩ (event_input_bit_takes_value n m i (EL i bs)))
             ) (count (LENGTH σs - 1))
        ’
  >- (disch_tac
      >> SPEC_ALL_TAC
      >> Induct_on ‘σs’ using SNOC_INDUCT >- gvs[]
      >> rw[]
      >> gvs[HD_SNOC]
      >> Cases_on ‘σs = []’
      >- (gvs[]
      )
      >> gvs[event_state_sequence_starts_with_def]
      >> rw[]
     )
     (* Step 3: *)

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
             (λx. ∑ ARB (mdr_summed_out_values_2 n ts i x)
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
     around *)
  >> irule EQ_SYM
  (* Nicer names *)
  >> qmatch_abbrev_tac ‘C * cond_prob sp e1 e2 = RHS’
  (* We are at the stage p(b_s | ds). Take a sum over σs, cs_p, and the
      remaining elements of bs *)
  >> qspecl_then [‘sp’,
                  ‘mdr_summed_out_events (ps,qs) n (LENGTH ds) ts’,
                  ‘e1’,
                  ‘e2’,
                  ‘mdr_summed_out_values_2 n ts i x’] assume_tac COND_PROB_EXTREAL_SUM_IMAGE_FN
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> rpt conj_tac >> unabbrev_all_tac
  >- gvs[]
  >- gvs[]
  >- gvs[]
  >- gvs[]
  (* The new intersection of events is an event *)
  >- (rw[]
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
      >- gvs[mdr_summed_out_events_def, event_input_string_starts_with_def]
      >> gvs[]
      (* If σs1 ≠ σs2, then the next part is disjoint *)
      >> Cases_on ‘σs1 ≠ σs2’
      >- gvs[mdr_summed_out_events_def, event_state_sequence_starts_with_def]
      >> gvs[]
      (* We have cs1_p ≠ cs2_p, and so the final part is disjoint *)
      >> gvs[mdr_summed_out_events_def, event_srcc_parity_string_starts_with_def]
     )
  (* The numerator of the conditional probability (i.e. the intersection of the
     two events in the conditional probability) is contained in the union of
     the new events we are intesecting over. *)
  >- (PURE_REWRITE_TAC[BIGUNION_IMAGE]
      >> gvs[SUBSET_DEF]
      >> qx_gen_tac ‘y’
      >> rw[]
      (* Apply event_received_string_starts_with_def to assumption *)
      >> pop_assum (fn th => assume_tac (SIMP_RULE bool_ss [event_received_string_starts_with_def] th))
      >> gs[]
      >> qexists ‘(bs,
                   encode_recursive_parity_equation_state_sequence (ps,qs) ts bs,
                   encode_recursive_parity_equation (ps,qs) ts bs)’
      >> gs[]
      >> rpt conj_tac
      >- (gs[mdr_summed_out_values_2_alt]
          >> gs[event_input_bit_takes_value_def]
          >> rw[]
          >> metis_tac[mem_encode_recursive_parity_equation_state_sequence_length]
         )
      >> gs[mdr_summed_out_events_def,
            event_input_string_starts_with_def,
            event_state_sequence_starts_with_def,
            event_srcc_parity_string_starts_with_def]
     )
  (* Name the constant *)
  >> qmatch_abbrev_tac ‘C * ∑ _ _ = _’
  (* Prove some helpful, reusable properties *)
  >> sg ‘C ≠ −∞’ >- cheat
  >> sg ‘C ≠ +∞’ >- cheat
  (* Move the constant into the sum *)
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_CMUL_ALT]
  >> conj_tac
  >- (rpt conj_tac
      >- gvs[]
      >- gvs[]
      >- gvs[]
      >> disj2_tac
      >> rw[]
      >> irule (cj 1 COND_PROB_FINITE)
      >> gvs[]
      >> irule EVENTS_INTER >> gvs[]
     )
  (* OUTDATED
.
Make our sum take all values over the input bitstring, the states,
     and the parity bits, rather than just the valid choices, by giving each
     term with invalid bitstring/states/parity bits a value of 0, so that it
     doesn't affect the overall sum.
.
    First apply EXTREAL_SUM_IMAGE_IN_IF to change our term to the appropriate
    term, then apply EXTREAL_SUM_IMAGE_INTER_ELIM in order to expand the set we
    are summing over
   *)
  (*>> qmatch_goalsub_abbrev_tac ‘_ = RHS’
      >> DEP_PURE_ONCE_REWRITE_TAC [EXTREAL_SUM_IMAGE_IN_IF]
      >> simp[Abbr ‘RHS’]
      >> conj_tac
      >- (disj1_tac
          >> rw[]
          >> irule (cj 1 mul_not_infty2)
          >> rpt conj_tac
          >- gvs[]
          >- gvs[]
          >- (irule (cj 2 COND_PROB_FINITE)
              >> gvs[]
              >> namedCases_on ‘x'’ ["bs σs cs_p"]
              >> irule EVENTS_INTER
              >> gvs[]
             )
          >> irule (cj 1 COND_PROB_FINITE)
          >> gvs[]
          >> gvs[EVENTS_INTER]
         )
      >> sg ‘mdr_summed_out_values (ps, qs) n ts i x =
             (mdr_summed_out_values_complete n ts)
             ∩ mdr_summed_out_values (ps, qs) n ts i x
            ’
      >- (gvs[mdr_summed_out_values_def, mdr_summed_out_values_complete_alt]
          >> rw[EXTENSION]
          >> EQ_TAC
      >> rw[] >> rw[]
      >> metis_tac[mem_encode_recursive_parity_equation_state_sequence_length]
     )
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_INTER_ELIM]
  >> conj_tac
  >- (rw[]
      >> disj1_tac
      >> rw[]
      >> irule (cj 1 mul_not_infty2)
      >> rpt conj_tac
      >- gvs[]
      >- gvs[]
      >- (irule (cj 2 COND_PROB_FINITE)
          >> gvs[]
          >> namedCases_on ‘x'’ ["bs σs cs_p"]
          >> irule EVENTS_INTER
          >> gvs[]
         )
      >> irule (cj 1 COND_PROB_FINITE)
      >> gvs[EVENTS_INTER]
     )*)
  (* The function in the sum is the equivalent bit *)
  >> irule EXTREAL_SUM_IMAGE_EQ'
  >> gvs[]
  >> qx_gen_tac ‘w’
  >> disch_tac
  >> namedCases_on ‘w’ ["bs σs cs_p"]
  (* We are currently up to the step
     argmax Σ p(bs, cs_p, σs | ds) over bs, cs_p, σs.
     Next step:
     argmax Σ p(ds | bs, cs_p, σs) p(bs, cs_p, σs) over ''
.
     That is, we apply Bayes' rule here
   *)
  >> DEP_PURE_ONCE_REWRITE_TAC[BAYES_RULE_GENERALIZED]
  >> conj_tac
  >- (rpt conj_tac
      >- gvs[]
      >- gvs[]
      >- (irule EVENTS_INTER >> gvs[]
         )
      >- gvs[]
     (*>> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
             >> conj_tac
             >- (gvs[]
                 >> irule EVENTS_INTER >> gvs[]
                )
             >> gvs[EXTENSION]
             >> namedCases_on ‘w’ ["bs σs cs_p"] >> gvs[]
             >> gvs[mdr_summed_out_events_def]
             >> qexists ‘(bs, REPLICATE (LENGTH ds) F)’
             >> rpt conj_tac
             >- gvs[event_input_bit_takes_value_def,
                    mdr_summed_out_values_def]
             >- gvs[event_input_string_starts_with_def,
                    mdr_summed_out_values_def]
             >- gvs[event_state_sequence_starts_with_def,
                    mdr_summed_out_values_def]
             >> gvs[event_srcc_parity_string_starts_with_def,
                    mdr_summed_out_values_def]*)
     )
  (* Merge the constant part into the constant *)
  >> qmatch_goalsub_abbrev_tac ‘C * (val1 * val2 / val3)’
  >> sg ‘C * (val1 * val2 / val3) = (C / val3) * val1 * val2’
  >- (sg ‘val1 ≠ +∞ ∧ val1 ≠ −∞ ∧ val2 ≠ +∞ ∧ val2 ≠ −∞ ∧ val3 ≠ +∞ ∧ val3 ≠ −∞’
      >- (cheat
         (*unabbrev_all_tac
           >> gvs[PROB_FINITE, COND_PROB_FINITE]
           >> rpt conj_tac
           >- (irule (cj 1 COND_PROB_FINITE)
               >> gvs[]
               >> conj_tac
               >> irule EVENTS_INTER >> gvs[]
              )*)
         )
      >> Cases_on ‘C’ >> gvs[]
      >> qpat_x_assum ‘Normal r = ARB’ (fn th => gvs[GSYM th])
      >> Cases_on ‘val1’ >> gvs[]
      >> Cases_on ‘val2’ >> gvs[]
      >> Cases_on ‘val3’ >> gvs[]
      >> Cases_on ‘r''' = 0’
      >- cheat
      >> gvs[extreal_mul_eq, extreal_div_eq]
     )
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[Abbr ‘C’, Abbr ‘val3’]
  >> qmatch_abbrev_tac ‘C * val1 * val2 = _’
  (* Introduce a variable b which tells us whether the current choice of
     (bs, σs, cs_p) is valid, or if it is self-contradictory (since a given
     choice of bs will correspond to only one specific choice of σs and cs_p) *)
  >> qabbrev_tac ‘b = ((bs, σs, cs_p) ∈ mdr_summed_out_values (ps,qs) n ts i x)’
  (* When the values being summed over are invalid (i.e. we have ¬b), then
     val2 will equal 0, so we can remove the if _ then _ else _.
.
     This is because the event in val2 requries an element of the event to
     correspond to (bs, σs, cs_p) and also have the ith element of the input
     to be x, but when the values being summed over are invalid, we precisely
     know that at least one of these things is not the case.
   *)
  >> sg ‘¬b ⇒ val2 = 0’
  >- (rw[]
      >> unabbrev_all_tac
      >> gvs[]
      >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
      >> conj_tac
      >- (gvs[]
          >> irule EVENTS_INTER
          >> gvs[]
         )
      >> metis_tac[mdr_summed_out_values_mdr_summed_out_events_empty]
     )
  (* 
     Next step: p(ds | bs, cs_p, σs) = Π P(d_i | c_i)
.
     That is, we split val1 up into a product of each individual received value
     given the corresponding sent value
    *)
  >> sg ‘b ⇒ val1 = TODO1’
  >- (unabbrev_all_tac
      >> rw[]
      >> gvs[mdr_summed_out_events_def]
      (* The sent string taking a particular value abosorbs all other events
         in the denominator of the conditional probability *)
      >> gs[mdr_summed_out_values_def]
      >> gs[inter_input_state_sequence_eq_input]
      >> gs[inter_input_parity_eq_sent]
      >> qspecl_then [‘ps’, ‘qs’, ‘ts’] assume_tac
                     encode_recursive_parity_equation_with_systematic_inj
      >> gs[INJ_DEF]
      >> gs[inter_input_bit_sent_eq_sent]
      (* Now that we have simplified our conditional probability to just be
         in terms of the received string taking a value given that the sent
         string takes a value, it is now more obvious that this conditional
         probability is the product of the probabilities of each individual
         received bit given the corresponding sent bit. *)
      >> gvs[cond_prob_string_given_sent_prod]
      (* While this isn't a product, it's an explicit expression for the
         probability, which will be equal to the product *)
      >> cheat
     )
  >> ‘C * val1 * val2 = C * TODO1 * val2’ by (Cases_on ‘b’ >> gvs[])
  >> qpat_x_assum ‘b ⇒ val1 = _’ kall_tac
  >> qpat_x_assum ‘Abbrev (val1 = _)’ kall_tac
  >> pop_assum (fn th => PURE_REWRITE_TAC[th])
  >> qmatch_abbrev_tac ‘C * val1 * val2 = _’
  (* We can eliminate x because it is simply equal to EL i bs*)
  >> drule mdr_summed_out_values_2_el_i_x
  >> disch_tac >> gvs[]
  (* We are currently up to the step
     argmax Σ p(ds | bs, cs_p, σs) p(bs, cs_p, σs) over ''
.
     Next step: split val2 up into p(σ_0)p(b_1)p(c_1_p,σ_1|b_1,σ_0)p(b_2)      
                p(c_2_p,σ_2|b_2,σ_1)p(b_3)p(c_3_p,σ_3|b_3,σ_2)...
   *)
  >> sg ‘val2 = ARB’
  >- (unabbrev_all_tac
      >> gvs[event_input_bit_takes_value_mdr_summed_out_events_el_i_x]
      >> 
     )
QED

val _ = export_theory();

