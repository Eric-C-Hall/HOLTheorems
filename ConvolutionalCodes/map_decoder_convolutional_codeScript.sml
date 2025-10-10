(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory map_decoder_convolutional_code

Ancestors ecc_prob_space argmin_extreal map_decoder parity_equations recursive_parity_equations useful_theorems arithmetic bitstring extreal list pred_set probability real rich_list sigma_algebra martingale measure topology

Libs donotexpandLib map_decoderLib realLib dep_rewrite ConseqConv;

val _ = hide "S";

(* -------------------------------------------------------------------------- *)
(* Add generally useful theorems to the simpset                               *)
(* -------------------------------------------------------------------------- *)
val _ = augment_srw_ss [rewrites[TAKE_TAKE,
                                 DROP_TAKE,
                                 LENGTH_TAKE,
                                 EVENTS_INTER,
                                 PROB_EMPTY,
                                 PROB_FINITE]]

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
                                      (ps,qs) ts (TAKE i bs) = σ
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
(*                                                                            *)
(* We require i < n in order to make the event empty in the case where we     *)
(* have an invalid index, rather than indeterminate                           *)
(* -------------------------------------------------------------------------- *)
Definition event_srcc_parity_bit_takes_value_def:
  event_srcc_parity_bit_takes_value (ps,qs) n m ts i c_p =
  {(bs, ns) | LENGTH bs = n ∧
              LENGTH ns = m ∧
              i < n ∧
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
Definition event_input_state_parity_def:
  event_input_state_parity (ps,qs) n m ts (bs, σs, cs_p) =
  (event_input_string_starts_with n m bs)
  ∩ (event_state_sequence_starts_with n m (ps,qs) ts σs)
  ∩ (event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p)
End

Definition input_state_parity_valid_def:
  input_state_parity_valid (ps,qs) ts (bs, σs, cs_p) =
  ((σs = encode_recursive_parity_equation_state_sequence (ps,qs) ts bs) ∧
   (cs_p = encode_recursive_parity_equation (ps,qs) ts bs))
End

(* -------------------------------------------------------------------------- *)
(* These intersection theorems are only helpful if we don't know that our     *)
(* encoding function is injective, because otherwise we could simply use the  *)
(* fact that, for example, a particular input string corresponds exactly to   *)
(* a particular state sequence.                                               *)
(* -------------------------------------------------------------------------- *)

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

(* Should this be a simp rule, or is it wiser to avoid it being a simp rule
   because in some situations one event will be more useful and in other
   situations the other event will be more useful? *)
(* Possible improvement: can we remove the precondition LENGTH bs = n
                         and LENGTH σs = n + 1*)
Theorem inter_input_state_eq_input:
  ∀n m ps qs ts bs σs.
    LENGTH bs = n ∧
    LENGTH σs = n + 1 ⇒
    (event_input_string_starts_with n m bs)
    ∩ (event_state_sequence_starts_with n m (ps,qs) ts σs) =
    if
    σs = encode_recursive_parity_equation_state_sequence (ps,qs) ts bs
    then
      event_input_string_starts_with n m bs
    else ∅
Proof
  rw[]
  >- (gvs[event_input_string_starts_with_def,
          event_state_sequence_starts_with_def]
      >> rw[EXTENSION] >> EQ_TAC >> rw[] >> gvs[TAKE_LENGTH_ID_rwt]
      >> metis_tac[IS_PREFIX_LENGTH_ANTI]
    )
  >> gvs[event_input_string_starts_with_def,
         event_state_sequence_starts_with_def]
  >> rw[EXTENSION] >> CCONTR_TAC >> gvs[]
  >> metis_tac[IS_PREFIX_LENGTH_ANTI,
               encode_recursive_parity_equation_state_sequence_length]
QED

(* Possible improvement: can we remove the precondition LENGTH bs = n *)
Theorem inter_input_parity_eq_sent:
  ∀n m ps qs ts bs cs_p.
    LENGTH bs = n ∧
    LENGTH cs_p = n ⇒
    (event_input_string_starts_with n m bs)
    ∩ (event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p) =
    if
    cs_p = encode_recursive_parity_equation (ps,qs) ts bs
    then
      event_sent_string_starts_with
      (encode_recursive_parity_equation_with_systematic (ps,qs) ts) n m
      (encode_recursive_parity_equation_with_systematic (ps,qs) ts bs)
    else
      ∅
Proof
  rw[]
  >- (gvs[event_input_string_starts_with_def,
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
     )
  >> gvs[event_input_string_starts_with_def,
         event_srcc_parity_string_starts_with_def]
  >> rw[EXTENSION] >> CCONTR_TAC >> gvs[]
  >> metis_tac[IS_PREFIX_LENGTH_ANTI,
               encode_recursive_parity_equation_length]
QED

Theorem inter_input_parity_eq_input:
  ∀n m ps qs ts bs cs_p.
    LENGTH bs = n ∧
    LENGTH cs_p = n ⇒
    (event_input_string_starts_with n m bs)
    ∩ (event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p) =
    if
    cs_p = encode_recursive_parity_equation (ps,qs) ts bs
    then
      event_input_string_starts_with n m bs
    else
      ∅
Proof
  rw[]
  >- (gvs[event_input_string_starts_with_def,
          event_srcc_parity_string_starts_with_def]
      >> rw[EXTENSION] >> EQ_TAC >> rw[] >> metis_tac[IS_PREFIX_LENGTH_ANTI]
     )
  >> gvs[event_input_string_starts_with_def,
         event_srcc_parity_string_starts_with_def]
  >> rw[EXTENSION] >> CCONTR_TAC >> gvs[]
  >> metis_tac[IS_PREFIX_LENGTH_ANTI,
               encode_recursive_parity_equation_length]
QED

Theorem inter_input_parity_eq_parity:
  ∀n m ps qs ts bs cs_p.
    LENGTH bs = n ∧
    LENGTH cs_p = n ∧
    LENGTH ps = LENGTH ts + 1 ∧
    LAST ps ⇒
    (event_input_string_starts_with n m bs)
    ∩ (event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p) =
    if
    cs_p = encode_recursive_parity_equation (ps,qs) ts bs
    then
      event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p
    else
      ∅
Proof
  rw[]
  >- (gvs[event_input_string_starts_with_def,
          event_srcc_parity_string_starts_with_def]
      >> rw[EXTENSION] >> EQ_TAC >> rw[]
      >> irule (iffRL encode_recursive_parity_equation_prefix_inj)
      >> qexistsl [‘ps’, ‘qs’, ‘ts’]
      >> gvs[]
     )
  >> gvs[event_input_string_starts_with_def,
         event_srcc_parity_string_starts_with_def]
  >> rw[EXTENSION] >> CCONTR_TAC >> gvs[]
  >> metis_tac[IS_PREFIX_LENGTH_ANTI,
               encode_recursive_parity_equation_length]
QED

(* Possible improvement: remove requirement that LENGTH bs = n *)
Theorem inter_input_bit_sent_eq_sent:
  ∀enc n m psqs t bs i x.
    LENGTH bs = n ∧
    (∀xs ys. enc xs ≼ enc ys ⇔ xs ≼ ys) ⇒
    (event_input_bit_takes_value n m i x)
    ∩ (event_sent_string_starts_with enc n m (enc bs)) =
    if
    EL i bs = x
    then
      event_sent_string_starts_with enc n m (enc bs)
    else ∅
Proof
  rw[]
  >- (gvs[event_input_bit_takes_value_def,
          event_sent_string_starts_with_def]
      >> rw[EXTENSION] >> EQ_TAC >> rw[]
      >> metis_tac[IS_PREFIX_LENGTH_ANTI]
     )
  >> rw[EXTENSION]
  >> CCONTR_TAC
  >> gvs[]
  >> gvs[event_input_bit_takes_value_def,
         event_sent_string_starts_with_def]
  >> metis_tac[IS_PREFIX_LENGTH_ANTI]
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

Theorem event_input_state_parity_is_event[simp]:
  ∀psqs n m p ts bsσscs_p.
    event_input_state_parity psqs n m ts bsσscs_p
                             ∈ events (ecc_bsc_prob_space n m p)
Proof
  rw[]
  >> namedCases_on ‘psqs’ ["ps qs"]
  >> namedCases_on ‘bsσscs_p’ ["bs σs cs_p"]
  >> rw[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
  >> gvs[event_input_state_parity_def]
  >> gvs[event_input_string_starts_with_def]
QED

Theorem finite_mdr_summed_out_values_2[simp]:
  ∀ps qs n ts i x.
    FINITE (mdr_summed_out_values_2 n ts i x)
Proof
  rw[]
  >> gvs[mdr_summed_out_values_2_def]
QED

(* -------------------------------------------------------------------------- *)
(* A version of BAYES_RULE which does not require prob p B ≠ 0, since HOL4    *)
(* treats undefined values as having a value of the appropriate type, and so  *)
(* an undefined value multiplied by zero is equal to zero, not undefined.     *)
(*                                                                            *)
(* The old implementation of bayes rule has been updated to not require       *)
(* prob p B ≠ 0, so this version of the theorem is no longer necessary        *)
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
Theorem mdr_summed_out_values_event_input_state_parity:
  ∀ps qs n m ts i x bs σs cs_p.
    (bs, σs, cs_p) ∈ mdr_summed_out_values (ps,qs) n ts i x ⇔
      (event_input_bit_takes_value n m i x)
      ∩ (event_input_state_parity (ps,qs) n m ts (bs, σs, cs_p)) =
      {(bs, ns) | ns | LENGTH ns = m}
Proof
  (* This proof could probably be made neater *)
  rw[]
  >> EQ_TAC >> rw[]
  >- (gvs[mdr_summed_out_values_def,
          event_input_state_parity_def,
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
         event_input_state_parity_def,
         event_input_bit_takes_value_def,
         event_input_string_starts_with_def,
         event_state_sequence_starts_with_def,
         event_srcc_parity_string_starts_with_def]
QED*)

(* Possible improvement: remove assumption that LENGTH bs = n (also remove
   this assumption from theorems this depends on) *)
(* TODO: Fix this 
Theorem mdr_summed_out_values_event_input_state_parity_empty:
  ∀ps qs n m ts i x bs σs cs_p.
    LENGTH bs = n ⇒
    ((bs, σs, cs_p) ∉ mdr_summed_out_values (ps,qs) n ts i x ⇔
       (event_input_bit_takes_value n m i x)
       ∩ (event_input_state_parity (ps,qs) n m ts (bs, σs, cs_p)) = ∅)
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
      >> drule (iffLR mdr_summed_out_values_event_input_state_parity)
      >> rw[]
      >> rw[EXTENSION]
      >> metis_tac[LENGTH_REPLICATE]
     )
  >> rw[]
  >> irule (iffRL mdr_summed_out_values_event_input_state_parity)
  >> qexists ‘m’
  >> gvs[]
  >> gvs[EXTENSION]
  >> rw[]
  >> EQ_TAC
  >- (rw[]
      >> Cases_on ‘x''’
      >> gvs[event_input_bit_takes_value_def,
             event_input_state_parity_def]
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
         event_input_state_parity_def,
         event_input_bit_takes_value_def,
         event_input_string_starts_with_def,
         event_state_sequence_starts_with_def,
         event_srcc_parity_string_starts_with_def]
  >> metis_tac[IS_PREFIX_LENGTH_ANTI]
QED*)

(* Possible improvement: remove assumption that LENGTH bs = n (also remove
   this assumption from theorems this depends on) *)
Theorem event_input_bit_takes_value_event_input_state_parity_el_i_x:
  ∀n m i x ps qs ts bs σs cs_p.
    LENGTH bs = n ∧
    EL i bs = x ⇒
    (event_input_bit_takes_value n m i x)
    ∩ (event_input_state_parity (ps,qs) n m ts (bs,σs,cs_p)) =
    event_input_state_parity (ps,qs) n m ts (bs,σs,cs_p)
Proof
  rw[]
  >> gvs[event_input_bit_takes_value_def,
         event_input_state_parity_def,
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

Theorem event_state_takes_value_zero:
  ∀n m ps qs ts σ.
    event_state_takes_value n m (ps,qs) ts 0 σ =
    if ts = σ then
      event_universal n m
    else
      ∅
Proof
  rw[event_state_takes_value_def]
QED

Theorem IS_PREFIX_SNOC_L:
  ∀b bs cs.
    LENGTH bs + 1 ≤ LENGTH cs ⇒
    (SNOC b bs ≼ cs ⇔ (bs ≼ cs ∧ EL (LENGTH bs) cs = b))
Proof
  Induct_on ‘bs’ >> Cases_on ‘cs’ >> rw[]
  >- metis_tac[]
  >> EQ_TAC >> rw[]
QED

Theorem event_state_sequence_starts_with_snoc:
  ∀n m ps qs ts σ σs.
    LENGTH σs ≤ n ⇒
    event_state_sequence_starts_with n m (ps,qs) ts (SNOC σ σs)
    = (event_state_sequence_starts_with n m (ps,qs) ts σs)
      ∩ (event_state_takes_value n m (ps,qs) ts (LENGTH σs) σ)
Proof
  rw[]
  >> gvs[event_state_sequence_starts_with_def,
         event_state_takes_value_def]
  >> rw[EXTENSION] >> EQ_TAC >> rw[] >> gvs[IS_PREFIX_SNOC_L,
                                            el_encode_recursive_parity_equation_state_sequence]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Add this better version of is_prefix_el to the library               *)
(* -------------------------------------------------------------------------- *)
Theorem is_prefix_el_better:
  ∀n l1 l2.
    l1 ≼ l2 ∧
    n < LENGTH l1 ⇒
    EL n l1 = EL n l2
Proof
  rw[]
  >> irule is_prefix_el
  >> gvs[]
  >> metis_tac[IS_PREFIX_LENGTH, LESS_LESS_EQ_TRANS]
QED

Theorem event_input_string_starts_with_inter_event_input_bit_takes_value:
  ∀n m bs i x.
    i < LENGTH bs ⇒
    (event_input_string_starts_with n m bs)
    ∩ (event_input_bit_takes_value n m i x) =
    if x = EL i bs
    then
      event_input_string_starts_with n m bs
    else
      ∅
Proof
  rpt gen_tac
  >> rpt disch_tac
  >> gvs[event_input_string_starts_with_def,
         event_input_bit_takes_value_def]
  >> rw[EXTENSION]
  >- (EQ_TAC >> rw[]
      >> gvs[is_prefix_el_better]
     )
  >> CCONTR_TAC
  >> gvs[is_prefix_el_better]
QED

(* A version of the above theorem which will only simplify, and not make the
   expression more complicated, and thus can be used as a simp rule *)
Theorem event_input_string_starts_with_inter_event_input_bit_takes_value_simp_rule[simp]:
  ∀n m bs i x.
    (i < LENGTH bs ∧ x = EL i bs ⇒
     (event_input_string_starts_with n m bs)
     ∩ (event_input_bit_takes_value n m i x) =
     event_input_string_starts_with n m bs) ∧
    (i < LENGTH bs ∧ x ≠ EL i bs ⇒
     (event_input_string_starts_with n m bs)
     ∩ (event_input_bit_takes_value n m i x) =
     ∅)
Proof
  rw[event_input_string_starts_with_inter_event_input_bit_takes_value]
QED

Theorem event_state_sequence_starts_with_inter_event_state_takes_value[simp]:
  ∀n m ps qs ts σs i.
    i < LENGTH σs ⇒
    (event_state_sequence_starts_with n m (ps,qs) ts σs)
    ∩ (event_state_takes_value n m (ps,qs) ts i (EL i σs)) =
    event_state_sequence_starts_with n m (ps,qs) ts σs
Proof
  rw[event_state_sequence_starts_with_def,
     event_state_takes_value_def]
  >> rw[EXTENSION] >> EQ_TAC >> rw[]
  >> qmatch_asmsub_abbrev_tac ‘σs ≼ σs'’
  >> ‘LENGTH σs ≤ LENGTH σs'’ by metis_tac[IS_PREFIX_LENGTH]
  >> gvs[Abbr ‘σs'’]
  >> gvs[GSYM el_encode_recursive_parity_equation_state_sequence]
  >> irule EQ_SYM
  >> irule is_prefix_el
  >> gvs[]
QED

Theorem encode_recursive_parity_equation_state_encode_recursive_parity_equation_state:
  ∀ps qs ts bs1 bs2.
    encode_recursive_parity_equation_state
    (ps,qs)
    (encode_recursive_parity_equation_state (ps,qs) ts bs1)
    bs2 =
    encode_recursive_parity_equation_state (ps,qs) ts (bs1 ++ bs2)
Proof
  Induct_on ‘bs1’ >> rw[]
  >> gvs[encode_recursive_parity_equation_state_def]
QED

(* -------------------------------------------------------------------------- *)
(* If we have the event that a state takes a certain value, and also we have  *)
(* a certain input, and also the next state takes a certain value, then if    *)
(* the next state follows from the previous state, we can absorb the third    *)
(* condition into the first two, otherwise our event is contradictory and     *)
(* thus is the empty event                                                    *)
(*                                                                            *)
(* Possible improvement: it would be nice to automatically be able to         *)
(* generate this theorem from if (state = ...) and (input = ...) then         *)
(* (state = ...)                                                              *)
(* -------------------------------------------------------------------------- *)
Theorem event_state_input_step:
  ∀n m ps qs ts i j b σ1 σ2.
    i < n ∧
    j = i + 1 ⇒
    (event_state_takes_value n m (ps,qs) ts i σ1)
    ∩ (event_input_bit_takes_value n m i b)
    ∩ (event_state_takes_value n m (ps,qs) ts j σ2) =
    if
    encode_recursive_parity_equation_state (ps,qs) σ1 [b] = σ2
    then
      (event_state_takes_value n m (ps,qs) ts i σ1)
      ∩ event_input_bit_takes_value n m i b
    else
      ∅
Proof
  rw[]
  (* If the new state follows from the old state and input *)
  >- (gvs[event_state_takes_value_def,
          event_input_bit_takes_value_def]
      >> rw[EXTENSION] >> EQ_TAC >> rw[]
      >> gvs[encode_recursive_parity_equation_state_encode_recursive_parity_equation_state]
      >> gvs[GSYM SNOC_APPEND]
      >> gvs[GSYM TAKE_SUC_BY_TAKE]
      >> gvs[ADD1]
     )
  (* If the new state doesn't follow from the old state and input *)
  >> rw[EXTENSION]
  >> CCONTR_TAC
  >> gvs[]
  >> qpat_x_assum ‘_ ≠ _’ mp_tac >> gvs[]
  >> gvs[event_state_takes_value_def,
         event_input_bit_takes_value_def]
  >> gvs[encode_recursive_parity_equation_state_encode_recursive_parity_equation_state]
  >> gvs[GSYM SNOC_APPEND]
  >> gvs[GSYM TAKE_SUC_BY_TAKE]
  >> gvs[ADD1]
QED

Theorem event_srcc_parity_string_starts_with_snoc:
  ∀ps qs n m ts x cs_p.
    LENGTH cs_p + 1 ≤ n ⇒
    event_srcc_parity_string_starts_with (ps,qs) n m ts (SNOC x cs_p) =
    (event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p)
    ∩ (event_srcc_parity_bit_takes_value (ps,qs) n m ts (LENGTH cs_p) x)
Proof
  rw[]
  >> gvs[event_srcc_parity_string_starts_with_def,
         event_srcc_parity_bit_takes_value_def]
  >> rw[EXTENSION] >> EQ_TAC >> rw[] >> gvs[IS_PREFIX_SNOC_L]
QED

(* -------------------------------------------------------------------------- *)
(* The relationship between count1 and count. I'm surprised that a search     *)
(* for this theorem returned no results.                                      *)
(* -------------------------------------------------------------------------- *)
Theorem count1_count:
  ∀n.
    count1 n = count (n + 1)
Proof
  rw[]
QED

Theorem encode_recursive_parity_equation_take_el_sing:
  ∀ps qs ts i bs x.
    i + 1 ≤ LENGTH bs ⇒
    encode_recursive_parity_equation
    (ps,qs)
    (encode_recursive_parity_equation_state (ps,qs) ts (TAKE i bs))
    [EL i bs] =
    [EL i (encode_recursive_parity_equation (ps,qs) ts bs)]
Proof
  rw[]
  >> qspecl_then [‘i’,‘ps’, ‘qs’, ‘ts’, ‘TAKE (i + 1) bs’]
                 assume_tac
                 drop_encode_recursive_parity_equation
  >> gvs[LENGTH_TAKE]
  >> gvs[TAKE_TAKE,
         DROP_TAKE]
  >> pop_assum (fn th => PURE_REWRITE_TAC[GSYM th])
  >> gvs[encode_recursive_parity_equation_take]
  >> gvs[DROP_TAKE]
QED

Theorem event_srcc_parity_bit_takes_value_inter_input_state:
  ∀n m ps qs ts b i σ c_p.
    i < n ⇒
    (event_state_takes_value n m (ps,qs) ts i σ)
    ∩ (event_input_bit_takes_value n m i b)
    ∩ (event_srcc_parity_bit_takes_value (ps,qs) n m ts i c_p) =
    if
    encode_recursive_parity_equation (ps,qs) σ [b] = [c_p]
    then
      (event_state_takes_value n m (ps,qs) ts i σ)
      ∩ (event_input_bit_takes_value n m i b)
    else
      ∅
Proof
  rw[]
  >- (gvs[event_state_takes_value_def,
          event_input_bit_takes_value_def,
          event_srcc_parity_bit_takes_value_def]
      >> rw[EXTENSION] >> EQ_TAC >> rw[]
      >> gvs[encode_recursive_parity_equation_take_el_sing]
     )
  >> rw[EXTENSION]
  >> CCONTR_TAC >> gvs[]
  >> qpat_x_assum ‘_ ≠ _’ mp_tac >> gvs[]
  >> gvs[event_state_takes_value_def,
         event_input_bit_takes_value_def,
         event_srcc_parity_bit_takes_value_def]
  >> gvs[encode_recursive_parity_equation_take_el_sing]
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
(*                                                                            *)
(* Possible improvement: not sure if 0 < p ∧ p < 1 is necessary              *)
(* -------------------------------------------------------------------------- *)
Theorem split_mdr_events_prob:
  ∀n m p ps qs ts bs σs cs_p.
    0 < p ∧ p < 1 ∧
    LENGTH bs = n ∧
    LENGTH σs = n + 1 ∧
    LENGTH cs_p = n ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_input_state_parity (ps,qs) n m ts (bs,σs,cs_p)) =
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
  rw[]
  (* It's more convenient for LENGTH bs*)
  >> sg ‘LENGTH cs_p = LENGTH bs’ >> gvs[] 
  (* Step 1: Split P(bs) up *)
  >> kall_tac prob_event_input_string_starts_with_decompose
  (* Step 2: Split σs away from P(bs,σs) *)
  >> sg ‘∀n m p (ps : bool list) qs ts bs σs.
           0 < p ∧ p < 1 ∧
           LENGTH bs = n ∧
           σs ≠ [] ∧
           LENGTH σs ≤ n + 1 ⇒
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
  >- (rpt (pop_assum kall_tac)
      >> rpt gen_tac
      >> strip_tac
      >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[le_lt]
      >> SPEC_ALL_TAC
      >> Induct_on ‘σs’ using SNOC_INDUCT >- gvs[] (* Base case: σs = [] *)
      >> rw[]
      >> gvs[HD_SNOC]
      >> Cases_on ‘σs = []’ (* Second base case: σs = σ::[] *)
      >- (gvs[]
          >> gvs[event_state_sequence_starts_with_sing,
                 event_state_takes_value_zero]
          >> rw[]
         )
      (* Inductive step *)
      (* Break down SNOC *)
      >> gvs[event_state_sequence_starts_with_snoc]
      >> gvs[ADD1]
      (* Better names *)
      >> qmatch_goalsub_abbrev_tac ‘prob sp (e1 ∩ (e2 ∩ e3)) = RHS’
      (* Introduce events which subsume e3 *)
      >> qabbrev_tac ‘e4 = event_input_bit_takes_value
                           (LENGTH bs) m (LENGTH σs - 1) (EL (LENGTH σs - 1) bs)’
      >> qabbrev_tac ‘e5 = event_state_takes_value
                           (LENGTH bs) m (ps,qs) ts (LENGTH σs - 1)
                           (EL (LENGTH σs - 1) σs)’
      >> Q.SUBGOAL_THEN ‘e1 ∩ (e2 ∩ e3) = e1 ∩ (e2 ∩ (e3 ∩ e4 ∩ e5))’
          (fn th => gvs[th])
      >- (‘e1 ∩ (e2 ∩ e3) = (e1 ∩ e4) ∩ ((e2 ∩ e5) ∩ e3)’ suffices_by ASM_SET_TAC[]
          >> ‘e1 = e1 ∩ e4 ∧ e2 = e2 ∩ e5’ suffices_by metis_tac[]
          >> conj_tac
          >- (unabbrev_all_tac
              >> DEP_PURE_ONCE_REWRITE_TAC[event_input_string_starts_with_inter_event_input_bit_takes_value]
              >> gvs[]
              >> Cases_on ‘bs’ >> gvs[]
             )
          >> unabbrev_all_tac
          >> DEP_PURE_ONCE_REWRITE_TAC[event_state_sequence_starts_with_inter_event_state_takes_value]
          >> gvs[]
          >> Cases_on ‘σs’ >> gvs[]
         )
      (* Subsume e3, and introduce a factor to handle the case in which e3
         is being taken with regards to an invalid state *)
      >> Q.SUBGOAL_THEN ‘prob sp (e1 ∩ (e2 ∩ (e3 ∩ e4 ∩ e5))) = prob sp (e1 ∩ (e2 ∩ (e4 ∩ e5))) * cond_prob sp e3 (e5 ∩ e4)’
          (fn th => PURE_REWRITE_TAC[th])
      >- (Cases_on ‘e5 ∩ e4 = ∅’
          (* If the denominator of our conditional probability is the empty
             event, we treat this as a special case to avoid having an invalid
             conditional probability *)
          >- gvs[AC INTER_COMM INTER_ASSOC, Abbr ‘sp’, PROB_EMPTY]
          (* Break the conditional probability down so that its numerator is
             an intersection of events, so that we can simplify this
             intersection at the same time as we simplify the other equivalent
             intersection. *)
          >> gvs[cond_prob_def, AC INTER_COMM INTER_ASSOC]
          (* Depending on whether e3 is valid with respect to e4 and e5, the
             intersection either breaks down to e4 ∩ e5 or to ∅ *)
          >> sg ‘e3 ∩ e4 ∩ e5 = e4 ∩ e5 ∨ e3 ∩ e4 ∩ e5 = ∅’
          >- (Q.SUBGOAL_THEN ‘e3 ∩ e4 ∩ e5 = e5 ∩ e4 ∩ e3’
               (fn th => PURE_REWRITE_TAC[th])
              >- gvs[AC INTER_COMM INTER_ASSOC]
              >> gvs[Abbr ‘e3’, Abbr ‘e4’, Abbr ‘e5’]
              >> DEP_PURE_ONCE_REWRITE_TAC[event_state_input_step]
              >> conj_tac
              >- (Cases_on ‘bs’ >> Cases_on ‘σs’ >> gvs[])
              >> rw[]
              >> gvs[AC INTER_COMM INTER_ASSOC]
             )
          >- (gvs[AC INTER_COMM INTER_ASSOC]
              (* The top and bottom of the division are identical, so this
                 factor reduces to 1, if the denominator is not zero and is
                 finite. *)
              >> DEP_PURE_ONCE_REWRITE_TAC[div_refl]
              >> conj_tac
              >- (conj_tac
                  (* Denominator is not zero *)
                  >- (gvs[Abbr ‘sp’]
                      >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
                      >> gvs[Abbr ‘e4’, Abbr ‘e5’, EVENTS_INTER]
                     )
                  (* Denominator is finite *)
                  >> gvs[PROB_FINITE, Abbr ‘sp’, Abbr ‘e4’, Abbr ‘e5’, EVENTS_INTER]
                 )
              >> gvs[]
             )
          >> gvs[AC INTER_COMM INTER_ASSOC]
          >> gvs[Abbr ‘sp’, PROB_EMPTY]
          >> disj2_tac
          >> irule zero_div
          >> gvs[prob_ecc_bsc_prob_space_zero,
                 Abbr ‘e4’, Abbr ‘e5’, EVENTS_INTER]
         )
      (* Remove events which were introduced to subsume e3 (they are, in
          turn, subsumed into e1 and e2) *)
      >> Q.SUBGOAL_THEN ‘e1 ∩ (e2 ∩ (e4 ∩ e5)) = e1 ∩ e2’ (fn th => gvs[th])
      >- (‘e1 ∩ (e2 ∩ (e4 ∩ e5)) = (e1 ∩ e4) ∩ (e2 ∩ e5)’ by gvs[AC INTER_COMM INTER_ASSOC]
          >> pop_assum (fn th => PURE_REWRITE_TAC[th])
          >> ‘e1 = e1 ∩ e4 ∧ e2 = e2 ∩ e5’ suffices_by metis_tac[]
          (* This is copy/pasted from where the exact same thing was proven
             when introducing events to subsume e3 *)
          >> conj_tac
          >- (unabbrev_all_tac
              >> DEP_PURE_ONCE_REWRITE_TAC[event_input_string_starts_with_inter_event_input_bit_takes_value]
              >> gvs[]
              >> Cases_on ‘bs’ >> gvs[]
             )
          >> unabbrev_all_tac
          >> DEP_PURE_ONCE_REWRITE_TAC[event_state_sequence_starts_with_inter_event_state_takes_value]
          >> gvs[]
          >> Cases_on ‘σs’ >> gvs[]
         )
      (* Apply the inductive hypothesis and move the new term into the product
         of terms, finishing the proof *)
      >> unabbrev_all_tac
      >> gvs[]
      >> qmatch_abbrev_tac ‘C1 * C2 * ind * step = C1 * C2 * combined : extreal’
      >> ‘ind * step = combined’ suffices_by rw[AC mul_comm mul_assoc]
      >> unabbrev_all_tac
      >> qmatch_goalsub_abbrev_tac ‘∏ f1 S1 * step = ∏ f2 S2’
      (* Split S2 into new_elt INSERT S1, so we can use the inductive step
         on the product in order to bring the element out *)
      >> Q.SUBGOAL_THEN ‘S2 = (LENGTH σs - 1) INSERT S1’
          (fn th => gvs[th] >> gvs[Abbr ‘S2’])
      >- (unabbrev_all_tac
          >> ‘LENGTH σs = (LENGTH σs - 1) + 1’ by (Cases_on ‘σs’ >> gvs[])
          >> metis_tac[count_add1]
         )
      (* Bring the element out of S2 *)
      >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 EXTREAL_PROD_IMAGE_THM]
      >> conj_tac >- (unabbrev_all_tac >> gvs[])
      >> unabbrev_all_tac >> gvs[]
      >> gvs[]
      >> qmatch_abbrev_tac ‘ind1 * step1 = step2 * ind2 : extreal’
      >> ‘ind1 = ind2 ∧ step1 = step2’ suffices_by gvs[AC mul_comm mul_assoc]
      >> conj_tac
      >- (unabbrev_all_tac
          >> irule EXTREAL_PROD_IMAGE_EQ
          >> rw[]
          >> gvs[EL_SNOC]
         )
      >> unabbrev_all_tac
      >> ‘LENGTH σs - 1 + 1 = LENGTH σs’ by (Cases_on ‘σs’ >> gvs[])
      >> gvs[]
      >> gvs[EL_SNOC, EL_LENGTH_SNOC]
     )     
  (* Step 3: Split cs away from P(bs,σs,cs) *)
  >> sg ‘∀n m p ps qs ts bs σs cs_p.
           0 ≤ p ∧ p ≤ 1 ∧
           0 < p ∧ p < 1 ∧
           LENGTH bs = n ∧
           LENGTH σs = n + 1 ∧
           LENGTH cs_p ≤ n ⇒
           prob (ecc_bsc_prob_space n m p)
                ((event_input_string_starts_with n m bs)
                 ∩ (event_state_sequence_starts_with n m (ps,qs) ts σs)
                 ∩ (event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p))
           = prob (ecc_bsc_prob_space n m p)
                  ((event_input_string_starts_with n m bs)
                   ∩ (event_state_sequence_starts_with n m (ps,qs) ts σs)) *
             ∏ (λi.
                  cond_prob (ecc_bsc_prob_space n m p)
                            (event_srcc_parity_bit_takes_value (ps,qs) n m ts i
                                                               (EL i cs_p))
                            ((event_state_takes_value n m (ps,qs) ts i (EL i σs))
                             ∩ (event_input_bit_takes_value n m i (EL i bs)))
               ) (count (LENGTH cs_p))’        
  >- (rpt (pop_assum kall_tac)
      >> rw[]
      >> Induct_on ‘cs_p’ using SNOC_INDUCT
      >- (gvs[event_srcc_parity_string_starts_with_def]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 1 event_input_string_starts_with_event_universal]
          >> conj_tac
          >- (qexists ‘p’
              >> gvs[EVENTS_INTER, event_input_string_starts_with_is_event,
                     event_state_sequence_starts_with_is_event]
             )
          >> gvs[]
         )
      >> rw[]
      >> qmatch_abbrev_tac ‘prob sp (e1 ∩ e2 ∩ e3_with_step) = prob sp (e1 ∩ e2) * ∏ f s’
      >> qmatch_asmsub_abbrev_tac ‘prob sp (e1 ∩ e2 ∩ e3_without_step) = prob sp (e1 ∩ e2) * ∏ _ _’
      (* Each step will add one of the factors in the product *)
      >> Q.SUBGOAL_THEN ‘prob sp (e1 ∩ e2 ∩ e3_with_step) =
                         prob sp (e1 ∩ e2 ∩ e3_without_step) *
                         f (LENGTH cs_p)’
          (fn th => PURE_REWRITE_TAC[th])          
      >- (gvs[Abbr ‘e3_with_step’]
          (* Break up the SNOC, to move towards the inductive hypothesis on the
             left hand side *)
          >> gvs[event_srcc_parity_string_starts_with_snoc]
          (* Apply the inductive hypothesis to move the RHS towards the LHS *)
          >> qmatch_abbrev_tac ‘_ = _ * ∏ f2 _ * f _’
          >> qpat_x_assum ‘prob _ _ = prob _ _ * ∏ _ _ ’
                          (fn th => gvs[ReqD (GSYM th)])
          (* Name the event we are adding in this step *)
          >> qmatch_abbrev_tac ‘prob _ (_ ∩ _ ∩ (_ ∩ e_step)) = _’
          (* Introduce events to subsume e_step (on both the LHS and RHS,
             to maintain concsistency between each side) *)
          >> qabbrev_tac ‘e4 = event_input_bit_takes_value
                               (LENGTH bs) m (LENGTH cs_p) (EL (LENGTH cs_p) bs)
                         ’
          >> qabbrev_tac ‘e5 = event_state_takes_value
                               (LENGTH bs) m (ps,qs) ts (LENGTH cs_p) (EL (LENGTH cs_p) σs)’
          >> ‘e1 = e1 ∩ e4’ by gvs[Abbr ‘e1’, Abbr ‘e4’]
          >> first_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
          >> ‘e2 = e2 ∩ e5’ by gvs[Abbr ‘e2’, Abbr ‘e5’]
          >> first_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
          (* Move events to subsume e_step to the appropriate location *)
          >> Q.SUBGOAL_THEN ‘(e1 ∩ e4) ∩ (e2 ∩ e5) ∩ (e3_without_step ∩ e_step) =
                             (e1 ∩ e2 ∩ e3_without_step ∩ (e_step ∩ e4 ∩ e5))’
              (fn th => PURE_REWRITE_TAC[th])
          >- gvs[AC INTER_COMM INTER_ASSOC]
          (* Do the same thing to the RHS *)
          >> Q.SUBGOAL_THEN ‘(e1 ∩ e4) ∩ (e2 ∩ e5) ∩ e3_without_step =
                             e1 ∩ e2 ∩ (e3_without_step ∩ (e4 ∩ e5))’
              (fn th => PURE_REWRITE_TAC[th])
          >- gvs[AC INTER_COMM INTER_ASSOC]
          (* Treat the special case where e4 ∩ e5 = ∅, because that will end up
             being the denominator in the application of cond_prob in the
             application of f *)
          >> Cases_on ‘e4 ∩ e5 = ∅’
          >- (gvs[]
              >> gvs[GSYM INTER_ASSOC]
              >> gvs[Abbr ‘sp’]
             )
          (* Subsume e_step. We either get the empty set if the step is invalid
             with respect to the existing events, or we get the intersection
             of the events used to subsume it. *)
          >> Q.SUBGOAL_THEN ‘e_step ∩ e4 ∩ e5 = ∅ ∨ e_step ∩ e4 ∩ e5 = e4 ∩ e5’
              assume_tac
          >- (‘e5 ∩ e4 ∩ e_step = ∅ ∨ e5 ∩ e4 ∩ e_step = e5 ∩ e4’ suffices_by gvs[AC INTER_COMM INTER_ASSOC]
              >> unabbrev_all_tac
              >> gvs[event_srcc_parity_bit_takes_value_inter_input_state]
             )
          >> gvs[]
          (* Prove the case where we get the empty set *)
          >- (gvs[PROB_EMPTY, Abbr ‘sp’]
              >> disj2_tac
              >> gvs[Abbr ‘f’]
              (* The numerator of the conditional probability is the
                 intersection we have information about *)
              >> gvs[cond_prob_def]
              >> gvs[EL_LENGTH_SNOC]
              >> gvs[AC INTER_COMM INTER_ASSOC]
              >> DEP_PURE_ONCE_REWRITE_TAC[zero_div]
              >> gvs[prob_ecc_bsc_prob_space_zero, Abbr ‘e4’, Abbr ‘e5’]
             )
          (* Prove the case where the subsumed event simply disappears
             without taking e4 and e5 along with it. *)
          >> gvs[AC INTER_COMM INTER_ASSOC]
          (* We just need to prove that the added factor in this case is equal
             to 1, because the new event has disappeared without affecting the
             event *)
          >> ‘f (LENGTH cs_p) = 1’ suffices_by gvs[]
          >> gvs[Abbr ‘f’]
          (* In this case, the conditional probability simplifies to
             prob (e4 ∩ e5) / prob (e4 ∩ e5), which simplifies to 1 assuming
             we don't have 0, +∞, or −∞ *)
          >> gvs[cond_prob_def]
          >> gvs[EL_LENGTH_SNOC]
          >> gvs[AC INTER_COMM INTER_ASSOC]
          >> DEP_PURE_ONCE_REWRITE_TAC[div_refl] >> gvs[]
          >> conj_tac
          (* The probability is nonzero: we earlier handled the situation of
             e4 ∩ e5 = ∅ *)
          >- gvs[Abbr ‘sp’, Abbr ‘e4’, Abbr ‘e5’, prob_ecc_bsc_prob_space_zero]
          (* The probability is not infinite because no probability is *)
          >> gvs[Abbr ‘sp’, Abbr ‘e4’, Abbr ‘e5’]
         )         
      (* Use the inductive hypothesis and drag the new factor into the
         product from the inductive step. In order to use the inductive
         hypothesis, we first handle the case where cs_p has grown too large
         to be valid *)
      >> Cases_on ‘LENGTH cs_p ≤ LENGTH bs’ >> gvs[]
      >> qmatch_abbrev_tac ‘C * ∏ f2 s2 * step = C * ∏ f s’
      >> ‘∏ f s = ∏ f2 s2 * step’ suffices_by gvs[AC mul_comm mul_assoc]
      >> gvs[Abbr ‘step’, Abbr ‘s’, Abbr ‘s2’, Abbr ‘C’]
      >> gvs[COUNT_SUC]
      >> gvs[EXTREAL_PROD_IMAGE_THM]
      >> gvs[mul_comm]
      >> qmatch_goalsub_abbrev_tac ‘C * LHS = C * RHS’
      >> ‘LHS = RHS’ suffices_by gvs[]
      >> gvs[Abbr ‘LHS’, Abbr ‘RHS’, Abbr ‘C’]
      >> irule EXTREAL_PROD_IMAGE_EQ
      >> rw[]
      >> gvs[Abbr ‘f’, Abbr ‘f2’]
      >> gvs[EL_SNOC]
     )         
  (* Step 4: Combine the subtheorems to arrive at the final result *)
  >> gvs[event_input_state_parity_def]
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> conj_tac
  >- gvs[le_lt]
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> conj_tac
  >- (gvs[]
      >> Cases_on ‘σs’ >> gvs[]
     )
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_event_input_string_starts_with_decompose]
  >> conj_tac
  >- gvs[le_lt]
  >> gvs[]
QED

(* Possible improvement: can we remove some of these assumptions, especially
   LENGTH ps = LENGTH ts + 1?*)

Theorem event_input_bit_takes_value_inter_event_input_state_parity:
  ∀n m i x ps qs ts bs σs cs_p.
    i < LENGTH bs ⇒
    (event_input_bit_takes_value n m i x)
    ∩ (event_input_state_parity (ps,qs) n m ts (bs,σs,cs_p)) =
    if
    (EL i bs = x)
    then
      event_input_state_parity (ps,qs) n m ts (bs,σs,cs_p)
    else
      ∅
Proof
  rpt gen_tac
  >> disch_tac
  >> gvs[event_input_state_parity_def]
  >> qmatch_goalsub_abbrev_tac ‘ev_ib ∩ (ev_is ∩ ev_ssq ∩ ev_pa)’
  >> Q.SUBGOAL_THEN ‘ev_ib ∩ (ev_is ∩ ev_ssq ∩ ev_pa) =
                     (ev_is ∩ ev_ib) ∩ ev_ssq ∩ ev_pa’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- gvs[AC INTER_COMM INTER_ASSOC]
  >> unabbrev_all_tac
  >> rw[]
QED

(* -------------------------------------------------------------------------- *)
(* The event with a given input, state sequence, and encoded bits corresponds *)
(* to the event with a given input.                                           *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_state_parity_event_input_string_starts_with:
  ∀ps qs n m ts bs σs cs_p.
    LENGTH bs = n ∧
    LENGTH σs = n + 1 ∧
    LENGTH cs_p = n ⇒
    event_input_state_parity (ps,qs) n m ts (bs,σs,cs_p) =
    if
    σs = encode_recursive_parity_equation_state_sequence (ps,qs) ts bs ∧
    cs_p = encode_recursive_parity_equation (ps,qs) ts bs
    then
      event_input_string_starts_with n m bs
    else
      ∅
Proof
  rw[]
  >- (gvs[event_input_state_parity_def]
      >> gvs[inter_input_state_eq_input]
      >> gvs[inter_input_parity_eq_input]
     )
  >> gvs[event_input_state_parity_def]
  >> gvs[inter_input_state_eq_input]
  >> rw[] >> gvs[]
  >> gvs[inter_input_parity_eq_input]
QED

Theorem event_input_state_parity_event_sent_string_starts_with:
  ∀ps qs n m ts bs σs cs_p.
    LENGTH bs = n ∧
    LENGTH σs = n + 1 ∧
    LENGTH cs_p = n ⇒
    event_input_state_parity (ps,qs) n m ts (bs,σs,cs_p) =
    if
    σs = encode_recursive_parity_equation_state_sequence (ps,qs) ts bs ∧
    cs_p = encode_recursive_parity_equation (ps,qs) ts bs
    then
      event_sent_string_starts_with
      (encode_recursive_parity_equation_with_systematic (ps,qs) ts)
      n
      m
      (encode_recursive_parity_equation_with_systematic (ps,qs) ts bs)
    else
      ∅
Proof
  rw[]
  >- (gvs[event_input_state_parity_def]
      >> gvs[inter_input_state_eq_input]
      >> gvs[inter_input_parity_eq_sent]
     )
  >> gvs[event_input_state_parity_def]
  >> gvs[inter_input_state_eq_input]
  >> rw[] >> gvs[]
  >> gvs[inter_input_parity_eq_sent]
QED

(* -------------------------------------------------------------------------- *)
(* The event with a given input, state sequence, and encoded bits corresponds *)
(* to the event with the corresponding encoded bits, assuming injectivity     *)
(* -------------------------------------------------------------------------- *)
Theorem event_input_state_parity_event_srcc_parity_string_starts_with:
  ∀ps qs n m ts bs σs cs_p.
    LENGTH bs = n ∧
    LENGTH σs = n + 1 ∧
    LENGTH cs_p = n ∧
    LENGTH ps = LENGTH ts + 1 ∧
    LAST ps ⇒
    event_input_state_parity (ps,qs) n m ts (bs,σs,cs_p) =
    if
    σs = encode_recursive_parity_equation_state_sequence (ps,qs) ts bs ∧
    cs_p = encode_recursive_parity_equation (ps,qs) ts bs
    then
      event_srcc_parity_string_starts_with (ps,qs) n m ts cs_p
    else
      ∅
Proof
  rw[]
  >- (gvs[event_input_state_parity_def]
      >> gvs[inter_input_state_eq_input]
      >> gvs[inter_input_parity_eq_parity]
     )
  >> gvs[event_input_state_parity_def]
  >> gvs[inter_input_state_eq_input]
  >> rw[] >> gvs[]
  >> gvs[inter_input_parity_eq_parity]
QED

(* -------------------------------------------------------------------------- *)
(* General outline of plan of proof, following Chapter 6 of Modern Coding     *)
(* Theory:                                                                    *)
(*                                                                            *)
(* 1. MAP decoder = argmax p(b_s | ds)                                        *)
(* 2.             = argmax Σ p(bs, cs_p, σs | ds) over bs, cs_p, σs           *)
(* 3.             = argmax Σ p(ds | bs, cs_p, σs) p(bs, cs_p, σs) over ''     *)
(* 4.  p(bs, cs_p, σs) = p(σ_0)p(b_0)p(c_0_p,σ_1|b_0,σ_0)p(b_1)               *)
(*                         p(c_1_p,σ_2|b_1,σ_1)p(b_2)p(c_2_p,σ_3|b_2,σ_2)...  *)
(* 5.  p(ds | bs, cs_p, σs) = Π P(d_i | c_i)                                  *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_encode_recursive_parity_equation_with_systematic:
  ∀ps qs ts n m p ds.
    let
      enc = encode_recursive_parity_equation_with_systematic (ps, qs) ts;
    in
      0 < p ∧ p < 1 ∧
      LENGTH ds = m ∧
      m = 2 * n ⇒
      map_decoder_bitwise enc n m p ds =
      MAP (λi.
             argmax_bool
             (λx. ∑ ARB (mdr_summed_out_values_2 n ts i x)
             )
          )
          (COUNT_LIST n)
Proof
  (* ------------------------------------------------------------------------ *)
  (* Focus on proving that the inside of the argmax on the LHS is equal to    *)
  (* the inside of the argmax on the RHS, up to a multiplicative constant.    *)
  (* ------------------------------------------------------------------------ *)
  rw[]
  (* More standard properties showing that p represents a probability *)
  >> ‘0 ≤ p ∧ p ≤ 1’ by gvs[lt_le]
  (* Definition of bitwise decoder *)
  >> gvs[map_decoder_bitwise_def]
  (* We care about the inside of the MAP *)
  >> rw[MAP_EQ_f]
  (* Simplify assumption *)
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
  (* Flip the equality *)
  >> irule EQ_SYM
  (* Nicer names *)
  >> qmatch_abbrev_tac ‘C * cond_prob sp e1 e2 = RHS’
  (* ------------------------------------------------------------------------ *)
  (* We are working with p(b_s | ds). The event e1 corresponds to b_s, and    *)
  (* the event e2 corresponds to ds. To arrive at the next step, we need to   *)
  (* sum over σs, cs_p, and the remaining elements of bs.                     *)
  (* ------------------------------------------------------------------------ *)
  >> qspecl_then [‘sp’,
                  ‘event_input_state_parity (ps,qs) n (LENGTH ds) ts’,
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
      (* If bs1 ≠ bs2, then the input string event is disjoint *)
      >> Cases_on ‘bs1 ≠ bs2’
      >- (gvs[event_input_state_parity_def, event_input_string_starts_with_def,
              mdr_summed_out_values_2_alt]
          >> disj1_tac >> disj1_tac
          >> metis_tac[IS_PREFIX_LENGTH_ANTI]
         )
      >> gvs[]
      (* If σs1 ≠ σs2, then the next part is disjoint *)
      >> Cases_on ‘σs1 ≠ σs2’
      >- (gvs[event_input_state_parity_def, event_state_sequence_starts_with_def,
              mdr_summed_out_values_2_alt]
          >> disj1_tac
          >> metis_tac[IS_PREFIX_LENGTH_ANTI,
                       encode_recursive_parity_equation_state_sequence_length]
         )
      >> gvs[]
      (* We have cs1_p ≠ cs2_p, and so the final part is disjoint *)
      >> gvs[event_input_state_parity_def, event_srcc_parity_string_starts_with_def,
             mdr_summed_out_values_2_alt]
      >> metis_tac[IS_PREFIX_LENGTH_ANTI,
                   encode_recursive_parity_equation_length]
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
      >> gs[event_input_state_parity_def,
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
     )
  (* ------------------------------------------------------------------------ *)
  (* Focus on proving the equivalence of the inside of the sum                *)
  (* ------------------------------------------------------------------------ *)
  >> irule EXTREAL_SUM_IMAGE_EQ'
  >> gvs[]
  >> qx_gen_tac ‘w’
  >> disch_tac
  >> namedCases_on ‘w’ ["bs σs cs_p"]
  (* ------------------------------------------------------------------------ *)
  (* We have completed step 2, and are now on to step 3.                      *)
  (*                                                                          *)
  (* That is, we have argmax Σ p(bs, cs_p, σs | ds) over bs, cs_p, σs,        *)
  (* and we want argmax Σ p(ds | bs, cs_p, σs) p(bs, cs_p, σs) over ''        *)
  (*                                                                          *)
  (* That is, we apply Bayes' rule here.                                      *)
  (* ------------------------------------------------------------------------ *)
  >> DEP_PURE_ONCE_REWRITE_TAC[BAYES_RULE_GENERALIZED]
  >> conj_tac
  >- (rpt conj_tac
      >- gvs[]
      >- gvs[]
      >- (irule EVENTS_INTER >> gvs[]
         )
      >- gvs[]
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
  (* TODO FIX THE GENERAL IDEA HERE IS THAT IN THE SPEICAL CASE WHERE OUR
     BS ΣS CS_P IS INVALID, VAL2 WILL BE 0, IN WHICH CASE THE LEFT AND RIGHT
     WILL BE ZERO. ITS IMPORTANT TO HANDLE THIS BECAUSE VAL1 WILL BE INVALID.
  >> sg ‘input_state_pariry_valid (ps,qs) ts (bs, σs, cs_p)’
  (* Introduce a variable b which tells us whether the current choice of
     (bs, σs, cs_p) is valid, or if it is self-contradictory (since a given
     choice of bs will correspond to only one specific choice of σs and cs_p) *) 
  >> qabbrev_tac ‘b = input_state_parity_valid (ps,qs) ts (bs,σs,cs_p)’
  (* When the values being summed over are invalid (i.e. we have ¬b), then
     val2 will equal 0. 
, so we can remove the if _ then _ else _.
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
      >- gvs[]
      >> metis_tac[mdr_summed_out_values_event_input_state_parity_empty]
     )
   *)
  (* ------------------------------------------------------------------------ *)
  (* We are currently up to step 4: split the probability of a given input,   *)
  (* state sequence and output into probabilities based on the transitions    *)
  (* through the state machine. That is:                                      *)
  (*                                                                          *)
  (* val2 = p(σ_0)p(b_0)p(c_0_p,σ_1|b_0,σ_0)p(b_1)p(c_1_p,σ_2|b_1,σ_1)p(b_2)  *)
  (* p(c_2_p,σ_3|b_2,σ_2)...                                                  *)
  (*                                                                          *)
  (* This is what is proven in split_mdr_events_prob.                         *)
  (* ------------------------------------------------------------------------ *)
  >> sg ‘val2 = TODO2’
  >- (unabbrev_all_tac
      >> gvs[event_input_bit_takes_value_event_input_state_parity_el_i_x,
             mdr_summed_out_values_2_def]
      >> gvs[split_mdr_events_prob]
      >> cheat
     )
  >> gvs[]
  (* ------------------------------------------------------------------------ *)
  (* We are now up to step 5: split the probability of an error over the      *)
  (* channel up into the individual probabilities of an error in each bit.    *)
  (*                                                                          *)
  (* That is, p(ds | bs, cs_p, σs) = Π P(d_i | c_i)                           *)
  (*                                                                          *)
  (* We are splitting val1 up.                                                *)
  (* ------------------------------------------------------------------------ *)
  >> sg ‘input_state_parity_valid (ps,qs) ts (bs, σs, cs_p) ⇒ val1 = TODO1’
  >- (unabbrev_all_tac
      (* As a first step, we're going to want to head towards
         p(ds | cs_p), so get rid of the input bit events and the state
         events. *)
      >> DEP_PURE_ONCE_REWRITE_TAC[event_input_bit_takes_value_inter_event_input_state_parity]
      >> conj_tac >- gvs[mdr_summed_out_values_2_def]
      >> REVERSE (rw[])
      >- gvs[mdr_summed_out_values_2_def]
      >> cheat
     (*
      (* The event with a given input, state, and parity bits is equal to the
         event with the given parity bits, assuming injectivity *)
      >> DEP_PURE_ONCE_REWRITE_TAC[event_input_state_parity_event_sent_string_starts_with]
      >> conj_tac >- gvs[mdr_summed_out_values_2_def]
      (* Handle the case where we have an invalid state sequence or parity bits *)
      >> REVERSE (rw[])
      >- (gvs[]
          >> ‘F’ suffices_by gvs[]
          >> pop_assum mp_tac >> gvs[]
          >> gvs[input_state_parity_valid_def]
         )
      (* Now that we have simplified our conditional probability to just be
         in terms of the received string taking a value given that the sent
         string takes a value, it is now more obvious that this conditional
         probability is the product of the probabilities of each individual
         received bit given the corresponding sent bit. *)
      >> DEP_PURE_ONCE_REWRITE_TAC[cond_prob_string_given_sent_prod]
      >> conj_tac >- gvs[mdr_summed_out_values_2_def]
      (* While this isn't a product, it's an explicit expression for the
         probability, which will be equal to the product *)
      >> cheat
         *)
     )
  (*  >> ‘C * val1 * val2 = C * TODO1 * val2’ by (Cases_on ‘b’ >> gvs[])
  >> qpat_x_assum ‘b ⇒ val1 = _’ kall_tac
  >> qpat_x_assum ‘Abbrev (val1 = _)’ kall_tac
  >> pop_assum (fn th => PURE_REWRITE_TAC[th])
  >> qmatch_abbrev_tac ‘C * val1 * val2 = _’
  (* We can eliminate x because it is simply equal to EL i bs*)
  >> drule mdr_summed_out_values_2_el_i_x
  >> disch_tac >> gvs[]*)
  >> cheat
QED

