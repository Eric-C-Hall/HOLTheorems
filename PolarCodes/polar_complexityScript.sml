(* ========================================================================= *)
(*   Algorithmic Time Complexity of Polar Encoding and Divide-and-Conquer    *)
(*   Butterfly Successive Cancellation Decoding in O(N log N) Operations     *)
(*   (Erdal Arıkan, 2009, arXiv:0807.3917, Sections VII-C, VIII-B, & IX).    *)
(*                                                                           *)
(*   Written by Gemini (Google DeepMind AI agent).                           *)
(* ========================================================================= *)

Theory polar_complexity

Ancestors
  combin arithmetic pair list rich_list pred_set logroot
  real real_sigma extreal_base extreal measure probability
  bitstring bxor_lemmas interleave fundamental
  jared_yeager_prod_list ecc_prob_space complexity
  memoryless_channel bhattacharyya capacity
  polar_encode combine_channel split_channel bdmc
  successive_cancellation_decoder

Libs
  dep_rewrite hurdUtils numLib realLib;

val _ = clear_overloads_on "interleave";
val _ = remove_termtok {term_name = "interleave", tok = "interleave"};
val _ = overload_on ("interleave", “interleave$interleave”);
val _ = hide "W";
val _ = hide "S";
val _ = hide "K";

(* ------------------------------------------------------------------------- *)
(* Block 1: Polar Encoding Operation-Count Model & O(N log N) Complexity     *)
(* ------------------------------------------------------------------------- *)

(* Recursive primitive-operation count of functional polar_encode
   (Erdal Arıkan, 2009, Section VII-C, pp. 14-15):
   - Base case LENGTH inputs <= 1: 0 operations.
   - Recursive step LENGTH inputs >= 2:
       * LENGTH inputs data-routing steps for deinterleave 2 inputs,
       * MAX (LENGTH even_inputs) (LENGTH odd_inputs) scalar XOR operations
         for bxor even_inputs odd_inputs,
       * LENGTH xored cons steps to append polar_encode xored ++
         polar_encode odd_inputs (since LENGTH (polar_encode xored) =
         LENGTH xored),
       * plus recursive operation counts on xored and odd_inputs.

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_encode_cost_def:
  polar_encode_cost (inputs : bool list) : num =
    if LENGTH inputs ≤ 1 then 0
    else
      let
        even_odd_inputs = deinterleave 2 inputs;
        even_inputs = EL 0 even_odd_inputs;
        odd_inputs = EL 1 even_odd_inputs;
        xored = bxor even_inputs odd_inputs
      in
        LENGTH inputs +
        MAX (LENGTH even_inputs) (LENGTH odd_inputs) +
        LENGTH xored +
        polar_encode_cost xored +
        polar_encode_cost odd_inputs
Termination
  WF_REL_TAC ‘measure LENGTH’ >>
  rpt strip_tac >>
  ‘2 ≤ LENGTH inputs ∧ LENGTH inputs MOD 2 < 2’ by simp[] >>
  simp[bxor_length, length_el_deinterleave] >>
  Cases_on ‘LENGTH inputs = 2’ >- gvs[] >>
  ‘2 < LENGTH inputs’ by decide_tac >>
  ‘LENGTH inputs = (LENGTH inputs DIV 2) * 2 + LENGTH inputs MOD 2’
    by metis_tac[DIVISION, DECIDE “0 < 2n”] >>
  rw[] >> decide_tac
End

(* Arıkan's Section VII-C in-place RAM encoder cost model (charging N steps
   for reverse-shuffle R_N and N/2 scalar mod-2 additions, with in-place array
   slice writes rather than functional list append, satisfying
   2 * chi_E(2^n) = 3 * n * 2^n, i.e., chi_E(N) = (3/2) * N * log_2 N).

   Written by Gemini (Google DeepMind AI agent) *)
Definition arikan_encode_ram_cost_def:
  arikan_encode_ram_cost (inputs : bool list) : num =
    if LENGTH inputs ≤ 1 then 0
    else
      let
        even_odd_inputs = deinterleave 2 inputs;
        even_inputs = EL 0 even_odd_inputs;
        odd_inputs = EL 1 even_odd_inputs;
        xored = bxor even_inputs odd_inputs
      in
        LENGTH inputs +
        MAX (LENGTH even_inputs) (LENGTH odd_inputs) +
        arikan_encode_ram_cost xored +
        arikan_encode_ram_cost odd_inputs
Termination
  WF_REL_TAC ‘measure LENGTH’ >>
  rpt strip_tac >>
  ‘2 ≤ LENGTH inputs ∧ LENGTH inputs MOD 2 < 2’ by simp[] >>
  simp[bxor_length, length_el_deinterleave] >>
  Cases_on ‘LENGTH inputs = 2’ >- gvs[] >>
  ‘LENGTH inputs = (LENGTH inputs DIV 2) * 2 + LENGTH inputs MOD 2’
    by metis_tac[DIVISION, DECIDE “0 < 2n”] >>
  rw[] >> decide_tac
End

(* Bit-pattern invariance: polar_encode_cost depends only on input length.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_cost_length_cong:
  ∀u v. LENGTH u = LENGTH v ⇒ polar_encode_cost u = polar_encode_cost v
Proof
  ‘∀m u v. LENGTH u = m ∧ LENGTH v = m ⇒ polar_encode_cost u = polar_encode_cost v’
    suffices_by metis_tac[] >>
  completeInduct_on ‘m’ >> rpt strip_tac >>
  ONCE_REWRITE_TAC[polar_encode_cost_def] >>
  Cases_on ‘m ≤ 1’ >- simp[] >>
  simp[LET_THM] >>
  ‘2 ≤ m ∧ m MOD 2 < 2’ by simp[] >>
  ‘LENGTH (EL 0 (deinterleave 2 u)) = LENGTH (EL 0 (deinterleave 2 v)) ∧
   LENGTH (EL 1 (deinterleave 2 u)) = LENGTH (EL 1 (deinterleave 2 v))’
    by simp[length_el_deinterleave] >>
  ‘LENGTH (bxor (EL 0 (deinterleave 2 u)) (EL 1 (deinterleave 2 u))) =
   LENGTH (bxor (EL 0 (deinterleave 2 v)) (EL 1 (deinterleave 2 v)))’
    by simp[bxor_length] >>
  ‘LENGTH (bxor (EL 0 (deinterleave 2 u)) (EL 1 (deinterleave 2 u))) < m ∧
   LENGTH (EL 1 (deinterleave 2 u)) < m’
    by (simp[bxor_length, length_el_deinterleave] >>
        Cases_on ‘m = 2’ >- gvs[] >>
        ‘m = (m DIV 2) * 2 + m MOD 2’
          by metis_tac[DIVISION, DECIDE “0 < 2n”] >>
        rw[] >> decide_tac) >>
  ‘polar_encode_cost (bxor (HD (deinterleave 2 u)) (EL 1 (deinterleave 2 u))) =
   polar_encode_cost (bxor (HD (deinterleave 2 v)) (EL 1 (deinterleave 2 v)))’
    by (first_assum irule >>
        qexists_tac ‘LENGTH (bxor (EL 0 (deinterleave 2 u)) (EL 1 (deinterleave 2 u)))’ >>
        gvs[]) >>
  pop_assum SUBST1_TAC >>
  ‘polar_encode_cost (EL 1 (deinterleave 2 u)) =
   polar_encode_cost (EL 1 (deinterleave 2 v))’
    by (first_assum irule >>
        qexists_tac ‘LENGTH (EL 1 (deinterleave 2 u))’ >>
        gvs[]) >>
  pop_assum SUBST1_TAC >>
  gvs[]
QED

(* Exact division and modulo by 2 on even multiples 2 * k.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem double_div_mod_2[local,simp]:
  ∀k : num. (2 * k) DIV 2 = k ∧ (2 * k) MOD 2 = 0
Proof
  gen_tac >> ‘2 * k = k * 2’ by decide_tac >>
  pop_assum SUBST1_TAC >> simp[MULT_DIV, MOD_EQ_0]
QED

(* Exact closed-form operation count 2 * n * 2^n on blocks of length 2^n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_cost_pow2:
  ∀n u. LENGTH u = 2 ** n ⇒ polar_encode_cost u = 2 * n * (2 ** n)
Proof
  Induct_on ‘n’
  >- (rpt strip_tac >> ONCE_REWRITE_TAC[polar_encode_cost_def] >> simp[]) >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC[polar_encode_cost_def] >>
  simp[LET_THM] >>
  ‘LENGTH u = 2 * (2 ** n)’ by gvs[EXP] >>
  ‘LENGTH (EL 0 (deinterleave 2 u)) = 2 ** n ∧
   LENGTH (EL 1 (deinterleave 2 u)) = 2 ** n’
    by (match_mp_tac length_deinterleave_2_half >> simp[]) >>
  ‘LENGTH (bxor (EL 0 (deinterleave 2 u)) (EL 1 (deinterleave 2 u))) = 2 ** n’
    by simp[bxor_length] >>
  ‘polar_encode_cost (bxor (HD (deinterleave 2 u)) (EL 1 (deinterleave 2 u))) =
   2 * n * (2 ** n)’ by (first_assum irule >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  ‘polar_encode_cost (EL 1 (deinterleave 2 u)) = 2 * n * (2 ** n)’
    by (first_assum irule >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  gvs[EXP, ADD1, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >> decide_tac
QED

(* Exact closed-form Arıkan Section VII-C RAM cost: 2 * chi_E(2^n) = 3 * n * 2^n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem arikan_encode_ram_cost_pow2:
  ∀n u. LENGTH u = 2 ** n ⇒ 2 * arikan_encode_ram_cost u = 3 * n * (2 ** n)
Proof
  Induct_on ‘n’
  >- (rpt strip_tac >> ONCE_REWRITE_TAC[arikan_encode_ram_cost_def] >> simp[]) >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC[arikan_encode_ram_cost_def] >>
  simp[LET_THM] >>
  ‘LENGTH u = 2 * (2 ** n)’ by gvs[EXP] >>
  ‘LENGTH (EL 0 (deinterleave 2 u)) = 2 ** n ∧
   LENGTH (EL 1 (deinterleave 2 u)) = 2 ** n’
    by (match_mp_tac length_deinterleave_2_half >> simp[]) >>
  ‘LENGTH (bxor (EL 0 (deinterleave 2 u)) (EL 1 (deinterleave 2 u))) = 2 ** n’
    by simp[bxor_length] >>
  ‘2 * arikan_encode_ram_cost
         (bxor (HD (deinterleave 2 u)) (EL 1 (deinterleave 2 u))) =
   3 * n * (2 ** n)’ by (first_assum irule >> gvs[]) >>
  ‘2 * arikan_encode_ram_cost (EL 1 (deinterleave 2 u)) = 3 * n * (2 ** n)’
    by (first_assum irule >> gvs[]) >>
  gvs[EXP, ADD1, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >>
  pop_assum mp_tac >> pop_assum mp_tac >> decide_tac
QED

(* Strict positivity of polar_encode_cost for all non-trivial inputs (LENGTH >= 2).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_cost_pos:
  ∀u. 2 ≤ LENGTH u ⇒ 0 < polar_encode_cost u
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[polar_encode_cost_def] >> simp[LET_THM]
QED

(* Worst-case O(N log N) time complexity of polar encoding
   (Erdal Arıkan, 2009, Section I-C.6 Theorem 5 & Section VII-C, pp. 14-15).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_complexity_nlogn:
  ∃(C : num). 0 < C ∧
    ∀n u. 1 ≤ n ∧ LENGTH u = 2 ** n ⇒
      polar_encode_cost u ≤ C * (2 ** n) * LOG 2 (2 ** n)
Proof
  qexists_tac ‘2’ >> simp[] >> rpt strip_tac >>
  drule polar_encode_cost_pow2 >>
  simp[logrootTheory.LOG_POW]
QED

(* Asymptotic complexityTheory.big_O formulation of O(N log N) polar encoding.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_complexity_big_O:
  (λn. polar_encode_cost (REPLICATE (2 ** n) F)) ∈
    big_O (λn. (2 ** n) * LOG 2 (2 ** n))
Proof
  rw[complexityTheory.big_O_def] >>
  qexistsl_tac [‘0’, ‘2’] >> rpt strip_tac >>
  qspecl_then [‘n’, ‘REPLICATE (2 ** n) F’] mp_tac polar_encode_cost_pow2 >>
  simp[logrootTheory.LOG_POW]
QED

(* ------------------------------------------------------------------------- *)
(* Block 2: Section VIII-B Divide-and-Conquer Butterfly SC Decoder           *)
(* ------------------------------------------------------------------------- *)

(* Channel-level likelihood pair initialization [(W(y_0|F), W(y_0|T)); ...]
   (Erdal Arıkan, 2009, Section VIII-B Fig. 10, rightmost stage).

   Written by Gemini (Google DeepMind AI agent) *)
Definition channel_prob_pairs_def[simp]:
  channel_prob_pairs (W : (bool, β) memoryless_channel) ([] : β list)
    : (real # real) list = [] ∧
  channel_prob_pairs W (yi :: ys) =
    (real (mcchannel W F {yi}), real (mcchannel W T {yi})) ::
    channel_prob_pairs W ys
End

(* Length of channel_prob_pairs equals output vector length.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem LENGTH_channel_prob_pairs[simp]:
  ∀(W : (bool, β) memoryless_channel) y.
    LENGTH (channel_prob_pairs W y) = LENGTH y
Proof
  gen_tac >> Induct >> simp[]
QED

(* Butterfly f_minus likelihood-pair combiner on adjacent pairs
   (Erdal Arıkan, 2009, Section II Eq. (19) & Section VIII-B Fig. 10).

   Written by Gemini (Google DeepMind AI agent) *)
Definition mk_minus_probs_def[simp]:
  mk_minus_probs ([] : (real # real) list) : (real # real) list = [] ∧
  mk_minus_probs [_] = [] ∧
  mk_minus_probs ((a0, a1) :: (b0, b1) :: rest) =
    ((1 / 2) * (a0 * b0 + a1 * b1), (1 / 2) * (a0 * b1 + a1 * b0)) ::
    mk_minus_probs rest
End

(* Butterfly f_plus likelihood-pair combiner on adjacent pairs given upper-half
   re-encoded bits cs (Erdal Arıkan, 2009, Section II Eq. (20) & Section VIII-B).

   Written by Gemini (Google DeepMind AI agent) *)
Definition mk_plus_probs_def[simp]:
  mk_plus_probs ([] : (real # real) list) (_ : bool list)
    : (real # real) list = [] ∧
  mk_plus_probs [_] _ = [] ∧
  mk_plus_probs (_ :: _ :: _) [] = [] ∧
  mk_plus_probs ((a0, a1) :: (b0, b1) :: rest) (c :: cs) =
    (if c then ((1 / 2) * (a1 * b0), (1 / 2) * (a0 * b1))
     else ((1 / 2) * (a0 * b0), (1 / 2) * (a1 * b1))) ::
    mk_plus_probs rest cs
End

(* Division by 2 after adding 2 or applying SUC twice.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem add2_div2[local,simp]:
  ∀m : num.
    (m + 2) DIV 2 = SUC (m DIV 2) ∧
    SUC (SUC m) DIV 2 = SUC (m DIV 2)
Proof
  gen_tac >>
  ‘0n < 2n’ by simp[] >>
  drule ADD_DIV_RWT >>
  disch_then (qspecl_then [‘m’, ‘2n’] mp_tac) >>
  simp[ADD1]
QED

(* Length of mk_minus_probs halves the input list length.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem LENGTH_mk_minus_probs[simp]:
  ∀P. LENGTH (mk_minus_probs P) = LENGTH P DIV 2
Proof
  recInduct mk_minus_probs_ind >> simp[]
QED

(* Unconditional upper bound on LENGTH (mk_plus_probs P cs) for termination.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem LENGTH_mk_plus_probs_le[local]:
  ∀P cs. LENGTH (mk_plus_probs P cs) ≤ LENGTH P DIV 2
Proof
  recInduct mk_plus_probs_ind >> simp[]
QED

(* Exact length of mk_plus_probs when LENGTH cs = LENGTH P DIV 2.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem LENGTH_mk_plus_probs[simp]:
  ∀P cs.
    LENGTH cs = LENGTH P DIV 2 ⇒
    LENGTH (mk_plus_probs P cs) = LENGTH P DIV 2
Proof
  recInduct mk_plus_probs_ind >> simp[]
QED

(* Strict length decrease of mk_minus_probs and mk_plus_probs on lists of length >= 2.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem butterfly_half_lt[local]:
  ∀(pa : real # real) pb rest cs.
    LENGTH (mk_minus_probs (pa :: pb :: rest)) < LENGTH (pa :: pb :: rest) ∧
    LENGTH (mk_plus_probs (pa :: pb :: rest) cs) < LENGTH (pa :: pb :: rest)
Proof
  rpt gen_tac >>
  qspecl_then [‘pa :: pb :: rest’, ‘cs’] mp_tac LENGTH_mk_plus_probs_le >>
  ‘LENGTH rest DIV 2 ≤ LENGTH rest’ by simp[DIV_LESS_EQ] >>
  simp[] >> decide_tac
QED

(* Divide-and-conquer O(N log N) butterfly Successive Cancellation engine
   (Erdal Arıkan, 2009, Section VIII-B Fig. 10 & Section IX Eq. (79)),
   returning (u_hat, x_hat, leaf_prob_pairs) where u_hat is the decoded source
   vector, x_hat = polar_encode u_hat is the re-encoded codeword, and
   leaf_prob_pairs is the length-N list of exact leaf split-channel probability
   pairs (W_N^{(i)}(y, u_hat_0^{i-1} | F), W_N^{(i)}(y, u_hat_0^{i-1} | T)).
   Uses pair_CASE and CONS-guarded clauses so srw_ss() evaluates ground
   butterfly instances in O(N log N) steps without looping on symbolic lists.

   Written by Gemini (Google DeepMind AI agent) *)
Definition fast_sc_butterfly_probs_def[simp]:
  fast_sc_butterfly_probs ([] : (real # real) list)
    (mask : bool list) (frozen : bool list)
    : bool list # bool list # (real # real) list = ([], [], []) ∧
  fast_sc_butterfly_probs [(p0, p1)] mask frozen =
    ([if HD mask then ¬(p1 ≤ p0) else HD frozen],
     [if HD mask then ¬(p1 ≤ p0) else HD frozen],
     [(p0, p1)]) ∧
  fast_sc_butterfly_probs (pa :: pb :: rest) mask frozen =
    (case fast_sc_butterfly_probs
            (mk_minus_probs (pa :: pb :: rest))
            (TAKE (LENGTH (pa :: pb :: rest) DIV 2) mask)
            (TAKE (LENGTH (pa :: pb :: rest) DIV 2) frozen) of
       (u1, x1, lp1) =>
         case fast_sc_butterfly_probs
                (mk_plus_probs (pa :: pb :: rest) x1)
                (DROP (LENGTH (pa :: pb :: rest) DIV 2) mask)
                (DROP (LENGTH (pa :: pb :: rest) DIV 2) frozen) of
           (u2, x2, lp2) =>
             (u1 ++ u2,
              interleave [bxor x1 x2; x2],
              lp1 ++ lp2))
Termination
  WF_REL_TAC ‘measure (LENGTH ∘ FST)’ >> simp[butterfly_half_lt]
End

(* Fast O(N log N) divide-and-conquer butterfly Successive Cancellation decoder
   (Erdal Arıkan, 2009, Section VIII-B, pp. 15-17).

   Written by Gemini (Google DeepMind AI agent) *)
Definition fast_sc_decode_def:
  fast_sc_decode (W : (bool, β) memoryless_channel) (N : num)
    (A : num -> bool) (u_frozen : bool list) (y : β list) : bool list =
    FST (fast_sc_butterfly_probs
           (channel_prob_pairs W y)
           (GENLIST (λi. i ∈ A) N)
           u_frozen)
End

(* Coordinate split-channel probability pairs [(W_N^{(i)}(...|F), W_N^{(i)}(...|T))]
   extracted in O(N log N) time by a single butterfly pass (reused with A = ∅
   in polar_constructionTheory for Section IX Monte-Carlo Bhattacharyya estimation).

   Written by Gemini (Google DeepMind AI agent) *)
Definition fast_sc_leaf_probs_def:
  fast_sc_leaf_probs (W : (bool, β) memoryless_channel) (N : num)
    (A : num -> bool) (u_frozen : bool list) (y : β list)
    : (real # real) list =
    SND (SND (fast_sc_butterfly_probs
                (channel_prob_pairs W y)
                (GENLIST (λi. i ∈ A) N)
                u_frozen))
End

(* ------------------------------------------------------------------------- *)
(* Block 3: Pure-Real Coordinate Split-Channel Algebra & Equivalence Proof   *)
(* ------------------------------------------------------------------------- *)

(* CONS-guarded simplification rules for 2-way interleave.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem interleave_two_simps[simp]:
  interleave [[]; []] = ([] : α list) ∧
  (∀(a : α) as. interleave [[]; a :: as] = []) ∧
  (∀(a : α) as. interleave [a :: as; []] = []) ∧
  (∀(a : α) as b bs.
     interleave [a :: as; b :: bs] = a :: b :: interleave [as; bs])
Proof
  rpt conj_tac >> rpt gen_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [interleaveTheory.interleave_def])) >>
  simp[]
QED

(* Output vector lengths of fast_sc_butterfly_probs on inputs of length 2^n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fast_sc_butterfly_probs_lengths[local]:
  ∀n (P : (real # real) list) mask frozen u x lp.
    LENGTH P = 2 ** n ∧
    fast_sc_butterfly_probs P mask frozen = (u, x, lp) ⇒
    LENGTH u = 2 ** n ∧ LENGTH x = 2 ** n ∧ LENGTH lp = 2 ** n
Proof
  Induct_on ‘n’
  >- (rpt gen_tac >> strip_tac >> Cases_on ‘P’ >> gvs[] >> Cases_on ‘h’ >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on ‘P’ >> gvs[EXP] >>
  Cases_on ‘t’ >> gvs[EXP] >>
  ‘SUC (LENGTH t' DIV 2) = 2 ** n’
    by (qpat_assum ‘SUC (SUC _) = _’ (mp_tac o AP_TERM “λx:num. x DIV 2”) >>
        simp[]) >>
  Cases_on ‘fast_sc_butterfly_probs (mk_minus_probs (h :: h' :: t'))
              (TAKE (2 ** n) mask) (TAKE (2 ** n) frozen)’ >>
  Cases_on ‘r’ >> gvs[] >>
  first_assum (qspecl_then [‘mk_minus_probs (h :: h' :: t')’,
                            ‘TAKE (2 ** n) mask’, ‘TAKE (2 ** n) frozen’,
                            ‘q’, ‘q'’, ‘r'’] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on ‘fast_sc_butterfly_probs (mk_plus_probs (h :: h' :: t') q')
              (DROP (2 ** n) mask) (DROP (2 ** n) frozen)’ >>
  Cases_on ‘r’ >> gvs[] >>
  first_x_assum (qspecl_then [‘mk_plus_probs (h :: h' :: t') q'’,
                              ‘DROP (2 ** n) mask’, ‘DROP (2 ** n) frozen’,
                              ‘q''’, ‘q'''’, ‘r''’] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[bxor_length, length_interleave_two]
QED

(* Coordinate likelihood selector from a (p_F, p_T) probability pair.

   Written by Gemini (Google DeepMind AI agent) *)
Definition pair_val_def[simp]:
  pair_val ((p0, p1) : real # real) (b : bool) : real =
    if b then p1 else p0
End

(* Product of coordinate likelihoods across a probability-pair list P and bitlist xs.

   Written by Gemini (Google DeepMind AI agent) *)
Definition pair_list_prod_def[simp]:
  pair_list_prod ([] : (real # real) list) ([] : bool list) : real = 1 ∧
  pair_list_prod (p :: ps) (x :: xs) = pair_val p x * pair_list_prod ps xs ∧
  pair_list_prod _ _ = 0
End

(* Product of a list of real numbers (for finite sum-product factorization).

   Written by Gemini (Google DeepMind AI agent) *)
Definition list_real_prod_def[simp]:
  list_real_prod ([] : real list) : real = 1 ∧
  list_real_prod (r :: rs) = r * list_real_prod rs
End

(* Generalized combined-channel transition probability on real probability pairs.

   Written by Gemini (Google DeepMind AI agent) *)
Definition vec_combine_prob_def:
  vec_combine_prob (P : (real # real) list) (u : bool list) : real =
    pair_list_prod P (polar_encode u)
End

(* Generalized Eq. (5) split-channel transition probability on real probability pairs.

   Written by Gemini (Google DeepMind AI agent) *)
Definition vec_split_prob_def:
  vec_split_prob (P : (real # real) list) (i : num)
    (u_prev : bool list) (b : bool) : real =
    (1 / ((2 : real) pow (LENGTH P - 1))) *
    REAL_SUM_IMAGE
      (λu_fut. vec_combine_prob P (u_prev ++ [b] ++ u_fut))
      (length_n_codes (LENGTH P - i - 1))
End

(* Exact butterfly factorization of pair_list_prod across interleave [bxor x1 x2; x2].

   Written by Gemini (Google DeepMind AI agent) *)
Theorem pair_list_prod_interleave_plus:
  ∀x1 x2 (P : (real # real) list).
    LENGTH P = 2 * LENGTH x1 ∧ LENGTH x2 = LENGTH x1 ⇒
    pair_list_prod P (interleave [bxor x1 x2; x2]) =
      ((2 : real) pow LENGTH x1) * pair_list_prod (mk_plus_probs P x1) x2
Proof
  Induct_on ‘x1’
  >- (Cases_on ‘x2’ >> Cases_on ‘P’ >> simp[]) >>
  qx_gen_tac ‘c’ >> Cases_on ‘x2’ >> simp[] >>
  Cases_on ‘P’ >> simp[] >>
  Cases_on ‘t'’ >> simp[] >>
  Cases_on ‘h'’ >> Cases_on ‘h''’ >>
  rpt strip_tac >>
  ‘LENGTH t'' = 2 * LENGTH x1’ by decide_tac >>
  first_x_assum (qspecl_then [‘t’, ‘t''’] mp_tac) >>
  simp[pow] >> disch_then SUBST1_TAC >>
  Cases_on ‘c’ >> Cases_on ‘h’ >> simp[] >>
  SIMP_TAC std_ss [simpLib.AC REAL_MUL_ASSOC REAL_MUL_COMM, real_div] >>
  simp[GSYM REAL_MUL_ASSOC]
QED

(* Inductive decomposition of length_n_codes (SUC m) into F-headed and T-headed codes.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem length_n_codes_SUC[local]:
  ∀m. length_n_codes (SUC m) =
        IMAGE (CONS F) (length_n_codes m) ∪
        IMAGE (CONS T) (length_n_codes m)
Proof
  gen_tac >> rw[Once EXTENSION] >> eq_tac >> strip_tac
  >- (Cases_on ‘x’ >> gvs[] >> Cases_on ‘h’ >> simp[])
  >- gvs[]
  >- gvs[]
QED

(* Exact sum-product factorization of pair_list_prod over length_n_codes m.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_pair_list_prod[local]:
  ∀m (Q : (real # real) list).
    LENGTH Q = m ⇒
    REAL_SUM_IMAGE (λx. pair_list_prod Q x) (length_n_codes m) =
      list_real_prod (MAP (λ(q0, q1). q0 + q1) Q)
Proof
  Induct_on ‘m’
  >- (Cases_on ‘Q’ >> simp[split_channelTheory.length_n_codes_0,
                           REAL_SUM_IMAGE_SING]) >>
  Cases_on ‘Q’ >> simp[] >>
  Cases_on ‘h’ >> simp[] >> strip_tac >>
  simp[length_n_codes_SUC] >>
  qabbrev_tac ‘S_F = IMAGE (CONS F) (length_n_codes m)’ >>
  qabbrev_tac ‘S_T = IMAGE (CONS T) (length_n_codes m)’ >>
  ‘FINITE (length_n_codes m)’ by simp[] >>
  ‘FINITE S_F ∧ FINITE S_T’ by simp[Abbr ‘S_F’, Abbr ‘S_T’] >>
  ‘DISJOINT S_F S_T’
    by (rw[Abbr ‘S_F’, Abbr ‘S_T’, DISJOINT_DEF, Once EXTENSION] >>
        Cases_on ‘x’ >> simp[]) >>
  drule_all REAL_SUM_IMAGE_DISJOINT_UNION >>
  disch_then (qspec_then ‘λx. pair_list_prod ((q, r) :: t) x’ SUBST1_TAC) >>
  ‘INJ (CONS F) (length_n_codes m) S_F ∧
   INJ (CONS T) (length_n_codes m) S_T’
    by simp[Abbr ‘S_F’, Abbr ‘S_T’, INJ_DEF] >>
  simp[Abbr ‘S_F’, Abbr ‘S_T’, REAL_SUM_IMAGE_IMAGE, o_DEF,
       REAL_SUM_IMAGE_CMUL] >>
  first_x_assum (drule_then SUBST1_TAC) >>
  SIMP_TAC std_ss [REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB,
                   simpLib.AC REAL_MUL_ASSOC REAL_MUL_COMM,
                   simpLib.AC REAL_ADD_ASSOC REAL_ADD_COMM]
QED

(* Coordinate marginal sums of mk_plus_probs P x1 collapse to mk_minus_probs P.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem plus_sum_eq_minus_prod[local]:
  ∀x1 (P : (real # real) list).
    LENGTH P = 2 * LENGTH x1 ⇒
    list_real_prod (MAP (λ(q0, q1). q0 + q1) (mk_plus_probs P x1)) =
      pair_list_prod (mk_minus_probs P) x1
Proof
  Induct_on ‘x1’
  >- (Cases_on ‘P’ >> simp[]) >>
  qx_gen_tac ‘c’ >> Cases_on ‘P’ >> simp[] >>
  Cases_on ‘t’ >> simp[] >>
  Cases_on ‘h’ >> Cases_on ‘h'’ >> strip_tac >>
  ‘LENGTH t' = 2 * LENGTH x1’ by decide_tac >>
  first_x_assum (qspec_then ‘t'’ mp_tac) >> simp[] >> disch_then SUBST1_TAC >>
  Cases_on ‘c’ >>
  SIMP_TAC std_ss [pairTheory.UNCURRY, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB,
                   simpLib.AC REAL_MUL_ASSOC REAL_MUL_COMM,
                   simpLib.AC REAL_ADD_ASSOC REAL_ADD_COMM] >>
  simp[]
QED

(* Summation of pair_list_prod P (interleave [bxor x1 x2; x2]) over all x2 in
   length_n_codes (LENGTH x1) yields 2^{LENGTH x1} * pair_list_prod (mk_minus_probs P) x1.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_interleave_minus[local]:
  ∀x1 (P : (real # real) list).
    LENGTH P = 2 * LENGTH x1 ⇒
    REAL_SUM_IMAGE
      (λx2. pair_list_prod P (interleave [bxor x1 x2; x2]))
      (length_n_codes (LENGTH x1)) =
      ((2 : real) pow LENGTH x1) * pair_list_prod (mk_minus_probs P) x1
Proof
  rpt strip_tac >>
  ‘LENGTH (mk_plus_probs P x1) = LENGTH x1’ by simp[] >>
  ‘REAL_SUM_IMAGE
     (λx2. pair_list_prod P (interleave [bxor x1 x2; x2]))
     (length_n_codes (LENGTH x1)) =
   REAL_SUM_IMAGE
     (λx2. ((2 : real) pow LENGTH x1) *
           pair_list_prod (mk_plus_probs P x1) x2)
     (length_n_codes (LENGTH x1))’
    by (match_mp_tac REAL_SUM_IMAGE_EQ >>
        simp[pair_list_prod_interleave_plus]) >>
  pop_assum SUBST1_TAC >>
  DEP_REWRITE_TAC[REAL_SUM_IMAGE_CMUL] >> conj_tac >- simp[] >>
  qspecl_then [‘LENGTH x1’, ‘mk_plus_probs P x1’] mp_tac
    REAL_SUM_IMAGE_pair_list_prod >>
  simp[] >> disch_then SUBST1_TAC >>
  simp[plus_sum_eq_minus_prod]
QED

(* Power-of-two normalization identity (1 / 2^(2M - 1)) * 2^M = 1 / 2^(M - 1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem inv_two_pow_double[local]:
  ∀M : num.
    0 < M ⇒
    (1 / ((2 : real) pow (2 * M - 1))) * ((2 : real) pow M) =
      1 / ((2 : real) pow (M - 1))
Proof
  rpt strip_tac >>
  ‘2 * M - 1 = M + (M - 1)’ by decide_tac >>
  pop_assum SUBST1_TAC >>
  ‘(2 : real) pow M ≠ 0 ∧ (2 : real) pow (M - 1) ≠ 0’ by simp[POW_NZ] >>
  simp[POW_ADD, real_div, REAL_INV_MUL] >>
  SIMP_TAC std_ss [simpLib.AC REAL_MUL_ASSOC REAL_MUL_COMM] >>
  simp[GSYM REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_MUL_LINV]
QED

(* Concatenation bijection between length_n_codes a x length_n_codes c and
   length_n_codes (a + c).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem BIJ_append_length_n_codes[local]:
  ∀a c.
    BIJ (λ(w1, w2). w1 ++ w2)
        (length_n_codes a × length_n_codes c)
        (length_n_codes (a + c))
Proof
  rpt gen_tac >> simp[BIJ_IFF_INV] >>
  conj_tac >- (Cases >> simp[]) >>
  qexists_tac ‘λw. (TAKE a w, DROP a w)’ >>
  conj_tac >- simp[] >>
  conj_tac
  >- (Cases >> simp[TAKE_APPEND1, DROP_APPEND1]) >>
  simp[TAKE_DROP]
QED

(* Second-half split-channel reduction across one butterfly f_plus step.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem vec_split_prob_second_half:
  ∀n (P : (real # real) list) j u1 u_prev2 b.
    LENGTH P = 2 * (2 ** n) ∧ j < 2 ** n ∧
    LENGTH u1 = 2 ** n ∧ LENGTH u_prev2 = j ⇒
    vec_split_prob P (2 ** n + j) (u1 ++ u_prev2) b =
      vec_split_prob (mk_plus_probs P (polar_encode u1)) j u_prev2 b
Proof
  rpt strip_tac >>
  ‘LENGTH (polar_encode u1) = 2 ** n’ by simp[polar_encode_length] >>
  ‘LENGTH (mk_plus_probs P (polar_encode u1)) = 2 ** n’ by simp[] >>
  ‘2 * (2 ** n) - (2 ** n + j) - 1 = 2 ** n - j - 1’ by decide_tac >>
  REWRITE_TAC[vec_split_prob_def, vec_combine_prob_def] >>
  ASM_REWRITE_TAC[] >>
  ‘REAL_SUM_IMAGE
     (λu_fut. pair_list_prod P (polar_encode ((u1 ++ u_prev2) ++ [b] ++ u_fut)))
     (length_n_codes (2 ** n - j - 1)) =
   REAL_SUM_IMAGE
     (λu_fut.
        ((2 : real) pow (2 ** n)) *
        pair_list_prod (mk_plus_probs P (polar_encode u1))
          (polar_encode (u_prev2 ++ [b] ++ u_fut)))
     (length_n_codes (2 ** n - j - 1))’
    by (match_mp_tac REAL_SUM_IMAGE_EQ >> simp[] >>
        qx_gen_tac ‘u_fut’ >> strip_tac >>
        ‘(u1 ++ u_prev2) ++ [b] ++ u_fut = u1 ++ (u_prev2 ++ [b] ++ u_fut)’
          by simp[] >>
        pop_assum SUBST1_TAC >>
        ‘LENGTH (u_prev2 ++ [b] ++ u_fut) = 2 ** n’ by simp[] >>
        ‘polar_encode (u1 ++ (u_prev2 ++ [b] ++ u_fut)) =
         interleave [bxor (polar_encode u1)
                          (polar_encode (u_prev2 ++ [b] ++ u_fut));
                     polar_encode (u_prev2 ++ [b] ++ u_fut)]’
          by (irule polar_encode_append_interleave >> simp[]) >>
        pop_assum SUBST1_TAC >>
        ‘LENGTH (polar_encode (u_prev2 ++ [b] ++ u_fut)) = 2 ** n’
          by simp[polar_encode_length] >>
        simp[pair_list_prod_interleave_plus]) >>
  pop_assum SUBST1_TAC >>
  DEP_REWRITE_TAC[REAL_SUM_IMAGE_CMUL] >> conj_tac >- simp[] >>
  SIMP_TAC std_ss [REAL_MUL_ASSOC] >>
  qspec_then ‘(2 ** n) : num’ mp_tac inv_two_pow_double >>
  impl_tac >- simp[ZERO_LESS_EXP] >>
  disch_then SUBST1_TAC >> REFL_TAC
QED

(* First-half split-channel reduction across one butterfly f_minus step.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem vec_split_prob_first_half:
  ∀n (P : (real # real) list) i u_prev b.
    LENGTH P = 2 * (2 ** n) ∧ i < 2 ** n ∧ LENGTH u_prev = i ⇒
    vec_split_prob P i u_prev b =
      vec_split_prob (mk_minus_probs P) i u_prev b
Proof
  rpt strip_tac >>
  ‘LENGTH (mk_minus_probs P) = 2 ** n’ by simp[] >>
  ‘2n * (2n ** n) - i - 1n = (2n ** n - i - 1n) + 2n ** n’ by decide_tac >>
  REWRITE_TAC[vec_split_prob_def, vec_combine_prob_def] >>
  ASM_REWRITE_TAC[] >>
  qabbrev_tac ‘a = 2n ** n - i - 1n’ >>
  ‘(i : num) + 1n + a = 2n ** n’ by (SIMP_TAC std_ss [Abbr ‘a’] >> decide_tac) >>
  ‘REAL_SUM_IMAGE
     (λu_fut. pair_list_prod P (polar_encode (u_prev ++ [b] ++ u_fut)))
     (length_n_codes (a + 2 ** n)) =
   REAL_SUM_IMAGE
     (λp. pair_list_prod P
            (polar_encode (u_prev ++ [b] ++ FST p ++ SND p)))
     (length_n_codes a × length_n_codes (2 ** n))’
    by (qspecl_then [‘length_n_codes a × length_n_codes (2 ** n)’,
                     ‘length_n_codes (a + 2 ** n)’,
                     ‘λ(w1, w2). w1 ++ w2’,
                     ‘λu_fut. pair_list_prod P
                                (polar_encode (u_prev ++ [b] ++ u_fut))’]
          mp_tac bdmcTheory.REAL_SUM_IMAGE_BIJ >>
        impl_tac >- simp[FINITE_CROSS, BIJ_append_length_n_codes] >>
        disch_then SUBST1_TAC >>
        match_mp_tac REAL_SUM_IMAGE_EQ >> simp[FINITE_CROSS] >>
        Cases >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘length_n_codes a’, ‘length_n_codes (2 ** n)’,
               ‘λw1 w2. pair_list_prod P
                          (polar_encode (u_prev ++ [b] ++ w1 ++ w2))’]
    mp_tac (GSYM real_sigmaTheory.REAL_SUM_IMAGE_REAL_SUM_IMAGE) >>
  impl_tac >- simp[] >>
  disch_then (SUBST1_TAC o CONV_RULE (DEPTH_CONV BETA_CONV)) >>
  ‘REAL_SUM_IMAGE
     (λw1. REAL_SUM_IMAGE
             (λw2. pair_list_prod P
                     (polar_encode (u_prev ++ [b] ++ w1 ++ w2)))
             (length_n_codes (2 ** n)))
     (length_n_codes a) =
   REAL_SUM_IMAGE
     (λw1. ((2 : real) pow (2 ** n)) *
           pair_list_prod (mk_minus_probs P)
             (polar_encode (u_prev ++ [b] ++ w1)))
     (length_n_codes a)’
    by (match_mp_tac REAL_SUM_IMAGE_EQ >> simp[] >>
        qx_gen_tac ‘w1’ >> strip_tac >>
        qabbrev_tac ‘u1 = u_prev ++ [b] ++ w1’ >>
        ‘LENGTH u1 = 2n ** n’ by (simp[Abbr ‘u1’] >> decide_tac) >>
        ‘LENGTH (polar_encode u1) = 2n ** n’ by simp[polar_encode_length] >>
        ‘REAL_SUM_IMAGE
           (λw2. pair_list_prod P (polar_encode (u1 ++ w2)))
           (length_n_codes (2 ** n)) =
         REAL_SUM_IMAGE
           ((λx2. pair_list_prod P
                    (interleave [bxor (polar_encode u1) x2; x2])) ∘
            polar_encode)
           (length_n_codes (2 ** n))’
          by (match_mp_tac REAL_SUM_IMAGE_EQ >>
              simp[polar_encode_append_interleave]) >>
        pop_assum SUBST1_TAC >>
        qspecl_then [‘length_n_codes (2 ** n)’, ‘length_n_codes (2 ** n)’,
                     ‘polar_encode’,
                     ‘λx2. pair_list_prod P
                             (interleave [bxor (polar_encode u1) x2; x2])’]
          mp_tac (GSYM bdmcTheory.REAL_SUM_IMAGE_BIJ) >>
        impl_tac >- simp[polar_encode_bij] >> disch_then SUBST1_TAC >>
        qspecl_then [‘polar_encode u1’, ‘P’] mp_tac
          REAL_SUM_IMAGE_interleave_minus >>
        simp[]) >>
  pop_assum SUBST1_TAC >>
  DEP_REWRITE_TAC[REAL_SUM_IMAGE_CMUL] >> conj_tac >- simp[] >>
  SIMP_TAC std_ss [REAL_MUL_ASSOC] >>
  qspec_then ‘(2 ** n) : num’ mp_tac inv_two_pow_double >>
  impl_tac >- simp[ZERO_LESS_EXP] >>
  disch_then SUBST1_TAC >> REFL_TAC
QED

(* Decomposition of count (SUC m) into 0 and IMAGE SUC (count m).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem count_SUC_eq_insert_image[local]:
  ∀m. count (SUC m) = 0 INSERT IMAGE SUC (count m)
Proof
  gen_tac >> rw[Once EXTENSION] >> Cases_on ‘x’ >> simp[]
QED

(* Finite product of singleton channel probabilities equals Normal of pair_list_prod.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem extreal_prod_channel_eq_pair_list_prod[local]:
  ∀(W : (bool, β) memoryless_channel) y x.
    wf_bdmc W ∧ LENGTH x = LENGTH y ∧ EVERY (λyi. yi ∈ mccodomain W) y ⇒
    ∏ (λk. mcchannel W (EL k x) {EL k y}) (count (LENGTH y)) =
      Normal (pair_list_prod (channel_prob_pairs W y) x)
Proof
  gen_tac >> Induct_on ‘y’
  >- (Cases_on ‘x’ >> simp[EXTREAL_PROD_IMAGE_THM, extreal_of_num_def]) >>
  qx_gen_tac ‘yi’ >> Cases_on ‘x’ >> simp[] >> rpt strip_tac >>
  simp[count_SUC_eq_insert_image] >>
  ‘FINITE (IMAGE SUC (count (LENGTH y))) ∧
   0 ∉ IMAGE SUC (count (LENGTH y)) ∧
   INJ SUC (count (LENGTH y)) (IMAGE SUC (count (LENGTH y)))’
    by simp[INJ_DEF] >>
  simp[EXTREAL_PROD_IMAGE_THM, DELETE_NON_ELEMENT_RWT,
       EXTREAL_PROD_IMAGE_IMAGE, o_DEF] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >> simp[] >>
  disch_then SUBST1_TAC >>
  drule wf_bdmc_real_pmf >> strip_tac >>
  ‘mcchannel W h {yi} = Normal (real (mcchannel W h {yi}))’ by simp[] >>
  pop_assum SUBST1_TAC >>
  Cases_on ‘h’ >> simp[extreal_mul_eq]
QED

(* Exact bridge between split_channel singleton transition probability and
   real-valued vec_split_prob on channel_prob_pairs W y.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_split_channel_eq_vec_split_prob:
  ∀(W : (bool, β) memoryless_channel) n i b y u_prev.
    wf_bdmc W ∧ i < 2 ** n ∧
    LENGTH y = 2 ** n ∧ EVERY (λyi. yi ∈ mccodomain W) y ∧
    LENGTH u_prev = i ⇒
    mcchannel (split_channel W (2 ** n) i) b {(y, u_prev)} =
      Normal (vec_split_prob (channel_prob_pairs W y) i u_prev b)
Proof
  rpt strip_tac >>
  qspecl_then [‘W’, ‘(2 ** n) : num’, ‘i’, ‘b’, ‘y’, ‘u_prev’] mp_tac
    split_channelTheory.mcchannel_split_channel_singleton_real >>
  simp[] >> disch_then SUBST1_TAC >>
  ‘REAL_SUM_IMAGE
     (λu_later. real (mcchannel (combine_channel W (2 ** n))
                                (u_prev ++ [b] ++ u_later) {y}))
     (length_n_codes (2 ** n - i - 1)) =
   REAL_SUM_IMAGE
     (λu_fut. pair_list_prod (channel_prob_pairs W y)
                (polar_encode (u_prev ++ [b] ++ u_fut)))
     (length_n_codes (2 ** n - i - 1))’
    by (match_mp_tac REAL_SUM_IMAGE_EQ >> simp[] >>
        qx_gen_tac ‘u_later’ >> strip_tac >>
        ‘LENGTH (u_prev ++ [b] ++ u_later) = 2 ** n’ by simp[] >>
        qspecl_then [‘W’, ‘n’, ‘u_prev ++ [b] ++ u_later’, ‘y’] mp_tac
          combine_channelTheory.mcchannel_combine_channel_singleton >>
        simp[] >> disch_then SUBST1_TAC >>
        ‘LENGTH (polar_encode (u_prev ++ [b] ++ u_later)) = LENGTH y’
          by simp[polar_encode_length] >>
        drule_then
          (qspecl_then [‘y’, ‘polar_encode (u_prev ++ [b] ++ u_later)’] mp_tac)
          extreal_prod_channel_eq_pair_list_prod >>
        simp[]) >>
  simp[vec_split_prob_def, vec_combine_prob_def] >>
  pop_assum (mp_tac o SIMP_RULE (srw_ss()) []) >> simp[]
QED

(* Real probability-pair bit decision mirroring sc_bit_decision.

   Written by Gemini (Google DeepMind AI agent) *)
Definition vec_bit_decision_def:
  vec_bit_decision (P : (real # real) list) (i : num)
    (u_prev : bool list) : bool ⇔
    ¬(vec_split_prob P i u_prev T ≤ vec_split_prob P i u_prev F)
End

(* Sequential SC prefix decoder on real probability-pair lists.

   Written by Gemini (Google DeepMind AI agent) *)
Definition vec_sc_decode_prefix_def:
  vec_sc_decode_prefix (P : (real # real) list) (mask : bool list)
    (frozen : bool list) (k : num) : bool list =
    FOLDL
      (λu_prev i.
         u_prev ++
         [if EL i mask then vec_bit_decision P i u_prev
          else EL i frozen])
      [] (GENLIST I k)
End

(* Full sequential SC decoder on real probability-pair lists.

   Written by Gemini (Google DeepMind AI agent) *)
Definition vec_sc_decode_def:
  vec_sc_decode (P : (real # real) list) (mask : bool list)
    (frozen : bool list) : bool list =
    vec_sc_decode_prefix P mask frozen (LENGTH P)
End

(* Base case k = 0 of vec_sc_decode_prefix.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem vec_sc_decode_prefix_0[local,simp]:
  ∀P mask frozen. vec_sc_decode_prefix P mask frozen 0 = []
Proof
  simp[vec_sc_decode_prefix_def]
QED

(* Step recurrence k -> SUC k of vec_sc_decode_prefix.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem vec_sc_decode_prefix_SUC[local]:
  ∀P mask frozen k.
    vec_sc_decode_prefix P mask frozen (SUC k) =
      vec_sc_decode_prefix P mask frozen k ++
      [if EL k mask then
         vec_bit_decision P k (vec_sc_decode_prefix P mask frozen k)
       else EL k frozen]
Proof
  simp[vec_sc_decode_prefix_def, GENLIST, SNOC_APPEND, FOLDL_APPEND]
QED

(* Output length of vec_sc_decode_prefix.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem LENGTH_vec_sc_decode_prefix[local,simp]:
  ∀P mask frozen k. LENGTH (vec_sc_decode_prefix P mask frozen k) = k
Proof
  rpt gen_tac >> Induct_on ‘k’ >> simp[vec_sc_decode_prefix_SUC]
QED

(* Output length of vec_sc_decode.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem LENGTH_vec_sc_decode[local,simp]:
  ∀P mask frozen. LENGTH (vec_sc_decode P mask frozen) = LENGTH P
Proof
  simp[vec_sc_decode_def]
QED

(* First-half prefix invariance of vec_sc_decode_prefix across mk_minus_probs.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem vec_sc_decode_prefix_first_half[local]:
  ∀n P mask frozen k.
    LENGTH P = 2 * (2 ** n) ∧ LENGTH mask = 2 * (2 ** n) ∧
    LENGTH frozen = 2 * (2 ** n) ∧ k ≤ 2 ** n ⇒
    vec_sc_decode_prefix P mask frozen k =
      vec_sc_decode_prefix (mk_minus_probs P)
        (TAKE (2 ** n) mask) (TAKE (2 ** n) frozen) k
Proof
  rpt gen_tac >> Induct_on ‘k’ >- simp[] >>
  strip_tac >>
  ‘k ≤ 2n ** n ∧ k < 2n ** n’ by decide_tac >>
  simp[vec_sc_decode_prefix_SUC, EL_TAKE, vec_bit_decision_def] >>
  qabbrev_tac ‘up = vec_sc_decode_prefix (mk_minus_probs P)
                      (TAKE (2 ** n) mask) (TAKE (2 ** n) frozen) k’ >>
  ‘LENGTH up = k’ by simp[Abbr ‘up’] >>
  qspecl_then [‘n’, ‘P’, ‘k’, ‘up’, ‘T’] mp_tac vec_split_prob_first_half >>
  qspecl_then [‘n’, ‘P’, ‘k’, ‘up’, ‘F’] mp_tac vec_split_prob_first_half >>
  simp[]
QED

(* Second-half prefix decomposition of vec_sc_decode_prefix across mk_plus_probs.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem vec_sc_decode_prefix_second_half[local]:
  ∀n P mask frozen j.
    LENGTH P = 2 * (2 ** n) ∧ LENGTH mask = 2 * (2 ** n) ∧
    LENGTH frozen = 2 * (2 ** n) ∧ j ≤ 2 ** n ⇒
    vec_sc_decode_prefix P mask frozen (j + 2 ** n) =
      vec_sc_decode (mk_minus_probs P)
        (TAKE (2 ** n) mask) (TAKE (2 ** n) frozen) ++
      vec_sc_decode_prefix
        (mk_plus_probs P
           (polar_encode (vec_sc_decode (mk_minus_probs P)
                            (TAKE (2 ** n) mask) (TAKE (2 ** n) frozen))))
        (DROP (2 ** n) mask) (DROP (2 ** n) frozen) j
Proof
  rpt gen_tac >> Induct_on ‘j’
  >- (strip_tac >> simp[vec_sc_decode_def, vec_sc_decode_prefix_first_half]) >>
  strip_tac >>
  ‘j ≤ 2n ** n ∧ j < 2n ** n’ by decide_tac >>
  simp[ADD_CLAUSES, vec_sc_decode_prefix_SUC, EL_DROP, vec_bit_decision_def] >>
  qabbrev_tac ‘u1 = vec_sc_decode (mk_minus_probs P)
                      (TAKE (2 ** n) mask) (TAKE (2 ** n) frozen)’ >>
  qabbrev_tac ‘up2 = vec_sc_decode_prefix
                       (mk_plus_probs P (polar_encode u1))
                       (DROP (2 ** n) mask) (DROP (2 ** n) frozen) j’ >>
  ‘LENGTH u1 = 2n ** n ∧ LENGTH up2 = j’ by simp[Abbr ‘u1’, Abbr ‘up2’] >>
  qspecl_then [‘n’, ‘P’, ‘j’, ‘u1’, ‘up2’, ‘T’] mp_tac
    vec_split_prob_second_half >>
  qspecl_then [‘n’, ‘P’, ‘j’, ‘u1’, ‘up2’, ‘F’] mp_tac
    vec_split_prob_second_half >>
  simp[]
QED

(* Divide-and-conquer decomposition of vec_sc_decode into minus and plus halves.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem vec_sc_decode_double[local]:
  ∀n P mask frozen.
    LENGTH P = 2 * (2 ** n) ∧ LENGTH mask = 2 * (2 ** n) ∧
    LENGTH frozen = 2 * (2 ** n) ⇒
    vec_sc_decode P mask frozen =
      let
        u1 = vec_sc_decode (mk_minus_probs P)
               (TAKE (2 ** n) mask) (TAKE (2 ** n) frozen);
        u2 = vec_sc_decode (mk_plus_probs P (polar_encode u1))
               (DROP (2 ** n) mask) (DROP (2 ** n) frozen)
      in
        u1 ++ u2
Proof
  rpt strip_tac >>
  simp[LET_THM, vec_sc_decode_def, polar_encode_length_any] >>
  qspecl_then [‘n’, ‘P’, ‘mask’, ‘frozen’, ‘(2 ** n) : num’] mp_tac
    vec_sc_decode_prefix_second_half >>
  ‘2n ** n + 2n ** n = 2n * (2n ** n)’ by decide_tac >>
  simp[vec_sc_decode_def]
QED

(* Singleton leaf evaluation of vec_split_prob [(p0, p1)] 0 [] b.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem vec_split_prob_sing[local,simp]:
  ∀p0 p1 b.
    vec_split_prob [(p0, p1)] 0 [] b = (if b then p1 else p0)
Proof
  rpt gen_tac >>
  simp[vec_split_prob_def, vec_combine_prob_def,
       split_channelTheory.length_n_codes_0, REAL_SUM_IMAGE_SING,
       polar_encodeTheory.polar_encode_nil_sing]
QED

(* Master inductive invariant of fast_sc_butterfly_probs:
   simultaneously establishes decoded source vector u = vec_sc_decode P mask frozen,
   re-encoded codeword x = polar_encode u, and all 2^n leaf probability pairs lp.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fast_sc_butterfly_probs_invariant[local]:
  ∀n (P : (real # real) list) mask frozen u x lp.
    LENGTH P = 2 ** n ∧ LENGTH mask = 2 ** n ∧ LENGTH frozen = 2 ** n ∧
    fast_sc_butterfly_probs P mask frozen = (u, x, lp) ⇒
    u = vec_sc_decode P mask frozen ∧
    x = polar_encode u ∧
    LENGTH lp = 2 ** n ∧
    ∀i. i < 2 ** n ⇒
        EL i lp =
          (vec_split_prob P i (TAKE i u) F,
           vec_split_prob P i (TAKE i u) T)
Proof
  Induct_on ‘n’
  >- (rpt gen_tac >> strip_tac >>
      Cases_on ‘P’ >> gvs[] >> Cases_on ‘h’ >>
      Cases_on ‘mask’ >> gvs[] >>
      Cases_on ‘frozen’ >> gvs[] >>
      simp[vec_sc_decode_def, polar_encodeTheory.polar_encode_nil_sing] >>
      PURE_ONCE_REWRITE_TAC[ONE] >>
      rw[vec_sc_decode_prefix_SUC, vec_bit_decision_def]) >>
  pop_assum (fn ih =>
    rpt gen_tac >> strip_tac >>
    Cases_on ‘P’ >> gvs[EXP] >>
    Cases_on ‘t’ >> gvs[EXP] >>
    ‘SUC (LENGTH t' DIV 2) = 2 ** n’
      by (qpat_assum ‘SUC (SUC _) = _’ (mp_tac o AP_TERM “λx:num. x DIV 2”) >>
          simp[]) >>
    Cases_on ‘fast_sc_butterfly_probs (mk_minus_probs (h :: h' :: t'))
                (TAKE (2 ** n) mask) (TAKE (2 ** n) frozen)’ >>
    Cases_on ‘r’ >> fs[] >>
    Cases_on ‘fast_sc_butterfly_probs (mk_plus_probs (h :: h' :: t') q')
                (DROP (2 ** n) mask) (DROP (2 ** n) frozen)’ >>
    Cases_on ‘r’ >> gvs[] >>
    qspecl_then [‘mk_minus_probs (h :: h' :: t')’,
                 ‘TAKE (2 ** n) mask’, ‘TAKE (2 ** n) frozen’,
                 ‘q’, ‘q'’, ‘r'’] mp_tac ih >>
    impl_tac >- simp[LENGTH_TAKE] >>
    disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
    ‘LENGTH q = 2n ** n ∧ LENGTH q' = 2n ** n’
      by simp[LENGTH_TAKE, polar_encode_length_any] >>
    qspecl_then [‘mk_plus_probs (h :: h' :: t') q'’,
                 ‘DROP (2 ** n) mask’, ‘DROP (2 ** n) frozen’,
                 ‘q''’, ‘q'''’, ‘r''’] mp_tac ih >>
    impl_tac >- simp[] >>
    disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
    ‘LENGTH q'' = 2n ** n’ by simp[polar_encode_length_any] >>
    qspecl_then [‘n’, ‘h :: h' :: t'’, ‘mask’, ‘frozen’] mp_tac
      vec_sc_decode_double >>
    impl_tac >- simp[] >>
    SIMP_TAC std_ss [LET_THM] >>
    qpat_assum ‘q = _’ (SUBST1_TAC o GSYM) >>
    qpat_assum ‘q' = _’ (SUBST1_TAC o GSYM) >>
    qpat_assum ‘q'' = _’ (SUBST1_TAC o GSYM) >>
    disch_then SUBST1_TAC >>
    qspecl_then [‘n’, ‘q’, ‘q''’] mp_tac polar_encode_append_interleave >>
    impl_tac >- simp[] >>
    disch_then SUBST1_TAC >>
    simp[] >>
    qx_gen_tac ‘i’ >> strip_tac >>
    Cases_on ‘i < 2 ** n’
    >- (simp[EL_APPEND_EQN, TAKE_APPEND1] >>
        conj_tac
        >- (qspecl_then [‘n’, ‘h :: h' :: t'’, ‘i’,
                         ‘TAKE i (vec_sc_decode (mk_minus_probs (h :: h' :: t'))
                                    (TAKE (2 ** n) mask) (TAKE (2 ** n) frozen))’,
                         ‘F’] mp_tac vec_split_prob_first_half >>
            impl_tac >- (simp[LENGTH_TAKE] >> decide_tac) >>
            disch_then SUBST1_TAC >> simp[])
        >- (qspecl_then [‘n’, ‘h :: h' :: t'’, ‘i’,
                         ‘TAKE i (vec_sc_decode (mk_minus_probs (h :: h' :: t'))
                                    (TAKE (2 ** n) mask) (TAKE (2 ** n) frozen))’,
                         ‘T’] mp_tac vec_split_prob_first_half >>
            impl_tac >- (simp[LENGTH_TAKE] >> decide_tac) >>
            disch_then SUBST1_TAC >> simp[]))
    >- (qabbrev_tac ‘j = i - 2n ** n’ >>
        ‘j < 2n ** n ∧ i = j + 2n ** n’ by (simp[Abbr ‘j’] >> decide_tac) >>
        simp[EL_APPEND_EQN, TAKE_APPEND2] >>
        ‘j + 2n ** n = 2n ** n + j’ by decide_tac >>
        pop_assum SUBST1_TAC >>
        conj_tac >>
        irule (GSYM vec_split_prob_second_half) >>
        simp[LENGTH_TAKE, polar_encode_length_any]))
QED

(* Prefix equivalence between vec_sc_decode_prefix and sc_decode_prefix.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem vec_sc_decode_prefix_eq_sc_decode_prefix[local]:
  ∀(W : (bool, β) memoryless_channel) n A u_frozen y k.
    wf_bdmc W ∧
    LENGTH u_frozen = 2 ** n ∧ LENGTH y = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y ∧ k ≤ 2 ** n ⇒
    vec_sc_decode_prefix (channel_prob_pairs W y)
      (GENLIST (λi. i ∈ A) (2 ** n)) u_frozen k =
    sc_decode_prefix W (2 ** n) A u_frozen y k
Proof
  rpt gen_tac >> Induct_on ‘k’ >- simp[] >>
  strip_tac >>
  ‘k ≤ 2n ** n ∧ k < 2n ** n’ by decide_tac >>
  simp[vec_sc_decode_prefix_SUC, sc_decode_prefix_SUC] >>
  Cases_on ‘k ∈ A’ >> simp[vec_bit_decision_def, sc_bit_decision_def] >>
  qspecl_then [‘W’, ‘n’, ‘k’, ‘T’, ‘y’,
               ‘sc_decode_prefix W (2 ** n) A u_frozen y k’]
    mp_tac mcchannel_split_channel_eq_vec_split_prob >>
  qspecl_then [‘W’, ‘n’, ‘k’, ‘F’, ‘y’,
               ‘sc_decode_prefix W (2 ** n) A u_frozen y k’]
    mp_tac mcchannel_split_channel_eq_vec_split_prob >>
  simp[extreal_le_eq]
QED

(* Exact equivalence between vec_sc_decode on channel_prob_pairs W y and sc_decode.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem vec_sc_decode_eq_sc_decode[local]:
  ∀(W : (bool, β) memoryless_channel) n A u_frozen y.
    wf_bdmc W ∧
    LENGTH u_frozen = 2 ** n ∧ LENGTH y = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    vec_sc_decode (channel_prob_pairs W y)
      (GENLIST (λi. i ∈ A) (2 ** n)) u_frozen =
    sc_decode W (2 ** n) A u_frozen y
Proof
  rpt strip_tac >>
  simp[vec_sc_decode_def, sc_decode_eq_prefix,
       vec_sc_decode_prefix_eq_sc_decode_prefix]
QED

(* Exact functional equivalence of O(N log N) butterfly fast_sc_decode and
   sequential specification sc_decode (for arbitrary A : num -> bool).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fast_sc_decode_correct_any_A:
  ∀(W : (bool, β) memoryless_channel) n A u_frozen y.
    wf_bdmc W ∧
    LENGTH u_frozen = 2 ** n ∧ LENGTH y = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    fast_sc_decode W (2 ** n) A u_frozen y =
    sc_decode W (2 ** n) A u_frozen y
Proof
  rpt strip_tac >>
  simp[fast_sc_decode_def] >>
  Cases_on ‘fast_sc_butterfly_probs (channel_prob_pairs W y)
              (GENLIST (λi. i ∈ A) (2 ** n)) u_frozen’ >>
  Cases_on ‘r’ >> simp[] >>
  qspecl_then [‘n’, ‘channel_prob_pairs W y’,
               ‘GENLIST (λi. i ∈ A) (2 ** n)’, ‘u_frozen’,
               ‘q’, ‘q'’, ‘r'’] mp_tac fast_sc_butterfly_probs_invariant >>
  simp[vec_sc_decode_eq_sc_decode]
QED

(* Canonical contract theorem: exact functional equivalence of fast_sc_decode
   and sc_decode (Erdal Arıkan, 2009, Section VIII-B, pp. 15-17).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fast_sc_decode_correct:
  ∀(W : (bool, β) memoryless_channel) n A u_frozen y.
    wf_bdmc W ∧ A ⊆ count (2 ** n) ∧
    LENGTH u_frozen = 2 ** n ∧ LENGTH y = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    fast_sc_decode W (2 ** n) A u_frozen y =
    sc_decode W (2 ** n) A u_frozen y
Proof
  rw[fast_sc_decode_correct_any_A]
QED

(* All-frozen behavior of sc_decode at A = ∅: returns u when LENGTH u = N.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_empty_eq[local]:
  ∀(W : (bool, β) memoryless_channel) N u y.
    LENGTH u = N ⇒ sc_decode W N ∅ u y = u
Proof
  rpt strip_tac >>
  irule LIST_EQ >> simp[EL_sc_decode]
QED

(* When A = ∅ (all bits frozen to u), a single O(N log N) butterfly pass returns
   u_hat = u and all 2^n exact coordinate split-channel likelihood pairs
   (W_N^{(i)}(y, u_0^{i-1} | F), W_N^{(i)}(y, u_0^{i-1} | T))
   (Erdal Arıkan, 2009, Section IX Eq. (79), p. 18).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fast_sc_leaf_probs_empty_set:
  ∀(W : (bool, β) memoryless_channel) n u y.
    wf_bdmc W ∧ LENGTH u = 2 ** n ∧ LENGTH y = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    fast_sc_decode W (2 ** n) ∅ u y = u ∧
    LENGTH (fast_sc_leaf_probs W (2 ** n) ∅ u y) = 2 ** n ∧
    ∀i. i < 2 ** n ⇒
        EL i (fast_sc_leaf_probs W (2 ** n) ∅ u y) =
          (real (mcchannel (split_channel W (2 ** n) i) F {(y, TAKE i u)}),
           real (mcchannel (split_channel W (2 ** n) i) T {(y, TAKE i u)}))
Proof
  rpt strip_tac
  >- simp[fast_sc_decode_correct_any_A, sc_decode_empty_eq]
  >- (simp[fast_sc_leaf_probs_def] >>
      Cases_on ‘fast_sc_butterfly_probs (channel_prob_pairs W y)
                  (GENLIST (λi. F) (2 ** n)) u’ >>
      Cases_on ‘r’ >> simp[] >>
      qspecl_then [‘n’, ‘channel_prob_pairs W y’,
                   ‘GENLIST (λi. F) (2 ** n)’, ‘u’,
                   ‘q’, ‘q'’, ‘r'’] mp_tac fast_sc_butterfly_probs_lengths >>
      simp[])
  >- (‘fast_sc_decode W (2 ** n) ∅ u y = u’
        by simp[fast_sc_decode_correct_any_A, sc_decode_empty_eq] >>
      qpat_x_assum ‘fast_sc_decode _ _ _ _ _ = u’ mp_tac >>
      simp[fast_sc_decode_def, fast_sc_leaf_probs_def] >>
      Cases_on ‘fast_sc_butterfly_probs (channel_prob_pairs W y)
                  (GENLIST (λi. F) (2 ** n)) u’ >>
      Cases_on ‘r’ >> simp[] >> disch_then SUBST_ALL_TAC >>
      qspecl_then [‘n’, ‘channel_prob_pairs W y’,
                   ‘GENLIST (λi. F) (2 ** n)’, ‘u’,
                   ‘u’, ‘q'’, ‘r'’] mp_tac fast_sc_butterfly_probs_invariant >>
      impl_tac >- simp[] >>
      disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
      qspecl_then [‘W’, ‘n’, ‘i’, ‘F’, ‘y’, ‘TAKE i u’] mp_tac
        mcchannel_split_channel_eq_vec_split_prob >>
      qspecl_then [‘W’, ‘n’, ‘i’, ‘T’, ‘y’, ‘TAKE i u’] mp_tac
        mcchannel_split_channel_eq_vec_split_prob >>
      simp[LENGTH_TAKE])
QED

(* ------------------------------------------------------------------------- *)
(* Block 4: Butterfly SC Decoding Cost Model & O(N log N) Complexity         *)
(* ------------------------------------------------------------------------- *)

(* Recursive operation count of fast_sc_butterfly_probs on a length-k vector:
   - Base k = 0: 0 operations.
   - Base k = 1: 2 operations at an information leaf (comparison + negation),
     1 operation at a frozen leaf (reading frozen bit).
   - Step k >= 2 (half = k DIV 2):
       8 * half (mk_minus_probs) + 5 * half (mk_plus_probs) +
       5 * half (bxor + interleave + u_hat/leaves append) = 18 * half
       plus both half-size recursive calls.

   Written by Gemini (Google DeepMind AI agent) *)
Definition fast_sc_butterfly_cost_def:
  fast_sc_butterfly_cost (k : num) (mask : bool list) (frozen : bool list) : num =
    if k = 0 then 0
    else if k = 1 then
      (if NULL mask then 1 else if HD mask then 2 else 1)
    else
      let half = k DIV 2 in
        18 * half +
        fast_sc_butterfly_cost half (TAKE half mask) (TAKE half frozen) +
        fast_sc_butterfly_cost half (DROP half mask) (DROP half frozen)
Termination
  WF_REL_TAC ‘measure FST’ >> simp[]
End

(* Total operation count of fast_sc_decode W N A u_frozen y:
   2 * LENGTH y channel evaluations + N mask-generation steps +
   fast_sc_butterfly_cost (LENGTH y) (GENLIST (λi. i ∈ A) N) u_frozen.

   Written by Gemini (Google DeepMind AI agent) *)
Definition fast_sc_decode_cost_def:
  fast_sc_decode_cost (W : (bool, β) memoryless_channel) (N : num)
    (A : num -> bool) (u_frozen : bool list) (y : β list) : num =
    2 * LENGTH y + N +
    fast_sc_butterfly_cost (LENGTH y) (GENLIST (λi. i ∈ A) N) u_frozen
End

(* Tight lower and upper bounds on fast_sc_butterfly_cost at k = 2 ** n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fast_sc_butterfly_cost_pow2_bounds:
  ∀n mask frozen.
    9 * n * (2 ** n) + 2 ** n ≤ fast_sc_butterfly_cost (2 ** n) mask frozen ∧
    fast_sc_butterfly_cost (2 ** n) mask frozen ≤ 9 * n * (2 ** n) + 2 * (2 ** n)
Proof
  Induct_on ‘n’
  >- (rpt gen_tac >> ONCE_REWRITE_TAC[fast_sc_butterfly_cost_def] >> rw[]) >>
  rpt gen_tac >>
  ONCE_REWRITE_TAC[fast_sc_butterfly_cost_def] >>
  simp[LET_THM] >>
  simp[EXP] >>
  first_assum (qspecl_then [‘TAKE (2 ** n) mask’, ‘TAKE (2 ** n) frozen’]
                 mp_tac) >>
  first_x_assum (qspecl_then [‘DROP (2 ** n) mask’, ‘DROP (2 ** n) frozen’]
                   mp_tac) >>
  simp[ADD1, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >> decide_tac
QED

(* Worst-case O(N log N) time complexity of butterfly Successive Cancellation
   decoding (Erdal Arıkan, 2009, Section I-C.6 Theorem 5 & Section VIII-B).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fast_sc_decode_complexity_nlogn:
  ∃(C : num). 0 < C ∧
    ∀(W : (bool, β) memoryless_channel) n A u_frozen y.
      wf_bdmc W ∧ 1 ≤ n ∧ A ⊆ count (2 ** n) ∧
      LENGTH u_frozen = 2 ** n ∧ LENGTH y = 2 ** n ∧
      EVERY (λyi. yi ∈ mccodomain W) y ⇒
      fast_sc_decode_cost W (2 ** n) A u_frozen y ≤
        C * (2 ** n) * LOG 2 (2 ** n)
Proof
  qexists_tac ‘14’ >> simp[] >> rpt strip_tac >>
  simp[fast_sc_decode_cost_def, logrootTheory.LOG_POW] >>
  ‘5 * (2 ** n) ≤ 5 * (2 ** n) * n’ by simp[] >>
  pop_assum mp_tac >>
  qspecl_then [‘n’, ‘GENLIST (λi. i ∈ A) (2 ** n)’, ‘u_frozen’]
    mp_tac fast_sc_butterfly_cost_pow2_bounds >>
  decide_tac
QED

(* Asymptotic complexityTheory.big_O formulation of O(N log N) SC decoding.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fast_sc_decode_complexity_big_O:
  ∀(W : (bool, β) memoryless_channel) A_seq uf_seq y_seq.
    (∀n. LENGTH (y_seq n) = 2 ** n) ⇒
    (λn. fast_sc_decode_cost W (2 ** n) (A_seq n) (uf_seq n) (y_seq n)) ∈
      big_O (λn. (2 ** n) * LOG 2 (2 ** n))
Proof
  rw[complexityTheory.big_O_def] >>
  qexistsl_tac [‘0’, ‘14’] >> rpt strip_tac >>
  ‘1 ≤ n’ by decide_tac >>
  simp[fast_sc_decode_cost_def, logrootTheory.LOG_POW] >>
  ‘5 * (2 ** n) ≤ 5 * (2 ** n) * n’ by simp[] >>
  pop_assum mp_tac >>
  qspecl_then [‘n’, ‘GENLIST (λi. i ∈ A_seq n) (2 ** n)’, ‘uf_seq n’]
    mp_tac fast_sc_butterfly_cost_pow2_bounds >>
  decide_tac
QED

(* ------------------------------------------------------------------------- *)
(* Block 5: Compute-Safe [simp] Rules for Concrete BEC/BSC & Numeral N = 2^n *)
(* ------------------------------------------------------------------------- *)

(* Exhaustive case rewrite for erasure_bit so y ∈ {E_T; E_F; Erasure} reduces
   to T even on universally quantified y : erasure_bit (T2-F18-01, T3-17).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem erasure_bit_in_set_simp[simp]:
  (∀y : erasure_bit. (y = E_T ∨ y = E_F ∨ y = Erasure) ⇔ T) ∧
  (∀P (n : num) (x : α). EVERY P (REPLICATE n x) ⇔ (n = 0 ∨ P x))
Proof
  conj_tac
  >- (Cases >> simp[])
  >- (gen_tac >> Induct >> simp[] >> metis_tac[])
QED

(* Concrete wf_bdmc and accessor [simp] rules for binary_erasure_channel.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem binary_erasure_channel_simps[simp]:
  ∀p. 0 ≤ p ∧ p ≤ 1 ⇒
      wf_bdmc (binary_erasure_channel p) ∧
      mcdomain (binary_erasure_channel p) = 𝕌(:bool) ∧
      mccodomain (binary_erasure_channel p) = {E_T; E_F; Erasure} ∧
      mcevents (binary_erasure_channel p) = POW {E_T; E_F; Erasure}
Proof
  rpt strip_tac >> simp[wf_bdmc_binary_erasure_channel] >>
  drule_all wf_binary_erasure_channel0 >> strip_tac >>
  drule bdmcTheory.memoryless_channel_ABS_accessors >>
  simp[binary_erasure_channel_def, binary_erasure_channel0_def,
       mcdomain0_def, mccodomain0_def, mcevents0_def, mcsigma0_def] >>
  rw[Once EXTENSION] >> Cases_on ‘x’ >> simp[]
QED

(* Concrete wf_bdmc and accessor [simp] rules for binary_symmetric_channel.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem binary_symmetric_channel_simps[simp]:
  ∀p. 0 ≤ p ∧ p ≤ 1 ⇒
      wf_bdmc (binary_symmetric_channel p) ∧
      mcdomain (binary_symmetric_channel p) = 𝕌(:bool) ∧
      mccodomain (binary_symmetric_channel p) = 𝕌(:bool) ∧
      mcevents (binary_symmetric_channel p) = POW 𝕌(:bool)
Proof
  rpt strip_tac >> simp[wf_bdmc_binary_symmetric_channel] >>
  drule_all wf_binary_symmetric_channel0 >> strip_tac >>
  drule bdmcTheory.memoryless_channel_ABS_accessors >>
  simp[binary_symmetric_channel_def, binary_symmetric_channel0_def,
       mcdomain0_def, mccodomain0_def, mcevents0_def, mcsigma0_def] >>
  rw[Once EXTENSION] >> Cases_on ‘x’ >> simp[]
QED

(* Direct real-valued transition probability [simp] rules for BEC(Normal r),
   BEC(0), and BEC(1), eliminating all extreal terms before butterfly recursion.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem real_mcchannel_bec_simps[simp]:
  (∀r x y. 0 ≤ r ∧ r ≤ 1 ⇒
     real (mcchannel (binary_erasure_channel (Normal r)) x {y}) =
       if y = Erasure then r
       else if y = (if x then E_T else E_F) then 1 - r
       else 0) ∧
  (∀x y.
     real (mcchannel (binary_erasure_channel 0) x {y}) =
       if y = Erasure then 0
       else if y = (if x then E_T else E_F) then 1
       else 0) ∧
  (∀x y.
     real (mcchannel (binary_erasure_channel 1) x {y}) =
       if y = Erasure then 1 else 0)
Proof
  rpt conj_tac >> rpt strip_tac
  >- (qspecl_then [‘Normal r’, ‘x’, ‘y’] mp_tac
        bdmcTheory.mcchannel_binary_erasure_channel_singleton >>
      simp[bool_to_erasure_bit_def, extreal_of_num_def, extreal_le_eq,
           extreal_sub_eq] >>
      rw[])
  >- (qspecl_then [‘0’, ‘x’, ‘y’] mp_tac
        bdmcTheory.mcchannel_binary_erasure_channel_singleton >>
      simp[bool_to_erasure_bit_def, extreal_of_num_def, extreal_le_eq,
           extreal_sub_eq] >>
      rw[])
  >- (qspecl_then [‘1’, ‘x’, ‘y’] mp_tac
        bdmcTheory.mcchannel_binary_erasure_channel_singleton >>
      simp[bool_to_erasure_bit_def, extreal_of_num_def, extreal_le_eq,
           extreal_sub_eq] >>
      rw[])
QED

(* Direct real-valued transition probability [simp] rules for BSC(Normal r),
   BSC(0), and BSC(1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem real_mcchannel_bsc_simps[simp]:
  (∀r x y. 0 ≤ r ∧ r ≤ 1 ⇒
     real (mcchannel (binary_symmetric_channel (Normal r)) x {y}) =
       if y ≠ x then r else 1 - r) ∧
  (∀x y.
     real (mcchannel (binary_symmetric_channel 0) x {y}) =
       if y ≠ x then 0 else 1) ∧
  (∀x y.
     real (mcchannel (binary_symmetric_channel 1) x {y}) =
       if y ≠ x then 1 else 0)
Proof
  rpt conj_tac >> rpt strip_tac
  >- (qspecl_then [‘Normal r’, ‘x’, ‘y’] mp_tac
        bdmcTheory.mcchannel_binary_symmetric_channel_singleton >>
      simp[extreal_of_num_def, extreal_le_eq, extreal_sub_eq] >> rw[])
  >- (qspecl_then [‘0’, ‘x’, ‘y’] mp_tac
        bdmcTheory.mcchannel_binary_symmetric_channel_singleton >>
      simp[extreal_of_num_def, extreal_le_eq, extreal_sub_eq] >> rw[])
  >- (qspecl_then [‘1’, ‘x’, ‘y’] mp_tac
        bdmcTheory.mcchannel_binary_symmetric_channel_singleton >>
      simp[extreal_of_num_def, extreal_le_eq, extreal_sub_eq] >> rw[])
QED

(* CONS-guarded [simp] rules for stride-2 get_every_nth_element and polar_encode
   so ground lists like polar_encode [T;F;T;T;F;T;F;F] (T2-F18-04) reduce in
   srw_ss() without ever looping on symbolic lists.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_cons_simps[simp]:
  get_every_nth_element ([] : bool list) 2 0 = [] ∧
  get_every_nth_element ([] : bool list) 2 1 = [] ∧
  (∀b. get_every_nth_element [b] 2 0 = [b]) ∧
  (∀b. get_every_nth_element [b] 2 1 = []) ∧
  (∀b0 b1 rest.
     get_every_nth_element (b0 :: b1 :: rest) 2 0 =
       b0 :: get_every_nth_element rest 2 0 ∧
     get_every_nth_element (b0 :: b1 :: rest) 2 1 =
       b1 :: get_every_nth_element rest 2 1) ∧
  polar_encode [] = [] ∧
  (∀b. polar_encode [b] = [b]) ∧
  (∀b0 b1 rest.
     polar_encode (b0 :: b1 :: rest) =
       polar_encode
         (bxor (b0 :: get_every_nth_element rest 2 0)
               (b1 :: get_every_nth_element rest 2 1)) ++
       polar_encode (b1 :: get_every_nth_element rest 2 1))
Proof
  simp[split_channelTheory.get_every_2nd_cons2,
       polar_encodeTheory.polar_encode_nil_sing,
       interleaveTheory.get_every_nth_element_compute] >>
  rpt gen_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [polar_encode_def])) >>
  simp[LET_THM, deinterleave_2_eq, split_channelTheory.get_every_2nd_cons2]
QED

(* Primitive-recursive fuel-bounded power-of-two recognizer for numeral N.

   Written by Gemini (Google DeepMind AI agent) *)
Definition is_pow2_aux_def:
  is_pow2_aux 0 (n : num) = F ∧
  is_pow2_aux (SUC fuel) n =
    if n = 0 then F
    else if n = 1 then T
    else (n MOD 2 = 0) ∧ is_pow2_aux fuel (n DIV 2)
End
val _ = export_rewrites ["is_pow2_aux_compute"];

(* Fuel-bounded characterization of is_pow2_aux when n <= fuel.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_pow2_aux_fuel_iff[local]:
  ∀fuel n.
    n ≤ fuel ⇒
    (is_pow2_aux fuel n ⇔ ∃k. n = 2 ** k)
Proof
  Induct_on ‘fuel’
  >- rw[is_pow2_aux_def] >>
  qx_gen_tac ‘m’ >> strip_tac >>
  simp[is_pow2_aux_def] >>
  Cases_on ‘m = 0’ >- simp[] >>
  Cases_on ‘m = 1’ >- (simp[] >> qexists_tac ‘0’ >> simp[]) >>
  simp[] >>
  ‘2n ≤ m ∧ m MOD 2n < 2n’ by simp[] >>
  ‘m = (m DIV 2n) * 2n + m MOD 2n’
    by metis_tac[DIVISION, DECIDE “0n < 2n”] >>
  ‘m DIV 2n ≤ fuel’ by decide_tac >>
  first_x_assum (qspec_then ‘m DIV 2n’ mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  eq_tac >> strip_tac
  >- (qexists_tac ‘SUC k’ >> simp[EXP] >> decide_tac)
  >- (Cases_on ‘k’ >- gvs[] >> gvs[EXP] >> qexists_tac ‘n’ >> simp[])
QED

(* Equivalence between is_pow2_aux N N and ∃n. N = 2 ** n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_pow2_aux_iff_pow2:
  ∀N. is_pow2_aux N N ⇔ ∃n. N = 2 ** n
Proof
  gen_tac >> irule is_pow2_aux_fuel_iff >> simp[]
QED

(* Additive decomposition of REPLICATE (a + b) x into REPLICATE a x ++ REPLICATE b x.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem replicate_add[local]:
  ∀a b (x : α). REPLICATE (a + b) x = REPLICATE a x ++ REPLICATE b x
Proof
  Induct_on ‘a’ >> simp[ADD_CLAUSES]
QED

(* All-false mask behavior of fast_sc_butterfly_probs: returns frozen vector
   unconditionally without requiring wf_bdmc.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fast_sc_butterfly_probs_all_false[local]:
  ∀n (P : (real # real) list) (frozen : bool list).
    LENGTH P = 2 ** n ∧ LENGTH frozen = 2 ** n ⇒
    FST (fast_sc_butterfly_probs P (REPLICATE (2 ** n) F) frozen) = frozen
Proof
  Induct_on ‘n’
  >- (rpt strip_tac >> Cases_on ‘P’ >> gvs[] >>
      Cases_on ‘h’ >> Cases_on ‘frozen’ >>
      gvs[rich_listTheory.REPLICATE_compute]) >>
  pop_assum (fn ih =>
    rpt strip_tac >>
    Cases_on ‘P’ >> gvs[EXP] >>
    Cases_on ‘t’ >> gvs[EXP] >>
    ‘SUC (LENGTH t' DIV 2) = 2 ** n’
      by (qpat_assum ‘SUC (SUC _) = _’ (mp_tac o AP_TERM “λx:num. x DIV 2”) >>
          simp[]) >>
    ‘REPLICATE (2 * 2 ** n) F = REPLICATE (2 ** n) F ++ REPLICATE (2 ** n) F’
      by (‘2n * (2n ** n) = 2n ** n + 2n ** n’ by decide_tac >>
          pop_assum SUBST1_TAC >> simp[replicate_add]) >>
    pop_assum SUBST1_TAC >>
    simp[TAKE_APPEND1, DROP_APPEND2, TAKE_LENGTH_ID_rwt] >>
    Cases_on ‘fast_sc_butterfly_probs (mk_minus_probs (h :: h' :: t'))
                (REPLICATE (2 ** n) F) (TAKE (2 ** n) frozen)’ >>
    Cases_on ‘r’ >> simp[] >>
    qspecl_then [‘n’, ‘mk_minus_probs (h :: h' :: t')’,
                 ‘REPLICATE (2 ** n) F’, ‘TAKE (2 ** n) frozen’,
                 ‘q’, ‘q'’, ‘r'’] mp_tac fast_sc_butterfly_probs_lengths >>
    impl_tac >- simp[] >> strip_tac >>
    Cases_on ‘fast_sc_butterfly_probs (mk_plus_probs (h :: h' :: t') q')
                (REPLICATE (2 ** n) F) (DROP (2 ** n) frozen)’ >>
    Cases_on ‘r’ >> simp[] >>
    qspecl_then [‘mk_minus_probs (h :: h' :: t')’, ‘TAKE (2 ** n) frozen’]
      mp_tac ih >>
    impl_tac >- simp[LENGTH_TAKE] >> simp[] >> disch_then SUBST1_TAC >>
    qspecl_then [‘mk_plus_probs (h :: h' :: t') q'’, ‘DROP (2 ** n) frozen’]
      mp_tac ih >>
    impl_tac >- simp[] >> simp[] >> disch_then SUBST1_TAC >>
    simp[TAKE_DROP])
QED

(* All-frozen A = ∅ reduction for fast_sc_decode on concrete power-of-two numerals
   (solves T2-F18-03 immediately even when fast_sc_decode_def is omitted from refs).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem fast_sc_decode_empty_numeral_simp[simp]:
  ∀(W : (bool, β) memoryless_channel) k u_frozen y.
    is_pow2_aux (NUMERAL k) (NUMERAL k) ∧
    LENGTH u_frozen = NUMERAL k ∧
    LENGTH y = NUMERAL k ⇒
    fast_sc_decode W (NUMERAL k) ∅ u_frozen y = u_frozen
Proof
  rpt strip_tac >>
  fs[is_pow2_aux_iff_pow2] >>
  simp[fast_sc_decode_def] >>
  ‘GENLIST (λi. F) (2 ** n) = REPLICATE (2 ** n) F’
    by (irule LIST_EQ >> simp[rich_listTheory.EL_REPLICATE]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘n’, ‘channel_prob_pairs W y’, ‘u_frozen’] mp_tac
    fast_sc_butterfly_probs_all_false >>
  simp[]
QED

(* Numeral specialization of sc_decode = fast_sc_decode for concrete power-of-two N
   (kept non-[simp] to avoid conflicting with reverse orientation of
   fast_sc_decode_correct in check_goal_with_thms when fast_sc_decode_def is
   absent from refs).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_eq_fast_sc_decode_numeral:
  ∀(W : (bool, β) memoryless_channel) k A u_frozen y.
    is_pow2_aux (NUMERAL k) (NUMERAL k) ∧
    wf_bdmc W ∧
    LENGTH u_frozen = NUMERAL k ∧
    LENGTH y = NUMERAL k ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    sc_decode W (NUMERAL k) A u_frozen y =
    fast_sc_decode W (NUMERAL k) A u_frozen y
Proof
  rpt strip_tac >>
  fs[is_pow2_aux_iff_pow2] >>
  qspecl_then [‘W’, ‘n’, ‘A’, ‘u_frozen’, ‘y’] mp_tac
    fast_sc_decode_correct_any_A >>
  simp[]
QED

(* Rewrites sc_bit_decision for concrete power-of-two numerals NUMERAL k > 1
   into the O(N log N) butterfly leaf probability pair, leaving N = 1 untouched
   for T2-F14-01..03.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_bit_decision_numeral_simp[simp]:
  ∀(W : (bool, β) memoryless_channel) k i y u_prev.
    1 < NUMERAL k ∧
    is_pow2_aux (NUMERAL k) (NUMERAL k) ∧
    wf_bdmc W ∧
    i < NUMERAL k ∧
    LENGTH y = NUMERAL k ∧
    EVERY (λyi. yi ∈ mccodomain W) y ∧
    LENGTH u_prev = i ⇒
    sc_bit_decision W (NUMERAL k) i y u_prev =
      (case EL i (fast_sc_leaf_probs W (NUMERAL k) ∅
                    (u_prev ++ REPLICATE (NUMERAL k - i) F) y) of
         (p0, p1) => ¬(p1 ≤ p0))
Proof
  rpt strip_tac >>
  fs[is_pow2_aux_iff_pow2] >>
  qspecl_then [‘W’, ‘n’, ‘u_prev ++ REPLICATE (2 ** n - i) F’, ‘y’] mp_tac
    fast_sc_leaf_probs_empty_set >>
  impl_tac >- (simp[] >> decide_tac) >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  first_x_assum (qspec_then ‘i’ mp_tac) >>
  impl_tac >- simp[] >>
  simp[TAKE_APPEND1, TAKE_LENGTH_ID_rwt] >> disch_then SUBST1_TAC >>
  simp[sc_bit_decision_def] >>
  qspecl_then [‘W’, ‘n’, ‘i’, ‘T’, ‘y’, ‘u_prev’] mp_tac
    mcchannel_split_channel_eq_vec_split_prob >>
  qspecl_then [‘W’, ‘n’, ‘i’, ‘F’, ‘y’, ‘u_prev’] mp_tac
    mcchannel_split_channel_eq_vec_split_prob >>
  simp[extreal_le_eq]
QED
