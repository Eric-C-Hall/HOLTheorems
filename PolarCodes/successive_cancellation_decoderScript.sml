(* ========================================================================= *)
(*   Successive Cancellation (SC) Decoder, G_N-Coset Codeword Assembly,      *)
(*   Block Error Probabilities, Proposition 2, and Polar Code                *)
(*   Information-Set Optimality                                              *)
(*   (Erdal Arıkan, 2009, arXiv:0807.3917, Sections I-C & V).                *)
(*                                                                           *)
(*   Based on initial stub by Eric Hall (under the guidance of Michael       *)
(*   Norrish). Edited and completed by Gemini (Google DeepMind AI agent):    *)
(*   formalized division-free deterministic sc_bit_decision and sc_decode    *)
(*   (with successive_cancellation_decoder alias), G_N-coset codeword        *)
(*   assembly, fixed-frozen and ensemble-averaged block error probabilities, *)
(*   structural decoder & frozen-averaging equivalence theorems, polar       *)
(*   coding rule existence and sum-minimization optimality, and              *)
(*   Proposition 2 (proposition_2_avg, proposition_2_exists_frozen,          *)
(*   proposition_2).                                                         *)
(* ========================================================================= *)

Theory successive_cancellation_decoder

Ancestors
  combin pair relation arithmetic pred_set list rich_list sorting
  real real_sigma transc sigma_algebra extreal_base extreal
  measure probability bitstring bxor_lemmas interleave
  fundamental jared_yeager_prod_list ecc_prob_space
  memoryless_channel bhattacharyya capacity
  polar_encode combine_channel split_channel bdmc

Libs
  dep_rewrite numLib realLib;

val _ = hide "W";
val _ = hide "S";
val _ = hide "K";

(* ------------------------------------------------------------------------- *)
(* Block 1: Division-Free Deterministic Successive Cancellation Decoder      *)
(* ------------------------------------------------------------------------- *)

(* Division-free deterministic Successive Cancellation bit decision function
   h_i(y_1^N, u_hat_1^{i-1}) from Erdal Arıkan (2009), Section I-C Eq. (12),
   p. 4: returns F (0) whenever W_N^{(i)}(y, u_hat_prev | T) <=
   W_N^{(i)}(y, u_hat_prev | F) (breaking ties in favor of F, including 0 <= 0
   and zero-denominator cases), and returns T (1) otherwise.

   Written by Gemini (Google DeepMind AI agent) *)
Definition sc_bit_decision_def[nocompute]:
  sc_bit_decision (W : (bool, β) memoryless_channel) (N : num) (i : num)
    (y : β list) (u_hat_prev : bool list) : bool ⇔
    ¬(mcchannel (split_channel W N i) T {(y, u_hat_prev)} ≤
      mcchannel (split_channel W N i) F {(y, u_hat_prev)})
End

(* Sequential Successive Cancellation (SC) decoder from Erdal Arıkan (2009),
   Section I-C Eq. (11), p. 4: sequentially generates [u_hat_0; ...; u_hat_{N-1}]
   where u_hat_i = sc_bit_decision W N i y [u_hat_0; ...; u_hat_{i-1}] for i in A
   and u_hat_i = EL i u_frozen for i not in A.

   Written by Gemini (Google DeepMind AI agent) *)
Definition sc_decode_def:
  sc_decode (W : (bool, β) memoryless_channel) (N : num)
    (A : num -> bool) (u_frozen : bool list) (y : β list) : bool list =
    FOLDL
      (λu_hat_prev i.
         u_hat_prev ++
         [if i ∈ A then sc_bit_decision W N i y u_hat_prev
          else EL i u_frozen])
      [] (GENLIST I N)
End

(* Canonical full-name constant alias for sc_decode matching theory name.

   Written by Gemini (Google DeepMind AI agent) *)
Definition successive_cancellation_decoder_def:
  successive_cancellation_decoder = sc_decode
End

(* Prefix of the first k sequentially decoded SC bits (for inductive proofs).

   Written by Gemini (Google DeepMind AI agent) *)
Definition sc_decode_prefix_def:
  sc_decode_prefix (W : (bool, β) memoryless_channel) (N : num)
    (A : num -> bool) (u_frozen : bool list) (y : β list) (k : num) : bool list =
    FOLDL
      (λu_hat_prev i.
         u_hat_prev ++
         [if i ∈ A then sc_bit_decision W N i y u_hat_prev
          else EL i u_frozen])
      [] (GENLIST I k)
End

(* Element lookup on a list appended with a singleton element.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem el_append_sing[local]:
  ∀(l : α list) x i.
    i ≤ LENGTH l ⇒
    EL i (l ++ [x]) = (if i < LENGTH l then EL i l else x)
Proof
  Induct_on ‘l’ >> Cases_on ‘i’ >> simp[]
QED

(* Full SC decoding of block-length N equals the length-N prefix sc_decode_prefix.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_eq_prefix:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y.
    sc_decode W N A u_frozen y = sc_decode_prefix W N A u_frozen y N
Proof
  REWRITE_TAC[sc_decode_def, sc_decode_prefix_def]
QED

(* Base step k = 0 of sc_decode_prefix.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_prefix_0[simp]:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y.
    sc_decode_prefix W N A u_frozen y 0 = []
Proof
  simp[sc_decode_prefix_def]
QED

(* Step recurrence k -> SUC k of sc_decode_prefix.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_prefix_SUC:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y k.
    sc_decode_prefix W N A u_frozen y (SUC k) =
      sc_decode_prefix W N A u_frozen y k ++
      [if k ∈ A then
         sc_bit_decision W N k y (sc_decode_prefix W N A u_frozen y k)
       else EL k u_frozen]
Proof
  simp[sc_decode_prefix_def, GENLIST, SNOC_APPEND, FOLDL_APPEND]
QED

(* Exact length k of sc_decode_prefix W N A u_frozen y k.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem LENGTH_sc_decode_prefix[simp]:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y k.
    LENGTH (sc_decode_prefix W N A u_frozen y k) = k
Proof
  Induct_on ‘k’ >> simp[sc_decode_prefix_SUC]
QED

(* Exact output length N of sc_decode W N A u_frozen y.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem LENGTH_sc_decode[simp]:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y.
    LENGTH (sc_decode W N A u_frozen y) = N
Proof
  simp[sc_decode_eq_prefix]
QED

(* Alias of LENGTH_sc_decode for Proposition 2 first-error decomposition.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_length:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y.
    LENGTH (sc_decode W N A u_frozen y) = N
Proof
  simp[]
QED

(* Taking the first j <= k bits of sc_decode_prefix yields sc_decode_prefix at j.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem TAKE_sc_decode_prefix:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y j k.
    j ≤ k ⇒
    TAKE j (sc_decode_prefix W N A u_frozen y k) =
      sc_decode_prefix W N A u_frozen y j
Proof
  Induct_on ‘k’ >- simp[] >>
  rpt strip_tac >>
  Cases_on ‘j = SUC k’
  >- (gvs[] >> simp[TAKE_LENGTH_TOO_LONG]) >>
  ‘j ≤ k’ by decide_tac >>
  simp[sc_decode_prefix_SUC, TAKE_APPEND1]
QED

(* Taking the first i <= N bits of sc_decode yields sc_decode_prefix at i.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem TAKE_sc_decode:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y i.
    i ≤ N ⇒
    TAKE i (sc_decode W N A u_frozen y) =
      sc_decode_prefix W N A u_frozen y i
Proof
  simp[sc_decode_eq_prefix, TAKE_sc_decode_prefix]
QED

(* Coordinate-i bit characterization of sc_decode_prefix for i < k.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem EL_sc_decode_prefix:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y i k.
    i < k ⇒
    EL i (sc_decode_prefix W N A u_frozen y k) =
      if i ∈ A then
        sc_bit_decision W N i y (sc_decode_prefix W N A u_frozen y i)
      else EL i u_frozen
Proof
  Induct_on ‘k’ >- simp[] >>
  rpt strip_tac >>
  ‘i ≤ k’ by decide_tac >>
  simp[sc_decode_prefix_SUC, el_append_sing] >>
  Cases_on ‘i < k’ >- simp[] >>
  ‘i = k’ by decide_tac >>
  gvs[]
QED

(* Coordinate-i bit equation for sc_decode (Erdal Arıkan, 2009, Eq. 11).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem EL_sc_decode:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y i.
    i < N ⇒
    EL i (sc_decode W N A u_frozen y) =
      if i ∈ A then
        sc_bit_decision W N i y (TAKE i (sc_decode W N A u_frozen y))
      else EL i u_frozen
Proof
  rpt strip_tac >>
  ‘i ≤ N’ by decide_tac >>
  simp[TAKE_sc_decode, sc_decode_eq_prefix, EL_sc_decode_prefix]
QED

(* Alias of EL_sc_decode for Proposition 2 first-error decomposition.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_el:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y i.
    i < N ⇒
    EL i (sc_decode W N A u_frozen y) =
      if i ∈ A then
        sc_bit_decision W N i y (TAKE i (sc_decode W N A u_frozen y))
      else EL i u_frozen
Proof
  simp[EL_sc_decode]
QED

(* Frozen-coordinate fidelity: sc_decode preserves u_frozen on all i < N with i not in A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem EL_sc_decode_frozen:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen y i.
    i < N ∧ i ∉ A ⇒
    EL i (sc_decode W N A u_frozen y) = EL i u_frozen
Proof
  simp[EL_sc_decode]
QED

(* Prefix congruence of sc_decode_prefix when two frozen vectors agree outside A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_prefix_frozen_cong[local]:
  ∀(W : (bool, β) memoryless_channel) N A u_f1 u_f2 y k.
    k ≤ N ∧ (∀i. i < N ∧ i ∉ A ⇒ EL i u_f1 = EL i u_f2) ⇒
    sc_decode_prefix W N A u_f1 y k = sc_decode_prefix W N A u_f2 y k
Proof
  Induct_on ‘k’ >- simp[] >>
  rpt strip_tac >>
  ‘k ≤ N ∧ k < N’ by decide_tac >>
  ‘sc_decode_prefix W N A u_f1 y k = sc_decode_prefix W N A u_f2 y k’
    by (first_x_assum irule >> simp[]) >>
  simp[sc_decode_prefix_SUC] >>
  Cases_on ‘k ∈ A’ >> simp[]
QED

(* Congruence of sc_decode: sc_decode depends on u_frozen only at coordinates
   i < N outside A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_frozen_cong:
  ∀(W : (bool, β) memoryless_channel) N A u_f1 u_f2 y.
    (∀i. i < N ∧ i ∉ A ⇒ EL i u_f1 = EL i u_f2) ⇒
    sc_decode W N A u_f1 y = sc_decode W N A u_f2 y
Proof
  rpt strip_tac >>
  simp[sc_decode_eq_prefix] >>
  irule sc_decode_prefix_frozen_cong >>
  simp[]
QED

(* Deterministic tie-breaking likelihood inequality: if sc_bit_decision differs
   from b, then W_N^{(i)}(y, u_prev | b) <= W_N^{(i)}(y, u_prev | ~b).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_bit_decision_neq_imp_le:
  ∀(W : (bool, β) memoryless_channel) N i y u_prev b.
    sc_bit_decision W N i y u_prev ≠ b ⇒
    mcchannel (split_channel W N i) b {(y, u_prev)} ≤
    mcchannel (split_channel W N i) (¬b) {(y, u_prev)}
Proof
  rpt gen_tac >> Cases_on ‘b’ >> simp[sc_bit_decision_def] >>
  metis_tac[le_total]
QED

(* First-error decomposition of SC block error (Erdal Arıkan, 2009, Eqs. 51-52).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_neq_first_error:
  ∀(W : (bool, β) memoryless_channel) N A u y.
    LENGTH u = N ∧ sc_decode W N A u y ≠ u ⇒
    ∃i. i < N ∧ i ∈ A ∧
        TAKE i (sc_decode W N A u y) = TAKE i u ∧
        sc_bit_decision W N i y (TAKE i u) ≠ EL i u ∧
        mcchannel (split_channel W N i) (EL i u) {(y, TAKE i u)} ≤
        mcchannel (split_channel W N i) (¬EL i u) {(y, TAKE i u)}
Proof
  rpt strip_tac >>
  qabbrev_tac ‘uhat = sc_decode W N A u y’ >>
  ‘LENGTH uhat = N’ by simp[Abbr ‘uhat’] >>
  ‘∃j. j < N ∧ EL j uhat ≠ EL j u’
    by (CCONTR_TAC >>
        ‘uhat = u’
          by (irule LIST_EQ >> simp[] >> qx_gen_tac ‘k’ >> strip_tac >>
              fs[] >> first_x_assum (qspec_then ‘k’ mp_tac) >> simp[]) >>
        gvs[]) >>
  qabbrev_tac ‘i = LEAST j. j < N ∧ EL j uhat ≠ EL j u’ >>
  ‘(i < N ∧ EL i uhat ≠ EL i u) ∧
   ∀k. k < i ⇒ ¬(k < N ∧ EL k uhat ≠ EL k u)’
    by (simp[Abbr ‘i’] >> numLib.LEAST_ELIM_TAC >>
        conj_tac >- (qexists_tac ‘j’ >> simp[]) >>
        simp[]) >>
  ‘TAKE i uhat = TAKE i u’
    by (irule LIST_EQ >> simp[LENGTH_TAKE] >>
        qx_gen_tac ‘k’ >> strip_tac >>
        ‘k < N’ by decide_tac >>
        simp[EL_TAKE] >>
        first_x_assum (qspec_then ‘k’ mp_tac) >> simp[]) >>
  ‘EL i uhat = (if i ∈ A then sc_bit_decision W N i y (TAKE i uhat) else EL i u)’
    by simp[Abbr ‘uhat’, EL_sc_decode] >>
  ‘i ∈ A’ by (CCONTR_TAC >> gvs[]) >>
  ‘sc_bit_decision W N i y (TAKE i u) ≠ EL i u’ by gvs[] >>
  qexists_tac ‘i’ >> simp[] >>
  irule sc_bit_decision_neq_imp_le >> simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Block 2: G_N-Coset Codeword Assembly, Coset Bijections & Cardinalities    *)
(* ------------------------------------------------------------------------- *)

(* Set of length-N source vectors u agreeing with u_frozen on all frozen
   coordinates i in count N DIFF A (Erdal Arıkan, 2009, Section I-C.1, p. 4).

   Written by Gemini (Google DeepMind AI agent) *)
Definition coset_source_vectors_def:
  coset_source_vectors (N : num) (A : num -> bool) (u_frozen : bool list)
    : (bool list) -> bool =
    {u | LENGTH u = N ∧ ∀i. i < N ∧ i ∉ A ⇒ EL i u = EL i u_frozen}
End

(* Set of canonical length-N frozen-bit configurations (fixing coordinates in
   A to F so there are exactly 2^{|count N DIFF A|} distinct configurations,
   bijective with X^{N-K}).

   Written by Gemini (Google DeepMind AI agent) *)
Definition frozen_configs_def:
  frozen_configs (N : num) (A : num -> bool) : (bool list) -> bool =
    {u_f | LENGTH u_f = N ∧ ∀i. i < N ∧ i ∈ A ⇒ EL i u_f = F}
End

(* Projection of any length-N bit-vector u onto its canonical frozen
   configuration in frozen_configs N A (zeroing coordinates in A to F).

   Written by Gemini (Google DeepMind AI agent) *)
Definition project_frozen_def:
  project_frozen (N : num) (A : num -> bool) (u : bool list) : bool list =
    GENLIST (λi. if i ∈ A then F else EL i u) N
End

(* Explicit coordinate-wise assembly of length-N source vector u from a K-bit
   information vector u_info (placed at sorted indices of A INTER count N) and
   frozen vector u_frozen (placed at count N DIFF A).

   Written by Gemini (Google DeepMind AI agent) *)
Definition assemble_source_vector_def:
  assemble_source_vector (N : num) (A : num -> bool)
    (u_info : bool list) (u_frozen : bool list) : bool list =
    GENLIST (λi. if i ∈ A then EL (CARD (A ∩ count i)) u_info
                 else EL i u_frozen) N
End

(* Extraction of the K information bits of u at indices in A INTER count N in
   ascending coordinate order.

   Written by Gemini (Google DeepMind AI agent) *)
Definition extract_info_bits_def:
  extract_info_bits (N : num) (A : num -> bool) (u : bool list) : bool list =
    MAP (λi. EL i u) (FILTER (λi. i ∈ A) (GENLIST I N))
End

(* G_N-coset polar encoder x_1^N = u_1^N G_N from Erdal Arıkan (2009),
   Section I-C Eq. (9), p. 4.

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_coset_encode_def:
  polar_coset_encode (N : num) (A : num -> bool)
    (u_info : bool list) (u_frozen : bool list) : bool list =
    polar_encode (assemble_source_vector N A u_info u_frozen)
End

(* Block error probability P_e(N, K, A, u_{A^c}) for a fixed frozen-bit vector
   u_frozen under SC decoding with uniform information bits on A INTER count N
   (Erdal Arıkan, 2009, Section I-C.3, p. 4).

   Written by Gemini (Google DeepMind AI agent) *)
Definition block_error_prob_fixed_def:
  block_error_prob_fixed (W : (bool, β) memoryless_channel) (N : num)
    (A : num -> bool) (u_frozen : bool list) : extreal =
    (1 / 2 pow CARD (A ∩ count N)) *
    ∑ (λu. ∑ (λy. if sc_decode W N A u_frozen y ≠ u then
                    mcchannel (combine_channel W N) u {y}
                  else 0)
             (cross_list (REPLICATE N (mccodomain W))))
      (coset_source_vectors N A u_frozen)
End

(* Ensemble-averaged block error probability P_e(N, K, A), defined as the
   uniform average of block_error_prob_fixed W N A u_frozen over all 2^{N-K}
   frozen configurations u_frozen in frozen_configs N A (Erdal Arıkan, 2009,
   Section I-C.3 Eq. (13), p. 4 & Section V-A Eqs. (47)-(50), p. 10).

   Written by Gemini (Google DeepMind AI agent) *)
Definition block_error_prob_avg_def:
  block_error_prob_avg (W : (bool, β) memoryless_channel) (N : num)
    (A : num -> bool) : extreal =
    (1 / 2 pow CARD (count N DIFF A)) *
    ∑ (λu_frozen. block_error_prob_fixed W N A u_frozen)
      (frozen_configs N A)
End

(* Local coordinatewise splice combining u_f outside A with u_a on A.

   Written by Gemini (Google DeepMind AI agent) *)
Definition splice_vectors_def[local]:
  splice_vectors N A (u_f : bool list) (u_a : bool list) : bool list =
    GENLIST (λi. if i ∈ A then EL i u_a else EL i u_f) N
End

(* Partition of count N into active indices A INTER count N and frozen indices
   count N DIFF A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_inter_plus_diff_count:
  ∀N A. CARD (A ∩ count N) + CARD (count N DIFF A) = N
Proof
  rpt gen_tac >>
  ‘CARD (count N DIFF A) = N - CARD (count N ∩ A)’
    by simp[CARD_DIFF_EQN] >>
  ‘count N ∩ A = A ∩ count N’ by simp[INTER_COMM] >>
  ‘CARD (A ∩ count N) ≤ CARD (count N)’
    by (irule CARD_SUBSET >> simp[]) >>
  gvs[]
QED

(* Inclusion of coset_source_vectors N A u_frozen in length_n_codes N.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem coset_source_vectors_SUBSET:
  ∀N A u_frozen. coset_source_vectors N A u_frozen ⊆ length_n_codes N
Proof
  simp[SUBSET_DEF, coset_source_vectors_def]
QED

(* Finiteness of coset_source_vectors N A u_frozen.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem FINITE_coset_source_vectors[simp]:
  ∀N A u_frozen. FINITE (coset_source_vectors N A u_frozen)
Proof
  rpt gen_tac >>
  irule SUBSET_FINITE >>
  qexists_tac ‘length_n_codes N’ >>
  simp[coset_source_vectors_SUBSET]
QED

(* Expressing frozen_configs N A as coset_source_vectors relative to count N DIFF A
   and REPLICATE N F.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem frozen_configs_alt_coset:
  ∀N A. frozen_configs N A =
          coset_source_vectors N (count N DIFF A) (REPLICATE N F)
Proof
  rpt gen_tac >>
  simp[EXTENSION, frozen_configs_def, coset_source_vectors_def] >>
  gen_tac >> EQ_TAC >> strip_tac >> simp[EL_REPLICATE] >>
  rpt strip_tac >> gvs[EL_REPLICATE]
QED

(* Finiteness of frozen_configs N A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem FINITE_frozen_configs[simp]:
  ∀N A. FINITE (frozen_configs N A)
Proof
  simp[frozen_configs_alt_coset]
QED

(* The all-zero vector REPLICATE N F belongs to frozen_configs N A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REPLICATE_F_IN_frozen_configs:
  ∀N A. REPLICATE N F ∈ frozen_configs N A
Proof
  simp[frozen_configs_def, EL_REPLICATE]
QED

(* Non-emptiness of frozen_configs N A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem frozen_configs_nonempty[simp]:
  ∀N A. frozen_configs N A ≠ ∅
Proof
  rpt gen_tac >> simp[Once EXTENSION] >>
  qexists_tac ‘REPLICATE N F’ >>
  simp[REPLICATE_F_IN_frozen_configs]
QED

(* Bijection from canonical information configurations frozen_configs N (count N DIFF A)
   onto coset_source_vectors N A u_f.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem BIJ_frozen_to_coset:
  ∀N A u_f.
    BIJ (splice_vectors N A u_f)
        (frozen_configs N (count N DIFF A))
        (coset_source_vectors N A u_f)
Proof
  rpt gen_tac >>
  rw[BIJ_IFF_INV]
  >- (simp[splice_vectors_def, coset_source_vectors_def]) >>
  qexists_tac ‘project_frozen N (count N DIFF A)’ >>
  rpt conj_tac
  >- (rw[project_frozen_def, frozen_configs_def])
  >- (rw[frozen_configs_def, splice_vectors_def, project_frozen_def] >>
      irule LIST_EQ >> simp[] >> qx_gen_tac ‘i’ >> strip_tac >>
      Cases_on ‘i ∈ A’ >> simp[])
  >- (rw[coset_source_vectors_def, splice_vectors_def, project_frozen_def] >>
      irule LIST_EQ >> simp[] >> qx_gen_tac ‘i’ >> strip_tac >>
      Cases_on ‘i ∈ A’ >> simp[])
QED

(* Bijection between (u_f, u_a) in frozen_configs N A x frozen_configs N (count N DIFF A)
   and all length-N bit vectors length_n_codes N.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem BIJ_frozen_cross_to_length_n_codes:
  ∀N A.
    BIJ (λ(u_f, u_a). splice_vectors N A u_f u_a)
        (frozen_configs N A × frozen_configs N (count N DIFF A))
        (length_n_codes N)
Proof
  rpt gen_tac >>
  rw[BIJ_IFF_INV, FORALL_PROD]
  >- (simp[splice_vectors_def]) >>
  qexists_tac ‘λu. (project_frozen N A u, project_frozen N (count N DIFF A) u)’ >>
  rpt conj_tac
  >- (rw[project_frozen_def, frozen_configs_def])
  >- (simp[FORALL_PROD] >>
      qx_genl_tac [‘u_f’, ‘u_a’] >>
      rw[frozen_configs_def, splice_vectors_def, project_frozen_def] >>
      irule LIST_EQ >> simp[] >> qx_gen_tac ‘i’ >> strip_tac >>
      Cases_on ‘i ∈ A’ >> simp[])
  >- (qx_gen_tac ‘u’ >>
      rw[splice_vectors_def, project_frozen_def] >>
      irule LIST_EQ >> simp[] >> qx_gen_tac ‘i’ >> strip_tac >>
      Cases_on ‘i ∈ A’ >> simp[])
QED

(* Exact cardinality 2 ** CARD (count N DIFF A) of frozen_configs N A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_frozen_configs:
  ∀N A. CARD (frozen_configs N A) = 2 ** CARD (count N DIFF A)
Proof
  Induct_on ‘N’
  >- (gen_tac >>
      ‘frozen_configs 0 A = {[]}’
        by (simp[frozen_configs_def, EXTENSION] >> Cases >> simp[]) >>
      ‘count 0 DIFF A = ∅’ by simp[EXTENSION] >>
      simp[]) >>
  gen_tac >>
  Cases_on ‘N ∈ A’
  >- (‘count (SUC N) DIFF A = count N DIFF A’
        by (simp[EXTENSION] >> qx_gen_tac ‘x’ >>
            Cases_on ‘x = N’ >> gvs[] >>
            EQ_TAC >> strip_tac >> simp[] >> decide_tac) >>
      ‘BIJ (λu. u ++ [F]) (frozen_configs N A) (frozen_configs (SUC N) A)’
        by (simp[BIJ_IFF_INV] >> conj_tac
            >- (qx_gen_tac ‘u’ >> strip_tac >> fs[frozen_configs_def] >>
                qx_gen_tac ‘i’ >> strip_tac >>
                ‘i ≤ LENGTH u’ by decide_tac >>
                simp[el_append_sing] >> Cases_on ‘i < LENGTH u’ >> simp[])
            >- (qexists_tac ‘TAKE N’ >> rpt conj_tac
                >- (qx_gen_tac ‘v’ >> strip_tac >> fs[frozen_configs_def] >>
                    simp[LENGTH_TAKE, EL_TAKE])
                >- (qx_gen_tac ‘v’ >> strip_tac >> fs[frozen_configs_def] >>
                    simp[TAKE_APPEND1, TAKE_LENGTH_ID])
                >- (qx_gen_tac ‘v’ >> strip_tac >> fs[frozen_configs_def] >>
                    irule LIST_EQ >> simp[LENGTH_TAKE] >>
                    qx_gen_tac ‘i’ >> strip_tac >>
                    ‘i ≤ N’ by decide_tac >>
                    simp[el_append_sing, LENGTH_TAKE] >>
                    Cases_on ‘i < N’ >- simp[EL_TAKE] >>
                    ‘i = N’ by decide_tac >> gvs[]))) >>
      qspecl_then [‘λ(u : bool list). u ++ [F]’,
                   ‘frozen_configs N A’,
                   ‘frozen_configs (SUC N) A’] mp_tac FINITE_BIJ_CARD >>
      simp[])
  >- (‘count (SUC N) DIFF A = N INSERT (count N DIFF A)’
        by (simp[EXTENSION] >> qx_gen_tac ‘x’ >>
            Cases_on ‘x = N’ >> gvs[] >>
            EQ_TAC >> strip_tac >> simp[] >> decide_tac) >>
      ‘N ∉ count N DIFF A ∧ FINITE (count N DIFF A)’ by simp[] >>
      ‘CARD (count (SUC N) DIFF A) = SUC (CARD (count N DIFF A))’
        by simp[] >>
      ‘BIJ (λ(u, b). u ++ [b])
           (frozen_configs N A × 𝕌(:bool))
           (frozen_configs (SUC N) A)’
        by (rw[BIJ_IFF_INV, FORALL_PROD]
            >- (fs[frozen_configs_def] >> qx_gen_tac ‘i’ >> strip_tac >>
                ‘i ≠ N’ by metis_tac[] >>
                ‘i < LENGTH p_1 ∧ i ≤ LENGTH p_1’ by decide_tac >>
                simp[el_append_sing])
            >- (qexists_tac ‘λv. (TAKE N v, EL N v)’ >>
                rpt conj_tac
                >- (qx_gen_tac ‘v’ >> strip_tac >> fs[frozen_configs_def] >>
                    simp[LENGTH_TAKE, EL_TAKE])
                >- (simp[FORALL_PROD] >> qx_genl_tac [‘u’, ‘b’] >>
                    strip_tac >> fs[frozen_configs_def] >>
                    conj_tac
                    >- simp[TAKE_APPEND1, TAKE_LENGTH_ID]
                    >- (‘LENGTH u ≤ LENGTH u’ by decide_tac >>
                        drule_then (qspec_then ‘b’ mp_tac) el_append_sing >>
                        simp[]))
                >- (qx_gen_tac ‘v’ >> strip_tac >> fs[frozen_configs_def] >>
                    irule LIST_EQ >> simp[LENGTH_TAKE] >>
                    qx_gen_tac ‘i’ >> strip_tac >>
                    ‘i ≤ N’ by decide_tac >>
                    simp[el_append_sing, LENGTH_TAKE] >>
                    Cases_on ‘i < N’ >- simp[EL_TAKE] >>
                    ‘i = N’ by decide_tac >> gvs[]))) >>
      qspecl_then [‘λ(u : bool list, b : bool). u ++ [b]’,
                   ‘frozen_configs N A × 𝕌(:bool)’,
                   ‘frozen_configs (SUC N) A’] mp_tac FINITE_BIJ_CARD >>
      ‘CARD (𝕌(:bool)) = 2’
        by simp[UNIV_BOOL, DELETE_NON_ELEMENT_RWT] >>
      simp[FINITE_CROSS, CARD_CROSS, EXP])
QED

(* Exact cardinality 2 ** CARD (A INTER count N) of coset_source_vectors N A u_f.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_coset_source_vectors:
  ∀N A u_f.
    CARD (coset_source_vectors N A u_f) = 2 ** CARD (A ∩ count N)
Proof
  rpt gen_tac >>
  qspecl_then [‘splice_vectors N A u_f’,
               ‘frozen_configs N (count N DIFF A)’,
               ‘coset_source_vectors N A u_f’] mp_tac FINITE_BIJ_CARD >>
  simp[BIJ_frozen_to_coset] >>
  disch_then (SUBST1_TAC o SYM) >>
  simp[CARD_frozen_configs] >>
  ‘N - CARD (count N DIFF A) = CARD (A ∩ count N)’
    by (qspecl_then [‘N’, ‘A’] mp_tac CARD_inter_plus_diff_count >>
        decide_tac) >>
  simp[]
QED

(* Surjectivity of coordinate rank r = CARD (A INTER count i) onto count (CARD (A INTER count N)).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem rank_in_inter_count_surj[local]:
  ∀N A r.
    r < CARD (A ∩ count N) ⇒
    ∃i. i < N ∧ i ∈ A ∧ CARD (A ∩ count i) = r
Proof
  Induct_on ‘N’
  >- (‘∀A. A ∩ count 0 = ∅’ by simp[EXTENSION] >> simp[]) >>
  rpt strip_tac >>
  Cases_on ‘N ∈ A’
  >- (‘A ∩ count (SUC N) = N INSERT (A ∩ count N)’
        by (simp[EXTENSION] >> qx_gen_tac ‘x’ >>
            Cases_on ‘x = N’ >> gvs[] >>
            EQ_TAC >> strip_tac >> simp[] >> decide_tac) >>
      ‘FINITE (A ∩ count N)’
        by (irule SUBSET_FINITE >> qexists_tac ‘count N’ >> simp[SUBSET_DEF]) >>
      ‘N ∉ A ∩ count N’ by simp[] >>
      ‘CARD (A ∩ count (SUC N)) = SUC (CARD (A ∩ count N))’ by simp[] >>
      Cases_on ‘r < CARD (A ∩ count N)’
      >- (first_x_assum (drule_then strip_assume_tac) >>
          qexists_tac ‘i’ >> simp[])
      >- (‘r = CARD (A ∩ count N)’ by decide_tac >>
          qexists_tac ‘N’ >> simp[]))
  >- (‘A ∩ count (SUC N) = A ∩ count N’
        by (simp[EXTENSION] >> qx_gen_tac ‘x’ >>
            Cases_on ‘x = N’ >> gvs[] >>
            EQ_TAC >> strip_tac >> simp[] >> decide_tac) >>
      gvs[] >>
      first_x_assum (drule_then strip_assume_tac) >>
      qexists_tac ‘i’ >> simp[])
QED

(* Bijection of K-bit message assembly assemble_source_vector N A onto
   coset_source_vectors N A u_frozen.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem BIJ_assemble_source_vector:
  ∀N A u_frozen.
    BIJ (λu_info. assemble_source_vector N A u_info u_frozen)
        (length_n_codes (CARD (A ∩ count N)))
        (coset_source_vectors N A u_frozen)
Proof
  rpt gen_tac >>
  qabbrev_tac ‘K_a = CARD (A ∩ count N)’ >>
  qabbrev_tac ‘f = λ(u_info : bool list). assemble_source_vector N A u_info u_frozen’ >>
  ‘INJ f (length_n_codes K_a) (coset_source_vectors N A u_frozen)’
    by (simp[INJ_DEF] >> conj_tac
        >- rw[Abbr ‘f’, assemble_source_vector_def, coset_source_vectors_def]
        >- (qx_genl_tac [‘x’, ‘y’] >> rpt strip_tac >>
            irule LIST_EQ >> fs[Abbr ‘K_a’] >>
            qx_gen_tac ‘r’ >> strip_tac >>
            drule rank_in_inter_count_surj >> strip_tac >>
            ‘EL i (f x) = EL i (f y)’ by simp[] >>
            qpat_x_assum ‘f x = f y’ kall_tac >>
            fs[Abbr ‘f’, assemble_source_vector_def] >>
            rfs[])) >>
  ‘FINITE (length_n_codes K_a) ∧
   FINITE (coset_source_vectors N A u_frozen) ∧
   CARD (length_n_codes K_a) = CARD (coset_source_vectors N A u_frozen)’
    by simp[Abbr ‘K_a’, CARD_coset_source_vectors] >>
  ‘IMAGE f (length_n_codes K_a) ⊆ coset_source_vectors N A u_frozen’
    by (fs[INJ_DEF, SUBSET_DEF] >> metis_tac[]) >>
  ‘CARD (IMAGE f (length_n_codes K_a)) = CARD (length_n_codes K_a)’
    by (drule_all INJ_CARD_IMAGE_EQ >> simp[]) >>
  ‘IMAGE f (length_n_codes K_a) = coset_source_vectors N A u_frozen’
    by (irule SUBSET_EQ_CARD >> simp[]) >>
  fs[BIJ_DEF, SURJ_DEF, IN_IMAGE] >>
  conj_tac >- (fs[INJ_DEF]) >>
  qx_gen_tac ‘u’ >> strip_tac >>
  ‘u ∈ IMAGE f (length_n_codes K_a)’ by metis_tac[] >>
  fs[IN_IMAGE] >> metis_tac[]
QED

(* Output length N of polar_coset_encode N A u_info u_frozen.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_coset_encode_length[simp]:
  ∀N A u_info u_frozen.
    LENGTH (polar_coset_encode N A u_info u_frozen) = N
Proof
  simp[polar_coset_encode_def, assemble_source_vector_def,
       polar_encode_length_any]
QED

(* ------------------------------------------------------------------------- *)
(* Block 3: Block Error Probabilities — Normal Bounds & Averaging Identities *)
(* ------------------------------------------------------------------------- *)

(* Normalization of 2 ** k and 1 / 2 pow k across num, real, and extreal.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem part1_two_pow_props[local]:
  ∀k. (&(2 ** k) : real) = (2 : real) pow k ∧
      (0 : real) < (2 : real) pow k ∧
      (2 : real) pow k ≠ 0 ∧
      0 ≤ (1 / (2 : real) pow k) ∧
      ((2 : extreal) pow k = Normal ((2 : real) pow k)) ∧
      (((1 / 2 pow k) : extreal) = Normal (1 / (2 : real) pow k)) ∧
      (&(2 ** k) : real) * (1 / (2 : real) pow k) = 1 ∧
      (1 / (2 : real) pow k) * &(2 ** k) = 1
Proof
  gen_tac >>
  ‘(&(2 ** k) : real) = (2 : real) pow k’
    by simp[GSYM REAL_OF_NUM_POW] >>
  ‘(0 : real) < (2 : real) pow k’
    by (irule REAL_POW_LT >> REAL_ARITH_TAC) >>
  ‘(2 : real) pow k ≠ 0’ by REAL_ASM_ARITH_TAC >>
  ‘0 ≤ (1 / (2 : real) pow k)’
    by (simp[real_div, REAL_LE_INV_EQ] >> REAL_ASM_ARITH_TAC) >>
  simp[extreal_of_num_def, extreal_pow_def, extreal_div_eq, real_div,
       REAL_MUL_RINV, REAL_MUL_LINV]
QED

(* Congruence of block_error_prob_fixed across frozen vectors agreeing outside A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_fixed_frozen_cong:
  ∀(W : (bool, β) memoryless_channel) N A u_f1 u_f2.
    (∀i. i < N ∧ i ∉ A ⇒ EL i u_f1 = EL i u_f2) ⇒
    block_error_prob_fixed W N A u_f1 = block_error_prob_fixed W N A u_f2
Proof
  rpt strip_tac >>
  ‘coset_source_vectors N A u_f1 = coset_source_vectors N A u_f2’
    by (simp[EXTENSION, coset_source_vectors_def] >> gen_tac >>
        EQ_TAC >> strip_tac >> simp[] >> metis_tac[]) >>
  ‘∀y. sc_decode W N A u_f1 y = sc_decode W N A u_f2 y’
    by (gen_tac >> irule sc_decode_frozen_cong >> simp[]) >>
  simp[block_error_prob_fixed_def]
QED

(* Explicit Normal real representation of block_error_prob_fixed W N A u_frozen
   for any well-formed B-DMC W and general block-length N.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_fixed_real_sum:
  ∀(W : (bool, β) memoryless_channel) N A u_frozen.
    wf_bdmc W ⇒
    block_error_prob_fixed W N A u_frozen =
      Normal
        ((1 / (2 : real) pow CARD (A ∩ count N)) *
         REAL_SUM_IMAGE
           (λu. REAL_SUM_IMAGE
                  (λy. if sc_decode W N A u y ≠ u then
                         real (mcchannel (combine_channel W N) u {y})
                       else 0)
                  (cross_list (REPLICATE N (mccodomain W))))
           (coset_source_vectors N A u_frozen))
Proof
  rpt strip_tac >>
  simp[block_error_prob_fixed_def] >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  ‘∑ (λu. ∑ (λy. if sc_decode W N A u_frozen y ≠ u then
                   mcchannel (combine_channel W N) u {y}
                 else 0) Y_N)
     (coset_source_vectors N A u_frozen) =
   ∑ (λu. Normal
            (REAL_SUM_IMAGE
               (λy. if sc_decode W N A u y ≠ u then
                      real (mcchannel (combine_channel W N) u {y})
                    else 0) Y_N))
     (coset_source_vectors N A u_frozen)’
    by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
        qx_gen_tac ‘u’ >> strip_tac >>
        ‘LENGTH u = N ∧ ∀i. i < N ∧ i ∉ A ⇒ EL i u = EL i u_frozen’
          by fs[coset_source_vectors_def] >>
        ‘∀y. sc_decode W N A u_frozen y = sc_decode W N A u y’
          by (gen_tac >> irule sc_decode_frozen_cong >> metis_tac[]) >>
        ‘∑ (λy. if sc_decode W N A u_frozen y ≠ u then
                  mcchannel (combine_channel W N) u {y}
                else 0) Y_N =
         ∑ (λy. Normal (if sc_decode W N A u y ≠ u then
                          real (mcchannel (combine_channel W N) u {y})
                        else 0)) Y_N’
          by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
              qx_gen_tac ‘y’ >> strip_tac >>
              Cases_on ‘sc_decode W N A u y ≠ u’ >>
              simp[extreal_of_num_def] >>
              ‘LENGTH y = N ∧ EVERY (λyi. yi ∈ mccodomain W) y’
                by fs[Abbr ‘Y_N’, in_cross_list_replicate] >>
              drule_all mcchannel_combine_channel_singleton_normal_gen >>
              strip_tac >> simp[real_normal]) >>
        pop_assum SUBST1_TAC >>
        simp[EXTREAL_SUM_IMAGE_NORMAL]) >>
  pop_assum SUBST1_TAC >>
  simp[EXTREAL_SUM_IMAGE_NORMAL, part1_two_pow_props, extreal_mul_eq]
QED

(* Non-negativity and Normal representation of block_error_prob_fixed W N A uf
   (seam theorem for Proposition 2).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_fixed_normal:
  ∀(W : (bool, β) memoryless_channel) N A uf.
    wf_bdmc W ⇒
    0 ≤ real (block_error_prob_fixed W N A uf) ∧
    block_error_prob_fixed W N A uf =
      Normal (real (block_error_prob_fixed W N A uf))
Proof
  rpt gen_tac >> strip_tac >>
  drule block_error_prob_fixed_real_sum >>
  disch_then (qspecl_then [‘N’, ‘A’, ‘uf’] SUBST1_TAC) >>
  REWRITE_TAC[real_normal] >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  irule REAL_LE_MUL >>
  conj_tac >- simp[part1_two_pow_props] >>
  irule REAL_SUM_IMAGE_POS >> simp[] >>
  qx_gen_tac ‘u’ >> strip_tac >>
  irule REAL_SUM_IMAGE_POS >> simp[] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  Cases_on ‘sc_decode W N A u y ≠ u’ >> simp[] >>
  ‘LENGTH u = N’ by fs[coset_source_vectors_def] >>
  ‘LENGTH y = N ∧ EVERY (λyi. yi ∈ mccodomain W) y’
    by fs[Abbr ‘Y_N’, in_cross_list_replicate] >>
  qspecl_then [‘W’, ‘N’, ‘u’, ‘y’] mp_tac
    mcchannel_combine_channel_singleton_normal_gen >>
  simp[] >> strip_tac >> simp[real_normal]
QED

(* General-N Normal real-sum representation of ensemble-averaged block error
   probability over all joint (u, y) pairs.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_avg_real_sum_gen:
  ∀(W : (bool, β) memoryless_channel) N A.
    wf_bdmc W ⇒
    block_error_prob_avg W N A =
      Normal
        ((1 / (2 : real) pow N) *
         REAL_SUM_IMAGE
           (λu. REAL_SUM_IMAGE
                  (λy. if sc_decode W N A u y ≠ u
                       then real (mcchannel (combine_channel W N) u {y})
                       else 0)
                  (cross_list (REPLICATE N (mccodomain W))))
           (length_n_codes N))
Proof
  rpt strip_tac >>
  simp[block_error_prob_avg_def] >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  qabbrev_tac ‘K_a = CARD (A ∩ count N)’ >>
  qabbrev_tac ‘M_a = CARD (count N DIFF A)’ >>
  qabbrev_tac ‘err_u = λ(u : bool list).
                         REAL_SUM_IMAGE
                           (λy. if sc_decode W N A u y ≠ u
                                then real (mcchannel (combine_channel W N) u {y})
                                else 0) Y_N’ >>
  ‘∑ (λu_frozen. block_error_prob_fixed W N A u_frozen) (frozen_configs N A) =
   ∑ (λu_frozen.
        Normal ((1 / (2 : real) pow K_a) *
                REAL_SUM_IMAGE
                  (λu_a. err_u (splice_vectors N A u_frozen u_a))
                  (frozen_configs N (count N DIFF A))))
     (frozen_configs N A)’
    by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
        qx_gen_tac ‘u_f’ >> strip_tac >>
        drule block_error_prob_fixed_real_sum >>
        disch_then (qspecl_then [‘N’, ‘A’, ‘u_f’] SUBST1_TAC) >>
        qspecl_then [‘frozen_configs N (count N DIFF A)’,
                     ‘coset_source_vectors N A u_f’,
                     ‘splice_vectors N A u_f’,
                     ‘λ(u : bool list).
                        REAL_SUM_IMAGE
                          (λy. if sc_decode W N A u y ≠ u
                               then real (mcchannel (combine_channel W N) u {y})
                               else 0)
                          (cross_list (REPLICATE N (mccodomain W)))’]
          mp_tac REAL_SUM_IMAGE_BIJ >>
        simp[BIJ_frozen_to_coset, o_DEF] >>
        disch_then SUBST1_TAC >>
        simp[Abbr ‘K_a’, Abbr ‘err_u’, Abbr ‘Y_N’]) >>
  pop_assum SUBST1_TAC >>
  simp[EXTREAL_SUM_IMAGE_NORMAL, part1_two_pow_props, extreal_mul_eq,
       REAL_SUM_IMAGE_CMUL] >>
  ‘REAL_SUM_IMAGE err_u (length_n_codes N) =
   REAL_SUM_IMAGE
     (λu_f. REAL_SUM_IMAGE
              (λu_a. err_u (splice_vectors N A u_f u_a))
              (frozen_configs N (count N DIFF A)))
     (frozen_configs N A)’
    by (qspecl_then [‘frozen_configs N A × frozen_configs N (count N DIFF A)’,
                     ‘length_n_codes N’,
                     ‘λ(u_f : bool list, u_a : bool list). splice_vectors N A u_f u_a’,
                     ‘err_u : bool list -> real’]
          mp_tac REAL_SUM_IMAGE_BIJ >>
        simp[FINITE_CROSS, BIJ_frozen_cross_to_length_n_codes,
             REAL_SUM_IMAGE_REAL_SUM_IMAGE, o_DEF] >>
        disch_then SUBST1_TAC >>
        irule REAL_SUM_IMAGE_EQ >> simp[FINITE_CROSS, FORALL_PROD]) >>
  pop_assum (SUBST1_TAC o SYM) >>
  ‘K_a + M_a = N’ by simp[Abbr ‘K_a’, Abbr ‘M_a’, CARD_inter_plus_diff_count] >>
  ‘(2 : real) pow N = (2 : real) pow M_a * (2 : real) pow K_a’
    by (‘N = M_a + K_a’ by decide_tac >>
        pop_assum SUBST1_TAC >> simp[POW_ADD]) >>
  simp[part1_two_pow_props, real_div, REAL_INV_MUL, REAL_MUL_ASSOC]
QED

(* Ensemble-average real-sum representation under A SUBSET count N
   (exact seam theorem expected by Proposition 2).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_avg_real_sum:
  ∀(W : (bool, β) memoryless_channel) N A.
    wf_bdmc W ∧ A ⊆ count N ⇒
    block_error_prob_avg W N A =
      Normal
        ((1 / (2 : real) pow N) *
         REAL_SUM_IMAGE
           (λu. REAL_SUM_IMAGE
                  (λy. if sc_decode W N A u y ≠ u
                       then real (mcchannel (combine_channel W N) u {y})
                       else 0)
                  (cross_list (REPLICATE N (mccodomain W))))
           (length_n_codes N))
Proof
  rw[block_error_prob_avg_real_sum_gen]
QED

(* Equivalence of block_error_prob_avg W N A with the uniform mean of
   block_error_prob_fixed W N A uf over all 2^N vectors uf in length_n_codes N
   (exact seam theorem expected by Proposition 2).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_avg_eq_mean_fixed:
  ∀(W : (bool, β) memoryless_channel) N A.
    wf_bdmc W ∧ A ⊆ count N ⇒
    block_error_prob_avg W N A =
      Normal ((1 / (2 : real) pow N) *
              REAL_SUM_IMAGE (λuf. real (block_error_prob_fixed W N A uf))
                             (length_n_codes N))
Proof
  rpt strip_tac >>
  simp[block_error_prob_avg_def] >>
  qabbrev_tac ‘K_a = CARD (A ∩ count N)’ >>
  qabbrev_tac ‘M_a = CARD (count N DIFF A)’ >>
  qabbrev_tac ‘g = λ(uf : bool list). real (block_error_prob_fixed W N A uf)’ >>
  ‘K_a + M_a = N’ by simp[Abbr ‘K_a’, Abbr ‘M_a’, CARD_inter_plus_diff_count] >>
  ‘∑ (λu_frozen. block_error_prob_fixed W N A u_frozen) (frozen_configs N A) =
   ∑ (λu_frozen. Normal (g u_frozen)) (frozen_configs N A)’
    by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[Abbr ‘g’] >>
        qx_gen_tac ‘u_f’ >> strip_tac >>
        irule (cj 2 block_error_prob_fixed_normal) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[EXTREAL_SUM_IMAGE_NORMAL, part1_two_pow_props, extreal_mul_eq] >>
  ‘REAL_SUM_IMAGE g (length_n_codes N) =
   REAL_SUM_IMAGE
     (λu_f. REAL_SUM_IMAGE
              (λu_a. g (splice_vectors N A u_f u_a))
              (frozen_configs N (count N DIFF A)))
     (frozen_configs N A)’
    by (qspecl_then [‘frozen_configs N A × frozen_configs N (count N DIFF A)’,
                     ‘length_n_codes N’,
                     ‘λ(u_f : bool list, u_a : bool list). splice_vectors N A u_f u_a’,
                     ‘g : bool list -> real’]
          mp_tac REAL_SUM_IMAGE_BIJ >>
        simp[FINITE_CROSS, BIJ_frozen_cross_to_length_n_codes,
             REAL_SUM_IMAGE_REAL_SUM_IMAGE, o_DEF] >>
        disch_then SUBST1_TAC >>
        irule REAL_SUM_IMAGE_EQ >> simp[FINITE_CROSS, FORALL_PROD]) >>
  ‘REAL_SUM_IMAGE g (length_n_codes N) =
   (&(2 ** K_a) : real) * REAL_SUM_IMAGE g (frozen_configs N A)’
    by (pop_assum SUBST1_TAC >>
        ‘∀u_f. u_f ∈ frozen_configs N A ⇒
               REAL_SUM_IMAGE (λu_a. g (splice_vectors N A u_f u_a))
                              (frozen_configs N (count N DIFF A)) =
               (&(2 ** K_a) : real) * g u_f’
          by (qx_gen_tac ‘u_f’ >> strip_tac >>
              ‘REAL_SUM_IMAGE (λu_a. g (splice_vectors N A u_f u_a))
                              (frozen_configs N (count N DIFF A)) =
               REAL_SUM_IMAGE (λu_a. g u_f)
                              (frozen_configs N (count N DIFF A))’
                by (irule REAL_SUM_IMAGE_EQ >> simp[] >>
                    qx_gen_tac ‘u_a’ >> strip_tac >>
                    simp[Abbr ‘g’] >> AP_TERM_TAC >>
                    irule block_error_prob_fixed_frozen_cong >>
                    simp[splice_vectors_def]) >>
              pop_assum SUBST1_TAC >>
              simp[REAL_SUM_IMAGE_FINITE_CONST3, CARD_frozen_configs] >>
              ‘N - CARD (count N DIFF A) = K_a’
                by (qpat_x_assum ‘K_a + M_a = N’ mp_tac >>
                    simp[Abbr ‘M_a’] >> decide_tac) >>
              simp[]) >>
        irule EQ_TRANS >>
        qexists_tac ‘REAL_SUM_IMAGE (λu_f. (&(2 ** K_a) : real) * g u_f)
                                    (frozen_configs N A)’ >>
        conj_tac
        >- (irule REAL_SUM_IMAGE_EQ >> simp[])
        >- simp[REAL_SUM_IMAGE_CMUL]) >>
  pop_assum SUBST1_TAC >>
  ‘(&(2 ** K_a) : real) = (2 : real) pow K_a ∧
   (2 : real) pow K_a ≠ 0 ∧
   (2 : real) pow M_a ≠ 0’
    by simp[part1_two_pow_props] >>
  ‘(2 : real) pow N = (2 : real) pow M_a * (2 : real) pow K_a’
    by (‘N = M_a + K_a’ by decide_tac >>
        pop_assum SUBST1_TAC >> simp[POW_ADD]) >>
  simp[real_div, REAL_INV_MUL, REAL_MUL_ASSOC] >>
  ‘inv ((2 : real) pow M_a) * inv ((2 : real) pow K_a) * (2 : real) pow K_a =
   inv ((2 : real) pow M_a) * (inv ((2 : real) pow K_a) * (2 : real) pow K_a)’
    by REAL_ARITH_TAC >>
  simp[REAL_MUL_LINV]
QED

(* Extreal joint-sum representation of block_error_prob_avg W (2 ** n) A
   (Erdal Arıkan, 2009, Section V-A Eqs. 47-50).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_avg_eq_joint_sum:
  ∀(W : (bool, β) memoryless_channel) n A.
    wf_bdmc W ⇒
    block_error_prob_avg W (2 ** n) A =
      (1 / 2 pow (2 ** n)) *
      ∑ (λu. ∑ (λy. if sc_decode W (2 ** n) A u y ≠ u then
                      mcchannel (combine_channel W (2 ** n)) u {y}
                    else 0)
               (cross_list (REPLICATE (2 ** n) (mccodomain W))))
        (length_n_codes (2 ** n))
Proof
  rpt strip_tac >>
  drule block_error_prob_avg_real_sum_gen >>
  disch_then (qspecl_then [‘2n ** n’, ‘A’] SUBST1_TAC) >>
  qabbrev_tac ‘N = 2n ** n’ >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  ‘∑ (λu. ∑ (λy. if sc_decode W N A u y ≠ u then
                   mcchannel (combine_channel W N) u {y}
                 else 0) Y_N)
     (length_n_codes N) =
   ∑ (λu. Normal
            (REAL_SUM_IMAGE
               (λy. if sc_decode W N A u y ≠ u then
                      real (mcchannel (combine_channel W N) u {y})
                    else 0) Y_N))
     (length_n_codes N)’
    by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
        qx_gen_tac ‘u’ >> strip_tac >>
        ‘∑ (λy. if sc_decode W N A u y ≠ u then
                  mcchannel (combine_channel W N) u {y}
                else 0) Y_N =
         ∑ (λy. Normal (if sc_decode W N A u y ≠ u then
                          real (mcchannel (combine_channel W N) u {y})
                        else 0)) Y_N’
          by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
              qx_gen_tac ‘y’ >> strip_tac >>
              Cases_on ‘sc_decode W N A u y ≠ u’ >>
              simp[extreal_of_num_def] >>
              ‘LENGTH u = N’ by gvs[] >>
              ‘LENGTH y = N ∧ EVERY (λyi. yi ∈ mccodomain W) y’
                by fs[Abbr ‘Y_N’, in_cross_list_replicate] >>
              qspecl_then [‘W’, ‘N’, ‘u’, ‘y’] mp_tac
                mcchannel_combine_channel_singleton_normal_gen >>
              simp[] >> strip_tac >> simp[real_normal]) >>
        pop_assum SUBST1_TAC >>
        simp[EXTREAL_SUM_IMAGE_NORMAL]) >>
  pop_assum SUBST1_TAC >>
  simp[EXTREAL_SUM_IMAGE_NORMAL, part1_two_pow_props, extreal_mul_eq]
QED

(* Cartesian-product extreal sum representation of block_error_prob_avg W (2 ** n) A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_avg_eq_cross_sum:
  ∀(W : (bool, β) memoryless_channel) n A.
    wf_bdmc W ⇒
    block_error_prob_avg W (2 ** n) A =
      ∑ (λ(u, y). if sc_decode W (2 ** n) A u y ≠ u then
                    (1 / 2 pow (2 ** n)) *
                    mcchannel (combine_channel W (2 ** n)) u {y}
                  else 0)
        (length_n_codes (2 ** n) ×
         cross_list (REPLICATE (2 ** n) (mccodomain W)))
Proof
  rpt strip_tac >>
  drule block_error_prob_avg_real_sum_gen >>
  disch_then (qspecl_then [‘2n ** n’, ‘A’] SUBST1_TAC) >>
  qabbrev_tac ‘N = 2n ** n’ >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  ‘∑ (λ(u, y). if sc_decode W N A u y ≠ u then
                 (1 / 2 pow N) * mcchannel (combine_channel W N) u {y}
               else 0)
     (length_n_codes N × Y_N) =
   ∑ (λp. Normal
            ((1 / (2 : real) pow N) *
             (if sc_decode W N A (FST p) (SND p) ≠ FST p then
                real (mcchannel (combine_channel W N) (FST p) {SND p})
              else 0)))
     (length_n_codes N × Y_N)’
    by (irule EXTREAL_SUM_IMAGE_EQ' >>
        simp[FINITE_CROSS, FORALL_PROD] >>
        qx_genl_tac [‘u’, ‘y’] >> strip_tac >>
        reverse (Cases_on ‘sc_decode W N A u y ≠ u’)
        >- simp[extreal_of_num_def] >>
        simp[] >>
        ‘LENGTH u = N’ by gvs[] >>
        ‘LENGTH y = N ∧ EVERY (λyi. yi ∈ mccodomain W) y’
          by fs[Abbr ‘Y_N’, in_cross_list_replicate] >>
        qspecl_then [‘W’, ‘N’, ‘u’, ‘y’] mp_tac
          mcchannel_combine_channel_singleton_normal_gen >>
        simp[] >> strip_tac >>
        simp[part1_two_pow_props, extreal_mul_eq, real_normal]) >>
  pop_assum SUBST1_TAC >>
  simp[FINITE_CROSS, EXTREAL_SUM_IMAGE_NORMAL, REAL_SUM_IMAGE_CMUL,
       REAL_SUM_IMAGE_REAL_SUM_IMAGE, part1_two_pow_props]
QED

(* Filtered Cartesian-product sum representation of block_error_prob_avg W (2 ** n) A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_avg_eq_filtered_cross_sum:
  ∀(W : (bool, β) memoryless_channel) n A.
    wf_bdmc W ⇒
    block_error_prob_avg W (2 ** n) A =
      ∑ (λ(u, y). (1 / 2 pow (2 ** n)) *
                  mcchannel (combine_channel W (2 ** n)) u {y})
        {(u, y) | u ∈ length_n_codes (2 ** n) ∧
                  y ∈ cross_list (REPLICATE (2 ** n) (mccodomain W)) ∧
                  sc_decode W (2 ** n) A u y ≠ u}
Proof
  rpt strip_tac >>
  drule block_error_prob_avg_eq_cross_sum >>
  disch_then (qspecl_then [‘n’, ‘A’] SUBST1_TAC) >>
  qabbrev_tac ‘N = 2n ** n’ >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE (length_n_codes N × Y_N)’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >>
        simp[FINITE_CROSS, finite_cross_list_replicate]) >>
  ‘{(u, y) | u ∈ length_n_codes N ∧ y ∈ Y_N ∧ sc_decode W N A u y ≠ u} =
   {p | p ∈ length_n_codes N × Y_N ∧
        (λ(u, y). sc_decode W N A u y ≠ u) p}’
    by (simp[EXTENSION, FORALL_PROD, EXISTS_PROD] >>
        qx_genl_tac [‘u’, ‘y’] >>
        simp[GSPECIFICATION, EXISTS_PROD, CONJ_ASSOC]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘length_n_codes N × Y_N’,
               ‘λ(u : bool list, y : β list). sc_decode W N A u y ≠ u’,
               ‘λ(u : bool list, y : β list).
                  (1 / 2 pow N) * mcchannel (combine_channel W N) u {y}’]
    mp_tac EXTREAL_SUM_IMAGE_FILTER >>
  impl_tac
  >- (simp[] >> disj1_tac >> simp[FORALL_PROD] >>
      qx_genl_tac [‘u’, ‘y’] >> strip_tac >>
      ‘LENGTH u = N’ by gvs[] >>
      ‘LENGTH y = N ∧ EVERY (λyi. yi ∈ mccodomain W) y’
        by fs[Abbr ‘Y_N’, in_cross_list_replicate] >>
      qspecl_then [‘W’, ‘N’, ‘u’, ‘y’] mp_tac
        mcchannel_combine_channel_singleton_normal_gen >>
      simp[] >> strip_tac >> simp[part1_two_pow_props, extreal_mul_eq]) >>
  disch_then SUBST1_TAC >>
  irule EXTREAL_SUM_IMAGE_EQ' >>
  simp[FORALL_PROD]
QED

(* Finite real minimizer lemma for exists_frozen_le_block_error_prob_avg.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem part1_finite_exists_min[local]:
  ∀(s : α -> bool).
    FINITE s ⇒ s ≠ ∅ ⇒ ∀(f : α -> real). ∃x0. x0 ∈ s ∧ ∀x. x ∈ s ⇒ f x0 ≤ f x
Proof
  Induct_on ‘FINITE’ >> simp[] >>
  qx_gen_tac ‘s’ >> strip_tac >>
  qx_gen_tac ‘e’ >> strip_tac >> gen_tac >>
  Cases_on ‘s = ∅’
  >- (qexists_tac ‘e’ >> simp[])
  >- (first_x_assum (drule_then (qspec_then ‘f’ strip_assume_tac)) >>
      Cases_on ‘f e ≤ f x0’
      >- (qexists_tac ‘e’ >> simp[] >> qx_gen_tac ‘x’ >> strip_tac >> gvs[] >>
          first_x_assum (drule_then assume_tac) >> REAL_ASM_ARITH_TAC)
      >- (qexists_tac ‘x0’ >> simp[] >> qx_gen_tac ‘x’ >> strip_tac >> gvs[] >>
          first_x_assum (drule_then assume_tac) >> REAL_ASM_ARITH_TAC))
QED

(* Existential fixed-frozen witness achieving fixed-frozen error probability at
   most ensemble-averaged error probability.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem exists_frozen_le_block_error_prob_avg:
  ∀(W : (bool, β) memoryless_channel) n A.
    wf_bdmc W ⇒
    ∃u_frozen.
      LENGTH u_frozen = 2 ** n ∧
      block_error_prob_fixed W (2 ** n) A u_frozen ≤
      block_error_prob_avg W (2 ** n) A
Proof
  rpt strip_tac >>
  qabbrev_tac ‘N = 2n ** n’ >>
  qabbrev_tac ‘S_f = frozen_configs N A’ >>
  qabbrev_tac ‘g = λ(u_f : bool list). real (block_error_prob_fixed W N A u_f)’ >>
  ‘FINITE S_f ∧ S_f ≠ ∅’ by simp[Abbr ‘S_f’] >>
  drule_all part1_finite_exists_min >>
  disch_then (qspec_then ‘g’ strip_assume_tac) >>
  qexists_tac ‘x0’ >>
  ‘LENGTH x0 = N’ by fs[Abbr ‘S_f’, frozen_configs_def] >>
  simp[] >>
  ‘block_error_prob_fixed W N A x0 = Normal (g x0)’
    by (simp[Abbr ‘g’] >> irule (cj 2 block_error_prob_fixed_normal) >> simp[]) >>
  ‘block_error_prob_avg W N A =
   Normal ((1 / (2 : real) pow CARD (count N DIFF A)) *
           REAL_SUM_IMAGE g S_f)’
    by (simp[block_error_prob_avg_def, Abbr ‘S_f’] >>
        ‘∑ (λu_frozen. block_error_prob_fixed W N A u_frozen)
           (frozen_configs N A) =
         ∑ (λu_frozen. Normal (g u_frozen)) (frozen_configs N A)’
          by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[Abbr ‘g’] >>
              qx_gen_tac ‘u_f’ >> strip_tac >>
              irule (cj 2 block_error_prob_fixed_normal) >> simp[]) >>
        pop_assum SUBST1_TAC >>
        simp[EXTREAL_SUM_IMAGE_NORMAL, part1_two_pow_props, extreal_mul_eq]) >>
  pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
  simp[extreal_le_eq] >>
  ‘&(CARD S_f) * g x0 ≤ REAL_SUM_IMAGE g S_f’
    by (‘&(CARD S_f) * g x0 = REAL_SUM_IMAGE (λu_f. g x0) S_f’
          by simp[REAL_SUM_IMAGE_FINITE_CONST3] >>
        pop_assum SUBST1_TAC >>
        qspec_then ‘S_f’ mp_tac REAL_SUM_IMAGE_MONO >>
        simp[]) >>
  ‘CARD S_f = 2 ** CARD (count N DIFF A)’
    by simp[Abbr ‘S_f’, CARD_frozen_configs] >>
  ‘(1 / (2 : real) pow CARD (count N DIFF A)) * (&(CARD S_f) * g x0) ≤
   (1 / (2 : real) pow CARD (count N DIFF A)) * REAL_SUM_IMAGE g S_f’
    by (irule REAL_LE_LMUL_IMP >> simp[part1_two_pow_props]) >>
  gvs[REAL_MUL_ASSOC, part1_two_pow_props]
QED

(* Local helper: REAL_SUM_IMAGE vanishes when every summand on finite s is 0.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem part1_real_sum_image_eq_0[local]:
  ∀(s : α -> bool) (f : α -> real).
    FINITE s ∧ (∀x. x ∈ s ⇒ f x = 0) ⇒ REAL_SUM_IMAGE f s = 0
Proof
  rpt strip_tac >>
  mp_tac (Q.ISPEC ‘s : α -> bool’ REAL_SUM_IMAGE_FINITE_CONST2) >>
  simp[] >> disch_then (qspecl_then [‘f’, ‘0’] mp_tac) >> simp[]
QED

(* Boundary K = 0: when A = EMPTY, fixed-frozen block error probability is 0.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_fixed_empty:
  ∀(W : (bool, β) memoryless_channel) N u_frozen.
    wf_bdmc W ⇒
    block_error_prob_fixed W N ∅ u_frozen = 0
Proof
  rpt strip_tac >>
  drule block_error_prob_fixed_real_sum >>
  disch_then (qspecl_then [‘N’, ‘∅’, ‘u_frozen’] SUBST1_TAC) >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  ‘∀u y. u ∈ coset_source_vectors N ∅ u_frozen ⇒ sc_decode W N ∅ u y = u’
    by (rpt strip_tac >>
        ‘LENGTH u = N’ by fs[coset_source_vectors_def] >>
        irule LIST_EQ >> simp[] >>
        qx_gen_tac ‘i’ >> strip_tac >>
        simp[EL_sc_decode]) >>
  ‘REAL_SUM_IMAGE
     (λu. REAL_SUM_IMAGE
            (λy. if sc_decode W N ∅ u y ≠ u then
                   real (mcchannel (combine_channel W N) u {y})
                 else 0) Y_N)
     (coset_source_vectors N ∅ u_frozen) = 0’
    by (irule part1_real_sum_image_eq_0 >> simp[] >>
        qx_gen_tac ‘u’ >> strip_tac >>
        irule part1_real_sum_image_eq_0 >> simp[] >>
        qx_gen_tac ‘y’ >> strip_tac >>
        metis_tac[]) >>
  simp[extreal_of_num_def]
QED

(* Boundary K = 0: when A = EMPTY, ensemble-averaged block error probability is 0.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_avg_empty[simp]:
  ∀(W : (bool, β) memoryless_channel) N.
    wf_bdmc W ⇒
    block_error_prob_avg W N ∅ = 0
Proof
  rpt strip_tac >>
  drule block_error_prob_avg_real_sum_gen >>
  disch_then (qspecl_then [‘N’, ‘∅’] SUBST1_TAC) >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  ‘∀u y. u ∈ length_n_codes N ⇒ sc_decode W N ∅ u y = u’
    by (rpt strip_tac >>
        ‘LENGTH u = N’ by gvs[] >>
        irule LIST_EQ >> simp[] >>
        qx_gen_tac ‘i’ >> strip_tac >>
        simp[EL_sc_decode]) >>
  ‘REAL_SUM_IMAGE
     (λu. REAL_SUM_IMAGE
            (λy. if sc_decode W N ∅ u y ≠ u then
                   real (mcchannel (combine_channel W N) u {y})
                 else 0) Y_N)
     (length_n_codes N) = 0’
    by (irule part1_real_sum_image_eq_0 >> simp[] >>
        qx_gen_tac ‘u’ >> strip_tac >>
        irule part1_real_sum_image_eq_0 >> simp[] >>
        qx_gen_tac ‘y’ >> strip_tac >>
        metis_tac[]) >>
  simp[extreal_of_num_def]
QED

(* Boundary K = N: when A = count N, block_error_prob_fixed is independent of
   u_frozen and equals block_error_prob_avg.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_fixed_full:
  ∀(W : (bool, β) memoryless_channel) N u_frozen.
    wf_bdmc W ⇒
    block_error_prob_fixed W N (count N) u_frozen =
      block_error_prob_avg W N (count N)
Proof
  rpt strip_tac >>
  drule block_error_prob_fixed_real_sum >>
  disch_then (qspecl_then [‘N’, ‘count N’, ‘u_frozen’] SUBST1_TAC) >>
  drule block_error_prob_avg_real_sum_gen >>
  disch_then (qspecl_then [‘N’, ‘count N’] SUBST1_TAC) >>
  ‘count N ∩ count N = count N’ by simp[EXTENSION] >>
  ‘coset_source_vectors N (count N) u_frozen = length_n_codes N’
    by simp[EXTENSION, coset_source_vectors_def] >>
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Block 4: Polar Coding Information-Set Rule, Existence, and Optimality     *)
(* (Erdal Arıkan, 2009, arXiv:0807.3917, Section I-C.4 & Section V-C)        *)
(* ------------------------------------------------------------------------- *)

(* Polar coding information-set rule (Erdal Arıkan, 2009, arXiv:0807.3917,
   Section I-C.4, p. 5): A is a K-element subset of {0, ..., N - 1} such
   that every active index i in A has Bhattacharyya parameter at most that
   of every frozen index j in count N DIFF A.

   Written by Gemini (Google DeepMind AI agent) *)
Definition is_polar_info_set_def:
  is_polar_info_set (W : (bool, β) memoryless_channel) (N : num) (K : num)
    (A : num -> bool) ⇔
    A ⊆ count N ∧ CARD A = K ∧
    ∀i j. i ∈ A ∧ j ∈ count N DIFF A ⇒
          bhattacharyya (split_channel W N i) ≤
          bhattacharyya (split_channel W N j)
End

(* General finite-list sorting selector via sortingTheory.QSORT: for any
   transitive, total relation R on natural numbers and K <= N, taking the
   first K elements of QSORT R (COUNT_LIST N) yields a K-element subset A
   of count N dominating count N DIFF A under R.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem qsort_count_list_subset_exists:
  ∀(R : num -> num -> bool) N K.
    transitive R ∧ relation$total R ∧ K ≤ N ⇒
    ∃A. A ⊆ count N ∧ CARD A = K ∧
        ∀i j. i ∈ A ∧ j ∈ count N DIFF A ⇒ R i j
Proof
  rpt strip_tac >>
  qabbrev_tac ‘L = QSORT R (COUNT_LIST N)’ >>
  qexists_tac ‘set (TAKE K L)’ >>
  ‘PERM (COUNT_LIST N) L’ by simp[Abbr ‘L’, QSORT_PERM] >>
  ‘LENGTH L = N’
    by simp[Abbr ‘L’, LENGTH_QSORT, rich_listTheory.LENGTH_COUNT_LIST] >>
  ‘set L = count N’
    by (drule PERM_LIST_TO_SET >>
        simp[rich_listTheory.COUNT_LIST_COUNT]) >>
  ‘ALL_DISTINCT L’
    by (drule ALL_DISTINCT_PERM >>
        simp[rich_listTheory.all_distinct_count_list]) >>
  ‘TAKE K L ++ DROP K L = L’ by simp[TAKE_DROP] >>
  ‘ALL_DISTINCT (TAKE K L)’
    by (qpat_x_assum ‘ALL_DISTINCT L’ mp_tac >>
        qpat_x_assum ‘TAKE K L ++ DROP K L = L’ (SUBST1_TAC o SYM) >>
        simp[ALL_DISTINCT_APPEND]) >>
  ‘∀y. MEM y (TAKE K L) ∨ MEM y (DROP K L) ⇔ y < N’
    by (‘set (TAKE K L) ∪ set (DROP K L) = count N’
          by (qpat_x_assum ‘set L = count N’ (SUBST1_TAC o SYM) >>
              qpat_x_assum ‘TAKE K L ++ DROP K L = L’
                (fn th => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [SYM th]))) >>
              simp[]) >>
        pop_assum mp_tac >> simp[EXTENSION]) >>
  rpt conj_tac
  >- (simp[SUBSET_DEF] >> qx_gen_tac ‘x’ >> strip_tac >>
      first_x_assum (qspec_then ‘x’ mp_tac) >> simp[])
  >- (qpat_x_assum ‘ALL_DISTINCT (TAKE K L)’
        (mp_tac o MATCH_MP ALL_DISTINCT_CARD_LIST_TO_SET) >>
      simp[LENGTH_TAKE])
  >- (rpt strip_tac >> fs[] >>
      ‘MEM j (DROP K L)’
        by (qpat_x_assum ‘∀y. _ ⇔ y < N’ (qspec_then ‘j’ mp_tac) >> simp[]) >>
      ‘SORTED R L’ by simp[Abbr ‘L’, QSORT_SORTED] >>
      drule_then (qspecl_then [‘TAKE K L’, ‘DROP K L’] mp_tac) SORTED_APPEND >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [‘i’, ‘j’] mp_tac) >> simp[])
QED

(* Constructive canonical polar information-set selector sorting COUNT_LIST N
   by split-channel Bhattacharyya parameter via QSORT.

   Written by Gemini (Google DeepMind AI agent) *)
Definition polar_info_set_def:
  polar_info_set (W : (bool, β) memoryless_channel) (N : num) (K : num)
    : num -> bool =
    set (TAKE K (QSORT (λi j. bhattacharyya (split_channel W N i) ≤
                              bhattacharyya (split_channel W N j))
                       (COUNT_LIST N)))
End

(* Constructive correctness of polar_info_set W N K for all K <= N.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_polar_info_set_polar_info_set:
  ∀(W : (bool, β) memoryless_channel) N K.
    K ≤ N ⇒ is_polar_info_set W N K (polar_info_set W N K)
Proof
  rpt strip_tac >>
  simp[is_polar_info_set_def, polar_info_set_def] >>
  qabbrev_tac ‘R = λ(i : num) (j : num).
                     bhattacharyya (split_channel W N i) ≤
                     bhattacharyya (split_channel W N j)’ >>
  ‘transitive R ∧ relation$total R’
    by (simp[Abbr ‘R’, relationTheory.transitive_def,
             relationTheory.total_def, le_total] >>
        rpt strip_tac >> irule le_trans >>
        first_x_assum (irule_at Any) >> simp[]) >>
  qabbrev_tac ‘L = QSORT R (COUNT_LIST N)’ >>
  ‘PERM (COUNT_LIST N) L’ by simp[Abbr ‘L’, QSORT_PERM] >>
  ‘LENGTH L = N’
    by simp[Abbr ‘L’, LENGTH_QSORT, rich_listTheory.LENGTH_COUNT_LIST] >>
  ‘set L = count N’
    by (drule PERM_LIST_TO_SET >>
        simp[rich_listTheory.COUNT_LIST_COUNT]) >>
  ‘ALL_DISTINCT L’
    by (drule ALL_DISTINCT_PERM >>
        simp[rich_listTheory.all_distinct_count_list]) >>
  ‘TAKE K L ++ DROP K L = L’ by simp[TAKE_DROP] >>
  ‘ALL_DISTINCT (TAKE K L)’
    by (qpat_x_assum ‘ALL_DISTINCT L’ mp_tac >>
        qpat_x_assum ‘TAKE K L ++ DROP K L = L’ (SUBST1_TAC o SYM) >>
        simp[ALL_DISTINCT_APPEND]) >>
  ‘∀y. MEM y (TAKE K L) ∨ MEM y (DROP K L) ⇔ y < N’
    by (‘set (TAKE K L) ∪ set (DROP K L) = count N’
          by (qpat_x_assum ‘set L = count N’ (SUBST1_TAC o SYM) >>
              qpat_x_assum ‘TAKE K L ++ DROP K L = L’
                (fn th => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [SYM th]))) >>
              simp[]) >>
        pop_assum mp_tac >> simp[EXTENSION]) >>
  rpt conj_tac
  >- (simp[SUBSET_DEF] >> qx_gen_tac ‘x’ >> strip_tac >>
      first_x_assum (qspec_then ‘x’ mp_tac) >> simp[])
  >- (qpat_x_assum ‘ALL_DISTINCT (TAKE K L)’
        (mp_tac o MATCH_MP ALL_DISTINCT_CARD_LIST_TO_SET) >>
      simp[LENGTH_TAKE])
  >- (rpt strip_tac >> fs[] >>
      ‘MEM j (DROP K L)’
        by (qpat_x_assum ‘∀y. _ ⇔ y < N’ (qspec_then ‘j’ mp_tac) >> simp[]) >>
      ‘SORTED R L’ by simp[Abbr ‘L’, QSORT_SORTED] >>
      drule_then (qspecl_then [‘TAKE K L’, ‘DROP K L’] mp_tac) SORTED_APPEND >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [‘i’, ‘j’] mp_tac) >>
      simp[Abbr ‘R’])
QED

(* Exact existence characterization of polar information sets for arbitrary
   block-length N and dimension K (marked [simp] so ground numeral queries
   such as N = 1 reduce directly to K <= N).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_polar_info_set_exists_iff[simp]:
  ∀(W : (bool, β) memoryless_channel) N K.
    (∃A. is_polar_info_set W N K A) ⇔ K ≤ N
Proof
  rpt gen_tac >> EQ_TAC >> strip_tac
  >- (fs[is_polar_info_set_def] >>
      ‘CARD A ≤ CARD (count N)’
        by (irule CARD_SUBSET >> simp[]) >>
      fs[])
  >- (qexists_tac ‘polar_info_set W N K’ >>
      irule is_polar_info_set_polar_info_set >> simp[])
QED

(* General-N existence of a polar information set whenever K <= N.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_info_set_exists_gen:
  ∀(W : (bool, β) memoryless_channel) N K.
    K ≤ N ⇒ ∃A. is_polar_info_set W N K A
Proof
  simp[]
QED

(* Existence of a polar information set of size K <= 2 ** n for any
   well-formed B-DMC W (Erdal Arıkan, 2009, arXiv:0807.3917, Section I-C.4).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_info_set_exists:
  ∀(W : (bool, β) memoryless_channel) n K.
    wf_bdmc W ∧ K ≤ 2 ** n ⇒ ∃A. is_polar_info_set W (2 ** n) K A
Proof
  simp[]
QED

(* Boundary characterization of is_polar_info_set at dimension K = 0
   (kept non-[simp] to preserve syntactic matching in downstream quantified
   theorems).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_polar_info_set_0:
  ∀(W : (bool, β) memoryless_channel) N A.
    is_polar_info_set W N 0 A ⇔ A = ∅
Proof
  rpt gen_tac >> simp[is_polar_info_set_def] >>
  EQ_TAC >> strip_tac >> simp[] >>
  ‘FINITE A’ by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
  fs[CARD_EQ_0]
QED

(* Boundary characterization of is_polar_info_set at full dimension K = N
   (kept non-[simp] to preserve syntactic matching in downstream quantified
   theorems).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_polar_info_set_full:
  ∀(W : (bool, β) memoryless_channel) N A.
    is_polar_info_set W N N A ⇔ A = count N
Proof
  rpt gen_tac >> simp[is_polar_info_set_def] >>
  EQ_TAC >> strip_tac >> simp[] >>
  irule SUBSET_EQ_CARD >>
  ‘FINITE A’ by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
  simp[]
QED

(* General finite-set sum-minimization lemma over extended reals: if A and B
   are K-element subsets of a finite set U on which f never takes -infty,
   and every element of A has f-value at most every element of U DIFF A,
   then the sum of f over A is at most the sum of f over B.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem finite_polar_sum_minimal_extreal:
  ∀(U : α -> bool) (f : α -> extreal) K A B.
    FINITE U ∧ (∀x. x ∈ U ⇒ f x ≠ −∞) ∧
    A ⊆ U ∧ CARD A = K ∧
    (∀i j. i ∈ A ∧ j ∈ U DIFF A ⇒ f i ≤ f j) ∧
    B ⊆ U ∧ CARD B = K ⇒
    ∑ f A ≤ ∑ f B
Proof
  rpt strip_tac >>
  ‘FINITE A’ by (irule SUBSET_FINITE >> qexists_tac ‘U’ >> simp[]) >>
  ‘FINITE B’ by (irule SUBSET_FINITE >> qexists_tac ‘U’ >> simp[]) >>
  qabbrev_tac ‘I_ab = A ∩ B’ >>
  qabbrev_tac ‘D1 = A DIFF B’ >>
  qabbrev_tac ‘D2 = B DIFF A’ >>
  ‘FINITE I_ab ∧ FINITE D1 ∧ FINITE D2’
    by simp[Abbr ‘I_ab’, Abbr ‘D1’, Abbr ‘D2’, INTER_FINITE] >>
  ‘∀x. x ∈ I_ab ⇒ x ∈ U ∧ f x ≠ −∞’
    by (qx_gen_tac ‘x’ >> simp[Abbr ‘I_ab’] >> strip_tac >>
        ‘x ∈ U’ by (qpat_x_assum ‘A ⊆ U’ mp_tac >> simp[SUBSET_DEF]) >>
        simp[]) >>
  ‘∀x. x ∈ D1 ⇒ x ∈ A ∧ x ∈ U ∧ f x ≠ −∞’
    by (qx_gen_tac ‘x’ >> simp[Abbr ‘D1’] >> strip_tac >>
        ‘x ∈ U’ by (qpat_x_assum ‘A ⊆ U’ mp_tac >> simp[SUBSET_DEF]) >>
        simp[]) >>
  ‘∀x. x ∈ D2 ⇒ x ∈ U DIFF A ∧ x ∈ U ∧ f x ≠ −∞’
    by (qx_gen_tac ‘x’ >> simp[Abbr ‘D2’] >> strip_tac >>
        ‘x ∈ U’ by (qpat_x_assum ‘B ⊆ U’ mp_tac >> simp[SUBSET_DEF]) >>
        simp[]) >>
  ‘A = I_ab ∪ D1 ∧ DISJOINT I_ab D1’
    by (simp[Abbr ‘I_ab’, Abbr ‘D1’, DISJOINT_DEF, EXTENSION] >>
        conj_tac >> gen_tac >> Cases_on ‘x ∈ B’ >> simp[]) >>
  ‘B = I_ab ∪ D2 ∧ DISJOINT I_ab D2’
    by (simp[Abbr ‘I_ab’, Abbr ‘D2’, DISJOINT_DEF, EXTENSION] >>
        conj_tac >> gen_tac >> Cases_on ‘x ∈ A’ >> simp[]) >>
  ‘CARD D1 = CARD D2’
    by (simp[Abbr ‘D1’, Abbr ‘D2’, CARD_DIFF_EQN] >>
        ‘B ∩ A = A ∩ B’ by simp[INTER_COMM] >>
        simp[]) >>
  ‘∀x. x ∈ I_ab ∪ D1 ⇒ f x ≠ −∞’
    by (qx_gen_tac ‘x’ >> simp[IN_UNION] >> strip_tac >> simp[]) >>
  ‘∀x. x ∈ I_ab ∪ D2 ⇒ f x ≠ −∞’
    by (qx_gen_tac ‘x’ >> simp[IN_UNION] >> strip_tac >> simp[]) >>
  ‘∑ f A = ∑ f I_ab + ∑ f D1’
    by (‘∑ f (I_ab ∪ D1) = ∑ f I_ab + ∑ f D1’
          by (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> simp[]) >>
        qpat_x_assum ‘A = I_ab ∪ D1’
          (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
        first_assum ACCEPT_TAC) >>
  ‘∑ f B = ∑ f I_ab + ∑ f D2’
    by (‘∑ f (I_ab ∪ D2) = ∑ f I_ab + ∑ f D2’
          by (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> simp[]) >>
        qpat_x_assum ‘B = I_ab ∪ D2’
          (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
        first_assum ACCEPT_TAC) >>
  Cases_on ‘D1 = ∅’
  >- (‘CARD D2 = 0n’
        by (qpat_x_assum ‘CARD D1 = CARD D2’ (SUBST1_TAC o SYM) >> simp[]) >>
      ‘D2 = ∅’
        by (qpat_x_assum ‘FINITE D2’ (mp_tac o MATCH_MP CARD_EQ_0) >> simp[]) >>
      qpat_x_assum ‘∑ f A = _’ SUBST1_TAC >>
      qpat_x_assum ‘∑ f B = _’ SUBST1_TAC >>
      simp[])
  >- (qabbrev_tac ‘S1 = IMAGE f D1’ >>
      ‘FINITE S1 ∧ S1 ≠ ∅’ by simp[Abbr ‘S1’] >>
      qabbrev_tac ‘m = sup S1’ >>
      ‘m ∈ S1’ by simp[Abbr ‘m’, sup_maximal] >>
      ‘∃i0. i0 ∈ D1 ∧ f i0 = m’
        by (qpat_x_assum ‘m ∈ S1’ mp_tac >>
            simp[Abbr ‘S1’, IN_IMAGE] >> strip_tac >>
            qexists_tac ‘x’ >> simp[]) >>
      pop_assum strip_assume_tac >>
      ‘i0 ∈ A ∧ m ≠ −∞’
        by (qpat_x_assum ‘f i0 = m’ (SUBST1_TAC o SYM) >> simp[]) >>
      ‘∑ f D1 ≤ &(CARD D1) * m’
        by (‘∑ f D1 ≤ ∑ (λx : α. m) D1’
              by (irule EXTREAL_SUM_IMAGE_MONO >> simp[Abbr ‘m’] >>
                  qx_gen_tac ‘x’ >> disch_tac >>
                  irule le_sup_imp' >> simp[Abbr ‘S1’] >>
                  qexists_tac ‘x’ >> simp[]) >>
            ‘∑ (λx : α. m) D1 = &(CARD D1) * m’
              by (irule EXTREAL_SUM_IMAGE_FINITE_CONST >> simp[]) >>
            pop_assum (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
      ‘&(CARD D2) * m ≤ ∑ f D2’
        by (‘∑ (λx : α. m) D2 ≤ ∑ f D2’
              by (irule EXTREAL_SUM_IMAGE_MONO >> simp[] >>
                  qx_gen_tac ‘x’ >> disch_tac >>
                  ‘x ∈ U DIFF A’ by simp[] >>
                  qpat_x_assum ‘f i0 = m’ (SUBST1_TAC o SYM) >>
                  qpat_x_assum ‘∀i j. i ∈ A ∧ j ∈ U DIFF A ⇒ f i ≤ f j’
                    irule >> simp[]) >>
            ‘∑ (λx : α. m) D2 = &(CARD D2) * m’
              by (irule EXTREAL_SUM_IMAGE_FINITE_CONST >> simp[]) >>
            pop_assum (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
      ‘∑ f D1 ≤ ∑ f D2’
        by (irule le_trans >>
            qexists_tac ‘(&(CARD D2) : extreal) * m’ >> simp[] >>
            qpat_x_assum ‘CARD D1 = CARD D2’ (SUBST1_TAC o SYM) >>
            first_assum ACCEPT_TAC) >>
      qpat_x_assum ‘∑ f A = _’ SUBST1_TAC >>
      qpat_x_assum ‘∑ f B = _’ SUBST1_TAC >>
      irule le_ladd_imp >> first_assum ACCEPT_TAC)
QED

(* Real-valued finite-set sum-minimization corollary (directly reusable in
   polar_constructionScript.sml for real-valued Bhattacharyya vectors).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem finite_polar_sum_minimal_real:
  ∀(U : α -> bool) (g : α -> real) K A B.
    FINITE U ∧ A ⊆ U ∧ CARD A = K ∧
    (∀i j. i ∈ A ∧ j ∈ U DIFF A ⇒ g i ≤ g j) ∧
    B ⊆ U ∧ CARD B = K ⇒
    REAL_SUM_IMAGE g A ≤ REAL_SUM_IMAGE g B
Proof
  rpt strip_tac >>
  ‘FINITE A ∧ FINITE B’ by metis_tac[SUBSET_FINITE] >>
  mp_tac (ISPECL [“U : α -> bool”, “λx : α. Normal (g x)”,
                  “K : num”, “A : α -> bool”, “B : α -> bool”]
                 finite_polar_sum_minimal_extreal) >>
  simp[EXTREAL_SUM_IMAGE_NORMAL, extreal_le_eq]
QED

(* Sum-minimization optimality of any polar information set A over all
   K-element subsets B of count (2 ** n) (Erdal Arıkan, 2009, arXiv:0807.3917,
   Section I-C.4 & Section V-C Eq. 54).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_info_set_minimal:
  ∀(W : (bool, β) memoryless_channel) n K A B.
    wf_bdmc W ∧ is_polar_info_set W (2 ** n) K A ∧
    B ⊆ count (2 ** n) ∧ CARD B = K ⇒
    ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) A ≤
    ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) B
Proof
  rpt strip_tac >>
  fs[is_polar_info_set_def] >>
  irule (SIMP_RULE std_ss [AND_IMP_INTRO]
           (ISPECL [“count (2 ** n)”,
                    “λi. bhattacharyya (split_channel (W : (bool, β) memoryless_channel) (2 ** n) i)”,
                    “K : num”, “A : num -> bool”, “B : num -> bool”]
                   finite_polar_sum_minimal_extreal)) >>
  simp[] >> qx_gen_tac ‘i’ >> strip_tac >>
  ‘wf_bdmc (split_channel W (2 ** n) i)’ by simp[wf_bdmc_split_channel] >>
  drule bhattacharyya_bounds >> strip_tac >> simp[pos_not_neginf]
QED

(* ------------------------------------------------------------------------- *)
(* Block 5: Proposition 2 — SC Block Error Probability Bound & Corollaries   *)
(*          (Erdal Arıkan, 2009, arXiv:0807.3917, Sections I-C & V-B)        *)
(* ------------------------------------------------------------------------- *)

(* Singleton transition probabilities of combine_channel W N on Y_N are Normal
   reals in [0, 1].

   Written by Gemini (Google DeepMind AI agent) *)
Theorem combine_channel_singleton_normal[local]:
  ∀(W : (bool, β) memoryless_channel) N u y.
    wf_bdmc W ∧ LENGTH u = N ∧
    y ∈ cross_list (REPLICATE N (mccodomain W)) ⇒
    0 ≤ real (mcchannel (combine_channel W N) u {y}) ∧
    real (mcchannel (combine_channel W N) u {y}) ≤ 1 ∧
    mcchannel (combine_channel W N) u {y} =
      Normal (real (mcchannel (combine_channel W N) u {y}))
Proof
  rpt strip_tac >>
  ‘LENGTH y = N ∧ EVERY (λyi. yi ∈ mccodomain W) y’
    by fs[in_cross_list_replicate] >>
  qspecl_then [‘W’, ‘N’, ‘u’, ‘y’] mp_tac
    mcchannel_combine_channel_singleton_normal_gen >>
  simp[] >> strip_tac >> simp[real_normal]
QED

(* Non-negativity of fixed-frozen block error probability in extreal.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_fixed_pos:
  ∀(W : (bool, β) memoryless_channel) N A uf.
    wf_bdmc W ⇒ 0 ≤ block_error_prob_fixed W N A uf
Proof
  rpt strip_tac >>
  drule block_error_prob_fixed_normal >>
  disch_then (qspecl_then [‘N’, ‘A’, ‘uf’] strip_assume_tac) >>
  pop_assum SUBST1_TAC >>
  simp[extreal_of_num_def, extreal_le_eq]
QED

(* Non-negativity and Normal representation of ensemble-averaged block error
   probability block_error_prob_avg W N A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_avg_normal:
  ∀(W : (bool, β) memoryless_channel) N A.
    wf_bdmc W ⇒
    0 ≤ real (block_error_prob_avg W N A) ∧
    block_error_prob_avg W N A =
      Normal (real (block_error_prob_avg W N A)) ∧
    0 ≤ block_error_prob_avg W N A
Proof
  rpt gen_tac >> strip_tac >>
  drule block_error_prob_avg_real_sum_gen >>
  disch_then (qspecl_then [‘N’, ‘A’] SUBST1_TAC) >>
  REWRITE_TAC[real_normal, extreal_of_num_def, extreal_le_eq] >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  ‘0 ≤ (1 / (2 : real) pow N) *
       REAL_SUM_IMAGE
         (λu. REAL_SUM_IMAGE
                (λy. if sc_decode W N A u y ≠ u
                     then real (mcchannel (combine_channel W N) u {y})
                     else 0) Y_N)
         (length_n_codes N)’
    by (irule REAL_LE_MUL >>
        conj_tac >- simp[part1_two_pow_props] >>
        irule REAL_SUM_IMAGE_POS >> simp[] >>
        qx_gen_tac ‘u’ >> strip_tac >>
        irule REAL_SUM_IMAGE_POS >> simp[] >>
        qx_gen_tac ‘y’ >> strip_tac >>
        Cases_on ‘sc_decode W N A u y ≠ u’ >> simp[] >>
        irule (cj 1 combine_channel_singleton_normal) >>
        gvs[Abbr ‘Y_N’]) >>
  simp[]
QED

(* Decomposing any list l at index i < LENGTH l into
   TAKE i l ++ [EL i l] ++ DROP (i + 1) l.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem take_el_drop[local]:
  ∀i (l : α list).
    i < LENGTH l ⇒ TAKE i l ++ [EL i l] ++ DROP (i + 1) l = l
Proof
  Induct_on ‘l’ >> simp[] >>
  Cases_on ‘i’ >> simp[ADD1]
QED

(* Extracting the middle element at index LENGTH l1 from l1 ++ [x] ++ l2.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem el_length_append[local]:
  ∀(l1 : α list) x l2. EL (LENGTH l1) (l1 ++ [x] ++ l2) = x
Proof
  Induct_on ‘l1’ >> simp[]
QED

(* Extracting the prefix TAKE (LENGTH l1) from l1 ++ l2.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem take_length_append[local]:
  ∀(l1 : α list) l2. TAKE (LENGTH l1) (l1 ++ l2) = l1
Proof
  rw[TAKE_APPEND1]
QED

(* Bijection between (u_prev, (u_i, u_later)) in
   length_n_codes i x (UNIV(:bool) x length_n_codes (N - i - 1))
   and u = u_prev ++ [u_i] ++ u_later in length_n_codes N for i < N.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem BIJ_split_length_n_codes:
  ∀N i.
    i < N ⇒
    BIJ (λ(u_prev, (u_i, u_later)). u_prev ++ [u_i] ++ u_later)
        (length_n_codes i × (𝕌(:bool) × length_n_codes (N - i - 1)))
        (length_n_codes N)
Proof
  rpt strip_tac >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_PROD, EXISTS_PROD] >>
  conj_tac
  >- (qx_genl_tac [‘u1’, ‘b1’, ‘v1’, ‘u2’, ‘b2’, ‘v2’] >>
      strip_tac >> strip_tac >>
      ‘TAKE i (u1 ++ (b1::v1)) = TAKE i (u2 ++ (b2::v2))’ by gvs[] >>
      ‘TAKE i (u1 ++ (b1::v1)) = u1 ∧ TAKE i (u2 ++ (b2::v2)) = u2’
        by metis_tac[take_length_append] >>
      gvs[])
  >- (qx_gen_tac ‘x’ >> strip_tac >>
      qexistsl_tac [‘TAKE i x’, ‘EL i x’, ‘DROP (i + 1) x’] >>
      mp_tac (ISPECL [“i : num”, “x : bool list”] take_el_drop) >>
      simp[])
QED

(* Coordinate-i ML tie-or-error event E_i (Erdal Arıkan, 2009, Section V-B
   Eq. 52, with split-channel superscript W_N^{(i)}): the true bit EL i u has
   split-channel likelihood <= the flipped bit ~(EL i u) given (y, TAKE i u).

   Written by Gemini (Google DeepMind AI agent) *)
Definition sc_error_event_i_def:
  sc_error_event_i (W : (bool, β) memoryless_channel) (N : num) (i : num)
                   (u : bool list) (y : β list) ⇔
    mcchannel (split_channel W N i) (EL i u) {(y, TAKE i u)} ≤
    mcchannel (split_channel W N i) (¬EL i u) {(y, TAKE i u)}
End

(* Deterministic tie-breaking inclusion: whenever b differs from
   sc_bit_decision W N i y u_prev, W_N^{(i)}(y, u_prev | b) <=
   W_N^{(i)}(y, u_prev | ~b) holds unconditionally for both b = F and b = T.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_bit_decision_error_imp_le:
  ∀(W : (bool, β) memoryless_channel) N i y u_prev b.
    b ≠ sc_bit_decision W N i y u_prev ⇒
    mcchannel (split_channel W N i) b {(y, u_prev)} ≤
    mcchannel (split_channel W N i) (¬b) {(y, u_prev)}
Proof
  Cases_on ‘b’ >> simp[sc_bit_decision_def] >> metis_tac[le_total]
QED

(* First-error decomposition (Erdal Arıkan, 2009, Section V-B Eq. 51): if
   sc_decode W N A u y <> u for LENGTH u = N, then the earliest differing
   coordinate i < N lies in A, has exact prefix agreement
   TAKE i (sc_decode W N A u y) = TAKE i u, and satisfies
   EL i u <> sc_bit_decision W N i y (TAKE i u).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_first_error:
  ∀(W : (bool, β) memoryless_channel) N A u y.
    LENGTH u = N ∧ sc_decode W N A u y ≠ u ⇒
    ∃i. i ∈ A ∧ i < N ∧
        TAKE i (sc_decode W N A u y) = TAKE i u ∧
        EL i u ≠ sc_bit_decision W N i y (TAKE i u)
Proof
  rpt strip_tac >>
  drule_all sc_decode_neq_first_error >> strip_tac >>
  qexists_tac ‘i’ >> gvs[]
QED

(* Combining first-error decomposition with pointwise tie-breaking inclusion:
   any block decoding error sc_decode W N A u y <> u implies
   sc_error_event_i W N i u y for some active information coordinate i in A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_decode_error_imp_exists_event_i:
  ∀(W : (bool, β) memoryless_channel) N A u y.
    LENGTH u = N ∧ sc_decode W N A u y ≠ u ⇒
    ∃i. i ∈ A ∧ i < N ∧ sc_error_event_i W N i u y
Proof
  rpt strip_tac >>
  drule_all sc_decode_neq_first_error >> strip_tac >>
  qexists_tac ‘i’ >> simp[sc_error_event_i_def]
QED

(* Pointwise non-negative weighted union-bound inequality over finite
   information set A.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem real_indicator_first_error_le_sum[local]:
  ∀(W : (bool, β) memoryless_channel) N A u y (w : real).
    FINITE A ∧ LENGTH u = N ∧ 0 ≤ w ⇒
    (if sc_decode W N A u y ≠ u then w else 0) ≤
    REAL_SUM_IMAGE (λi. if sc_error_event_i W N i u y then w else 0) A
Proof
  rpt strip_tac >>
  Cases_on ‘sc_decode W N A u y ≠ u’ >> simp[]
  >- (drule_all sc_decode_error_imp_exists_event_i >> strip_tac >>
      qabbrev_tac ‘f = λj. if sc_error_event_i W N j u y then w else (0 : real)’ >>
      ‘w = f i’ by simp[Abbr ‘f’] >>
      pop_assum SUBST1_TAC >>
      irule REAL_SUM_IMAGE_POS_MEM_LE >>
      simp[Abbr ‘f’] >> rw[])
  >- (irule REAL_SUM_IMAGE_POS >> simp[] >> rw[])
QED

(* Division-by-zero-free Bhattacharyya inequality: for non-negative reals
   a and b, a <= b implies a = sqrt(a^2) <= sqrt(a * b).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem real_le_sqrt_mul:
  ∀(a : real) (b : real).
    0 ≤ a ∧ a ≤ b ⇒ a ≤ sqrt (a * b)
Proof
  rpt strip_tac >>
  ‘a * a ≤ a * b’ by (irule REAL_LE_LMUL_IMP >> simp[]) >>
  ‘0 ≤ a * a’ by (irule REAL_LE_MUL >> simp[]) >>
  ‘sqrt (a * a) ≤ sqrt (a * b)’
    by (irule SQRT_MONO_LE >> simp[]) >>
  ‘sqrt (a * a) = a’
    by simp[GSYM POW_2, POW_2_SQRT] >>
  REAL_ASM_ARITH_TAC
QED

(* Guarded indicator version: for any non-negative reals a, b >= 0,
   (if a <= b then a else 0) <= sqrt (a * b).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem real_indicator_le_sqrt_mul[local]:
  ∀(a : real) (b : real).
    0 ≤ a ∧ 0 ≤ b ⇒
    (if a ≤ b then a else 0) ≤ sqrt (a * b)
Proof
  rpt strip_tac >> rw[real_le_sqrt_mul] >>
  irule SQRT_POS_LE >> irule REAL_LE_MUL >> simp[]
QED

(* Explicit two-point expansion of REAL_SUM_IMAGE over UNIV(:bool).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_UNIV_BOOL[local]:
  ∀f : bool -> real. REAL_SUM_IMAGE f 𝕌(:bool) = f T + f F
Proof
  gen_tac >>
  simp[UNIV_BOOL, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT]
QED

(* Two-input average Bhattacharyya dominance for a single split-channel output:
   (1/2) * aF * 1_{aF <= aT} + (1/2) * aT * 1_{aT <= aF} <= sqrt (aF * aT).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem real_bool_sum_indicator_le_sqrt[local]:
  ∀(aF : real) (aT : real).
    0 ≤ aF ∧ 0 ≤ aT ⇒
    REAL_SUM_IMAGE
      (λb. (1 / 2) * (if (if b then aT else aF) ≤ (if ¬b then aT else aF)
                      then (if b then aT else aF) else 0))
      𝕌(:bool) ≤
    sqrt (aF * aT)
Proof
  rpt strip_tac >>
  simp[REAL_SUM_IMAGE_UNIV_BOOL] >>
  qspecl_then [‘aF’, ‘aT’] mp_tac real_indicator_le_sqrt_mul >>
  qspecl_then [‘aT’, ‘aF’] mp_tac real_indicator_le_sqrt_mul >>
  ‘aT * aF = aF * aT’ by REAL_ARITH_TAC >>
  simp[] >> REAL_ARITH_TAC
QED

(* Real-valued split-channel marginalization identity for i < N:
   (1 / 2^N) * sum_{u_later in length_n_codes (N - i - 1)}
                 W_N(y | u_prev ++ [u_i] ++ u_later)
   = (1 / 2) * W_N^{(i)}(y, u_prev | u_i).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem split_channel_marginalize_later_real[local]:
  ∀(W : (bool, β) memoryless_channel) N i u_i y u_prev.
    wf_bdmc W ∧ i < N ∧
    y ∈ cross_list (REPLICATE N (mccodomain W)) ∧
    u_prev ∈ length_n_codes i ⇒
    (1 / (2 : real) pow N) *
    REAL_SUM_IMAGE
      (λu_later. real (mcchannel (combine_channel W N)
                                 (u_prev ++ [u_i] ++ u_later) {y}))
      (length_n_codes (N - i - 1)) =
    (1 / 2) * real (mcchannel (split_channel W N i) u_i {(y, u_prev)})
Proof
  rpt strip_tac >>
  ‘LENGTH y = N ∧ EVERY (λyi. yi ∈ mccodomain W) y’
    by fs[in_cross_list_replicate] >>
  ‘LENGTH u_prev = i’ by fs[] >>
  qspecl_then [‘W’, ‘N’, ‘i’, ‘u_i’, ‘y’, ‘u_prev’] mp_tac
    mcchannel_split_channel_singleton_real >>
  simp[] >> disch_then SUBST1_TAC >>
  simp[real_normal] >>
  disj2_tac >>
  ‘N = SUC (N - 1)’ by decide_tac >>
  pop_assum (fn th => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[pow]
QED

(* Coordinate-i error event probability bound (Erdal Arıkan, 2009, Section V-B
   Eq. 53): for any wf_bdmc W and i < N, P(E_i) <= Z(W_N^{(i)}) with zero
   division by zero.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sc_error_event_i_prob_le_bhattacharyya_gen:
  ∀(W : (bool, β) memoryless_channel) N i.
    wf_bdmc W ∧ i < N ⇒
    (1 / (2 : real) pow N) *
    REAL_SUM_IMAGE
      (λy. REAL_SUM_IMAGE
             (λu. if sc_error_event_i W N i u y
                  then real (mcchannel (combine_channel W N) u {y})
                  else 0)
             (length_n_codes N))
      (cross_list (REPLICATE N (mccodomain W))) ≤
    real (bhattacharyya (split_channel W N i))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  ‘wf_bdmc (split_channel W N i) ∧
   mccodomain (split_channel W N i) = Y_N × length_n_codes i’
    by (drule_all wf_bdmc_split_channel_gen >>
        drule_all split_channel_accessors_gen >> simp[Abbr ‘Y_N’]) >>
  ‘(1 / (2 : real) pow N) *
   REAL_SUM_IMAGE
     (λy. REAL_SUM_IMAGE
            (λu. if sc_error_event_i W N i u y
                 then real (mcchannel (combine_channel W N) u {y})
                 else 0)
            (length_n_codes N)) Y_N =
   REAL_SUM_IMAGE
     (λy. (1 / (2 : real) pow N) *
          REAL_SUM_IMAGE
            (λu. if sc_error_event_i W N i u y
                 then real (mcchannel (combine_channel W N) u {y})
                 else 0)
            (length_n_codes N)) Y_N’
    by simp[REAL_SUM_IMAGE_CMUL] >>
  pop_assum SUBST1_TAC >>
  ‘real (bhattacharyya (split_channel W N i)) =
   REAL_SUM_IMAGE
     (λy. REAL_SUM_IMAGE
            (λu_prev. sqrt (real (mcchannel (split_channel W N i) F {(y, u_prev)}) *
                            real (mcchannel (split_channel W N i) T {(y, u_prev)})))
            (length_n_codes i)) Y_N’
    by (qspec_then ‘split_channel W N i’ mp_tac bhattacharyya_real_sum >>
        simp[] >> disch_then SUBST1_TAC >>
        simp[real_normal, REAL_SUM_IMAGE_REAL_SUM_IMAGE]) >>
  pop_assum SUBST1_TAC >>
  irule REAL_SUM_IMAGE_MONO >> reverse conj_tac >- simp[] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  ‘BIJ (λ((u_prev, u_i), u_later). u_prev ++ [u_i] ++ u_later)
       ((length_n_codes i × 𝕌(:bool)) × length_n_codes (N - i - 1))
       (length_n_codes N)’
    by (simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_PROD, EXISTS_PROD] >>
        conj_tac
        >- (qx_genl_tac [‘u1’, ‘b1’, ‘v1’, ‘u2’, ‘b2’, ‘v2’] >>
            strip_tac >> strip_tac >>
            ‘TAKE i (u1 ++ (b1::v1)) = TAKE i (u2 ++ (b2::v2))’ by gvs[] >>
            ‘TAKE i (u1 ++ (b1::v1)) = u1 ∧ TAKE i (u2 ++ (b2::v2)) = u2’
              by metis_tac[take_length_append] >>
            gvs[])
        >- (qx_gen_tac ‘x’ >> strip_tac >>
            qexistsl_tac [‘TAKE i x’, ‘EL i x’, ‘DROP (i + 1) x’] >>
            mp_tac (ISPECL [“i : num”, “x : bool list”] take_el_drop) >>
            simp[])) >>
  ‘REAL_SUM_IMAGE
     (λu. if sc_error_event_i W N i u y
          then real (mcchannel (combine_channel W N) u {y})
          else 0)
     (length_n_codes N) =
   REAL_SUM_IMAGE
     (λu_prev.
        REAL_SUM_IMAGE
          (λu_i.
             REAL_SUM_IMAGE
               (λu_later.
                  if mcchannel (split_channel W N i) u_i {(y, u_prev)} ≤
                     mcchannel (split_channel W N i) (¬u_i) {(y, u_prev)}
                  then real (mcchannel (combine_channel W N)
                                       (u_prev ++ [u_i] ++ u_later) {y})
                  else 0)
               (length_n_codes (N - i - 1)))
          𝕌(:bool))
     (length_n_codes i)’
    by (qspecl_then
          [‘(length_n_codes i × 𝕌(:bool)) × length_n_codes (N - i - 1)’,
           ‘length_n_codes N’,
           ‘λ((u_prev : bool list, u_i : bool), u_later : bool list).
              u_prev ++ [u_i] ++ u_later’,
           ‘λu : bool list.
              if sc_error_event_i W N i u y
              then real (mcchannel (combine_channel W N) u {y})
              else 0’]
          mp_tac REAL_SUM_IMAGE_BIJ >>
        impl_tac >- fs[FINITE_CROSS] >>
        disch_then SUBST1_TAC >>
        simp[REAL_SUM_IMAGE_REAL_SUM_IMAGE, FINITE_CROSS] >>
        irule REAL_SUM_IMAGE_EQ >>
        simp[FINITE_CROSS, FORALL_PROD, o_DEF, sc_error_event_i_def] >>
        qx_genl_tac [‘u_prev’, ‘u_i’, ‘u_later’] >> strip_tac >>
        ‘LENGTH u_prev = i’ by fs[] >>
        ‘TAKE i (u_prev ++ [u_i] ++ u_later) = u_prev’
          by (‘u_prev ++ [u_i] ++ u_later = u_prev ++ ([u_i] ++ u_later)’
                by simp[] >>
              pop_assum SUBST1_TAC >>
              metis_tac[take_length_append]) >>
        ‘EL i (u_prev ++ [u_i] ++ u_later) = u_i’
          by metis_tac[el_length_append] >>
        simp[]) >>
  pop_assum SUBST1_TAC >>
  DEP_ONCE_REWRITE_TAC[GSYM REAL_SUM_IMAGE_CMUL] >>
  conj_tac >- simp[] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  irule REAL_SUM_IMAGE_MONO >> reverse conj_tac >- simp[] >>
  qx_gen_tac ‘u_prev’ >> strip_tac >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  DEP_ONCE_REWRITE_TAC[GSYM REAL_SUM_IMAGE_CMUL] >>
  conj_tac >- simp[] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  REWRITE_TAC[REAL_SUM_IMAGE_UNIV_BOOL] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  ‘(y, u_prev) ∈ mccodomain (split_channel W N i)’ by fs[] >>
  drule_all wf_bdmc_mcchannel_singleton_normal >>
  disch_then (fn th =>
    mp_tac (Q.SPEC ‘F’ th) >> mp_tac (Q.SPEC ‘T’ th)) >>
  rpt strip_tac >>
  ASM_REWRITE_TAC[real_normal, extreal_le_eq] >>
  ‘(1 / (2 : real) pow N) *
   REAL_SUM_IMAGE
     (λu_later. if r ≤ r'
                then real (mcchannel (combine_channel W N)
                                     (u_prev ++ [T] ++ u_later) {y})
                else 0)
     (length_n_codes (N - i - 1)) =
   (1 / 2) * (if r ≤ r' then r else 0)’
    by (reverse (Cases_on ‘r ≤ r'’) >- simp[REAL_SUM_IMAGE_0] >>
        ASM_REWRITE_TAC[] >>
        qspecl_then [‘W’, ‘N’, ‘i’, ‘T’, ‘y’, ‘u_prev’] mp_tac
          split_channel_marginalize_later_real >>
        ASM_REWRITE_TAC[real_normal] >>
        impl_tac >- fs[Abbr ‘Y_N’] >>
        simp[]) >>
  ‘(1 / (2 : real) pow N) *
   REAL_SUM_IMAGE
     (λu_later. if r' ≤ r
                then real (mcchannel (combine_channel W N)
                                     (u_prev ++ [F] ++ u_later) {y})
                else 0)
     (length_n_codes (N - i - 1)) =
   (1 / 2) * (if r' ≤ r then r' else 0)’
    by (reverse (Cases_on ‘r' ≤ r’) >- simp[REAL_SUM_IMAGE_0] >>
        ASM_REWRITE_TAC[] >>
        qspecl_then [‘W’, ‘N’, ‘i’, ‘F’, ‘y’, ‘u_prev’] mp_tac
          split_channel_marginalize_later_real >>
        ASM_REWRITE_TAC[real_normal] >>
        impl_tac >- fs[Abbr ‘Y_N’] >>
        simp[]) >>
  pop_assum SUBST1_TAC >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘r'’, ‘r’] mp_tac real_indicator_le_sqrt_mul >>
  qspecl_then [‘r’, ‘r'’] mp_tac real_indicator_le_sqrt_mul >>
  ‘r * r' = r' * r’ by REAL_ARITH_TAC >>
  ASM_REWRITE_TAC[] >>
  REAL_ASM_ARITH_TAC
QED

(* General-N Proposition 2 ensemble-average bound (holds for all N : num,
   including N = 0).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_2_avg_gen:
  ∀(W : (bool, β) memoryless_channel) N A.
    wf_bdmc W ∧ A ⊆ count N ⇒
    block_error_prob_avg W N A ≤
    ∑ (λi. bhattacharyya (split_channel W N i)) A
Proof
  rpt strip_tac >>
  ‘FINITE A’ by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
  drule_all block_error_prob_avg_real_sum >>
  disch_then SUBST1_TAC >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE N (mccodomain W))’ >>
  ‘FINITE Y_N’
    by (fs[Abbr ‘Y_N’, wf_bdmc_def] >> simp[finite_cross_list_replicate]) >>
  ‘∑ (λi. bhattacharyya (split_channel W N i)) A =
   Normal (REAL_SUM_IMAGE (λi. real (bhattacharyya (split_channel W N i))) A)’
    by (‘∑ (λi. bhattacharyya (split_channel W N i)) A =
         ∑ (λi. Normal (real (bhattacharyya (split_channel W N i)))) A’
          by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
              qx_gen_tac ‘i’ >> strip_tac >>
              ‘i < N’ by (fs[SUBSET_DEF] >> first_x_assum drule >> simp[]) >>
              drule_all wf_bdmc_split_channel_gen >> strip_tac >>
              drule bhattacharyya_bounds >> strip_tac >> gvs[real_normal]) >>
        pop_assum SUBST1_TAC >>
        simp[EXTREAL_SUM_IMAGE_NORMAL]) >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[extreal_le_eq] >>
  ‘REAL_SUM_IMAGE
     (λu. REAL_SUM_IMAGE
            (λy. if sc_decode W N A u y ≠ u
                 then real (mcchannel (combine_channel W N) u {y})
                 else 0) Y_N)
     (length_n_codes N) ≤
   REAL_SUM_IMAGE
     (λu. REAL_SUM_IMAGE
            (λy. REAL_SUM_IMAGE
                   (λi. if sc_error_event_i W N i u y
                        then real (mcchannel (combine_channel W N) u {y})
                        else 0) A) Y_N)
     (length_n_codes N)’
    by (irule REAL_SUM_IMAGE_MONO >> reverse conj_tac >- simp[] >>
        qx_gen_tac ‘u’ >> strip_tac >>
        CONV_TAC (DEPTH_CONV BETA_CONV) >>
        irule REAL_SUM_IMAGE_MONO >> reverse conj_tac >- simp[] >>
        qx_gen_tac ‘y’ >> strip_tac >>
        CONV_TAC (DEPTH_CONV BETA_CONV) >>
        irule real_indicator_first_error_le_sum >>
        conj_tac >- fs[] >>
        conj_tac >- fs[] >>
        irule (cj 1 combine_channel_singleton_normal) >>
        fs[Abbr ‘Y_N’]) >>
  ‘REAL_SUM_IMAGE
     (λu. REAL_SUM_IMAGE
            (λy. REAL_SUM_IMAGE
                   (λi. if sc_error_event_i W N i u y
                        then real (mcchannel (combine_channel W N) u {y})
                        else 0) A) Y_N)
     (length_n_codes N) =
   REAL_SUM_IMAGE
     (λi. REAL_SUM_IMAGE
            (λy. REAL_SUM_IMAGE
                   (λu. if sc_error_event_i W N i u y
                        then real (mcchannel (combine_channel W N) u {y})
                        else 0)
                   (length_n_codes N)) Y_N) A’
    by (irule EQ_TRANS >>
        qexists_tac
          ‘REAL_SUM_IMAGE
             (λy. REAL_SUM_IMAGE
                    (λu. REAL_SUM_IMAGE
                           (λi. if sc_error_event_i W N i u y
                                then real (mcchannel (combine_channel W N) u {y})
                                else 0) A)
                    (length_n_codes N)) Y_N’ >>
        conj_tac >- (ho_match_mp_tac NESTED_REAL_SUM_IMAGE_REVERSE >> simp[]) >>
        irule EQ_TRANS >>
        qexists_tac
          ‘REAL_SUM_IMAGE
             (λy. REAL_SUM_IMAGE
                    (λi. REAL_SUM_IMAGE
                           (λu. if sc_error_event_i W N i u y
                                then real (mcchannel (combine_channel W N) u {y})
                                else 0)
                           (length_n_codes N)) A) Y_N’ >>
        conj_tac
        >- (irule REAL_SUM_IMAGE_EQ >> reverse conj_tac >- simp[] >>
            qx_gen_tac ‘y’ >> strip_tac >>
            CONV_TAC (DEPTH_CONV BETA_CONV) >>
            ho_match_mp_tac NESTED_REAL_SUM_IMAGE_REVERSE >> simp[]) >>
        ho_match_mp_tac NESTED_REAL_SUM_IMAGE_REVERSE >> simp[]) >>
  ‘(1 / (2 : real) pow N) *
   REAL_SUM_IMAGE
     (λu. REAL_SUM_IMAGE
            (λy. if sc_decode W N A u y ≠ u
                 then real (mcchannel (combine_channel W N) u {y})
                 else 0) Y_N)
     (length_n_codes N) ≤
   REAL_SUM_IMAGE
     (λi. (1 / (2 : real) pow N) *
          REAL_SUM_IMAGE
            (λy. REAL_SUM_IMAGE
                   (λu. if sc_error_event_i W N i u y
                        then real (mcchannel (combine_channel W N) u {y})
                        else 0)
                   (length_n_codes N)) Y_N) A’
    by (pop_assum (ASSUME_TAC o SYM) >>
        ‘0 ≤ (1 / (2 : real) pow N)’ by simp[part1_two_pow_props] >>
        DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_CMUL] >>
        conj_tac >- simp[] >>
        CONV_TAC (DEPTH_CONV BETA_CONV) >>
        ASM_REWRITE_TAC[] >>
        irule REAL_LE_LMUL_IMP >> ASM_REWRITE_TAC[]) >>
  irule REAL_LE_TRANS >>
  first_x_assum (irule_at (Pos hd)) >>
  irule REAL_SUM_IMAGE_MONO >> reverse conj_tac >- simp[] >>
  qx_gen_tac ‘i’ >> strip_tac >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  ‘i < N’ by (fs[SUBSET_DEF] >> first_x_assum drule >> simp[]) >>
  qpat_x_assum ‘Abbrev (Y_N = _)’
    (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  irule sc_error_event_i_prob_le_bhattacharyya_gen >>
  simp[]
QED

(* Proposition 2, Eq. (13) (Erdal Arıkan, 2009, Section I-C & Section V-B):
   ensemble-averaged block error probability under successive cancellation
   decoding satisfies P_e(N, K, A) <= sum_{i in A} Z(W_N^{(i)}) for N = 2 ** n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_2_avg:
  ∀(W : (bool, β) memoryless_channel) n A.
    wf_bdmc W ∧ A ⊆ count (2 ** n) ⇒
    block_error_prob_avg W (2 ** n) A ≤
    ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) A
Proof
  rw[proposition_2_avg_gen]
QED

(* Finite minimum-is-at-most-mean inequality for REAL_SUM_IMAGE:
   on any non-empty finite set s, there exists x0 in s with
   &(CARD s) * f x0 <= REAL_SUM_IMAGE f s.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_EXISTS_LE_MEAN[local]:
  ∀(s : α -> bool) (f : α -> real).
    FINITE s ∧ s ≠ ∅ ⇒
    ∃x0. x0 ∈ s ∧ &(CARD s) * f x0 ≤ REAL_SUM_IMAGE f s
Proof
  rpt strip_tac >>
  drule_all part1_finite_exists_min >>
  disch_then (qspec_then ‘f’ strip_assume_tac) >>
  qexists_tac ‘x0’ >> simp[] >>
  ‘f x0 * &(CARD s) = REAL_SUM_IMAGE (λx. f x0) s’
    by simp[REAL_SUM_IMAGE_FINITE_CONST3] >>
  pop_assum SUBST1_TAC >>
  qspec_then ‘s’ mp_tac REAL_SUM_IMAGE_MONO >> simp[]
QED

(* Non-emptiness of length_n_codes N for every N : num.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem length_n_codes_nonempty[local]:
  ∀N. length_n_codes N ≠ ∅
Proof
  gen_tac >> simp[Once EXTENSION] >>
  qexists_tac ‘REPLICATE N F’ >> simp[]
QED

(* General-N existential frozen-vector bound: there exists u_frozen of length N
   whose fixed-frozen block error probability is at most
   block_error_prob_avg W N A (and hence at most sum_{i in A} Z(W_N^{(i)})).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_2_exists_frozen_gen:
  ∀(W : (bool, β) memoryless_channel) N A.
    wf_bdmc W ∧ A ⊆ count N ⇒
    ∃u_frozen.
      LENGTH u_frozen = N ∧
      block_error_prob_fixed W N A u_frozen ≤
      ∑ (λi. bhattacharyya (split_channel W N i)) A
Proof
  rpt strip_tac >>
  qspecl_then [‘length_n_codes N’,
               ‘λuf. real (block_error_prob_fixed W N A uf)’]
    mp_tac REAL_SUM_IMAGE_EXISTS_LE_MEAN >>
  simp[length_n_codes_nonempty] >> strip_tac >>
  qexists_tac ‘x0’ >>
  ‘LENGTH x0 = N’ by fs[] >>
  simp[] >>
  irule le_trans >>
  qexists_tac ‘block_error_prob_avg W N A’ >>
  conj_tac
  >- (‘block_error_prob_fixed W N A x0 =
       Normal (real (block_error_prob_fixed W N A x0))’
        by (irule (cj 2 block_error_prob_fixed_normal) >> simp[]) >>
      ‘block_error_prob_avg W N A =
       Normal ((1 / (2 : real) pow N) *
               REAL_SUM_IMAGE (λuf. real (block_error_prob_fixed W N A uf))
                              (length_n_codes N))’
        by (irule block_error_prob_avg_eq_mean_fixed >> simp[]) >>
      pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
      gvs[extreal_le_eq, part1_two_pow_props])
  >- (irule proposition_2_avg_gen >> simp[])
QED

(* Proposition 2, Eq. (14) (Erdal Arıkan, 2009, Section I-C & Section V-B):
   existence of a frozen vector u_frozen of length 2 ** n achieving
   P_e(2^n, K, A, u_frozen) <= sum_{i in A} Z(W_{2^n}^{(i)}).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_2_exists_frozen:
  ∀(W : (bool, β) memoryless_channel) n A.
    wf_bdmc W ∧ A ⊆ count (2 ** n) ⇒
    ∃u_frozen.
      LENGTH u_frozen = 2 ** n ∧
      block_error_prob_fixed W (2 ** n) A u_frozen ≤
      ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) A
Proof
  rw[proposition_2_exists_frozen_gen]
QED

(* Combined Proposition 2 (Erdal Arıkan, 2009, Section I-C Eqs. 13-14 &
   Section V-B Eqs. 47-53): both ensemble-averaged and existential fixed-frozen
   SC block error probability bounds for any B-DMC W and A SUBSET count (2 ** n).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_2:
  ∀(W : (bool, β) memoryless_channel) n A.
    wf_bdmc W ∧ A ⊆ count (2 ** n) ⇒
    block_error_prob_avg W (2 ** n) A ≤
      ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) A ∧
    ∃u_frozen.
      LENGTH u_frozen = 2 ** n ∧
      block_error_prob_fixed W (2 ** n) A u_frozen ≤
      ∑ (λi. bhattacharyya (split_channel W (2 ** n) i)) A
Proof
  metis_tac[proposition_2_avg, proposition_2_exists_frozen]
QED

(* ------------------------------------------------------------------------- *)
(* Safe Non-Looping [simp] Corollaries for Concrete Numeral E2E Evaluations  *)
(* ------------------------------------------------------------------------- *)

(* Concrete finite-set subset check against count N without requiring
   INSERT_SUBSET.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem INSERT_SUBSET_COUNT[simp]:
  ∀e s N. (e INSERT s) ⊆ count N ⇔ e < N ∧ s ⊆ count N
Proof
  simp[INSERT_SUBSET]
QED

(* Safe INSERT expansion for finite sums of split-channel Bhattacharyya
   parameters (avoids s DELETE e / DELETE_NON_ELEMENT_RWT and infinity
   side-conditions).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem EXTREAL_SUM_IMAGE_INSERT_split_bhattacharyya[simp]:
  ∀(W : (bool, β) memoryless_channel) N e s.
    wf_bdmc W ∧ FINITE s ∧ e < N ∧ s ⊆ count N ⇒
    ∑ (λi. bhattacharyya (split_channel W N i)) (e INSERT s) =
      if s = ∅ then
        bhattacharyya (split_channel W N e)
      else if e ∈ s then
        ∑ (λi. bhattacharyya (split_channel W N i)) s
      else
        bhattacharyya (split_channel W N e) +
        ∑ (λi. bhattacharyya (split_channel W N i)) s
Proof
  rpt strip_tac >>
  Cases_on ‘s = ∅’ >> simp[] >>
  Cases_on ‘e ∈ s’ >> simp[ABSORPTION_RWT] >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_PROPERTY] >>
  simp[DELETE_NON_ELEMENT_RWT] >>
  disj1_tac >> qx_gen_tac ‘i’ >> strip_tac >>
  ‘i < N’
    by (gvs[] >> fs[SUBSET_DEF] >> first_x_assum drule >> simp[]) >>
  drule_all wf_bdmc_split_channel_gen >> strip_tac >>
  drule bhattacharyya_bounds >> strip_tac >>
  irule pos_not_neginf >> simp[]
QED

(* Base N = 1 split-channel Bhattacharyya simplification rule.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bhattacharyya_split_channel_1_0_simp[simp]:
  ∀(W : (bool, β) memoryless_channel).
    wf_bdmc W ⇒ bhattacharyya (split_channel W 1 0) = bhattacharyya W
Proof
  rw[bhattacharyya_split_channel_1_0]
QED

(* Transitive upper-bound simplification rule for block_error_prob_avg W N A <= B.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_avg_le_ub[simp]:
  ∀(W : (bool, β) memoryless_channel) N A B.
    wf_bdmc W ∧ A ⊆ count N ∧
    ∑ (λi. bhattacharyya (split_channel W N i)) A ≤ B ⇒
    block_error_prob_avg W N A ≤ B
Proof
  rpt strip_tac >>
  irule le_trans >>
  qexists_tac ‘∑ (λi. bhattacharyya (split_channel W N i)) A’ >>
  simp[proposition_2_avg_gen]
QED

(* Transitive existential upper-bound simplification rule for fixed-frozen
   block error probability.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem block_error_prob_fixed_exists_le_ub[simp]:
  ∀(W : (bool, β) memoryless_channel) N A B.
    wf_bdmc W ∧ A ⊆ count N ∧
    ∑ (λi. bhattacharyya (split_channel W N i)) A ≤ B ⇒
    ∃u_frozen.
      LENGTH u_frozen = N ∧
      block_error_prob_fixed W N A u_frozen ≤ B
Proof
  rpt strip_tac >>
  drule_all proposition_2_exists_frozen_gen >> strip_tac >>
  qexists_tac ‘u_frozen’ >> simp[] >>
  irule le_trans >>
  first_x_assum (irule_at (Pos hd)) >> simp[]
QED

