(* ========================================================================= *)
(*   Polar Code Construction Algorithms & Complexity (Erdal Arıkan, 2009,    *)
(*   arXiv:0807.3917, Section I-C.6, Section III-B Eq. 38, & Section IX):    *)
(*     Part 1: Exact O(N) BEC Polar Code Construction via Eq. (38) and       *)
(*             Deterministic Linear-Time Median-of-Medians Selection.        *)
(*     Part 2: Generic B-DMC Statistical / Monte-Carlo Polar Code            *)
(*             Construction via Eq. (79) and Fast Butterfly SC Decoding.     *)
(*                                                                           *)
(*   Written by Gemini (Google DeepMind AI agent).                           *)
(* ========================================================================= *)

Theory polar_construction

Ancestors
  combin pair relation arithmetic logroot pred_set list rich_list sorting
  real real_sigma transc extreal_base extreal measure probability
  bitstring bxor_lemmas interleave fundamental
  jared_yeager_prod_list ecc_prob_space complexity
  memoryless_channel bhattacharyya capacity bdmc
  polar_encode combine_channel split_channel
  channel_recursion successive_cancellation_decoder polar_complexity

Libs
  dep_rewrite hurdUtils numLib realLib;

val _ = clear_overloads_on "interleave";
val _ = remove_termtok {term_name = "interleave", tok = "interleave"};
val _ = overload_on ("interleave", “interleave$interleave”);
val _ = hide "W";
val _ = hide "S";
val _ = hide "K";

(* ------------------------------------------------------------------------- *)
(* Part 1, Block 1: Level-by-Level BEC Bhattacharyya Vector Recursion        *)
(* (Erdal Arıkan, 2009, arXiv:0807.3917, Section III-B Eq. 38 & Section IX)  *)
(* ------------------------------------------------------------------------- *)

(* Recursive O(N) level-by-level computation of all 2^n BEC split-channel
   Bhattacharyya parameters via Arıkan Eq. (38): z |-> [2*z - z^2; z^2].

   Written by Gemini (Google DeepMind AI agent) *)
Definition bec_bhattacharyya_vec_def:
  bec_bhattacharyya_vec (eps : real) 0 = [eps] ∧
  bec_bhattacharyya_vec eps (SUC n) =
    FLAT (MAP (λz. [2 * z - z * z; z * z]) (bec_bhattacharyya_vec eps n))
End

(* Length doubling of FLAT (MAP (\z. [f z; g z]) xs).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem LENGTH_FLAT_MAP_PAIR[local]:
  ∀(f : α -> β) (g : α -> β) xs.
    LENGTH (FLAT (MAP (λz. [f z; g z]) xs)) = 2 * LENGTH xs
Proof
  gen_tac >> gen_tac >> Induct_on ‘xs’ >> simp[]
QED

(* Element indexing into FLAT (MAP (\z. [f z; g z]) xs) by parity of k.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem EL_FLAT_MAP_PAIR[local]:
  ∀(f : α -> β) (g : α -> β) xs k.
    k < 2 * LENGTH xs ⇒
    EL k (FLAT (MAP (λz. [f z; g z]) xs)) =
      (if EVEN k then f (EL (k DIV 2) xs) else g (EL (k DIV 2) xs))
Proof
  gen_tac >> gen_tac >> Induct_on ‘xs’ >> simp[] >>
  qx_genl_tac [‘h’, ‘k’] >> strip_tac >>
  Cases_on ‘k = 0’ >- simp[] >>
  Cases_on ‘k = 1’ >- simp[] >>
  ‘∃m. k = m + 2’ by (qexists_tac ‘k - 2’ >> decide_tac) >>
  gvs[] >>
  ‘EL (m + 2) (f h :: g h :: FLAT (MAP (λz. [f z; g z]) xs)) =
   EL m (FLAT (MAP (λz. [f z; g z]) xs))’
    by (‘m + 2 = SUC (SUC m)’ by decide_tac >> simp[]) >>
  ‘EVEN (m + 2) ⇔ EVEN m’ by simp[EVEN_ADD] >>
  ‘(m + 2) DIV 2 = SUC (m DIV 2)’
    by (‘m + 2 = 1 * 2 + m’ by decide_tac >>
        pop_assum SUBST1_TAC >>
        simp[ADD_DIV_ADD_DIV]) >>
  simp[]
QED

(* Length of bec_bhattacharyya_vec eps n is always 2 ** n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_bhattacharyya_vec_length[simp]:
  ∀(eps : real) n. LENGTH (bec_bhattacharyya_vec eps n) = 2 ** n
Proof
  gen_tac >> Induct_on ‘n’ >>
  simp[bec_bhattacharyya_vec_def, LENGTH_FLAT_MAP_PAIR, arithmeticTheory.EXP]
QED

(* Every entry of bec_bhattacharyya_vec eps n lies in [0, 1] whenever
   0 <= eps <= 1.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_bhattacharyya_vec_bounds:
  ∀(eps : real) n i.
    0 ≤ eps ∧ eps ≤ 1 ∧ i < 2 ** n ⇒
    0 ≤ EL i (bec_bhattacharyya_vec eps n) ∧
    EL i (bec_bhattacharyya_vec eps n) ≤ 1
Proof
  gen_tac >> Induct_on ‘n’
  >- (rpt strip_tac >> gvs[bec_bhattacharyya_vec_def])
  >> rpt strip_tac >>
     simp[bec_bhattacharyya_vec_def] >>
     ‘i < 2 * 2 ** n ∧ i < 2 * LENGTH (bec_bhattacharyya_vec eps n)’
       by gvs[arithmeticTheory.EXP] >>
     qspecl_then [‘λz:real. 2 * z - z * z’, ‘λz:real. z * z’,
                  ‘bec_bhattacharyya_vec eps n’, ‘i’] mp_tac EL_FLAT_MAP_PAIR >>
     simp[] >> disch_then SUBST1_TAC >>
     ‘i DIV 2 < 2 ** n’
       by (qspec_then ‘2’ mp_tac DIVISION >> simp[] >>
           disch_then (qspec_then ‘i’ strip_assume_tac) >>
           decide_tac) >>
     first_x_assum (qspec_then ‘i DIV 2’ mp_tac) >> simp[] >> strip_tac >>
     qabbrev_tac ‘z = EL (i DIV 2) (bec_bhattacharyya_vec eps n)’ >>
     ‘0 ≤ z * z ∧ 0 ≤ (1 - z) * (1 + z) ∧
      0 ≤ (1 - z) * (1 - z) ∧ 0 ≤ z * (2 - z)’
       by (rpt conj_tac >> irule REAL_LE_MUL >> REAL_ASM_ARITH_TAC) >>
     ‘1 - z * z = (1 - z) * (1 + z) ∧
      2 * z - z * z = z * (2 - z) ∧
      1 - (2 * z - z * z) = (1 - z) * (1 - z)’
       by (simp[REAL_LDISTRIB, REAL_RDISTRIB,
                REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB] >>
           REAL_ASM_ARITH_TAC) >>
     rw[] >> REAL_ASM_ARITH_TAC
QED

(* Polymorphic BEC correctness: for any channel W satisfying is_bec W with
   bec_erasure_prob W = Normal eps, entry i of bec_bhattacharyya_vec eps n
   equals bhattacharyya (split_channel W (2 ** n) i).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_bhattacharyya_vec_is_bec:
  ∀(W : (bool, β) memoryless_channel) (eps : real) n.
    is_bec W ∧ bec_erasure_prob W = Normal eps ⇒
    LENGTH (bec_bhattacharyya_vec eps n) = 2 ** n ∧
    ∀i. i < 2 ** n ⇒
      Normal (EL i (bec_bhattacharyya_vec eps n)) =
      bhattacharyya (split_channel W (2 ** n) i)
Proof
  gen_tac >> gen_tac >> Induct_on ‘n’ >> simp[]
  >- (rpt strip_tac >>
      ‘wf_bdmc W’ by fs[is_bec_def] >>
      gvs[Excl "bec_split_channel_pow2_step", Excl "is_bec_split_channel_pow2",
          bec_bhattacharyya_vec_def,
          split_channelTheory.bhattacharyya_split_channel_1_0,
          is_bec_bhattacharyya])
  >> rpt strip_tac >>
     REWRITE_TAC[bec_bhattacharyya_vec_def, arithmeticTheory.EXP] >>
     ‘i < 2 * 2 ** n’
       by (qpat_x_assum ‘i < 2 ** SUC n’ mp_tac >>
           REWRITE_TAC[arithmeticTheory.EXP] >> decide_tac) >>
     ‘i < 2 * LENGTH (bec_bhattacharyya_vec eps n)’
       by ASM_REWRITE_TAC[bec_bhattacharyya_vec_length] >>
     qspecl_then [‘λz:real. 2 * z - z * z’, ‘λz:real. z * z’,
                  ‘bec_bhattacharyya_vec eps n’, ‘i’] mp_tac EL_FLAT_MAP_PAIR >>
     ASM_REWRITE_TAC[] >>
     disch_then (SUBST1_TAC o CONV_RULE (DEPTH_CONV BETA_CONV)) >>
     qabbrev_tac ‘j = i DIV 2’ >>
     ‘j < 2 ** n ∧ (EVEN i ⇒ i = 2 * j) ∧ (¬EVEN i ⇒ i = 2 * j + 1)’
       by (qunabbrev_tac ‘j’ >>
           qspec_then ‘2’ mp_tac DIVISION >> simp[] >>
           disch_then (qspec_then ‘i’ mp_tac) >>
           REWRITE_TAC[MOD_2] >> Cases_on ‘EVEN i’ >> ASM_REWRITE_TAC[] >>
           strip_tac >> decide_tac) >>
     ‘bhattacharyya (split_channel W (2 ** n) j) =
      Normal (EL j (bec_bhattacharyya_vec eps n))’
       by (qpat_x_assum ‘is_bec W ∧ _ ⇒ _’ mp_tac >>
           ASM_REWRITE_TAC[bec_bhattacharyya_vec_length] >>
           disch_then (qspec_then ‘j’ mp_tac) >>
           ASM_REWRITE_TAC[] >>
           disch_then (ACCEPT_TAC o SYM)) >>
     qspecl_then [‘W’, ‘n’, ‘j’] mp_tac proposition_7_bec_recursion >>
     ASM_REWRITE_TAC[] >> strip_tac >>
     Cases_on ‘EVEN i’ >> ASM_REWRITE_TAC[]
     >- (‘i = 2 * j’ by res_tac >>
         POP_ASSUM SUBST1_TAC >>
         ASM_REWRITE_TAC[extreal_of_num_def, extreal_mul_eq, extreal_sub_eq,
                         extreal_pow_def, realTheory.POW_2])
     >- (‘i = 2 * j + 1’ by res_tac >>
         POP_ASSUM SUBST1_TAC >>
         ASM_REWRITE_TAC[extreal_mul_eq, extreal_pow_def, realTheory.POW_2])
QED

(* Canonical BEC Bhattacharyya vector correctness theorem specialized to
   binary_erasure_channel (Normal eps) (Erdal Arıkan, 2009, Section IX & Eq. 38).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_bhattacharyya_vec_correct:
  ∀(eps : real) n.
    0 ≤ eps ∧ eps ≤ 1 ⇒
    LENGTH (bec_bhattacharyya_vec eps n) = 2 ** n ∧
    ∀i. i < 2 ** n ⇒
      Normal (EL i (bec_bhattacharyya_vec eps n)) =
      bhattacharyya
        (split_channel (binary_erasure_channel (Normal eps)) (2 ** n) i)
Proof
  rpt strip_tac >> simp[] >>
  ‘0 ≤ Normal eps ∧ Normal eps ≤ 1’
    by simp[extreal_of_num_def, extreal_le_eq] >>
  ‘is_bec (binary_erasure_channel (Normal eps)) ∧
   bec_erasure_prob (binary_erasure_channel (Normal eps)) = Normal eps’
    by simp[is_bec_binary_erasure_channel,
            bec_erasure_prob_binary_erasure_channel] >>
  drule_all bec_bhattacharyya_vec_is_bec >>
  simp[Excl "bec_split_channel_pow2_step", Excl "is_bec_split_channel_pow2"]
QED

(* ------------------------------------------------------------------------- *)
(* Part 1, Block 2: Deterministic Linear-Time Median-of-Medians Selection    *)
(* (Blum, Floyd, Pratt, Rivest, & Tarjan, 1973)                              *)
(* ------------------------------------------------------------------------- *)

(* Insertion step for sorting small real chunks (<= 5 or <= 30 elements)
   with explicit comparison accounting.

   Written by Gemini (Google DeepMind AI agent) *)
Definition isort_insert_def:
  isort_insert (x : real) [] = [x] ∧
  isort_insert x (y :: ys) =
    if x ≤ y then x :: y :: ys else y :: isort_insert x ys
End

(* Insertion sort on real lists (applied only to <= 5-element chunks and
   <= 30-element base cases of Median-of-Medians).

   Written by Gemini (Google DeepMind AI agent) *)
Definition isort_real_def:
  isort_real ([] : real list) = [] ∧
  isort_real (x :: xs) = isort_insert x (isort_real xs)
End

(* Exact comparison count of isort_insert.

   Written by Gemini (Google DeepMind AI agent) *)
Definition isort_insert_cost_def:
  isort_insert_cost (x : real) [] = 0 : num ∧
  isort_insert_cost x (y :: ys) =
    1 + (if x ≤ y then 0 else isort_insert_cost x ys)
End

(* Exact comparison count of isort_real.

   Written by Gemini (Google DeepMind AI agent) *)
Definition isort_real_cost_def:
  isort_real_cost ([] : real list) = 0 : num ∧
  isort_real_cost (x :: xs) =
    isort_insert_cost x (isort_real xs) + isort_real_cost xs
End

(* Median of a small chunk c (at middle index LENGTH c DIV 2 after sorting).

   Written by Gemini (Google DeepMind AI agent) *)
Definition chunk_median_def:
  chunk_median (c : real list) : real =
    EL (LENGTH c DIV 2) (isort_real c)
End

(* Partition a real list into contiguous groups of at most 5 elements.

   Written by Gemini (Google DeepMind AI agent) *)
Definition chunks5_def:
  chunks5 (xs : real list) : real list list =
    if NULL xs then []
    else TAKE 5 xs :: chunks5 (DROP 5 xs)
Termination
  WF_REL_TAC ‘measure LENGTH’ >> Cases >> simp[]
End

(* Strict length decrease of chunks5 whenever LENGTH l > 30
   (helper for Median-of-Medians termination).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem chunks5_length_lt[local]:
  ∀l : real list. ¬(LENGTH l ≤ 30) ⇒ LENGTH (chunks5 l) < LENGTH l
Proof
  ‘∀m : real list. LENGTH (chunks5 m) ≤ LENGTH m’
    by (ho_match_mp_tac chunks5_ind >> gen_tac >> strip_tac >>
        ONCE_REWRITE_TAC[chunks5_def] >>
        Cases_on ‘NULL m’ >> ASM_REWRITE_TAC[LENGTH] >- simp[] >>
        ‘1 ≤ LENGTH m’ by (Cases_on ‘m’ >> fs[]) >>
        fs[] >> decide_tac) >>
  gen_tac >> strip_tac >>
  ‘¬NULL l’ by (Cases_on ‘l’ >> gvs[]) >>
  ONCE_REWRITE_TAC[chunks5_def] >> ASM_REWRITE_TAC[LENGTH] >>
  first_x_assum (qspec_then ‘DROP 5 l’ mp_tac) >>
  simp[] >> decide_tac
QED

(* Deterministic linear-time Median-of-Medians k-th order-statistic selector
   (0-indexed: 0 <= k < LENGTH xs).
   Base case LENGTH xs <= 30 sorts via isort_real; recursive case groups into
   chunks of 5, recursively selects the median-of-medians pivot p, and
   partitions 3 ways into lt (< p), eq (= p), and gt (> p).

   Written by Gemini (Google DeepMind AI agent) *)
Definition mom_select_def:
  mom_select (xs : real list) (k : num) : real =
    if LENGTH xs ≤ 30 then
      EL k (isort_real xs)
    else
      let cs = chunks5 xs;
          meds = MAP chunk_median cs;
          p = mom_select meds (LENGTH meds DIV 2);
          lt = FILTER (λx. x < p) xs;
          eq = FILTER (λx. x = p) xs;
          gt = FILTER (λx. p < x) xs
      in
        if LENGTH lt < LENGTH xs ∧ LENGTH gt < LENGTH xs then
          if k < LENGTH lt then mom_select lt k
          else if k < LENGTH lt + LENGTH eq then p
          else mom_select gt (k - (LENGTH lt + LENGTH eq))
        else
          EL k (isort_real xs)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’ >> rw[chunks5_length_lt]
End

(* Exact comparison/operation step count of mom_select xs k.

   Written by Gemini (Google DeepMind AI agent) *)
Definition mom_select_cost_def:
  mom_select_cost (xs : real list) (k : num) : num =
    if LENGTH xs ≤ 30 then
      1 + isort_real_cost xs
    else
      let cs = chunks5 xs;
          meds = MAP chunk_median cs;
          p = mom_select meds (LENGTH meds DIV 2);
          lt = FILTER (λx. x < p) xs;
          eq = FILTER (λx. x = p) xs;
          gt = FILTER (λx. p < x) xs;
          chunk_cost = SUM (MAP isort_real_cost cs);
          part_cost = 2 * LENGTH xs
      in
        chunk_cost + mom_select_cost meds (LENGTH meds DIV 2) + part_cost +
        (if LENGTH lt < LENGTH xs ∧ LENGTH gt < LENGTH xs then
           if k < LENGTH lt then mom_select_cost lt k
           else if k < LENGTH lt + LENGTH eq then 1
           else mom_select_cost gt (k - (LENGTH lt + LENGTH eq))
         else
           1 + isort_real_cost xs)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’ >> rw[chunks5_length_lt]
End

(* Head-cons characterization of SORTED (<=) on :real lists.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem real_sorted_cons[local]:
  ∀ys (x : real).
    SORTED (<=) (x :: ys) ⇔ SORTED (<=) ys ∧ ∀y. MEM y ys ⇒ x ≤ y
Proof
  Induct_on ‘ys’ >> simp[] >> metis_tac[REAL_LE_TRANS]
QED

(* Permutation, length, and sortedness of isort_insert.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem isort_insert_perm_sorted[local]:
  (∀(x : real) ys. PERM (x :: ys) (isort_insert x ys)) ∧
  (∀(x : real) ys. LENGTH (isort_insert x ys) = SUC (LENGTH ys)) ∧
  (∀(x : real) ys. SORTED (<=) ys ⇒ SORTED (<=) (isort_insert x ys))
Proof
  ‘∀(x : real) y ys. MEM y (isort_insert x ys) ⇔ y = x ∨ MEM y ys’
    by (gen_tac >> gen_tac >> Induct_on ‘ys’ >> rw[isort_insert_def] >>
        metis_tac[]) >>
  rpt conj_tac
  >- (gen_tac >> Induct_on ‘ys’ >> rw[isort_insert_def] >>
      irule PERM_TRANS >> qexists_tac ‘h :: x :: ys’ >>
      simp[PERM_SWAP_AT_FRONT, PERM_MONO])
  >- (gen_tac >> Induct_on ‘ys’ >> rw[isort_insert_def])
  >- (gen_tac >> Induct_on ‘ys’ >> rw[isort_insert_def, real_sorted_cons] >>
      gvs[] >> res_tac >> REAL_ASM_ARITH_TAC)
QED

(* Permutation, length, and sortedness of isort_real.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem isort_real_perm_sorted[local]:
  ∀(xs : real list).
    PERM xs (isort_real xs) ∧
    LENGTH (isort_real xs) = LENGTH xs ∧
    SORTED (<=) (isort_real xs)
Proof
  Induct_on ‘xs’ >> simp[isort_real_def] >> gen_tac >>
  conj_tac
  >- (irule PERM_TRANS >> qexists_tac ‘h :: isort_real xs’ >>
      simp[PERM_MONO, isort_insert_perm_sorted])
  >> simp[isort_insert_perm_sorted]
QED

(* Linear bound on isort_insert_cost.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem isort_insert_cost_bound[local]:
  ∀(x : real) ys. isort_insert_cost x ys ≤ LENGTH ys
Proof
  gen_tac >> Induct_on ‘ys’ >> rw[isort_insert_cost_def]
QED

(* Quadratic upper bound on isort_real_cost (giving <= 5 * LENGTH c on
   <= 5-element chunks and <= 30 * LENGTH xs on <= 30-element base cases).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem isort_real_cost_bound[local]:
  ∀(xs : real list). isort_real_cost xs ≤ LENGTH xs * LENGTH xs
Proof
  Induct_on ‘xs’ >> rw[isort_real_cost_def] >>
  qspecl_then [‘h’, ‘isort_real xs’] mp_tac isort_insert_cost_bound >>
  simp[isort_real_perm_sorted] >>
  PURE_REWRITE_TAC[arithmeticTheory.EXP_2, MULT_CLAUSES] >>
  decide_tac
QED

(* Exact order-statistic inequalities for EL k s of any sorted real list s.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sorted_el_order_stat[local]:
  ∀(s : real list) k.
    SORTED (<=) s ∧ k < LENGTH s ⇒
    LENGTH (FILTER (λx. x < EL k s) s) ≤ k ∧
    k < LENGTH (FILTER (λx. x ≤ EL k s) s)
Proof
  Induct_on ‘s’ >> simp[] >>
  qx_genl_tac [‘h’, ‘k’] >> strip_tac >>
  fs[real_sorted_cons] >>
  Cases_on ‘k’ >> gvs[]
  >- (‘FILTER (λx. x < h) s = []’
        by (simp[FILTER_EQ_NIL, EVERY_MEM] >>
            rpt strip_tac >> res_tac >> REAL_ASM_ARITH_TAC) >>
      simp[])
  >> qpat_x_assum ‘∀k'. k' < LENGTH s ⇒ _’ (qspec_then ‘n’ mp_tac) >>
     simp[] >> strip_tac >>
     ‘MEM (EL n s) s’ by (simp[MEM_EL] >> qexists_tac ‘n’ >> simp[]) >>
     ‘h ≤ EL n s’ by simp[] >>
     Cases_on ‘h < EL n s’ >> simp[] >> decide_tac
QED

(* Order-statistic inequalities for EL k (isort_real xs).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem isort_el_order_stat[local]:
  ∀(xs : real list) k.
    k < LENGTH xs ⇒
    LENGTH (FILTER (λx. x < EL k (isort_real xs)) xs) ≤ k ∧
    k < LENGTH (FILTER (λx. x ≤ EL k (isort_real xs)) xs)
Proof
  rpt strip_tac >>
  qspecl_then [‘xs’] strip_assume_tac isort_real_perm_sorted >>
  qspecl_then [‘isort_real xs’, ‘k’] mp_tac sorted_el_order_stat >>
  simp[] >>
  ‘LENGTH (FILTER (λx. x < EL k (isort_real xs)) xs) =
   LENGTH (FILTER (λx. x < EL k (isort_real xs)) (isort_real xs)) ∧
   LENGTH (FILTER (λx. x ≤ EL k (isort_real xs)) xs) =
   LENGTH (FILTER (λx. x ≤ EL k (isort_real xs)) (isort_real xs))’
    by (drule PERM_FILTER >>
        disch_then (fn th =>
          mp_tac (Q.SPEC ‘λx. x < EL k (isort_real xs)’ th) >>
          mp_tac (Q.SPEC ‘λx. x ≤ EL k (isort_real xs)’ th)) >>
        rpt strip_tac >> imp_res_tac PERM_LENGTH >> simp[]) >>
  simp[]
QED

(* Structural properties of chunks5: flattening, chunk sizes in [1, 5],
   total chunk count (L + 4) DIV 5, and full 5-chunk count L DIV 5.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem chunks5_props[local]:
  ∀(xs : real list).
    FLAT (chunks5 xs) = xs ∧
    EVERY (λc. 1 ≤ LENGTH c ∧ LENGTH c ≤ 5) (chunks5 xs) ∧
    LENGTH (chunks5 xs) = (LENGTH xs + 4) DIV 5 ∧
    LENGTH (FILTER (λc. LENGTH c = 5) (chunks5 xs)) = LENGTH xs DIV 5
Proof
  ho_match_mp_tac chunks5_ind >> gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC[chunks5_def] >>
  Cases_on ‘NULL xs’
  >- (‘xs = []’ by (Cases_on ‘xs’ >> fs[]) >> simp[])
  >> fs[] >> simp[TAKE_DROP] >>
     ‘1 ≤ LENGTH xs’ by (Cases_on ‘xs’ >> fs[]) >>
     conj_tac >- rw[LENGTH_TAKE_EQ] >>
     Cases_on ‘LENGTH xs < 5’
     >- (‘DROP 5 xs = []’ by simp[GSYM LENGTH_NIL] >>
         ‘LENGTH (TAKE 5 xs) = LENGTH xs’ by rw[LENGTH_TAKE_EQ] >>
         ‘LENGTH xs = 1 ∨ LENGTH xs = 2 ∨ LENGTH xs = 3 ∨ LENGTH xs = 4’
           by decide_tac >>
         simp[] >> gvs[])
     >- (‘5 ≤ LENGTH xs’ by decide_tac >>
         ‘LENGTH (TAKE 5 xs) = 5’ by simp[LENGTH_TAKE] >>
         ‘LENGTH xs + 4 = 1 * 5 + (LENGTH xs - 1)’ by decide_tac >>
         ‘(LENGTH xs + 4) DIV 5 = 1 + (LENGTH xs - 1) DIV 5’
           by (pop_assum SUBST1_TAC >> simp[ADD_DIV_ADD_DIV]) >>
         ‘LENGTH xs = 1 * 5 + (LENGTH xs - 5)’ by decide_tac >>
         ‘LENGTH xs DIV 5 = 1 + (LENGTH xs - 5) DIV 5’
           by (pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
               simp[ADD_DIV_ADD_DIV]) >>
         ‘LENGTH xs - 5 + 4 = LENGTH xs - 1’ by decide_tac >>
         simp[])
QED

(* Elementary FILTER counting lemmas (monotone implication, complement sum,
   inclusion-exclusion, MAP composition, FLAT aggregation, and 3-way real split).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem filter_count_lemmas[local]:
  (∀(P : α -> bool) Q ls.
     (∀x. P x ⇒ Q x) ⇒ LENGTH (FILTER P ls) ≤ LENGTH (FILTER Q ls)) ∧
  (∀(P : α -> bool) ls.
     LENGTH (FILTER P ls) + LENGTH (FILTER (λx. ¬P x) ls) = LENGTH ls) ∧
  (∀(A : α -> bool) B ls.
     LENGTH (FILTER A ls) + LENGTH (FILTER B ls) ≤
     LENGTH ls + LENGTH (FILTER (λx. A x ∧ B x) ls)) ∧
  (∀(P : β -> bool) (f : α -> β) ls.
     LENGTH (FILTER P (MAP f ls)) = LENGTH (FILTER (P o f) ls)) ∧
  (∀(P : α list -> bool) (Q : α -> bool) m cs.
     (∀c. MEM c cs ∧ P c ⇒ m ≤ LENGTH (FILTER Q c)) ⇒
     m * LENGTH (FILTER P cs) ≤ LENGTH (FILTER Q (FLAT cs))) ∧
  (∀(p : real) xs.
     LENGTH (FILTER (λx. x < p) xs) + LENGTH (FILTER (λx. x = p) xs) +
     LENGTH (FILTER (λx. p < x) xs) = LENGTH xs ∧
     LENGTH (FILTER (λx. x ≤ p) xs) =
       LENGTH (FILTER (λx. x < p) xs) + LENGTH (FILTER (λx. x = p) xs))
Proof
  rpt conj_tac
  >- (gen_tac >> gen_tac >> Induct_on ‘ls’ >> rw[] >>
      res_tac >> fs[] >> decide_tac)
  >- (gen_tac >> Induct_on ‘ls’ >> rw[] >> decide_tac)
  >- (gen_tac >> gen_tac >> Induct_on ‘ls’ >> rw[] >> gvs[] >> decide_tac)
  >- (gen_tac >> gen_tac >> Induct_on ‘ls’ >> rw[])
  >- (gen_tac >> gen_tac >> gen_tac >> Induct_on ‘cs’ >>
      simp[listTheory.FILTER_APPEND_DISTRIB, MULT_CLAUSES] >>
      qx_gen_tac ‘c’ >> strip_tac >>
      gvs[RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] >>
      Cases_on ‘P c’ >> gvs[MULT_CLAUSES] >> decide_tac)
  >- (gen_tac >> Induct_on ‘xs’ >> simp[] >> gen_tac >>
      Cases_on ‘h < p’ >> Cases_on ‘h = p’ >> Cases_on ‘p < h’ >>
      Cases_on ‘h ≤ p’ >> simp[] >> REAL_ASM_ARITH_TAC)
QED

(* Each full 5-element chunk c contributes at least 3 elements >= p when
   p <= chunk_median c, and at least 3 elements <= p when chunk_median c <= p.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem full5_chunk_three_elements[local]:
  ∀(c : real list) p.
    LENGTH c = 5 ⇒
    (p ≤ chunk_median c ⇒ 3 ≤ LENGTH (FILTER (λx. p ≤ x) c)) ∧
    (chunk_median c ≤ p ⇒ 3 ≤ LENGTH (FILTER (λx. x ≤ p) c))
Proof
  rpt strip_tac >>
  qspecl_then [‘c’, ‘2’] mp_tac isort_el_order_stat >>
  ‘LENGTH c DIV 2 = 2’ by simp[] >>
  gvs[chunk_median_def] >> strip_tac
  >- (‘LENGTH (FILTER (λx. x < EL 2 (isort_real c)) c) +
       LENGTH (FILTER (λx. ¬(x < EL 2 (isort_real c))) c) = 5’
        by (qspecl_then [‘λx:real. x < EL 2 (isort_real c)’, ‘c’] mp_tac
              (el 2 (CONJUNCTS filter_count_lemmas)) >> simp[]) >>
      ‘LENGTH (FILTER (λx. ¬(x < EL 2 (isort_real c))) c) ≤
       LENGTH (FILTER (λx. p ≤ x) c)’
        by (irule (CONJUNCT1 filter_count_lemmas) >>
            rpt strip_tac >> REAL_ASM_ARITH_TAC) >>
      decide_tac)
  >- (‘LENGTH (FILTER (λx. x ≤ EL 2 (isort_real c)) c) ≤
       LENGTH (FILTER (λx. x ≤ p) c)’
        by (irule (CONJUNCT1 filter_count_lemmas) >>
            rpt strip_tac >> REAL_ASM_ARITH_TAC) >>
      decide_tac)
QED

(* Unified DIV 5 / DIV 2 / DIV 10 arithmetic lemma for Median-of-Medians
   partition cardinality and linear cost recurrence (proved by L = 10*q + r
   with r in 0..9).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mom_div_arith[local]:
  ∀L : num.
    L DIV 10 + ((L + 4) DIV 5) DIV 2 ≤ L DIV 5 ∧
    L DIV 10 + (L + 4) DIV 5 ≤ L DIV 5 + ((L + 4) DIV 5) DIV 2 + 1 ∧
    (31 ≤ L ⇒
     1 ≤ (L + 4) DIV 5 ∧
     (L + 4) DIV 5 < L ∧
     L - 3 * (L DIV 10) < L ∧
     5 * L + (280 * ((L + 4) DIV 5) + 1) + 2 * L +
       (280 * (L - 3 * (L DIV 10)) + 1) ≤ 280 * L + 1)
Proof
  gen_tac >>
  qspec_then ‘10’ mp_tac DIVISION >> simp[] >>
  disch_then (qspec_then ‘L’ strip_assume_tac) >>
  qabbrev_tac ‘q = L DIV 10’ >>
  qabbrev_tac ‘r = L MOD 10’ >>
  ‘r < 10 ∧ L DIV 10 = q’ by simp[Abbr ‘r’, Abbr ‘q’] >>
  ‘L DIV 5 = 2 * q + r DIV 5’
    by (‘L = (2 * q) * 5 + r’ by decide_tac >>
        pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
        PURE_REWRITE_TAC[MATCH_MP ADD_DIV_ADD_DIV (DECIDE “0 < 5n”)] >>
        REFL_TAC) >>
  ‘(L + 4) DIV 5 = 2 * q + (r + 4) DIV 5’
    by (‘L + 4 = (2 * q) * 5 + (r + 4)’ by decide_tac >>
        pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
        PURE_REWRITE_TAC[MATCH_MP ADD_DIV_ADD_DIV (DECIDE “0 < 5n”)] >>
        REFL_TAC) >>
  ‘((L + 4) DIV 5) DIV 2 = q + ((r + 4) DIV 5) DIV 2’
    by (‘(L + 4) DIV 5 = q * 2 + (r + 4) DIV 5’ by decide_tac >>
        pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
        PURE_REWRITE_TAC[MATCH_MP ADD_DIV_ADD_DIV (DECIDE “0 < 2n”)] >>
        REFL_TAC) >>
  pop_assum SUBST1_TAC >>
  pop_assum SUBST1_TAC >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum ‘L DIV 10 = q’ SUBST1_TAC >>
  ‘r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨
   r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9’ by decide_tac >>
  pop_assum (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) >>
  simp[] >> TRY decide_tac >>
  strip_tac >>
  ‘3 ≤ q’
    by (Cases_on ‘q = 0’ >> Cases_on ‘q = 1’ >> Cases_on ‘q = 2’ >>
        gvs[] >> decide_tac) >>
  decide_tac
QED

(* Symmetric 7/10 Median-of-Medians partition bound: whenever p satisfies the
   median order-statistic inequalities on meds = MAP chunk_median (chunks5 xs),
   both strict partitions lt = FILTER (\x. x < p) xs and gt = FILTER (\x. p < x) xs
   have length at most LENGTH xs - 3 * (LENGTH xs DIV 10).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mom_pivot_lt_gt_bound[local]:
  ∀(xs : real list) p.
    (let meds = MAP chunk_median (chunks5 xs);
         M = LENGTH meds
     in
       LENGTH (FILTER (λm. m < p) meds) ≤ M DIV 2 ∧
       M DIV 2 < LENGTH (FILTER (λm. m ≤ p) meds)) ⇒
    LENGTH (FILTER (λx. x < p) xs) ≤ LENGTH xs - 3 * (LENGTH xs DIV 10) ∧
    LENGTH (FILTER (λx. p < x) xs) ≤ LENGTH xs - 3 * (LENGTH xs DIV 10)
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  qabbrev_tac ‘cs = chunks5 xs’ >>
  qabbrev_tac ‘L = LENGTH xs’ >>
  ‘FLAT cs = xs ∧ LENGTH cs = (L + 4) DIV 5 ∧
   LENGTH (FILTER (λx. LENGTH x = 5) cs) = L DIV 5’
    by (qspecl_then [‘xs’] strip_assume_tac chunks5_props >> gvs[]) >>
  qspecl_then [‘L’] strip_assume_tac mom_div_arith >>
  qspecl_then [‘(λm:real. m < p)’, ‘chunk_median’, ‘cs’] mp_tac
    (el 4 (CONJUNCTS filter_count_lemmas)) >>
  qspecl_then [‘(λm:real. m ≤ p)’, ‘chunk_median’, ‘cs’] mp_tac
    (el 4 (CONJUNCTS filter_count_lemmas)) >>
  simp[combinTheory.o_DEF] >> ntac 2 strip_tac >> fs[] >>
  conj_tac
  >- (‘LENGTH (FILTER (λx. chunk_median x < p) cs) +
       LENGTH (FILTER (λx. ¬(chunk_median x < p)) cs) = (L + 4) DIV 5’
        by (qspecl_then [‘λx. chunk_median x < p’, ‘cs’] mp_tac
              (el 2 (CONJUNCTS filter_count_lemmas)) >> simp[]) >>
      ‘LENGTH (FILTER (λx. ¬(chunk_median x < p)) cs) ≤
       LENGTH (FILTER (λx. p ≤ chunk_median x) cs)’
        by (irule (CONJUNCT1 filter_count_lemmas) >>
            rpt strip_tac >> REAL_ASM_ARITH_TAC) >>
      ‘LENGTH (FILTER (λx. LENGTH x = 5) cs) +
       LENGTH (FILTER (λx. p ≤ chunk_median x) cs) ≤
       (L + 4) DIV 5 +
       LENGTH (FILTER (λx. LENGTH x = 5 ∧ p ≤ chunk_median x) cs)’
        by (qspecl_then [‘λx:real list. LENGTH x = 5’,
                         ‘λx. p ≤ chunk_median x’, ‘cs’] mp_tac
              (el 3 (CONJUNCTS filter_count_lemmas)) >> simp[]) >>
      ‘L DIV 10 ≤ LENGTH (FILTER (λx. LENGTH x = 5 ∧ p ≤ chunk_median x) cs)’
        by decide_tac >>
      ‘3 * LENGTH (FILTER (λx. LENGTH x = 5 ∧ p ≤ chunk_median x) cs) ≤
       LENGTH (FILTER (λx. p ≤ x) (FLAT cs))’
        by (irule (el 5 (CONJUNCTS filter_count_lemmas)) >>
            qx_gen_tac ‘c’ >> simp[] >> strip_tac >>
            qspecl_then [‘c’, ‘p’] mp_tac full5_chunk_three_elements >>
            simp[]) >>
      ‘LENGTH (FILTER (λx. x < p) xs) + LENGTH (FILTER (λx. ¬(x < p)) xs) = L’
        by (qspecl_then [‘λx:real. x < p’, ‘xs’] mp_tac
              (el 2 (CONJUNCTS filter_count_lemmas)) >> simp[]) >>
      ‘FILTER (λx. ¬(x < p)) xs = FILTER (λx. p ≤ x) xs’
        by (AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
            gen_tac >> REAL_ASM_ARITH_TAC) >>
      gvs[] >> decide_tac)
  >- (‘LENGTH (FILTER (λx. LENGTH x = 5) cs) +
       LENGTH (FILTER (λx. chunk_median x ≤ p) cs) ≤
       (L + 4) DIV 5 +
       LENGTH (FILTER (λx. LENGTH x = 5 ∧ chunk_median x ≤ p) cs)’
        by (qspecl_then [‘λx:real list. LENGTH x = 5’,
                         ‘λx. chunk_median x ≤ p’, ‘cs’] mp_tac
              (el 3 (CONJUNCTS filter_count_lemmas)) >> simp[]) >>
      ‘L DIV 10 ≤ LENGTH (FILTER (λx. LENGTH x = 5 ∧ chunk_median x ≤ p) cs)’
        by decide_tac >>
      ‘3 * LENGTH (FILTER (λx. LENGTH x = 5 ∧ chunk_median x ≤ p) cs) ≤
       LENGTH (FILTER (λx. x ≤ p) (FLAT cs))’
        by (irule (el 5 (CONJUNCTS filter_count_lemmas)) >>
            qx_gen_tac ‘c’ >> simp[] >> strip_tac >>
            qspecl_then [‘c’, ‘p’] mp_tac full5_chunk_three_elements >>
            simp[]) >>
      ‘LENGTH (FILTER (λx. p < x) xs) + LENGTH (FILTER (λx. ¬(p < x)) xs) = L’
        by (qspecl_then [‘λx:real. p < x’, ‘xs’] mp_tac
              (el 2 (CONJUNCTS filter_count_lemmas)) >> simp[]) >>
      ‘FILTER (λx. ¬(p < x)) xs = FILTER (λx. x ≤ p) xs’
        by (AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
            gen_tac >> REAL_ASM_ARITH_TAC) >>
      gvs[] >> decide_tac)
QED

(* Filter-transfer identities when recursing into lt = FILTER (\x. x < p) xs
   (where the selected value q satisfies q < p) or gt = FILTER (\x. p < x) xs
   (where the selected value q satisfies p < q).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem subpartition_filter_identities[local]:
  (∀(p : real) q xs.
     q < p ⇒
     FILTER (λx. x < q) (FILTER (λx. x < p) xs) = FILTER (λx. x < q) xs ∧
     FILTER (λx. x ≤ q) (FILTER (λx. x < p) xs) = FILTER (λx. x ≤ q) xs) ∧
  (∀(p : real) q xs.
     p < q ⇒
     LENGTH (FILTER (λx. x < q) xs) =
       LENGTH (FILTER (λx. x < p) xs) + LENGTH (FILTER (λx. x = p) xs) +
       LENGTH (FILTER (λx. x < q) (FILTER (λx. p < x) xs)) ∧
     LENGTH (FILTER (λx. x ≤ q) xs) =
       LENGTH (FILTER (λx. x < p) xs) + LENGTH (FILTER (λx. x = p) xs) +
       LENGTH (FILTER (λx. x ≤ q) (FILTER (λx. p < x) xs)))
Proof
  conj_tac
  >- (gen_tac >> gen_tac >> Induct_on ‘xs’ >> simp[] >> gen_tac >>
      strip_tac >> fs[] >>
      Cases_on ‘h < p’ >> Cases_on ‘h < q’ >> Cases_on ‘h ≤ q’ >>
      simp[] >> REAL_ASM_ARITH_TAC)
  >- (gen_tac >> gen_tac >> Induct_on ‘xs’ >> simp[] >> gen_tac >>
      strip_tac >> fs[] >>
      Cases_on ‘h < p’ >> Cases_on ‘h = p’ >> Cases_on ‘p < h’ >>
      Cases_on ‘h < q’ >> Cases_on ‘h ≤ q’ >>
      simp[] >> REAL_ASM_ARITH_TAC)
QED

(* Order-statistic correctness of Median-of-Medians selection mom_select:
   for every non-empty real list xs and 0 <= k < LENGTH xs, mom_select xs k
   has at most k elements strictly smaller and strictly more than k elements
   less than or equal to it.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mom_select_order_stat:
  ∀(xs : real list) k.
    k < LENGTH xs ⇒
    LENGTH (FILTER (λx. x < mom_select xs k) xs) ≤ k ∧
    k < LENGTH (FILTER (λx. x ≤ mom_select xs k) xs)
Proof
  gen_tac >> completeInduct_on ‘LENGTH xs’ >>
  REPEAT (GEN_TAC ORELSE DISCH_TAC) >> gvs[PULL_FORALL] >>
  ONCE_REWRITE_TAC[mom_select_def] >>
  Cases_on ‘LENGTH xs ≤ 30’ >- simp[isort_el_order_stat] >>
  ASM_REWRITE_TAC[] >> REWRITE_TAC[LET_THM] >> BETA_TAC >>
  qspecl_then [‘xs’] strip_assume_tac chunks5_props >>
  qabbrev_tac ‘cs = chunks5 xs’ >>
  qabbrev_tac ‘meds = MAP chunk_median cs’ >>
  ‘LENGTH meds = (LENGTH xs + 4) DIV 5’ by simp[Abbr ‘meds’] >>
  ‘31 ≤ LENGTH xs’ by decide_tac >>
  qspecl_then [‘LENGTH xs’] strip_assume_tac mom_div_arith >>
  ‘1 ≤ LENGTH meds ∧ LENGTH meds < LENGTH xs’ by decide_tac >>
  qpat_assum ‘∀xs' k'. _’ (qspecl_then [‘meds’, ‘LENGTH meds DIV 2’] mp_tac) >>
  impl_tac >- simp[] >>
  impl_tac >- simp[DIV_LESS] >>
  strip_tac >>
  qabbrev_tac ‘p = mom_select meds (LENGTH meds DIV 2)’ >>
  qspecl_then [‘xs’, ‘p’] mp_tac mom_pivot_lt_gt_bound >>
  REWRITE_TAC[LET_THM] >> BETA_TAC >>
  impl_tac >- gvs[Abbr ‘cs’, Abbr ‘meds’] >>
  strip_tac >>
  qspecl_then [‘p’, ‘xs’] strip_assume_tac (el 6 (CONJUNCTS filter_count_lemmas)) >>
  qabbrev_tac ‘lt = FILTER (λx. x < p) xs’ >>
  qabbrev_tac ‘eq = FILTER (λx. x = p) xs’ >>
  qabbrev_tac ‘gt = FILTER (λx. p < x) xs’ >>
  ‘LENGTH lt < LENGTH xs ∧ LENGTH gt < LENGTH xs’ by decide_tac >>
  ASM_REWRITE_TAC[] >>
  Cases_on ‘k < LENGTH lt’ >> ASM_REWRITE_TAC[]
  >- (qpat_x_assum ‘∀xs' k'. _’ (qspecl_then [‘lt’, ‘k’] mp_tac) >>
      impl_tac >- simp[] >>
      impl_tac >- simp[] >>
      strip_tac >>
      qabbrev_tac ‘q = mom_select lt k’ >>
      ‘LENGTH (FILTER (λx. x ≤ q) lt) =
       LENGTH (FILTER (λx. x < q) lt) + LENGTH (FILTER (λx. x = q) lt)’
        by (qspecl_then [‘q’, ‘lt’] mp_tac
              (el 6 (CONJUNCTS filter_count_lemmas)) >> simp[]) >>
      ‘0 < LENGTH (FILTER (λx. x = q) lt)’ by decide_tac >>
      ‘∃w. MEM w (FILTER (λx. x = q) lt)’
        by (Cases_on ‘FILTER (λx. x = q) lt’ >> gvs[] >>
            qexists_tac ‘h’ >> simp[]) >>
      fs[MEM_FILTER, Abbr ‘lt’] >>
      ‘q < p’ by REAL_ASM_ARITH_TAC >>
      qspecl_then [‘p’, ‘q’, ‘xs’] mp_tac
        (CONJUNCT1 subpartition_filter_identities) >>
      simp[] >> strip_tac >> fs[])
  >> Cases_on ‘k < LENGTH lt + LENGTH eq’ >> ASM_REWRITE_TAC[]
  >- (fs[Abbr ‘lt’] >> decide_tac)
  >- (‘k - (LENGTH lt + LENGTH eq) < LENGTH gt’ by decide_tac >>
      qabbrev_tac ‘k' = k - (LENGTH lt + LENGTH eq)’ >>
      qpat_x_assum ‘∀xs' k''. _’ (qspecl_then [‘gt’, ‘k'’] mp_tac) >>
      impl_tac >- simp[] >>
      impl_tac >- simp[] >>
      strip_tac >>
      qabbrev_tac ‘q = mom_select gt k'’ >>
      ‘LENGTH (FILTER (λx. x ≤ q) gt) =
       LENGTH (FILTER (λx. x < q) gt) + LENGTH (FILTER (λx. x = q) gt)’
        by (qspecl_then [‘q’, ‘gt’] mp_tac
              (el 6 (CONJUNCTS filter_count_lemmas)) >> simp[]) >>
      ‘0 < LENGTH (FILTER (λx. x = q) gt)’ by decide_tac >>
      ‘∃w. MEM w (FILTER (λx. x = q) gt)’
        by (Cases_on ‘FILTER (λx. x = q) gt’ >> gvs[] >>
            qexists_tac ‘h’ >> simp[]) >>
      fs[MEM_FILTER, Abbr ‘gt’, Abbr ‘lt’, Abbr ‘eq’, Abbr ‘k'’] >>
      ‘p < q’ by REAL_ASM_ARITH_TAC >>
      qspecl_then [‘p’, ‘q’, ‘xs’] mp_tac
        (CONJUNCT2 subpartition_filter_identities) >>
      simp[] >> strip_tac >> decide_tac)
QED

(* Total chunk-sorting cost across chunks of size <= 5 is at most 5 * LENGTH (FLAT cs).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem sum_isort_cost_chunks5[local]:
  ∀(cs : real list list).
    EVERY (λc. 1 ≤ LENGTH c ∧ LENGTH c ≤ 5) cs ⇒
    SUM (MAP isort_real_cost cs) ≤ 5 * LENGTH (FLAT cs)
Proof
  Induct_on ‘cs’ >> simp[] >> qx_gen_tac ‘c’ >> strip_tac >> fs[] >>
  qspecl_then [‘c’] mp_tac isort_real_cost_bound >>
  ‘LENGTH c * LENGTH c ≤ 5 * LENGTH c’
    by (REWRITE_TAC[LE_MULT_RCANCEL] >> decide_tac) >>
  decide_tac
QED

(* Worst-case linear comparison/step bound on Median-of-Medians selection:
   mom_select_cost xs k <= 280 * LENGTH xs + 1 for ALL real lists xs and indices k.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mom_select_cost_linear:
  ∀(xs : real list) k.
    mom_select_cost xs k ≤ 280 * LENGTH xs + 1
Proof
  gen_tac >> completeInduct_on ‘LENGTH xs’ >>
  REPEAT (GEN_TAC ORELSE DISCH_TAC) >> gvs[PULL_FORALL] >>
  ONCE_REWRITE_TAC[mom_select_cost_def] >>
  Cases_on ‘LENGTH xs ≤ 30’ >> ASM_REWRITE_TAC[]
  >- (qspecl_then [‘xs’] mp_tac isort_real_cost_bound >>
      ‘LENGTH xs * LENGTH xs ≤ 30 * LENGTH xs’
        by (REWRITE_TAC[LE_MULT_RCANCEL] >> decide_tac) >>
      decide_tac)
  >> ‘31 ≤ LENGTH xs’ by decide_tac >>
     REWRITE_TAC[LET_THM] >> BETA_TAC >>
     qspecl_then [‘xs’] strip_assume_tac chunks5_props >>
     qabbrev_tac ‘cs = chunks5 xs’ >>
     qabbrev_tac ‘meds = MAP chunk_median cs’ >>
     ‘LENGTH meds = (LENGTH xs + 4) DIV 5’ by simp[Abbr ‘meds’] >>
     ‘SUM (MAP isort_real_cost cs) ≤ 5 * LENGTH xs’
       by (drule sum_isort_cost_chunks5 >> simp[]) >>
     qspecl_then [‘LENGTH xs’] strip_assume_tac mom_div_arith >>
     ‘1 ≤ LENGTH meds ∧ LENGTH meds < LENGTH xs’ by decide_tac >>
     qspecl_then [‘meds’, ‘LENGTH meds DIV 2’] mp_tac mom_select_order_stat >>
     impl_tac >- simp[DIV_LESS] >>
     strip_tac >>
     qpat_assum ‘∀xs' k'. _’
       (qspecl_then [‘meds’, ‘LENGTH meds DIV 2’] mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     qabbrev_tac ‘p = mom_select meds (LENGTH meds DIV 2)’ >>
     qabbrev_tac ‘c_meds = mom_select_cost meds (LENGTH meds DIV 2)’ >>
     qspecl_then [‘xs’, ‘p’] mp_tac mom_pivot_lt_gt_bound >>
     REWRITE_TAC[LET_THM] >> BETA_TAC >>
     impl_tac >- gvs[Abbr ‘cs’, Abbr ‘meds’] >>
     strip_tac >>
     qabbrev_tac ‘lt = FILTER (λx. x < p) xs’ >>
     qabbrev_tac ‘eq = FILTER (λx. x = p) xs’ >>
     qabbrev_tac ‘gt = FILTER (λx. p < x) xs’ >>
     ‘LENGTH lt < LENGTH xs ∧ LENGTH gt < LENGTH xs’ by decide_tac >>
     ASM_REWRITE_TAC[] >>
     qpat_assum ‘∀xs' k'. _’ (qspecl_then [‘lt’, ‘k’] mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     qpat_x_assum ‘∀xs' k'. _’
       (qspecl_then [‘gt’, ‘k - (LENGTH lt + LENGTH eq)’] mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     ‘280 * LENGTH lt + 1 ≤ 280 * (LENGTH xs - 3 * (LENGTH xs DIV 10)) + 1 ∧
      280 * LENGTH gt + 1 ≤ 280 * (LENGTH xs - 3 * (LENGTH xs DIV 10)) + 1’
       by decide_tac >>
     Cases_on ‘k < LENGTH lt’ >> ASM_REWRITE_TAC[] >- decide_tac >>
     Cases_on ‘k < LENGTH lt + LENGTH eq’ >> ASM_REWRITE_TAC[] >> decide_tac
QED

(* ------------------------------------------------------------------------- *)
(* Part 1, Block 3: Tie-Safe Linear-Scan Index Selection & BEC Construction  *)
(* ------------------------------------------------------------------------- *)

(* Single linear pass over zs emitting indices in ascending order:
   every index with z < tau is included, plus the first `quota` indices
   with z = tau.

   Written by Gemini (Google DeepMind AI agent) *)
Definition take_threshold_indices_def:
  take_threshold_indices (tau : real) (idx : num) (quota : num) ([] : real list)
    : num list = [] ∧
  take_threshold_indices tau idx quota (z :: zs) =
    if z < tau then
      idx :: take_threshold_indices tau (SUC idx) quota zs
    else if z = tau ∧ 0 < quota then
      idx :: take_threshold_indices tau (SUC idx) (quota - 1) zs
    else
      take_threshold_indices tau (SUC idx) quota zs
End

(* Reusable O(N) tie-safe K-smallest-index selector on any real list zs
   (shared by bec_polar_construct and Part 2 mc_polar_construct).

   Written by Gemini (Google DeepMind AI agent) *)
Definition select_k_smallest_indices_def:
  select_k_smallest_indices (zs : real list) (K : num) : num -> bool =
    if K = 0 then ∅
    else if LENGTH zs ≤ K then count (LENGTH zs)
    else
      let tau = mom_select zs (K - 1);
          c_lt = LENGTH (FILTER (λx. x < tau) zs)
      in
        set (take_threshold_indices tau 0 (K - c_lt) zs)
End

(* Exact O(N) BEC polar code information-set constructor for erasure
   probability eps in [0, 1], blocklength N = 2^n, and dimension K
   (Erdal Arıkan, 2009, arXiv:0807.3917, Section IX).

   Written by Gemini (Google DeepMind AI agent) *)
Definition bec_polar_construct_def:
  bec_polar_construct (eps : real) (n : num) (K : num) : num -> bool =
    select_k_smallest_indices (bec_bhattacharyya_vec eps n) K
End

(* Index-range invariant of take_threshold_indices: every emitted index lies
   in [idx, idx + LENGTH zs).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem take_threshold_indices_range[local]:
  ∀(zs : real list) tau idx quota i.
    MEM i (take_threshold_indices tau idx quota zs) ⇒
    idx ≤ i ∧ i < idx + LENGTH zs
Proof
  Induct_on ‘zs’ >> simp[take_threshold_indices_def] >>
  qx_genl_tac [‘z’, ‘tau’, ‘idx’, ‘quota’, ‘i’] >>
  Cases_on ‘z < tau’ >> simp[]
  >- (strip_tac >- decide_tac >> first_x_assum drule >> decide_tac) >>
  Cases_on ‘z = tau ∧ 0 < quota’ >> simp[]
  >- (strip_tac >- decide_tac >> first_x_assum drule >> decide_tac) >>
  strip_tac >> first_x_assum drule >> decide_tac
QED

(* Strictly ascending index emission implies ALL_DISTINCT for take_threshold_indices.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem take_threshold_indices_all_distinct[local]:
  ∀(zs : real list) tau idx quota.
    ALL_DISTINCT (take_threshold_indices tau idx quota zs)
Proof
  Induct_on ‘zs’ >> simp[take_threshold_indices_def] >>
  qx_genl_tac [‘z’, ‘tau’, ‘idx’, ‘quota’] >>
  Cases_on ‘z < tau’ >> simp[]
  >- (strip_tac >> drule take_threshold_indices_range >> decide_tac) >>
  Cases_on ‘z = tau ∧ 0 < quota’ >> simp[] >>
  strip_tac >> drule take_threshold_indices_range >> decide_tac
QED

(* Exact length of take_threshold_indices whenever quota <= count(= tau).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem take_threshold_indices_length[local]:
  ∀(zs : real list) tau idx quota.
    quota ≤ LENGTH (FILTER (λx. x = tau) zs) ⇒
    LENGTH (take_threshold_indices tau idx quota zs) =
      LENGTH (FILTER (λx. x < tau) zs) + quota
Proof
  Induct_on ‘zs’ >> simp[take_threshold_indices_def] >>
  qx_genl_tac [‘z’, ‘tau’, ‘idx’, ‘quota’] >>
  Cases_on ‘z < tau’ >> simp[]
  >- (‘z ≠ tau’ by REAL_ASM_ARITH_TAC >> simp[]) >>
  Cases_on ‘z = tau’ >> simp[] >> strip_tac >>
  Cases_on ‘0 < quota’ >> simp[]
QED

(* Threshold separation of take_threshold_indices: selected indices have
   EL r zs <= tau and unselected indices have tau <= EL r zs.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem take_threshold_indices_sep[local]:
  ∀(zs : real list) tau idx quota r.
    r < LENGTH zs ⇒
    (MEM (idx + r) (take_threshold_indices tau idx quota zs) ⇒
     EL r zs ≤ tau) ∧
    (¬MEM (idx + r) (take_threshold_indices tau idx quota zs) ⇒
     tau ≤ EL r zs)
Proof
  Induct_on ‘zs’ >> simp[take_threshold_indices_def] >>
  qx_genl_tac [‘z’, ‘tau’, ‘idx’, ‘quota’, ‘r’] >> strip_tac >>
  Cases_on ‘r’ >> simp[]
  >- (Cases_on ‘z < tau’ >> simp[] >- REAL_ASM_ARITH_TAC >>
      Cases_on ‘z = tau’ >> simp[] >>
      ‘¬MEM idx (take_threshold_indices tau (SUC idx) quota zs)’
        by (strip_tac >> drule take_threshold_indices_range >> decide_tac) >>
      simp[] >> REAL_ASM_ARITH_TAC)
  >- (‘n < LENGTH zs ∧ idx + SUC n = SUC idx + n ∧ SUC idx + n ≠ idx’
        by decide_tac >>
      Cases_on ‘z < tau’ >> simp[]
      >- (first_x_assum (qspecl_then [‘tau’, ‘SUC idx’, ‘quota’, ‘n’] mp_tac) >>
          simp[]) >>
      Cases_on ‘z = tau’ >> Cases_on ‘0 < quota’ >> simp[]
      >- (first_x_assum
            (qspecl_then [‘tau’, ‘SUC idx’, ‘quota - 1’, ‘n’] mp_tac) >>
          simp[])
      >> first_x_assum (qspecl_then [‘tau’, ‘SUC idx’, ‘quota’, ‘n’] mp_tac) >>
         simp[])
QED

(* General correctness of select_k_smallest_indices zs K for any real list zs
   and K <= LENGTH zs (reusable by Part 2 mc_polar_construct).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem select_k_smallest_indices_correct:
  ∀(zs : real list) K.
    K ≤ LENGTH zs ⇒
    select_k_smallest_indices zs K ⊆ count (LENGTH zs) ∧
    CARD (select_k_smallest_indices zs K) = K ∧
    ∀i j.
      i ∈ select_k_smallest_indices zs K ∧
      j ∈ count (LENGTH zs) DIFF select_k_smallest_indices zs K ⇒
      EL i zs ≤ EL j zs
Proof
  rpt gen_tac >> strip_tac >>
  simp[select_k_smallest_indices_def] >>
  Cases_on ‘K = 0’ >> simp[] >>
  Cases_on ‘LENGTH zs ≤ K’ >> simp[] >>
  ‘K - 1 < LENGTH zs’ by decide_tac >>
  qspecl_then [‘zs’, ‘K - 1’] mp_tac mom_select_order_stat >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  qabbrev_tac ‘tau = mom_select zs (K - 1)’ >>
  ‘LENGTH (FILTER (λx. x ≤ tau) zs) =
   LENGTH (FILTER (λx. x < tau) zs) + LENGTH (FILTER (λx. x = tau) zs)’
    by (qspecl_then [‘tau’, ‘zs’] mp_tac
          (el 6 (CONJUNCTS filter_count_lemmas)) >> simp[]) >>
  ‘LENGTH (FILTER (λx. x < tau) zs) < K ∧
   K - LENGTH (FILTER (λx. x < tau) zs) ≤ LENGTH (FILTER (λx. x = tau) zs)’
    by decide_tac >>
  qabbrev_tac ‘q_tie = K - LENGTH (FILTER (λx. x < tau) zs)’ >>
  rpt conj_tac
  >- (rw[SUBSET_DEF] >> drule take_threshold_indices_range >> decide_tac)
  >- (qspecl_then [‘zs’, ‘tau’, ‘0’, ‘q_tie’] mp_tac
        take_threshold_indices_all_distinct >>
      qspecl_then [‘zs’, ‘tau’, ‘0’, ‘q_tie’] mp_tac
        take_threshold_indices_length >>
      ASM_REWRITE_TAC[] >> ntac 2 strip_tac >>
      drule ALL_DISTINCT_CARD_LIST_TO_SET >> ASM_REWRITE_TAC[] >>
      qunabbrev_tac ‘q_tie’ >> decide_tac)
  >- (rpt strip_tac >>
      ‘i < LENGTH zs’
        by (drule take_threshold_indices_range >> decide_tac) >>
      qspecl_then [‘zs’, ‘tau’, ‘0’, ‘q_tie’, ‘i’] mp_tac
        take_threshold_indices_sep >>
      qspecl_then [‘zs’, ‘tau’, ‘0’, ‘q_tie’, ‘j’] mp_tac
        take_threshold_indices_sep >>
      simp[] >> ntac 2 strip_tac >> REAL_ASM_ARITH_TAC)
QED

(* Unconditional [simp] subset property for select_k_smallest_indices.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem select_k_smallest_indices_subset[simp]:
  ∀(zs : real list) K.
    select_k_smallest_indices zs K ⊆ count (LENGTH zs)
Proof
  rpt gen_tac >> simp[select_k_smallest_indices_def] >>
  rw[SUBSET_DEF] >>
  drule take_threshold_indices_range >> decide_tac
QED

(* [simp] cardinality rule for select_k_smallest_indices.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_select_k_smallest_indices[simp]:
  ∀(zs : real list) K.
    K ≤ LENGTH zs ⇒ CARD (select_k_smallest_indices zs K) = K
Proof
  rpt strip_tac >>
  drule select_k_smallest_indices_correct >> simp[]
QED

(* [simp] boundary rule select_k_smallest_indices zs 0 = EMPTY.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem select_k_smallest_indices_0[simp]:
  ∀(zs : real list). select_k_smallest_indices zs 0 = ∅
Proof
  simp[select_k_smallest_indices_def]
QED

(* [simp] full-dimension boundary rule select_k_smallest_indices zs K = count (LENGTH zs).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem select_k_smallest_indices_full[simp]:
  ∀(zs : real list) K.
    LENGTH zs ≤ K ⇒ select_k_smallest_indices zs K = count (LENGTH zs)
Proof
  rw[select_k_smallest_indices_def]
QED

(* Sum-minimization optimality of select_k_smallest_indices zs K over all
   K-element subsets B SUBSET count (LENGTH zs).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem select_k_smallest_indices_sum_minimal:
  ∀(zs : real list) K B.
    K ≤ LENGTH zs ∧ B ⊆ count (LENGTH zs) ∧ CARD B = K ⇒
    REAL_SUM_IMAGE (λi. EL i zs) (select_k_smallest_indices zs K) ≤
    REAL_SUM_IMAGE (λi. EL i zs) B
Proof
  rpt strip_tac >>
  drule select_k_smallest_indices_correct >> strip_tac >>
  qabbrev_tac ‘A = select_k_smallest_indices zs K’ >>
  ‘FINITE A ∧ FINITE B’
    by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
  ‘Normal (REAL_SUM_IMAGE (λi. EL i zs) A) ≤
   Normal (REAL_SUM_IMAGE (λi. EL i zs) B)’
    by (qspecl_then [‘count (LENGTH zs)’, ‘λi. Normal (EL i zs)’, ‘K’, ‘A’, ‘B’]
          mp_tac finite_polar_sum_minimal_extreal >>
        simp[EXTREAL_SUM_IMAGE_NORMAL, extreal_le_eq]) >>
  gvs[extreal_le_eq]
QED

(* Polymorphic BEC polar construction correctness: for any channel W satisfying
   is_bec W with bec_erasure_prob W = Normal eps and K <= 2 ** n,
   bec_polar_construct eps n K is a valid polar information set for W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_polar_construct_is_bec:
  ∀(W : (bool, β) memoryless_channel) (eps : real) n K.
    is_bec W ∧ bec_erasure_prob W = Normal eps ∧ K ≤ 2 ** n ⇒
    is_polar_info_set W (2 ** n) K (bec_polar_construct eps n K)
Proof
  rpt strip_tac >>
  REWRITE_TAC[is_polar_info_set_def, bec_polar_construct_def] >>
  qabbrev_tac ‘zs = bec_bhattacharyya_vec eps n’ >>
  ‘LENGTH zs = 2 ** n ∧
   ∀i. i < 2 ** n ⇒ bhattacharyya (split_channel W (2 ** n) i) = Normal (EL i zs)’
    by (qunabbrev_tac ‘zs’ >>
        qspecl_then [‘W’, ‘eps’, ‘n’] mp_tac bec_bhattacharyya_vec_is_bec >>
        ASM_REWRITE_TAC[] >> strip_tac >>
        conj_tac >- ASM_REWRITE_TAC[] >>
        qx_gen_tac ‘i’ >> strip_tac >>
        qpat_x_assum ‘∀i. _’ (qspec_then ‘i’ mp_tac) >>
        ASM_REWRITE_TAC[] >> disch_then (ACCEPT_TAC o SYM)) >>
  ‘K ≤ LENGTH zs’ by ASM_REWRITE_TAC[] >>
  drule select_k_smallest_indices_correct >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  ASM_REWRITE_TAC[] >>
  rpt strip_tac >>
  ‘i < 2 ** n’
    by (qspecl_then [‘zs’, ‘K’] mp_tac select_k_smallest_indices_subset >>
        REWRITE_TAC[SUBSET_DEF, IN_COUNT] >> rpt strip_tac >>
  first_x_assum drule >> ASM_REWRITE_TAC[bec_bhattacharyya_vec_length] >>
  decide_tac) >>
  ‘j < 2 ** n’ by fs[] >>
  ‘EL i zs ≤ EL j zs’
    by (first_x_assum irule >> simp[]) >>
  qpat_x_assum ‘∀i. i < 2 ** n ⇒ _’
    (fn th => mp_tac (Q.SPEC ‘i’ th) >> mp_tac (Q.SPEC ‘j’ th)) >>
  ASM_REWRITE_TAC[] >> ntac 2 strip_tac >>
  ASM_REWRITE_TAC[extreal_le_eq]
QED

(* Canonical BEC polar code construction correctness theorem
   (Erdal Arıkan, 2009, arXiv:0807.3917, Section IX).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_polar_construct_correct:
  ∀(eps : real) n K.
    0 ≤ eps ∧ eps ≤ 1 ∧ K ≤ 2 ** n ⇒
    is_polar_info_set (binary_erasure_channel (Normal eps)) (2 ** n) K
      (bec_polar_construct eps n K)
Proof
  rpt strip_tac >>
  irule bec_polar_construct_is_bec >>
  ‘0 ≤ Normal eps ∧ Normal eps ≤ 1’
    by simp[extreal_of_num_def, extreal_le_eq] >>
  simp[is_bec_binary_erasure_channel, bec_erasure_prob_binary_erasure_channel]
QED

(* Ground-numeral [simp] subset rule (handles goals like A SUBSET count 16
   when A = bec_polar_construct eps 4 K).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_polar_construct_subset[simp]:
  ∀(eps : real) n K N.
    2 ** n ≤ N ⇒ bec_polar_construct eps n K ⊆ count N
Proof
  rpt strip_tac >> simp[bec_polar_construct_def] >>
  qspecl_then [‘bec_bhattacharyya_vec eps n’, ‘K’] mp_tac
    select_k_smallest_indices_subset >>
  REWRITE_TAC[SUBSET_DEF, IN_COUNT] >> rpt strip_tac >>
  first_x_assum drule >> ASM_REWRITE_TAC[bec_bhattacharyya_vec_length] >>
  decide_tac
QED

(* Ground-numeral [simp] cardinality rule for bec_polar_construct.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_bec_polar_construct[simp]:
  ∀(eps : real) n K.
    K ≤ 2 ** n ⇒ CARD (bec_polar_construct eps n K) = K
Proof
  rpt strip_tac >> simp[bec_polar_construct_def]
QED

(* Ground-numeral [simp] is_polar_info_set rule matching literal blocklengths
   N (e.g. N = 16 with n = 4 in T2-F19-03 and T2-F19-04).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_polar_info_set_bec_polar_construct_eq[simp]:
  ∀(eps : real) n K N.
    0 ≤ eps ∧ eps ≤ 1 ∧ K ≤ 2 ** n ∧ N = 2 ** n ⇒
    is_polar_info_set (binary_erasure_channel (Normal eps)) N K
      (bec_polar_construct eps n K)
Proof
  rpt strip_tac >> gvs[bec_polar_construct_correct]
QED

(* Ground-numeral [simp] is_polar_info_set rule for binary_erasure_channel 0
   (extreal numeral 0 vs Normal 0).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_polar_info_set_bec_polar_construct_0[simp]:
  ∀n K N.
    K ≤ 2 ** n ∧ N = 2 ** n ⇒
    is_polar_info_set (binary_erasure_channel 0) N K
      (bec_polar_construct 0 n K)
Proof
  rpt strip_tac >>
  ‘(0 : extreal) = Normal 0’ by simp[extreal_of_num_def] >>
  pop_assum SUBST1_TAC >> ASM_REWRITE_TAC[] >>
  irule bec_polar_construct_correct >> simp[]
QED

(* Ground-numeral [simp] is_polar_info_set rule for binary_erasure_channel 1
   (extreal numeral 1 vs Normal 1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_polar_info_set_bec_polar_construct_1[simp]:
  ∀n K N.
    K ≤ 2 ** n ∧ N = 2 ** n ⇒
    is_polar_info_set (binary_erasure_channel 1) N K
      (bec_polar_construct 1 n K)
Proof
  rpt strip_tac >>
  ‘(1 : extreal) = Normal 1’ by simp[extreal_of_num_def] >>
  pop_assum SUBST1_TAC >> ASM_REWRITE_TAC[] >>
  irule bec_polar_construct_correct >> simp[]
QED

(* Ground-numeral [simp] Bhattacharyya ordering rule when is_polar_info_set_def
   is unfolded before matching N = 2 ** n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_polar_construct_bhattacharyya_le[simp]:
  ∀(eps : real) n K N i j.
    0 ≤ eps ∧ eps ≤ 1 ∧ K ≤ 2 ** n ∧ N = 2 ** n ∧
    i ∈ bec_polar_construct eps n K ∧
    j < N ∧ j ∉ bec_polar_construct eps n K ⇒
    bhattacharyya (split_channel (binary_erasure_channel (Normal eps)) N i) ≤
    bhattacharyya (split_channel (binary_erasure_channel (Normal eps)) N j)
Proof
  rpt strip_tac >>
  gvs[Excl "bec_split_channel_pow2_step", Excl "is_bec_split_channel_pow2"] >>
  qspecl_then [‘eps’, ‘n’, ‘K’] mp_tac bec_polar_construct_correct >>
  ASM_REWRITE_TAC[is_polar_info_set_def, IN_DIFF, IN_COUNT] >>
  strip_tac >> first_x_assum irule >> ASM_REWRITE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Part 1, Block 4: O(N) Cost Model & Worst-Case Linear Complexity Proofs    *)
(* (Erdal Arıkan, 2009, arXiv:0807.3917, Section I-C.6 & Section IX)         *)
(* ------------------------------------------------------------------------- *)

(* Operation count of Phase 1 (bec_bhattacharyya_vec eps n):
   1 base allocation at n = 0, plus 3 arithmetic operations (z*z, 2*z, -)
   for each of the 2^n parent entries at level n.

   Written by Gemini (Google DeepMind AI agent) *)
Definition bec_bhattacharyya_vec_cost_def:
  bec_bhattacharyya_vec_cost 0 = 1 : num ∧
  bec_bhattacharyya_vec_cost (SUC n) =
    bec_bhattacharyya_vec_cost n + 3 * (2 ** n)
End

(* Operation count of Phase 2 (select_k_smallest_indices zs K):
   Median-of-Medians order-statistic selection + linear c_lt filter pass +
   linear take_threshold_indices pass.

   Written by Gemini (Google DeepMind AI agent) *)
Definition select_k_smallest_indices_cost_def:
  select_k_smallest_indices_cost (zs : real list) (K : num) : num =
    if K = 0 then 1
    else if LENGTH zs ≤ K then 1 + LENGTH zs
    else mom_select_cost zs (K - 1) + 3 * LENGTH zs
End

(* Total end-to-end operation count of exact BEC polar code construction
   (Phase 1 vector recursion + Phase 2 Median-of-Medians selection).

   Written by Gemini (Google DeepMind AI agent) *)
Definition bec_polar_construct_cost_def:
  bec_polar_construct_cost (eps : real) (n : num) (K : num) : num =
    bec_bhattacharyya_vec_cost n +
    select_k_smallest_indices_cost (bec_bhattacharyya_vec eps n) K
End

(* Exact closed-form & linear bound for Phase 1 cost:
   bec_bhattacharyya_vec_cost n + 2 = 3 * 2^n <= 3 * 2^n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_bhattacharyya_vec_cost_linear:
  ∀n. bec_bhattacharyya_vec_cost n + 2 = 3 * (2 ** n) ∧
      bec_bhattacharyya_vec_cost n ≤ 3 * (2 ** n)
Proof
  Induct_on ‘n’ >>
  simp[bec_bhattacharyya_vec_cost_def, arithmeticTheory.EXP] >> decide_tac
QED

(* Worst-case linear bound for Phase 2 selection cost on any real list zs
   (reusable by Part 2 mc_polar_construct_complexity).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem select_k_smallest_indices_cost_linear:
  ∀(zs : real list) K.
    select_k_smallest_indices_cost zs K ≤ 283 * LENGTH zs + 2
Proof
  rpt gen_tac >> simp[select_k_smallest_indices_cost_def] >>
  qspecl_then [‘zs’, ‘K - 1’] mp_tac mom_select_cost_linear >>
  rw[] >> decide_tac
QED

(* Unconditional explicit linear bound:
   bec_polar_construct_cost eps n K <= 288 * (2 ** n) for all eps, n, K.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_polar_construct_cost_upper:
  ∀(eps : real) n K.
    bec_polar_construct_cost eps n K ≤ 288 * (2 ** n)
Proof
  rpt gen_tac >> simp[bec_polar_construct_cost_def] >>
  qspec_then ‘n’ strip_assume_tac bec_bhattacharyya_vec_cost_linear >>
  qspecl_then [‘bec_bhattacharyya_vec eps n’, ‘K’] mp_tac
    select_k_smallest_indices_cost_linear >>
  ‘0 < 2 ** n’ by simp[ZERO_LESS_EXP] >>
  simp[] >> decide_tac
QED

(* Canonical O(N) worst-case linear time complexity theorem for BEC polar
   code construction (Erdal Arıkan, 2009, arXiv:0807.3917, Section I-C.6 &
   Section IX; Roadmap Item 15).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_polar_construct_complexity_linear:
  ∃(C : num).
    0 < C ∧
    ∀(eps : real) n K.
      0 ≤ eps ∧ eps ≤ 1 ∧ K ≤ 2 ** n ⇒
      bec_polar_construct_cost eps n K ≤ C * (2 ** n)
Proof
  qexists_tac ‘288’ >> simp[bec_polar_construct_cost_upper]
QED

(* Asymptotic complexityTheory.big_O formulation of Phase 1 BEC Bhattacharyya
   vector computation: O(2^n) = O(N).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_bhattacharyya_vec_cost_big_O:
  (λn. bec_bhattacharyya_vec_cost n) ∈ big_O (λn. 2 ** n)
Proof
  rw[big_O_def] >> qexistsl_tac [‘0’, ‘3’] >>
  simp[bec_bhattacharyya_vec_cost_linear]
QED

(* Asymptotic complexityTheory.big_O formulation of end-to-end BEC polar
   code construction for any rate/dimension schedule K_fn: O(2^n) = O(N).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_polar_construct_cost_big_O:
  ∀(eps : real) (K_fn : num -> num).
    (λn. bec_polar_construct_cost eps n (K_fn n)) ∈ big_O (λn. 2 ** n)
Proof
  rw[big_O_def] >> qexistsl_tac [‘0’, ‘288’] >>
  simp[bec_polar_construct_cost_upper]
QED

(* ------------------------------------------------------------------------- *)
(* Part 2: Generic B-DMC Approximate Monte-Carlo Polar Code Construction     *)
(*         (Erdal Arıkan, 2009, arXiv:0807.3917, Section IX, Eq. (79))       *)
(* ------------------------------------------------------------------------- *)

(* Zero-denominator-guarded Eq. (79) sample statistic from coordinate
   probability pair (pF, pT) and true sample bit u_i:
   returns sqrt (p_{~u_i} / p_{u_i}) when 0 < p_{u_i}, and 0 otherwise.

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_stat_from_pair_def[simp]:
  mc_stat_from_pair ((pF, pT) : real # real) (u_i : bool) : real =
    let p_den = if u_i then pT else pF;
        p_num = if u_i then pF else pT
    in
      if 0 < p_den then sqrt (p_num / p_den) else 0
End

(* Elementwise extraction of all Eq. (79) sample statistics from a length-N
   butterfly probability-pair list and length-N input sample u.

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_stats_from_pairs_def[simp]:
  mc_stats_from_pairs ([] : (real # real) list) (_ : bool list) : real list = [] ∧
  mc_stats_from_pairs (_ :: _) [] = [] ∧
  mc_stats_from_pairs (p :: ps) (b :: bs) =
    mc_stat_from_pair p b :: mc_stats_from_pairs ps bs
End

(* Length and element-indexing characterization of mc_stats_from_pairs.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem LENGTH_EL_mc_stats_from_pairs[local]:
  ∀(ps : (real # real) list) (bs : bool list).
    LENGTH ps = LENGTH bs ⇒
    LENGTH (mc_stats_from_pairs ps bs) = LENGTH ps ∧
    ∀i. i < LENGTH ps ⇒
        EL i (mc_stats_from_pairs ps bs) =
        mc_stat_from_pair (EL i ps) (EL i bs)
Proof
  Induct_on ‘ps’ >> Cases_on ‘bs’ >> simp[] >>
  rpt strip_tac >> Cases_on ‘i’ >> simp[]
QED

(* Full length-(2^n) vector of Eq. (79) Monte-Carlo Bhattacharyya sample
   statistics [s_0(u, y); ...; s_{2^n - 1}(u, y)] computed in O(N log N) time
   via a single A = EMPTY butterfly pass (fast_sc_leaf_probs W (2 ** n) EMPTY u y).

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_butterfly_sample_vec_def[simp]:
  mc_butterfly_sample_vec (W : (bool, β) memoryless_channel)
    (n : num) (u : bool list) (y : β list) : real list =
    mc_stats_from_pairs (fast_sc_leaf_probs W (2 ** n) ∅ u y) u
End

(* Coordinate-i Monte-Carlo Bhattacharyya sample statistic s_i(u, y) from
   Erdal Arıkan (2009), Section IX Eq. (79), pp. 17-18, computed via the
   O(N log N) A = EMPTY butterfly probability-pair pass (returning 0 whenever
   i >= LENGTH sv or the denominator transition probability is 0).

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_bhattacharyya_sample_def:
  mc_bhattacharyya_sample (W : (bool, β) memoryless_channel)
    (n : num) (i : num) ((u, y) : bool list # β list) : real =
    let sv = mc_butterfly_sample_vec W n u y in
      if i < LENGTH sv then EL i sv else 0
End

(* Sum of a list of real numbers (simp- and compute-friendly).

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_real_sum_list_def[simp]:
  mc_real_sum_list ([] : real list) : real = 0 ∧
  mc_real_sum_list (x :: xs) = x + mc_real_sum_list xs
End

(* Empirical Monte-Carlo Bhattacharyya parameter estimate Z_hat(W_{2^n}^(i))
   across a finite list of M samples [(u_1, y_1); ...; (u_M, y_M)] from
   Erdal Arıkan (2009), Section IX, p. 18 (returning 0 when samples = []).

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_bhattacharyya_estimate_def:
  mc_bhattacharyya_estimate (W : (bool, β) memoryless_channel)
    (n : num) (i : num) (samples : (bool list # β list) list) : real =
    if samples = [] then 0
    else
      mc_real_sum_list (MAP (mc_bhattacharyya_sample W n i) samples) /
      &(LENGTH samples)
End

(* Elementwise addition of two equal-length real vectors for O(M N log N)
   single-butterfly-pass-per-sample accumulation.

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_vec_add_def[simp]:
  mc_vec_add ([] : real list) (_ : real list) : real list = [] ∧
  mc_vec_add (_ :: _) [] = [] ∧
  mc_vec_add (x :: xs) (y :: ys) = (x + y) :: mc_vec_add xs ys
End

(* Single-pass-per-sample computation of all N = 2^n empirical Bhattacharyya
   estimates: runs mc_butterfly_sample_vec once per sample in O(N log N) time
   and accumulates the M length-N vectors in O(M N) additions.

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_bhattacharyya_estimate_vec_def:
  mc_bhattacharyya_estimate_vec (W : (bool, β) memoryless_channel)
    (n : num) (samples : (bool list # β list) list) : real list =
    if samples = [] then REPLICATE (2 ** n) 0
    else
      let M = &(LENGTH samples);
          vecs = MAP (λ(u, y).
                        let sv = mc_butterfly_sample_vec W n u y in
                          if LENGTH sv = 2 ** n then sv
                          else GENLIST (λi. if i < LENGTH sv then EL i sv else 0)
                                       (2 ** n))
                     samples;
          totals = FOLDR mc_vec_add (REPLICATE (2 ** n) 0) vecs
      in
        MAP (λtot. tot / M) totals
End

(* Section IX Approximate Monte-Carlo Polar Code Construction Algorithm for
   generic B-DMCs (Erdal Arıkan, 2009, Section IX, pp. 17-18): selects a
   K-element information set A_hat SUBSET count (2^n) minimizing the sum of
   empirical Monte-Carlo Bhattacharyya estimates Z_hat(W_{2^n}^(i)) via
   Part 1's non-[simp] linear-time Median-of-Medians selector
   select_k_smallest_indices.

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_polar_construct_def:
  mc_polar_construct (W : (bool, β) memoryless_channel)
    (n : num) (K : num) (samples : (bool list # β list) list) : num -> bool =
    select_k_smallest_indices
      (GENLIST (λi. mc_bhattacharyya_estimate W n i samples) (2 ** n))
      K
End

(* Length and elementwise sum characterization of mc_vec_add.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_vec_add_length_el[local]:
  ∀(xs : real list) (ys : real list) N.
    LENGTH xs = N ∧ LENGTH ys = N ⇒
    LENGTH (mc_vec_add xs ys) = N ∧
    ∀i. i < N ⇒ EL i (mc_vec_add xs ys) = EL i xs + EL i ys
Proof
  Induct_on ‘xs’ >> Cases_on ‘ys’ >> simp[] >>
  rpt strip_tac >> Cases_on ‘i’ >> simp[] >>
  first_x_assum (qspec_then ‘LENGTH xs’ mp_tac) >> simp[]
QED

(* Coordinatewise sum characterization of FOLDR mc_vec_add.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem FOLDR_mc_vec_add_el[local]:
  ∀(vecs : real list list) N.
    EVERY (λv. LENGTH v = N) vecs ⇒
    LENGTH (FOLDR mc_vec_add (REPLICATE N (0 : real)) vecs) = N ∧
    ∀i. i < N ⇒
        EL i (FOLDR mc_vec_add (REPLICATE N (0 : real)) vecs) =
        mc_real_sum_list (MAP (λv. EL i v) vecs)
Proof
  Induct_on ‘vecs’
  >- simp[rich_listTheory.LENGTH_REPLICATE, rich_listTheory.EL_REPLICATE] >>
  qx_genl_tac [‘v’, ‘N’] >> simp[] >> strip_tac >>
  first_x_assum (qspec_then ‘N’ mp_tac) >> simp[] >> strip_tac >>
  qspecl_then [‘v’, ‘FOLDR mc_vec_add (REPLICATE N (0 : real)) vecs’, ‘N’]
    mp_tac mc_vec_add_length_el >>
  simp[]
QED

(* Coordinatewise indexing across padded length-(2^n) sample vectors equals
   MAP (mc_bhattacharyya_sample W n idx).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem pad_vec_map_el[local]:
  ∀(W : (bool, β) memoryless_channel) n idx (ls : (bool list # β list) list).
    idx < 2 ** n ⇒
    MAP (λv. EL idx v)
      (MAP (λ(u, y).
              let sv = mc_butterfly_sample_vec W n u y in
                if LENGTH sv = 2 ** n then sv
                else GENLIST (λi. if i < LENGTH sv then EL i sv else (0 : real))
                             (2 ** n))
           ls) =
    MAP (mc_bhattacharyya_sample W n idx) ls
Proof
  gen_tac >> gen_tac >> gen_tac >> Induct_on ‘ls’ >- simp[] >>
  qx_gen_tac ‘h’ >> Cases_on ‘h’ >>
  strip_tac >> first_x_assum (drule_then assume_tac) >>
  ‘EL idx
     (let sv = mc_butterfly_sample_vec W n q r in
        if LENGTH sv = 2 ** n then sv
        else GENLIST (λi. if i < LENGTH sv then EL i sv else (0 : real))
                     (2 ** n)) =
   mc_bhattacharyya_sample W n idx (q, r)’
    by (REWRITE_TAC[mc_bhattacharyya_sample_def, LET_THM] >> BETA_TAC >>
        Cases_on ‘LENGTH (mc_butterfly_sample_vec W n q r) = 2 ** n’
        >- ASM_REWRITE_TAC[]
        >- (ASM_REWRITE_TAC[] >>
            qspecl_then
              [‘λi. if i < LENGTH (mc_butterfly_sample_vec W n q r)
                    then EL i (mc_butterfly_sample_vec W n q r) else (0 : real)’,
               ‘2 ** n’, ‘idx’] mp_tac EL_GENLIST >>
            ASM_REWRITE_TAC[] >> BETA_TAC >>
            disch_then SUBST1_TAC >> REFL_TAC)) >>
  ASM_REWRITE_TAC[MAP, UNCURRY_DEF] >> BETA_TAC >> ASM_REWRITE_TAC[]
QED

(* Exact equivalence between single-pass-per-sample vector accumulation
   mc_bhattacharyya_estimate_vec and coordinatewise GENLIST of
   mc_bhattacharyya_estimate.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_bhattacharyya_estimate_vec_eq_genlist:
  ∀(W : (bool, β) memoryless_channel) n samples.
    mc_bhattacharyya_estimate_vec W n samples =
    GENLIST (λi. mc_bhattacharyya_estimate W n i samples) (2 ** n)
Proof
  rpt gen_tac >>
  Cases_on ‘samples = []’
  >- (simp[mc_bhattacharyya_estimate_vec_def, mc_bhattacharyya_estimate_def] >>
      irule LIST_EQ >>
      simp[rich_listTheory.LENGTH_REPLICATE, rich_listTheory.EL_REPLICATE]) >>
  ‘∀(ls : (bool list # β list) list).
     EVERY (λv. LENGTH v = 2 ** n)
       (MAP (λ(u, y).
               let sv = mc_butterfly_sample_vec W n u y in
                 if LENGTH sv = 2 ** n then sv
                 else GENLIST (λi. if i < LENGTH sv then EL i sv else (0 : real))
                              (2 ** n)) ls)’
    by (Induct >- simp[] >>
        qx_gen_tac ‘h’ >> Cases_on ‘h’ >>
        ASM_REWRITE_TAC[MAP, EVERY_DEF, UNCURRY_DEF] >>
        BETA_TAC >> REWRITE_TAC[LET_THM] >> BETA_TAC >>
        Cases_on ‘LENGTH (mc_butterfly_sample_vec W n q r) = 2 ** n’ >>
        ASM_REWRITE_TAC[LENGTH_GENLIST]) >>
  first_x_assum (qspec_then ‘samples’ assume_tac) >>
  drule FOLDR_mc_vec_add_el >>
  REWRITE_TAC[mc_bhattacharyya_estimate_vec_def, mc_bhattacharyya_estimate_def] >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[LET_THM] >> BETA_TAC >>
  strip_tac >>
  irule LIST_EQ >> REWRITE_TAC[LENGTH_MAP, LENGTH_GENLIST] >>
  ASM_REWRITE_TAC[] >>
  qx_gen_tac ‘idx’ >> strip_tac >>
  DEP_REWRITE_TAC[EL_MAP, EL_GENLIST] >>
  ASM_REWRITE_TAC[] >> BETA_TAC >>
  first_x_assum (drule_then SUBST1_TAC) >>
  simp[SIMP_RULE (srw_ss()) [LET_THM] pad_vec_map_el]
QED

(* Unconditional [simp] subset rule for mc_polar_construct.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_polar_construct_SUBSET[simp]:
  ∀(W : (bool, β) memoryless_channel) n K samples.
    mc_polar_construct W n K samples ⊆ count (2 ** n)
Proof
  rpt gen_tac >> REWRITE_TAC[mc_polar_construct_def] >>
  qspecl_then [‘GENLIST (λi. mc_bhattacharyya_estimate W n i samples) (2 ** n)’, ‘K’]
    mp_tac select_k_smallest_indices_subset >>
  REWRITE_TAC[LENGTH_GENLIST]
QED

(* [simp] cardinality rule for mc_polar_construct whenever K <= 2 ** n.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem CARD_mc_polar_construct[simp]:
  ∀(W : (bool, β) memoryless_channel) n K samples.
    K ≤ 2 ** n ⇒ CARD (mc_polar_construct W n K samples) = K
Proof
  simp[mc_polar_construct_def]
QED

(* [simp] boundary rule mc_polar_construct W n 0 samples = EMPTY.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_polar_construct_0[simp]:
  ∀(W : (bool, β) memoryless_channel) n samples.
    mc_polar_construct W n 0 samples = ∅
Proof
  simp[mc_polar_construct_def]
QED

(* [simp] full-dimension boundary rule mc_polar_construct W n K samples = count (2 ** n).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_polar_construct_full[simp]:
  ∀(W : (bool, β) memoryless_channel) n K samples.
    2 ** n ≤ K ⇒ mc_polar_construct W n K samples = count (2 ** n)
Proof
  rpt strip_tac >> simp[mc_polar_construct_def] >>
  qspecl_then [‘GENLIST (λi. mc_bhattacharyya_estimate W n i samples) (2 ** n)’, ‘K’]
    mp_tac select_k_smallest_indices_full >>
  simp[]
QED

(* Exact subset and cardinality theorem for mc_polar_construct (holds for all
   K <= 2 ** n and all sample lists including samples = []).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_polar_construct_card:
  ∀(W : (bool, β) memoryless_channel) n K samples.
    K ≤ 2 ** n ⇒
    mc_polar_construct W n K samples ⊆ count (2 ** n) ∧
    CARD (mc_polar_construct W n K samples) = K
Proof
  simp[]
QED

(* Empirical estimate ordering and sum-minimization optimality of
   mc_polar_construct: every selected coordinate has empirical estimate <=
   every unselected coordinate, minimizing the sum of empirical estimates over
   all K-element subsets B SUBSET count (2 ** n).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_polar_construct_minimal:
  ∀(W : (bool, β) memoryless_channel) n K samples B.
    K ≤ 2 ** n ∧ B ⊆ count (2 ** n) ∧ CARD B = K ⇒
    (∀i j.
       i ∈ mc_polar_construct W n K samples ∧
       j ∈ count (2 ** n) DIFF mc_polar_construct W n K samples ⇒
       mc_bhattacharyya_estimate W n i samples ≤
       mc_bhattacharyya_estimate W n j samples) ∧
    REAL_SUM_IMAGE (λi. mc_bhattacharyya_estimate W n i samples)
      (mc_polar_construct W n K samples) ≤
    REAL_SUM_IMAGE (λi. mc_bhattacharyya_estimate W n i samples) B
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac ‘zs = GENLIST (λk. mc_bhattacharyya_estimate W n k samples) (2 ** n)’ >>
  ‘LENGTH zs = 2 ** n’ by simp[Abbr ‘zs’] >>
  ‘K ≤ LENGTH zs’ by simp[] >>
  drule select_k_smallest_indices_correct >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      ‘i ∈ select_k_smallest_indices zs K’
        by gvs[mc_polar_construct_def] >>
      ‘i < 2 ** n’ by metis_tac[SUBSET_DEF, IN_COUNT] >>
      ‘j < 2 ** n ∧ j ∉ select_k_smallest_indices zs K’
        by gvs[mc_polar_construct_def, IN_DIFF, IN_COUNT] >>
      ‘j ∈ count (LENGTH zs) DIFF select_k_smallest_indices zs K’
        by simp[IN_DIFF, IN_COUNT] >>
      first_x_assum (qspecl_then [‘i’, ‘j’] mp_tac) >>
      ASM_REWRITE_TAC[] >>
      simp[Abbr ‘zs’])
  >- (‘B ⊆ count (LENGTH zs)’ by ASM_REWRITE_TAC[] >>
      qspecl_then [‘zs’, ‘K’, ‘B’] mp_tac select_k_smallest_indices_sum_minimal >>
      ASM_REWRITE_TAC[] >>
      qabbrev_tac ‘A = select_k_smallest_indices zs K’ >>
      ‘mc_polar_construct W n K samples = A’
        by simp[mc_polar_construct_def, Abbr ‘A’, Abbr ‘zs’] >>
      ‘FINITE A ∧ FINITE B’ by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
      ‘REAL_SUM_IMAGE (λi. EL i zs) A =
       REAL_SUM_IMAGE (λi. mc_bhattacharyya_estimate W n i samples) A’
        by (irule real_sigmaTheory.REAL_SUM_IMAGE_EQ >> simp[] >>
            qx_gen_tac ‘x’ >> strip_tac >>
            ‘x < 2 ** n’ by metis_tac[SUBSET_DEF, IN_COUNT] >>
            simp[Abbr ‘zs’]) >>
      ‘REAL_SUM_IMAGE (λi. EL i zs) B =
       REAL_SUM_IMAGE (λi. mc_bhattacharyya_estimate W n i samples) B’
        by (irule real_sigmaTheory.REAL_SUM_IMAGE_EQ >> simp[] >>
            qx_gen_tac ‘x’ >> strip_tac >>
            ‘x < 2 ** n’ by metis_tac[SUBSET_DEF, IN_COUNT] >>
            simp[Abbr ‘zs’]) >>
      simp[])
QED

(* Exact Eq. (79) split-channel ratio formula for mc_bhattacharyya_sample.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_bhattacharyya_sample_eq_split_channel:
  ∀(W : (bool, β) memoryless_channel) n i u y.
    wf_bdmc W ∧ i < 2 ** n ∧
    LENGTH u = 2 ** n ∧ LENGTH y = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    mc_bhattacharyya_sample W n i (u, y) =
      let p_den = real (mcchannel (split_channel W (2 ** n) i)
                                  (EL i u) {(y, TAKE i u)});
          p_num = real (mcchannel (split_channel W (2 ** n) i)
                                  (¬(EL i u)) {(y, TAKE i u)})
      in
        if 0 < p_den then sqrt (p_num / p_den) else 0
Proof
  rpt strip_tac >>
  qspecl_then [‘W’, ‘n’, ‘u’, ‘y’] mp_tac
    polar_complexityTheory.fast_sc_leaf_probs_empty_set >>
  simp[] >> strip_tac >>
  qspecl_then [‘fast_sc_leaf_probs W (2 ** n) ∅ u y’, ‘u’] mp_tac
    LENGTH_EL_mc_stats_from_pairs >>
  simp[] >> strip_tac >>
  simp[mc_bhattacharyya_sample_def, mc_butterfly_sample_vec_def, LET_THM] >>
  Cases_on ‘EL i u’ >> simp[]
QED

(* Running fast_sc_decode with information set A = EMPTY and frozen vector
   equal to the true sample u recovers u identically (feeding u_prev = TAKE i u
   to every coordinate decision element i < 2^n), and mc_bhattacharyya_sample
   computes the exact Arıkan Section IX Eq. (79) split-channel likelihood-ratio
   square-root statistic at (y, TAKE i (fast_sc_decode W (2 ** n) EMPTY u y)).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_sample_via_fast_sc_correct:
  ∀(W : (bool, β) memoryless_channel) n i u y.
    wf_bdmc W ∧ i < 2 ** n ∧
    LENGTH u = 2 ** n ∧ LENGTH y = 2 ** n ∧
    EVERY (λyi. yi ∈ mccodomain W) y ⇒
    fast_sc_decode W (2 ** n) ∅ u y = u ∧
    Normal (mc_bhattacharyya_sample W n i (u, y)) =
      let u_prev = TAKE i (fast_sc_decode W (2 ** n) ∅ u y);
          u_i = EL i u;
          p_den = mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)};
          p_num = mcchannel (split_channel W (2 ** n) i) (¬u_i) {(y, u_prev)}
      in
        if 0 < p_den then sqrt (p_num / p_den) else 0
Proof
  rpt gen_tac >> strip_tac >>
  ‘fast_sc_decode W (2 ** n) ∅ u y = u’
    by (qspecl_then [‘W’, ‘n’, ‘u’, ‘y’] mp_tac
          polar_complexityTheory.fast_sc_leaf_probs_empty_set >>
        simp[]) >>
  conj_tac >- ASM_REWRITE_TAC[] >>
  qspecl_then [‘W’, ‘n’, ‘i’, ‘u’, ‘y’] mp_tac
    mc_bhattacharyya_sample_eq_split_channel >>
  simp[] >> disch_then SUBST1_TAC >>
  drule_all wf_bdmc_split_channel >> strip_tac >>
  ‘(y, TAKE i u) ∈ mccodomain (split_channel W (2 ** n) i)’
    by simp[mccodomain_split_channel_alt, LENGTH_TAKE] >>
  qspecl_then [‘split_channel W (2 ** n) i’, ‘EL i u’, ‘(y, TAKE i u)’]
    mp_tac bdmcTheory.wf_bdmc_mcchannel_singleton_normal >>
  qspecl_then [‘split_channel W (2 ** n) i’, ‘¬(EL i u)’, ‘(y, TAKE i u)’]
    mp_tac bdmcTheory.wf_bdmc_mcchannel_singleton_normal >>
  simp[] >> rpt strip_tac >>
  rw[LET_THM, extreal_of_num_def, extreal_lt_eq] >>
  ‘r' ≠ 0 ∧ 0 ≤ r / r'’
    by (conj_tac >- REAL_ASM_ARITH_TAC >- simp[realTheory.REAL_LE_DIV]) >>
  simp[extreal_div_eq, extreal_sqrt_def]
QED

(* Algebraic cancellation p * sqrt(q / p) = sqrt(p * q) for all non-negative
   reals p, q, holding both when p > 0 and when p = 0 (with zero-denominator
   guard 0).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_bhattacharyya_cancel_lemma[local]:
  ∀(p : real) (q : real).
    0 ≤ p ∧ 0 ≤ q ⇒
    p * (if 0 < p then sqrt (q / p) else 0) = sqrt (p * q)
Proof
  rpt strip_tac >>
  Cases_on ‘0 < p’
  >- (ASM_REWRITE_TAC[] >>
      ‘p ≠ 0’ by REAL_ASM_ARITH_TAC >>
      ‘0 ≤ q / p’ by simp[realTheory.REAL_LE_DIV] >>
      ‘0 ≤ p * p’ by simp[realTheory.REAL_LE_MUL] >>
      ‘p * (q / p) = q’ by simp[realTheory.REAL_DIV_LMUL] >>
      ‘p * q = (p * p) * (q / p)’
        by (POP_ASSUM
              (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (SYM th))))) >>
            REAL_ARITH_TAC) >>
      ‘sqrt (p * q) = sqrt (p * p) * sqrt (q / p)’
        by (POP_ASSUM SUBST1_TAC >> irule realTheory.SQRT_MUL >> simp[]) >>
      ‘sqrt (p * p) = p’
        by (‘sqrt (p * p) = sqrt p * sqrt p’
              by (irule realTheory.SQRT_MUL >> simp[]) >>
            POP_ASSUM SUBST1_TAC >>
            REWRITE_TAC[GSYM realTheory.POW_2] >>
            irule realTheory.SQRT_POW_2 >> simp[]) >>
      ASM_REWRITE_TAC[])
  >- (‘p = 0’ by REAL_ASM_ARITH_TAC >>
      simp[realTheory.SQRT_0])
QED

(* Normal representation of extreal reciprocal powers of two 1 / 2 pow k.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem extreal_inv_two_pow_normal[local]:
  ∀k : num.
    ((2 : extreal) pow k = Normal ((2 : real) pow k)) ∧
    ((1 / (2 : extreal) pow k) = Normal (1 / (2 : real) pow k))
Proof
  gen_tac >>
  ‘(2 : extreal) pow k = Normal ((2 : real) pow k)’
    by (Induct_on ‘k’ >>
        simp[extreal_of_num_def, extreal_pow_def, extreal_mul_eq,
             realTheory.pow]) >>
  ‘(2 : real) pow k ≠ 0’ by simp[realTheory.POW_NZ] >>
  simp[extreal_of_num_def, extreal_div_eq]
QED

(* Splitting a finite REAL_SUM_IMAGE over a Cartesian product s x t for any
   pair function h : alpha # beta -> real.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_CROSS_SPLIT[local]:
  ∀(h : α # β -> real) (s : α -> bool) (t : β -> bool).
    FINITE s ∧ FINITE t ⇒
    REAL_SUM_IMAGE h (s × t) =
    REAL_SUM_IMAGE (λx. REAL_SUM_IMAGE (λy. h (x, y)) t) s
Proof
  rpt strip_tac >>
  ‘h = (λp. h (FST p, SND p))’
    by simp[FUN_EQ_THM, FORALL_PROD] >>
  POP_ASSUM SUBST1_TAC >>
  qspecl_then [‘s’, ‘t’, ‘λx y. h (x, y)’] mp_tac
    real_sigmaTheory.REAL_SUM_IMAGE_REAL_SUM_IMAGE >>
  simp[]
QED

(* Pure-variable real multiplication rearrangement lemmas used when factoring
   inner marginalization constants in mc_bhattacharyya_unbiased.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_real_mul_rearrange[local]:
  (∀(a : real) b c d. (a * b) * c * d = (a * d * b) * c) ∧
  (∀(a : real) b c. a * (b * c) = a * (c * b))
Proof
  conj_tac >> rpt gen_tac >>
  CONV_TAC (AC_CONV (realTheory.REAL_MUL_ASSOC, realTheory.REAL_MUL_COMM))
QED

(* Bijection decomposing length-N bitlists at coordinate i < N into
   (u_prev IN length_n_codes i, (u_i IN UNIV(:bool), u_later IN length_n_codes (N - i - 1))).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem BIJ_split_bitlist_at[local]:
  ∀N i.
    i < N ⇒
    BIJ (λ(u_prev, (u_i, u_later)). u_prev ++ [u_i] ++ u_later)
        (length_n_codes i × (𝕌(:bool) × length_n_codes (N - i - 1)))
        (length_n_codes N)
Proof
  rpt strip_tac >>
  simp[BIJ_IFF_INV] >>
  conj_tac >- (simp[FORALL_PROD] >> rw[]) >>
  qexists_tac ‘λu. (TAKE i u, (EL i u, DROP (i + 1) u))’ >>
  rpt conj_tac
  >- (simp[] >> rw[])
  >- (simp[FORALL_PROD] >>
      qx_genl_tac [‘u_prev’, ‘u_i’, ‘u_later’] >> strip_tac >>
      ‘TAKE i (u_prev ++ [u_i] ++ u_later) = u_prev’
        by (‘u_prev ++ [u_i] ++ u_later = u_prev ++ ([u_i] ++ u_later)’
              by simp[] >>
            pop_assum SUBST1_TAC >>
            simp[rich_listTheory.TAKE_APPEND1]) >>
      ‘EL i (u_prev ++ [u_i] ++ u_later) = u_i’
        by (‘u_prev ++ [u_i] ++ u_later = u_prev ++ ([u_i] ++ u_later)’
              by simp[] >>
            pop_assum SUBST1_TAC >>
            simp[rich_listTheory.EL_APPEND2]) >>
      ‘DROP (i + 1) (u_prev ++ [u_i] ++ u_later) = u_later’
        by (‘u_prev ++ [u_i] ++ u_later = (u_prev ++ [u_i]) ++ u_later ∧
             LENGTH (u_prev ++ [u_i]) = i + 1’ by simp[] >>
            pop_assum (SUBST1_TAC o SYM) >>
            pop_assum SUBST1_TAC >>
            simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
      simp[])
  >- (qx_gen_tac ‘x’ >> strip_tac >>
      ‘TAKE (i + 1) x ++ DROP (i + 1) x = x’ by simp[TAKE_DROP] >>
      ‘TAKE (i + 1) x = TAKE i x ++ [EL i x]’
        by (qspecl_then [‘i’, ‘x’] mp_tac rich_listTheory.SNOC_EL_TAKE >>
            simp[SNOC_APPEND, ADD1]) >>
      pop_assum SUBST_ALL_TAC >>
      gvs[])
QED

(* Arıkan Section IX Eq. (79) Exact Expectation Unbiasedness Identity
   (Erdal Arıkan, 2009, arXiv:0807.3917, pp. 17-18):
   For ANY well-formed B-DMC W (including channels with zero transition
   probabilities such as BEC and Z-channels, with no positivity assumption)
   and any coordinate 0 <= i < 2^n, the expectation of
   mc_bhattacharyya_sample W n i (U_1^N, Y_1^N) under the joint distribution
   P(u, y) = 2^{-N} W_N(y | u) equals Z(W_N^(i)) identically.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_bhattacharyya_unbiased:
  ∀(W : (bool, β) memoryless_channel) n i.
    wf_bdmc W ∧ i < 2 ** n ⇒
    ∑ (λu. ∑ (λy. (1 / 2 pow (2 ** n)) *
                  mcchannel (combine_channel W (2 ** n)) u {y} *
                  Normal (mc_bhattacharyya_sample W n i (u, y)))
             (cross_list (REPLICATE (2 ** n) (mccodomain W))))
      (length_n_codes (2 ** n)) =
    bhattacharyya (split_channel W (2 ** n) i)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘Y_N = cross_list (REPLICATE (2 ** n) (mccodomain W))’ >>
  ‘FINITE (mccodomain W)’ by gvs[wf_bdmc_def] >>
  ‘FINITE Y_N’ by simp[Abbr ‘Y_N’, combine_channelTheory.finite_cross_list_replicate] >>
  ‘FINITE 𝕌(:bool)’ by simp[UNIV_BOOL] >>
  ‘∀k. FINITE (length_n_codes k)’
    by metis_tac[combine_channelTheory.cross_list_replicate_univ_bool,
                 combine_channelTheory.finite_cross_list_replicate] >>
  ‘FINITE (𝕌(:bool) × length_n_codes (2 ** n - i - 1))’
    by simp[FINITE_CROSS] >>
  ‘wf_bdmc (split_channel W (2 ** n) i)’
    by (irule wf_bdmc_split_channel >> simp[]) >>
  ‘mccodomain (split_channel W (2 ** n) i) = Y_N × length_n_codes i’
    by simp[mccodomain_split_channel, Abbr ‘Y_N’] >>
  qspec_then ‘split_channel W (2 ** n) i’ mp_tac bdmcTheory.bhattacharyya_real_sum >>
  ASM_REWRITE_TAC[] >>
  disch_then SUBST1_TAC >>
  DEP_REWRITE_TAC[REAL_SUM_IMAGE_CROSS_SPLIT] >>
  ASM_REWRITE_TAC[] >> BETA_TAC >>
  Know
    ‘∑ (λu. ∑ (λy. (1 / 2 pow (2 ** n)) *
                   mcchannel (combine_channel W (2 ** n)) u {y} *
                   Normal (mc_bhattacharyya_sample W n i (u, y)))
              Y_N)
       (length_n_codes (2 ** n)) =
     Normal
       (REAL_SUM_IMAGE
          (λu. REAL_SUM_IMAGE
                 (λy. (1 / (2 : real) pow (2 ** n)) *
                      real (mcchannel (combine_channel W (2 ** n)) u {y}) *
                      mc_bhattacharyya_sample W n i (u, y))
                 Y_N)
          (length_n_codes (2 ** n)))’
  >- (simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
      irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
      qx_gen_tac ‘u’ >> strip_tac >>
      simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
      irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
      qx_gen_tac ‘y’ >> strip_tac >>
      ‘LENGTH y = 2 ** n ∧ EVERY (λyi. yi ∈ mccodomain W) y’
        by gvs[Abbr ‘Y_N’, combine_channelTheory.in_cross_list_replicate] >>
      ‘LENGTH u = 2 ** n’ by gvs[] >>
      qspecl_then [‘W’, ‘n’, ‘u’, ‘y’] mp_tac
        combine_channelTheory.mcchannel_combine_channel_singleton_normal >>
      ASM_REWRITE_TAC[] >> strip_tac >>
      simp[extreal_inv_two_pow_normal, extreal_mul_eq, extreal_11, real_normal] >>
      CONV_TAC (AC_CONV (realTheory.REAL_MUL_ASSOC, realTheory.REAL_MUL_COMM))) >>
  disch_then SUBST1_TAC >>
  REWRITE_TAC[extreal_11] >>
  qspecl_then
    [‘λu y. (1 / (2 : real) pow (2 ** n)) *
            real (mcchannel (combine_channel W (2 ** n)) u {y}) *
            mc_bhattacharyya_sample W n i (u, y)’,
     ‘length_n_codes (2 ** n)’, ‘Y_N’]
    mp_tac real_sigmaTheory.NESTED_REAL_SUM_IMAGE_REVERSE >>
  ASM_REWRITE_TAC[] >> BETA_TAC >> disch_then SUBST1_TAC >>
  irule real_sigmaTheory.REAL_SUM_IMAGE_EQ >> ASM_REWRITE_TAC[] >>
  qx_gen_tac ‘y’ >> strip_tac >> BETA_TAC >>
  ‘LENGTH y = 2 ** n ∧ EVERY (λyi. yi ∈ mccodomain W) y’
    by gvs[Abbr ‘Y_N’, combine_channelTheory.in_cross_list_replicate] >>
  qabbrev_tac ‘S_dom = length_n_codes i × (𝕌(:bool) × length_n_codes (2 ** n - i - 1))’ >>
  ‘FINITE S_dom’ by simp[Abbr ‘S_dom’, FINITE_CROSS] >>
  ‘BIJ (λ(u_prev, (u_i, u_later)). u_prev ++ [u_i] ++ u_later) S_dom (length_n_codes (2 ** n))’
    by simp[Abbr ‘S_dom’, BIJ_split_bitlist_at] >>
  Know
    ‘REAL_SUM_IMAGE
       (λu. (1 / (2 : real) pow (2 ** n)) *
            real (mcchannel (combine_channel W (2 ** n)) u {y}) *
            mc_bhattacharyya_sample W n i (u, y))
       (length_n_codes (2 ** n)) =
     REAL_SUM_IMAGE
       ((λu. (1 / (2 : real) pow (2 ** n)) *
             real (mcchannel (combine_channel W (2 ** n)) u {y}) *
             mc_bhattacharyya_sample W n i (u, y)) ∘
        (λ(u_prev, (u_i, u_later)). u_prev ++ [u_i] ++ u_later))
       S_dom’
  >- (irule bdmcTheory.REAL_SUM_IMAGE_BIJ >> ASM_REWRITE_TAC[]) >>
  disch_then SUBST1_TAC >>
  qunabbrev_tac ‘S_dom’ >>
  ‘FINITE (𝕌(:bool) × length_n_codes (2 ** n - i - 1))’
    by (irule FINITE_CROSS >> ASM_REWRITE_TAC[]) >>
  DEP_REWRITE_TAC[REAL_SUM_IMAGE_CROSS_SPLIT] >>
  ASM_REWRITE_TAC[] >> BETA_TAC >>
  irule real_sigmaTheory.REAL_SUM_IMAGE_EQ >> ASM_REWRITE_TAC[] >>
  qx_gen_tac ‘u_prev’ >> strip_tac >> BETA_TAC >>
  DEP_REWRITE_TAC[REAL_SUM_IMAGE_CROSS_SPLIT] >>
  ASM_REWRITE_TAC[combinTheory.o_THM] >> BETA_TAC >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  ‘LENGTH u_prev = i’ by gvs[] >>
  qmatch_goalsub_abbrev_tac ‘REAL_SUM_IMAGE inner_fn _’ >>
  Know
    ‘∀u_i.
       inner_fn u_i =
       (1 / 2) *
       real (mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)}) *
       (let p_den = real (mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)});
            p_num = real (mcchannel (split_channel W (2 ** n) i) (¬u_i) {(y, u_prev)})
        in
          if 0 < p_den then sqrt (p_num / p_den) else 0)’
  >- (qx_gen_tac ‘u_i’ >>
      qunabbrev_tac ‘inner_fn’ >> BETA_TAC >>
      qabbrev_tac ‘s_val =
        (let p_den = real (mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)});
             p_num = real (mcchannel (split_channel W (2 ** n) i) (¬u_i) {(y, u_prev)})
         in
           if 0 < p_den then sqrt (p_num / p_den) else 0)’ >>
      ‘1 / (2 : real) pow (2 ** n) = (1 / 2) * (1 / (2 : real) pow (2 ** n - 1))’
        by (‘2 ** n = SUC (2 ** n - 1)’ by decide_tac >>
            ‘(2 : real) ≠ 0 ∧ (2 : real) pow (2 ** n - 1) ≠ 0’
              by simp[realTheory.POW_NZ] >>
            CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV (ASSUME “2 ** n = SUC (2 ** n - 1)”))))) >>
            REWRITE_TAC[realTheory.pow, GSYM realTheory.REAL_INV_1OVER] >>
            irule realTheory.REAL_INV_MUL >> ASM_REWRITE_TAC[]) >>
      qmatch_goalsub_abbrev_tac ‘REAL_SUM_IMAGE lat_fn _’ >>
      Know
        ‘REAL_SUM_IMAGE lat_fn (length_n_codes (2 ** n - i - 1)) =
         REAL_SUM_IMAGE
           (λu_later.
              ((1 / 2) * s_val * (1 / (2 : real) pow (2 ** n - 1))) *
              real (mcchannel (combine_channel W (2 ** n))
                              (u_prev ++ [u_i] ++ u_later) {y}))
           (length_n_codes (2 ** n - i - 1))’
      >- (irule real_sigmaTheory.REAL_SUM_IMAGE_EQ >> ASM_REWRITE_TAC[] >>
          qx_gen_tac ‘u_later’ >> strip_tac >>
          qunabbrev_tac ‘lat_fn’ >> BETA_TAC >>
          ‘LENGTH u_later = 2 ** n - i - 1’ by gvs[] >>
          ‘LENGTH (u_prev ++ [u_i] ++ u_later) = 2 ** n’ by simp[] >>
          qspecl_then [‘W’, ‘n’, ‘i’, ‘u_prev ++ [u_i] ++ u_later’, ‘y’] mp_tac
            mc_bhattacharyya_sample_eq_split_channel >>
          ASM_REWRITE_TAC[] >>
          ‘TAKE i (u_prev ++ [u_i] ++ u_later) = u_prev’
            by (‘u_prev ++ [u_i] ++ u_later = u_prev ++ ([u_i] ++ u_later)’
                  by simp[] >>
                pop_assum SUBST1_TAC >>
                simp[rich_listTheory.TAKE_APPEND1]) >>
          ‘EL i (u_prev ++ [u_i] ++ u_later) = u_i’
            by (‘u_prev ++ [u_i] ++ u_later = u_prev ++ ([u_i] ++ u_later)’
                  by simp[] >>
                pop_assum SUBST1_TAC >>
                simp[rich_listTheory.EL_APPEND2]) >>
          ASM_REWRITE_TAC[] >>
          disch_then SUBST1_TAC >>
          qunabbrev_tac ‘s_val’ >>
          ASM_REWRITE_TAC[] >>
          MATCH_ACCEPT_TAC (CONJUNCT1 mc_real_mul_rearrange)) >>
      disch_then SUBST1_TAC >>
      qspec_then ‘length_n_codes (2 ** n - i - 1)’ mp_tac
        real_sigmaTheory.REAL_SUM_IMAGE_CMUL >>
      ASM_REWRITE_TAC[] >>
      disch_then
        (qspecl_then
           [‘λu_later. real (mcchannel (combine_channel W (2 ** n))
                                       (u_prev ++ [u_i] ++ u_later) {y})’,
            ‘(1 / 2) * s_val * (1 / (2 : real) pow (2 ** n - 1))’]
           (SUBST1_TAC o BETA_RULE)) >>
      REWRITE_TAC[GSYM realTheory.REAL_MUL_ASSOC] >>
      ‘real (mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)}) =
       (1 / (2 : real) pow (2 ** n - 1)) *
       REAL_SUM_IMAGE
         (λu_later. real (mcchannel (combine_channel W (2 ** n))
                                    (u_prev ++ [u_i] ++ u_later) {y}))
         (length_n_codes (2 ** n - i - 1))’
        by (qspecl_then [‘W’, ‘2 ** n’, ‘i’, ‘u_i’, ‘y’, ‘u_prev’] mp_tac
              mcchannel_split_channel_singleton_real >>
            ASM_REWRITE_TAC[] >>
            strip_tac >> ASM_REWRITE_TAC[real_normal]) >>
      POP_ASSUM (SUBST1_TAC o SYM) >>
      qunabbrev_tac ‘s_val’ >>
      MATCH_ACCEPT_TAC (CONJUNCT2 mc_real_mul_rearrange)) >>
  strip_tac >>
  ‘REAL_SUM_IMAGE inner_fn 𝕌(:bool) =
   REAL_SUM_IMAGE
     (λu_i.
        (1 / 2) *
        real (mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)}) *
        (let p_den = real (mcchannel (split_channel W (2 ** n) i) u_i {(y, u_prev)});
             p_num = real (mcchannel (split_channel W (2 ** n) i) (¬u_i) {(y, u_prev)})
         in
           if 0 < p_den then sqrt (p_num / p_den) else 0))
     𝕌(:bool)’
    by (irule real_sigmaTheory.REAL_SUM_IMAGE_EQ >> ASM_REWRITE_TAC[] >>
        qx_gen_tac ‘u_i’ >> strip_tac >> BETA_TAC >> ASM_REWRITE_TAC[]) >>
  POP_ASSUM SUBST1_TAC >>
  REWRITE_TAC[UNIV_BOOL] >>
  simp[real_sigmaTheory.REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT, LET_THM] >>
  ‘0 ≤ real (mcchannel (split_channel W (2 ** n) i) F {(y, u_prev)}) ∧
   0 ≤ real (mcchannel (split_channel W (2 ** n) i) T {(y, u_prev)})’
    by (‘(y, u_prev) ∈ mccodomain (split_channel W (2 ** n) i)’
          by simp[mccodomain_split_channel_alt] >>
        qspecl_then [‘split_channel W (2 ** n) i’, ‘F’, ‘(y, u_prev)’] mp_tac
          bdmcTheory.wf_bdmc_mcchannel_singleton_normal >>
        qspecl_then [‘split_channel W (2 ** n) i’, ‘T’, ‘(y, u_prev)’] mp_tac
          bdmcTheory.wf_bdmc_mcchannel_singleton_normal >>
        simp[] >> rpt strip_tac >> simp[real_normal]) >>
  qspecl_then [‘real (mcchannel (split_channel W (2 ** n) i) T {(y, u_prev)})’,
               ‘real (mcchannel (split_channel W (2 ** n) i) F {(y, u_prev)})’]
    mp_tac mc_bhattacharyya_cancel_lemma >>
  qspecl_then [‘real (mcchannel (split_channel W (2 ** n) i) F {(y, u_prev)})’,
               ‘real (mcchannel (split_channel W (2 ** n) i) T {(y, u_prev)})’]
    mp_tac mc_bhattacharyya_cancel_lemma >>
  ASM_REWRITE_TAC[] >>
  ntac 2 strip_tac >>
  ‘∀(a : real) (b : real).
     (1 / 2) * a * b = (1 / 2) * (a * b) ∧
     2⁻¹ * a * b = (1 / 2) * (a * b) ∧
     a * 2⁻¹ * b = (1 / 2) * (a * b)’
    by (rpt gen_tac >> REWRITE_TAC[GSYM realTheory.REAL_INV_1OVER] >>
        rpt conj_tac >>
        CONV_TAC (AC_CONV (realTheory.REAL_MUL_ASSOC, realTheory.REAL_MUL_COMM))) >>
  ASM_REWRITE_TAC[] >>
  ‘real (mcchannel (split_channel W (2 ** n) i) T {(y, u_prev)}) *
   real (mcchannel (split_channel W (2 ** n) i) F {(y, u_prev)}) =
   real (mcchannel (split_channel W (2 ** n) i) F {(y, u_prev)}) *
   real (mcchannel (split_channel W (2 ** n) i) T {(y, u_prev)})’
    by CONV_TAC (AC_CONV (realTheory.REAL_MUL_ASSOC, realTheory.REAL_MUL_COMM)) >>
  ASM_REWRITE_TAC[] >>
  REAL_ARITH_TAC
QED

(* Per-sample operation count of mc_butterfly_sample_vec at depth n:
   fast_sc_decode_cost W (2 ** n) EMPTY u y (the O(N log N) butterfly pass)
   plus 3 * 2^n coordinate ratio/sqrt evaluations.

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_sample_vec_cost_def:
  mc_sample_vec_cost (W : (bool, β) memoryless_channel)
    (n : num) ((u, y) : bool list # β list) : num =
    fast_sc_decode_cost W (2 ** n) ∅ u y + 3 * (2 ** n)
End

(* End-to-end operation count of Section IX Monte-Carlo polar code construction
   across M = LENGTH samples samples at blocklength N = 2^n:
   - M full-vector O(N log N) butterfly sample passes
   - Vector accumulation and division by M: (M + 1) * 2^n
   - Linear-time Median-of-Medians K-smallest selection (from Part 1):
     select_k_smallest_indices_cost.

   Written by Gemini (Google DeepMind AI agent) *)
Definition mc_polar_construct_cost_def:
  mc_polar_construct_cost (W : (bool, β) memoryless_channel)
    (n : num) (K : num) (samples : (bool list # β list) list) : num =
    SUM (MAP (mc_sample_vec_cost W n) samples) +
    (LENGTH samples + 1) * (2 ** n) +
    select_k_smallest_indices_cost
      (GENLIST (λi. mc_bhattacharyya_estimate W n i samples) (2 ** n))
      K
End

(* Upper bound on SUM (MAP (mc_sample_vec_cost W n) samples) across valid
   length-(2^n) samples.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem SUM_mc_sample_vec_cost_le[local]:
  ∀(W : (bool, β) memoryless_channel) n samples.
    EVERY (λ(u, y). LENGTH u = 2 ** n ∧ LENGTH y = 2 ** n) samples ⇒
    SUM (MAP (mc_sample_vec_cost W n) samples) ≤
      LENGTH samples * ((9 * n + 8) * (2 ** n))
Proof
  gen_tac >> gen_tac >> Induct_on ‘samples’ >- simp[] >>
  qx_gen_tac ‘h’ >> Cases_on ‘h’ >> rename1 ‘(u, y)’ >>
  simp[mc_sample_vec_cost_def, fast_sc_decode_cost_def] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  qspecl_then [‘n’, ‘GENLIST (λi. F) (2 ** n)’, ‘u’] mp_tac
    polar_complexityTheory.fast_sc_butterfly_cost_pow2_bounds >>
  strip_tac >>
  simp[ADD1, RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB] >> decide_tac
QED

(* Pure-:num arithmetic combination lemma for mc_polar_construct_complexity.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_complexity_arith[local]:
  ∀(M : num) (n : num) (P : num).
    1 ≤ n ∧ 0 < P ⇒
    M * ((9 * n + 8) * P) + ((M + 1) * P + (283 * P + 2)) ≤
      286 * (n * M * P + P)
Proof
  rpt strip_tac >>
  ‘M * ((9 * n + 8) * P) = (9 * n + 8) * (M * P)’
    by CONV_TAC (AC_CONV (MULT_ASSOC, MULT_COMM)) >>
  ‘(M + 1) * P = M * P + P’ by simp[RIGHT_ADD_DISTRIB] >>
  ‘(9 * n + 9) * (M * P) = (9 * n + 8) * (M * P) + M * P’
    by (‘9 * n + 9 = (9 * n + 8) + 1’ by decide_tac >>
        POP_ASSUM SUBST1_TAC >>
        REWRITE_TAC[RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >>
  ‘(9 * n + 9) * (M * P) ≤ (18 * n) * (M * P)’ by simp[] >>
  ‘(18 * n) * (M * P) = 18 * (n * M * P)’
    by CONV_TAC (AC_CONV (MULT_ASSOC, MULT_COMM)) >>
  decide_tac
QED

(* End-to-end O(M N log N + N) worst-case operation count bound for generic
   B-DMC Monte-Carlo polar code construction across M = LENGTH samples
   samples of blocklength N = 2^n (Erdal Arıkan, 2009, Section IX, p. 18;
   Roadmap Item 16).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_polar_construct_complexity:
  ∃(C : num).
    0 < C ∧
    ∀(W : (bool, β) memoryless_channel) n K samples.
      wf_bdmc W ∧ 1 ≤ n ∧ K ≤ 2 ** n ∧
      EVERY (λ(u, y). LENGTH u = 2 ** n ∧ LENGTH y = 2 ** n) samples ⇒
      mc_polar_construct_cost W n K samples ≤
        C * (LENGTH samples * (2 ** n) * LOG 2 (2 ** n) + 2 ** n)
Proof
  qexists_tac ‘286’ >> simp[] >> rpt strip_tac >>
  simp[mc_polar_construct_cost_def, logrootTheory.LOG_POW] >>
  drule SUM_mc_sample_vec_cost_le >>
  disch_then (qspec_then ‘W’ strip_assume_tac) >>
  qspecl_then
    [‘GENLIST (λi. mc_bhattacharyya_estimate W n i samples) (2 ** n)’, ‘K’]
    mp_tac select_k_smallest_indices_cost_linear >>
  simp[] >> strip_tac >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac
    ‘LENGTH samples * ((9 * n + 8) * 2 ** n) +
     ((LENGTH samples + 1) * 2 ** n + (283 * 2 ** n + 2))’ >>
  conj_tac
  >- (irule arithmeticTheory.LESS_EQ_LESS_EQ_MONO >> ASM_REWRITE_TAC[] >>
      irule arithmeticTheory.LESS_EQ_LESS_EQ_MONO >> simp[])
  >- (irule mc_complexity_arith >> simp[ZERO_LESS_EXP])
QED

(* Asymptotic complexityTheory.big_O formulation of per-sample butterfly
   Monte-Carlo Bhattacharyya estimation cost: O(N log N).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mc_sample_vec_cost_big_O:
  ∀(W : (bool, β) memoryless_channel) u_seq y_seq.
    (∀n. LENGTH (y_seq n) = 2 ** n) ⇒
    (λn. mc_sample_vec_cost W n (u_seq n, y_seq n)) ∈
      big_O (λn. (2 ** n) * LOG 2 (2 ** n))
Proof
  rw[complexityTheory.big_O_def] >>
  qexistsl_tac [‘0’, ‘17’] >> rpt strip_tac >>
  ‘1 ≤ n’ by decide_tac >>
  simp[mc_sample_vec_cost_def, fast_sc_decode_cost_def, logrootTheory.LOG_POW] >>
  ‘8 * (2 ** n) ≤ 8 * (2 ** n) * n’ by simp[] >>
  pop_assum mp_tac >>
  qspecl_then [‘n’, ‘GENLIST (λi. F) (2 ** n)’, ‘u_seq n’] mp_tac
    polar_complexityTheory.fast_sc_butterfly_cost_pow2_bounds >>
  decide_tac
QED

