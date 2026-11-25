(* ========================================================================= *)
(*   Binary-Input Discrete Memoryless Channels (B-DMCs), Binary Erasure      *)
(*   Channels (BECs), Output-Bijection Invariance, Parameter Bounds, and     *)
(*   Proposition 1 (Erdal Arıkan, 2009, arXiv:0807.3917, Section I-A &       *)
(*   Appendix A).                                                            *)
(*                                                                           *)
(*   Written by Gemini (Google DeepMind AI agent).                           *)
(* ========================================================================= *)

Theory bdmc

Ancestors
  combin arithmetic pair pred_set real real_sigma transc
  sigma_algebra extreal_base extreal measure probability
  lifting transfer fundamental extreal_information
  memoryless_channel bhattacharyya capacity

Libs
  dep_rewrite liftLib transferLib realLib;

val _ = hide "W";
val _ = hide "S";

local
  val zero_tm = realSyntax.zero_tm
  fun has_pos asl x =
    List.exists (fn a => aconv a (realSyntax.mk_less (zero_tm, x))) asl
  fun drop_asm asl tm =
    is_forall tm orelse is_exists tm orelse is_disj tm orelse
    markerSyntax.is_abbrev tm orelse
    (is_neg tm andalso
     (let val (l, r) = dest_eq (dest_neg tm) in
        aconv r zero_tm andalso has_pos asl l
      end handle HOL_ERR _ => false))
in
  val REAL_ASM_ARITH_TAC : tactic = fn (asl, w) =>
    (REPEAT (WEAKEN_TAC (drop_asm asl)) >>
     realLib.REAL_ASM_ARITH_TAC) (asl, w)
end;

(* ------------------------------------------------------------------------- *)
(* Block 1: memoryless_channel Quotient Helpers & Finite Sum Utilities       *)
(* ------------------------------------------------------------------------- *)

(* Every abstract memoryless_channel has a well-formed representation.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_memoryless_channel_REP[simp]:
  ∀W : (α, β) memoryless_channel.
    wf_memoryless_channel (memoryless_channel_REP W)
Proof
  gen_tac >>
  mp_tac (MATCH_MP (iffLR liftingTheory.Qt_alt) Qt_memoryless_channel) >>
  simp[memoryless_channelequiv_def]
QED

(* Left inverse property of memoryless_channel_ABS on memoryless_channel_REP.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem memoryless_channel_ABS_REP[simp]:
  ∀W : (α, β) memoryless_channel.
    memoryless_channel_ABS (memoryless_channel_REP W) = W
Proof
  gen_tac >>
  mp_tac (MATCH_MP (iffLR liftingTheory.Qt_alt) Qt_memoryless_channel) >>
  simp[]
QED

(* Representation-of-abstraction identity for well-formed channel triples.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem memoryless_channel_REP_ABS:
  ∀r : (α -> bool) # (β algebra) # (α -> β measure).
    wf_memoryless_channel r ⇒
    memoryless_channel_REP (memoryless_channel_ABS r) = r
Proof
  rw[] >>
  qspec_then ‘r’ mp_tac
    (MATCH_MP liftingTheory.R_repabs Qt_memoryless_channel) >>
  simp[memoryless_channelequiv_def]
QED

(* Extensionality of abstract memoryless channels via domain, sigma-algebra,
   and transition kernel.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem memoryless_channel_component_equality:
  ∀W1 W2 : (α, β) memoryless_channel.
    W1 = W2 ⇔
      mcdomain W1 = mcdomain W2 ∧
      mcsigma W1 = mcsigma W2 ∧
      mcchannel W1 = mcchannel W2
Proof
  rw[EQ_IMP_THM] >>
  ‘memoryless_channel_REP W1 = memoryless_channel_REP W2’
    by simp[memoryless_channel_REP_alt] >>
  metis_tac[memoryless_channel_ABS_REP]
QED

(* Alias for memoryless_channel extensionality theorem.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem memoryless_channel_EQ_THM:
  ∀W1 W2 : (α, β) memoryless_channel.
    W1 = W2 ⇔
      mcdomain W1 = mcdomain W2 ∧
      mcsigma W1 = mcsigma W2 ∧
      mcchannel W1 = mcchannel W2
Proof
  simp[memoryless_channel_component_equality]
QED

(* Projections of memoryless_channel_ABS on a well-formed representation.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem memoryless_channel_ABS_accessors:
  ∀r : (α -> bool) # (β algebra) # (α -> β measure).
    wf_memoryless_channel r ⇒
    mcdomain (memoryless_channel_ABS r) = mcdomain0 r ∧
    mcsigma (memoryless_channel_ABS r) = mcsigma0 r ∧
    mccodomain (memoryless_channel_ABS r) = mccodomain0 r ∧
    mcevents (memoryless_channel_ABS r) = mcevents0 r ∧
    mcchannel (memoryless_channel_ABS r) = mcchannel0 r ∧
    mcprob_space (memoryless_channel_ABS r) = mcprob_space0 r
Proof
  rw[mcdomain_def, mcsigma_def, mccodomain_def, mcevents_def,
     mcchannel_def, mcprob_space_def, memoryless_channel_REP_ABS]
QED

(* Unpacked projections of memoryless_channel_ABS on an explicit triple.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem memoryless_channel_ABS_triple_accessors:
  ∀(dom : α -> bool) (sig : β algebra) (ch : α -> β measure).
    wf_memoryless_channel (dom, sig, ch) ⇒
    mcdomain (memoryless_channel_ABS (dom, sig, ch)) = dom ∧
    mcsigma (memoryless_channel_ABS (dom, sig, ch)) = sig ∧
    mccodomain (memoryless_channel_ABS (dom, sig, ch)) = FST sig ∧
    mcevents (memoryless_channel_ABS (dom, sig, ch)) = SND sig ∧
    mcchannel (memoryless_channel_ABS (dom, sig, ch)) = ch
Proof
  rpt strip_tac >>
  drule memoryless_channel_ABS_accessors >>
  simp[mcdomain0_def, mcsigma0_def, mccodomain0_def, mcevents0_def,
       mcchannel0_def]
QED

(* Rewrites a filtered extreal sum over {y | y ∈ s ∧ P y} into an if-guarded
   sum over s.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem EXTREAL_SUM_IMAGE_FILTER:
  ∀s P (f : α -> extreal).
    FINITE s ∧
    ((∀y. y ∈ s ⇒ f y ≠ −∞) ∨ (∀y. y ∈ s ⇒ f y ≠ +∞)) ⇒
    ∑ f {y | y ∈ s ∧ P y} = ∑ (λy. if P y then f y else 0) s
Proof
  qx_genl_tac [‘s’, ‘P’, ‘f’] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  ‘{y | y ∈ s ∧ P y} = s ∩ {y | P y}’ by rw[Once EXTENSION] >>
  pop_assum SUBST1_TAC >>
  ‘FINITE (s ∩ {y | P y})’ by simp[INTER_FINITE] >>
  ‘∑ f (s ∩ {y | P y}) = ∑ (λy. if P y then f y else 0) (s ∩ {y | P y})’
    by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[]) >>
  pop_assum SUBST1_TAC >>
  strip_tac >>
  irule EXTREAL_SUM_IMAGE_INTER_ELIM >> simp[]
  >- (disj1_tac >> rw[extreal_of_num_def])
  >- (disj2_tac >> rw[extreal_of_num_def])
QED

(* Explicit two-point expansion of an extreal sum over UNIV(:bool).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem EXTREAL_SUM_IMAGE_BOOL[local]:
  (∀f : bool -> extreal. (∀b. f b ≠ −∞) ⇒ ∑ f 𝕌(:bool) = f T + f F) ∧
  (∀f : bool -> extreal. (∀b. f b ≠ −∞) ⇒ ∑ f {T; F} = f T + f F)
Proof
  conj_tac >> rw[UNIV_BOOL] >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_INSERT] >>
  simp[EXTREAL_SUM_IMAGE_SING, DELETE_NON_ELEMENT_RWT]
QED

(* Explicit three-point expansion of an extreal sum over {E_T; E_F; Erasure}.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem EXTREAL_SUM_IMAGE_ERASURE_BIT[local]:
  ∀f : erasure_bit -> extreal.
    (∀y. f y ≠ −∞) ⇒ ∑ f {E_T; E_F; Erasure} = f E_T + (f E_F + f Erasure)
Proof
  rw[] >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_INSERT] >>
  simp[EXTREAL_SUM_IMAGE_SING, DELETE_NON_ELEMENT_RWT] >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_INSERT] >>
  simp[EXTREAL_SUM_IMAGE_SING, DELETE_NON_ELEMENT_RWT]
QED

(* Reindexing a finite extreal sum along a bijection f : s -> t.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem EXTREAL_SUM_IMAGE_BIJ:
  ∀(s : α -> bool) (t : β -> bool) (f : α -> β) (g : β -> extreal).
    FINITE s ∧ BIJ f s t ∧
    ((∀y. y ∈ t ⇒ g y ≠ −∞) ∨ (∀y. y ∈ t ⇒ g y ≠ +∞)) ⇒
    ∑ g t = ∑ (g ∘ f) s
Proof
  rpt strip_tac >>
  ‘t = IMAGE f s ∧ INJ f s (IMAGE f s)’
    by (fs[BIJ_DEF, INJ_DEF, SURJ_DEF, Once EXTENSION] >> metis_tac[]) >>
  ‘∑ g t = ∑ g (IMAGE f s)’ by metis_tac[] >>
  pop_assum SUBST1_TAC >>
  irule EXTREAL_SUM_IMAGE_IMAGE >> simp[]
QED

(* Reindexing a finite real sum along a bijection f : s -> t.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_BIJ:
  ∀(s : α -> bool) (t : β -> bool) (f : α -> β) (g : β -> real).
    FINITE s ∧ BIJ f s t ⇒
    REAL_SUM_IMAGE g t = REAL_SUM_IMAGE (g ∘ f) s
Proof
  rpt strip_tac >>
  ‘t = IMAGE f s ∧ INJ f s (IMAGE f s)’
    by (fs[BIJ_DEF, INJ_DEF, SURJ_DEF, Once EXTENSION] >> metis_tac[]) >>
  ‘REAL_SUM_IMAGE g t = REAL_SUM_IMAGE g (IMAGE f s)’ by metis_tac[] >>
  pop_assum SUBST1_TAC >>
  irule REAL_SUM_IMAGE_IMAGE >> simp[]
QED

(* Base-2 logarithm of 2 in transcTheory.logr.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem logr_2_2[simp]:
  logr (2 : real) (2 : real) = 1
Proof
  simp[GSYM lg_def, lg_2]
QED

(* Two-point concavity inequality for logr 2 on (0, +infty).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem logr_2_concave[local]:
  ∀(x : real) y t.
    0 < x ∧ 0 < y ∧ 0 ≤ t ∧ t ≤ 1 ⇒
    t * logr 2 x + (1 - t) * logr 2 y ≤ logr 2 (t * x + (1 - t) * y)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPEC ‘2’ pos_concave_logr) >>
  simp[pos_concave_fn, pos_convex_fn] >>
  disch_then (qspecl_then [‘x’, ‘y’, ‘t’] mp_tac) >>
  simp[] >> REAL_ASM_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Block 2: Core B-DMC & Polymorphic BEC Definitions + Discrete PMF          *)
(* ------------------------------------------------------------------------- *)

(* Well-formed Binary-Input Discrete Memoryless Channel (B-DMC),
   Erdal Arıkan (2009), Section I-A, p. 1: binary input alphabet bool,
   finite output alphabet mccodomain W, and discrete powerset sigma-algebra.

   Validated by Eric Hall: require our memoryless channel to have boolean
   input, finite output, and the event space be the power set of the sample
   space.

   Written by Gemini (Google DeepMind AI agent) *)
Definition wf_bdmc_def:
  wf_bdmc (W : (bool, β) memoryless_channel) ⇔
    mcdomain W = 𝕌(:bool) ∧
    FINITE (mccodomain W) ∧
    mcevents W = POW (mccodomain W)
End

(* Polymorphic Binary Erasure Channel (BEC) predicate on arbitrary finite
   output alphabets, Erdal Arıkan (2009), Section I-A, p. 1: every output y
   either identifies the input unambiguously (W(y|0) W(y|1) = 0) or is an
   erasure symbol (W(y|0) = W(y|1)).

   Written by Gemini (Google DeepMind AI agent) *)
Definition is_bec_def:
  is_bec (W : (bool, β) memoryless_channel) ⇔
    wf_bdmc W ∧
    ∀y. y ∈ mccodomain W ⇒
        mcchannel W F {y} * mcchannel W T {y} = 0 ∨
        mcchannel W F {y} = mcchannel W T {y}
End

(* Erasure probability of a polymorphic BEC, Erdal Arıkan (2009), Section I-A,
   p. 1: sum of W(y|0) over all erasure symbols y with W(y|0) = W(y|1).

   Written by Gemini (Google DeepMind AI agent) *)
Definition bec_erasure_prob_def:
  bec_erasure_prob (W : (bool, β) memoryless_channel) : extreal =
    ∑ (λy. mcchannel W F {y})
      {y | y ∈ mccodomain W ∧ mcchannel W F {y} = mcchannel W T {y}}
End

(* Output sigma-algebra of a well-formed B-DMC.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_mcsigma:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒ mcsigma W = (mccodomain W, POW (mccodomain W))
Proof
  rw[wf_bdmc_def, mcsigma_alt]
QED

(* Output probability space property for any input bit of a well-formed B-DMC.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_prob_space:
  ∀(W : (bool, β) memoryless_channel) x.
    wf_bdmc W ⇒ prob_space (mccodomain W, POW (mccodomain W), mcchannel W x)
Proof
  rpt strip_tac >>
  qspecl_then [‘W’, ‘x’] mp_tac memoryless_channel_wf_prob_space_property >>
  fs[wf_bdmc_def, mcprob_space_alt]
QED

(* Empty and full-codomain transition probabilities of a well-formed B-DMC.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_mcchannel_empty_univ[simp]:
  ∀(W : (bool, β) memoryless_channel) x.
    wf_bdmc W ⇒
    mcchannel W x ∅ = 0 ∧ mcchannel W x (mccodomain W) = 1
Proof
  qx_genl_tac [‘W’, ‘x’] >> strip_tac >>
  qspecl_then [‘W’, ‘x’] mp_tac wf_bdmc_prob_space >> simp[] >> strip_tac >>
  conj_tac
  >- (drule PROB_EMPTY >> REWRITE_TAC[PROB] >> simp[])
  >- (drule PROB_UNIV >> REWRITE_TAC[PROB, p_space_def, m_space_def] >> simp[])
QED

(* Finite additivity of mcchannel W x on disjoint subsets of mccodomain W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_mcchannel_additive:
  ∀(W : (bool, β) memoryless_channel) x s t.
    wf_bdmc W ∧ s ⊆ mccodomain W ∧ t ⊆ mccodomain W ∧ DISJOINT s t ⇒
    mcchannel W x (s ∪ t) = mcchannel W x s + mcchannel W x t
Proof
  rpt strip_tac >>
  qspecl_then [‘W’, ‘x’] mp_tac wf_bdmc_prob_space >> simp[] >> strip_tac >>
  drule PROB_ADDITIVE >>
  disch_then (qspecl_then [‘s’, ‘t’] mp_tac) >>
  REWRITE_TAC[PROB, events_def, measurable_sets_def] >> simp[IN_POW]
QED

(* Non-emptiness of the output alphabet of any well-formed B-DMC.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_mccodomain_nonempty:
  ∀W : (bool, β) memoryless_channel. wf_bdmc W ⇒ mccodomain W ≠ ∅
Proof
  rpt strip_tac >>
  drule_then (qspec_then ‘F’ assume_tac) wf_bdmc_prob_space >>
  drule PROB_SPACE_NOT_EMPTY >> simp[p_space_def]
QED

(* Transition probabilities on subsets of mccodomain W lie in [0, 1] and are Normal.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_mcchannel_normal:
  ∀(W : (bool, β) memoryless_channel) x s.
    wf_bdmc W ∧ s ⊆ mccodomain W ⇒
    0 ≤ mcchannel W x s ∧ mcchannel W x s ≤ 1 ∧
    ∃r. 0 ≤ r ∧ r ≤ 1 ∧ mcchannel W x s = Normal r
Proof
  rpt strip_tac >>
  drule_then (qspec_then ‘x’ assume_tac) wf_bdmc_prob_space >>
  drule prob_normal >>
  disch_then (qspec_then ‘s’ mp_tac) >>
  simp[events_def, prob_def, IN_POW] >>
  strip_tac >>
  simp[extreal_of_num_def, extreal_le_eq] >>
  qexists_tac ‘r’ >> simp[]
QED

(* Singleton transition probabilities of a B-DMC lie in [0, 1] and are Normal.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_mcchannel_singleton_normal:
  ∀(W : (bool, β) memoryless_channel) x y.
    wf_bdmc W ∧ y ∈ mccodomain W ⇒
    0 ≤ mcchannel W x {y} ∧ mcchannel W x {y} ≤ 1 ∧
    ∃r. 0 ≤ r ∧ r ≤ 1 ∧ mcchannel W x {y} = Normal r
Proof
  qx_genl_tac [‘W’, ‘x’, ‘y’] >> strip_tac >>
  irule wf_bdmc_mcchannel_normal >> simp[SUBSET_DEF]
QED

(* Finite-additivity sum decomposition of mcchannel W x s over singletons.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_mcchannel_sum:
  ∀(W : (bool, β) memoryless_channel) x s.
    wf_bdmc W ∧ s ⊆ mccodomain W ⇒
    mcchannel W x s = ∑ (λy. mcchannel W x {y}) s
Proof
  rpt strip_tac >>
  drule_then (qspec_then ‘x’ assume_tac) wf_bdmc_prob_space >>
  ‘FINITE s’ by (fs[wf_bdmc_def] >> metis_tac[SUBSET_FINITE]) >>
  drule PROB_EXTREAL_SUM_IMAGE >>
  disch_then (qspec_then ‘s’ mp_tac) >>
  fs[events_def, prob_def, IN_POW, SUBSET_DEF]
QED

(* Singleton transition probabilities sum to 1 across mccodomain W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_mcchannel_sum_1:
  ∀(W : (bool, β) memoryless_channel) x.
    wf_bdmc W ⇒ ∑ (λy. mcchannel W x {y}) (mccodomain W) = 1
Proof
  rpt strip_tac >>
  drule_then (qspec_then ‘x’ assume_tac) wf_bdmc_prob_space >>
  drule PROB_EXTREAL_SUM_IMAGE_SPACE >>
  fs[wf_bdmc_def, p_space_def, events_def, prob_def, IN_POW, SUBSET_DEF]
QED

(* Real-valued transition probability mass extraction for a B-DMC.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_real_pmf:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    (∀x y. y ∈ mccodomain W ⇒
           mcchannel W x {y} = Normal (real (mcchannel W x {y})) ∧
           0 ≤ real (mcchannel W x {y}) ∧
           real (mcchannel W x {y}) ≤ 1) ∧
    (∀x. REAL_SUM_IMAGE (λy. real (mcchannel W x {y})) (mccodomain W) = 1)
Proof
  rpt strip_tac
  >- (qspecl_then [‘W’, ‘x’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
      simp[] >> strip_tac >> simp[])
  >- (qspecl_then [‘W’, ‘x’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
      simp[] >> strip_tac >> simp[])
  >- (qspecl_then [‘W’, ‘x’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
      simp[] >> strip_tac >> simp[])
  >- (drule_then (qspec_then ‘x’ mp_tac) wf_bdmc_mcchannel_sum_1 >>
      ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
      ‘∑ (λy. mcchannel W x {y}) (mccodomain W) =
       ∑ (λy. Normal (real (mcchannel W x {y}))) (mccodomain W)’
        by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >> qx_gen_tac ‘y’ >> strip_tac >>
            qspecl_then [‘W’, ‘x’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
            simp[] >> strip_tac >> simp[]) >>
      pop_assum SUBST1_TAC >>
      simp[EXTREAL_SUM_IMAGE_NORMAL, extreal_of_num_def])
QED

(* Non-looping real PMF bounds and sum-to-one property for simp/gvs contexts.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_real_pmf_safe[local]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    (∀x y. y ∈ mccodomain W ⇒
           0 ≤ real (mcchannel W x {y}) ∧
           real (mcchannel W x {y}) ≤ 1) ∧
    (∀x. REAL_SUM_IMAGE (λy. real (mcchannel W x {y})) (mccodomain W) = 1)
Proof
  gen_tac >> strip_tac >> drule wf_bdmc_real_pmf >> simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Block 3: BEC & BSC Concrete Channel Instances                             *)
(* ------------------------------------------------------------------------- *)

(* Concrete binary_erasure_channel p is a well-formed B-DMC for 0 ≤ p ≤ 1.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_binary_erasure_channel:
  ∀p. 0 ≤ p ∧ p ≤ 1 ⇒ wf_bdmc (binary_erasure_channel p)
Proof
  rw[wf_bdmc_def, binary_erasure_channel_def] >>
  drule_all wf_binary_erasure_channel0 >> strip_tac >>
  drule memoryless_channel_ABS_accessors >>
  simp[binary_erasure_channel0_def, mcdomain0_def, mccodomain0_def,
       mcevents0_def, mcsigma0_def, UNIV_BOOL]
QED

(* Singleton transition probabilities of binary_erasure_channel p.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_binary_erasure_channel_singleton:
  ∀p x y.
    0 ≤ p ∧ p ≤ 1 ⇒
    mcchannel (binary_erasure_channel p) x {y} =
      if y = Erasure then p
      else if y = bool_to_erasure_bit x then 1 - p
      else 0
Proof
  rw[binary_erasure_channel_def] >>
  drule_all wf_binary_erasure_channel0 >> strip_tac >>
  drule memoryless_channel_ABS_accessors >>
  simp[binary_erasure_channel0_def, mcchannel0_def, EXTREAL_SUM_IMAGE_SING]
QED

(* Concrete binary_erasure_channel p satisfies the polymorphic BEC predicate.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_bec_binary_erasure_channel:
  ∀p. 0 ≤ p ∧ p ≤ 1 ⇒ is_bec (binary_erasure_channel p)
Proof
  rw[is_bec_def, wf_bdmc_binary_erasure_channel] >>
  simp[mcchannel_binary_erasure_channel_singleton, bool_to_erasure_bit_def] >>
  Cases_on ‘y’ >> simp[mul_lzero, mul_rzero]
QED

(* Erasure probability of binary_erasure_channel p equals p (including p = 1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_erasure_prob_binary_erasure_channel:
  ∀p. 0 ≤ p ∧ p ≤ 1 ⇒ bec_erasure_prob (binary_erasure_channel p) = p
Proof
  rpt strip_tac >>
  ‘∃r. 0 ≤ r ∧ r ≤ 1 ∧ p = Normal r’
    by (Cases_on ‘p’ >> gvs[extreal_of_num_def, extreal_le_eq]) >>
  pop_assum strip_assume_tac >>
  ‘wf_bdmc (binary_erasure_channel p)’
    by (irule wf_bdmc_binary_erasure_channel >> simp[]) >>
  PURE_ONCE_REWRITE_TAC[bec_erasure_prob_def] >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_FILTER] >>
  conj_tac
  >- (conj_tac >- fs[wf_bdmc_def] >>
      disj1_tac >> qx_gen_tac ‘y’ >> strip_tac >>
      qspecl_then [‘binary_erasure_channel p’, ‘F’, ‘y’] mp_tac
        wf_bdmc_mcchannel_singleton_normal >>
      simp[] >> strip_tac >> gvs[]) >>
  drule_all wf_binary_erasure_channel0 >> strip_tac >>
  ‘mccodomain (binary_erasure_channel p) = {E_T; E_F; Erasure}’
    by (drule memoryless_channel_ABS_accessors >>
        simp[binary_erasure_channel_def, binary_erasure_channel0_def,
             mccodomain0_def, mcsigma0_def]) >>
  pop_assum SUBST1_TAC >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_ERASURE_BIT] >>
  conj_tac
  >- (qx_gen_tac ‘y’ >>
      rw[mcchannel_binary_erasure_channel_singleton, bool_to_erasure_bit_def,
         extreal_of_num_def, extreal_sub_eq]) >>
  simp[mcchannel_binary_erasure_channel_singleton, bool_to_erasure_bit_def] >>
  Cases_on ‘1 - Normal r = 0’ >> simp[add_lzero]
QED

(* Concrete binary_symmetric_channel p is a well-formed B-DMC for 0 ≤ p ≤ 1.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_binary_symmetric_channel:
  ∀p. 0 ≤ p ∧ p ≤ 1 ⇒ wf_bdmc (binary_symmetric_channel p)
Proof
  rw[wf_bdmc_def, binary_symmetric_channel_def] >>
  drule_all wf_binary_symmetric_channel0 >> strip_tac >>
  drule memoryless_channel_ABS_accessors >>
  simp[binary_symmetric_channel0_def, mcdomain0_def, mccodomain0_def,
       mcevents0_def, mcsigma0_def, UNIV_BOOL]
QED

(* Singleton transition probabilities of binary_symmetric_channel p.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem mcchannel_binary_symmetric_channel_singleton:
  ∀p x y.
    0 ≤ p ∧ p ≤ 1 ⇒
    mcchannel (binary_symmetric_channel p) x {y} =
      if y ≠ x then p else 1 - p
Proof
  rw[binary_symmetric_channel_def] >>
  drule_all wf_binary_symmetric_channel0 >> strip_tac >>
  drule memoryless_channel_ABS_accessors >>
  simp[binary_symmetric_channel0_def, mcchannel0_def, EXTREAL_SUM_IMAGE_SING]
QED

(* ------------------------------------------------------------------------- *)
(* Block 4: apply_channel_prob_space & symmetric_capacity_bdmc_sum           *)
(* ------------------------------------------------------------------------- *)

(* Well-formedness of the joint input-output probability space induced by a
   B-DMC W and any input probability distribution P on (mcdomain W, POW (mcdomain W)).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem prob_space_apply_channel_prob_space:
  ∀(W : (bool, β) memoryless_channel) P.
    wf_bdmc W ∧ prob_space (mcdomain W, POW (mcdomain W), P) ⇒
    prob_space (apply_channel_prob_space W P)
Proof
  rpt strip_tac >>
  drule wf_bdmc_mcsigma >> strip_tac >>
  ‘mcdomain W = 𝕌(:bool) ∧ FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  ‘FINITE (𝕌(:bool))’ by simp[UNIV_BOOL] >>
  simp[apply_channel_prob_space_def, prod_sigma_POW] >>
  DEP_REWRITE_TAC[prob_on_finite_set] >>
  simp[FINITE_CROSS, m_space_def, measurable_sets_def, measure_def,
       p_space_def, events_def, prob_def, apply_channel_distribution_def] >>
  rpt conj_tac
  >- (* positive *)
     (rw[positive_def, IN_POW, mul_rzero, EXTREAL_SUM_IMAGE_0] >>
      irule EXTREAL_SUM_IMAGE_POS >> simp[] >>
      qx_gen_tac ‘x’ >>
      ‘{y | (x, y) ∈ s} ⊆ mccodomain W’
        by (rw[SUBSET_DEF] >> fs[SUBSET_DEF] >>
            first_x_assum (drule_then mp_tac) >> simp[]) >>
      qspecl_then [‘W’, ‘x’, ‘{y | (x, y) ∈ s}’] mp_tac
        wf_bdmc_mcchannel_normal >>
      simp[] >> strip_tac >>
      ‘0 ≤ P {x}’
        by (‘prob_space (𝕌(:bool), POW 𝕌(:bool), P)’ by gvs[] >>
            drule PROB_POSITIVE >>
            disch_then (qspec_then ‘{x}’ mp_tac) >>
            REWRITE_TAC[PROB, events_def, measurable_sets_def] >>
            simp[IN_POW, SUBSET_DEF]) >>
      irule le_mul >> simp[])
  >- (* total mass = 1 *)
     (simp[mul_rone] >>
      ‘prob_space (𝕌(:bool), POW 𝕌(:bool), P)’ by gvs[] >>
      drule PROB_EXTREAL_SUM_IMAGE_SPACE >>
      REWRITE_TAC[PROB, p_space_def, m_space_def, events_def,
                  measurable_sets_def] >>
      simp[IN_POW, SUBSET_DEF])
  >- (* additive *)
     (rw[additive_def, IN_POW] >>
      ‘∀x : bool.
         {y | (x, y) ∈ s ∨ (x, y) ∈ t} = {y | (x, y) ∈ s} ∪ {y | (x, y) ∈ t} ∧
         DISJOINT {y | (x, y) ∈ s} {y | (x, y) ∈ t} ∧
         {y | (x, y) ∈ s} ⊆ mccodomain W ∧
         {y | (x, y) ∈ t} ⊆ mccodomain W’
        by (gen_tac >> rpt conj_tac
            >- rw[Once EXTENSION]
            >- (fs[DISJOINT_DEF, Once EXTENSION] >> metis_tac[])
            >- (rw[SUBSET_DEF] >> fs[SUBSET_DEF] >>
                first_x_assum (drule_then mp_tac) >> simp[])
            >- (rw[SUBSET_DEF] >> fs[SUBSET_DEF] >>
                first_x_assum (drule_then mp_tac) >> simp[])) >>
      ‘∀x : bool.
         P {x} * mcchannel W x {y | (x, y) ∈ s ∨ (x, y) ∈ t} =
         P {x} * mcchannel W x {y | (x, y) ∈ s} +
         P {x} * mcchannel W x {y | (x, y) ∈ t}’
        by (gen_tac >>
            first_x_assum (qspec_then ‘x’ strip_assume_tac) >>
            ‘mcchannel W x ({y | (x, y) ∈ s} ∪ {y | (x, y) ∈ t}) =
             mcchannel W x {y | (x, y) ∈ s} + mcchannel W x {y | (x, y) ∈ t}’
              by (irule wf_bdmc_mcchannel_additive >> simp[]) >>
            ‘∃rp. 0 ≤ rp ∧ rp ≤ 1 ∧ P {x} = Normal rp’
              by (‘prob_space (𝕌(:bool), POW 𝕌(:bool), P)’ by gvs[] >>
                  drule prob_normal >>
                  disch_then (qspec_then ‘{x}’ mp_tac) >>
                  REWRITE_TAC[PROB, events_def, measurable_sets_def] >>
                  simp[IN_POW, SUBSET_DEF] >>
                  metis_tac[]) >>
            ‘∃rs. 0 ≤ rs ∧ rs ≤ 1 ∧ mcchannel W x {y | (x, y) ∈ s} = Normal rs’
              by (qspecl_then [‘W’, ‘x’, ‘{y | (x, y) ∈ s}’] mp_tac
                    wf_bdmc_mcchannel_normal >> simp[]) >>
            ‘∃rt. 0 ≤ rt ∧ rt ≤ 1 ∧ mcchannel W x {y | (x, y) ∈ t} = Normal rt’
              by (qspecl_then [‘W’, ‘x’, ‘{y | (x, y) ∈ t}’] mp_tac
                    wf_bdmc_mcchannel_normal >> simp[]) >>
            gvs[extreal_add_eq, extreal_mul_eq, REAL_ADD_LDISTRIB]) >>
      DEP_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_ADD] >>
      conj_tac
      >- (simp[] >> disj1_tac >> qx_gen_tac ‘x’ >> strip_tac >>
          first_x_assum (qspec_then ‘x’ kall_tac) >>
          first_x_assum (qspec_then ‘x’ strip_assume_tac) >>
          ‘∃rp. 0 ≤ rp ∧ rp ≤ 1 ∧ P {x} = Normal rp’
            by (‘prob_space (𝕌(:bool), POW 𝕌(:bool), P)’ by gvs[] >>
                drule prob_normal >>
                disch_then (qspec_then ‘{x}’ mp_tac) >>
                REWRITE_TAC[PROB, events_def, measurable_sets_def] >>
                simp[IN_POW, SUBSET_DEF] >>
                metis_tac[]) >>
          ‘∃rs. 0 ≤ rs ∧ rs ≤ 1 ∧ mcchannel W x {y | (x, y) ∈ s} = Normal rs’
            by (qspecl_then [‘W’, ‘x’, ‘{y | (x, y) ∈ s}’] mp_tac
                  wf_bdmc_mcchannel_normal >> simp[]) >>
          ‘∃rt. 0 ≤ rt ∧ rt ≤ 1 ∧ mcchannel W x {y | (x, y) ∈ t} = Normal rt’
            by (qspecl_then [‘W’, ‘x’, ‘{y | (x, y) ∈ t}’] mp_tac
                  wf_bdmc_mcchannel_normal >> simp[]) >>
          gvs[extreal_mul_eq]) >>
      irule EXTREAL_SUM_IMAGE_EQ' >> simp[])
QED

(* Specialization of prob_space_apply_channel_prob_space to the uniform input
   distribution used in symmetric_capacity_def.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem prob_space_apply_channel_uniform:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    prob_space
      (apply_channel_prob_space W
         (uniform_distribution (mcdomain W, POW (mcdomain W))))
Proof
  rpt strip_tac >>
  irule prob_space_apply_channel_prob_space >> simp[] >>
  irule prob_space_on_finite_set' >>
  fs[wf_bdmc_def, p_space_def, m_space_def, events_def, measurable_sets_def,
     prob_def, measure_def, UNIV_BOOL]
QED

(* Uniform distribution mass on each boolean singleton is 1 / 2.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem uniform_distribution_bool_singleton[local]:
  ∀x : bool.
    uniform_distribution (𝕌(:bool), POW 𝕌(:bool)) {x} = 1 / 2 ∧
    uniform_distribution ({T; F}, POW {T; F}) {x} = 1 / 2
Proof
  gen_tac >>
  simp[uniform_distribution_def, space_def, UNIV_BOOL]
QED

(* Joint and marginal distributions of apply_channel_prob_space under uniform input.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem apply_channel_uniform_dists[local]:
  ∀(W : (bool, β) memoryless_channel) x y.
    wf_bdmc W ∧ y ∈ mccodomain W ⇒
    (let p = apply_channel_prob_space W
               (uniform_distribution (mcdomain W, POW (mcdomain W))) in
       joint_distribution p FST SND {(x, y)} = (1 / 2) * mcchannel W x {y} ∧
       distribution p FST {x} = 1 / 2 ∧
       distribution p SND {y} =
         (1 / 2) * mcchannel W F {y} + (1 / 2) * mcchannel W T {y})
Proof
  rpt strip_tac >> simp[LET_THM] >>
  ‘mcdomain W = 𝕌(:bool)’ by fs[wf_bdmc_def] >>
  qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  simp[] >> rpt strip_tac >>
  rpt conj_tac
  >- (* joint *)
     (simp[joint_distribution_def, apply_channel_prob_space_def,
           apply_channel_distribution_def, p_space_def, m_space_def,
           prob_def, measure_def, uniform_distribution_bool_singleton] >>
      ‘∀b : bool. {y' | ((b ⇔ x) ∧ y' = y) ∧ y' ∈ mccodomain W} =
                  if b = x then {y} else ∅’
        by (gen_tac >> rw[Once EXTENSION] >> metis_tac[]) >>
      simp[] >>
      DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_BOOL] >>
      conj_tac
      >- (Cases >> Cases_on ‘x’ >>
          simp[mul_rzero, extreal_of_num_def, extreal_div_eq, extreal_mul_eq]) >>
      Cases_on ‘x’ >> simp[mul_rzero, add_lzero, add_rzero])
  >- (* marginal FST *)
     (simp[distribution_def, apply_channel_prob_space_def,
           apply_channel_distribution_def, p_space_def, m_space_def,
           prob_def, measure_def, uniform_distribution_bool_singleton] >>
      ‘∀b : bool. {y' | (b ⇔ x) ∧ y' ∈ mccodomain W} =
                  if b = x then mccodomain W else ∅’
        by (gen_tac >> rw[Once EXTENSION] >> metis_tac[]) >>
      simp[] >>
      DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_BOOL] >>
      conj_tac
      >- (Cases >> Cases_on ‘x’ >>
          simp[mul_rzero, mul_rone, extreal_of_num_def, extreal_div_eq,
               extreal_mul_eq]) >>
      Cases_on ‘x’ >> simp[mul_rzero, mul_rone, add_lzero, add_rzero])
  >- (* marginal SND *)
     (simp[distribution_def, apply_channel_prob_space_def,
           apply_channel_distribution_def, p_space_def, m_space_def,
           prob_def, measure_def, uniform_distribution_bool_singleton] >>
      ‘{y' | y' = y ∧ y' ∈ mccodomain W} = {y}’
        by (rw[Once EXTENSION] >> metis_tac[]) >>
      simp[] >>
      DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_BOOL] >>
      conj_tac
      >- (Cases >> simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq]) >>
      simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq, extreal_add_eq] >>
      REAL_ASM_ARITH_TAC)
QED

(* Reduction of measure-theoretic symmetric_capacity W to Erdal Arıkan's
   explicit double-sum formula (arXiv:0807.3917, Section I-A, p. 1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem symmetric_capacity_bdmc_sum:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    symmetric_capacity W =
      ∑ (λy. ∑ (λx. (1 / 2) * mcchannel W x {y} *
                    logr 2 (mcchannel W x {y} /
                            ((1 / 2) * mcchannel W F {y} +
                             (1 / 2) * mcchannel W T {y})))
               𝕌(:bool))
        (mccodomain W)
Proof
  rpt strip_tac >>
  drule wf_bdmc_mcsigma >> strip_tac >>
  drule prob_space_apply_channel_uniform >> strip_tac >>
  ‘mcdomain W = 𝕌(:bool) ∧ FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  qabbrev_tac ‘p = apply_channel_prob_space W
                     (uniform_distribution (mcdomain W, POW (mcdomain W)))’ >>
  ‘p_space p = {T; F} × mccodomain W ∧ events p = POW ({T; F} × mccodomain W)’
    by (simp[Abbr ‘p’, apply_channel_prob_space_def, p_space_def, m_space_def,
             events_def, measurable_sets_def] >>
        gvs[prod_sigma_POW]) >>
  ‘random_variable FST p ({T; F}, POW {T; F}) ∧
   random_variable SND p (mccodomain W, POW (mccodomain W))’
    by (rw[random_variable_def, IN_MEASURABLE, IN_FUNSET, space_def,
           subsets_def, IN_POW, INTER_SUBSET] >>
        Cases_on ‘x’ >> fs[]) >>
  simp[symmetric_capacity_def] >>
  ‘mutual_information 2 p ({T; F}, POW {T; F})
      (mccodomain W, POW (mccodomain W)) FST SND =
   ∑ (λ(x, y). joint_distribution p FST SND {(x, y)} *
               logr 2 (joint_distribution p FST SND {(x, y)} /
                       (distribution p FST {x} * distribution p SND {y})))
     ({T; F} × mccodomain W)’
    by (irule finite_mutual_information_reduce_POW >>
        simp[FINITE_CROSS]) >>
  ‘mcsigma W = (mccodomain W, POW (mccodomain W)) ∧
   apply_channel_prob_space W (uniform_distribution ({T; F}, POW {T; F})) = p’
    by gvs[Abbr ‘p’] >>
  simp[] >>
  qabbrev_tac ‘g = λ(x : bool) (y : β).
                     (1 / 2) * mcchannel W x {y} *
                     logr 2 (mcchannel W x {y} /
                             ((1 / 2) * mcchannel W F {y} +
                              (1 / 2) * mcchannel W T {y}))’ >>
  ‘∀x y. y ∈ mccodomain W ⇒ g x y ≠ −∞’
    by (qx_genl_tac [‘x’, ‘y’] >> strip_tac >> simp[Abbr ‘g’] >>
        qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
        qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
        simp[] >> rpt strip_tac >>
        Cases_on ‘(1 / 2 : real) * r + (1 / 2) * r' = 0’
        >- (‘r = 0 ∧ r' = 0’ by REAL_ASM_ARITH_TAC >>
            Cases_on ‘x’ >> gvs[] >>
            RULE_ASSUM_TAC (PURE_REWRITE_RULE [normal_0, mul_rzero, mul_lzero]) >>
            gvs[extreal_of_num_def])
        >- (Cases_on ‘x’ >>
            gvs[extreal_of_num_def, extreal_div_eq, extreal_mul_eq,
                extreal_add_eq, extreal_logr_def])) >>
  ‘∑ (λ(x, y). joint_distribution p FST SND {(x, y)} *
               logr 2 (joint_distribution p FST SND {(x, y)} /
                       (distribution p FST {x} * distribution p SND {y})))
     ({T; F} × mccodomain W) =
   ∑ (λz. g (FST z) (SND z)) ({T; F} × mccodomain W)’
    by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[FINITE_CROSS, FORALL_PROD] >>
        qx_genl_tac [‘x’, ‘y’] >> strip_tac >>
        mp_tac (Q.SPECL [‘W’, ‘x’, ‘y’] apply_channel_uniform_dists) >>
        simp[LET_THM, Abbr ‘g’] >> strip_tac >>
        qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
        qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
        simp[] >> rpt strip_tac >>
        Cases_on ‘(1 / 2 : real) * r + (1 / 2) * r' = 0’
        >- (‘r = 0 ∧ r' = 0’ by REAL_ASM_ARITH_TAC >>
            Cases_on ‘x’ >> gvs[] >>
            PURE_REWRITE_TAC[normal_0, mul_rzero, mul_lzero] >>
            REFL_TAC)
        >- (‘∀v : real. ((1 / 2) * v) / ((1 / 2) * ((1 / 2) * r + (1 / 2) * r')) =
                        v / ((1 / 2) * r + (1 / 2) * r')’
              by (gen_tac >> irule REAL_DIV_LMUL_CANCEL >> simp[]) >>
            Cases_on ‘x’ >>
            simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq,
                 extreal_add_eq, extreal_logr_def])) >>
  pop_assum SUBST1_TAC >>
  ‘∑ (λz. g (FST z) (SND z)) ({T; F} × mccodomain W) =
   ∑ (λx. ∑ (g x) (mccodomain W)) {T; F}’
    by (CONV_TAC SYM_CONV >>
        irule EXTREAL_SUM_IMAGE_SUM_IMAGE >>
        simp[] >> disj1_tac >> simp[FORALL_PROD]) >>
  pop_assum SUBST1_TAC >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_BOOL] >>
  conj_tac
  >- (gen_tac >> irule EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp[]) >>
  DEP_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_ADD] >>
  conj_tac
  >- (simp[] >> disj1_tac >> simp[]) >>
  irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_BOOL] >>
  simp[Abbr ‘g’]
QED

(* Real-valued single-output contribution to symmetric capacity I(W).

   Written by Gemini (Google DeepMind AI agent) *)
Definition cap_term_def:
  cap_term (a : real) (b : real) : real =
    (1 / 2) * a * logr 2 (a / ((1 / 2) * a + (1 / 2) * b)) +
    (1 / 2) * b * logr 2 (b / ((1 / 2) * a + (1 / 2) * b))
End

(* Exact Normal / REAL_SUM_IMAGE representation of symmetric_capacity W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem symmetric_capacity_real_sum:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    symmetric_capacity W =
      Normal (REAL_SUM_IMAGE
                (λy. cap_term (real (mcchannel W F {y}))
                              (real (mcchannel W T {y})))
                (mccodomain W))
Proof
  rpt strip_tac >>
  drule symmetric_capacity_bdmc_sum >> strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
  irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  simp[] >> rpt strip_tac >>
  Cases_on ‘(1 / 2 : real) * r + (1 / 2) * r' = 0’
  >- (‘r = 0 ∧ r' = 0’ by REAL_ASM_ARITH_TAC >>
      DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_BOOL] >>
      conj_tac
      >- (Cases >> gvs[] >>
          PURE_REWRITE_TAC[normal_0, mul_rzero, mul_lzero] >>
          simp[extreal_of_num_def]) >>
      gvs[cap_term_def] >>
      PURE_REWRITE_TAC[normal_0, mul_rzero, mul_lzero, add_lzero] >>
      REFL_TAC)
  >- (DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_BOOL] >>
      conj_tac
      >- (Cases >>
          simp[extreal_of_num_def, extreal_div_eq, extreal_add_eq,
               extreal_mul_eq, extreal_logr_def]) >>
      simp[cap_term_def, extreal_of_num_def, extreal_div_eq, extreal_add_eq,
           extreal_mul_eq, extreal_logr_def] >>
      REAL_ASM_ARITH_TAC)
QED

(* ------------------------------------------------------------------------- *)
(* Block 5: Parameter Bounds & BEC Exact Formulas                            *)
(* ------------------------------------------------------------------------- *)

(* Exact Normal / REAL_SUM_IMAGE representation of bhattacharyya W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bhattacharyya_real_sum:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    bhattacharyya W =
      Normal (REAL_SUM_IMAGE
                (λy. sqrt (real (mcchannel W F {y}) *
                           real (mcchannel W T {y})))
                (mccodomain W))
Proof
  rpt strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  simp[bhattacharyya_def, GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
  irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  simp[] >> rpt strip_tac >>
  simp[extreal_mul_eq, extreal_sqrt_def]
QED

(* Bhattacharyya parameter bounds 0 ≤ Z(W) ≤ 1 and finiteness (Normal witness).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bhattacharyya_bounds:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    0 ≤ bhattacharyya W ∧
    bhattacharyya W ≤ 1 ∧
    ∃z. 0 ≤ z ∧ z ≤ 1 ∧ bhattacharyya W = Normal z
Proof
  gen_tac >> strip_tac >>
  drule bhattacharyya_real_sum >> strip_tac >>
  drule wf_bdmc_real_pmf_safe >> strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  qabbrev_tac ‘z = REAL_SUM_IMAGE
                     (λy. sqrt (real (mcchannel W F {y}) *
                                real (mcchannel W T {y})))
                     (mccodomain W)’ >>
  ‘0 ≤ z’
    by (simp[Abbr ‘z’] >> irule REAL_SUM_IMAGE_POS >> simp[] >>
        rw[] >> irule realTheory.SQRT_POS_LE >> irule REAL_LE_MUL >> simp[]) >>
  ‘z ≤ 1’
    by (simp[Abbr ‘z’] >>
        ‘REAL_SUM_IMAGE
           (λy. sqrt (real (mcchannel W F {y}) * real (mcchannel W T {y})))
           (mccodomain W) ≤
         REAL_SUM_IMAGE
           (λy. (1 / 2) * real (mcchannel W F {y}) +
                (1 / 2) * real (mcchannel W T {y}))
           (mccodomain W)’
          by (irule REAL_SUM_IMAGE_MONO >> simp[] >>
              qx_gen_tac ‘y’ >> strip_tac >>
              qspecl_then [‘real (mcchannel W F {y})’,
                           ‘real (mcchannel W T {y})’]
                mp_tac AGM_SQRT >>
              simp[] >> REAL_ASM_ARITH_TAC) >>
        ‘REAL_SUM_IMAGE
           (λy. (1 / 2) * real (mcchannel W F {y}) +
                (1 / 2) * real (mcchannel W T {y}))
           (mccodomain W) = 1’
          by (simp[REAL_SUM_IMAGE_ADD, REAL_SUM_IMAGE_CMUL]) >>
        REAL_ASM_ARITH_TAC) >>
  simp[extreal_of_num_def, extreal_le_eq] >>
  qexists_tac ‘z’ >> simp[]
QED

(* Bounds 0 ≤ ε(W) ≤ 1 and Normal representation for bec_erasure_prob W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_erasure_prob_bounds:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    0 ≤ bec_erasure_prob W ∧
    bec_erasure_prob W ≤ 1 ∧
    ∃e. 0 ≤ e ∧ e ≤ 1 ∧ bec_erasure_prob W = Normal e
Proof
  gen_tac >> strip_tac >>
  drule wf_bdmc_real_pmf_safe >> strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  ‘bec_erasure_prob W =
   Normal (REAL_SUM_IMAGE
             (λy. if real (mcchannel W F {y}) = real (mcchannel W T {y})
                  then real (mcchannel W F {y}) else 0)
             (mccodomain W))’
    by (simp[bec_erasure_prob_def] >>
        DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_FILTER] >>
        conj_tac
        >- (simp[] >> disj1_tac >> qx_gen_tac ‘y’ >> strip_tac >>
            qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
            simp[] >> strip_tac >> gvs[]) >>
        simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
        irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
        qx_gen_tac ‘y’ >> strip_tac >>
        qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
        qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
        simp[] >> rpt strip_tac >>
        rw[extreal_of_num_def]) >>
  qabbrev_tac ‘e = REAL_SUM_IMAGE
                     (λy. if real (mcchannel W F {y}) = real (mcchannel W T {y})
                          then real (mcchannel W F {y}) else 0)
                     (mccodomain W)’ >>
  ‘0 ≤ e’
    by (simp[Abbr ‘e’] >> irule REAL_SUM_IMAGE_POS >> simp[] >> rw[]) >>
  ‘e ≤ 1’
    by (simp[Abbr ‘e’] >>
        irule REAL_LE_TRANS >>
        qexists_tac ‘REAL_SUM_IMAGE (λy. real (mcchannel W F {y})) (mccodomain W)’ >>
        conj_tac
        >- (irule REAL_SUM_IMAGE_MONO >> simp[] >> rw[])
        >- simp[]) >>
  simp[extreal_of_num_def, extreal_le_eq] >>
  qexists_tac ‘e’ >> simp[]
QED

(* For any polymorphic BEC W, Z(W) equals its erasure probability ε(W)
   (Erdal Arıkan, 2009, Section I-A, p. 1).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_bec_bhattacharyya:
  ∀W : (bool, β) memoryless_channel.
    is_bec W ⇒ bhattacharyya W = bec_erasure_prob W
Proof
  rw[is_bec_def, bhattacharyya_def, bec_erasure_prob_def] >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_FILTER] >>
  conj_tac
  >- (simp[] >> disj1_tac >> qx_gen_tac ‘y’ >> strip_tac >>
      qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
      simp[] >> strip_tac >> gvs[]) >>
  irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  simp[] >> rpt strip_tac >>
  Cases_on ‘r = r'’
  >- (gvs[extreal_mul_eq, extreal_sqrt_def] >>
      PURE_REWRITE_TAC[GSYM realTheory.POW_2] >>
      irule (GEN_ALL realTheory.POW_2_SQRT) >> simp[])
  >- (first_x_assum (drule_then mp_tac) >>
      simp[extreal_mul_eq, extreal_of_num_def, extreal_sqrt_def] >>
      strip_tac >> simp[realTheory.SQRT_0])
QED

(* Pointwise bounds 0 ≤ cap_term a b ≤ (a + b) / 2 for non-negative reals.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem cap_term_bounds[local]:
  ∀(a : real) (b : real).
    0 ≤ a ∧ 0 ≤ b ⇒
    0 ≤ cap_term a b ∧ cap_term a b ≤ (1 / 2) * a + (1 / 2) * b
Proof
  qx_genl_tac [‘a’, ‘b’] >> strip_tac >>
  Cases_on ‘a = 0’
  >- (Cases_on ‘b = 0’
      >- simp[cap_term_def]
      >- (‘0 < b ∧ 0 < (1 / 2 : real) * b ∧ (1 / 2 : real) * b ≠ 0’
            by REAL_ASM_ARITH_TAC >>
          pop_assum strip_assume_tac >>
          ‘b / ((1 / 2 : real) * b) = 2’
            by (simp[REAL_EQ_LDIV_EQ] >> REAL_ASM_ARITH_TAC) >>
          simp[cap_term_def]))
  >> Cases_on ‘b = 0’
  >- (‘0 < a ∧ 0 < (1 / 2 : real) * a ∧ (1 / 2 : real) * a ≠ 0’
        by REAL_ASM_ARITH_TAC >>
      pop_assum strip_assume_tac >>
      ‘a / ((1 / 2 : real) * a) = 2’
        by (simp[REAL_EQ_LDIV_EQ] >> REAL_ASM_ARITH_TAC) >>
      simp[cap_term_def])
  >> ‘0 < a ∧ 0 < b’ by REAL_ASM_ARITH_TAC >>
  pop_assum strip_assume_tac >>
  qabbrev_tac ‘m = (1 / 2 : real) * a + (1 / 2 : real) * b’ >>
  qabbrev_tac ‘s = a + b’ >>
  ‘0 < m ∧ 0 < s ∧ m ≠ 0 ∧ s ≠ 0 ∧ s = 2 * m ∧ a + b = s’
    by (simp[Abbr ‘m’, Abbr ‘s’] >> REAL_ASM_ARITH_TAC) >>
  pop_assum strip_assume_tac >>
  conj_tac
  >- (* 0 <= cap_term a b via concavity of logr 2 *)
     (qabbrev_tac ‘w = a / s’ >>
      ‘0 ≤ w ∧ w ≤ 1 ∧ 1 - w = b / s’
        by (simp[Abbr ‘w’, REAL_SUB_LDISTRIB] >> REAL_ASM_ARITH_TAC) >>
      pop_assum strip_assume_tac >>
      ‘0 < m / a ∧ 0 < m / b ∧ 0 < a / m ∧ 0 < b / m’
        by (simp[] >> REAL_ASM_ARITH_TAC) >>
      pop_assum strip_assume_tac >>
      ‘w * (m / a) + (1 - w) * (m / b) = 1’
        by (qpat_assum ‘1 - w = _’ SUBST1_TAC >>
            simp[Abbr ‘w’, REAL_INV_MUL]) >>
      ‘logr 2 (m / a) = -logr 2 (a / m) ∧ logr 2 (m / b) = -logr 2 (b / m)’
        by (conj_tac >> (simp[logr_div] >> REAL_ASM_ARITH_TAC)) >>
      ‘w * -logr 2 (a / m) + (1 - w) * -logr 2 (b / m) ≤ 0’
        by (qspecl_then [‘m / a’, ‘m / b’, ‘w’] mp_tac logr_2_concave >>
            qpat_x_assum ‘w * (m / a) + _ = 1’ SUBST1_TAC >>
            qpat_x_assum ‘logr 2 (m / a) = _’ SUBST1_TAC >>
            qpat_x_assum ‘logr 2 (m / b) = _’ SUBST1_TAC >>
            PURE_REWRITE_TAC[logr_1] >>
            disch_then irule >> simp[]) >>
      ‘0 ≤ s * -(w * -logr 2 (a / m) + (1 - w) * -logr 2 (b / m))’
        by (irule REAL_LE_MUL >> rpt conj_tac >> REAL_ASM_ARITH_TAC) >>
      pop_assum mp_tac >>
      ‘s * -(w * -logr 2 (a / m) + (1 - w) * -logr 2 (b / m)) =
       (s * w) * logr 2 (a / m) + (s * (1 - w)) * logr 2 (b / m)’
        by (PURE_REWRITE_TAC[REAL_MUL_RNEG, REAL_NEG_ADD, REAL_NEG_NEG,
                             REAL_ADD_LDISTRIB, REAL_MUL_ASSOC] >>
            REFL_TAC) >>
      pop_assum SUBST1_TAC >>
      ‘s * w = a ∧ s * (1 - w) = b’
        by (conj_tac
            >- simp[Abbr ‘w’, REAL_DIV_LMUL]
            >- (qpat_x_assum ‘1 - w = _’ SUBST1_TAC >> simp[REAL_DIV_LMUL])) >>
      qpat_x_assum ‘s * w = a’ SUBST1_TAC >>
      qpat_x_assum ‘s * (1 - w) = b’ SUBST1_TAC >>
      ‘(1 / 2) * a + (1 / 2) * b = m’ by simp[Abbr ‘m’] >>
      PURE_ONCE_REWRITE_TAC[cap_term_def] >>
      pop_assum SUBST1_TAC >> simp[] >> REAL_ASM_ARITH_TAC)
  >- (* cap_term a b <= m *)
     (‘0 < a / m ∧ a / m ≤ 2 ∧ 0 < b / m ∧ b / m ≤ 2’
        by (simp[] >> REAL_ASM_ARITH_TAC) >>
      pop_assum strip_assume_tac >>
      ‘logr 2 (a / m) ≤ 1 ∧ logr 2 (b / m) ≤ 1’
        by (conj_tac
            >- (qspecl_then [‘a / m’, ‘2’, ‘2’] mp_tac LOGR_MONO_LE_IMP >> simp[])
            >- (qspecl_then [‘b / m’, ‘2’, ‘2’] mp_tac LOGR_MONO_LE_IMP >> simp[])) >>
      pop_assum strip_assume_tac >>
      ‘(1 / 2) * a * logr 2 (a / m) ≤ (1 / 2) * a * 1 ∧
       (1 / 2) * b * logr 2 (b / m) ≤ (1 / 2) * b * 1’
        by (conj_tac >> irule REAL_LE_LMUL_IMP >> simp[] >> rpt conj_tac >> REAL_ASM_ARITH_TAC) >>
      pop_assum strip_assume_tac >>
      ‘(1 / 2) * a + (1 / 2) * b = m’ by simp[Abbr ‘m’] >>
      PURE_ONCE_REWRITE_TAC[cap_term_def] >>
      pop_assum SUBST1_TAC >> simp[] >> REAL_ASM_ARITH_TAC)
QED

(* Symmetric capacity bounds 0 ≤ I(W) ≤ 1 and finiteness (Normal witness).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem symmetric_capacity_bounds:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    0 ≤ symmetric_capacity W ∧
    symmetric_capacity W ≤ 1 ∧
    ∃c. 0 ≤ c ∧ c ≤ 1 ∧ symmetric_capacity W = Normal c
Proof
  gen_tac >> strip_tac >>
  drule symmetric_capacity_real_sum >> strip_tac >>
  drule wf_bdmc_real_pmf_safe >> strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  qabbrev_tac ‘c = REAL_SUM_IMAGE
                     (λy. cap_term (real (mcchannel W F {y}))
                                   (real (mcchannel W T {y})))
                     (mccodomain W)’ >>
  ‘0 ≤ c’
    by (simp[Abbr ‘c’] >> irule REAL_SUM_IMAGE_POS >> simp[] >>
        qx_gen_tac ‘y’ >> strip_tac >>
        qspecl_then [‘real (mcchannel W F {y})’, ‘real (mcchannel W T {y})’]
          mp_tac cap_term_bounds >> simp[]) >>
  ‘c ≤ 1’
    by (simp[Abbr ‘c’] >>
        ‘REAL_SUM_IMAGE
           (λy. cap_term (real (mcchannel W F {y})) (real (mcchannel W T {y})))
           (mccodomain W) ≤
         REAL_SUM_IMAGE
           (λy. (1 / 2) * real (mcchannel W F {y}) +
                (1 / 2) * real (mcchannel W T {y}))
           (mccodomain W)’
          by (irule REAL_SUM_IMAGE_MONO >> simp[] >>
              qx_gen_tac ‘y’ >> strip_tac >>
              qspecl_then [‘real (mcchannel W F {y})’,
                           ‘real (mcchannel W T {y})’]
                mp_tac cap_term_bounds >> simp[]) >>
        ‘REAL_SUM_IMAGE
           (λy. (1 / 2) * real (mcchannel W F {y}) +
                (1 / 2) * real (mcchannel W T {y}))
           (mccodomain W) = 1’
          by simp[REAL_SUM_IMAGE_ADD, REAL_SUM_IMAGE_CMUL] >>
        REAL_ASM_ARITH_TAC) >>
  simp[extreal_of_num_def, extreal_le_eq] >>
  qexists_tac ‘c’ >> simp[]
QED

(* Pointwise capacity summand identity for BEC output pairs (a * b = 0 or a = b).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_cap_term_real[local]:
  ∀(a : real) (b : real).
    0 ≤ a ∧ 0 ≤ b ∧ (a * b = 0 ∨ a = b) ⇒
    cap_term a b = ((1 / 2) * a + (1 / 2) * b) - (if a = b then a else 0)
Proof
  ntac 2 gen_tac >> disch_then (CONJUNCTS_THEN2 strip_assume_tac
    (CONJUNCTS_THEN2 strip_assume_tac assume_tac)) >>
  Cases_on ‘a = b’
  >- (ASM_REWRITE_TAC[cap_term_def] >>
      ‘(1 / 2 : real) * b + (1 / 2) * b = b’ by REAL_ARITH_TAC >>
      pop_assum SUBST1_TAC >>
      Cases_on ‘b = 0’ >> simp[REAL_DIV_REFL, logr_1])
  >- (qpat_x_assum ‘_ ∨ _’ mp_tac >> ASM_REWRITE_TAC[REAL_ENTIRE] >> strip_tac
      >- (‘b ≠ 0’ by (CCONTR_TAC >> gvs[]) >>
          ‘0 < (1 / 2 : real) * b’ by REAL_ASM_ARITH_TAC >>
          ‘b / ((1 / 2 : real) * b) = 2’
            by (DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ] >> ASM_REWRITE_TAC[] >>
                REAL_ARITH_TAC) >>
          ASM_REWRITE_TAC[cap_term_def, REAL_MUL_RZERO, REAL_MUL_LZERO,
                          REAL_ADD_LID, REAL_SUB_RZERO] >>
          pop_assum SUBST1_TAC >> simp[])
      >- (‘a ≠ 0’ by (CCONTR_TAC >> gvs[]) >>
          ‘0 < (1 / 2 : real) * a’ by REAL_ASM_ARITH_TAC >>
          ‘a / ((1 / 2 : real) * a) = 2’
            by (DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ] >> ASM_REWRITE_TAC[] >>
                REAL_ARITH_TAC) >>
          ASM_REWRITE_TAC[cap_term_def, REAL_MUL_RZERO, REAL_MUL_LZERO,
                          REAL_ADD_RID, REAL_SUB_RZERO] >>
          pop_assum SUBST1_TAC >> simp[]))
QED

(* Exact Normal / REAL_SUM_IMAGE representation of bec_erasure_prob W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_erasure_prob_real_sum[local]:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    bec_erasure_prob W =
      Normal (REAL_SUM_IMAGE
                (λy. if real (mcchannel W F {y}) = real (mcchannel W T {y})
                     then real (mcchannel W F {y}) else 0)
                (mccodomain W))
Proof
  rpt strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  simp[bec_erasure_prob_def] >>
  DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_FILTER] >>
  conj_tac
  >- (simp[] >> disj1_tac >> qx_gen_tac ‘y’ >> strip_tac >>
      qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
      simp[] >> strip_tac >> gvs[]) >>
  simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
  irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  simp[] >> rpt strip_tac >>
  rw[extreal_of_num_def]
QED

(* For any polymorphic BEC W, I(W) = 1 - ε(W) (Erdal Arıkan, 2009, Section I-A).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_bec_symmetric_capacity:
  ∀W : (bool, β) memoryless_channel.
    is_bec W ⇒ symmetric_capacity W = 1 - bec_erasure_prob W
Proof
  rpt strip_tac >>
  ‘wf_bdmc W’ by fs[is_bec_def] >>
  drule symmetric_capacity_real_sum >> strip_tac >>
  drule bec_erasure_prob_real_sum >> strip_tac >>
  drule wf_bdmc_real_pmf_safe >> strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  simp[extreal_of_num_def, extreal_sub_eq] >>
  ‘1 = (1 / 2) * REAL_SUM_IMAGE (λy. real (mcchannel W F {y})) (mccodomain W) +
       (1 / 2) * REAL_SUM_IMAGE (λy. real (mcchannel W T {y})) (mccodomain W)’
    by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[GSYM REAL_SUM_IMAGE_CMUL, GSYM REAL_SUM_IMAGE_ADD, GSYM REAL_SUM_IMAGE_SUB] >>
  irule REAL_SUM_IMAGE_EQ >> simp[] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  qspecl_then [‘real (mcchannel W F {y})’, ‘real (mcchannel W T {y})’]
    mp_tac bec_cap_term_real >>
  simp[] >>
  qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum ‘is_bec W’ (mp_tac o REWRITE_RULE[is_bec_def]) >>
  disch_then (qspec_then ‘y’ mp_tac o CONJUNCT2) >>
  rw[extreal_of_num_def, extreal_mul_eq] >> gvs[]
QED

(* ------------------------------------------------------------------------- *)
(* Block 6: Output-Bijection Invariance Lemmas                               *)
(* ------------------------------------------------------------------------- *)

(* Output-alphabet bijection relation between two B-DMCs W1 and W2.

   Written by Gemini (Google DeepMind AI agent) *)
Definition bdmc_output_bij_def:
  bdmc_output_bij (f : α -> β)
                  (W1 : (bool, α) memoryless_channel)
                  (W2 : (bool, β) memoryless_channel) ⇔
    wf_bdmc W1 ∧ wf_bdmc W2 ∧
    BIJ f (mccodomain W1) (mccodomain W2) ∧
    ∀x y. y ∈ mccodomain W1 ⇒ mcchannel W2 x {f y} = mcchannel W1 x {y}
End

(* Transfer of wf_bdmc across an output-alphabet bijection onto a discrete
   binary-input channel.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem wf_bdmc_output_bij:
  ∀(W1 : (bool, α) memoryless_channel)
   (W2 : (bool, β) memoryless_channel) (f : α -> β).
    wf_bdmc W1 ∧
    mcdomain W2 = 𝕌(:bool) ∧
    mcevents W2 = POW (mccodomain W2) ∧
    BIJ f (mccodomain W1) (mccodomain W2) ⇒
    wf_bdmc W2
Proof
  rw[wf_bdmc_def] >>
  ‘mccodomain W2 = IMAGE f (mccodomain W1)’
    by (fs[BIJ_DEF, SURJ_DEF, Once EXTENSION] >> metis_tac[]) >>
  simp[IMAGE_FINITE]
QED

(* Output-bijection invariance of the Bhattacharyya parameter Z(W).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bhattacharyya_output_bij:
  ∀(W1 : (bool, α) memoryless_channel)
   (W2 : (bool, β) memoryless_channel) (f : α -> β).
    wf_bdmc W1 ∧ wf_bdmc W2 ∧
    BIJ f (mccodomain W1) (mccodomain W2) ∧
    (∀x y. y ∈ mccodomain W1 ⇒ mcchannel W2 x {f y} = mcchannel W1 x {y}) ⇒
    bhattacharyya W1 = bhattacharyya W2
Proof
  rpt strip_tac >>
  qpat_assum ‘wf_bdmc W1’ (SUBST1_TAC o MATCH_MP bhattacharyya_real_sum) >>
  qpat_assum ‘wf_bdmc W2’ (SUBST1_TAC o MATCH_MP bhattacharyya_real_sum) >>
  AP_TERM_TAC >>
  ‘FINITE (mccodomain W1)’ by fs[wf_bdmc_def] >>
  CONV_TAC SYM_CONV >>
  drule_all_then (fn th => PURE_ONCE_REWRITE_TAC[th]) REAL_SUM_IMAGE_BIJ >>
  irule REAL_SUM_IMAGE_EQ >> simp[o_DEF]
QED

(* Output-bijection invariance of the symmetric capacity I(W).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem symmetric_capacity_output_bij:
  ∀(W1 : (bool, α) memoryless_channel)
   (W2 : (bool, β) memoryless_channel) (f : α -> β).
    wf_bdmc W1 ∧ wf_bdmc W2 ∧
    BIJ f (mccodomain W1) (mccodomain W2) ∧
    (∀x y. y ∈ mccodomain W1 ⇒ mcchannel W2 x {f y} = mcchannel W1 x {y}) ⇒
    symmetric_capacity W1 = symmetric_capacity W2
Proof
  rpt strip_tac >>
  qpat_assum ‘wf_bdmc W1’ (SUBST1_TAC o MATCH_MP symmetric_capacity_real_sum) >>
  qpat_assum ‘wf_bdmc W2’ (SUBST1_TAC o MATCH_MP symmetric_capacity_real_sum) >>
  AP_TERM_TAC >>
  ‘FINITE (mccodomain W1)’ by fs[wf_bdmc_def] >>
  CONV_TAC SYM_CONV >>
  drule_all_then (fn th => PURE_ONCE_REWRITE_TAC[th]) REAL_SUM_IMAGE_BIJ >>
  irule REAL_SUM_IMAGE_EQ >> simp[o_DEF]
QED

(* Output-bijection invariance of the polymorphic BEC predicate is_bec.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem is_bec_output_bij:
  ∀(W1 : (bool, α) memoryless_channel)
   (W2 : (bool, β) memoryless_channel) (f : α -> β).
    wf_bdmc W1 ∧ wf_bdmc W2 ∧
    BIJ f (mccodomain W1) (mccodomain W2) ∧
    (∀x y. y ∈ mccodomain W1 ⇒ mcchannel W2 x {f y} = mcchannel W1 x {y}) ⇒
    (is_bec W1 ⇔ is_bec W2)
Proof
  rw[is_bec_def, EQ_IMP_THM]
  >- (‘∃y1. y1 ∈ mccodomain W1 ∧ f y1 = y’
        by (fs[BIJ_DEF, SURJ_DEF] >> metis_tac[]) >>
      gvs[])
  >- (‘f y ∈ mccodomain W2’ by fs[BIJ_DEF, INJ_DEF] >>
      first_x_assum (drule_then mp_tac) >> simp[])
QED

(* Output-bijection invariance of bec_erasure_prob.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bec_erasure_prob_output_bij:
  ∀(W1 : (bool, α) memoryless_channel)
   (W2 : (bool, β) memoryless_channel) (f : α -> β).
    wf_bdmc W1 ∧ wf_bdmc W2 ∧
    BIJ f (mccodomain W1) (mccodomain W2) ∧
    (∀x y. y ∈ mccodomain W1 ⇒ mcchannel W2 x {f y} = mcchannel W1 x {y}) ⇒
    bec_erasure_prob W1 = bec_erasure_prob W2
Proof
  rpt strip_tac >>
  qpat_assum ‘wf_bdmc W1’ (SUBST1_TAC o MATCH_MP bec_erasure_prob_real_sum) >>
  qpat_assum ‘wf_bdmc W2’ (SUBST1_TAC o MATCH_MP bec_erasure_prob_real_sum) >>
  AP_TERM_TAC >>
  ‘FINITE (mccodomain W1)’ by fs[wf_bdmc_def] >>
  CONV_TAC SYM_CONV >>
  drule_all_then (fn th => PURE_ONCE_REWRITE_TAC[th]) REAL_SUM_IMAGE_BIJ >>
  irule REAL_SUM_IMAGE_EQ >> simp[o_DEF]
QED

(* Reflexivity of bdmc_output_bij.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bdmc_output_bij_refl:
  ∀W : (bool, α) memoryless_channel.
    wf_bdmc W ⇒ bdmc_output_bij I W W
Proof
  rw[bdmc_output_bij_def, BIJ_DEF, INJ_DEF, SURJ_DEF]
QED

(* Symmetry of bdmc_output_bij via BIJ_INV.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bdmc_output_bij_sym:
  ∀(f : α -> β) W1 W2.
    bdmc_output_bij f W1 W2 ⇒ ∃g. bdmc_output_bij g W2 W1
Proof
  rw[bdmc_output_bij_def] >>
  drule BIJ_INV >> strip_tac >>
  qexists_tac ‘g’ >> simp[] >>
  rpt strip_tac >>
  ‘g y ∈ mccodomain W1’ by fs[BIJ_DEF, INJ_DEF] >>
  ‘f (g y) = y’ by (first_x_assum (drule_then mp_tac) >> simp[o_DEF]) >>
  metis_tac[]
QED

(* Transitivity of bdmc_output_bij.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bdmc_output_bij_trans:
  ∀(f : α -> β) (g : β -> γ) W1 W2 W3.
    bdmc_output_bij f W1 W2 ∧ bdmc_output_bij g W2 W3 ⇒
    bdmc_output_bij (g ∘ f) W1 W3
Proof
  rw[bdmc_output_bij_def]
  >- (irule BIJ_COMPOSE >> qexists_tac ‘mccodomain W2’ >> simp[])
  >- (‘f y ∈ mccodomain W2’ by fs[BIJ_DEF, INJ_DEF] >> simp[])
QED

(* Bundled parameter invariance under bdmc_output_bij.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem bdmc_output_bij_invariance:
  ∀(f : α -> β) W1 W2.
    bdmc_output_bij f W1 W2 ⇒
    bhattacharyya W1 = bhattacharyya W2 ∧
    symmetric_capacity W1 = symmetric_capacity W2 ∧
    (is_bec W1 ⇔ is_bec W2) ∧
    bec_erasure_prob W1 = bec_erasure_prob W2
Proof
  ntac 3 gen_tac >> strip_tac >> fs[bdmc_output_bij_def] >> rpt conj_tac
  >- (qspecl_then [‘W1’, ‘W2’, ‘f’] mp_tac bhattacharyya_output_bij >> simp[])
  >- (qspecl_then [‘W1’, ‘W2’, ‘f’] mp_tac symmetric_capacity_output_bij >> simp[])
  >- (qspecl_then [‘W1’, ‘W2’, ‘f’] mp_tac is_bec_output_bij >> simp[])
  >- (qspecl_then [‘W1’, ‘W2’, ‘f’] mp_tac bec_erasure_prob_output_bij >> simp[])
QED

(* ------------------------------------------------------------------------- *)
(* Block 7: Proposition 1 — Lower Bound (proposition_1_lower)                *)
(* ------------------------------------------------------------------------- *)

(* Pointwise binary-entropy / Bhattacharyya logarithm inequality for non-negative
   transition masses a and b.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem cap_term_entropy_bound_real[local]:
  ∀(a : real) (b : real).
    0 ≤ a ∧ 0 ≤ b ⇒
    ((1 / 2) * a + (1 / 2) * b) - cap_term a b ≤
    ((1 / 2) * a + (1 / 2) * b) *
    logr 2 (if (1 / 2) * a + (1 / 2) * b = 0 then 1
            else 1 + sqrt (a * b) / ((1 / 2) * a + (1 / 2) * b))
Proof
  rpt strip_tac >>
  Cases_on ‘a = 0’
  >- (Cases_on ‘b = 0’
      >- simp[cap_term_def, logr_1]
      >- (‘0 < b ∧ 0 < (1 / 2 : real) * b ∧ (1 / 2 : real) * b ≠ 0’
            by REAL_ASM_ARITH_TAC >>
          pop_assum strip_assume_tac >>
          ‘b / ((1 / 2 : real) * b) = 2’
            by (simp[REAL_EQ_LDIV_EQ] >> REAL_ASM_ARITH_TAC) >>
          simp[cap_term_def, realTheory.SQRT_0, logr_1]))
  >> Cases_on ‘b = 0’
  >- (‘0 < a ∧ 0 < (1 / 2 : real) * a ∧ (1 / 2 : real) * a ≠ 0’
        by REAL_ASM_ARITH_TAC >>
      pop_assum strip_assume_tac >>
      ‘a / ((1 / 2 : real) * a) = 2’
        by (simp[REAL_EQ_LDIV_EQ] >> REAL_ASM_ARITH_TAC) >>
      simp[cap_term_def, realTheory.SQRT_0, logr_1])
  >> ‘0 < a ∧ 0 < b’ by REAL_ASM_ARITH_TAC >>
  pop_assum strip_assume_tac >>
  qabbrev_tac ‘m = (1 / 2 : real) * a + (1 / 2) * b’ >>
  qabbrev_tac ‘s = a + b’ >>
  ‘0 < m ∧ 0 < s ∧ m ≠ 0 ∧ s ≠ 0 ∧ s = 2 * m ∧ a + b = s ∧ a + b = 2 * m’
    by (simp[Abbr ‘m’, Abbr ‘s’] >> REAL_ASM_ARITH_TAC) >>
  pop_assum strip_assume_tac >>
  ‘0 < sqrt a ∧ sqrt a ≠ 0 ∧ 0 < sqrt b ∧ sqrt b ≠ 0’
    by (rpt conj_tac >>
        TRY (irule realTheory.SQRT_POS_LT >> simp[]) >>
        mp_tac (Q.SPEC ‘a’ realTheory.SQRT_POS_LT) >>
        mp_tac (Q.SPEC ‘b’ realTheory.SQRT_POS_LT) >>
        REAL_ASM_ARITH_TAC) >>
  pop_assum strip_assume_tac >>
  ‘(sqrt a) pow 2 = a ∧ (sqrt b) pow 2 = b ∧ sqrt (a * b) = sqrt a * sqrt b’
    by simp[realTheory.SQRT_POW_2, realTheory.SQRT_MUL] >>
  pop_assum strip_assume_tac >>
  ‘0 ≤ sqrt (a * b) / m ∧ 0 < 1 + sqrt (a * b) / m’
    by (conj_tac
        >- (irule REAL_LE_DIV >>
            conj_tac >- (irule realTheory.SQRT_POS_LE >> irule REAL_LE_MUL >> simp[]) >>
            REAL_ASM_ARITH_TAC)
        >- (‘0 ≤ sqrt (a * b) / m’
              by (irule REAL_LE_DIV >>
                  conj_tac >- (irule realTheory.SQRT_POS_LE >> irule REAL_LE_MUL >> simp[]) >>
                  REAL_ASM_ARITH_TAC) >>
            REAL_ASM_ARITH_TAC)) >>
  pop_assum strip_assume_tac >>
  qabbrev_tac ‘w1 = a / s’ >>
  qabbrev_tac ‘u1 = (sqrt a + sqrt b) / sqrt a’ >>
  qabbrev_tac ‘u2 = (sqrt a + sqrt b) / sqrt b’ >>
  ‘0 < u1 ∧ 0 < u2’
    by (simp[Abbr ‘u1’, Abbr ‘u2’] >> REAL_ASM_ARITH_TAC) >>
  pop_assum strip_assume_tac >>
  ‘0 ≤ w1 ∧ w1 ≤ 1 ∧ 1 - w1 = b / s’
    by (simp[Abbr ‘w1’, REAL_SUB_LDISTRIB] >> REAL_ASM_ARITH_TAC) >>
  pop_assum strip_assume_tac >>
  ‘a * u1 = a + sqrt (a * b) ∧ b * u2 = sqrt (a * b) + b’
    by (simp[Abbr ‘u1’, Abbr ‘u2’, REAL_ADD_LDISTRIB] >>
        ‘sqrt a * (sqrt a * sqrt b) = a * sqrt b ∧
         sqrt b * (sqrt a * sqrt b) = b * sqrt a’
          by (qpat_assum ‘(sqrt a) pow 2 = a’ (SUBST1_TAC o SYM) >>
              qpat_assum ‘(sqrt b) pow 2 = b’ (SUBST1_TAC o SYM) >>
              PURE_REWRITE_TAC[realTheory.POW_2] >>
              conj_tac >> CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM))) >>
        qpat_x_assum ‘sqrt a * _ = _’ SUBST1_TAC >>
        qpat_x_assum ‘sqrt b * _ = _’ SUBST1_TAC >>
        simp[] >> REAL_ASM_ARITH_TAC) >>
  ‘w1 * u1 + (1 - w1) * u2 = 1 + sqrt (a * b) / m’
    by (‘s * (w1 * u1 + (1 - w1) * u2) = a * u1 + b * u2’
          by (PURE_REWRITE_TAC[REAL_ADD_LDISTRIB, REAL_MUL_ASSOC] >>
              ‘s * w1 = a ∧ s * (1 - w1) = b’
                by (conj_tac
                    >- simp[Abbr ‘w1’, REAL_DIV_LMUL]
                    >- (qpat_assum ‘1 - w1 = _’ SUBST1_TAC >> simp[REAL_DIV_LMUL])) >>
              qpat_x_assum ‘s * w1 = a’ SUBST1_TAC >>
              qpat_x_assum ‘s * (1 - w1) = b’ SUBST1_TAC >> REFL_TAC) >>
        ‘s * (1 + sqrt (a * b) / m) = a * u1 + b * u2’
          by (qpat_assum ‘a * u1 = _’ SUBST1_TAC >>
              qpat_assum ‘b * u2 = _’ SUBST1_TAC >>
              qpat_assum ‘s = 2 * m’ SUBST1_TAC >>
              PURE_REWRITE_TAC[REAL_ADD_LDISTRIB] >>
              ‘(2 * m) * (sqrt (a * b) / m) = 2 * (m * (sqrt (a * b) / m))’
                by CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM)) >>
              pop_assum SUBST1_TAC >>
              simp[REAL_DIV_LMUL] >> REAL_ASM_ARITH_TAC) >>
        ‘s * (w1 * u1 + (1 - w1) * u2) = s * (1 + sqrt (a * b) / m)’
          by REAL_ASM_ARITH_TAC >>
        (pop_assum (DISJ_CASES_TAC o REWRITE_RULE[REAL_EQ_LMUL])
 >- (pop_assum mp_tac >> ASM_REWRITE_TAC[])
 >- first_assum ACCEPT_TAC)) >>
  ‘sqrt (a * b) * sqrt (a * b) = a * b’
    by (‘0 ≤ a * b’ by (irule REAL_LE_MUL >> rpt conj_tac >> REAL_ASM_ARITH_TAC) >>
        drule realTheory.SQRT_POW_2 >>
        PURE_REWRITE_TAC[realTheory.POW_2] >> simp[]) >>
  ‘u1 * u1 = (2 / (a / m)) * (1 + sqrt (a * b) / m) ∧
   u2 * u2 = (2 / (b / m)) * (1 + sqrt (a * b) / m)’
    by (conj_tac
        >- (‘a * (u1 * u1) = a + b + 2 * sqrt (a * b)’
              by (‘a * (a * (u1 * u1)) = (a * u1) * (a * u1)’
                    by CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM)) >>
                  ‘(a * u1) * (a * u1) = a * (a + b + 2 * sqrt (a * b))’
                    by (qpat_assum ‘a * u1 = _’ SUBST1_TAC >>
                        PURE_REWRITE_TAC[REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB] >>
                        qpat_assum ‘sqrt (a * b) * sqrt (a * b) = a * b’ SUBST1_TAC >>
                        ‘sqrt (a * b) * a = a * sqrt (a * b)’
                          by CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM)) >>
                        pop_assum SUBST1_TAC >> REAL_ASM_ARITH_TAC) >>
                  ‘a * (a * (u1 * u1)) = a * (a + b + 2 * sqrt (a * b))’
                    by REAL_ASM_ARITH_TAC >>
                  (pop_assum (DISJ_CASES_TAC o REWRITE_RULE[REAL_EQ_LMUL])
 >- (pop_assum mp_tac >> ASM_REWRITE_TAC[])
 >- first_assum ACCEPT_TAC)) >>
            ‘a * ((2 / (a / m)) * (1 + sqrt (a * b) / m)) =
             a + b + 2 * sqrt (a * b)’
              by (‘a * (2 / (a / m)) = 2 * m’
                    by (simp[real_div, REAL_INV_MUL, REAL_INV_INV] >>
                        ONCE_REWRITE_TAC[REAL_ARITH
                          “(a : real) * (2 * (inv a * m)) = (a * inv a) * (2 * m)”] >>
                        simp[REAL_MUL_RINV]) >>
                  ONCE_REWRITE_TAC[REAL_MUL_ASSOC] >>
                  pop_assum SUBST1_TAC >>
                  PURE_REWRITE_TAC[REAL_ADD_LDISTRIB] >>
                  ‘(2 * m) * (sqrt (a * b) / m) = 2 * (m * (sqrt (a * b) / m))’
                    by CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM)) >>
                  pop_assum SUBST1_TAC >>
                  simp[REAL_DIV_LMUL] >> REAL_ASM_ARITH_TAC) >>
            ‘a * (u1 * u1) = a * ((2 / (a / m)) * (1 + sqrt (a * b) / m))’
              by REAL_ASM_ARITH_TAC >>
            (pop_assum (DISJ_CASES_TAC o REWRITE_RULE[REAL_EQ_LMUL])
 >- (pop_assum mp_tac >> ASM_REWRITE_TAC[])
 >- first_assum ACCEPT_TAC))
        >- (‘b * (u2 * u2) = a + b + 2 * sqrt (a * b)’
              by (‘b * (b * (u2 * u2)) = (b * u2) * (b * u2)’
                    by CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM)) >>
                  ‘(b * u2) * (b * u2) = b * (a + b + 2 * sqrt (a * b))’
                    by (qpat_assum ‘b * u2 = _’ SUBST1_TAC >>
                        PURE_REWRITE_TAC[REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB] >>
                        qpat_assum ‘sqrt (a * b) * sqrt (a * b) = a * b’ SUBST1_TAC >>
                        ‘sqrt (a * b) * b = b * sqrt (a * b)’
                          by CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM)) >>
                        pop_assum SUBST1_TAC >> REAL_ASM_ARITH_TAC) >>
                  ‘b * (b * (u2 * u2)) = b * (a + b + 2 * sqrt (a * b))’
                    by REAL_ASM_ARITH_TAC >>
                  (pop_assum (DISJ_CASES_TAC o REWRITE_RULE[REAL_EQ_LMUL])
 >- (pop_assum mp_tac >> ASM_REWRITE_TAC[])
 >- first_assum ACCEPT_TAC)) >>
            ‘b * ((2 / (b / m)) * (1 + sqrt (a * b) / m)) =
             a + b + 2 * sqrt (a * b)’
              by (‘b * (2 / (b / m)) = 2 * m’
                    by (simp[real_div, REAL_INV_MUL, REAL_INV_INV] >>
                        ONCE_REWRITE_TAC[REAL_ARITH
                          “(b : real) * (2 * (inv b * m)) = (b * inv b) * (2 * m)”] >>
                        simp[REAL_MUL_RINV]) >>
                  ONCE_REWRITE_TAC[REAL_MUL_ASSOC] >>
                  pop_assum SUBST1_TAC >>
                  PURE_REWRITE_TAC[REAL_ADD_LDISTRIB] >>
                  ‘(2 * m) * (sqrt (a * b) / m) = 2 * (m * (sqrt (a * b) / m))’
                    by CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM)) >>
                  pop_assum SUBST1_TAC >>
                  simp[REAL_DIV_LMUL] >> REAL_ASM_ARITH_TAC) >>
            ‘b * (u2 * u2) = b * ((2 / (b / m)) * (1 + sqrt (a * b) / m))’
              by REAL_ASM_ARITH_TAC >>
            (pop_assum (DISJ_CASES_TAC o REWRITE_RULE[REAL_EQ_LMUL])
 >- (pop_assum mp_tac >> ASM_REWRITE_TAC[])
 >- first_assum ACCEPT_TAC))) >>
  ‘0 < a / m ∧ 0 < b / m ∧ 0 < 2 / (a / m) ∧ 0 < 2 / (b / m)’
    by (rpt conj_tac >> TRY (irule REAL_LT_DIV >> rpt conj_tac) >> simp[] >> REAL_ASM_ARITH_TAC) >>
  ‘2 * logr 2 u1 = 1 - logr 2 (a / m) + logr 2 (1 + sqrt (a * b) / m) ∧
   2 * logr 2 u2 = 1 - logr 2 (b / m) + logr 2 (1 + sqrt (a * b) / m)’
    by (conj_tac
        >- (qspecl_then [‘2’, ‘u1’, ‘u1’] mp_tac logr_mul >>
            qspecl_then [‘2’, ‘2 / (a / m)’, ‘1 + sqrt (a * b) / m’] mp_tac logr_mul >>
            qspecl_then [‘2’, ‘2’, ‘a / m’] mp_tac logr_div >>
            simp[] >> rpt strip_tac >> REAL_ASM_ARITH_TAC)
        >- (qspecl_then [‘2’, ‘u2’, ‘u2’] mp_tac logr_mul >>
            qspecl_then [‘2’, ‘2 / (b / m)’, ‘1 + sqrt (a * b) / m’] mp_tac logr_mul >>
            qspecl_then [‘2’, ‘2’, ‘b / m’] mp_tac logr_div >>
            simp[] >> rpt strip_tac >> REAL_ASM_ARITH_TAC)) >>
  qpat_assum ‘m ≠ 0’ (fn th => REWRITE_TAC[th]) >>
  qabbrev_tac ‘L = logr 2 (1 + sqrt (a * b) / m)’ >>
  ‘w1 * logr 2 u1 + (1 - w1) * logr 2 u2 ≤ L’
    by (qspecl_then [‘u1’, ‘u2’, ‘w1’] mp_tac logr_2_concave >>
        qpat_x_assum ‘w1 * u1 + _ = _’ SUBST1_TAC >>
        qpat_assum ‘Abbrev (L = _)’
          (SUBST1_TAC o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
        disch_then irule >> simp[]) >>
  ‘(4 * m) * (w1 * logr 2 u1 + (1 - w1) * logr 2 u2) ≤ (4 * m) * L’
    by (irule REAL_LE_LMUL_IMP >> simp[] >> rpt conj_tac >> REAL_ASM_ARITH_TAC) >>
  ‘(4 * m) * (w1 * logr 2 u1 + (1 - w1) * logr 2 u2) =
   a * (2 * logr 2 u1) + b * (2 * logr 2 u2)’
    by (PURE_REWRITE_TAC[REAL_ADD_LDISTRIB] >>
        ‘(4 * m) * (w1 * logr 2 u1) = (s * w1) * (2 * logr 2 u1) ∧
         (4 * m) * ((1 - w1) * logr 2 u2) = (s * (1 - w1)) * (2 * logr 2 u2)’
          by (conj_tac >>
              qpat_assum ‘s = 2 * m’ SUBST1_TAC >>
              ONCE_REWRITE_TAC[REAL_ARITH “(4 * (m : real)) = 2 * (2 * m)”] >>
              CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM))) >>
        qpat_x_assum ‘(4 * m) * (w1 * _) = _’ SUBST1_TAC >>
        qpat_x_assum ‘(4 * m) * ((1 - w1) * _) = _’ SUBST1_TAC >>
        ‘s * w1 = a ∧ s * (1 - w1) = b’
          by (conj_tac
              >- simp[Abbr ‘w1’, REAL_DIV_LMUL, REAL_INV_MUL]
              >- (qpat_assum ‘1 - w1 = _’ SUBST1_TAC >> simp[REAL_DIV_LMUL, REAL_INV_MUL])) >>
        qpat_x_assum ‘s * w1 = a’ SUBST1_TAC >>
        qpat_x_assum ‘s * (1 - w1) = b’ SUBST1_TAC >>
        REFL_TAC) >>
  ‘cap_term a b =
   (1 / 2) * (a * logr 2 (a / m)) + (1 / 2) * (b * logr 2 (b / m))’
    by (‘(1 / 2) * a + (1 / 2) * b = m’ by simp[Abbr ‘m’] >>
        PURE_ONCE_REWRITE_TAC[cap_term_def] >>
        pop_assum SUBST1_TAC >> PURE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] >> REFL_TAC) >>
  ‘a * L + b * L = 2 * (m * L)’
    by (‘a * L + b * L = (a + b) * L’ by REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] >>
        pop_assum SUBST1_TAC >> qpat_assum ‘a + b = 2 * m’ SUBST1_TAC >>
        REWRITE_TAC[GSYM REAL_MUL_ASSOC]) >>
  qpat_x_assum ‘cap_term a b = _’ SUBST1_TAC >>
  qpat_x_assum ‘(4 * m) * _ ≤ _’ mp_tac >>
  qpat_x_assum ‘(4 * m) * _ = _’ SUBST1_TAC >>
  qpat_x_assum ‘2 * logr 2 u1 = _’ SUBST1_TAC >>
  qpat_x_assum ‘2 * logr 2 u2 = _’ SUBST1_TAC >>
  PURE_REWRITE_TAC[REAL_ADD_LDISTRIB, REAL_SUB_LDISTRIB, GSYM REAL_MUL_ASSOC] >>
  strip_tac >> REAL_ASM_ARITH_TAC
QED

(* Real-sum Jensen proof of Arıkan's Proposition 1 lower bound.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_1_lower_real[local]:
  ∀(Y : β -> bool) (pF : β -> real) (pT : β -> real).
    FINITE Y ∧
    (∀y. y ∈ Y ⇒ 0 ≤ pF y ∧ 0 ≤ pT y) ∧
    REAL_SUM_IMAGE pF Y = 1 ∧
    REAL_SUM_IMAGE pT Y = 1 ⇒
    logr 2 (2 / (1 + REAL_SUM_IMAGE (λy. sqrt (pF y * pT y)) Y)) ≤
    REAL_SUM_IMAGE (λy. cap_term (pF y) (pT y)) Y
Proof
  rpt strip_tac >>
  qabbrev_tac ‘m = λy. (1 / 2 : real) * pF y + (1 / 2) * pT y’ >>
  qabbrev_tac ‘g' = λy. if m y = 0 then (1 : real) else 1 + sqrt (pF y * pT y) / m y’ >>
  qabbrev_tac ‘z = REAL_SUM_IMAGE (λy. sqrt (pF y * pT y)) Y’ >>
  qabbrev_tac ‘c = REAL_SUM_IMAGE (λy. cap_term (pF y) (pT y)) Y’ >>
  ‘0 ≤ z’
    by (simp[Abbr ‘z’] >> irule REAL_SUM_IMAGE_POS >> simp[] >>
        rw[] >> irule realTheory.SQRT_POS_LE >> irule REAL_LE_MUL >> simp[]) >>
  ‘REAL_SUM_IMAGE m Y = 1’
    by simp[Abbr ‘m’, REAL_SUM_IMAGE_ADD, REAL_SUM_IMAGE_CMUL] >>
  ‘∀y. y ∈ Y ⇒ 0 ≤ m y ∧ m y ≤ 1’
    by (qx_gen_tac ‘y’ >> strip_tac >>
        ‘0 ≤ m y’ by (simp[Abbr ‘m’] >> first_x_assum (drule_then strip_assume_tac) >> REAL_ASM_ARITH_TAC) >>
        ‘m y ≤ REAL_SUM_IMAGE m Y’
          by (irule REAL_SUM_IMAGE_POS_MEM_LE >> simp[] >>
              rw[Abbr ‘m’] >> first_x_assum (drule_then strip_assume_tac) >> REAL_ASM_ARITH_TAC) >>
        REAL_ASM_ARITH_TAC) >>
  ‘1 - c ≤ REAL_SUM_IMAGE (λy. m y * logr 2 (g' y)) Y’
    by (‘1 - c = REAL_SUM_IMAGE (λy. m y - cap_term (pF y) (pT y)) Y’
          by simp[Abbr ‘c’, REAL_SUM_IMAGE_SUB] >>
        pop_assum SUBST1_TAC >>
        irule REAL_SUM_IMAGE_MONO >> simp[] >>
        qx_gen_tac ‘y’ >> strip_tac >>
        qpat_assum ‘∀y. y ∈ Y ⇒ 0 ≤ pF y ∧ 0 ≤ pT y’ (drule_then strip_assume_tac) >>
        qspecl_then [‘pF y’, ‘pT y’] mp_tac cap_term_entropy_bound_real >>
        simp[Abbr ‘m’, Abbr ‘g'’]) >>
  ‘REAL_SUM_IMAGE (λy. m y * g' y) Y = 1 + z’
    by (‘REAL_SUM_IMAGE (λy. m y * g' y) Y =
         REAL_SUM_IMAGE (λy. m y + sqrt (pF y * pT y)) Y’
          by (irule REAL_SUM_IMAGE_EQ >> simp[] >>
              qx_gen_tac ‘y’ >> strip_tac >>
              Cases_on ‘m y = 0’
              >- (‘pF y = 0 ∧ pT y = 0’
                    by (qpat_assum ‘∀y. y ∈ Y ⇒ 0 ≤ pF y ∧ 0 ≤ pT y’
                          (drule_then strip_assume_tac) >>
                        fs[Abbr ‘m’] >> REAL_ASM_ARITH_TAC) >>
                  simp[Abbr ‘g'’, realTheory.SQRT_0])
              >- simp[Abbr ‘g'’, REAL_ADD_LDISTRIB, REAL_DIV_LMUL]) >>
        pop_assum SUBST1_TAC >>
        simp[REAL_SUM_IMAGE_ADD, Abbr ‘z’]) >>
  ‘REAL_SUM_IMAGE (λy. m y * logr 2 (g' y)) Y ≤ logr 2 (1 + z)’
    by (qpat_assum ‘REAL_SUM_IMAGE (λy. m y * g' y) Y = 1 + z’
          (SUBST1_TAC o SYM) >>
        drule jensen_pos_concave_SIGMA >>
        disch_then (qspecl_then [‘logr 2’, ‘m’, ‘g'’] mp_tac) >>
        impl_tac
        >- (simp[pos_concave_logr] >>
            qx_gen_tac ‘y’ >> strip_tac >> strip_tac >>
            ‘m y ≠ 0’ by REAL_ASM_ARITH_TAC >>
            simp[Abbr ‘g'’] >>
            qpat_assum ‘∀y. y ∈ Y ⇒ 0 ≤ pF y ∧ 0 ≤ pT y’
              (drule_then strip_assume_tac) >>
            ‘0 ≤ sqrt (pF y * pT y) / m y’
              by (irule REAL_LE_DIV >>
                  conj_tac
                  >- (irule realTheory.SQRT_POS_LE >> irule REAL_LE_MUL >> simp[])
                  >- REAL_ASM_ARITH_TAC) >>
            REAL_ASM_ARITH_TAC) >>
        simp[]) >>
  ‘0 < 1 + z’ by REAL_ASM_ARITH_TAC >>
  ‘logr 2 (2 / (1 + z)) = 1 - logr 2 (1 + z)’
    by simp[logr_div, logr_2_2] >>
  REAL_ASM_ARITH_TAC
QED

(* Proposition 1, Lower Bound (Erdal Arıkan, 2009, Section I-A Eq. (1) &
   Appendix A): I(W) ≥ log_2 (2 / (1 + Z(W))) for every B-DMC W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_1_lower:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒ logr 2 (2 / (1 + bhattacharyya W)) ≤ symmetric_capacity W
Proof
  rpt strip_tac >>
  drule bhattacharyya_real_sum >> strip_tac >>
  drule symmetric_capacity_real_sum >> strip_tac >>
  drule wf_bdmc_real_pmf_safe >> strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  qabbrev_tac ‘z = REAL_SUM_IMAGE
                     (λy. sqrt (real (mcchannel W F {y}) *
                                real (mcchannel W T {y})))
                     (mccodomain W)’ >>
  ‘0 ≤ z ∧ 1 + z ≠ 0’
    by (‘0 ≤ z’
          by (simp[Abbr ‘z’] >> irule REAL_SUM_IMAGE_POS >> simp[] >>
              rw[] >> irule realTheory.SQRT_POS_LE >> irule REAL_LE_MUL >> simp[]) >>
        simp[] >> REAL_ASM_ARITH_TAC) >>
  simp[extreal_of_num_def, extreal_add_eq, extreal_div_eq, extreal_logr_def,
       extreal_le_eq, Abbr ‘z’] >>
  qspecl_then [‘mccodomain W’, ‘λy. real (mcchannel W F {y})’,
               ‘λy. real (mcchannel W T {y})’]
    mp_tac proposition_1_lower_real >>
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Block 8: Proposition 1 — Upper Bound (proposition_1_upper) & proposition_1*)
(* ------------------------------------------------------------------------- *)

(* Variational distance d(W) = (1/2) ∑_y |W(y|0) - W(y|1)| of a B-DMC
   (Erdal Arıkan, 2009, Appendix A, p. 20).

   Written by Gemini (Google DeepMind AI agent) *)
Definition variational_distance_def:
  variational_distance (W : (bool, β) memoryless_channel) : extreal =
    (1 / 2) * ∑ (λy. abs (mcchannel W F {y} - mcchannel W T {y})) (mccodomain W)
End

(* Convexity bound (1 + t) * logr 2 (1 + t) ≤ 2 * t on [0, 1] derived directly
   from concavity of logr 2 without derivatives or limits.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem one_plus_t_logr_le_2t[local]:
  ∀t : real. 0 ≤ t ∧ t ≤ 1 ⇒ (1 + t) * logr 2 (1 + t) ≤ 2 * t
Proof
  rpt strip_tac >>
  ‘0 < 1 + t ∧ 1 + t ≠ 0 ∧ 0 < (1 + t) / 2’ by REAL_ASM_ARITH_TAC >>
  pop_assum strip_assume_tac >>
  qabbrev_tac ‘w = (1 - t) / (1 + t)’ >>
  ‘0 ≤ w ∧ w ≤ 1 ∧ 1 - w = (2 * t) / (1 + t)’
    by (simp[Abbr ‘w’, REAL_SUB_LDISTRIB] >> REAL_ASM_ARITH_TAC) >>
  pop_assum strip_assume_tac >>
  ‘w * (1 + t) + (1 - w) * ((1 + t) / 2) = 1’
    by (‘w * (1 + t) = 1 - t’ by simp[Abbr ‘w’, REAL_DIV_RMUL] >>
        ‘(1 - w) * ((1 + t) / 2) = t’
          by (simp[real_div] >>
              ONCE_REWRITE_TAC[REAL_ARITH
                “((2 * (t : real)) * inv (1 + t)) * ((1 + t) * inv 2) =
                 t * ((1 + t) * inv (1 + t)) * (2 * inv 2)”] >>
              simp[REAL_MUL_RINV]) >>
        REAL_ASM_ARITH_TAC) >>
  qspecl_then [‘1 + t’, ‘(1 + t) / 2’, ‘w’] mp_tac logr_2_concave >>
  simp[logr_1, logr_div] >> strip_tac >>
  ‘(1 + t) * (w * logr 2 (1 + t) + (1 - w) * (logr 2 (1 + t) - 1)) ≤ (1 + t) * 0’
    by (irule REAL_LE_LMUL_IMP >> simp[] >> rpt conj_tac >> REAL_ASM_ARITH_TAC) >>
  ‘(1 + t) * (w * logr 2 (1 + t) + (1 - w) * (logr 2 (1 + t) - 1)) =
   (1 + t) * logr 2 (1 + t) - 2 * t’
    by (PURE_REWRITE_TAC[REAL_ADD_LDISTRIB, REAL_MUL_ASSOC] >>
        ‘(1 + t) * w = 1 - t ∧ (1 + t) * (1 - w) = 2 * t’
          by (conj_tac >- simp[Abbr ‘w’] >>
              qpat_assum ‘1 - w = _’ SUBST1_TAC >> simp[]) >>
        qpat_x_assum ‘(1 + t) * w = _’ SUBST1_TAC >>
        qpat_x_assum ‘(1 + t) * (1 - w) = _’ SUBST1_TAC >>
        simp[REAL_SUB_RDISTRIB, REAL_SUB_LDISTRIB, REAL_ADD_RDISTRIB] >>
        REAL_ASM_ARITH_TAC) >>
  qpat_x_assum ‘_ ≤ (1 + t) * 0’ mp_tac >>
  pop_assum SUBST1_TAC >>
  PURE_REWRITE_TAC[REAL_MUL_RZERO] >> REAL_ASM_ARITH_TAC
QED

(* Ordered pointwise Lemma 2 bound: cap_term a b ≤ (1/2) * (b - a) for 0 ≤ a ≤ b.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem cap_term_le_half_diff_ordered[local]:
  ∀(a : real) (b : real).
    0 ≤ a ∧ a ≤ b ⇒ cap_term a b ≤ (1 / 2) * (b - a)
Proof
  rpt strip_tac >>
  Cases_on ‘a = 0’
  >- (Cases_on ‘b = 0’
      >- simp[cap_term_def]
      >- (‘0 < b ∧ 0 < (1 / 2 : real) * b ∧ (1 / 2 : real) * b ≠ 0’
            by REAL_ASM_ARITH_TAC >>
          ‘b / ((1 / 2 : real) * b) = 2’
            by (simp[REAL_EQ_LDIV_EQ] >> REAL_ASM_ARITH_TAC) >>
          simp[cap_term_def, logr_2_2] >> REAL_ASM_ARITH_TAC)) >>
  ‘0 < a ∧ 0 < b ∧ b ≠ 0’ by REAL_ASM_ARITH_TAC >>
  qabbrev_tac ‘m = (1 / 2 : real) * a + (1 / 2 : real) * b’ >>
  qabbrev_tac ‘s = a + b’ >>
  ‘0 < m ∧ 0 < s ∧ m ≠ 0 ∧ s ≠ 0 ∧ s = 2 * m ∧ a + b = s ∧ a + b = 2 * m’
    by (simp[Abbr ‘m’, Abbr ‘s’] >> REAL_ASM_ARITH_TAC) >>
  qabbrev_tac ‘t = (b - a) / s’ >>
  ‘0 ≤ t ∧ t < 1’ by (simp[Abbr ‘t’] >> REAL_ASM_ARITH_TAC) >>
  ‘t ≤ 1 ∧ 0 < 1 - t ∧ 1 - t ≤ 1’ by REAL_ASM_ARITH_TAC >>
  ‘a = m * (1 - t) ∧ b = m * (1 + t) ∧ (1 / 2) * (b - a) = m * t’
    by (‘2 * (m * t) = b - a’
          by (‘s * t = b - a’ by simp[Abbr ‘t’] >>
              pop_assum mp_tac >> qpat_assum ‘s = 2 * m’ SUBST1_TAC >>
              simp[]) >>
        simp[REAL_SUB_LDISTRIB, REAL_ADD_LDISTRIB] >>
        REAL_ASM_ARITH_TAC) >>
  ‘a / m = 1 - t ∧ b / m = 1 + t’
    by (DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ] >>
        qpat_assum ‘0 < m’ (fn th => REWRITE_TAC[th]) >>
        qpat_assum ‘a = m * (1 - t)’ SUBST1_TAC >>
        qpat_assum ‘b = m * (1 + t)’ SUBST1_TAC >>
        conj_tac >> CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM))) >>
  ‘cap_term a b =
   ((1 / 2) * m) * ((1 - t) * logr 2 (1 - t) + (1 + t) * logr 2 (1 + t))’
    by (‘(1 / 2) * a + (1 / 2) * b = m’
          by qpat_assum ‘Abbrev (m = _)’
               (ACCEPT_TAC o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
        PURE_ONCE_REWRITE_TAC[cap_term_def] >>
        pop_assum SUBST1_TAC >>
        qpat_x_assum ‘a / m = 1 - t’ SUBST1_TAC >>
        qpat_x_assum ‘b / m = 1 + t’ SUBST1_TAC >>
        qpat_x_assum ‘a = m * (1 - t)’ SUBST1_TAC >>
        qpat_x_assum ‘b = m * (1 + t)’ SUBST1_TAC >>
        REWRITE_TAC[REAL_ADD_LDISTRIB, REAL_MUL_ASSOC]) >>
  ‘logr 2 (1 - t) ≤ 0’
    by (qspecl_then [‘1 - t’, ‘1’, ‘2’] mp_tac LOGR_MONO_LE_IMP >>
        simp[logr_1]) >>
  ‘(1 - t) * logr 2 (1 - t) ≤ 0’
    by (‘0 ≤ (1 - t) * -(logr 2 (1 - t))’
          by (irule REAL_LE_MUL >> rpt conj_tac >> REAL_ASM_ARITH_TAC) >>
        pop_assum mp_tac >> PURE_REWRITE_TAC[REAL_MUL_RNEG] >> REAL_ASM_ARITH_TAC) >>
  ‘(1 + t) * logr 2 (1 + t) ≤ 2 * t’
    by (irule one_plus_t_logr_le_2t >> simp[]) >>
  ‘0 ≤ (1 / 2) * m’ by REAL_ASM_ARITH_TAC >>
  ‘((1 / 2) * m) * ((1 - t) * logr 2 (1 - t) + (1 + t) * logr 2 (1 + t)) ≤
   ((1 / 2) * m) * (2 * t)’
    by (irule REAL_LE_LMUL_IMP >> rpt conj_tac >> REAL_ASM_ARITH_TAC) >>
  ‘((1 / 2) * m) * (2 * t) = m * t’ by simp[] >>
  REAL_ASM_ARITH_TAC
QED

(* Symmetric pointwise Lemma 2 bound: cap_term a b ≤ (1/2) * abs (a - b).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem cap_term_le_half_abs_diff[local]:
  ∀(a : real) (b : real).
    0 ≤ a ∧ 0 ≤ b ⇒ cap_term a b ≤ (1 / 2) * abs (a - b)
Proof
  rpt strip_tac >>
  qspecl_then [‘a’, ‘b’] strip_assume_tac REAL_LE_TOTAL
  >- (‘abs (a - b) = b - a’ by (simp[abs] >> REAL_ASM_ARITH_TAC) >>
      pop_assum SUBST1_TAC >> irule cap_term_le_half_diff_ordered >> simp[])
  >- (‘abs (a - b) = a - b’ by (simp[abs] >> REAL_ASM_ARITH_TAC) >>
      ‘cap_term a b = cap_term b a’
        by (‘(1 / 2 : real) * a + (1 / 2) * b = (1 / 2) * b + (1 / 2) * a’
              by REAL_ARITH_TAC >>
            PURE_REWRITE_TAC[cap_term_def] >> pop_assum SUBST1_TAC >>
            REAL_ARITH_TAC) >>
      qpat_x_assum ‘abs _ = _’ SUBST1_TAC >>
      pop_assum SUBST1_TAC >> irule cap_term_le_half_diff_ordered >> simp[])
QED

(* Arıkan Lemma 2 (Appendix A, p. 20): I(W) ≤ d(W) for every B-DMC W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem lemma_2_variational_lower:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒ symmetric_capacity W ≤ variational_distance W
Proof
  rpt strip_tac >>
  drule symmetric_capacity_real_sum >> strip_tac >>
  drule wf_bdmc_real_pmf_safe >> strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  ‘variational_distance W =
   Normal ((1 / 2) *
           REAL_SUM_IMAGE
             (λy. abs (real (mcchannel W F {y}) - real (mcchannel W T {y})))
             (mccodomain W))’
    by (simp[variational_distance_def] >>
        ‘∑ (λy. abs (mcchannel W F {y} - mcchannel W T {y})) (mccodomain W) =
         Normal (REAL_SUM_IMAGE
                   (λy. abs (real (mcchannel W F {y}) -
                             real (mcchannel W T {y})))
                   (mccodomain W))’
          by (simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
              irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
              qx_gen_tac ‘y’ >> strip_tac >>
              qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
              qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
              simp[] >> rpt strip_tac >>
              simp[extreal_sub_eq, extreal_abs_def]) >>
        pop_assum SUBST1_TAC >>
        simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq]) >>
  simp[extreal_le_eq] >>
  ‘2 *
   REAL_SUM_IMAGE
     (λy. cap_term (real (mcchannel W F {y})) (real (mcchannel W T {y})))
     (mccodomain W) =
   REAL_SUM_IMAGE
     (λy. 2 * cap_term (real (mcchannel W F {y})) (real (mcchannel W T {y})))
     (mccodomain W)’
    by simp[REAL_SUM_IMAGE_CMUL] >>
  pop_assum SUBST1_TAC >>
  irule REAL_SUM_IMAGE_MONO >> simp[] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  qspecl_then [‘real (mcchannel W F {y})’, ‘real (mcchannel W T {y})’]
    mp_tac cap_term_le_half_abs_diff >>
  simp[] >> REAL_ASM_ARITH_TAC
QED

(* Finite Cauchy-Schwarz inequality for REAL_SUM_IMAGE via Lagrange's identity.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem REAL_SUM_IMAGE_CAUCHY_SCHWARZ:
  ∀s (f : α -> real) (g : α -> real).
    FINITE s ⇒
    (REAL_SUM_IMAGE (λx. f x * g x) s) pow 2 ≤
    REAL_SUM_IMAGE (λx. (f x) pow 2) s * REAL_SUM_IMAGE (λx. (g x) pow 2) s
Proof
  rpt strip_tac >>
  qabbrev_tac ‘A = REAL_SUM_IMAGE (λx. (f x) pow 2) s’ >>
  qabbrev_tac ‘B = REAL_SUM_IMAGE (λx. (g x) pow 2) s’ >>
  qabbrev_tac ‘C = REAL_SUM_IMAGE (λx. f x * g x) s’ >>
  ‘FINITE (s × s)’ by simp[FINITE_CROSS] >>
  ‘0 ≤ REAL_SUM_IMAGE
         (λz. (f (FST z) * g (SND z) - f (SND z) * g (FST z)) pow 2)
         (s × s)’
    by (irule REAL_SUM_IMAGE_POS >> simp[REAL_LE_POW2]) >>
  ‘REAL_SUM_IMAGE
     (λz. (f (FST z) * g (SND z) - f (SND z) * g (FST z)) pow 2)
     (s × s) =
   REAL_SUM_IMAGE
     (λz. ((f (FST z)) pow 2 * (g (SND z)) pow 2 +
           (f (SND z)) pow 2 * (g (FST z)) pow 2) -
          2 * ((f (FST z) * g (FST z)) * (f (SND z) * g (SND z))))
     (s × s)’
    by (irule REAL_SUM_IMAGE_EQ >> simp[] >> qx_gen_tac ‘z’ >> strip_tac >>
        PURE_REWRITE_TAC[SUB_POW_2, POW_MUL] >>
        ‘(f (FST z) * g (SND z)) * (f (SND z) * g (FST z)) =
         (f (FST z) * g (FST z)) * (f (SND z) * g (SND z))’
          by CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM)) >>
        pop_assum SUBST1_TAC >> REAL_ARITH_TAC) >>
  ‘REAL_SUM_IMAGE (λz. (f (FST z)) pow 2 * (g (SND z)) pow 2) (s × s) = A * B’
    by (qspecl_then [‘s’, ‘s’, ‘λi j. (f i) pow 2 * (g j) pow 2’]
          mp_tac REAL_SUM_IMAGE_REAL_SUM_IMAGE >>
        simp[] >> disch_then (SUBST1_TAC o SYM) >>
        simp[REAL_SUM_IMAGE_CMUL, Abbr ‘B’] >>
        ‘REAL_SUM_IMAGE (λx. (f x) pow 2 * REAL_SUM_IMAGE (λx. (g x) pow 2) s) s =
         REAL_SUM_IMAGE (λx. REAL_SUM_IMAGE (λx. (g x) pow 2) s * (f x) pow 2) s’
          by (irule REAL_SUM_IMAGE_EQ >> rw[] >> REAL_ARITH_TAC) >>
        pop_assum SUBST1_TAC >>
        simp[REAL_SUM_IMAGE_CMUL, Abbr ‘A’] >> REAL_ARITH_TAC) >>
  ‘REAL_SUM_IMAGE (λz. (f (SND z)) pow 2 * (g (FST z)) pow 2) (s × s) = A * B’
    by (qspecl_then [‘s’, ‘s’, ‘λi j. (f j) pow 2 * (g i) pow 2’]
          mp_tac REAL_SUM_IMAGE_REAL_SUM_IMAGE >>
        simp[] >> disch_then (SUBST1_TAC o SYM) >>
        ‘∀x. REAL_SUM_IMAGE (λy. (f y) pow 2 * (g x) pow 2) s =
             (g x) pow 2 * A’
          by (gen_tac >>
              ‘REAL_SUM_IMAGE (λy. (f y) pow 2 * (g x) pow 2) s =
               REAL_SUM_IMAGE (λy. (g x) pow 2 * (f y) pow 2) s’
                by (irule REAL_SUM_IMAGE_EQ >> rw[] >> REAL_ARITH_TAC) >>
              pop_assum SUBST1_TAC >>
              simp[REAL_SUM_IMAGE_CMUL, Abbr ‘A’]) >>
        simp[] >>
        ‘REAL_SUM_IMAGE (λx. (g x) pow 2 * A) s =
         REAL_SUM_IMAGE (λx. A * (g x) pow 2) s’
          by (irule REAL_SUM_IMAGE_EQ >> rw[] >> REAL_ARITH_TAC) >>
        pop_assum SUBST1_TAC >>
        simp[REAL_SUM_IMAGE_CMUL, Abbr ‘B’]) >>
  ‘REAL_SUM_IMAGE
     (λz. (f (FST z) * g (FST z)) * (f (SND z) * g (SND z)))
     (s × s) = C pow 2’
    by (simp[Abbr ‘C’, REAL_SUM_IMAGE_POW] >>
        irule REAL_SUM_IMAGE_EQ >> simp[FORALL_PROD]) >>
  qpat_x_assum ‘0 ≤ _’ mp_tac >>
  simp[REAL_SUM_IMAGE_SUB, REAL_SUM_IMAGE_ADD, REAL_SUM_IMAGE_CMUL] >>
  REAL_ARITH_TAC
QED

(* Real-sum Cauchy-Schwarz proof of Arıkan Lemma 3: d(W) ≤ sqrt (1 - Z(W)^2).

   Written by Gemini (Google DeepMind AI agent) *)
Theorem lemma_3_variational_upper_real[local]:
  ∀(Y : β -> bool) (pF : β -> real) (pT : β -> real).
    FINITE Y ∧
    (∀y. y ∈ Y ⇒ 0 ≤ pF y ∧ 0 ≤ pT y) ∧
    REAL_SUM_IMAGE pF Y = 1 ∧
    REAL_SUM_IMAGE pT Y = 1 ⇒
    (1 / 2) * REAL_SUM_IMAGE (λy. abs (pF y - pT y)) Y ≤
    sqrt (1 - (REAL_SUM_IMAGE (λy. sqrt (pF y * pT y)) Y) pow 2)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘S_diff = REAL_SUM_IMAGE (λy. abs (pF y - pT y)) Y’ >>
  qabbrev_tac ‘z = REAL_SUM_IMAGE (λy. sqrt (pF y * pT y)) Y’ >>
  ‘0 ≤ S_diff’
    by (simp[Abbr ‘S_diff’] >> irule REAL_SUM_IMAGE_POS >> simp[ABS_POS]) >>
  ‘S_diff =
   REAL_SUM_IMAGE
     (λy. abs (sqrt (pF y) - sqrt (pT y)) * (sqrt (pF y) + sqrt (pT y))) Y’
    by (simp[Abbr ‘S_diff’] >> irule REAL_SUM_IMAGE_EQ >> simp[] >>
        qx_gen_tac ‘y’ >> strip_tac >>
        first_x_assum (drule_then strip_assume_tac) >>
        ‘pF y - pT y = (sqrt (pF y) - sqrt (pT y)) * (sqrt (pF y) + sqrt (pT y))’
          by (‘(sqrt (pF y)) pow 2 = pF y ∧ (sqrt (pT y)) pow 2 = pT y’
                by simp[realTheory.SQRT_POW_2] >>
              PURE_REWRITE_TAC[REAL_SUB_RDISTRIB, REAL_ADD_LDISTRIB] >>
              qpat_x_assum ‘(sqrt (pF y)) pow 2 = _’ mp_tac >>
              qpat_x_assum ‘(sqrt (pT y)) pow 2 = _’ mp_tac >>
              PURE_REWRITE_TAC[realTheory.POW_2] >>
              ‘sqrt (pT y) * sqrt (pF y) = sqrt (pF y) * sqrt (pT y)’
                by REAL_ARITH_TAC >>
              pop_assum SUBST1_TAC >>
              REAL_ARITH_TAC) >>
        pop_assum SUBST1_TAC >>
        PURE_REWRITE_TAC[ABS_MUL] >> AP_TERM_TAC >>
        PURE_REWRITE_TAC[ABS_REFL] >>
        irule REAL_LE_ADD >> simp[realTheory.SQRT_POS_LE]) >>
  ‘S_diff pow 2 ≤
   REAL_SUM_IMAGE (λy. (abs (sqrt (pF y) - sqrt (pT y))) pow 2) Y *
   REAL_SUM_IMAGE (λy. (sqrt (pF y) + sqrt (pT y)) pow 2) Y’
    by (qpat_x_assum ‘S_diff = _’ SUBST1_TAC >>
        ho_match_mp_tac REAL_SUM_IMAGE_CAUCHY_SCHWARZ >> simp[]) >>
  ‘REAL_SUM_IMAGE (λy. (abs (sqrt (pF y) - sqrt (pT y))) pow 2) Y = 2 * (1 - z)’
    by (‘REAL_SUM_IMAGE (λy. (abs (sqrt (pF y) - sqrt (pT y))) pow 2) Y =
         REAL_SUM_IMAGE (λy. (pF y + pT y) - 2 * sqrt (pF y * pT y)) Y’
          by (irule REAL_SUM_IMAGE_EQ >> simp[REAL_POW2_ABS] >>
              qx_gen_tac ‘y’ >> strip_tac >>
              first_x_assum (drule_then strip_assume_tac) >>
              simp[SUB_POW_2, realTheory.SQRT_POW_2, realTheory.SQRT_MUL]) >>
        pop_assum SUBST1_TAC >>
        simp[REAL_SUM_IMAGE_SUB, REAL_SUM_IMAGE_ADD, REAL_SUM_IMAGE_CMUL,
             Abbr ‘z’] >>
        REAL_ARITH_TAC) >>
  ‘REAL_SUM_IMAGE (λy. (sqrt (pF y) + sqrt (pT y)) pow 2) Y = 2 * (1 + z)’
    by (‘REAL_SUM_IMAGE (λy. (sqrt (pF y) + sqrt (pT y)) pow 2) Y =
         REAL_SUM_IMAGE (λy. (pF y + pT y) + 2 * sqrt (pF y * pT y)) Y’
          by (irule REAL_SUM_IMAGE_EQ >> simp[] >>
              qx_gen_tac ‘y’ >> strip_tac >>
              first_x_assum (drule_then strip_assume_tac) >>
              simp[ADD_POW_2, realTheory.SQRT_POW_2, realTheory.SQRT_MUL]) >>
        pop_assum SUBST1_TAC >>
        simp[REAL_SUM_IMAGE_ADD, REAL_SUM_IMAGE_CMUL, Abbr ‘z’] >>
        REAL_ARITH_TAC) >>
  ‘((1 / 2) * S_diff) pow 2 ≤ 1 - z pow 2’
    by (‘((1 / 2) * S_diff) pow 2 = (1 / 4) * (S_diff pow 2)’
          by (PURE_ONCE_REWRITE_TAC[POW_MUL] >> simp[]) >>
        ‘(2 * (1 - z)) * (2 * (1 + z)) = 4 * (1 - z pow 2)’
          by (PURE_REWRITE_TAC[realTheory.POW_2, REAL_SUB_LDISTRIB,
                               REAL_SUB_RDISTRIB, REAL_ADD_LDISTRIB,
                               REAL_ADD_RDISTRIB] >>
              REAL_ARITH_TAC) >>
        qpat_x_assum ‘S_diff pow 2 ≤ _’ mp_tac >>
        qpat_x_assum ‘_ = 2 * (1 - z)’ SUBST1_TAC >>
        qpat_x_assum ‘_ = 2 * (1 + z)’ SUBST1_TAC >>
        qpat_x_assum ‘(2 * (1 - z)) * _ = _’ SUBST1_TAC >>
        qpat_x_assum ‘((1 / 2) * S_diff) pow 2 = _’ SUBST1_TAC >>
        REAL_ARITH_TAC) >>
  ‘0 ≤ (1 / 2) * S_diff ∧ 0 ≤ ((1 / 2) * S_diff) pow 2’
    by (simp[REAL_LE_POW2] >> qpat_assum ‘0 ≤ S_diff’ mp_tac >> REAL_ARITH_TAC) >>
  ‘(1 / 2) * S_diff = sqrt (((1 / 2) * S_diff) pow 2)’
    by (CONV_TAC SYM_CONV >> irule (GEN_ALL realTheory.POW_2_SQRT) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule realTheory.SQRT_MONO_LE >> simp[]
QED

(* Arıkan Lemma 3 (Appendix A, p. 20): d(W) ≤ sqrt (1 - Z(W)^2) for every B-DMC W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem lemma_3_variational_upper:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒ variational_distance W ≤ sqrt (1 - (bhattacharyya W) pow 2)
Proof
  rpt strip_tac >>
  drule bhattacharyya_real_sum >> strip_tac >>
  drule wf_bdmc_real_pmf_safe >> strip_tac >>
  ‘FINITE (mccodomain W)’ by fs[wf_bdmc_def] >>
  ‘variational_distance W =
   Normal ((1 / 2) *
           REAL_SUM_IMAGE
             (λy. abs (real (mcchannel W F {y}) - real (mcchannel W T {y})))
             (mccodomain W))’
    by (simp[variational_distance_def] >>
        ‘∑ (λy. abs (mcchannel W F {y} - mcchannel W T {y})) (mccodomain W) =
         Normal (REAL_SUM_IMAGE
                   (λy. abs (real (mcchannel W F {y}) -
                             real (mcchannel W T {y})))
                   (mccodomain W))’
          by (simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
              irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
              qx_gen_tac ‘y’ >> strip_tac >>
              qspecl_then [‘W’, ‘T’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
              qspecl_then [‘W’, ‘F’, ‘y’] mp_tac wf_bdmc_mcchannel_singleton_normal >>
              simp[] >> rpt strip_tac >>
              simp[extreal_sub_eq, extreal_abs_def]) >>
        pop_assum SUBST1_TAC >>
        simp[extreal_of_num_def, extreal_div_eq, extreal_mul_eq]) >>
  simp[extreal_of_num_def, extreal_pow_def, extreal_sub_eq, extreal_sqrt_def,
       extreal_le_eq] >>
  qspecl_then [‘mccodomain W’, ‘λy. real (mcchannel W F {y})’,
               ‘λy. real (mcchannel W T {y})’]
    mp_tac lemma_3_variational_upper_real >>
  simp[]
QED

(* Proposition 1, Upper Bound (Erdal Arıkan, 2009, Section I-A Eq. (2) &
   Appendix A): I(W) ≤ sqrt (1 - Z(W)^2) for every B-DMC W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_1_upper:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒ symmetric_capacity W ≤ sqrt (1 - (bhattacharyya W) pow 2)
Proof
  rpt strip_tac >>
  irule le_trans >>
  qexists_tac ‘variational_distance W’ >>
  simp[lemma_2_variational_lower, lemma_3_variational_upper]
QED

(* Proposition 1 (Erdal Arıkan, 2009, Section I-A Eqs. (1)-(2)):
   Both lower and upper bounds relating symmetric capacity I(W) and
   Bhattacharyya parameter Z(W) for any B-DMC W.

   Written by Gemini (Google DeepMind AI agent) *)
Theorem proposition_1:
  ∀W : (bool, β) memoryless_channel.
    wf_bdmc W ⇒
    logr 2 (2 / (1 + bhattacharyya W)) ≤ symmetric_capacity W ∧
    symmetric_capacity W ≤ sqrt (1 - (bhattacharyya W) pow 2)
Proof
  rw[proposition_1_lower, proposition_1_upper]
QED
