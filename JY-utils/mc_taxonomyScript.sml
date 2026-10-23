(* Scratch work of Jared Yeager, for use in work with Eric Hall and Michael Norrish *)

open HolKernel Parse boolLib bossLib;
open dep_rewrite;
open pairTheory;
open arithmeticTheory;
open pred_setTheory;
open listTheory;
open realTheory;
open realLib;
open extrealTheory;
open sigma_algebraTheory;
open borelTheory;
open measureTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;

(* open ex_machina; *)
open trivialTheory;
open memoryless_channelTheory;

val _ = new_theory "mc_taxonomy";

val _ = hide "W";

(* -------------------------------------------------------------------------- *)
(* Memoryless channel probability                                             *)
(*                                                                            *)
(* Takes a channel c, input a, and output b, and returns the probability      *)
(* of returning output b given input a.                                       *)
(* -------------------------------------------------------------------------- *)
Definition mcp_def:
  mcp c a b = mcchannel c a {b}
End

(* -------------------------------------------------------------------------- *)
(* Checks if a memoryless channel is a binary memoryless channel, i.e. it     *)
(* has two possible inputs                                                    *)
(* -------------------------------------------------------------------------- *)
Definition binary_mc_def:
    binary_mc c ⇔ CARD (mcdomain c) = 2
End

(* -------------------------------------------------------------------------- *)
(* Checks if a memoryless channel is a discrete memoryless channel.           *)
(*                                                                            *)
(* It should have a finite set of inputs and a finite set of outputs.         *)
(*                                                                            *)
(* We want to be able to specify the probability of each individual output    *)
(* given each individual input, so we reqruire that each singleton is an      *)
(* event.                                                                     *)
(* -------------------------------------------------------------------------- *)
Definition discrete_mc_def:
  discrete_mc c ⇔ FINITE (mcdomain c) ∧
                  FINITE (mccodomain c) ∧
                  ∀y. y ∈ mccodomain c ⇒ {y} ∈ mcevents c
End

Theorem discrete_mc_POW_sigma_algebra:
    ∀c. discrete_mc c ⇒ mcsigma c = (mccodomain c,POW (mccodomain c))
Proof
    rw[discrete_mc_def] >>
    qspec_then ‘c’ assume_tac memoryless_channel_wf_sigma_algebra_property >>
    gs[mcsigma_alt] >> irule SUBSET_ANTISYM >> conj_tac
    >- (simp[SUBSET_DEF] >> simp[IN_POW] >>
        dxrule SIGMA_ALGEBRA_SUBSET_CLASS >> simp[subset_class_def]) >>
    simp[SUBSET_DEF] >> simp[IN_POW] >>
    qx_gen_tac ‘s’ >> strip_tac >>
    dxrule SIGMA_ALGEBRA_COUNTABLE_UNION >> simp[subsets_def] >>
    disch_then $ qspec_then ‘IMAGE (λx. {x}) s’ mp_tac >>
    ‘BIGUNION (IMAGE (λx. {x}) s) = s’ by simp[Once EXTENSION,PULL_EXISTS] >>
    pop_assum SUBST1_TAC >> disch_then irule >>
    simp[SUBSET_DEF,PULL_EXISTS] >> reverse $ conj_tac
    >- (rw[] >> first_x_assum irule >> gs[SUBSET_DEF]) >>
    irule cardinalTheory.COUNTABLE_IMAGE >> irule finite_countable >>
    simp[SUBSET_FINITE,SF SFY_ss]
QED

(*** Boolean reskins ***)

Datatype:
    BIT = ZERO | ONE
End

Definition BIT_XOR_DEF:
    BIT_XOR ZERO ZERO = ZERO ∧
    BIT_XOR ZERO ONE = ONE ∧
    BIT_XOR ONE ZERO = ONE ∧
    BIT_XOR ONE ONE = ZERO
End

Definition BIT_NOT_DEF:
    BIT_NOT ZERO = ONE ∧
    BIT_NOT ONE = ZERO
End

Datatype:
    POLE = POS | NEG
End

(*** Meta Lifting Definition ***)

(* prove above wf under some conditions *)
Definition meta_lift_channel_rep_def:
    meta_lift_channel_rep (upa:α->γ) (downa:γ->α) (upb:β->δ) (downb:δ->β) W = (
        IMAGE upa (mcdomain W),
        (IMAGE upb (mccodomain W), IMAGE (IMAGE upb) (mcevents W)),
        (λal bls. mcchannel W (downa al) (IMAGE downb bls)))
End

Definition meta_lift_channel_def:
    meta_lift_channel (upa:α->γ) (downa:γ->α) (upb:β->δ) (downb:δ->β) W =
        memoryless_channel_ABS (meta_lift_channel_rep upa downa upb downb W)
End

Definition list_lift_channel_def:
    list_lift_channel = meta_lift_channel (λa:α. [a]) HD (λb:β. [b]) HD
End

Definition list_lift_range_channel_def:
    list_lift_range_channel = meta_lift_channel I I (λb:β. [b]) HD
End

Definition INL_lift_channel_def:
    INL_lift_channel = meta_lift_channel I I INL OUTL
End

Definition INR_lift_channel_def:
    INR_lift_channel = meta_lift_channel I I INR OUTR
End

(*** Compound Channels ***)

(* Prove wf *)
Definition basic_fusion_channel_rep_def:
    basic_fusion_channel_rep splitn W0 W1 = (
        general_cross $++ (mcdomain W0) (mcdomain W1),
        general_sigma $++ (mcsigma W0) (mcsigma W1),
        (λa01.
            let
                a0 = TAKE splitn a01;
                a1 = DROP splitn a01
            in
                general_prod_measure $++
                (mccodomain W0, mcevents W0, mcchannel W0 (MAP2 BIT_XOR a0 a1))
                (mccodomain W1, mcevents W1, mcchannel W1 a1)))
End

(*
Definition basic_fusion_channel_rep_def:
    basic_fusion_channel_rep W0 W1 = (
        general_cross $++ (mcdomain W0) (mcdomain W1),
        general_sigma $++ (mcsigma W0) (mcsigma W1),
        (λa01.
            let
                a0 = TAKE ((LENGTH a01) DIV 2) a01;
                a1 = DROP ((LENGTH a01) DIV 2) a01
            in
                general_prod_measure $++
                (mccodomain W0, mcevents W0, mcchannel W0 (MAP2 BIT_XOR a0 a1))
                (mccodomain W1, mcevents W1, mcchannel W1 a1)))
End
*)

Definition basic_fusion_channel_def:
    basic_fusion_channel splitn W0 W1 = memoryless_channel_ABS
        (basic_fusion_channel_rep splitn W0 W1)
End

(*
Definition basic_fusion_channel_def:
    basic_fusion_channel W0 W1 = memoryless_channel_ABS
        (basic_fusion_channel_rep W0 W1)
End
*)

Definition power_fusion_channel_def:
    power_fusion_channel W 0 = list_lift_channel W ∧
    power_fusion_channel W (SUC n) =
        basic_fusion_channel (2 ** n) (power_fusion_channel W n) (power_fusion_channel W n)
End

(*
Definition power_fusion_channel_def:
    power_fusion_channel W 0 = list_lift_channel W ∧
    power_fusion_channel W (SUC n) =
        basic_fusion_channel (power_fusion_channel W n) (power_fusion_channel W n)
End
*)

(*** Split Channels ***)

Definition discrete_uniform_measure_space_def:
    discrete_uniform_measure_space (S:α set) = (S, POW S,
        (λs:α set. extreal_of_num (CARD s) / extreal_of_num (CARD S)))
End

Definition BIT_msp_def:
    BIT_msp = discrete_uniform_measure_space (𝕌(:BIT))
End

(* Prove wf *)
Definition negative_pole_channel_rep_def:
    negative_pole_channel_rep W = (
        mcdomain W,
        general_sigma $++ (mcsigma W) (mcsigma W),
        (λx0 ys.
            ((general_prod_measure $++
                (mccodomain W, mcevents W, mcchannel W x0)
                (mccodomain W, mcevents W, mcchannel W ZERO) ys) +
            (general_prod_measure $++
                (mccodomain W, mcevents W, mcchannel W (BIT_NOT x0))
                (mccodomain W, mcevents W, mcchannel W ONE) ys)) / 2))
End

Definition negative_pole_channel_def:
    negative_pole_channel W = memoryless_channel_ABS (negative_pole_channel_rep W)
End

(* Prove wf *)
Definition positive_pole_channel_rep_def:
    positive_pole_channel_rep W = (
        mcdomain W,
        general_sigma (CONS ∘ INL) (measurable_space BIT_msp) (general_sigma $++ (mcsigma W) (mcsigma W)),
        (λx1 x0ys. ∫⁺ BIT_msp (λx0.
            ∫⁺ (general_prod_measure_space $++
                (mccodomain W, mcevents W, mcchannel W (BIT_XOR x0 x1))
                (mccodomain W, mcevents W, mcchannel W x1))
                (λys. 𝟙 x0ys ((INL x0)::ys)))))
End

Definition positive_pole_channel_def:
    positive_pole_channel W = memoryless_channel_ABS (positive_pole_channel_rep W)
End

(*
  Note that this leads to a "backwards" polarisation list, e.g.,
  W--+, which is ((W-)-)+ has polarisation list POS::(NEG::(NEG::[]))
*)
Definition pole_channel_def:
    pole_channel [] W = list_lift_range_channel (INR_lift_channel W) ∧
    pole_channel (NEG::polet) W = negative_pole_channel (pole_channel polet W) ∧
    pole_channel (POS::polet) W = positive_pole_channel (pole_channel polet W)
End

(** dip out of msp land **)

Definition GEN_LIST_SET_DEF:
    GEN_LIST_SET s n = {l | LENGTH l = n ∧ ∀i. i < n ⇒ EL i l ∈ s}
End

(*
val _ = reveal "C";
Definition GEN_LIST_SET_DEF:
    GEN_LIST_SET s n = {l | LENGTH l = n ∧ C EL l ∈ ((count n) → s)}
End
*)

(* Proof by Claude *)
Theorem finite_space_POW_pos_fn_integral_reduce:
    ∀m f. measure_space m ∧ POW (m_space m) = measurable_sets m ∧
        FINITE (m_space m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ⇒
        ∫⁺ m f = ∑ (λx. f x * measure m {x}) (m_space m)
Proof
    rpt strip_tac >>
    (* Singletons of points of the (POW) space are measurable. *)
    ‘∀x. x ∈ m_space m ⇒ {x} ∈ measurable_sets m’ by (
        rw[] >> ‘{x} ∈ POW (m_space m)’ suffices_by metis_tac[] >>
        simp[IN_POW,SUBSET_DEF]) >>
    ‘sigma_algebra (measurable_space m)’ by metis_tac[MEASURE_SPACE_SIGMA_ALGEBRA] >>
    (* Pointwise, f is the finite sum of its atoms' contributions:            *)
    (* ∑_x f(x)·𝟙_{x}(t) = f(t), since only the x = t term survives.          *)
    ‘∀t. t ∈ m_space m ⇒
        ∑ (λx. f x * indicator_fn {x} t) (m_space m) = f t’ by (
        rpt strip_tac >>
        ‘m_space m = t INSERT (m_space m DELETE t)’ by metis_tac[INSERT_DELETE] >>
        pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
        DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_PROPERTY] >>
        conj_tac
        >- (conj_tac >- simp[] >>
            disj1_tac >> rw[] >> irule pos_not_neginf >> irule le_mul >>
            simp[INDICATOR_FN_POS] >> gs[IN_INSERT, IN_DELETE] >> gs[]) >>
        simp[DELETE_DELETE] >>
        ‘∑ (λx. f x * indicator_fn {x} t) (m_space m DELETE t) = 0’ by (
            irule EXTREAL_SUM_IMAGE_0 >> simp[] >> rw[] >>
            ‘indicator_fn {x} t = 0’ by (rw[indicator_fn_def] >> gs[IN_DELETE]) >>
            simp[]) >>
        simp[indicator_fn_def]) >>
    (* Step 1: replace f by its atomic decomposition under the integral.      *)
    ‘∫⁺ m f = ∫⁺ m (λt. ∑ (λx. f x * indicator_fn {x} t) (m_space m))’ by (
        irule pos_fn_integral_cong >> rpt conj_tac
        >- (rw[] >> irule EXTREAL_SUM_IMAGE_POS >> rw[] >> irule le_mul >>
            simp[INDICATOR_FN_POS] >> gs[])
        >- simp[] >- (rw[] >> metis_tac[]) >- simp[]) >>
    pop_assum SUBST1_TAC >>
    (* Step 2: push the integral through the finite sum (linearity for        *)
    (* non-negative functions; needs no finiteness of f).                     *)
    ‘∫⁺ m (λt. ∑ (λx. f x * indicator_fn {x} t) (m_space m)) =
     ∑ (λx. ∫⁺ m (λt. f x * indicator_fn {x} t)) (m_space m)’ by (
        ho_match_mp_tac pos_fn_integral_sum >> rpt conj_tac
        >- gs[] >- gs[]
        >- (rw[] >> irule le_mul >> simp[INDICATOR_FN_POS] >> gs[])
        >- (rw[] >> ho_match_mp_tac IN_MEASURABLE_BOREL_MUL_INDICATOR >>
            gs[subsets_def] >> irule IN_MEASURABLE_BOREL_CONST' >> gs[])) >>
    pop_assum SUBST1_TAC >>
    (* Step 3: each atom's integral collapses to f x · measure {x} (extreal   *)
    (* coefficient, so the PosInf case is handled uniformly).                 *)
    irule EXTREAL_SUM_IMAGE_EQ >> rpt conj_tac
    >- (rw[] >> irule pos_fn_integral_cmul_indicator' >> gs[])
    >- gs[]
    >- (disj1_tac >> rw[]
        >- (irule pos_not_neginf >> irule pos_fn_integral_pos >> rw[] >>
            irule le_mul >> simp[INDICATOR_FN_POS] >> gs[])
        >- (irule pos_not_neginf >> irule le_mul >> gs[MEASURE_POSITIVE]))
QED

Theorem power_fusion_channel_discrete_mcdomain:
    ∀W. discrete_mc W ⇒ ∀n.
        mcdomain (power_fusion_channel W n) = GEN_LIST_SET 𝕌(:BIT) (2 ** n) ∧
        mccodomain (power_fusion_channel W n) = GEN_LIST_SET (mccodomain W) (2 ** n) ∧
        mcevents (power_fusion_channel W n) = POW (GEN_LIST_SET (mccodomain W) (2 ** n)) ∧
        ∀xl yls. xl ∈ mcdomain (power_fusion_channel W n) ∧
            yls ∈ mcevents (power_fusion_channel W n) ⇒
            mcchannel (power_fusion_channel W n) xl yls =
                EXTREAL_SUM_IMAGE (λyl. EXTREAL_PROD_IMAGE (λi. mcp W (EL i xl) (EL i yl)) (count (2 ** n))) yls 
Proof
    cheat
QED

(* conecting to encoding *)

val _ = export_theory();
