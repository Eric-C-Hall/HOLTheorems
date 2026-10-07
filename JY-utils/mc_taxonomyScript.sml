(* Scratch work of Jared Yeager, for use in work with Eric Hall and Michael Norrish *)

open HolKernel Parse boolLib bossLib;
open pairTheory;
open arithmeticTheory;
open pred_setTheory;
open listTheory;
open realTheory;
open realLib;
open extrealTheory;
open sigma_algebraTheory;
open measureTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;

(* open ex_machina; *)
open trivialTheory;
open memoryless_channelTheory;

val _ = new_theory "mc_taxonomy";

val _ = hide "W";

(*** Memoryless channel probability ***)

Definition mcp_def:
    mcp c a b = mcchannel c a ($= b)
End

(*** Binary and Discrete ***)

Definition binary_mc_def:
    binary_mc c ⇔ CARD (mcdomain c) = 2
End

Definition discrete_mc_def:
    discrete_mc c ⇔ FINITE (mccodomain c)
End

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

(*
Definition list_lift_channel_rep_def:
    list_lift_channel_rep W = (
        IMAGE (λx. [x]) (mcdomain W),
        (IMAGE (λy. [y]) (mcrange W), IMAGE (IMAGE (λy. [y])) (mcevents W)),
        (λal bls. mcchannel W (HD al) (IMAGE HD bls)))
End

Definition list_lift_channel_def:
    list_lift_channel W = memoryless_channel_ABS (list_lift_channel_rep W)
End
*)

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

Definition basic_fusion_channel_def:
    basic_fusion_channel W0 W1 = memoryless_channel_ABS
        (basic_fusion_channel_rep W0 W1)
End

Definition power_fusion_channel_def:
    power_fusion_channel 0 W = list_lift_channel W ∧
    power_fusion_channel (SUC n) W =
        basic_fusion_channel (power_fusion_channel n W) (power_fusion_channel n W)
End

(*** Split Channels ***)

Definition discrete_uniform_measure_space_def:
    discrete_uniform_measure_space (S:α set) = (S, POW S,
        (λs:α set. extreal_of_num (CARD s) / extreal_of_num (CARD S)))
End

Definition BIT_msp_def:
    BIT_msp = discrete_uniform_measure_space (𝕌(:BIT))
End

(*
(* Prove wf *)
Definition negative_pole_channel_rep_def:
    negative_pole_channel_rep W0 W1 = (
        mcdomain W0,
        general_sigma $++ (mcsigma W0) (mcsigma W1),
        (λx0 ys.
            ((general_prod_measure $++
                (mcrange W0, mcevents W0, mcchannel W0 x0)
                (mcrange W1, mcevents W1, mcchannel W1 ZERO) ys) +
            (general_prod_measure $++
                (mcrange W0, mcevents W0, mcchannel W0 (BIT_NOT x0))
                (mcrange W1, mcevents W1, mcchannel W1 ONE) ys)) / 2))
End

Definition negative_pole_channel_def:
    negative_pole_channel W0 W1 = memoryless_channel_ABS (negative_pole_channel_rep W0 W1)
End

(* Prove wf *)
Definition positive_pole_channel_rep_def:
    positive_pole_channel_rep W0 W1 = (
        mcdomain W1,
        general_sigma (CONS ∘ INL) (measurable_space BIT_msp) (general_sigma $++ (mcsigma W0) (mcsigma W1)),
        (λx1 x0ys. ∫⁺ BIT_msp (λx0.
            ∫⁺ (general_prod_measure_space $++
                (mcrange W0, mcevents W0, mcchannel W0 (BIT_XOR x0 x1))
                (mcrange W1, mcevents W1, mcchannel W1 x1))
                (λys. 𝟙 x0ys ((INL x0)::ys)))))
End

Definition positive_pole_channel_def:
    positive_pole_channel W0 W1 = memoryless_channel_ABS (positive_pole_channel_rep W0 W1)
End

Definition pole_channel_def:
    pole_channel [] W = list_lift_range_channel (INR_lift_channel W) ∧
    pole_channel (NEG::polet) W = negative_pole_channel (pole_channel polet W) (pole_channel polet W) ∧
    pole_channel (POS::polet) W = positive_pole_channel (pole_channel polet W) (pole_channel polet W)
End
*)

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

Definition pole_channel_def:
    pole_channel [] W = list_lift_range_channel (INR_lift_channel W) ∧
    pole_channel (NEG::polet) W = negative_pole_channel (pole_channel polet W) ∧
    pole_channel (POS::polet) W = positive_pole_channel (pole_channel polet W)
End

(* dip out of msp land *)
(* conecting to encording *)

val _ = export_theory();
