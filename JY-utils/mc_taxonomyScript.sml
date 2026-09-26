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

(*** Binary and Discrete ***)

Definition binary_mc_def:
    binary_mc c ⇔ CARD (mcdomain c) = 2
End

Definition discrete_mc_def:
    discrete_mc c ⇔ FINITE (mcrange c)
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

Datatype:
    POLE = POS | NEG
End

(* Memoryless channel probability *)

Definition mcp_def:
    mcp c a b = mcchannel c a ($= b)
End

(* Compound and Split channels *)

(* (W0:(BIT,β) memoryless_channel) (W:(BIT,β) memoryless_channel) *)

(*
Definition basic_fusion_channel_rep_def:
    basic_fusion_channel_rep W0 W1 =
        (mcdomain W0 × mcdomain W1, mcsigma W0 × mcsigma W1,
           (λ(a0,a1).
            general_prod_measure ($,)
                (mcrange W0, mcevents W0, mcchannel W0 (BIT_XOR a0 a1))
                (mcrange W1, mcevents W1, mcchannel W1 a1))
        )
End
*)

(* NTS: try combine channel *)

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
                (mcrange W0, mcevents W0, mcchannel W0 (MAP2 BIT_XOR a0 a1))
                (mcrange W1, mcevents W1, mcchannel W1 a1)))
End

(* prove above wf *)

Definition basic_fusion_channel_def:
    basic_fusion_channel W0 W1 = memoryless_channel_ABS
        (basic_fusion_channel_rep W0 W1)
End

Definition list_lift_channel_rep_def:
    list_lift_channel_rep W = (
        IMAGE (λx. [x]) (mcdomain W),
        (IMAGE (λy. [y]) (mcrange W), IMAGE (IMAGE (λy. [y])) (mcevents W)),
        (λal bls. mcchannel W (HD al) (IMAGE HD bls)))
End

(* prove above wf *)

Definition list_lift_channel_def:
    list_lift_channel W = memoryless_channel_ABS (list_lift_channel_rep W)
End

Definition power_fusion_channel_def:
    power_fusion_channel 0 W = list_lift_channel W ∧
    power_fusion_channel (SUC n) W =
        basic_fusion_channel (power_fusion_channel n W) (power_fusion_channel n W)
End

val _ = export_theory();
