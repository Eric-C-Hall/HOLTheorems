(* Written by Eric Hall, under the guidance of Michael Norrish *)

(* -------------------------------------------------------------------------- *)
(* Main reference:                                                            *)
(* Erdal Arıkan,                                                              *)
(* Channel polarization: A method for constructing capacity-achieving codes   *)
(* for symmetric binary-input memoryless channels. 2009.                      *)
(* -------------------------------------------------------------------------- *)

Theory capacity

Ancestors arithmetic extreal information lifting pair pred_set real measure sigma_algebra transfer memoryless_channel probability

Libs dep_rewrite liftLib transferLib realLib;

(* -------------------------------------------------------------------------- *)
(* The channel capacity is the mutual information between the input and       *)
(* output of the channel when maximizing over all possible input              *)
(* distributions                                                              *)
(* -------------------------------------------------------------------------- *)
(*Definition channel_capacity_def:
  channel_capacity (W : (α,β) memoryless_channel) =
  mutual_information
  2 shared_prob_space sigma_algebra_first_var sigma_algebra_second_var first_var second_var
End*)

(* -------------------------------------------------------------------------- *)
(* The symmetric capacity is the mutual information between the input and     *)
(* output of the channel when the input is given by the uniform distribution. *)
(*                                                                            *)
(* Assumes the domain is discrete                                             *)
(*                                                                            *)
(* Probability space has                                                      *)
(*                                                                            *)
(*                                                                            *)
(* The input and channel are the two sources of relevant randomness.          *)
(*                                                                            *)
(* Thus, our probab                                                           *)
(* Probability space must include uniform distribution on input               *)
(* Probability space must include output sigma algebra                        *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* TODO: prob dist on input -> prob dist on output

Output probability distribution has space which is space of input times space of output *)
(* -------------------------------------------------------------------------- *)
Definition symmetric_capacity_def:
  symmetric_capacity (W : (α, β) memoryless_channel) =
  let
    input_distribution = uniform_distribution (mcdomain W, POW (mcdomain W));
    input_prob_space = (mcdomain W, POW (mcdomain W));
    output_prob_space = ;
    
    p = TODO_TRANSFORM_VIA_CHANNEL_DISTRIBUTION
        W
  in
    mutual_information 2
                       input_distribution × output_distribution
                       
End

(* -------------------------------------------------------------------------- *)
(* The symmetric capacity is the mutual information between the input and     *)
(* output of the channel when the input is given by the uniform distribution. *)
(*                                                                            *)
(* Definition based on Arıkan's original polar codes paper                    *)
(* -------------------------------------------------------------------------- *)
(*
Theorem symmetric_capacity0_alt:
  symmetric_capacity0 (W : (bool -> bool) # (bool -> β m_space)) =
  EXTREAL_SUM_IMAGE
  (λy.
     EXTREAL_SUM_IMAGE
     (λx.
        (1/2) * prob (mcchannel0 W x) {y} *
        lg (prob (mcchannel0 W x) {y} /
                 ((1/2) *
                  (prob (mcchannel0 W x) {F}) *
                  prob (mcchannel0 W x) {T}
                 )
           )
     ) {T; F}
  ) (mcrange0 W)
QED
*)
