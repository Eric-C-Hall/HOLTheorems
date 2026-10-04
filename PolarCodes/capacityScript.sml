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
(* TODO: prob dist on input -> prob dist on output

Output probability distribution has space which is space of input times space of output *)
(* -------------------------------------------------------------------------- *)
Definition symmetric_capacity_def:
  symmetric_capacity (W : (α, β) memoryless_channel) =
  let
    p = TODO_TRANSFORM_VIA_CHANNEL_DISTRIBUTION
        W
        uniform_distribution (mcdomain W, POW (mcdomain W))

        (uniform_distribution (mcdomain W, POW (mcdomain W)))
        × (W )
  in
    mutual_information 2 
                       (POW (mcdomain0 W)) () I (λx. mcchannel0 W x)
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
