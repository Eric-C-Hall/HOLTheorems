(* Written by Eric Hall, under the guidance of Michael Norrish *)

(* -------------------------------------------------------------------------- *)
(* Main reference:                                                            *)
(* Erdal Arıkan,                                                              *)
(* Channel polarization: A method for constructing capacity-achieving codes   *)
(* for symmetric binary-input memoryless channels. 2009.                      *)
(* -------------------------------------------------------------------------- *)

Theory capacity

Ancestors arithmetic extreal extreal_information lifting pair pred_set real measure sigma_algebra transfer memoryless_channel probability

Libs dep_rewrite liftLib transferLib realLib;

(* TODO: Note to AI: This is quite incomplete, and the definitions and theorems in this file will probably need substantial editing. *)

(* -------------------------------------------------------------------------- *)
(* The joint distribution on (input, output) obtained by drawing an input     *)
(* according to P and then passing it through W.                              *)
(*                                                                            *)
(* Assumes the domain is finite, so that we may sum over it, and uses the     *)
(* fact that every section {y | (x,y) ∈ s} of a product-measurable set s is  *)
(* measurable in the output sigma algebra.                                    *)
(*                                                                            *)
(* Written by Claude                                                          *)
(* -------------------------------------------------------------------------- *)
Definition apply_channel_distribution_def:
  apply_channel_distribution (W : (α,β) memoryless_channel) (P : α measure) =
  λs. ∑ (λx. P {x} * mcchannel W x {y | (x,y) ∈ s}) (mcdomain W)
End

(* -------------------------------------------------------------------------- *)
(* The probability space which first chooses an input according to P, then    *)
(* chooses an output according to the probability distribution for that       *)
(* input. The sample space is the product of the input and output spaces.     *)
(*                                                                            *)
(* Written by Claude                                                          *)
(* -------------------------------------------------------------------------- *)
Definition apply_channel_prob_space_def:
  apply_channel_prob_space (W : (α,β) memoryless_channel) (P : α measure) =
  (mcdomain W × mccodomain W,
   subsets (prod_sigma (mcdomain W, POW (mcdomain W)) (mcsigma W)),
   apply_channel_distribution W P)
End

(* -------------------------------------------------------------------------- *)
(* The channel capacity is the mutual information between the input and       *)
(* output of the channel when maximizing over all possible input              *)
(* distributions                                                              *)
(*                                                                            *)
(* Assumes the domain is discrete                                             *)
(*                                                                            *)
(* Written by Claude                                                          *)
(* -------------------------------------------------------------------------- *)
Definition channel_capacity_def:
  channel_capacity (W : (α,β) memoryless_channel) =
  sup {mutual_information 2 (apply_channel_prob_space W P)
                            (mcdomain W, POW (mcdomain W)) (mcsigma W) FST SND
       | P | prob_space (mcdomain W, POW (mcdomain W), P)}
End

(* -------------------------------------------------------------------------- *)
(* A version of the channel capacity which uses the discrete mutual           *)
(* information. The joint mass function of the input and output is            *)
(* P(x,y) = P {x} * W(y|x), where W(y|x) is the probability that the channel  *)
(* outputs y when given input x.                                              *)
(*                                                                            *)
(* Assumes both the domain and codomain are discrete (finite, and every       *)
(* singleton of the codomain is an event)                                     *)
(*                                                                            *)
(* In process of manually validating this: it appears to be taking the input  *)
(* and output independently, on first glance? Is this correct?                *)
(*                                                                            *)
(* Written by Claude                                                          *)
(* -------------------------------------------------------------------------- *)
Definition channel_capacity_discrete_def:
  channel_capacity_discrete (W : (α,β) memoryless_channel) =
  sup {mutual_information_discrete 2 (mcdomain W) (mccodomain W)
                                   (λ(x,y). P {x} * mcchannel W x {y})
       | P | prob_space (mcdomain W, POW (mcdomain W), P)}
End

(* -------------------------------------------------------------------------- *)
(* The symmetric capacity is the mutual information between the input and     *)
(* output of the channel when the input is given by the uniform distribution. *)
(*                                                                            *)
(* Assumes the domain is discrete                                             *)
(*                                                                            *)
(* Written by Claude                                                          *)
(* -------------------------------------------------------------------------- *)
Definition symmetric_capacity_def:
  symmetric_capacity (W : (α,β) memoryless_channel) =
  mutual_information 2
    (apply_channel_prob_space W
       (uniform_distribution (mcdomain W, POW (mcdomain W))))
    (mcdomain W, POW (mcdomain W))
    (mcsigma W)
    FST SND
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
