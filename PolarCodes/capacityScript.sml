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
(*Definition channel_capacity0_def:
  channel_capacity0 (W : (bool -> bool) # (bool -> β m_space)) =
  ARB
  mutual_information 2 ()
End*)

(* -------------------------------------------------------------------------- *)
(* The symmetric capacity is the mutual information between the input and     *)
(* output of the channel when the input is given by the uniform distribution. *)
(* -------------------------------------------------------------------------- *)
Definition symmetric_capacity0_def:
  symmetric_capacity0 (W : (α -> bool) # (β algebra) # (α -> β measure)) =
  let
    p = (uniform_distribution (mcdomain0 W, POW (mcdomain0 W)))
        × (mcrange0 W ) (* the range shouldn't vary with input, redefine memoryless channel to not produce a distinct sigma algebra per input *)
  in
    mutual_information 2 
                       (POW (mcdomain0 W)) () I (λx. mcchannel0 W x)
End

(* -------------------------------------------------------------------------- *)
(* The symmetric capacity is the mutual information between the input and     *)
(* output of the channel when the input is given by the uniform distribution. *)
(* -------------------------------------------------------------------------- *)
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

