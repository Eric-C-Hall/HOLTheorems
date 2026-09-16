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
  symmetric_capacity0 (W : (α -> bool) # (α -> β m_space)) =
  let
    p =
  in
    mutual_information 2 (uniform_distribution (mcdomain0 W, POW (mcdomain0 W)))
                     (POW (mcdomain0 W)) () I (λx. mcchannel0 W x)
End

(* This definition was co-written with help from Gemini 3.8 Flash *)
Definition symmetric_capacity0_def:
  symmetric_capacity0 (W : ('a -> bool) # ('a -> 'b m_space)) =
  let
    p_X = uniform_distribution (mcdomain0 W, POW (mcdomain0 W));
    S = mcdomain0 W × mcrange0 W;
    p_joint = (S, POW S, (\A. SIGMA (\(x, y). p_X {x} * prob (mcchannel0 W x) {y}) A))
  in
    mutual_information 2 p_joint
                           (mcdomain0 W, POW (mcdomain0 W))
                           (mcrange0 W, POW (mcrange0 W))
                           FST
                           SND
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


