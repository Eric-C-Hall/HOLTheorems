(* Written by Eric Hall, under the guidance of Michael Norrish *)

(* -------------------------------------------------------------------------- *)
(* Main reference:                                                            *)
(* Erdal Arıkan,                                                              *)
(* Channel polarization: A method for constructing capacity-achieving codes   *)
(* for symmetric binary-input memoryless channels. 2009.                      *)
(* -------------------------------------------------------------------------- *)

Theory bhattacharyya

Ancestors arithmetic extreal lifting pair pred_set real measure sigma_algebra transfer memoryless_channel probability

Libs dep_rewrite liftLib transferLib realLib;

Definition bhattacharyya_def:
  bhattacharyya (W : (bool, β) memoryless_channel)
  = EXTREAL_SUM_IMAGE
    (λx. sqrt ((mcchannel W F) {x} * (mcchannel W T) {x}))
    (mccodomain W)
End



