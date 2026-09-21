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

Definition bhattacharyya0_def:
  bhattacharyya0 (W : (bool -> bool) # (β algebra) # (bool -> β measure))
  = EXTREAL_SUM_IMAGE
    (λx. sqrt ((mcchannel0 W F) {x} * (mcchannel0 W T) {x}))
    (mccodomain0 W)
End





