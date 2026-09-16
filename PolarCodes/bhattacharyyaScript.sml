(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory bhattacharyya

Ancestors arithmetic extreal lifting pair pred_set real measure sigma_algebra transfer memoryless_channel probability

Libs dep_rewrite liftLib transferLib realLib;

Definition bhattacharyya0_def:
  bhattacharyya0 (W : (bool -> bool) # (bool -> bool m_space)) =
  EXTREAL_SUM_IMAGE
  (λx. sqrt (prob (mcchannel0 W F) {x} * prob (mcchannel0 W T) {x}))
  (mcdomain0 W)
End





