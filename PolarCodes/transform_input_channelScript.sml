Theory transform_input_channel

Ancestors arithmetic list rich_list probability

Libs dep_rewrite realLib;

(* -------------------------------------------------------------------------- *)
(* Concat channel is more general, but that also makes it more complicated,   *)
(* harder to define and probably harder to write theorems about.              *)
(* -------------------------------------------------------------------------- *)
Definition transform_input_channel0_def:
  transform_input_channel0 f (W : (α -> bool) # (α -> β m_space)) =
  (mcdomain0 W,
   
  )
End

Theorem wf_memoryless_transform_input_channel0:
  ∀f W.
    wf_memoryless_channel W ⇒
    wf_memoryless_channel (transform_input_channel0 f W)
Proof
  cheat
QED

Theorem transform_input_channel0_respects:
  ((memoryless_channelequiv) ===> (=) ===> (memoryless_channelequiv))
  transform_input_channel0 transform_input_channel0
Proof
QED

val (concat_channel_def, concat_channel_relates) =
liftdef concat_channel0_respects "concat_channel";

(*
(* -------------------------------------------------------------------------- *)
(* Transforming the input to a channel is equivalent to concatentating a      *)
(* deterministic channel to the front of the channel.                         *)
(* -------------------------------------------------------------------------- *)
Theorem transform_input_channel_deterministic_channel_concat_channel:

Proof
QED
*)
