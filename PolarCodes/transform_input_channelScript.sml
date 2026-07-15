Theory transform_input_channel

Ancestors arithmetic lifting list memoryless_channel probability rich_list transfer

Libs dep_rewrite liftLib realLib transferLib;

(* -------------------------------------------------------------------------- *)
(* Concat channel is more general, but that also makes it more complicated,   *)
(* harder to define and probably harder to write theorems about.              *)
(* -------------------------------------------------------------------------- *)
Definition transform_input_channel0_def:
  transform_input_channel0 (f : α -> β) (S : α -> bool) (W : (β -> bool) # (β -> γ m_space)) =
  (S ∩ PREIMAGE f (mcdomain0 W),
   (mcchannel0 W) ∘ f
  ) : (α -> bool) # (α -> γ m_space)
End

Theorem wf_memoryless_channel_transform_input_channel0:
  ∀f S W.
    wf_memoryless_channel W ⇒
    wf_memoryless_channel (transform_input_channel0 f S W)
Proof
  rpt gen_tac >> strip_tac
  >> gvs[wf_memoryless_channel_def]
  >> gen_tac >> strip_tac
  >> gvs[transform_input_channel0_def, mcchannel0_def, mcdomain0_def]
QED

Theorem transform_input_channel0_respects:
  ((=) ===> (=) ===> (memoryless_channelequiv) ===> (memoryless_channelequiv))
  transform_input_channel0 transform_input_channel0
Proof
  simp[FUN_REL_def]
  >> rpt gen_tac
  >> simp[memoryless_channelequiv_def, wf_memoryless_channel_transform_input_channel0]
QED

val (transform_input_channel_def, transform_input_channel_relates) =
liftdef transform_input_channel0_respects "transform_input_channel";

(*
(* -------------------------------------------------------------------------- *)
(* Transforming the input to a channel is equivalent to concatentating a      *)
(* deterministic channel to the front of the channel.                         *)
(* -------------------------------------------------------------------------- *)
Theorem transform_input_channel_deterministic_channel_concat_channel:

Proof
QED
*)
