Theory concat_channel

Ancestors arithmetic bitstring bxor_lemmas lifting memoryless_channel transfer

Libs dep_rewrite realLib liftLib transferLib;

(* -------------------------------------------------------------------------- *)
(* TODO: maybe it would be more sensible to perform the pushforward in order  *)
(* to get the polar encoding channel, rather than the stronger technology     *)
(* of using the concatenation of channels. The weaker technology should       *)
(* suffice and should have stronger theorems available because it is more     *)
(* restricted.                                                                *)
(* -------------------------------------------------------------------------- *)

Definition concat_channel0_def:
  concat_channel0
  (W1 : (α -> bool) # (α -> β m_space))
  (W2 : (β -> bool) # (β -> γ m_space)) =
  (mcdomain0 W1, ARB (*mcchannel0 W1
                            mcchannel0 W2*))
  : (α -> bool) # (α -> γ m_space)
End

Theorem wf_memoryless_channel_concat_channel0:
  ∀W1 W2.
    wf_memoryless_channel W1 ∧
    wf_memoryless_channel W2 ⇒
    wf_memoryless_channel (concat_channel0 W1 W2)
Proof
  cheat
QED

Theorem concat_channel0_respects:
  ((memoryless_channelequiv) ===> (memoryless_channelequiv) ===>
                             (memoryless_channelequiv))
  concat_channel0 concat_channel0
Proof
  simp[FUN_REL_def]
  >> rpt gen_tac
  >> rename [‘memoryless_channelequiv W1 W2’]
  >> strip_tac
  >> rpt gen_tac
  >> rename [‘memoryless_channelequiv U1 U2 ⇒ _’]
  >> strip_tac
  >> gvs[memoryless_channelequiv_def, wf_memoryless_channel_concat_channel0]
QED

val (concat_channel_def, concat_channel_relates) =
liftdef concat_channel0_respects "concat_channel";

Overload "o" = “concat_channel”;

(* mcrange might be helpful in checking that the output of the first channel is
   in the domain of the second channel *)


