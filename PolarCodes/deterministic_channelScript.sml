Theory deterministic_channel

Ancestors arithmetic bitstring bxor_lemmas degenerate_distribution lifting memoryless_channel transfer

Libs dep_rewrite realLib liftLib transferLib;

Definition deterministic_channel0_def:
  deterministic_channel0 (f : α -> β) (S : α -> bool) =
  (S, λx. degenerate_prob_space (f x) 𝕌(:β))
  : (α -> bool) # (α -> β m_space)
End

Theorem wf_memoryless_channel_deterministic_channel0:
  ∀f S.
    wf_memoryless_channel (deterministic_channel0 f S)
Proof
  rpt gen_tac
  >> simp[deterministic_channel0_def, wf_memoryless_channel_def]
  >> simp[mcchannel0_def, mcdomain0_def]
  >> gen_tac >> strip_tac
  >> simp[degenerate_prob_space_is_prob_space]
QED

Theorem deterministic_channel0_respects:
  ((=) ===> (=) ===> (memoryless_channelequiv))
  deterministic_channel0 deterministic_channel0
Proof
  simp[FUN_REL_def]
  >> rpt gen_tac
  >> simp[memoryless_channelequiv_def, wf_memoryless_channel_deterministic_channel0]
QED

val (deterministic_channel_def, deterministic_channel_relates) =
liftdef deterministic_channel0_respects "deterministic_channel";

