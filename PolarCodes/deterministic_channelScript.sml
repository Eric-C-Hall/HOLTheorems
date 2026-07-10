Theory deterministic_channel

Ancestors arithmetic bitstring bxor_lemmas degenerate_distribution memoryless_channel

Libs dep_rewrite realLib;

Definition deterministic_channel_def:
  deterministic_channel (f : α -> β) (S : α -> bool) =
  (S, λx. degenerate_distribution (f x))
  : (α -> bool) # (α -> β m_space)
End

