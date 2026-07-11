Theory deterministic_channel

Ancestors arithmetic bitstring bxor_lemmas degenerate_distribution memoryless_channel

Libs dep_rewrite realLib;

Definition deterministic_channel0_def:
  deterministic_channel0 (f : α -> β) (S : α -> bool) =
  (S, λx. degenerate_prob_space (f x) 𝕌(:β))
  : (α -> bool) # (α -> β m_space)
End

