Theory concat_channel

Ancestors arithmetic bitstring bxor_lemmas memoryless_channel

Libs dep_rewrite realLib;

Definition concat_channel0_def:
  concat_channel
  (W1 : (α -> bool) # (α -> β m_space))
  (W2 : (β -> bool) # (β -> γ m_space)) =
  (mcdomain W1, )
End



