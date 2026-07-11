Theory concat_channel

Ancestors arithmetic bitstring bxor_lemmas lifting memoryless_channel transfer

Libs dep_rewrite realLib liftLib transferLib;

Definition concat_channel0_def:
  concat_channel0
  (W1 : (α -> bool) # (α -> β m_space))
  (W2 : (β -> bool) # (β -> γ m_space)) =
  (mcdomain0 W1, mcchannel0 W1
                            mcchannel0 W2)
End

(* mcrange might be helpful in checking that the output of the first channel is
   in the domain of the second channel *)


