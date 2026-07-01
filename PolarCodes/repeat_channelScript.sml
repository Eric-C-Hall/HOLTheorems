Theory repeat_channel

Ancestors arithmetic bitstring bxor_lemmas interleave polar_encode

Libs dep_rewrite realLib;

Definition repeat_channel_def:
  repeat_channel (W : (bool, β) memoryless_channel) (num_inputs : num)
  (input : bool list)
  = if (num_inputs = 0) then []
    else
      ((memoryless_channel_REP W) (HD input))::(repeat_channel W (num_inputs - 1) (TL input)
                                                : (β list) mspace
End
