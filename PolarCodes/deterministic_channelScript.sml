Theory deterministic_channel

Ancestors arithmetic bitstring bxor_lemmas memoryless_channel

Libs dep_rewrite realLib;

(* Thanks to Jared Yeager for idea for representation of the dirac measure *)

Definition deterministic_channel_def:
  deterministic_channel (f : α -> β) (S : α -> bool) =
  (S, λx. combin$C 𝟙 (f x))
  : (α -> bool) # (α -> β measure)
End

