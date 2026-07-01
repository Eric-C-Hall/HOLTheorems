Theory split_channel

Ancestors arithmetic bitstring bxor_lemmas interleave

Libs dep_rewrite realLib;

(* -------------------------------------------------------------------------- *)
(* Based on "Channel polarization: A method for constructing                  *)
(* capacity-achieving codes for symmetric binary-input memoryless channels    *)
(* by Erdal Arıkan                                                            *)
(*                                                                            *)
(* Based on "Polar Codes: from theory to practice" by Mohammad Rowshan and    *)
(* Emanuele Viterbo                                                           *)
(* -------------------------------------------------------------------------- *)

Definition split_channel_def:
  split_channel (W : α -> β memoryless_channel) i =
  extreal_sum_image TODO ((1 / 2 ** TODO) * )
End
