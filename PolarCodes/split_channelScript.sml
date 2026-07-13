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



(* -------------------------------------------------------------------------- *)
(* TODO: find this definition somewhere                                       *)
(* Probably apply general_cross from martingaleTheory?                        *)
(* -------------------------------------------------------------------------- *)
Definition TODO_prod_set_def:
  TODO_prod_set (set : α -> bool) (num_prod : num) = ARB : α list -> bool
End

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition split_channel_def:
  split_channel (W : α -> β memoryless_channel) i =
  EXTREAL_SUM_IMAGE (λ(1 / 2 ** TODO) * ) (TODO_prod_set (mcdomain W) ())
End
