Theory combine_channel

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
(* Combines channels as in polar encoding.                                    *)
(* -------------------------------------------------------------------------- *)
Definition combine_channel_def:
  polar_encode_channel (W : binary_memoryless_channel) num_inputs
  = (λbs. )
End
