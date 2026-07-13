Theory combine_channel

Ancestors arithmetic bitstring bxor_lemmas interleave polar_encode

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
(*Definition combine_channel_def:
  combine_channel (W : (α, β) memoryless_channel) num_inputs
  = if num_inputs ≤ 1
    then
      λinputs.
        TODO TODO TODO
             Apply W to inputs here
             TODO TODO TODO
    else
      let
        recursive_channel = polar_encode_channel W (num_inputs DIV 2)
      in
        λinputs.
          let
        even_odd_inputs = deinterleave 2 inputs;
        even_inputs = EL 0 even_odd_inputs;
        odd_inputs = EL 1 even_odd_inputs;
      in
        polar_encode (bxor even_inputs odd_inputs) ++ polar_encode odd_inputs

                                                                   (λbs. )
                                                                   polar_encode_channel
End*)

(* -------------------------------------------------------------------------- *)
(* TODO: when combine_channel def has been defined, this should be a theorem  *)
(* rather than a definition                                                   *)
(* TODO: when defining combine_channel directly, can this be defined as an    *)
(* (α list, β list) memoryless_channel rather than a                          *)
(* (bool list, β list) memoryless_channel                                     *)
(* -------------------------------------------------------------------------- *)
Definition combine_channel_alt:
  combine_channel (W : (bool, β) memoryless_channel) (num_inputs : num)
  = polar_encode_channel W num_inputs
    : (bool list, β list) memoryless_channel
End
