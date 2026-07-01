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
(* The combined channel used in Polar encoding.                               *)
(*                                                                            *)
(* We can't output a memoryless_channel type because the number of inputs is  *)
(* dependent on num_inputs, but a type can't be chosen based on the values of *)
(* inputs. Thus, we output a bool list -> (β list) m_space, which is the      *)
(* underlying representative type.                                            *)
(* -------------------------------------------------------------------------- *)
Definition combine_channel_direct_def:
  combine_channel_direct (W : (bool, β) memoryless_channel) num_inputs inputs
  = MAP (memoryless_channel_REP W) (polar_encode inputs)
    : (β list) m_space
End
