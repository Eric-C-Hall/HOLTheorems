Theory polar_encode

Ancestors arithmetic

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
(* Unlike in Arıkan's original Polar Codes paper, we use the computer science *)
(* convention of 0-indexed lists rather than the mathematical convention of   *)
(* 1-indexed lists                                                            *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Polar encoding:                                                            *)
(* polar_encode = polar_encode (even_inputs bitwise_XOR odd_inputs) ++        *)
(*                polar_encode odd_inputs                                     *)
(* -------------------------------------------------------------------------- *)
Definition polar_encode_def:
  polar_encode (inputs : bool list) =
  if LENGTH inputs = 1 then inputs
  else
    let
      even_inputs = ;
      odd_inputs = ;
    in
      polar_encode () ++ polar_encode ()
End


