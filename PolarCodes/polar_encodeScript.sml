Theory polar_encode

Ancestors arithmetic bitstring interleave

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
(*                                                                            *)
(* Undefined behaviour if length of input is not a power of two.              *)
(* -------------------------------------------------------------------------- *)
Definition polar_encode_def:
  polar_encode (inputs : bool list) =
  if LENGTH inputs ≤ 1 then inputs
  else
    let
      even_odd_inputs = deinterleave 2 inputs;
      even_inputs = EL 0 even_odd_inputs;
      odd_inputs = EL 1 even_odd_inputs;
    in
      polar_encode (bxor even_inputs odd_inputs) ++ polar_encode odd_inputs
Termination
  WF_REL_TAC ‘measure (LENGTH)’
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> 
     )


