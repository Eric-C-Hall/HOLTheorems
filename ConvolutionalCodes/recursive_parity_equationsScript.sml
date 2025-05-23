open HolKernel Parse boolLib bossLib;

open parity_equationsTheory;

val _ = new_theory "recursive_parity_equations";

(* -------------------------------------------------------------------------- *)
(* Convolve a recursive parity equation over some input.                      *)
(*                                                                            *)
(* Starts by applying the numerator parity equation to the first n elements   *)
(* of the input. Combines the result with the provided feedback. Then         *)
(* applies the denominator to the first n elements and uses the resulting     *)
(* feedback to perform the next step along the input string.                  *)
(*                                                                            *)
(* The termination method used by this function is to treat any input beyond  *)
(* the end of the string as if it were zero, and to stop outputting bits when *)
(* there are no longer any input bits in the string. This reduces             *)
(* implementation complexity, but may not be the best termination method.     *)
(*                                                                            *)
(* (ps, qs): the recursive parity equation to convolve (ps is the numerator   *)
(* and qs is the denominator. That is, ps represents the effect that the      *)
(* current input will have on the output, and qs represents the effect that   *)
(* the current input will have on the feedback for the next iteration).       *)
(*                                                                            *)
(* bs: the input to the convolution                                           *)
(*                                                                            *)
(* f: the feedback from the previous step of the convolution (if no feedback  *)
(*    is available, you should probably set this to F)                        *)
(* -------------------------------------------------------------------------- *)
Definition convolve_recursive_parity_equation_def:
  convolve_recursive_parity_equation _ [] _ = [] ∧
  convolve_recursive_parity_equation (ps, qs) (b::bs) f =
  ((apply_parity_equation ps (b::bs)) ⇎ f)
  :: convolve_recursive_parity_equation (ps, qs) bs
  (apply_parity_equation qs (b::bs))
End



(* -------------------------------------------------------------------------- *)
(* TODO: Encode the recursive parity equation in a way which is sensible, in  *)
(* particular with regards to the ininitialization and termination schemes    *)
(* -------------------------------------------------------------------------- *)
Definition encode_recursive_parity_equation_def:
  encode_recursive_parity_equation rs bs =
  convolve_recursive_parity_equation 
End



Definition decode_recursive_parity_equation_def:
  decode_recursive_parity_equation rs bs = 
End

(* -------------------------------------------------------------------------- *)
(* Encoding and decoding a recursive parity equation using the BCJR algorithm *)
(* will return the original data again                                        *)
(* -------------------------------------------------------------------------- *)
Theorem encode_decode_recursive_parity_equation:
  (encode_recursive_parity_equation rs) ∘
  (decode_recursive_parity_equation rs) = I
Proof
QED


(* -------------------------------------------------------------------------- *)
(* Ensure that the decoding procedure for a recursive parity equation encoder *)
(* implements an a posteriori encoder (TODO: check that I have my terminology *)
(* correct)                                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem decode_recursive_parity_equation_a_posteriori:
  (decode_recursive_parity_equation rs)
Proof
QED

val _ = export_theory();
