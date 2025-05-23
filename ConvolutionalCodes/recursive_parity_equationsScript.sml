open HolKernel Parse boolLib bossLib;

open parity_equationsTheory;

val _ = new_theory "recursive_parity_equations";

(* -------------------------------------------------------------------------- *)
(* This is largely based on "Modern Coding Theory" by Tom Richardson and      *)
(* Rüdiger Urbanke.                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Run a recursive parity equation on some input. Does not output the         *)
(* systematic bits.                                                           *)
(*                                                                            *)
(* 1. Read the next input bit.                                                *)
(* 2. Calculate the feedback by applying the denominator parity equation to   *)
(*    the current state                                                       *)
(* 3. Add the feedback to the current input bit. Use this to update the       *)
(*    current state.                                                          *)
(* 4. Calculate the output in this step by applying the numerator parity      *)
(*    equation to the updated state.                                          *)
(* 5. Drop the oldest bit from the current state to ensure it retains its     *)
(*    original length                                                         *)
(* 6. Start again from step 1.                                                *)
(*                                                                            *)
(* Termination is simply handled by performing no additional output when      *)
(* there is no further input.                                                 *)
(*                                                                            *)
(* (ps, qs): the recursive parity equations to convolve (ps is the numerator  *)
(* and qs is the denominator).                                                *)
(* - The order of the booleans in each parity equation is the same as the     *)
(*   order of the corresponding booleans in the input. That is, the rightmost *)
(*   bit in the parity equation corresponds to the most recently read bit.    *)
(* - The last bit of qs is ignored and assumed to be 1. This is because we    *)
(*   always use the input as a part of the "feedback" to determine the        *)
(*   modified input at a given point in time, otherwise, the input would have *)
(*   no effect on computation. Nevertheless, we do expect this 1-bit to be    *)
(*   present.                                                                 *)
(* - We expect the length of each parity equation to be equal to the length   *)
(*   of the current state. If not, then we assume that the parity equations   *)
(*   are padded with sufficiently many zeroes to ensure that they are of the  *)
(*   correct length (the padding occuring before the final 1-bit in the case  *)
(*   of the denominator)                                                      *)
(*                                                                            *)
(* ts: the current state of the parity equation. This is a list of booleans,  *)
(*     so that the order of the booleans in the list is the same as the order *)
(*     that the corresponding booleans were in in the initial input. That is, *)
(*     the rightmost bit is the most recently read bit.                       *)
(*                                                                            *)
(* bs: the input bits                                                         *)
(* -------------------------------------------------------------------------- *)
Definition run_recursive_parity_equation_def:
  run_recursive_parity_equation _ _ [] = [] ∧
  run_recursive_parity_equation 
End


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
  convolve_recursive_parity_equation TODO
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
  (decode_recursive_parity_equation rs) = 
Proof
QED



(* -------------------------------------------------------------------------- *)
(* Unit tests                                                                 *)
(* -------------------------------------------------------------------------- *)


Theorem convolve_recursive_parity_equation_unit_test:
  convolve_recursive_parity_equation ([1, 1, 0, 1], [1, 0, 0, 1]) _ F =
Proof
QED

(* -------------------------------------------------------------------------- *)
(* Test convolve_recursive_parity_equation when the first parity equation is  *)
(* longer than the second one                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem convolve_recursive_parity_equation_unit_test_first_long:

Proof
QED

(* -------------------------------------------------------------------------- *)
(* Test convolve_recursive_parity_equation when the second parity equation is *)
(* longer than the first one                                                  *)
(* -------------------------------------------------------------------------- *)
Theorem convolve_recursive_parity_equation_unit_test_second_long:

Proof
QED





val _ = export_theory();
