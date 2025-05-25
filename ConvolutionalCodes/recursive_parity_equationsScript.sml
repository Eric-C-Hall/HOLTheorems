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
(* - We expect the length of each parity equation to be one more than the     *)
(*   length of the current state. If they are shorter, then we treat them as  *)
(*   if they were padded with sufficiently many zeroes to bring them up to    *)
(*   the correct length (the padding occuring before the final 1-bit in the   *)
(*   case of the denominator). If they are longer, than we treat the state as *)
(*   if it were padded with sufficiently many zeroes to bring it up to the    *)
(*   correct length.                                                          *)
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
  run_recursive_parity_equation (ps, qs) ts (b::bs) =
  let
    feedback = apply_parity_equation (FRONT qs) ts;
    new_input = (feedback ⇎ b);
    state_and_input = ts ⧺ [new_input];
    current_output = apply_parity_equation ps state_and_input;
    next_ts = TL state_and_input;
  in
    [current_output] ⧺ run_recursive_parity_equation (ps, qs) next_ts bs
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
(* Note for testing: we expect that the parity equations and state are of     *)
(* the same length to each other, so there is no need to test situations in   *)
(* which this assumption does not hold, because they are outside the scope of *)
(* what the function needs to satisfy.                                        *)
(* -------------------------------------------------------------------------- *)



val _ = export_theory();
