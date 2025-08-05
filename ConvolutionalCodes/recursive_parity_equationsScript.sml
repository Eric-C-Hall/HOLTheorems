open HolKernel Parse boolLib bossLib;

(* HOL4 theories *)
open bitstringTheory;
open listTheory;
open rich_listTheory;

(* My theories *)
open parity_equationsTheory;
open state_machineTheory;
open wf_state_machineTheory;

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
(* This is more akin to the state machine view of applying a convolutional    *)
(* code than the view where you slide a window across the input. In           *)
(* particular, we keep track of the current state during computation, and we  *)
(* implicitly add zero-padding on the left by starting in state 0.            *)
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
Definition encode_recursive_parity_equation_def:
  encode_recursive_parity_equation _ _ [] = [] ∧
  encode_recursive_parity_equation (ps, qs) ts (b::bs) =
  let
    feedback = apply_parity_equation (FRONT qs) ts;
    new_input = (feedback ⇎ b);
    state_and_input = ts ⧺ [new_input];
    current_output = apply_parity_equation ps state_and_input;
    next_ts = TL state_and_input;
  in
    [current_output] ⧺ encode_recursive_parity_equation (ps, qs) next_ts bs
End

(* -------------------------------------------------------------------------- *)
(* A version of encode_recursive_parity_equation which also outputs the       *)
(* systematic bits                                                            *)
(* -------------------------------------------------------------------------- *)
(*Definition encode_recursive_parity_equation_with_systematic:
  encode_recursive_parity_equation_with_systematic (ps, qs) ts bs =
End*)

(* -------------------------------------------------------------------------- *)
(* The state that encode_recursive_parity_equation ends in after applying a   *)
(* given set of parity equations to a given input starting from a given state *)
(* -------------------------------------------------------------------------- *)
Definition encode_recursive_parity_equation_state_def:
  encode_recursive_parity_equation_state _ ts [] = ts ∧
  encode_recursive_parity_equation_state (ps, qs) ts (b::bs) =
  let
    feedback = apply_parity_equation (FRONT qs) ts;
    new_input = (feedback ⇎ b);
    state_and_input = ts ⧺ [new_input];
    next_ts = TL state_and_input;
  in
    encode_recursive_parity_equation_state (ps, qs) next_ts bs
End
                                         
(* -------------------------------------------------------------------------- *)
(* Convert parity-equation expression of recursive convolutional codes into   *)
(* a state-machine format.                                                    *)
(*                                                                            *)
(* Includes the systematic bits.                                              *)
(* -------------------------------------------------------------------------- *)
Definition recursive_parity_equations_to_state_machine_def:
  recursive_parity_equations_to_state_machine (ps, qs) =
   let
     state_length = (MAX (LENGTH ps) (LENGTH qs)) - 1;
   in
     wf_state_machine_ABS <|
       num_states := 2 ** state_length;
       transition_fn :=
       λ(s, b).
         let
           s_vec = zero_extend state_length (n2v s);
           feedback = apply_parity_equation (FRONT qs) s_vec;
           new_input = (feedback ⇎ b);
           window = s_vec ⧺ [new_input];
           new_vec = TL (window);
         in
           (v2n new_vec, apply_parity_equations ps window)
       ;
       output_length := 1;
     |>
End

(* -------------------------------------------------------------------------- *)
(* Encodes a recursive parity equation using zero-tail termination.           *)
(*                                                                            *)
(* First, encodes as usual up until the end of the input string.              *)
(*                                                                            *)
(* Then, applies encoding without feedback on the state resulting from this   *)
(* encoding.                                                                  *)
(* -------------------------------------------------------------------------- *)
Definition encode_recursive_parity_equation_zero_tailed_def:
  encode_recursive_parity_equation_zero_tailed (ps, qs) ts bs =
  encode_recursive_parity_equation (ps, qs) ts bs ++
  convolve_parity_equations
  [ps] (encode_recursive_parity_equation_state (ps, qs) ts bs)
End

(* -------------------------------------------------------------------------- *)
(* A well-formed recursive convolutional code always has a "1" in the         *)
(* denominator in the bit which corresponds to the current input, because the *)
(* current input + feedback always has to take into account the current input.*)
(* As such, in this implementation, the last bit of the denominator is        *)
(* ignored and assumed to be 1.                                               *)
(* -------------------------------------------------------------------------- *)
Theorem denominator_last_one_equiv[simp]:
  ∀ps qs ts bs.
    encode_recursive_parity_equation (ps, qs ⧺ [F]) ts bs =
    encode_recursive_parity_equation (ps, qs ⧺ [T]) ts bs
Proof
  Induct_on ‘bs’ >> rw[encode_recursive_parity_equation_def, FRONT_APPEND]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Encode the recursive parity equation in a way which is sensible, in  *)
(* particular with regards to the ininitialization and termination schemes    *)
(*                                                                            *)
(* TODO: In particular, this should be the counterpart to                     *)
(* decode_recursive_parity_equation                                           *)
(* -------------------------------------------------------------------------- *)
(*Definition encode_recursive_parity_equation_def:
  encode_recursive_parity_equation rs bs =
  convolve_recursive_parity_equation ARB
End*)

(* -------------------------------------------------------------------------- *)
(* TODO: Decode a recursive parity equation encoded by                        *)
(* encode_recursive_parity_equation                                           *)
(* -------------------------------------------------------------------------- *)
(*Definition decode_recursive_parity_equation_def:
  decode_recursive_parity_equation rs bs = ARB
End*)

(* -------------------------------------------------------------------------- *)
(* Encoding and decoding a recursive parity equation using the BCJR algorithm *)
(* will return the original data again                                        *)
(*                                                                            *)
(* TODO: Main encoding/decoding theorom for recursive parity equations        *)
(* -------------------------------------------------------------------------- *)
(*Theorem encode_decode_recursive_parity_equation:
  (encode_recursive_parity_equation rs) ∘
  (decode_recursive_parity_equation rs) = I
Proof
QED*)

(* -------------------------------------------------------------------------- *)
(* Ensure that the decoding procedure for a recursive parity equation encoder *)
(* implements an a posteriori encoder (TODO: check that I have my terminology *)
(* correct)                                                                   *)
(*                                                                            *)
(* TODO: implement this                                                       *)
(* -------------------------------------------------------------------------- *)
(*Theorem decode_recursive_parity_equation_a_posteriori:
  (decode_recursive_parity_equation rs) = 
Proof
QED*)

(* -------------------------------------------------------------------------- *)
(* The length of a recursive parity equation                                  *)
(* -------------------------------------------------------------------------- *)
Theorem encode_recursive_parity_equation_length[simp]:
  ∀ps qs ts bs.
    LENGTH (encode_recursive_parity_equation (ps, qs) ts bs) = LENGTH bs
Proof
  Induct_on ‘bs’ >> rw[encode_recursive_parity_equation_def]
QED

(* -------------------------------------------------------------------------- *)
(* An expression for the result of encoding the concatenation of two strings  *)
(* -------------------------------------------------------------------------- *)
Theorem encode_recursive_parity_equation_append:
  ∀ps qs ts bs cs.
    encode_recursive_parity_equation (ps, qs) ts (bs ++ cs) =
    encode_recursive_parity_equation (ps, qs) ts bs ++
    encode_recursive_parity_equation
    (ps, qs)
    (encode_recursive_parity_equation_state (ps, qs) ts bs)
    cs
Proof
  Induct_on ‘bs’ >> rw[encode_recursive_parity_equation_def,
                       encode_recursive_parity_equation_state_def]
QED

Theorem encode_recursive_parity_equation_state_length[simp]:
  ∀ps qs ts bs.
    LENGTH (encode_recursive_parity_equation_state (ps,qs) ts bs) = LENGTH ts
Proof
  Induct_on ‘bs’ >> gvs[encode_recursive_parity_equation_state_def]
  >> gvs[LENGTH_TL]
QED

(* -------------------------------------------------------------------------- *)
(* Unit tests                                                                 *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Numerator: [T,T,F,T]                                                       *)
(* Denominator: [T,F,F,T]                                                     *)
(* Initial state: [F,F,F]                                                     *)
(* Input: [T,T,T,T,F,F,F,F,T,F]                                               *)
(*                                                                            *)
(* State     | State with feedback | Output                                   *)
(* [F,F,F,T] | [F,F,F,T]           | T                                        *)
(* [F,F,T,T] | [F,F,T,T]           | T                                        *)
(* [F,T,T,T] | [F,T,T,T]           | F                                        *)
(* [T,T,T,T] | [T,T,T,F]           | F                                        *)
(* [T,T,F,F] | [T,T,F,T]           | T                                        *)
(* [T,F,T,F] | [T,F,T,T]           | F                                        *)
(* [F,T,T,F] | [F,T,T,F]           | T                                        *)
(* [T,T,F,F] | [T,T,F,T]           | T                                        *)
(* [T,F,T,T] | [T,F,T,F]           | T                                        *)
(* [F,T,F,F] | [F,T,F,F]           | T                                        *)
(* -------------------------------------------------------------------------- *)
Theorem fun_recursive_parity_equation_unit_test:
  encode_recursive_parity_equation
  ([T;T;F;T], [T;F;F;T]) [F;F;F] [T;T;T;T;F;F;F;F;T;F] =
  [T;T;F;F;T;F;T;T;T;T]
Proof
  gvs[encode_recursive_parity_equation_def, apply_parity_equation_def]
QED

(* -------------------------------------------------------------------------- *)
(* Note for testing: we expect that the parity equations and state are of     *)
(* the same length to each other, so there is no need to test situations in   *)
(* which this assumption does not hold, because they are outside the scope of *)
(* what the function needs to satisfy.                                        *)
(* -------------------------------------------------------------------------- *)

val _ = export_theory();
