(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory binary_symmetric_channel

Ancestors bitstring extreal

Libs realLib;

(* -------------------------------------------------------------------------- *)
(* A binary symmetric channel is fully defined by its probability of error.   *)
(*                                                                            *)
(* Thus, our binary symmetric channel is represented by a single extreal.     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Applies a binary symmetric channel to a given input.                       *)
(*                                                                            *)
(* p: the probability of an error                                             *)
(* qs: the input, as a list of extreals, where a given extreal represents the *)
(*     probability that the current bit has a value of 1.                     *)
(*                                                                            *)
(* Output: a list of extreals, representing the probability that the each bit *)
(*         has a value of 1 after applying the binary symmetric channel       *)
(* -------------------------------------------------------------------------- *)
Definition bsc_apply_def:
  bsc_apply (p : extreal) qs =
  MAP (λq. (Normal 1 - p) * q + p * (Normal 1 - q)) qs
End
           
(* -------------------------------------------------------------------------- *)
(* Determines the probability of changing the bitstring bs to the bitstring   *)
(* cs in a binary symmetric channel.                                          *)
(*                                                                            *)
(* In the case where bs and cs are of different sizes, we simply truncate     *)
(* the longer string so that it is of equal length to the shorter one.        *)
(* -------------------------------------------------------------------------- *)
Definition bsc_probability_def:
  bsc_probability p [] cs = Normal 1 ∧
  bsc_probability p (b::bs) [] = Normal 1 ∧
  bsc_probability (p : extreal) (b::bs) (c::cs) =
  (if b = c then Normal 1 - p else p) * bsc_probability p bs cs
End

(* -------------------------------------------------------------------------- *)
(* Unit tests                                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem bsc_apply_unit_test[local]:
  bsc_apply (Normal 0.25) [Normal 1; Normal 0; Normal 1; Normal 0;
                           Normal 0.5; Normal 0.25; Normal 0.75; Normal (1/3)]
  = [Normal 0.75; Normal 0.25; Normal 0.75; Normal 0.25;
     Normal 0.5; Normal (3/8); Normal (5/8); Normal (5/12)]
Proof
  gvs[extreal_add_eq,
      extreal_sub_eq,
      extreal_mul_eq,
      extreal_div_eq,
      bsc_apply_def]
QED
