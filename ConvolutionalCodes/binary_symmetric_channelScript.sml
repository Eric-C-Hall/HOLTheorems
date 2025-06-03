(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

open bitstringTheory;
open extrealTheory;

open realLib;

val _ = new_theory "binary_symmetric_channel";

(* -------------------------------------------------------------------------- *)
(* A binary symmetric channel is fully defined by its probability of error.   *)
(*                                                                            *)
(* Thus, our binary symmetric channel is represented by a single extreal.     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Applies a binary symmetric channel to a given input.                       *)
(*                                                                            *)
(* p: the probability of an error                                             *)
(* bs: the input, as a list of extreals, where a given extreal represents the *)
(*     probability that the current bit has a value of 1.                     *)
(*                                                                            *)
(* Output: a list of extreals, representing the probability that the each bit *)
(*         has a value of 1 after applying the binary symmetric channel       *)
(* -------------------------------------------------------------------------- *)
Definition bsc_apply_def:
  bsc_apply (p : extreal) bs =
  MAP (λb. (Normal 1 - p) * b + p * (Normal 1 - b)) bs
End

Theorem extreal_add_eq_simp[simp] = extreal_add_eq;
Theorem extreal_sub_eq_simp[simp] = extreal_sub_eq;
Theorem extreal_mul_eq_simp[simp] = extreal_mul_eq;
Theorem extreal_div_eq_simp[simp] = extreal_div_eq;

(* -------------------------------------------------------------------------- *)
(* Unit tests                                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem bsc_apply_unit_test[local]:
  bsc_apply (Normal 0.25) [Normal 1; Normal 0; Normal 1; Normal 0;
                           Normal 0.5; Normal 0.25; Normal 0.75; Normal (1/3)]
  = [Normal 0.75; Normal 0.25; Normal 0.75; Normal 0.25;
     Normal 0.5; Normal (3/8); Normal (5/8); Normal (5/12)]
Proof
  gvs[bsc_apply_def]
QED

val _ = export_theory();
