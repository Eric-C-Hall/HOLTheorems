open HolKernel Parse boolLib bossLib;

open parity_equationsTheory;

val _ = new_theory "recursive_parity_equations";

(* -------------------------------------------------------------------------- *)
(* Convolve .                                                                *)
(*                                                                            *)
(* The termination method used by this                                        *)
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
  convolve_recursive_parity_equation (ps, qs) bs f =
  ((apply_parity_equation ps bs) ⇎ f)
  :: convolve_recursive_parity_equation (ps, qs)
  
End



val _ = export_theory();
