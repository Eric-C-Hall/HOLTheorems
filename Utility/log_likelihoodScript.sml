open HolKernel Parse boolLib bossLib;

val _ = new_theory "log_likelihood";

open extrealTheory;

(* -------------------------------------------------------------------------- *)
(* Converts a probability into a log likelihood                               *)
(* -------------------------------------------------------------------------- *)
Definition log_likelihood_def:
  log_likelihood (e : extreal) = ln (e / (1 - e))
End

val _ = export_theory();
