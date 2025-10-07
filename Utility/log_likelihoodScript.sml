Theory log_likelihood

Ancestors extreal

(* -------------------------------------------------------------------------- *)
(* Converts a probability into a log likelihood                               *)
(* -------------------------------------------------------------------------- *)
Definition log_likelihood_def:
  log_likelihood (e : extreal) = ln (e / (1 - e))
End
