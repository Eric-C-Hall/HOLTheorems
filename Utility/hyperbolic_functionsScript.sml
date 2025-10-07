Theory hyperbolic_functions

Ancestors extreal

(* -------------------------------------------------------------------------- *)
(* Euler's number                                                             *)
(* a.k.a. e                                                                   *)
(* i.e. the base of the natural logarithm.                                    *)
(*                                                                            *)
(* This may already be defined somewhere.                                     *)
(* -------------------------------------------------------------------------- *)
Definition eulers_number_def:
  eulers_number = exp(1) : real
End

Overload "𝑒" = “eulers_number”;

(* -------------------------------------------------------------------------- *)
(* Sinh for reals                                                             *)
(* -------------------------------------------------------------------------- *)
Definition sinh_def:
  sinh (r : real) = (exp r - exp (-r)) / 2
End

(* -------------------------------------------------------------------------- *)
(* Sinh for extreals                                                          *)
(* -------------------------------------------------------------------------- *)
Definition extsinh_def:
  extsinh (x : extreal) = case x of
                            +∞ => +∞
                          | −∞ => −∞
                          | Normal r => Normal (sinh r)
End

(* -------------------------------------------------------------------------- *)
(* Cosh for reals                                                             *)
(* -------------------------------------------------------------------------- *)
Definition cosh_def:
  cosh (r : real) = (exp r + exp (-r)) / 2
End

(* -------------------------------------------------------------------------- *)
(* Cosh for extreals                                                          *)
(* -------------------------------------------------------------------------- *)
Definition extcosh_def:
  extcosh (x : extreal) = case x of
                            +∞ => +∞
                          | −∞ => +∞
                          | Normal r => Normal (cosh r)
End

(* -------------------------------------------------------------------------- *)
(* Tanh for reals                                                             *)
(* -------------------------------------------------------------------------- *)
Definition tanh_def:
  tanh (r : real) = sinh r / cosh r
End

(* -------------------------------------------------------------------------- *)
(* Tanh for extreals                                                          *)
(*                                                                            *)
(* mlNeuralNetwork has a function called "tanh", but this is a function which *)
(* is written in ML and can be applied to values in the ML environment, but   *)
(* is not a HOL4 definition and thus cannot be used in HOL4 itself as an      *)
(* element of proofs and stuff. Furthermore, this definition of "tanh" is     *)
(* written for reals, and not for extreals.                                   *)
(* -------------------------------------------------------------------------- *)
Definition exttanh_def:
  exttanh (x : extreal) = extsinh x / extcosh x
End

(* -------------------------------------------------------------------------- *)
(* Arctanh for reals                                                          *)
(* -------------------------------------------------------------------------- *)
Definition arctanh_def:
  arctanh (r : real) = (ln ((1 + r) / (1 - r))) / 2
End

(* -------------------------------------------------------------------------- *)
(* Arctanh for extreals                                                       *)
(* -------------------------------------------------------------------------- *)
Definition extarctanh_def:
  extarctanh (x : extreal) = case x of
                               +∞ => ARB (* TODO: how should I handle
                                            undefined cases? *)
                             | −∞ => ARB 
                             | Normal r => Normal (arctanh r)
End
