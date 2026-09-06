Theory argmax_bool

Ancestors extreal real probability

Libs dep_rewrite realLib;

(* -------------------------------------------------------------------------- *)
(* Choose the value of a bit which maximizes the value of an extreal-valued   *)
(* function.                                                                  *)
(*                                                                            *)
(* f: the function to maximize (bool -> extreal)                              *)
(* Output: the choice of bit which maximize that function                     *)
(* -------------------------------------------------------------------------- *)
Definition argmax_bool_def:
  argmax_bool f = (f F ≤ f T : extreal)
End

(* -------------------------------------------------------------------------- *)
(* Similar to ldiv_le_imp                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem ldiv_le_iff:
  ∀x y z.
    0 < z ∧ z ≠ +∞ ⇒
    (x / z ≤ y / z : extreal ⇔ x ≤ y)
Proof
  rw[]
  >> REVERSE EQ_TAC >- metis_tac[ldiv_le_imp]
  >> Cases_on ‘x’ >> Cases_on ‘y’ >> Cases_on ‘z’
  >> gvs[infty_div, le_infty, extreal_div_eq, REAL_POS_NZ]
QED

(* -------------------------------------------------------------------------- *)
(* A division by a constant within an argmax_bool can be cancelled out        *)
(* -------------------------------------------------------------------------- *)
Theorem argmax_bool_div:
  ∀P c.
    0 < c ∧
    c ≠ +∞ ⇒
    argmax_bool (λb. P b / c) = argmax_bool P
Proof
  rw[]
  >> gvs[argmax_bool_def]
  >> gvs[ldiv_le_iff]
QED

Theorem argmax_bool_mul_const:
  ∀f g c.
    0 < c ∧
    c ≠ +∞ ∧
    (g = λx. c * f x)
    ⇒ (argmax_bool f ⇔ argmax_bool g)
Proof
  rw[]
  >> gvs[argmax_bool_def]
  >> gvs[le_lmul]
QED
