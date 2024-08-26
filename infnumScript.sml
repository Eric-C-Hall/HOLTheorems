open HolKernel Parse boolLib bossLib;

val _ = new_theory "infnum";

Datatype: infnum = INFINITY | N num
End

Overload "N0" = “N 0”
Overload "∞" = “INFINITY”

Definition inplus_def[simp]:
  inplus INFINITY n = INFINITY ∧
  inplus (N m) INFINITY = INFINITY ∧
  inplus (N m) (N n) = N (m + n)
End

Overload "+" = “inplus”

Theorem IN_ADD_RID[simp]:
  ∀n: infnum. n + N0 = n
Proof
  Cases >> simp[]
QED

Definition inlt_def[simp]:
  (inlt m INFINITY ⇔ m ≠ INFINITY) ∧
  (inlt INFINITY _ ⇔ F) ∧
  (inlt (N m) (N n) ⇔ m < n)
End

Overload "<" = “inlt”

Theorem inlt_REFL[simp]:
  inlt n n ⇔ F
Proof
  Cases_on ‘n’>> simp[]
QED

Theorem inlt_TRANS:
  inlt m n ∧ inlt n p ⇒ inlt m p
Proof
  Cases_on ‘m’ >> Cases_on ‘n’ >> Cases_on ‘p’ >> simp[]
QED

Theorem inlt_trichotomy:
  inlt p q ∨ p = q ∨ inlt q p
Proof
  Cases_on ‘p’ >> Cases_on ‘q’ >> simp[]
QED

Theorem NZERO_LTZERO[simp]:
  n ≠ N0 ⇔ inlt N0 n
Proof
  Cases_on ‘n’ >> simp[]
QED

Overload "<=" = “λin1 in2. ¬(inlt in2 in1)”

val _ = export_theory();
