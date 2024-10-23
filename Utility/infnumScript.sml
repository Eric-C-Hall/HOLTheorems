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

Definition insub_def[simp]:
  insub (N n) (N m) = N (n - m) ∧
  insub (N n) INFINITY = N0 ∧
  insub INFINITY (N m) = INFINITY ∧
  insub INFINITY INFINITY = ARB
End

Overload "-" = “insub”

Definition inlt_def[simp]:
  (inlt m INFINITY ⇔ m ≠ INFINITY) ∧
  (inlt INFINITY _ ⇔ F) ∧
  (inlt (N m) (N n) ⇔ m < n)
End

Overload "<" = “inlt”

Theorem inlt_REFL[simp]:
  ∀n : infnum.
    inlt n n ⇔ F
Proof
  Cases_on ‘n’>> simp[]
QED

Theorem inlt_TRANS:
  ∀n m p : infnum.
    inlt m n ∧ inlt n p ⇒ inlt m p
Proof
  rpt strip_tac
  >> Cases_on ‘m’ >> Cases_on ‘n’ >> Cases_on ‘p’ >> gvs[]
QED

Theorem inlt_trichotomy:
  ∀p q.
    inlt p q ∨ p = q ∨ inlt q p
Proof
  rpt strip_tac
  >> Cases_on ‘p’ >> Cases_on ‘q’ >> simp[]
QED

Theorem NZERO_LTZERO[simp]:
  ∀n.
    n ≠ N0 ⇔ inlt N0 n
Proof
  rpt strip_tac
  >> Cases_on ‘n’ >> simp[]
QED

Overload "<=" = “λin1 in2. ¬(inlt in2 in1)”

Definition infnum_to_num[simp]:
  infnum_to_num (N n) = n ∧
  infnum_to_num INFINITY = ARB
End

Theorem inlt_inle:
  ∀a b : infnum.
    a < b ⇒ a ≤ b
Proof
  rpt strip_tac
  >> Cases_on ‘a’ >> Cases_on ‘b’ >> gvs[]
QED

Theorem inlt_inlt_F:
  ∀a b : infnum.
    a < b ∧ b < a ⇒ F
Proof
  rpt strip_tac
  >> Cases_on ‘a’ >> Cases_on ‘b’ >> gvs[]
QED

Theorem inle_REFL[simp]:
  ∀a : infnum.
    a ≤ a
Proof
  Cases_on ‘a’ >> gvs[]
QED

Theorem inle_TRANS:
  ∀a b c : infnum.
    a ≤ b ∧ b ≤ c ⇒ a ≤ c
Proof
  Cases_on ‘a’ >> Cases_on ‘b’ >> Cases_on ‘c’ >> gvs[]
QED

Theorem inlte_TRANS:
  ∀a b c.
    a < b ∧ b ≤ c ⇒ a < c
Proof
  Cases_on ‘a’ >> Cases_on ‘b’ >> Cases_on ‘c’ >> gvs[]
QED

Theorem infnum_to_num_inplus:
  ∀i j.
    i ≠ INFINITY ∧
    j ≠ INFINITY ⇒
    infnum_to_num (i + j) = infnum_to_num i + infnum_to_num j
Proof
  rpt strip_tac
  >> Cases_on ‘i’ >> Cases_on ‘j’ >> gvs[]
QED

Theorem inplus_N_infinity[simp]:
  ∀i n.
    (i + N n = INFINITY) ⇔ (i = INFINITY)
Proof
  rpt strip_tac
  >> Cases_on ‘i’ >> gvs[]
QED

Theorem insub_id[simp]:
  ∀i.
    i ≠ INFINITY ⇒
    i - i = N0
Proof
  Cases_on ‘i’ >> gvs[]
QED

Theorem insub_N0[simp]:
  ∀i.
    i - N0 = i
Proof
  Cases_on ‘i’
  >> gvs[]
QED

Theorem inplus_insub[simp]:
  ∀i j.
    j ≠ INFINITY ⇒
    (i + j) - j  = i
Proof
  Cases_on ‘i’ >> Cases_on ‘j’ >> gvs[]
QED

Theorem insub_N_infinity[simp]:
  ∀i n.
    (i - N n = INFINITY) ⇔ (i = INFINITY)
Proof
  Cases_on ‘i’ >> gvs[]
QED

Theorem infnum_to_num_inplus:
  ∀i j.
    i ≠ INFINITY ∧
    j ≠ INFINITY ⇒
    infnum_to_num (i + j) = infnum_to_num i + infnum_to_num j
Proof
  rpt strip_tac
  >> Cases_on ‘i’ >> Cases_on ‘j’ >> gvs[]
QED

val _ = export_theory();
