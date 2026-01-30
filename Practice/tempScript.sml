Theory temp

Ancestors

Libs

Theorem drag_and_out_of_iff:
  ∀b1 b2 b3.
    (b1 ∧ b2 ⇔ b1 ∧ b3) ⇔ (b1 ⇒ (b2 ⇔ b3))
Proof
  rpt gen_tac
  >> Cases_on ‘b1’ >> simp[]
QED

Theorem temp1:
  ∀b1 b2 b3.
    ARB (b1 ∧ b2 ⇔ b1 ∧ b3)
Proof
  rpt gen_tac
  >> cong_tac (SOME 0)
  >> simp[drag_and_out_of_iff]
  >> strip_tac
QED
