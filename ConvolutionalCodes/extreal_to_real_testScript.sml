(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory extreal_to_real_test

Ancestors arithmetic extreal real probability

Libs extreal_to_realLib donotexpandLib realLib dep_rewrite ConseqConv;

val _ = hide "S";

Theorem extreal_to_real_test_case_1[local]:
  ∀a b : extreal.
    0 ≤ a ∧
    0 ≤ b ⇒
    (a + b) pow 2 = a pow 2 + 2 * a * b + b pow 2
Proof
  gvs[SF EXTREAL_NORMFRAG_SS]
  >> rw[SF EXTREAL_NORMFRAG_SS]
  (* First two goals *)
  >- metis_tac[REAL_NOT_LT, REAL_LE_ANTISYM]
  >- metis_tac[REAL_NOT_LT, REAL_LE_ANTISYM]
  (* Goal in the reals *)
  >> gvs[ADD_POW_2, AC REAL_ADD_SYM REAL_ADD_ASSOC]
QED

Theorem extreal_to_real_test_case_2[local]:
  ∀r. Normal r + +∞ = +∞
Proof
  gvs[SF EXTREAL_NORMFRAG_SS]
QED

Theorem extreal_to_real_test_case_3[local]:
  +∞ * +∞ = +∞
Proof
  gvs[SF EXTREAL_NORMFRAG_SS]
QED

Theorem extreal_to_real_test_case_4[local]:
  2 / 6 : extreal = Normal (100 / 300)
Proof
  gvs[SF EXTREAL_NORMFRAG_SS]
QED

Theorem extreal_to_real_practical_test_case_1[local]:
  ∀x y z.
    z ≠ 0 ∧
    z ≠ +∞ ∧
    z ≠ −∞ ⇒
    ((x / z = y / z) ⇔ x = y)
Proof
  gvs[SF EXTREAL_NORMFRAG_SS]
  >> rw[]
QED

Theorem extreal_to_real_practical_test_case_2[local]:
  ∀x y z.
    0 < z ∧ z ≠ +∞ ⇒
    (x / z ≤ y / z : extreal ⇔ x ≤ y)
Proof
  gvs[SF EXTREAL_NORMFRAG_SS]
QED

Definition practical_function_1_def[local]:
  practical_function_1 (p : extreal) qs =
  MAP (λq. (Normal 1 - p) * q + p * (Normal 1 - q)) qs
End

Theorem extreal_to_real_practical_test_case_3[local]:
  practical_function_1 (Normal 0.25) [Normal 1; Normal 0; Normal 1; Normal 0;
                                      Normal 0.5; Normal 0.25; Normal 0.75; Normal (1/3)]
  = [Normal 0.75; Normal 0.25; Normal 0.75; Normal 0.25;
     Normal 0.5; Normal (3/8); Normal (5/8); Normal (5/12)]
Proof
  gvs[SF EXTREAL_NORMFRAG_SS, practical_function_1_def]
QED
