(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory extreal_to_real

Ancestors arithmetic extreal real probability

Libs donotexpandLib realLib dep_rewrite ConseqConv;

val _ = hide "S";

Theorem extreal_forall_cases:
  ∀P.
    (∀x : extreal. P x) ⇔ (∀x' : real. P +∞ ∧ P −∞ ∧ P (Normal x'))
Proof
  rw[]
  >> EQ_TAC >> rw[]
  >> Cases_on ‘x’ >> metis_tac[]
QED

val EXTREAL_NORMFRAG_SS =
SSFRAG
{
name = SOME"EXTREAL_NORMFRAG",
ac = [],
congs = [],
convs = [],
dprocs = [],
filter = NONE,
rewrs = List.concat
            (map (fn (thy, th_names) =>
                    map (fn name =>
                           (SOME{Thy = thy, Name = name}, DB.fetch thy name)
                        ) th_names
                 )
                 [
                   ("extreal",
                    ["extreal_add_eq",
                     "extreal_sub_eq",
                     "extreal_mul_eq",
                     "extreal_div_eq",
                     "extreal_add_def",
                     "extreal_sub_def",
                     "extreal_mul_def",
                     "extreal_div_def",
                     "extreal_pow_def",
                     "extreal_inv_eq",
                     "extreal_of_num_def"
                    ]
                   ),
                   ("extreal_to_real",
                    ["extreal_forall_cases"
                    ]
                   ),
                   ("real",
                    ["REAL_LT_IMP_NE" (* Helpful for proving that a
                                         denominator is not zero, but also risks
                                         an explosion in things that need to be
                                         proven *)
                    ]
                   )
                 ]
            )
};

(* This is a tactic which splits the current proof state according to all
   extreal terms.

   Parse the conclusion, and 
 *)
(*val Cases_extreal = (fn (g : goal) =>
                        let
val extreal_term_quotations = [‘a’, ‘b’, ‘c’, ‘d’]
                        in
                          (EVERY (map Cases_on extreal_term_quotations)) g
                                                                         end
                    );

val simplify_extreal = Cases_extreal >>
gvs[] >>
gvs[extreal_add_def,
    extreal_sub_def,
    extreal_mul_def,
    extreal_div_def,
    extreal_pow_def]
>> rw[]*)

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

