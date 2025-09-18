(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory extreal_to_real

Ancestors arithmetic probability

Libs donotexpandLib map_decoderLib realLib dep_rewrite ConseqConv;

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
                     "extreal_pow_def"
                    ]
                   ),
                   ("extreal_to_real",
                    ["extreal_forall_cases"
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

Theorem extreal_to_real_test_case_1:
  ∀a b c d.
    a ≠ +∞ ∧ a ≠ −∞ ∧
    b ≠ +∞ ∧ b ≠ −∞ ∧
    c ≠ +∞ ∧ c ≠ −∞ ∧
    d ≠ +∞ ∧ d ≠ −∞ ⇒
    a + b = c * d : extreal
Proof
  gvs[SF EXTREAL_NORMFRAG_SS]
QED

