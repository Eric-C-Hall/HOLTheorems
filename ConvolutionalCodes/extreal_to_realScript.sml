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

val NORMFRAG_SS = rewrites[extreal_add_eq,
                           extreal_sub_eq,
                           extreal_mul_eq,
                           extreal_div_eq,
                           extreal_pow_def
                          ];

val NORMFRAG2_SS = SSFRAG{NORMFRAG_SS with name = SOME "NORMFRAG"};

SF NORMFRAG_SS




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

Theorem gfdlkj:
  ∀a b c d.
    a ≠ +∞ ∧ a ≠ −∞ ∧
    b ≠ +∞ ∧ b ≠ −∞ ∧
    c ≠ +∞ ∧ c ≠ −∞ ∧
    d ≠ +∞ ∧ d ≠ −∞ ⇒
    a + b = c * d : extreal
Proof
  gvs[extreal_forall_cases]
     Cases_extreal
  >> gvs[]
        simplify_extreal
        gvs[foobar]
        Cases_on ‘a’
  >> Cases_on ‘b’
  >> Cases_on ‘c’
  >> Cases_on ‘d’
  >> gvs[extreal_mul_eq]
QED

