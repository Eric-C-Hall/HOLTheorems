(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory extreal_to_real

Ancestors arithmetic extreal real probability

Libs donotexpandLib realLib dep_rewrite ConseqConv;

val _ = hide "S";

(* Somehow make it faster, because expanding all the cases and then contracting
   them all again is slow. *)

Theorem extreal_forall_cases:
  ∀P.
    (∀x : extreal. P x) ⇔ (∀x' : real. P +∞ ∧ P −∞ ∧ P (Normal x'))
Proof
  rw[]
  >> EQ_TAC >> rw[]
  >> Cases_on ‘x’ >> metis_tac[]
QED
