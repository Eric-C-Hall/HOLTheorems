(* Written by Eric Hall, under the guidance of Michael Norrish *)

structure extreal_to_realLib = struct

open HolKernel Parse boolLib bossLib;

open arithmeticTheory;
open extrealTheory;
open realTheory;
open probabilityTheory;

open extreal_to_realTheory;

open donotexpandLib;
open realLib;
open dep_rewrite;
open ConseqConv;

val _ = hide "S";

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
                   ),
                   ("probability",
                    ["PROB_FINITE"
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

end