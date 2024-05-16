(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "thingsToDiscuss";

(* HOL4 things to use:
   - realSimps
   - SCONV
   - ExclSF "REDUCE"
   - "INT_REDUCE"
   - CONV_TAC (REDEPTH_CONV numLib.num_CONV)  @@@ not sure if exactly right
   - numLib
   - SUC_TO_NUMERAL_DEFN_CONV
   - RADDCANON_SS
*)

(* HOL4 concepts:
   Numerals: numerals are represented using a system involving 1's and 2's.
   *)

(* Topics to research:
   - Mechanisation of probabilistic algorithms
   - Joe Hurd's PhD thesis on Mechanisation of Miller-Rabin test (Joe Leslie-Hurd)
   - Probabilistic programming
   - Aaron Coble theorem proving systems for probabilistic algorithms
   - Kozen 1997
   - 
*)

(* General advice:

   - Skim first, read more deeply later
*)


val _ = export_theory();


