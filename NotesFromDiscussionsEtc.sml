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


(* Model things in a mathematical way, not a computational way. e.g. don't use lists if what you really want to model is a function *)

(* term_grammar {} *)

(* EVAL ``3 + 4`` *)

(* SPEC_TAC is the opposite of gen_tac. It creates a forall in the goal, replacing an unbound variable. It's the opposite of gen_tac. Make sure the terms provided as input have the correct types, otherwise it won't work. *)

(* In general, when specifying terms, ensure everything has the correct type. That is why nowadays we use `...` instead of ``...`` *)

(* convolutional codes are linear non-block codes*)

(* free distance of convolutional codes may help when bounding number of errors correctable by them. *)

(* Often, induction needs to be done with a more general statement, with more forall quantifiers, because that improves the power of the inductive hypothesis at the cost of increasing the strength of the statement which needs to be proven. *)

val _ = export_theory();


