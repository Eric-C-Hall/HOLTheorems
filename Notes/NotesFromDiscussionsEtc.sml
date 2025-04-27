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

(* Induct_on PERM
   Induct_on `bs` using SNOC_INDUCT *)

(* GSYM *)

(* WF_REL_TAC `measure (LENGTH o SND)`
*)

(* Lib *)

(* POP_ASSUM_LIST*)

(* assum_list *)

(* Meta-; is the hotkey for commenting/uncommenting a region *)

(* SNOC_CASES *)

(* transition_origin_component_equality *)

(* Ctrl-x 1 to make window the only window, ctrl-x 0 to get rid of the window *)

(* gnvs avoids splitting on disjuncts *)

(* LIST_CONJ <- connects theorems in list with conjunctions *)

(* avoid writing an excessive number of new definitions. Do not unnecessarily multiply entities *)

(* In order to have more detail on the simplifier, use:
   set_trace "simplifier" 6
   this in particular is a high enough level to trace conversions *)

(* LIST_EQ_SIMP_CONV is what is reducing SNOC to APPEND. TODO: perhaps this shouldn't be included in the simpset *)

(* Function for deduplicating lists: nub *)

(* Be careful about including conditional rewrites in simp rules, beacause they
   require the simplifier to do extra, possibly useless work every time they
   see the LHS *)

val _ = export_theory();


