(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "thingsToDiscuss";

(* Wrote DEP_ASSUME_TAC. Given a theorem/assumption of the form
   a => b, this adds a subgoal to prove a, then adds b to the list
   of assumptions.
   
   Perhaps there was existing functionality that does the same thing? *)

val _ = export_theory();


