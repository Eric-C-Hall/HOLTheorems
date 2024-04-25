(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "thingsToDiscuss";

(* Theoretically it would be nice to have a functionality for simplifying
   polynomials. See for example proof of q2_sym_prob_correctly_decoded_prob
   at approximately "pop_assum DEP_ASSUME_TAC" *)

(* Wrote DEP_ASSUME_TAC. Given a theorem/assumption of the form
   a => b, this adds a subgoal to prove a, then adds b to the list
   of assumptions.
   
   Perhaps there was existing functionality that does the same thing? *)

open extrealTheory;
Theorem infiniteloop:
  (∀x : extreal. x pow 3 ≠ 0)∧
  3 = SUC 2 ⇒ F
Proof
  rpt strip_tac
  >> gvs[]
QED

(* Excl "SUC_DEF" doesn't work for preventing simplifying SUC *)
Theorem howtopreventsimplifyingSUC:
  ∀x. prime x ⇒ SUC (SUC 0) = x
Proof
  rpt strip_tac
  >> gvs[Excl "SUC_DEF"]
QED

(* What's an easy way to expand all constants (e.g. 7) out into a form
   containing repeated successors (e.g. SUC $ SUC $ SUC $ SUC $ SUC $
   SUC $ SUC 0) *)

(* It's nice how in HOL, you can write your own algorithms for proving things.
   For example, algorithm that generally works to simplify polynomials.
   Algorithm that generally works to prove a general expression in extreals
   where the extreals have finite values will have a finite value. *)

val _ = export_theory();


