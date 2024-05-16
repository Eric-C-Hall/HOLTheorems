(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "thingsToDiscuss";

(* I'm thinking that I should start writing my thesis proposal review.

   - Unsure if my topic is the correct one

   - Are there any example thesis proposal reviews?
 *)


(* Is there functionality for simplifying polynomials? *)

(* What specifically do you think it is important to work on? *)

(* How do I prevent simplifying SUC applied to a constant?
   Excl "SUC_DEF" doesn't work *)
Theorem howtopreventsimplifyingSUC:
  ∀x. prime x ⇒ SUC (SUC 0) = x
Proof
  rpt strip_tac
  >> gvs[Excl "SUC_DEF"]
QED

(* What's an easy way to expand all constants (e.g. 7) out into a form
   containing repeated successors (e.g. SUC $ SUC $ SUC $ SUC $ SUC $
   SUC $ SUC 0) *)


(* The following code results in an infinite loop *)
open extrealTheory;
Theorem infiniteloop:
  (∀x : extreal. x pow 3 ≠ 0)∧
  3 = SUC 2 ⇒ F
Proof
  rpt strip_tac
  >> gvs[]
QED

open realTheory

Theorem doesnotsimplify:
  3 - 1 - 1 - 1 = 0 : real
Proof
  gvs[]
  >> EVAL_TAC
QED

val _ = export_theory();


