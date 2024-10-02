(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "relevant";

(* thingsToDiscuss commits start on 15 Sep *)

(* How to use SPECL with generic types? *)

(* -------------------------------------------------------------------------- *)
(* How do I prevent SNOC from automatically simplifying?                      *)
(* I've tried using Excl "SNOC_APPEND", and the simplifier trace doesn't say  *)
(* what is causing SNOC to be transformed to an append.                       *)
(* -------------------------------------------------------------------------- *)
(*Theorem snoc_automatically_simplifying:
  ∀l ls.
  SNOC l ls = ARB
Proof
  gvs[Excl "SNOC_APPEND"]
  >> 
QED*)

(* It's probably a good idea to avoid state. *)

val _ = export_theory();
