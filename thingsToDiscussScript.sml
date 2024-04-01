(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "thingsToDiscuss";

(* -------------------------------------------------------------------------- *)

(* qspec_then does not allow instantiating variables of an abstract type with *)
(* variables of a specific type. It says "term cannot be constrained"         *)
Theorem termCannotBeConstrained:
  (∀x : α. [x] = []) ⇒
  ∀y : num. [y] = []
Proof
  rpt strip_tac
  >> pop_assum $ qspec_then ‘y’ assume_tac
QED

(* -------------------------------------------------------------------------- *)
(* What specifically allows you to temporarily ignore an assumption in calls  *)
(* to gvs, etc                                                                *)
(* -------------------------------------------------------------------------- *)



(* -------------------------------------------------------------------------- *)
(* How to add an existing theorem to the simpset. e.g. I don't think          *)
(* MODEQ_REFL is in the simpset. It also has the issue that the variable n    *)
(* isn't bound by a quantifier.                                               *)
(* -------------------------------------------------------------------------- *)


val _ = export_theory();

