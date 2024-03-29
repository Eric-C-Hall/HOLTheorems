(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "thingsToDiscuss";

(* The term cannot be contrained to be of type *)
Theorem termCannotBeConstrained:
  (∀x : α. [x] = []) ⇒
  ∀y : num. [y] = []
Proof
  rpt strip_tac
  >> pop_assum $ qspec_then ‘y’ assume_tac
QED


val _ = export_theory();

