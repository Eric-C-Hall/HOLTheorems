open HolKernel Parse boolLib bossLib;

open useful_tacticsLib;
open dep_rewrite;
open fsgraphTheory;
open finite_mapTheory;

val _ = new_theory "partite_ea";

(* -------------------------------------------------------------------------- *)
(* Gen partite: provides a specific partition which shows that a given graph  *)
(* is r-partite.                                                              *)
(*                                                                            *)
(* We represent a partition by a function which colours the nodes on the      *)
(* graph into at most r colours such that no two nodes of the same colour     *)
(* have an edge between them.                                                 *)
(*                                                                            *)
(* The previous verison of this definition required that every component of   *)
(* the partition was nonempty. This version doesn't have this requirement.    *)
(* It is easier to use the new version to prove things becauase you can avoid *)
(* performing additional work in the special case where there are empty sets  *)
(* in the partition.                                                          *)
(*                                                                            *)
(* It is no longer sensible to use a "set of sets" definition for the         *)
(* partition when empty components are allowed, because there may be multiple *)
(* empty components in the partition, and a set doesn't allow for duplicate   *)
(* components. Therefore, we changed the representation of a partition: we    *)
(* decided to represent it by a colouring function, rather than one of the    *)
(* other options.                                                             *)
(*                                                                            *)
(* See https://github.com/HOL-Theorem-Prover/HOL/issues/1465 for a detailed   *)
(* discussion of this change (this page has been archived on archive.org,     *)
(* although archive.org did not successfully archive the entire page).        *)
(* -------------------------------------------------------------------------- *)
Definition gen_partite_def :
  gen_partite r (g : fsgraph) (f : unit + num |-> num) <=>
  (∀m. m ∈ nodes g ⇒ f ' m < r) ∧
  (∀e. e ∈ fsgedges g ⇒ CARD (IMAGE ($' f) e) = 2)
End

(* -------------------------------------------------------------------------- *)
(* Gen bipartite: the special case of partite for r = 2                       *)
(*                                                                            *)
(* Using an overload instead of a definition minimizes the number of          *)
(* additional symbols defined and simplifies the process of proof: we only    *)
(* need to prove a theorem for gen_partite, and it will automatically also be *)
(* proven for gen_bipartite.                                                  *)
(* -------------------------------------------------------------------------- *)
Overload gen_bipartite = “gen_partite 2 g f”;

(* -------------------------------------------------------------------------- *)
(* Partite: when we only care that a partition exists, but we don't care what *)
(* the specific partition is                                                  *)
(* -------------------------------------------------------------------------- *)
Overload partite = “∃f. gen_partite r g f”;

(* -------------------------------------------------------------------------- *)
(* Bipartite: when we don't care what specific partition we use, and we are   *)
(* working with a graph that can be split into two components                 *)
(* -------------------------------------------------------------------------- *)
Overload bipartite = “∃f. gen_partite 2 g f”;

val _ = export_theory();
