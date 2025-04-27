(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "relevant";

(* What if, through a bug, a value gets duplicated and added to a partition twice, but the partition doesn't catch that error and claims that the result is valid because it doesn't allow duplicates? *)

(* It is interesting that set duplicate prevention makes it harder to define partitions in a way that allows for empty sets to be a part of the partition.*)

(* See messy usage of simplify_set_of_nonempty_if_no_nonempty inside gen_partite_gen_partite_ea. Is it possible to use this automatically as intended? *)

(* Would be cool to make wfmachine into its own type of well-formed machines, a la graphrep, graph, wfgraph *)

(* Should I go to the formal methods workshop *)

(* In this problem, it is common to represent functions with boolean inputs as lists of size 2: [falseValue, trueValue]. Thus, to apply the input F, we return falseValue, and to apply the input T, we return trueValue.

This is the typical representation when sending messages over the edges, although I am so far unaware of any typical representation for the functions within the nodes themselves.

I was thinking it might be possible to represent the function nodes in a similar way.

We could then flatten this out into a 1-dimensional list, so that it has a consistent type, and the type doesn't change depending on how many neighbours the function node has.*)

open arithmeticTheory pairTheory listTheory pred_setTheory sortingTheory
                      hurdUtils;

Theorem test:
  ∀v.
    FINITE (v DELETE ∅) ∧
    (ARB ⇒ (CARD (v DELETE ∅) * 1 = ARB)) ⇒ CARD (v DELETE ∅) = ARB
Proof
  rpt strip_tac
  >> gvs[]
QED

val _ = export_theory();
