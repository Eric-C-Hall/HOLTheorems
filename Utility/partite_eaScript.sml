open HolKernel Parse boolLib bossLib;

open useful_tacticsLib;
open dep_rewrite;
open fsgraphTheory;
open finite_mapTheory;
open pred_setTheory;

val _ = new_theory "partite_ea";

(* -------------------------------------------------------------------------- *)
(* A definition of a set which shows the partiteness of a graph by only using *)
(* one set to define the partition: we assume that the complement of this set *)
(* describes the remainder of the partition.                                  *)
(* -------------------------------------------------------------------------- *)
Definition gen_bipartite_ea_def:
  gen_bipartite_ea g A ⇔
    A ⊆ nodes g ∧
    ∀e. e ∈ fsgedges g ⇒ ∃n1 n2. e = {n1; n2} ∧ n1 ∈ A ∧ n2 ∉ A
End

(* -------------------------------------------------------------------------- *)
(* If a node is already in a graph, then adding it to the graph does not      *)
(* affect the graph                                                           *)
(* -------------------------------------------------------------------------- *)
Theorem fsgAddNode_in:
  ∀n g.
    n ∈ nodes g ⇒
    fsgAddNode n g = g
Proof
  rpt strip_tac
  >> gvs[fsgraph_component_equality]
  >> rw[INSERT_DEF, EXTENSION]
  >> EQ_TAC >> gvs[]
  >> Cases_on ‘x = n’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Any function shows that the empty graph is r-partite for any r             *)
(* -------------------------------------------------------------------------- *)
Theorem gen_bipartite_ea_empty[simp]:
  ∀r f.
    gen_bipartite_ea emptyG f ⇔ f = ∅
Proof
  rpt strip_tac
  >> gvs[gen_bipartite_ea_def]
QED

(* -------------------------------------------------------------------------- *)
(* Adding a new node to the graph maintains bipartiteness because it does not *)
(* have any edges that would constrain it to either being a part of or not    *)
(* being a part of the set defining the partition                             *)
(* -------------------------------------------------------------------------- *)
Theorem gen_bipartite_ea_fsgAddNode:
  ∀g n S.
    n ∉ S ⇒
    (gen_bipartite_ea (fsgAddNode n g) S ⇔ gen_bipartite_ea g S)
Proof
  rpt strip_tac
  >> EQ_TAC >> gvs[gen_bipartite_ea_def]
QED

val _ = export_theory();
