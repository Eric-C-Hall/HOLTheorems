open HolKernel Parse boolLib bossLib;

open useful_tacticsLib;
open dep_rewrite;
open fsgraphTheory;
open finite_mapTheory;
open pred_setTheory;

val _ = new_theory "partite_ea";

val _ = hide "S"

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
(* Special case 1 of gen_bipartite_ea_fsgAddNode                              *)
(* -------------------------------------------------------------------------- *)
Theorem gen_bipartite_ea_fsgAddNode_special_case_1[local]:
  ∀g n S.
    n ∉ S ⇒
    (gen_bipartite_ea (fsgAddNode n g) S ⇔ gen_bipartite_ea g S)
Proof
  rpt strip_tac
  >> EQ_TAC >> gvs[gen_bipartite_ea_def]
QED

(* -------------------------------------------------------------------------- *)
(* Special case 2 of gen_bipartite_ea_fsgAddNode                              *)
(* -------------------------------------------------------------------------- *)
Theorem gen_bipartite_ea_fsgAddNode_special_case_2[local]:
  ∀g n S.
    n ∉ nodes g ⇒
    (gen_bipartite_ea (fsgAddNode n g) S ⇔ gen_bipartite_ea g (S DELETE n))
Proof
  rw[gen_bipartite_ea_def, EQ_IMP_THM]
    >>~- ([‘_ ⊆ _ (*g*)’], ASM_SET_TAC[])
  >> (first_assum drule
      >> dsimp[PULL_EXISTS, genericGraphTheory.INSERT2_lemma]
      >> rw[]
      >> (drule alledges_valid
          >> dsimp[PULL_EXISTS, genericGraphTheory.INSERT2_lemma]
         )
     )
QED

(* -------------------------------------------------------------------------- *)
(* Special case 3 of gen_bipartite_ea_fsgAddNode                              *)
(* -------------------------------------------------------------------------- *)
Theorem gen_bipartite_ea_fsgAddNode_special_case_3[local]:
  ∀g n S.
    n ∈ nodes g ⇒
    (gen_bipartite_ea (fsgAddNode n g) S ⇔ gen_bipartite_ea g S)
Proof
  gvs[fsgAddNode_in]
QED

(* -------------------------------------------------------------------------- *)
(* Adding a new node to the graph maintains bipartiteness because it does not *)
(* have any edges that would constrain it to either being a part of or not    *)
(* being a part of the set defining the partition.                            *)
(*                                                                            *)
(* In the case where n is already in G, then adding the node does nothing,    *)
(* so we can simply use the same partition S. We cannot delete n from S in    *)
(* this case, because it may have edges to nodes not in S.                    *)
(*                                                                            *)
(* In the case where we are adding n to G, then our partition S of the larger *)
(* graph may contain n, in which case it is not a partition of the smaller    *)
(* graph. However, S DELETE n will be a partition of the smaller graph in     *)
(* this case.                                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem gen_bipartite_ea_fsgAddNode:
  ∀g n S.
    gen_bipartite_ea (fsgAddNode n g) S ⇔
      gen_bipartite_ea g (if n ∈ nodes g then S else S DELETE n)
Proof
  rw[]
  >> simp[gen_bipartite_ea_fsgAddNode_special_case_2,
          gen_bipartite_ea_fsgAddNode_special_case_3]
QED

(* -------------------------------------------------------------------------- *)
(* This comes up a lot when dealing with edges, because they are treated as   *)
(* two-element sets.                                                          *)
(* -------------------------------------------------------------------------- *)
Theorem swap_edge: (* This is proven already: INSERT_COMM (more generality) *)
  ∀a b.
    {a;b} = {b;a}
Proof
  rpt strip_tac
  >> gvs[EXTENSION]
  >> rw[]
  >> gvs[DISJ_SYM]
QED

(* -------------------------------------------------------------------------- *)
(* An expression for partiteness with an element added into the partition     *)
(* set. Useful for induction as elements are added to the partition set.      *)
(* -------------------------------------------------------------------------- *)
Theorem gen_bipartite_ea_insert_new_node:
  ∀g n S.
    gen_bipartite_ea g S ∧
    n ∈ nodes g ∧
    (∀m. m ∈ nodes g
         ∧ m ∈ S  ⇒
         {n; m} ∉ fsgedges g) ⇒
    gen_bipartite_ea g (n INSERT S)
Proof
  rw[gen_bipartite_ea_def] >> gvs[gen_bipartite_ea_def]
  >> last_x_assum drule >> strip_tac
  >> Cases_on ‘n1 = n’ >> Cases_on ‘n2 = n’ >> gvs[]
  >- metis_tac[]
  >- metis_tac[SUBSET_DEF, swap_edge]
  >- metis_tac[]
QED

val _ = export_theory();
