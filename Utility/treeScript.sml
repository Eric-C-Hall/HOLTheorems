Theory tree

Ancestors arithmetic extreal fsgraph fundamental genericGraph list pred_set rich_list

Libs dep_rewrite ConseqConv;

(* -------------------------------------------------------------------------- *)
(* True iff g is a tree.                                                      *)
(* -------------------------------------------------------------------------- *)
Definition is_tree_def:
  is_tree g ⇔ (connected g ∧
               (∀ns. ¬cycle g ns))
End

(* -------------------------------------------------------------------------- *)
(* Chooses a path between two nodes in a graph.                               *)
(*                                                                            *)
(* This is more useful in the case of a tree, because in a tree, a path       *)
(* always exists and it is unique, so the choice function always returns the  *)
(* same value.                                                                *)
(* -------------------------------------------------------------------------- *)
Definition get_path_def:
  get_path g org dest = (@vs. path g vs ∧ HD vs = org ∧ LAST vs = dest)
End

(* -------------------------------------------------------------------------- *)
(* Finds the ith parent of a node in a tree                                   *)
(*                                                                            *)
(* g: the graph (must be a tree)                                              *)
(* root: the root node of the tree. This defines the most ancestral point in  *)
(*       the tree, which induces an ordering on its children: this ensures    *)
(*       it is well-defined to ask which nodes are ancestors/descendants of   *)
(*       other nodes.                                                         *)
(* n: the node to find the ith parent on                                      *)
(* i: the number i to find the ith parent of (I avoided n to avoid confusion  *)
(*    with the node, which has label n for node)                              *)
(*                                                                            *)
(* Returns: the ith parent. If the ith parent doesn't exist, we have          *)
(*          undefined behaviour. (perhaps we could modify this definition to  *)
(*          have a specific output, e.g. the root, in this case)              *)
(* -------------------------------------------------------------------------- *)
Definition ith_parent_def:
  ith_parent g root n i = EL i (get_path g n root)
End

(* -------------------------------------------------------------------------- *)
(* Tests if a given node is an ancestor of another node in a tree.            *)
(* This includes if the two nodes are equal.                                  *)
(*                                                                            *)
(* g: the graph (must be a tree)                                              *)
(* root: the root node of the tree. This defines the most ancestral point in  *)
(*       the tree, which induces an ordering on its children: this ensures    *)
(*       it is well-defined to ask which nodes are ancestors/descendants of   *)
(*       other nodes.                                                         *)
(* anc: the node we are testing to see if it is an ancestor of the descendant *)
(*      node                                                                  *)
(* desc: the node we are testing to see if it is a descendant of the ancestor *)
(*       node                                                                 *)
(* -------------------------------------------------------------------------- *)
Definition is_ancestor_def:
  is_ancestor g root anc desc ⇔
    (∃i. ith_parent g root desc i = anc)
End

(* -------------------------------------------------------------------------- *)
(* Takes a particular subgraph of a given graph, which has the given          *)
(* selection of nodes                                                         *)
(* -------------------------------------------------------------------------- *)
Definition subgraph_def:
  subgraph (g : fsgraph) nodes =
  fsgAddEdges
  ({add_edge | add_edge ∈ fsgedges g ∧
               (∀edge_node. edge_node ∈ add_edge ⇒
                            edge_node ∈ nodes )})
  (fsgAddNodes
   nodes
   emptyG
  )
End

(* -------------------------------------------------------------------------- *)
(* Finds the subtree of all nodes that are descendants of node n, including   *)
(* the node n itself.                                                         *)
(*                                                                            *)
(* g: the graph (must be a tree)                                              *)
(* root: the root node of the tree. This defines the most ancestral point in  *)
(*       the tree, which induces an ordering on its children: this ensures    *)
(*       it is well-defined to ask which nodes are ancestors/descendants of   *)
(*       other nodes                                                          *)
(* n: the node are finding the subtree from                                   *)
(* Only valid if our initial graph is a tree.                                 *)
(* -------------------------------------------------------------------------- *)
Definition subtree_def:
  subtree (g : fsgraph) root n =
  subgraph g (nodes g ∩ {v | MEM n (get_path g root v)})
End

(* -------------------------------------------------------------------------- *)
(* Returns the distance between two nodes in a graph                          *)
(* -------------------------------------------------------------------------- *)
Definition distance_def:
  distance (g : fsgraph) v1 v2 = MAX_SET (IMAGE LENGTH {vs | path g vs ∧
                                                             HD vs = v1 ∧
                                                             LAST vs = v2})
End

(* -------------------------------------------------------------------------- *)
(* Returns the diameter of a graph                                            *)
(* -------------------------------------------------------------------------- *)
Definition diameter_def:
  diameter (g : fsgraph) = MAX_SET (IMAGE (UNCURRY (distance g))
                                          {(v1,v2) | v1 ∈ nodes g ∧
                                                     v2 ∈ nodes g}
                                   )
End

(* -------------------------------------------------------------------------- *)
(* Returns the eccentricity of a node in a graph.                             *)
(* -------------------------------------------------------------------------- *)
Definition eccentricity_def:
  eccentricity (g : fsgraph) n = MAX_SET (IMAGE (distance g n) (nodes g))
End

(* -------------------------------------------------------------------------- *)
(* A path in a tree between two nodes is unique.                              *)
(*                                                                            *)
(* Suppose, by way of contradiction, we had two paths                         *)
(*                                                                            *)
(* Since each path starts at the same location but the paths are not          *)
(* identical, there must be an index i at which EL i vs1 = EL i vs2 but we    *)
(* don't have EL (i + 1) vs1 = EL (i + 1) vs2.                                *)
(*                                                                            *)
(* Choose the next indices j and k after i + 1 at which EL j vs1 = EL k vs2   *)
(* but we don't have EL (j - 1) vs1 = EL (k - 1) vs2. This must exist because *)
(* the goal is identical for each path.                                       *)
(*                                                                            *)
(* Then taking vs1 from i to j followed by taking vs2 from j to i will        *)
(* provide a cycle in our graph.                                              *)
(*                                                                            *)
(* This contradicts the fact that we have a tree, because a tree has no       *)
(* cycles                                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem tree_path_unique:
  ∀g a b vs1 vs2.
    is_tree g ∧
    path g vs1 ∧
    HD vs1 = a ∧
    LAST vs1 = b ∧
    path g vs2 ∧
    HD vs2 = a ∧
    LAST vs2 = b ⇒
    vs1 = vs2
Proof

  rpt strip_tac
  (* We work by way of contradiction, assuming that there are two nonequal paths
     that have the same start and end points *)
  >> CCONTR_TAC
  (* It is convenient to separately treat the special case where our start and
     goal nodes are identical. This makes it easier to prove the base case of
     our induction. *)
  >> Cases_on ‘a = b’
  >- (gvs[]
      >> Cases_on ‘vs1’ >> Cases_on ‘vs2’ >> gvs[]
      >> Cases_on ‘t’ >> Cases_on ‘t'’ >> gvs[]
     )
  (* Prove that there is a point at which the paths diverge *)
  >> sg ‘∃i. EL i vs1 = EL i vs2 ∧
             EL (i + 1) vs1 ≠ EL (i + 1) vs2 ∧
             i + 1 ≤ LENGTH vs1 - 1 ∧
             i + 1 ≤ LENGTH vs2 - 1’
  >- (rpt $ pop_assum mp_tac
      (* Induct over each list *)
      >> SPEC_ALL_TAC
      >> Induct_on ‘vs1’ >> gvs[]
      >> rpt strip_tac
      >> namedCases_on ‘vs2’ ["", "v vs2"] >> gvs[]
      (* Apply the inductive hypothesis to the appropriate values *)
      >> last_x_assum $ qspecl_then [‘g’, ‘vs2'’] assume_tac
      (* Split up the statement about how the new path v::vs1 is a path into a
         statement about how the smaller path vs1 is a path, in order to apply
         the inductive hypothesis *)
      >> gvs[path_cons]
      (* Split up the statement about how the last element of the new path
        v::vs1 is the last element of the path v::vs2' into a statement about
        the last elements of the smaller paths, so that we may satisfy that
        condition of the inductive hypothesis. We need to check that vs1 and
        vs2' are not the empty set in order to do this. *)
      >> gvs[LAST_DEF]
      >> namedCases_on ‘vs1’ ["", "v vs1"] >> gvs[]
      >> namedCases_on ‘vs2'’ ["", "v' vs2"] >> gvs[]
      (* If the second elements are nonequal, then we can choose this as our
         choice of i. Otherwise, we have satisfied another condition of the
         inductive hypothesis. *)
      >> REVERSE $ Cases_on ‘v' = v''’
      >- (qexists ‘0’ >> gvs[])
      >> gvs[]
      (* Prove the last condition of the inductive hypothesis *)
      >> Cases_on ‘v' = LAST (v'::vs1')’
      >- (namedCases_on ‘vs1'’ ["", "v vs1"] >> gvs[]
          >> namedCases_on ‘vs2’ ["", "v vs2"] >> gvs[]
         )
      >> gvs[]
      (* Simplify EL (i + 1) (_::_) *)
      >> gvs[GSYM ADD1]
      (* If the inductive hypothesis holds by choosing i, then the next step
         holds by choosing i + 1 *)
      >> qexists ‘i + 1’
      (* Simplify EL (i + 1) (_::_) *)
      >> gvs[GSYM ADD1]
     )
  (* Prove that there is a point after the paths diverge at which the paths
     converge. At every point in the meantime, the paths have been entirely
     distinct.
.
     We prove this by strong induction on the length of vs2.
.
     Our inductive hypothesis is that for any vs2 of a lesser size, if the last
     elements are the same and the first elements are the same and there is a
     split at i, then there exists a convergence point after i.
.
     Now we are given vs2. If there is any pair of identical elements before the
     very end of vs2, then we can use the inductive hypothesis to solve.
     Otherwise, there's a convergence point at the very end, and all the
     elements up to that point are distinct *)
  >> sg ‘∃j k. i + 1 ≤ j ∧
               i + 1 ≤ k ∧
               j ≤ LENGTH vs1 - 1 ∧
               k ≤ LENGTH vs2 - 1 ∧
               (∀l m.
                  i + 1 ≤ l ∧
                  i + 1 ≤ m ∧
                  l ≤ j - 1 ∧
                  m ≤ k - 1 ⇒
                  EL l vs1 ≠ EL m vs2) ∧
               EL j vs1 = EL k vs2’        
  >- (‘∃l. LENGTH vs2 = l’ by simp[]
      >> rpt (pop_assum mp_tac) >> SPEC_ALL_TAC
      >> completeInduct_on ‘l’
      >> rpt strip_tac
      (* If there are identical elements before the end of vs2, we use the
         inductive hypothesis to solve *)
      >> Cases_on ‘∃x y. i + 1 ≤ x ∧
                         i + 1 ≤ y ∧
                         x ≤ LENGTH vs1 - 1 ∧
                         y ≤ LENGTH vs2 - 2 ∧
                         EL x vs1 = EL y vs2’
      >- (gvs[]
          (* Specify the appropriate variables to use the inductive hypothesis *)
          >> last_x_assum $ qspecl_then [‘y + 1’] assume_tac
          >> gvs[]
          >> last_x_assum (qspecl_then
                           [‘g’, ‘i’, ‘TAKE (x + 1) vs1’, ‘TAKE (y + 1) vs2’]
                           assume_tac)
          >> gvs[]
          >> gvs[HD_TAKE]
          >> gvs[LAST_TAKE]
          >> gvs[EL_TAKE]
          (* We need to know that the substrings the inductive hypothesis was
             applied to aren't equal. This follows from the fact that i was a
             divergence point, and so they differ at i + 1 *)
          >> sg ‘TAKE (x + 1) vs1 ≠ TAKE (y + 1) vs2’
          >- (gvs[LIST_EQ_REWRITE]
              >> rw[]
              >> qexists ‘i + 1’
              >> gvs[]
              >> gvs[EL_TAKE]
             )
          >> gvs[]
          (* Because all the elements of vs1 are distinct, and the convergence
             point y is the same in vs1 and vs2, we know that the head of vs1 is
             not equal to the convergence point *)
          >> sg ‘HD vs1 ≠ EL y vs2’
          >- (qpat_x_assum ‘EL x vs1 = EL y vs2’ (fn th => gvs[GSYM th])
              >> gvs[path_def]
              >> PURE_ONCE_REWRITE_TAC[GSYM EL]
              >> gvs[ALL_DISTINCT_EL_IMP]
             )
          >> gvs[]
          (* Use the j and k returned by the inductive hypothesis to prove the
             inductive step *)
          >> qexistsl [‘j’, ‘k’]
          >> gvs[EL_TAKE]
         )
      >> last_x_assum kall_tac (* We no longer need the inductive hyp, and it's
                                  laggy for the simplifier to constantly try to
                                  use it. *)
      >> gvs[]
      (* We now know that anywhere on vs1 after the divergence point is not
         equal to anywhere on vs2 after the divergence point and before the end
         (not including the end).
.
        Therefore, the convergence point is at the very end of vs2. However, it
        is not necessarily at the very end of vs1.
.
        Choose the earliest point after the divergence point where vs1 is equal
        to the very end of vs2.
       *)
      >> sg ‘∃j.
               i + 1 ≤ j ∧
               j ≤ LENGTH vs1 - 1 ∧
               (∀l. i + 1 ≤ l ∧ l ≤ j - 1 ⇒ EL l vs1 ≠ LAST vs2) ∧
               EL j vs1 = LAST vs2’
      >- (all_tac
          (* Remove all assumptions but the following assumptions, because if
             we have unnecessary assumptions, we need to prove them in our
             induction *)
          >> qpat_x_assum ‘LAST vs2 = LAST vs1’ mp_tac
          >> qpat_x_assum ‘i + 1 ≤ LENGTH vs1 - 1’ mp_tac
          >> rpt (pop_assum kall_tac) >> rpt strip_tac
          (* vs2 isn't mentioned elsewhere, so we can remove an unnecessary
             assumption. *)
          >> qpat_x_assum ‘LAST vs2 = LAST vs1’ (fn th => PURE_REWRITE_TAC[th])
          (* Specialise all variables so we have a stronger inductive
             hypothesis *)
          (*>> rpt $ pop_assum mp_tac >> SPEC_ALL_TAC*)
          (* Induct on vs1. In the base case, if the (i + 1)th element is the
             last element, then we can simply choose this element as our
             convergence point j. Otherwise, we know that the (i + 1)th element
             is not equal, so our problem reduces in size by 1, and now we only
             need to check that the elements from (i + 2) onwards are not
             equal. Thus, we can solve using the inductive hypothesis (with the
             same choice of i, because this will effectively slide our index
             along by one, and we no longer care about the first index). It's
             also important to note that in the special case where
             i + 1 = LENGTH vs1, we trivially must have that the (i + 1)th
             element is the last element because there's only one element there,
             so the precondition to the inductive hypothesis is satisfied.
           *)
          >> Induct_on ‘vs1’ >> gvs[]
          >> rpt strip_tac
          (* Base case *)
          >> Cases_on ‘EL (i + 1) (h::vs1) = LAST (h::vs1)’
          >- (qexists ‘i + 1’ >> gvs[LAST_EL])
          (* Precondition for inductive hypothesis *)
          >> Cases_on ‘i + 1 = LENGTH vs1’
          >- gvs[LAST_EL]
          (* Inductive step *)
          >> gvs[]
          >> qexists ‘j + 1’
          >> gvs[GSYM ADD1] >> gvs[ADD1]
          >> REVERSE conj_tac
          >- (Cases_on ‘vs1’ >> gvs[])
          >> rw[]
          >> last_x_assum $ qspecl_then [‘l - 1’] assume_tac
          >> gvs[]
          >> Cases_on ‘SUC i ≤ l - 1’
          >- (gvs[]
              >> Cases_on ‘l’ >> gvs[]
              >> Cases_on ‘vs1’ >> gvs[])
          >> gvs[]
          >> Cases_on ‘l = i + 1’ >> gvs[]
          >> gvs[GSYM ADD1]
         )
      (* So our convergence point is between the point j we found on vs1, and
         the very end of vs2. Prove that it satisfies the necessary properties.
       *)
      >> qexistsl [‘j’, ‘LENGTH vs2 - 1’]
      >> gvs[]
      >> REVERSE conj_tac
      >- (qpat_x_assum ‘LAST vs2 = LAST vs1’ (fn th => PURE_REWRITE_TAC[GSYM th])
          >> Cases_on ‘vs2’ >> simp[LAST_EL]
          >> Cases_on ‘vs1’ >> gvs[]
         )
      (* Prove that any pair of points up to j in vs1 and up to the end of vs2
         are nonequal. When the point in vs2 that is not the very end, this
         follows from the earlier part of the proof where we used the inductive
         hypothesis to solve the case where the convergence point was before the
         end. In the case where the point in vs2 is the very end, this follows
         from the conditions on the choice of j which was made. *)
      >> rpt strip_tac
      >> REVERSE (Cases_on ‘m = (LENGTH vs2 - 1)’)
      >- (first_x_assum $ qspecl_then [‘l’, ‘m’] assume_tac
          >> gvs[]
         )
      >> first_x_assum $ qspecl_then [‘l’, ‘m’] kall_tac (* We no longer need
        the conditions on j, and keeping implications may lag the simplifier *)
      >> gvs[]
     )
  (* We can now create our cycle and prove that our graph cannot be a tree, a
     contradiction. *)
  >> ‘cycle g (DROP i (TAKE (j + 1) vs1) ++
               REVERSE (DROP i (TAKE k vs2)))’
    suffices_by metis_tac[is_tree_def] 
  (* Prove that this is a cycle by the definition of a cycle *)
  >> PURE_REWRITE_TAC[cycle_def]
  (* It is frequently helpful to know that each of the components of the cycle
     is nonempty *)
  (*>> ‘DROP i (TAKE (j + 1) vs1) ≠ [] ∧
                          DROP i (TAKE k vs2) ≠ []’ by gvs[]*)
  >> rpt conj_tac
  >- (gvs[walk_append]
      >> rpt conj_tac
      >- (irule walk_drop
          >> gvs[]
          >> irule walk_take
          >> gvs[]
          >> gvs[path_def]
         )
      >- (
       )
      >>
     )
  >- (cheat
     )
  >- (cheat
     )
  >> gvs[HD_APPEND]
  >> Cases_on ‘DROP i (TAKE (j + 1 - i) vs1)’
  >- (‘F’ suffices_by simp[] (* This case should be a contradiction, we
                                shouldn't have this equal to [] *)
      >> gvs[]
      >> decide_tac
     )
  >- (Cases_on ‘DROP i (TAKE (k - i) vs2)’ >> gvs[]
     )
     
  >> DEP_PURE_ONCE_REWRITE_TAC[HD_DROP]
  >> Cases_on ‘DROP i (TAKE (j + 1 - i) vs1)’ >> gvs[]
  >- (Cases_on 

      gvs[HD_REVERSE]
     )

     gvs[HD_APPEND]
QED

Theorem tree_get_path_unique:
  ∀g a b vs.
    is_tree g ∧
    path g vs ∧
    HD vs = a ∧
    LAST vs = b ⇒
    get_path g a b = vs
Proof
  Induct_on ‘vs’
  >- gvs[path_def, walk_def]
  >> rpt strip_tac
  >> last_x_assum $ qspecl_then [‘g’, ‘HD vs’, ‘b’] assume_tac
  >> gvs[]
  >> gvs[path_cons]
  >- (gvs[get_path_def]
     )
     
  >> gvs[]
        
        rpt strip_tac
  >>

  
  rw[]
QED

(* Subsumed by nodes_subtree_subset: nodes (subtree g c b) ⊂
                                                   nodes (subtree g b a) *)
Theorem in_nodes_subtree[local]:
  ∀x g a b c.
    is_tree g ∧
    x ∈ nodes (subtree g c b) ⇒
    x ∈ nodes (subtree g b a)
Proof
  rpt strip_tac
  >> gvs[subtree_def]
  >> gvs[subgraph_def]
  >> 

  >> DEP_PURE_ONCE_REWRITE_TAC[nodes_fsgAddNodes]
  >> conj_tac
  >- (irule SUBSET_FINITE
      >> qexists ‘nodes g’
      >> rw[SUBSET_DEF]
      >> gvs[is_ancestor_def]
     )
QED

Theorem nodes_subtree_subset[simp]:
  ∀g a b c.
    nodes (subtree g c b) ⊂ nodes (subtree g b a)
Proof
  rpt strip_tac
  >> gvs[PSUBSET_MEMBER]
  >> conj_tac
  >- (gvs[SUBSET_DEF]
      >> rpt strip_tac
      >> gvs[subtree_def]
     )
QED

Theorem order_subtree_lt[simp]:
  ∀g a b c.
    order (subtree g c b) < order (subtree g b a) 
Proof
  rw[]
  >> irule order_psubset
  >> 

  rpt strip_tac
  >> gvs[gsize_def]
  >> irule CARD_PSUBSET
QED

(* -------------------------------------------------------------------------- *)
(* Might it be a good idea to update the message passing in order to take an  *)
(* input as a tree, which might make it easier to use induction?              *)
(*                                                                            *)
(* Might it be a good idea to have a tree datatype that is easier to induct   *)
(* on?                                                                        *)
(*                                                                            *)
(* Might it be a good idea to have a definition which converts between the    *)
(* fsgraph type, good for general graphs, and the tree type, good for         *)
(* induction and tree-specific operations?                                    *)
(* -------------------------------------------------------------------------- *)





