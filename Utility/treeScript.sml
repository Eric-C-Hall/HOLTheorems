Theory tree

Ancestors extreal list pred_set fsgraph fundamental genericGraph

Libs dep_rewrite;

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

Theorem walk_empty_not[simp]:
  ∀g.
    ¬walk g []
Proof
  gvs[walk_def]
QED

Theorem walk_cons:
  ∀g v vs.
    walk g (v::vs) ⇔ (walk g vs ∧ adjacent g v (HD vs) ∨
                      vs = [] ∧ v ∈ nodes g)
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (Cases_on ‘vs’ >> gvs[]
      >> rw[] >> gvs[walk_def]
      >> conj_tac
      >- metis_tac[]
      >> rw[]
      >> gvs[adjacent_rules]
     )
  >> rw[] >> gvs[walk_def]
  >> conj_tac
  >- (REVERSE $ rpt strip_tac
      >- simp[]
      >> gvs[]
      >> metis_tac[adjacent_members]
     )
  >> rpt strip_tac
  >> namedCases_on ‘vs’ ["", "v' vs"] >> gvs[]
  >> gvs[adjacent_iff]
QED

Theorem path_cons:
  ∀g v vs.
    path g (v::vs) ⇔ (path g vs ∧ adjacent g v (HD vs) ∧ ¬MEM v vs ∨
                      vs = [] ∧ v ∈ nodes g)
Proof
  rpt strip_tac
  >> gvs[path_def]
  >> gvs[walk_cons]
  >> EQ_TAC >> rw[] >> gvs[]
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
  >> gvs[path_def]
         
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





