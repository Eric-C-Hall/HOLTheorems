Theory tree

Ancestors extreal pred_set fsgraph

Libs dep_rewrite;

(* -------------------------------------------------------------------------- *)
(* True iff g is a tree.                                                      *)
(* -------------------------------------------------------------------------- *)
Definition is_tree_def:
  is_tree g ⇔ (connected g ∧
               (∀ns. ¬cycle g ns))
End

(* -------------------------------------------------------------------------- *)
(* Gets the path between two nodes in a tree.                                 *)
(*                                                                            *)
(* Because we have a tree, a path always exists and it is unique, so the      *)
(* choice function always returns the same value.                             *)
(* -------------------------------------------------------------------------- *)
Definition get_path_in_tree_def:
  get_path_in_tree g org dest = (@vs. path g vs ∧ HD vs = org ∧ LAST vs = dest)
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
  ith_parent g root n i = EL i (get_path_in_tree g n root)
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
    (∃i. ith_parent g root i desc = anc)
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
  subtree g root n = fsgAddEdges
                     ({add_edge | add_edge ∈ edges g ∧
                                  (∀edge_node. edge_node ∈ add_edge ⇒
                                               is_ancestor g root edge_node )})
                     (fsgAddNodes
                      ({add_node | is_ancestor g root n add_node })
                      emptyG
                     )
End

