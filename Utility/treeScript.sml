Theory tree

Ancestors arithmetic bag cardinal combin extreal fsgraph fundamental genericGraph indexedLists list marker permutes pred_set prim_rec product_order relation rich_list

Libs dep_rewrite ConseqConv donotexpandLib useful_tacticsLib;

val _ = hide "equiv_class"

(* -------------------------------------------------------------------------- *)
(* Definitions:                                                               *)
(*                                                                            *)
(* - Is a graph a tree (is_tree_def)                                          *)
(* - Get the path between two points (get_path_def)                           *)
(* - Does a path exist between two points (exists_path_def)                   *)
(* - Find the ith parent of a node in a tree (ith_parent_def)                 *)
(* - Is a node an ancestor of another node (is_ancestor_def)                  *)
(* - Find a given subgraph of a graph (subgraph_def)                          *)
(* - Find a given subtree of a tree (subtree_def)                             *)
(* - Return the distance between two nodes in the graph (distance_def)        *)
(* - Return the diameter of a graph (diameter_def)                            *)
(* - Return the eccentricity of a node in the graph (eccentricity_def)        *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Notation:                                                                  *)
(*                                                                            *)
(* - "a - b" denotes the path from a to b                                     *)
(* - "a - b - c" denotes that b is on a - c                                   *)
(* - "a ~ b" denotes that a is adjacent to b                                  *)
(* - "a ++ b" denotes appending two paths                                     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Most important theorems:                                                   *)
(*                                                                            *)
(* - Paths in a connected graph exist between any two points                  *)
(*   (connected_exists_path)                                                  *)
(* - Paths in a tree are unique (is_tree_path_unique)                         *)
(* - A walk may be restricted to a path (restrict_walk_to_path)               *)
(* - If c and d are on a - b, then c - d is a subpath of a - b                *)
(*   (get_path_drop_take)                                                     *)
(* - We have a - c = (a - b) ++ (b - c), so long as b is on a - c     .       *)
(*   (get_path_append)                                                        *)
(* - If we have a - b - c and b - c - d, then we have a - b - d. In other     *)
(*   words, we may join together two overlapping paths.                       *)
(*   (join_overlapping_paths_mem)                                             *)
(* - If we have two nonequal paths that start with the same value, there is   *)
(*   a point at which they diverge (exists_point_of_divergence)               *)
(* - If we have two paths that start at different values but end in the same  *)
(*   value, there's a point at which they converge                            *)
(*   (exists_point_of_convergence)                                            *)
(*                                                                            *)
(* - A graph is a tree if and only if when we take away a leaf node,          *)
(*   it remains a tree. In particular, note that any tree can be built up     *)
(*   by repeatedly adding leaves, so it'll be possible to prove any tree is a *)
(*   tree by repeatedly using this theorem (is_tree_remove_leaf_is_tree)      *)
(* - A graph is a tree if and only if when we take away several leaf nodes    *)
(*   at once, it remains a tree. (is_tree_removeNodes_is_tree)                *)
(* - If a graph is connected and every node has degree at most 2 and there is *)
(* a node of degree 1, then the graph is a tree (is_tree_degree_two)          *)
(* - If all the nodes in a graph are of degree two, except for two which have *)
(* degree one, then the graph is connected. (connected_degree_two)            *)
(* - A graph containing only a singular node is a tree (is_tree_sing)         *)
(* - A graph containing a singular node is connected (is_tree_connected)      *)
(* - If a graph is connected and has a degree zero node, then no other node   *)
(*   can be in the graph. (connected_degree_zero)                             *)
(* - graph isomorphisms preserve connectedness (graph_isomorphism_connected), *)
(*   (graph_isomorphism_connected_reverse)                                    *)
(* - TODO: graph isomorphisms preserve tree-ness                              *)
(* - the graph which is just a line of nodes is connected                     *)
(* - TODO: the graph which is just a line of nodes is a tree                  *)
(*                                                                            *)
(*                                                                            *)
(* - If a ~ x - b then x = EL 1 (a - b) (adjacent_mem_get_path_first_step)    *)
(*   (adjacent_mem_get_path_first_step_alt)                                   *)
(*                                                                            *)
(* - A tree has no cycles (from definition)                                   *)
(*                                                                            *)
(* TODO: clean up the following documentation. I think it can be made simpler *)
(*                                                                            *)
(* - If we have two paths starting at the same point and the first step is    *)
(*   distinct, then the paths as a whole will be completely distinct          *)
(*   (first_step_distinct_path_distinct)                                      *)
(* - Choosing a different first step from a given point will result in a      *)
(*   disjoint subtree.  (subtrees_distinct) (subtrees_disjoint)               *)
(* - We can join together a - b and b - c, as long as the first step on       *)
(*   b - a is not the first step on b - c, i.e. we don't immediately start    *)
(*   heading backwards upon reaching b. We don't require that b is on a - c.  *)
(*   (path_continuation)                                                      *)
(* - If the first step on b - c is not the first step on b - a, then b is on  *)
(*   a - c (path_continuation_mem)                                            *)
(* - The reverse of a - b is b - a (get_path_reverse)                         *)
(* - a - b - c iff c - b - a (mem_get_path_reverse)                           *)
(* - If a - b - c, then the first step towards b is the first step towards c. *)
(*   (first_step_on_path_same)                                                *)
(* - If a - b - c, then the first step from b - a is not equal to the first   *)
(*   step from b - c (so we don't immediately start heading backwards         *)
(*   upon reaching b) (first_step_not_equal_path)                             *)
(* - If c is in the subtree defined by a - b, then the subtree defined by     *)
(*   b - c is a subset of the subtree defined by a - b.                       *)
(*   (subtree_subset)                                                         *)
(* - If we have a - b - c adjacent to each other, then the order of the       *)
(*   subtree defined by b - c is strictly less than the order of the subtree  *)
(*   defined by a - b. (order_subtree_lt_adjacent)                            *)
(* - A node n is in the subtree defined by a - b if and only if we have       *)
(*   a - b - n, that is, b is on a - n (definition of subtree)                *)
(* - a ~ b = [a; b] (adjacent_get_path)                                       *)
(* - If a ~ b and b ~ c and a ≠ c, then a - c = [a; b; c]                     *)
(*   (adjacent_get_path_2_steps)                                              *)
(* - a ~ EL 1 (a - b) (adjacent_first_step)                                   *)
(* - If a ~ b and b ~ c then ¬(a ~ c) (is_tree_no_triangle)                   *)
(* - An expression for the intersection between adjacent nodes and the nodes  *)
(*   in a subtree (adjacent_nodes_inter_nodes_subtree)                        *)
(* - The union of subtrees one level down, excluding a particular subtree,    *)
(*   will get you a new subtree one level higher, minus the root node.        *)
(*   (bigunion_image_subtree_delete)                                          *)
(* - The union of all subtrees one level down will get you the entire tree,   *)
(*   minus the root node (bigunion_image_subtree)                             *)
(* - If we have a - b - c, then we cannot have b - a - c, this won't be a     *)
(*   valid path at the same time as a - b - c being a valid path              *)
(*   (mem_not_swap_first)                                                     *)
(* - If we have b ~ c - d and a ~ b and a ≠ c, then we have a ~ b - d. That   *)
(*   is, we can extend a path at the front by one if the new adjacent node is *)
(*   different to the adjacent node that is already on the path.              *)
(*   (extend_front_adjacent)                                                  *)
(* - If a - b - d and b - c - d, then a - c - d (midpoint_push)               *)
(* - If a - c - d and a - b - c, then a - b - d (midpoint_pull)               *)
(* - If a - b - d and b - c - d, then a - b - c (restrict_overlapping_pull)   *)
(* - If a - b - c and b - c - d, then b - c - d (restrict_overlapping_push)   *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* - If a - b - c and we move c to an adjacent node d, then a - b - d unless  *)
(*   d is the first on b - a. (move_end_to_adjacent)                          *)
(* - If a - b - c and adjacent a b and adjacent c d, then a - b - d unless    *)
(*   d = a. (move_end_to_adjacent_adjacent)                                   *)
(* - If x ~ x' and x is in the subtree defined by a - b then x' is also in    *)
(*   this subtree, unless it is the first step on (b - a).                    *)
(*   (in_subtree_adjacent)                                                    *)
(*                                                                            *)
(* - If a ~ b then either b = EL 1 (a - c) or a = EL 1 (b - c)                *)
(*   (adjacent_is_first_step)                                                 *)
(*                                                                            *)
(* exists_path_adjacent_tc                                                    *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* True iff g is a tree.                                                      *)
(*                                                                            *)
(* Note that this is only valid for undirected graphs: for directed graphs,   *)
(* there may be graphs without cycles that would not commonly be described    *)
(* as trees, for example:                                                     *)
(*                                                                            *)
(*   -> O -> O ->                                                             *)
(*  /            \                                                            *)
(* O              O                                                           *)
(*  \            /                                                            *)
(*   -> O -> O ->                                                             *)
(*                                                                            *)
(* Possible improvement: change this definition to work for directed graphs   *)
(*                       by treating directed edges as undirected edges and   *)
(*                       checking if it is a tree as normal. Then update      *)
(*                       theorems dependent on trees to no longer require the *)
(*                       input graph g to be an undirected graph.             *)
(*                       However, it would a messier definition after making  *)
(*                       this change, and I'm not sure if there is an         *)
(*                       existing definition to transform a directed graph    *)
(*                       into an undirected graph                             *)
(*                                                                            *)
(* Possible improvement: a self-loop currently isn't considered a cycle       *)
(*                       because it has length 1. We don't want going to      *)
(*                       another node and then coming back to count as a      *)
(*                       "cycle", but perhaps a tree should exclude           *)
(*                       self-loops                                           *)
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
(* Tells us if a path exists between two nodes in a graph. If a path exists,  *)
(* then we can use get_path to find the path.                                 *)
(*                                                                            *)
(* This always holds in the case of a tree, or any other connected graph.     *)
(*                                                                            *)
(* This is equivalent to the transitive closure of adjacency on g             *)
(* -------------------------------------------------------------------------- *)
Definition exists_path_def:
  exists_path g org dest = (∃vs. path g vs ∧ HD vs = org ∧ LAST vs = dest)
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
  subgraph g ns =
  removeNodes ((nodes g) DIFF ns) g
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
  subtree g root n =
  subgraph g (nodes g ∩ {v | MEM n (get_path g root v)})
End

(* -------------------------------------------------------------------------- *)
(* Returns the distance between two nodes in a graph                          *)
(* -------------------------------------------------------------------------- *)
Definition distance_def:
  distance g v1 v2 = MAX_SET (IMAGE LENGTH {vs | path g vs ∧
                                                 HD vs = v1 ∧
                                                 LAST vs = v2})
End

(* -------------------------------------------------------------------------- *)
(* Returns the diameter of a graph                                            *)
(* -------------------------------------------------------------------------- *)
Definition diameter_def:
  diameter g = MAX_SET (IMAGE (UNCURRY (distance g))
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

Definition graph_isomorphism_def:
  graph_isomorphism f g1 g2 ⇔
    BIJ f (nodes g1) (nodes g2) ∧
    (∀n m. n ∈ nodes g1 ∧ m ∈ nodes g1 ⇒ (adjacent g1 n m ⇔ adjacent g2 (f n) (f m)))
End

(* -------------------------------------------------------------------------- *)
(* The graph which consists of a line of nodes, each connected to the         *)
(* previous node                                                              *)
(*                                                                            *)
(* Very easy to prove stuff for using induction. A nice simple graph. Many    *)
(* graphs contain line graphs as components                                   *)
(*                                                                            *)
(* n: the number of nodes in the graph                                        *)
(* -------------------------------------------------------------------------- *)
Definition line_graph_def:
  line_graph 0 = emptyG ∧
  line_graph (SUC 0) = fsgAddNode (INR 0) (line_graph 0) ∧
  line_graph (SUC (SUC n)) = fsgAddEdges {{INR (SUC n); INR n}} (fsgAddNode (INR (SUC n)) (line_graph (SUC n)))
End

Overload adjacent_nodes = “λg cur_node.
                             {adj_node | adj_node ∈ nodes g ∧
                                         adjacent g adj_node cur_node }”;

Theorem exists_path_same[simp]:
  ∀g a.
    exists_path g a a ⇔ a ∈ nodes g
Proof
  rpt strip_tac
  >> gvs[exists_path_def]
  >> EQ_TAC >> rpt strip_tac >> gvs[]
  >- (Cases_on ‘vs’ >> gvs[path_def, walk_def])
  >> qexists ‘[a]’
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Prove that the resulting path only travels across a given edge in    *)
(*       a given direction if the original walk also did so at some point.    *)
(*       (Should probably use list$adjacent)                                  *)
(* -------------------------------------------------------------------------- *)
Theorem restrict_walk_to_path:
  ∀g vs.
    walk g vs ⇒ ∃vs'. HD vs' = HD vs ∧ LAST vs' = LAST vs ∧ path g vs'
Proof
  rpt strip_tac
  (* Pick the shortest walk from the start of vs to the end of vs.
     This must exist because ordering walks by length is a well-founded
     relation, and a walk from the start of vs to the end of vs exists.
     If this walk had a repeated vertex in it, then we could find a shorter
     walk by skipping from the first index of the vertex to the second instance
     of the vertex.
                                                                                                   *)
  (* Prove well-formedness of the relation which compares two walks and returns
     true if one is shorter than the other *)
  >> sg ‘WF (inv_image $< (λvs : (α + num) list. LENGTH vs))’
  >- simp[WF_inv_image]
  (* By the definition of well-formedness, any set has a minimal element under
     our relation *)
  >> gvs[WF_DEF]
  >> pop_assum $ qspecl_then [‘{vs' | HD vs' = HD vs ∧
                                      LAST vs' = LAST vs ∧
                                      walk g vs'}’] assume_tac
  >> gvs[]
  (* Show that there exists an element in this set, and so there exists a
     minimal element*)
  >> qmatch_asmsub_abbrev_tac ‘b ⇒ _’
  >> sg ‘b’ >> gvs[Abbr ‘b’]
  >- (qexists ‘vs’ >> gvs[])
  (* The minimal element is the path *)
  >> qexists ‘min'’
  >> gvs[]
  >> gvs[path_def]
  (* By way of contradiction, if two elements are not distinct, then we have a
     loop and thus this isn't the shortest walk *)
  >> CCONTR_TAC
  >> gvs[EL_ALL_DISTINCT_EL_EQ]
  (* Without loss of generality, n1 is earlier than n2 *)
  >> Cases_on ‘n1 = n2’ >> gvs[]
  >> wlog_tac ‘n1 < n2’ [‘n1’, ‘n2’]
  >- (last_x_assum $ qspecl_then [‘n2’, ‘n1’] assume_tac >> gvs[])
  (* Prove that there is a shorter walk *)
  >> sg ‘walk g (TAKE n1 min' ++ DROP n2 min')’
  >- (Cases_on ‘TAKE n1 min' = []’ >> gvs[]
      >- gvs[walk_drop]
      >> Cases_on ‘DROP n2 min' = []’ >> gvs[]
      >> gvs[walk_append]
      >> gvs[walk_take, walk_drop]
      >> gvs[LAST_TAKE, HD_DROP]
      >> ‘adjacent min' (EL (n1 - 1) min') (EL n2 min')’ suffices_by gvs[walk_def]
      >> gvs[adjacent_EL]
      >> qexists ‘n1 - 1’
      >> gvs[]
     )
  (* This contradicts the fact we know that the shortest walk is the shortest
     one *)
  >> pop_assum mp_tac >> gvs[]
  >> last_x_assum irule
  (* The length is shorter *)
  >> conj_tac
  >- gvs[]
  (* The head is the same *)
  >> conj_tac
  >- (Cases_on ‘TAKE n1 min' = []’ >> gvs[]
      >- gvs[HD_DROP]
      >> gvs[HD_APPEND_NOT_NIL]
      >> gvs[HD_TAKE]
     )
  (* The last is the same *)
  >> Cases_on ‘TAKE n1 min' = []’ >> gvs[]
  >- gvs[last_drop]
  >> gvs[LAST_APPEND_NOT_NIL]
  >> gvs[last_drop]
QED

Theorem exists_path_trans:
  ∀g x y z.
    exists_path g x y ∧
    exists_path g y z ⇒
    exists_path g x z
Proof
  rpt strip_tac
  >> gvs[exists_path_def]
  (* Find a walk from x to z *)
  >> sg ‘walk g (vs ++ TL vs')’
  >- (namedCases_on ‘vs'’ ["", "v vs'"] >> gvs[]
      >> Cases_on ‘vs = []’ >> gvs[]
      >> Cases_on ‘vs'' = []’ >> gvs[]
      >- gvs[path_def]
      >> gvs[walk_append]
      >> gvs[path_def]
      >> gvs[walk_cons]
     )
  (* Restrict the walk to a path *)
  >> drule restrict_walk_to_path
  >> rpt strip_tac
  >> qexists ‘vs''’
  >> gvs[]
  >> conj_tac
  >- (Cases_on ‘vs’ >> gvs[])
  >> Cases_on ‘vs'’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[]
QED

Theorem adjacent_exists_path:
  ∀g a b.
    adjacent g a b ⇒
    exists_path g a b
Proof
  rpt strip_tac
  >> gvs[exists_path_def]
  >> Cases_on ‘a = b’
  >- (qexists ‘[a]’
      >> gvs[]
      >> metis_tac[adjacent_members]
     )
  >> qexists ‘[a; b]’
  >> gvs[]
  >> gvs[path_def]
  >> gvs[walk_def]
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> (gvs[]
          >> drule adjacent_members
          >> simp[])
     )
  >> rpt gen_tac >> strip_tac
  >> gvs[adjacent_iff]
QED

(* -------------------------------------------------------------------------- *)
(* The definition of TC can be thought of in the following way:               *)
(*                                                                            *)
(* a and b are related under the transitive closure if and only if:           *)
(* For any P which starts off being true for precisely the originally         *)
(* provided adjacencies, and then we also require P to satisfy transitivity,  *)
(* then it will necessarily have to relate a and b as a consequence of these  *)
(* requirements.                                                              *)
(*                                                                            *)
(* Alternatively, its the smallest relation with the provided adjacencies     *)
(* which also satisfies transitivity.                                         *)
(*                                                                            *)
(* Note that this definition means that a point may not be related to itself  *)
(* under the transitive closure if there is no path which leads away from     *)
(* that point and then back to itself again (loops are counted as such paths) *)
(* -------------------------------------------------------------------------- *)
Theorem exists_path_adjacent_tc:
  ∀g a b.
    exists_path g a b ⇔
      (adjacent g)⁺ a b ∨ (a = b ∧ a ∈ nodes g)
Proof
  rpt strip_tac
  >> REVERSE EQ_TAC
  >- (PURE_ONCE_REWRITE_TAC[TC_DEF]
      >> REVERSE $ rpt strip_tac
      >- gvs[]
      >> pop_assum $ qspecl_then [‘λa b. exists_path g a b’] assume_tac
      >> gvs[]
      >> pop_assum irule
      >> conj_tac
      >- metis_tac[exists_path_trans]
      >> rpt strip_tac
      >> Cases_on ‘x = y’ >> gvs[]
      >- metis_tac[adjacent_members]
      >> metis_tac[adjacent_exists_path]
     )
  >> rpt strip_tac
  >> gvs[exists_path_def]
  >> Induct_on ‘vs’ >> gvs[]
  >> rpt strip_tac
  >> REVERSE $ gvs[path_cons]
  >- (Cases_on ‘vs’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[]
      >> metis_tac[TC_CASES1]
     )
  >> Cases_on ‘h = LAST (h::vs) ∧ h ∈ nodes g’ >> gvs[]
  >> disj1_tac
  >> PURE_ONCE_REWRITE_TAC[TC_CASES1]
  >> Cases_on ‘adjacent g h (LAST (h::vs))’ >> gvs[]
  >> qexists ‘HD vs’
  >> gvs[]
  >> Cases_on ‘vs’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* If a graph is connected, then there exists a path between any two nodes.   *)
(*                                                                            *)
(* Possible improvement: prove this theorem for generic graphs rather than    *)
(*                       just fsgraphs. I don't do this currently because     *)
(*                       I use an indcution rule that is only written for     *)
(*                       fsgraphs, but I don't see any reason it can't also   *)
(*                       be written for generic graphs.                       *)
(*                                                                            *)
(* Possible improvement: make this an iff: if there exists a path between any *)
(* two points, then the graph is connected                                    *)
(* -------------------------------------------------------------------------- *)
Theorem connected_exists_path:
  ∀g.
    connected g ⇔ (∀a b.
                     a ∈ nodes g ∧
                     b ∈ nodes g ⇒
                     exists_path g a b)
Proof
  rpt strip_tac
  >> gvs[connected_def]
  >> gvs[exists_path_adjacent_tc]
  >> metis_tac[]
QED

Theorem is_tree_exists_path[simp]:
  ∀g a b.
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    is_tree g ⇒ exists_path g a b
Proof
  metis_tac[is_tree_def, connected_exists_path]
QED

Theorem connected_hd_get_path:
  ∀g a b.
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    connected g ⇒
    HD (get_path g a b) = a
Proof
  rpt strip_tac
  >> gvs[get_path_def]
  >> SELECT_ELIM_TAC
  >> gvs[connected_exists_path, exists_path_def]
QED

Theorem is_tree_hd_get_path:
  ∀g a b.
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    is_tree g ⇒
    HD (get_path g a b) = a
Proof
  metis_tac[is_tree_def, connected_hd_get_path]
QED

Theorem exists_path_hd_get_path[simp]:
  ∀g a b.
    exists_path g a b ⇒
    HD (get_path g a b) = a
Proof
  rpt strip_tac
  >> gvs[get_path_def]
  >> SELECT_ELIM_TAC
  >> gvs[exists_path_def]
  >> metis_tac[]
QED

Theorem connected_last_get_path:
  ∀g a b.
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    connected g ⇒
    LAST (get_path g a b) = b
Proof
  rpt strip_tac
  >> gvs[get_path_def]
  >> SELECT_ELIM_TAC
  >> gvs[connected_exists_path, exists_path_def]
QED

Theorem is_tree_last_get_path:
  ∀g a b.
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    is_tree g ⇒
    LAST (get_path g a b) = b
Proof
  metis_tac[is_tree_def, connected_last_get_path]
QED

Theorem exists_path_last_get_path[simp]:
  ∀g a b.
    exists_path g a b ⇒
    LAST (get_path g a b) = b
Proof
  rpt strip_tac
  >> gvs[get_path_def]
  >> SELECT_ELIM_TAC
  >> gvs[exists_path_def]
  >> metis_tac[]
QED

Theorem connected_path_get_path:
  ∀g a b.
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    connected g ⇒
    path g (get_path g a b)
Proof
  rpt strip_tac
  >> gvs[get_path_def]
  >> SELECT_ELIM_TAC
  >> gvs[connected_exists_path, exists_path_def]
QED

Theorem path_get_path:
  ∀g a b.
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    is_tree g ⇒
    path g (get_path g a b)
Proof
  metis_tac[connected_path_get_path, is_tree_def]
QED

Theorem exists_path_path_get_path[simp]:
  ∀g a b.
    exists_path g a b ⇒
    path g (get_path g a b)
Proof
  rpt strip_tac
  >> gvs[get_path_def]
  >> SELECT_ELIM_TAC
  >> gvs[exists_path_def]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* An alternative charaterization of a cycle in terms of a path.              *)
(*                                                                            *)
(* Advantage: bundling up walk and ALL_DISTINCT together as a path allows us  *)
(*            to use theorems about paths, which naturally consider           *)
(*            distinctness, rather than separately having to apply theorems   *)
(*            about walks as well as theorems about ALL_DISTINCT.             *)
(*                                                                            *)
(* Disadvantage: we have to consider adjacency of the first two elements      *)
(*               separately                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem cycle_alt:
  ∀g vs.
    cycle g vs ⇔
      path g (TL vs) ∧
      4 ≤ LENGTH vs ∧
      HD vs = LAST vs ∧
      adjacent g (HD vs) (HD (TL vs))
Proof
  rpt strip_tac
  >> gvs[cycle_def]
  >> gvs[path_def]
  >> Cases_on ‘vs’ >> gvs[]
  >> gvs[walk_cons]
  >> Cases_on ‘t’ >> gvs[]
  >> metis_tac[]
QED

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
(*                                                                            *)
(* Note that this is only true in undirected graphs. One can have cycle-free  *)
(* directed graphs without unique paths.                                      *)
(*                                                                            *)
(* Possible improvement: use the more generalised theorems                    *)
(* exists_point_of_divergence and exists_point_of_convergence to simplify     *)
(* this proof and make it run faster.                                         *)
(* -------------------------------------------------------------------------- *)
Theorem is_tree_path_unique:
  ∀(g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph) a b vs1 vs2.
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
  >> ‘cycle g (DROP i (TAKE (j + 1) vs1) ++ REVERSE (DROP i (TAKE k vs2)))’
    suffices_by metis_tac[is_tree_def]
  (* Prove that this is a cycle by the definition of a cycle *)
  >> PURE_REWRITE_TAC[cycle_def, cycle_def]
  (* It is frequently helpful to know that each of the components of the cycle
     is nonempty *)
  (*>> ‘DROP i (TAKE (j + 1) vs1) ≠ [] ∧
                          DROP i (TAKE k vs2) ≠ []’ by gvs[]*)
  >> rpt conj_tac
  >- (gvs[walk_append]
      >> rpt conj_tac
      >- (irule walk_drop >> gvs[]
          >> irule walk_take >> gvs[]
          >> gvs[path_def]
         )
      >- (irule walk_drop >> gvs[]
          >> irule walk_take >> gvs[]
          >> gvs[path_def]
         )
      >> gvs[HD_REVERSE]
      >> gvs[last_drop]
      >> gvs[LAST_TAKE]
      >> gvs[path_def, walk_def]
      >> PURE_ONCE_REWRITE_TAC[adjacent_SYM]
      >> first_x_assum irule
      >> gvs[adjacent_EL]
      >> qexists ‘k - 1’ >> gvs[]
     )
  >- (gvs[TL_APPEND]
      >> gvs[ALL_DISTINCT_APPEND]
      (* First string is all distinct *)
      >> conj_tac
      >- (irule ALL_DISTINCT_TL
          >> irule ALL_DISTINCT_DROP
          >> irule ALL_DISTINCT_TAKE
          >> gvs[path_def]
         )
      (* Second string is all distinct *)
      >> conj_tac
      >- (irule ALL_DISTINCT_DROP
          >> irule ALL_DISTINCT_TAKE
          >> gvs[path_def]
         )
      (* Strings are all distinct with respect to each other *)
      >> rpt strip_tac
      >> gvs[MEM_EL]
      >> gvs[GSYM (cj 2 EL), ADD1]
      >> gvs[EL_DROP]
      >> gvs[EL_TAKE]
      >> gvs[LENGTH_TL]
      >> gvs[EL_DROP]
      >> gvs[EL_TAKE]
      >> gvs[LESS_EQ, ADD1]
      (* The equivalent elements in the last assumption range between i + 1 and
         j in vs1, and between i and k - 1 in vs2. We need to treat j in vs1
         and i in vs2 as special cases, because those are the points of
         convergence and divergence. However, for any other choices of indices,
         this contradicts the fact that we earlier proved that the two paths
         are distinct from each other on the part where they split from each
         other.
       *)
      >> REVERSE (Cases_on ‘i + (n + 1) = j ∨ i + n' = i’)
      >- gvs[]
      >> gvs[]
      (* We are at the point of convergence, and need to prove that this is
         distinct from any other point in vs2. This follows from the fact that
         vs2 is a path *)
      >- (gvs[path_def]
          >> gvs[EL_ALL_DISTINCT_EL_EQ]
         )
      (* We are at the point of divergence, and need to prove that this is
        distinct from any other point on vs1. This follows from the fact that
        vs1 is a path *)
      >> qpat_x_assum ‘EL i vs1 = EL i vs2’ (fn th => gvs[GSYM th])
      >> gvs[path_def]
      >> gvs[EL_ALL_DISTINCT_EL_EQ]
     )
  >- (all_tac
      (* Our point of divergence is i, our point of convergence is j on vs1 and
       k on vs2.
.
       Each of j and k is not equal to i, so they must be at least one step away
       from i. However, this in itself only shows that our cycle is at least
       length 2 (excluding the repeated node at the start and end). We need to
       show our cycle has at least length 3.
.
       If j and k were both one step away, then the first step away from i would
       be equal on both paths, which contradicts the fact that i is a point of
       divergence.
.
       Thus, at least one of j/k is at least two steps away while the other is
       at least one step away. So our cycle is has at least length 3.
       *)
      >> REVERSE $ Cases_on ‘j - i = 1 ∧ k - i = 1’
      >- simp[]
      >> irule FALSITY
      >> qpat_x_assum ‘EL (i + 1) vs1 ≠ EL (i + 1) vs2’ mp_tac
      >> PURE_REWRITE_TAC[IMP_CLAUSES, cj 1 NOT_CLAUSES]
      >> qpat_x_assum ‘EL j vs1 = EL k vs2’ mp_tac
      >> ‘j = i + 1’ by simp[]
      >> ‘k = i + 1’ by simp[]
      >> simp[]
     )
  >> gvs[HD_APPEND_NOT_NIL]
  >> gvs[LAST_APPEND_NOT_NIL]
  >> gvs[LAST_REVERSE]
  >> gvs[HD_DROP]
  >> gvs[EL_TAKE]
QED

Theorem walk_in_nodes:
  ∀g v vs.
    MEM v vs ∧
    walk g vs ⇒
    v ∈ nodes g
Proof
  rpt strip_tac
  >> gvs[walk_def]
QED

Theorem path_in_nodes:
  ∀g v vs.
    MEM v vs ∧
    path g vs ⇒
    v ∈ nodes g
Proof
  rpt strip_tac
  >> gvs[path_def]
  >> metis_tac[walk_in_nodes]
QED

Theorem is_tree_get_path_unique:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b vs.
    is_tree g ∧
    path g vs ∧
    HD vs = a ∧
    LAST vs = b ⇒
    get_path g a b = vs
Proof
  rpt strip_tac
  >> irule is_tree_path_unique
  >> gvs[]
  (* This is used several times *)
  >> sg ‘HD vs ∈ nodes g’
  >- (irule path_in_nodes
      >> qexists ‘vs’ >> gvs[]
      >> Cases_on ‘vs’ >> gvs[]
     )
  (* This is also used several times *)
  >> sg ‘LAST vs ∈ nodes g’
  >- (irule path_in_nodes
      >> qexists ‘vs’ >> gvs[]
      >> Cases_on ‘vs’ >> gvs[MEM_LAST]
     )
  >> conj_tac
  >- simp[is_tree_hd_get_path]
  >> conj_tac
  >- simp[is_tree_last_get_path]
  >> qexists ‘g’
  >> simp[path_get_path]
QED

Theorem is_tree_get_path_same:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a.
    is_tree g ∧
    a ∈ nodes g ⇒
    get_path g a a = [a]
Proof
  rpt strip_tac
  >> gvs[is_tree_get_path_unique]
QED

Theorem exists_path_get_path_same[simp]:
  ∀g a.
    exists_path g a a ⇒
    get_path g a a = [a]
Proof
  rpt strip_tac
  >> gvs[get_path_def]
  >> SELECT_ELIM_TAC
  >> conj_tac
  >- (qexists ‘[a]’ >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘x’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[]
QED

Theorem exists_path_in_nodes:
  ∀g a b.
    exists_path g a b ⇒
    a ∈ nodes g ∧
    b ∈ nodes g
Proof
  rpt strip_tac
  >- (gvs[exists_path_def]
      >> Cases_on ‘vs’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[]
      >> gvs[path_def]
      >> gvs[walk_def]
     )
  >> gvs[exists_path_def]
  >> Cases_on ‘vs’ using SNOC_CASES >> gvs[]
  >> Cases_on ‘l’ using SNOC_CASES >> gvs[]
  >> gvs[path_def]
  >> gvs[walk_def]
QED

Theorem get_path_empty[simp]:
  ∀g a b.
    exists_path g a b ⇒
    (get_path g a b = [] ⇔ F)
Proof
  rpt strip_tac
  >> EQ_TAC >> simp[]
  >> gvs[get_path_def, exists_path_def]
  >> SELECT_ELIM_TAC
  >> gvs[]
  >> metis_tac[]
QED

Theorem exists_path_0_less_len_get_path[simp]:
  ∀g a b.
    exists_path g a b ⇒
    0 < LENGTH (get_path g a b)
Proof
  rpt strip_tac
  >> simp[LENGTH_NON_NIL]
QED

Theorem exists_path_1_leq_len_get_path[simp]:
  ∀g a b.
    exists_path g a b ⇒
    1 ≤ LENGTH (get_path g a b)
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[ONE, GSYM LESS_EQ]
  >> gvs[]
QED

Theorem MEM_get_path_first[simp]:
  ∀g a b.
    exists_path g a b ⇒
    MEM a (get_path g a b)
Proof
  rpt strip_tac
  >> gvs[MEM_EL]
  >> qexists ‘0’
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* The existing relationship between LAST and EL uses PRE, but I think it's   *)
(* more common to use minus one instead of pre                                *)
(* -------------------------------------------------------------------------- *)
Theorem LAST_EL_LEN_MINUS_ONE:
  ∀l.
    l ≠ [] ⇒
    LAST l = EL (LENGTH l - 1) l
Proof
  rpt strip_tac
  >> gvs[GSYM EL_PRE_LENGTH]
  >> gvs[PRE_SUB1]
QED

Theorem EL_LEN_MINUS_ONE_get_path[simp]:
  ∀g a b.
    exists_path g a b ⇒
    EL (LENGTH (get_path g a b) - 1) (get_path g a b) = b
Proof
  rpt strip_tac
  >> gvs[GSYM LAST_EL_LEN_MINUS_ONE]
QED

Theorem MEM_get_path_last[simp]:
  ∀g a b.
    exists_path g a b ⇒
    MEM b (get_path g a b)
Proof
  rpt strip_tac
  >> gvs[MEM_EL]
  >> qexists ‘LENGTH (get_path g a b) - 1’
  >> simp[]
QED

Theorem get_path_sing[simp]:
  ∀g a b h.
    exists_path g a b ⇒
    (get_path g a b = [h] ⇔ a = h ∧ b = h)
Proof
  rpt strip_tac
  >> gvs[get_path_def]
  >> SELECT_ELIM_TAC
  >> gvs[exists_path_def]
  >> conj_tac >- metis_tac[]
  >> rpt strip_tac
  >> Cases_on ‘vs’ >> gvs[]
  >> Cases_on ‘x’ >> gvs[]
  >> Cases_on ‘t’ using SNOC_CASES >> gvs[]
  >- (Cases_on ‘t'’ >> gvs[])
  >> Cases_on ‘t'’ >> gvs[]
  >- gvs[LAST_DEF]
  >> rpt strip_tac
  >> gvs[]
QED

Theorem LAST_TL:
  ∀l.
    1 < LENGTH l ⇒
    LAST (TL l) =  LAST l
Proof
  rw[]
  >> Cases_on ‘l’ >> simp[]
  >> Cases_on ‘t’ >> gvs[TL_DEF]
QED

Theorem path_append:
  ∀g vs1 vs2.
    vs1 ≠ [] ∧
    vs2 ≠ [] ⇒
    (path g (vs1 ++ vs2) ⇔ path g vs1 ∧
                           path g vs2 ∧
                           adjacent g (LAST vs1) (HD vs2) ∧
                           (∀v. MEM v vs1 ⇒ ¬MEM v vs2)
    )
Proof
  rpt strip_tac
  >> gvs[path_def]
  >> gvs[walk_append]
  >> gvs[ALL_DISTINCT_APPEND]
  >> metis_tac[]
QED

Theorem path_tl:
  ∀g ls.
    TL ls ≠ [] ∧
    path g ls ⇒
    path g (TL ls)
Proof
  rpt strip_tac
  >> Cases_on ‘ls’ >> gvs[]
  >> gvs[path_cons]
QED

Theorem get_path_equals_cons:
  ∀g a b h t.
    exists_path g a b ∧
    get_path g a b = h::t ⇒
    a = h
Proof
  rpt strip_tac
  >> ‘HD (get_path g a b) = h’ by (pop_assum (fn th => PURE_REWRITE_TAC[th])
                                   >> simp[])
  >> gvs[]
QED

Theorem is_tree_get_path_equals_cons:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b h t.
    is_tree g ∧
    exists_path g a b ∧
    t ≠ [] ⇒
    (get_path g a b = h::t ⇔
       (a = h ∧ ∃a2. get_path g a2 b = t ∧ adjacent g a a2 ∧ a2 ∈ nodes g ∧
                     ¬MEM a (get_path g a2 b)))
Proof
  rpt strip_tac
  >> EQ_TAC >> disch_tac
  >- (‘a = h’ by metis_tac[get_path_equals_cons]
      >> gvs[]
      >> namedCases_on ‘t’ ["", "a2 t"] >> gvs[]
      >> qexists ‘a2’
      >> ‘path g (get_path g a b)’ by gvs[]
      >> gvs[path_def, walk_def, Excl "exists_path_path_get_path"]
      >> sg ‘get_path g a2 b = a2::t'’
      >- (irule is_tree_get_path_unique
          >> gvs[]
          >> ‘LAST (get_path g a b) = b’ by gvs[]
          >> gvs[Excl "exists_path_last_get_path"]
          >> ‘path g (get_path g a (LAST (a2::t')))’ by gvs[]
          >> gvs[Excl "exists_path_path_get_path"]
          >> gvs[path_cons])
      >> gvs[]
     )
  >> gvs[]
  >> irule is_tree_get_path_unique
  >> gvs[]
  >> ‘exists_path g a2 b’ by metis_tac[adjacent_exists_path,
                                       exists_path_trans, adjacent_SYM]
  >> gvs[LAST_DEF]
  >> gvs[path_cons]
QED

(* -------------------------------------------------------------------------- *)
(* Maybe this is too trivial to have as a theorem, but it wasn't obvious to   *)
(* me that it was trivial when I searched for it                              *)
(* -------------------------------------------------------------------------- *)
Theorem path_cons_cons_adjacent:
  ∀g h h' t.
    path g (h::h'::t) ⇒
    adjacent g h h'
Proof
  rpt strip_tac
  >> gvs[path_def, walk_def]
QED

Theorem path_reverse[simp]:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph vs.
    path g (REVERSE vs) ⇔ path g vs
Proof
  rpt strip_tac
  (* Since REVERSE (REVERSE vs) = vs, without loss of generality we may prove
   only one direction *)
  >> wlog_tac ‘path g vs’ [‘vs’]
  >- metis_tac[REVERSE_REVERSE]
  >> gvs[]
  (* *)
  >> Induct_on ‘vs’ >> gvs[]
  >> rpt strip_tac
  >> gvs[path_cons]
  >> Cases_on ‘vs = []’ >> gvs[]
  >> gvs[path_append]
  >> conj_tac
  >- metis_tac[adjacent_members]
  >> gvs[LAST_REVERSE]
  >> metis_tac[adjacent_SYM]
QED

Theorem get_path_reverse[simp]:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ⇒
    REVERSE (get_path g b a) = get_path g a b
Proof
  rpt strip_tac
  >> irule is_tree_path_unique
  >> gvs[HD_REVERSE, LAST_REVERSE]
  >> qexists ‘g’
  >> gvs[]
QED

Theorem exists_path_sym:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b.
    exists_path g a b ⇔ exists_path g b a
Proof
  rpt strip_tac
  (* The two directions are effectively proving the same thing, up to renaming
     of a and b. Without loss of generality, we can prove only one direction. *)
  >> wlog_tac ‘exists_path g a b’ [‘a’, ‘b’]
  >- metis_tac[]
  >> gvs[]
  (* If we have a path in one direction, its reverse is a path in the other
     direction *)
  >> gvs[exists_path_def]
  >> qexists ‘REVERSE vs’
  >> Cases_on ‘vs = []’ >> gvs[]
  >> gvs[HD_REVERSE, LAST_REVERSE]
  >> metis_tac[path_reverse]
QED

Theorem get_path_exists_cons:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b.
    is_tree g ∧
    exists_path g a b ∧
    a ≠ b ⇒
    (∃a2. get_path g a b = a::(get_path g a2 b) ∧
          adjacent g a a2 ∧
          a2 ∈ nodes g ∧
          ¬MEM a (get_path g a2 b))
Proof
  rpt strip_tac
  >> Cases_on ‘get_path g a b’ >> gvs[]
  >> Cases_on ‘t = []’ >> gvs[]
  >> metis_tac[is_tree_get_path_equals_cons]
QED

Theorem mem_get_path_in_nodes:
  ∀g a b n.
    exists_path g a b ∧
    MEM n (get_path g a b) ⇒
    n ∈ nodes g
Proof
  rpt strip_tac
  >> metis_tac[path_in_nodes, exists_path_path_get_path]
QED

Theorem el_get_path_in_nodes[simp]:
  ∀g a b i.
    exists_path g a b ∧
    i ≤ LENGTH (get_path g a b) - 1 ⇒
    EL i (get_path g a b) ∈ nodes g
Proof
  rpt strip_tac
  >> sg ‘MEM (EL i (get_path g a b)) (get_path g a b)’
  >- (irule EL_MEM
      >> gvs[LESS_EQ, ADD1]
      >> Cases_on ‘i’ >> gvs[]
     )
  >> metis_tac[mem_get_path_in_nodes]
QED

Theorem take_get_path:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b n.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    0 < n ∧
    n ≤ LENGTH (get_path g a b) ⇒
    TAKE n (get_path g a b) = get_path g a (EL (n - 1) (get_path g a b))
Proof
  rpt strip_tac
  >> irule EQ_SYM
  >> irule is_tree_path_unique
  >> rpt strip_tac
  >- (qexists ‘a’
      >> sg ‘exists_path g a (EL (n - 1) (get_path g a b))’
      >- (irule is_tree_exists_path
          >> gvs[])
      >> gvs[HD_TAKE]
     )
  >- (qexists ‘EL (n - 1) (get_path g a b)’
      >> gvs[LAST_TAKE]
     )
  >> qexists ‘g’
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* The path from c to d is a subpath of the path from a to b, if c and d are  *)
(* on this path.                                                              *)
(* -------------------------------------------------------------------------- *)
Theorem get_path_drop_take:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c d.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    MEM c (get_path g a b) ∧
    MEM d (get_path g a b) ∧
    findi c (get_path g a b) ≤ findi d (get_path g a b) ⇒
    get_path g c d = DROP (findi c (get_path g a b))
                          (TAKE (findi d (get_path g a b) + 1)
                                (get_path g a b))
Proof
  rpt strip_tac
  >> ‘c ∈ nodes g ∧ d ∈ nodes g’ by metis_tac[is_tree_exists_path,
                                              mem_get_path_in_nodes]
  >> irule is_tree_path_unique
  (* Required condition to apply HD_DROP or LAST_DROP *)
  >> sg ‘findi c (get_path g a b) <
         LENGTH (TAKE (findi d (get_path g a b) + 1) (get_path g a b))’
  >- (gvs[LENGTH_TAKE_EQ]
      >> rw[]
      >> gvs[MEM_findi]
     )
  (* Prove that the heads are the same, the tails are the same, and that they
     are both paths *)
  >> rpt strip_tac
  >- (qexists ‘c’
      >> simp[HD_DROP, EL_TAKE, EL_findi]
     )
  >- (qexists ‘d’
      >> simp[last_drop, LAST_TAKE]
      >> DEP_PURE_ONCE_REWRITE_TAC[LAST_TAKE]
      >> conj_tac
      >- (gvs[]
          >> metis_tac[MEM_findi, LESS_EQ, ADD1]
         )
      >> simp[EL_findi]
     )
  >> qexists ‘g’
  >> simp[]
  >> irule path_drop
  >> gvs[]
QED

Theorem findi_hd:
  ∀l ls.
    findi l ls = 0 ⇔ l = HD ls ∨ ls = []
Proof
  rpt strip_tac
  >> Cases_on ‘ls’ >> rw[findi_def]
QED

Theorem findi_get_path_hd[simp]:
  ∀g a b.
    exists_path g a b ⇒
    findi a (get_path g a b) = 0
Proof
  rpt strip_tac
  >> gvs[findi_hd]
QED

Theorem findi_last:
  ∀l ls.
    findi l ls = LENGTH ls - 1 ⇔ (LAST ls = l ∧ ¬MEM l (FRONT ls)) ∨ ls = []
Proof
  rpt strip_tac
  >> Induct_on ‘ls’ >> gvs[findi_def]
  >> rpt strip_tac
  >> rw[]
  >- (Cases_on ‘ls’ >> gvs[])
  >> Cases_on ‘ls’ >> gvs[ADD1]
QED

Theorem MEM_FRONT_NOT_LAST_GEN:
  ∀l ls.
    ls ≠ [] ∧
    ALL_DISTINCT ls ∧
    l = LAST ls ⇒
    ¬MEM l (FRONT ls)
Proof
  metis_tac[MEM_FRONT_NOT_LAST]
QED

Theorem get_path_all_distinct[simp]:
  ∀g a b.
    exists_path g a b ⇒
    ALL_DISTINCT (get_path g a b)
Proof
  rpt strip_tac
  >> ‘path g (get_path g a b)’ by gvs[]
  >> gvs[path_def, Excl "exists_path_path_get_path"]
QED

Theorem findi_get_path_last[simp]:
  ∀g a b.
    exists_path g a b ⇒
    findi b (get_path g a b) = LENGTH (get_path g a b) - 1
Proof
  rpt strip_tac
  >> gvs[findi_last]
  >> irule MEM_FRONT_NOT_LAST_GEN
  >> simp[]
QED

Theorem MEM_findi_leq:
  ∀x l.
    MEM x l ⇒ findi x l ≤ LENGTH l - 1
Proof
  rpt strip_tac
  >> gvs[LE_LT1]
  >> Cases_on ‘LENGTH l’ >> gvs[]
  >> metis_tac[MEM_findi, ADD1]
QED

Theorem TL_DROP_SUB:
  ∀n ls.
    n ≤ LENGTH ls - 1 ⇒
    TL (DROP n ls) = DROP (n + 1) ls
Proof
  Induct_on ‘ls’ >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘n’ >> gvs[ADD1]
QED

(* -------------------------------------------------------------------------- *)
(* A path a-c can be split into a-b and b-c, as long as b is on a-c.          *)
(* -------------------------------------------------------------------------- *)
Theorem get_path_append:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ∈ nodes g ∧
    c ∈ nodes g ∧
    MEM b (get_path g a c) ⇒
    get_path g a c = get_path g a b ++ TL (get_path g b c)
Proof
  rpt strip_tac
  >> sg ‘b ∈ nodes g’
  >- (irule path_in_nodes
      >> qexists ‘get_path g a c’
      >> simp[]
     )
  (* We already know the first appended list is not empty, prove that the
     second appended list is not empty *)
  >> Cases_on ‘TL (get_path g b c) = []’ >> gvs[]
  >- (Cases_on ‘get_path g b c’ >> gvs[])
  (* Prove that b and c are nonequal *)
  >> Cases_on ‘b = c’ >> gvs[]
  (* Prove that each component of g a c is equivalent to the corresponding
     component on the right hand side*)
  >> qsuff_tac ‘TAKE (findi b (get_path g a c) + 1) (get_path g a c) =
                get_path g a b ∧
                DROP (findi b (get_path g a c) + 1) (get_path g a c) =
                TL (get_path g b c)’
  >- (rpt strip_tac
      >> qpat_x_assum ‘TAKE _ _ = get_path g a b’
                      (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
      >> qpat_x_assum ‘DROP _ _ = TL (get_path g b c)’
                      (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
      >> gvs[]
     )
  (* Prove the first component is equal *)
  >> conj_tac
  >- (qspecl_then [‘g’, ‘a’, ‘c’, ‘a’, ‘b’] assume_tac get_path_drop_take
      >> gvs[]
     )
  (* Prove the second component is equal *)
  >> qspecl_then [‘g’, ‘a’, ‘c’, ‘b’, ‘c’] assume_tac get_path_drop_take
  >> gvs[]
  >> gvs[MEM_findi_leq]
  >> Cases_on ‘LENGTH (get_path g a c)’ >> gvs[ADD1]
  >> pop_assum (fn th => gvs[GSYM th])
  >> gvs[TL_DROP_SUB, MEM_findi_leq]
QED

(* -------------------------------------------------------------------------- *)
(* If we two sequences which start at the same value and eventually reach     *)
(* different values, there exists a point of divergence. This is the last     *)
(* point at which the sequences are the same: at the next step, the sequences *)
(* are different.                                                             *)
(*                                                                            *)
(* Possible improvement: generalise to allow this to work even if the initial *)
(*   point at which the sequences are the same is not at the start            *)
(* -------------------------------------------------------------------------- *)
Theorem exists_point_of_divergence:
  ∀vs1 vs2 i.
    i < LENGTH vs1 ∧
    i < LENGTH vs2 ∧
    HD vs1 = HD vs2 ∧
    EL i vs1 ≠ EL i vs2 ⇒
    ∃j.
      (∀k. k ≤ j ⇒ EL k vs1 = EL k vs2) ∧
      EL (j + 1) vs1 ≠ EL (j + 1) vs2 ∧
      j < i
Proof
  (* Induct on the first sequence *)
  Induct_on ‘vs1’ >> gvs[]
  >> rpt strip_tac
  (* Split up the second sequence in the corresponding manner *)
  >> namedCases_on ‘vs2’ ["", "v vs2"] >> gvs[]
  (* Apply the inductive hypothesis to the appropriate values *)
  >> last_x_assum $ qspecl_then [‘vs2'’, ‘i - 1’] assume_tac
  (* Prove the preconditions to use the inductive hypothesis *)
  >> gvs[ADD1]
  >> namedCases_on ‘vs1’ ["", "v vs1"] >> gvs[]
  >> namedCases_on ‘vs2'’ ["", "v vs2"] >> gvs[]
  (* Consider the base case where i was equal to 0 *)
  >> Cases_on ‘i’ >> gvs[LESS_MONO_EQ, GSYM ADD1]
  >> gvs[ADD1]
  (* In the base case where the second element is nonequal, our point of
     divergence must be at the very start *)
  >> REVERSE (Cases_on ‘v' = v''’) >> gvs[]
  >- (qexists ‘0’ >> gvs[])
  (* We have proven all preconditions for the inductive hypothesis. Thus, we
     have a j which works for the smaller list. Thus, SUC j will work for the
     larger list *)
  >> qexists ‘SUC j’
  >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘k’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* If we have two sequences which are different values at some point and      *)
(* eventually reach the same values (not necessarily at the same index as     *)
(* each other), then there is some pair of indices at which the sequences are *)
(* the same, such that the sequences are not the same at any prior pair of    *)
(* indices.                                                                   *)
(*                                                                            *)
(* Possible improvement: this currently only shows that if both indices are   *)
(* strictly smaller, then the data at the prior indices is not the same. This *)
(* could be strengthened to find a point relative to which even if only one   *)
(* of the indices is strictly smaller and the other is smaller in a           *)
(* non-strict manner, the sequences are not the same. However, this is not    *)
(* necessary for my purposes, because we typically already know that both of  *)
(* the sequences are paths, and they meet at their endpoints, which implies   *)
(* that the last element cannot be equal to any of the prior ones.            *)
(* See also product_orderScript.                                              *)
(* -------------------------------------------------------------------------- *)
Theorem exists_point_of_convergence:
  ∀vs1 vs2 i j k.
    i < LENGTH vs1 ∧
    i < LENGTH vs2 ∧
    j < LENGTH vs1 ∧
    k < LENGTH vs2 ∧
    i ≤ j ∧
    i ≤ k ∧
    EL i vs1 ≠ EL i vs2 ∧
    EL j vs1 = EL k vs2 ⇒
    ∃l m.
      (∀x y. i ≤ x ∧ x < l ∧ i ≤ y ∧ y < m ⇒ EL x vs1 ≠ EL y vs2) ∧
      EL l vs1 = EL m vs2 ∧
      l ≤ j ∧
      m ≤ k
Proof
  (* If there exists an earlier choice of j and k such that EL j vs1 = EL k vs2,
     we have reduced the problem to a smaller instance and can thus apply the
     inductive hypothesis to solve. The same choice of l and m will work.
.
     By "an earlier choice of j and k", I mean that both j and k are strictly
     smaller.
.
     If there does not exist an earlier choice of j and k such that
     EL j vs1 = EL k vs2, then the appropriate choice of l and m will be j and
     k. It is easy to check that in this case, all requirements of l and m are
     met.
   *)
  (* We want to induct on j and k, where our inductive hypothesis says that our
     property holds if both j and k are smaller. First, introduce the induction
     theorem we are going to use, which is based on the well-formedness of this
     relation on j and k. *)
  qspec_then ‘product_order ($< : num -> num -> bool) ($< : num -> num -> bool)’
             assume_tac WF_INDUCTION_THM >> gvs[]
  (* Now, combine j and k into one variable, jk, so we can induct on that. *)
  >> rpt strip_tac
  >> qabbrev_tac ‘jk = (j,k)’
  >> gs[Abbrev_def]
  (* Generalise all our variables so that we have a stronger inductive
     hypothesis*)
  >> last_x_assum assume_tac
  >> rpt (last_x_assum mp_tac) >> disch_tac >> SPEC_ALL_TAC
  (* Ensure that jk is at the front, because that's what we are inducting over,
     so that HO_MATCH_MP_TAC recognises it *)
  >> NTAC 3 gen_tac
  >> SPEC_TAC (“j : num”, “j : num”) >> SPEC_TAC (“i : num”, “i : num”)
  >> SPEC_ALL_TAC
  (* Apply our induction theorem *)
  >> pop_assum (fn th => HO_MATCH_MP_TAC th)
  (* Simplify *)
  >> rpt strip_tac >> gvs[]
  (* Use inductive hypothesis to prove this theorem in the case where there is
     a choice of strictly earlier j and k such that EL j vs1 = EL k vs2 *)
  >> Cases_on ‘∃j_earlier k_earlier.
                 i ≤ j_earlier ∧
                 i ≤ k_earlier ∧
                 j_earlier < j ∧
                 k_earlier < k ∧
                 EL j_earlier vs1 = EL k_earlier vs2’
  >- (gvs[]
      (* Apply the inductive hypothesis *)
      >> last_x_assum $ qspec_then ‘(j_earlier, k_earlier)’ assume_tac
      >> gvs[product_order_def]
      >> first_x_assum $ qspecl_then [‘i’, ‘vs1’, ‘vs2’] assume_tac
      >> gvs[]
      (* The choice of l and m given in the inductive hypothesis also works in
         the inductive step *)
      >> qexistsl [‘l’, ‘m’]
      >> gvs[] >> metis_tac[]
     )
  (* We no longer need the inductive hypothesis *)
  >> last_x_assum kall_tac
  (* We now know that no prior choice of j and k can have EL j vs1 = EL k vs2,
     so we can choose l = j and m = k*)
  >> qexistsl [‘j’, ‘k’]
  >> gvs[]
  >> rpt strip_tac
  >> first_x_assum $ qspecl_then [‘x’, ‘y’] assume_tac
  >> metis_tac[]
QED

Theorem adjacent_two[simp]:
  ∀a b v1 v2.
    adjacent [a;b] v1 v2 ⇔ v1 = a ∧ v2 = b
Proof
  rpt strip_tac
  >> gvs[adjacent_iff]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* If two nodes are adjacent, then the path between them is simply the first  *)
(* node followed by the second                                                *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_get_path:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b.
    is_tree g ∧
    adjacent g a b ∧
    a ≠ b ⇒
    get_path g a b = [a; b]
Proof
  rpt strip_tac
  >> irule is_tree_get_path_unique
  >> gvs[path_def, walk_def]
  >> metis_tac[adjacent_members]
QED

Theorem adjacent_get_path_2_steps:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    adjacent g a b ∧
    adjacent g b c ∧
    a ≠ c ∧
    a ≠ b ∧
    b ≠ c ⇒
    get_path g a c = [a; b; c]
Proof
  rpt strip_tac
  >> irule is_tree_get_path_unique
  >> simp[]
  >> simp[path_def]
  >> simp[walk_def]
  >> rpt strip_tac
  >- metis_tac[adjacent_members]
  >- metis_tac[adjacent_members]
  >- metis_tac[adjacent_members]
  >> gvs[adjacent_iff]
QED

(* -------------------------------------------------------------------------- *)
(* If we have a path from a to b, and x is on this path and x is adjacent to  *)
(* a, then x must be the second node on the path.                             *)
(*                                                                            *)
(* This follows from uniqueness of paths: otherwise, we could choose either   *)
(* go directly to x or we could choose to take the long way via the path.     *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_mem_get_path_first_step:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b x.
    is_tree g ∧
    b ∈ nodes g ∧
    MEM x (get_path g a b) ∧
    adjacent g a x ⇒
    x = a ∨ x = EL 1 (get_path g a b)
Proof
  rpt strip_tac
  >> ‘a ∈ nodes g’ by metis_tac[adjacent_members]
  >> Cases_on ‘x = a’ >> gvs[]
  >> gvs[MEM_EL]
  >> CCONTR_TAC
  (* Path due to adjacency *)
  >> sg ‘get_path g a (EL n (get_path g a b)) = [a; EL n (get_path g a b)]’
  >- gvs[adjacent_get_path]
  (* Path due to subpath *)
  >> sg ‘get_path g a (EL n (get_path g a b)) = TAKE (n + 1) (get_path g a b)’
  >- (irule is_tree_get_path_unique
      >> gvs[HD_TAKE, LAST_TAKE])
  >> gvs[]
  (* These paths have different lengths so must be different. Contradiction *)
  >> ‘LENGTH (TAKE (n + 1) (get_path g a b)) =
      LENGTH [a; EL n (get_path g a b)]’ by metis_tac[]
  >> gvs[]
  >> Cases_on ‘n’ >> gvs[]
  >> Cases_on ‘n'’ >> gvs[]
QED

Theorem adjacent_mem_get_path_first_step_alt:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b x.
    is_tree g ∧
    b ∈ nodes g ∧
    MEM x (get_path g a b) ∧
    adjacent g a x ∧
    x ≠ a ⇒
    EL 1 (get_path g a b) = x
Proof
  metis_tac[adjacent_mem_get_path_first_step]
QED

(* -------------------------------------------------------------------------- *)
(* The subtree of nodes reachable by taking a certain edge from a certain     *)
(* node is disjoint from the subtree of nodes reachable by taking a different *)
(* edge from that node                                                        *)
(* -------------------------------------------------------------------------- *)
Theorem subtrees_distinct:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph root n m.
    is_tree g ∧
    adjacent g root n ∧
    adjacent g root m ∧
    n ≠ m ∧
    root ≠ n ∧
    root ≠ m ⇒
    (nodes (subtree g root n) ∩ nodes (subtree g root m) = ∅)
Proof
  rpt strip_tac
  >> ‘root' ∈ nodes g ∧ n ∈ nodes g ∧ m ∈ nodes g’ by metis_tac[adjacent_members]
  >> gvs[subtree_def, subgraph_def]
  >> gvs[EXTENSION]
  >> rpt strip_tac
  >> CCONTR_TAC >> gvs[]
  >> ‘EL 1 (get_path g root' x) = n’ by metis_tac[adjacent_mem_get_path_first_step]
  >> ‘EL 1 (get_path g root' x) = m’ by metis_tac[adjacent_mem_get_path_first_step]
  >> metis_tac[]
QED

Theorem subtrees_disjoint:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph root n m.
    is_tree g ∧
    adjacent g root n ∧
    adjacent g root m ∧
    n ≠ m ∧
    root ≠ n ∧
    root ≠ m ⇒
    DISJOINT (nodes (subtree g root n)) (nodes (subtree g root m))
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[DISJOINT_DEF]
  >> irule subtrees_distinct
  >> simp[]
QED

Theorem adjacent_first_step[simp]:
  ∀g a b.
    a ≠ b ∧
    exists_path g a b ⇒
    adjacent g a (EL 1 (get_path g a b))
Proof
  rpt strip_tac
  >> gvs[exists_path_def, get_path_def]
  >> SELECT_ELIM_TAC
  >> conj_tac >- metis_tac[]
  >> rpt strip_tac
  >> Cases_on ‘x’ >> Cases_on ‘vs’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[]
  >> Cases_on ‘t'’ >> gvs[]
  >> gvs[path_def, walk_def]
QED

Theorem hd_not_first_step[simp]:
  ∀g a b.
    a ≠ b ∧
    exists_path g a b ⇒
    (a = EL 1 (get_path g a b) ⇔ F)
Proof
  rpt strip_tac
  (* Because a ≠ b, we know 1 is a valid index in get_path g a b, so our
     theorem makes sense *)
  >> sg ‘1 < LENGTH (get_path g a b)’
  >- (Cases_on ‘get_path g a b’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[])
  (* All the elements are distinct and the zeroth element is a, which
     contradicts the fact that the first element is a. *)
  >> ‘ALL_DISTINCT (get_path g a b) ∧ EL 0 (get_path g a b) = a’ by gvs[]
  (* Use theorem relating ALL_DISTINCT to the EL x being distinct *)
  >> qpat_x_assum ‘ALL_DISTINCT _’ mp_tac
  >> PURE_REWRITE_TAC[EL_ALL_DISTINCT_EL_EQ]
  >> rpt strip_tac
  (* We specifically have EL 0 and EL 1 non-distinct *)
  >> pop_assum $ qspecl_then [‘0’, ‘1’] assume_tac
  >> gvs[]
QED

Theorem nodes_subgraph[simp]:
  ∀g ns.
    ns ⊆ nodes g ⇒
    nodes (subgraph g ns) = ns
Proof
  rpt strip_tac
  >> gvs[subgraph_def]
  >> gvs[DIFF_DIFF_SUBSET]
QED

Theorem HD_TL:
  ∀ls.
    ls ≠ [] ⇒
    HD (TL ls) = EL 1 ls
Proof
  rpt strip_tac
  >> Cases_on ‘ls’ >> gvs[]
QED

Theorem distinct_1_less_len_get_path[simp]:
  ∀g a b.
    exists_path g a b ⇒
    (1 < LENGTH (get_path g a b) ⇔ a ≠ b)
Proof
  rpt strip_tac
  >> Cases_on ‘a = b’ >> gvs[]
  >> Cases_on ‘get_path g a b’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[]
QED

Theorem distinct_2_leq_len_get_path[simp]:
  ∀g a b.
    exists_path g a b ⇒
    (2 ≤ LENGTH (get_path g a b) ⇔ a ≠ b)
Proof
  rpt strip_tac
  >> Cases_on ‘a = b’ >> gvs[]
  >> Cases_on ‘get_path g a b’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* If we have a path a-c, and we have a point b not equal to a on a-c, then   *)
(* the first step on a-b is the first step on a-c.                            *)
(*                                                                            *)
(* This follows from get_path_append, which allows us to split a-c up into    *)
(* a-b followed by b-c.                                                       *)
(* -------------------------------------------------------------------------- *)
Theorem first_step_on_path_same:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ∈ nodes g ∧
    c ∈ nodes g ∧
    a ≠ b ∧
    MEM b (get_path g a c) ⇒
    EL 1 (get_path g a c) = EL 1 (get_path g a b)
Proof
  rpt strip_tac
  >> ‘b ∈ nodes g’ by metis_tac[mem_get_path_in_nodes, is_tree_exists_path]
  >> qspecl_then [‘g’, ‘a’, ‘b’, ‘c’] mp_tac get_path_append
  >> simp[]
  >> strip_tac
  (* This assumption is annoying because the simplifier likes to split
     MEM b (_ ++ _) into two cases, but it's not helpful here. I don't need this
     assumption here so I just get rid of it *)
  >> qpat_x_assum ‘MEM b (get_path g a c)’ kall_tac
  (* *)
  >> gvs[EL_APPEND]
QED

Theorem first_MEM_TL_path:
  ∀g vs.
    path g vs ⇒
    (MEM (HD vs) (TL vs) ⇔ F)
Proof
  rpt strip_tac
  >> Cases_on ‘vs’ >> gvs[]
  >> gvs[path_def]
QED

Theorem first_MEM_TL_get_path[simp]:
  ∀g a b.
    exists_path g a b ⇒
    (MEM a (TL (get_path g a b)) ⇔ F)
Proof
  rpt strip_tac
  >> qspecl_then [‘g’, ‘get_path g a b’] assume_tac first_MEM_TL_path
  >> gvs[]
QED

Theorem MEM_TL_get_path:
  ∀g a b x.
    exists_path g a b ⇒
    (MEM x (TL (get_path g a b)) ⇔ MEM x (get_path g a b) ∧ x ≠ a)
Proof
  rpt strip_tac
  >> Cases_on ‘x = a’ >> gvs[]
  >> Cases_on ‘get_path g a b’ >> gvs[]
  >> gvs[is_tree_get_path_equals_cons]
  >> Cases_on ‘x = h’ >> gvs[]
  >> ‘F’ suffices_by gvs[]
  >> qpat_x_assum ‘h ≠ a’ mp_tac >> simp[]
  >> ‘HD (get_path g a b) = HD (h::t)’ by metis_tac[]
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* In a tree, if a path arrives at a point, and leaves in a different         *)
(* direction to the direction in which it came, then the concatenation of     *)
(* these paths is path.                                                       *)
(*                                                                            *)
(* To prove this, we need to show that the nodes on one side of the path are  *)
(* distinct with respect to the ndoes on the other side of the path. But this *)
(* follows from subtrees_distinct.                                            *)
(* -------------------------------------------------------------------------- *)
Theorem path_continuation:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    c ∈ nodes g ∧
    EL 1 (get_path g b c) ≠ EL 1 (get_path g b a) ⇒
    get_path g a c = get_path g a b ++ TL (get_path g b c)
Proof
  rpt strip_tac
  (* It's helpful to know and easy to prove that b ≠ c ∧ a ≠ c*)
  >> Cases_on ‘b = c’ >> gvs[]
  >> Cases_on ‘a = c’ >> gvs[]
  (* It's also helpful to know a ≠ b*)
  >> Cases_on ‘a = b’ >> gvs[]
  >- (qmatch_goalsub_abbrev_tac ‘avoidrewrite1 = _::avoidrewrite2’
      >> ‘a = HD (get_path g a c)’ by gvs[]
      >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> unabbrev_all_tac
      >> gvs[Excl "exists_path_hd_get_path"]
     )
  (* This may be proven through uniqueness of paths in trees if we prove that
     the right hand side is a path with the correct endpoints. *)
  >> irule is_tree_path_unique
  (* Basic simplifications, and preconditions for basic simpliciations *)
  >> gvs[HD_APPEND_NOT_NIL]
  >> Cases_on ‘TL (get_path g b c) = []’ >> gvs[]
  >- (Cases_on ‘get_path g b c’ >> gvs[])
  >> gvs[LAST_APPEND_NOT_NIL]
  >> sg ‘1 < LENGTH (get_path g b c)’
  >- (Cases_on ‘get_path g b c’ >> gvs[] >> Cases_on ‘t’ >> gvs[])
  >> gvs[LAST_TL]
  >> qexists ‘g’
  >> gvs[]
  (* To prove that our appended path is a path, it suffices to show that each
     subpath is a path and the subpaths are distinct with respect to each
     other.*)
  >> gvs[path_append]
  (* Basic simplifications *)
  >> conj_tac >- (irule path_tl >> gvs[])
  >> conj_tac >- (gvs[HD_TL, adjacent_first_step])
  >> rpt strip_tac
  (* Now we need to show that the two subpaths are distinct with respect to
     each other. We do this by using subtrees_distinct to show that the
     corresponding subtrees when travelling in different directions from the
     point of contact are distinct. *)
  >> qspecl_then [‘g’, ‘b’, ‘EL 1 (get_path g b c)’, ‘EL 1 (get_path g b a)’]
                 assume_tac subtrees_distinct
  >> gvs[]
  (* Break down our definition of subtrees to get an expression in terms of
     paths *)
  >> gvs[subtree_def, subgraph_def]
  >> gvs[DIFF_DIFF_SUBSET]
  >> pop_assum mp_tac >> gvs[EXTENSION]
  (* v is precisely the counterexample which is in the paths in both directions,
     but simultaneously can't be because then it would be in two distinct
     subtrees. *)
  >> qexists ‘v’
  >> ‘v ∈ nodes g’ by metis_tac[is_tree_exists_path, mem_get_path_in_nodes]
  >> gvs[]
  (* Use first_step_on_path_same to show that the first step on b-c is the
     first step on b-v, since v is in b-c *)
  >> qspecl_then [‘g’, ‘b’, ‘v’, ‘c’] assume_tac first_step_on_path_same
  >> gvs[]
  >> Cases_on ‘b = v’ >> gvs[]
  >> ‘MEM v (get_path g b c)’ by metis_tac[MEM_TL]
  >> gvs[]
  (* Use first_step_on_path_same to show that the first step on b-a is the
     first step on b-v, since v is in a-b and hence is in b-a *)
  >> qspecl_then [‘g’, ‘b’, ‘v’, ‘a’] assume_tac first_step_on_path_same
  >> gvs[]
  (* It has done more simplificaiton than I expected: now I have the assumptions
     MEM v a-b and ¬MEM v b-a, which are contradictory. *)
  >> ‘get_path g b a = REVERSE (get_path g a b)’ by gvs[]
  >> metis_tac[MEM_REVERSE]
QED

(* -------------------------------------------------------------------------- *)
(* If a-b arrives at b along one edge and b-c leaves b along a different      *)
(* edge, then b is on a-c.                                                    *)
(* -------------------------------------------------------------------------- *)
Theorem path_continuation_mem:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    c ∈ nodes g ∧
    EL 1 (get_path g b c) ≠ EL 1 (get_path g b a) ⇒
    MEM b (get_path g a c)
Proof
  rpt strip_tac
  (* This is basically the same as path_continuation, so we use that theorem *)
  >> drule_all_then assume_tac path_continuation
  >> gvs[]
QED

Theorem first_step_not_equal_path:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    c ∈ nodes g ∧
    a ≠ b ∧
    b ≠ c ∧
    MEM b (get_path g a c) ⇒
    EL 1 (get_path g b a) ≠ EL 1 (get_path g b c)
Proof
  rpt gen_tac >> strip_tac
  (* By way of contradiction, we assume that the elements on each side are
     identical to each other *)
  >> strip_tac
  (* Split the path at b so that we may see that each of these given components
     are a part of one path, and hence the elements within them will be
     distinct from each other *)
  >> drule_all_then assume_tac get_path_append
  (* The elements in the two paths are distinct *)
  >> sg ‘ALL_DISTINCT (get_path g a b ++ TL (get_path g b c))’
  >- (pop_assum (fn th => PURE_REWRITE_TAC[GSYM th]) >> gvs[])
  >> gvs[ALL_DISTINCT_APPEND]
  (* Use distinctness on the element we expect to be distinct but are assuming
     is not distinct. *)
  >> qmatch_asmsub_abbrev_tac ‘e = EL 1 _’
  >> last_x_assum $ qspecl_then [‘e’] assume_tac
  >> gvs[Abbr ‘e’]
  (* Simplify MEM _ (TL (get_path _ _ _)) *)
  >> gvs[MEM_TL_get_path]
  (* We are aiming to prove that the element is both on the path a-b and b-c.
     Make it more clear that this is what we are trying to do. *)
  >> pop_assum mp_tac
  >> gvs[]
  (* The second requirement is obvious*)
  >> gvs[EL_MEM]
  (* Use the representation of our element as the first element on b-a, because
     this is convenient to prove it is on a-b. *)
  >> qpat_x_assum ‘EL 1 _ = _’ (fn th => gvs[GSYM th])
  (* Reverse b-a to get a-b *)
  >> ‘get_path g b a = REVERSE (get_path g a b)’ by gvs[]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  (* Combine EL and REVERSE *)
  >> gvs[EL_REVERSE]
  (* Clearly an element of a-b is a member of a-b *)
  >> irule EL_MEM
  (* To apply the definition of PRE, we need to know if it is being applied to
     0 or a nonzero value *)
  >> qmatch_abbrev_tac ‘PRE l < _’
  >> Cases_on ‘l’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Allows us to join together partially overlapping paths.                    *)
(* -------------------------------------------------------------------------- *)
(* Theorem:                                                                   *)
(* If we have a-c and b-d, and b is in a-c and c is in b-d, then b and c are  *)
(* in a-d.                                                                    *)
(* -------------------------------------------------------------------------- *)
(* Once we know b and c are in a-d, we can use get_path_append to create      *)
(* a-d by frankensteining together a-c and b-d.                               *)
(* -------------------------------------------------------------------------- *)
(* Proof:                                                                     *)
(*                                                                            *)
(* The points just before b and just after b are not equal to each other      *)
(* because they are each a part of the path a-c.                              *)
(*                                                                            *)
(* Thus, we can use path_continuation_mem to show that b is in a-d.           *)
(* -------------------------------------------------------------------------- *)
Theorem join_overlapping_paths_mem:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c d.
    is_tree g ∧
    a ∈ nodes g ∧
    (b ∈ nodes g ∨ c ∈ nodes g) ∧
    d ∈ nodes g ∧
    MEM b (get_path g a c) ∧
    MEM c (get_path g b d) ∧
    b ≠ c ⇒
    MEM b (get_path g a d)
Proof
  rpt gen_tac >> simp[GSYM AND_IMP_INTRO] >> rpt disch_tac
  >> sg ‘b ∈ nodes g ∧ c ∈ nodes g’
  >- (gvs[]
      >- (irule mem_get_path_in_nodes >> qexistsl [‘b’, ‘d’] >> simp[])
      >> irule mem_get_path_in_nodes >> qexistsl [‘a’, ‘c’] >> simp[])
  (* Special case of a = b *)
  >> Cases_on ‘a = b’ >> gnvs[]
  (* We can prove this by showing that the edge into b is distinct from the
     edge out of b, using path_continuation_mem *)
  >> irule path_continuation_mem
  >> gnvs[]
  (* Since c is on b-d, the first step on b-d is the same as the first step
     on  b-c by first_step_on_path_same *)
  >> qspecl_then [‘g’, ‘b’, ‘c’, ‘d’] assume_tac first_step_on_path_same
  >> gvs[]
  (* Since a-c is a path with b on it, the first element back from b is
     different to the first element forward from b. *)
  >> irule NEQ_SYM
  >> irule first_step_not_equal_path
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* If we have a - b - c, the first step on a - b is a member of a - c         *)
(* -------------------------------------------------------------------------- *)
Theorem mem_first_step_subpath:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ∈ nodes g ∧
    c ∈ nodes g ∧
    MEM b (get_path g a c) ∧
    a ≠ b ⇒
    MEM (EL 1 (get_path g a b)) (get_path g a c)
Proof
  rpt strip_tac
  >> qspecl_then [‘g’, ‘a’, ‘b’, ‘c’] assume_tac first_step_on_path_same
  >> gvs[]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
  >> gvs[MEM_EL]
  >> qexists ‘1’ >> gvs[]
  >> CCONTR_TAC >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* If we have a - b - c, the first step on a - c is a member of a - b         *)
(* -------------------------------------------------------------------------- *)
Theorem mem_first_step_suppath:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ∈ nodes g ∧
    c ∈ nodes g ∧
    MEM b (get_path g a c) ∧
    a ≠ b ⇒
    MEM (EL 1 (get_path g a c)) (get_path g a b)
Proof
  rpt strip_tac
  >> qspecl_then [‘g’, ‘a’, ‘b’, ‘c’] assume_tac first_step_on_path_same
  >> gvs[]
  >> gvs[MEM_EL]
  >> qexists ‘1’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* If the first steps on two paths from the same origin are distinct, then    *)
(* the paths are distinct everywhere except for the origin                    *)
(* -------------------------------------------------------------------------- *)
Theorem first_step_distinct_path_distinct:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph org p1 p2.
    is_tree g ∧
    org ∈ nodes g ∧
    p1 ∈ nodes g ∧
    p2 ∈ nodes g ∧
    org ≠ p1 ∧
    org ≠ p2 ∧
    EL 1 (get_path g org p1) ≠ EL 1 (get_path g org p2) ⇒
    (∀n. n ≠ org ∧ MEM n (get_path g org p1) ⇒ ¬MEM n (get_path g org p2))
Proof
  rpt strip_tac
  (* This theorem is essentially another way of wording subtrees_distinct. *)
  >> qspecl_then [‘g’ ,
                  ‘org’,
                  ‘EL 1 (get_path g org p1)’,
                  ‘EL 1 (get_path g org p2)’] assume_tac subtrees_distinct
  >> gvs[]
  >> pop_assum mp_tac >> gvs[EXTENSION]
  (* The n which is in both subtrees is the n which is in both paths *)
  >> qexists ‘n’
  >> gvs[subtree_def]
  (* n ∈ nodes g *)
  >> ‘n ∈ nodes g’ by metis_tac[mem_get_path_in_nodes, is_tree_exists_path]
  >> gvs[]
  (* The first element on each of these larger paths is an element of the
     smaller path *)
  >> conj_tac
  >> (irule mem_first_step_suppath
      >> gvs[])
QED

Theorem subtree_subset:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ≠ b ∧
    b ≠ c ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    c ∈ nodes (subtree g a b) ⇒
    nodes (subtree g b c) ⊂ nodes (subtree g a b)
Proof
  rpt strip_tac
  >> gvs[subtree_def]
  >> gvs[PSUBSET_DEF]
  >> REVERSE conj_tac
  >- (gvs[EXTENSION] >> rpt strip_tac
      >> qexists ‘b’
      >> gvs[is_tree_get_path_same]
     )
  >> gvs[SUBSET_DEF]
  >> rpt strip_tac
  (* a-b-c and b-c-x are overlapping paths, so we can use the relevant thm *)
  >> qspecl_then [‘g’, ‘a’, ‘b’, ‘c’, ‘x’] assume_tac join_overlapping_paths_mem
  >> gvs[]
QED

Theorem order_subtree_lt:
  ∀g : ('a, 'b, 'c, finiteG, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ≠ b ∧
    b ≠ c ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    c ∈ nodes (subtree g a b) ⇒
    order (subtree g b c) < order (subtree g a b)
Proof
  rpt strip_tac
  >> gvs[gsize_def]
  >> irule CARD_PSUBSET
  >> gvs[subtree_subset]
QED

Theorem is_tree_no_triangle:
  ∀g a b c.
    is_tree g ∧
    a ≠ b ∧
    b ≠ c ∧
    a ≠ c ∧
    adjacent g a b ∧
    adjacent g b c ⇒
    ¬adjacent g c a
Proof
  rpt strip_tac
  >> ‘a ∈ nodes g’ by (irule (cj 1 adjacent_members) >> qexists ‘b’ >> simp[])
  >> ‘b ∈ nodes g’ by (irule (cj 1 adjacent_members) >> qexists ‘c’ >> simp[])
  >> ‘c ∈ nodes g’ by (irule (cj 1 adjacent_members) >> qexists ‘a’ >> simp[])
  >> sg ‘cycle g [a; b; c; a]’
  >- (gvs[cycle_def, cycle_def, walk_def]
      >> conj_tac
      >- (gen_tac >> strip_tac >> simp[])
      >> rpt gen_tac >> strip_tac
      >> gvs[adjacent_iff]
     )
  >> gvs[is_tree_def]
QED

Theorem order_subtree_lt_adjacent:
  ∀g : ('a, 'b, 'c, finiteG, 'e, 'f) udgraph a b c.
    is_tree g ∧
    adjacent g a b ∧
    adjacent g b c ∧
    a ≠ b ∧
    b ≠ c ∧
    a ≠ c ⇒
    order (subtree g b c) < order (subtree g a b)
Proof
  rpt strip_tac
  >> ‘a ∈ nodes g ∧ b ∈ nodes g ∧ c ∈ nodes g’ by metis_tac[adjacent_members]
  (* This is a special case of order_subtree_lt *)
  >> irule order_subtree_lt
  >> gvs[]
  >> gvs[subtree_def]
  (* The path from a - c must be [a; b; c] because this is a path with the right
     start and end points and paths are unique in trees. *)
  >> sg ‘get_path g a c = [a;b;c]’
  >- (qspecl_then [‘g’, ‘a’, ‘c’, ‘[a;b;c]’] assume_tac is_tree_get_path_unique
      >> gvs[]
      >> pop_assum irule
      >> gvs[path_def, walk_def]
      >> rpt strip_tac >> gvs[]
      >> gvs[adjacent_iff]
     )
  (* Proof is trivial from here *)
  >> gvs[]
QED

Theorem nodes_subtree_subset:
  ∀g root n.
    nodes (subtree g root n) ⊆ nodes g
Proof
  rpt strip_tac
  >> simp[subtree_def]
QED

Theorem BAG_FILTER_T[simp]:
  ∀b.
    BAG_FILTER (λe. T) b = b
Proof
  simp[BAG_FILTER_EQ]
QED

Theorem removeNodes_empty[simp]:
  ∀g.
    removeNodes ∅ g = g
Proof
  rpt strip_tac
  >> simp[gengraph_component_equality]
  >> simp[FUN_EQ_THM]
  >> rpt strip_tac
  >> rw[]
QED

Theorem subgraph_nodes[simp]:
  ∀g.
    subgraph g (nodes g) = g
Proof
  rpt strip_tac
  >> gvs[subgraph_def]
QED

Theorem subtree_id:
  ∀g a.
    a ∈ nodes g ∧
    connected g ⇒
    subtree g a a = g
Proof
  rpt strip_tac
  >> simp[subtree_def]
  >> Q.SUBGOAL_THEN ‘nodes g ∩ {v | MEM a (get_path g a v)} = nodes g’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- (simp[EXTENSION]
      >> rpt strip_tac >> EQ_TAC >> rpt strip_tac >> simp[]
      >> gvs[MEM_get_path_first, connected_exists_path]
     )
  >> simp[]
QED

Theorem first_step_in_nodes:
  ∀g a b.
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    is_tree g ∧
    a ≠ b ⇒
    EL 1 (get_path g a b) ∈ nodes g
Proof
  rpt strip_tac
  >> irule path_in_nodes
  >> qexists ‘get_path g a b’
  >> simp[path_get_path]
  >> simp[EL_MEM]
QED

Theorem adjacent_nodes_inter_nodes_subtree:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b.
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    is_tree g ⇒
    (adjacent_nodes g a)
    ∩ nodes (subtree g a b) = if a ≠ b
                              then
                                if adjacent g a b then
                                  {EL 1 (get_path g a b)}
                                else
                                  ∅
                              else
                                {adj_node | adj_node ∈ nodes g ∧
                                            adjacent g a adj_node}
Proof
  rpt strip_tac
  >> simp[Once adjacent_SYM, Cong LHS_CONG]
  >> simp[INTER_DEF]
  >> simp[EXTENSION]
  >> gen_tac
  >> Cases_on ‘a = b’ >> gvs[]
  >- (CCONTR_TAC >> gvs[]
      >> gvs[subtree_id, iffLR is_tree_def]
      >> metis_tac[]
     )
  >> EQ_TAC
  >- (rpt strip_tac
      >> gvs[subtree_def]
      >> qspecl_then [‘g’, ‘a’, ‘x’] assume_tac adjacent_get_path
      >> gvs[]
      >> Cases_on ‘a = x’ >> gvs[]
     )
  >> Cases_on ‘adjacent g a b’ >> simp[] >> disch_tac
  >> gvs[]
  >> simp[subtree_def, first_step_in_nodes]
  >> ‘EL 1 (get_path g a b) = b’ suffices_by simp[]
  >> irule adjacent_mem_get_path_first_step_alt
  >> simp[]
QED

Theorem dst_in_subtree:
  ∀g src dst.
    is_tree g ∧
    src ∈ nodes g ∧
    dst ∈ nodes g ⇒
    dst ∈ nodes (subtree g src dst)
Proof
  rpt strip_tac
  >> simp[subtree_def]
QED

Theorem src_not_in_subtree:
  ∀g src dst.
    is_tree g ∧
    src ≠ dst ⇒
    src ∉ nodes (subtree g src dst)
Proof
  rpt strip_tac
  >> gvs[subtree_def]
QED

Theorem mem_not_swap_first:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ∈ nodes g ∧
    c ∈ nodes g ∧
    a ≠ b ∧
    MEM b (get_path g a c) ⇒
    ¬(MEM a (get_path g b c))
Proof
  rpt strip_tac
  >> ‘b ∈ nodes g’ by metis_tac[mem_get_path_in_nodes, is_tree_exists_path]
  >> qspecl_then [‘g’, ‘a’, ‘b’, ‘c’] assume_tac get_path_append
  >> gvs[]
  (* We have a - c = a - b ++ TL (b - c), and a occurs on a - b and also on
     TL (b - c), thus it occurs twice in a - c, contradiction. *)
  >> ‘path g (get_path g a c)’ by metis_tac[path_get_path]
  >> gvs[path_def, ALL_DISTINCT_APPEND,
         Excl "exists_path_path_get_path", Excl "get_path_all_distinct"]
  >> qpat_x_assum ‘MEM a (get_path g b c)’ mp_tac >> simp[]
  >> gvs[MEM_TL_get_path]
  >> pop_assum $ qspecl_then [‘a’] assume_tac
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* If we take the union of subtrees one level down, excluding a particular    *)
(* subtree, we get back a subtree one level higher, minus the root node.      *)
(* -------------------------------------------------------------------------- *)
Theorem bigunion_image_subtree_delete:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph src prev.
    is_tree g ∧
    ¬selfloops_ok g ∧
    prev ∈ adjacent_nodes g src ⇒
    BIGUNION (IMAGE
              (λdst. nodes (subtree g src dst))
              ((adjacent_nodes g src) DELETE prev)
             ) = (nodes (subtree g prev src)) DELETE src
Proof
  rpt strip_tac
  >> simp[EXTENSION]
  >> gen_tac
  >> EQ_TAC
  (* If x is in the union of subtrees, then x is in the larger subtree *)
  >- (strip_tac
      >> gvs[]
      >> qpat_x_assum ‘∀x. x ∈ s ⇔ _’ kall_tac
      >> Cases_on ‘x = src’
      >- (gvs[]
          >> qpat_x_assum ‘src ∈ nodes (subtree g src dst)’ mp_tac >> simp[]
          >> REVERSE $ Cases_on ‘src = dst’
          >- simp[src_not_in_subtree]
          >> gvs[]
          >> gvs[subtree_id, iffLR is_tree_def]
          >> gvs[GCONTRAPOS adjacent_REFL_E]
         )
      >> simp[]
      >> gvs[subtree_def]
      (* We have:
           src - dst - x
           adjacent prev src
           adjacent dst src
           prev ≠ dst
         We want to prove:
           prev - src - x    (i.e. src is on prev - x)
         We can do this by joining together (join_overlapping_paths_mem):
           prev - src - dst and src - dst - x
         Thus it suffices to show:
           prev - src - dst, which is clear from adjacent_get_path_2_steps or
                             alternatively path_continuation_mem
       *)
      >> irule join_overlapping_paths_mem
      >> simp[]
      >> qexists ‘dst’
      >> simp[]
      >> Cases_on ‘src = dst’ >> simp[]
      >- gvs[GCONTRAPOS adjacent_REFL_E]
      >> qspecl_then [‘g’, ‘prev’, ‘src’, ‘dst’]
                     (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
                     adjacent_get_path_2_steps
      >> conj_tac
      >- (simp[]
          >> simp[adjacent_SYM]
          >> CCONTR_TAC >> gvs[GCONTRAPOS adjacent_REFL_E]
         )
      >> simp[]
     )
  (* If x is in the larger subtree, then x is in the union of subtrees. *)
  >> rpt strip_tac
  (* It's generally helpful to know that the things we are working with are
     valid nodes *)
  >> ‘adjacent g prev src’ by gvs[IN_DEF]
  >> ‘src ∈ nodes g’ by metis_tac[adjacent_members]
  >> ‘prev ∈ nodes g’ by metis_tac[adjacent_members]
  >> ‘x ∈ nodes g’ by gvs[subtree_def]
  >> qexists ‘nodes (subtree g src (EL 1 (get_path g src x)))’
  >> conj_tac
  >- (gvs[subtree_def]
      >> irule EL_MEM
      >> Cases_on ‘get_path g src x’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[]
     )
  >> qexists ‘EL 1 (get_path g src x)’
  >> simp[]
  >> rpt conj_tac
  >- simp[first_step_in_nodes]
  >- simp[adjacent_SYM]
  (* This choice of prev contradicts x ∈ nodes (subtree g prev src) *)
  >> gvs[subtree_def]
  >> CCONTR_TAC >> gvs[]
  (* We have src - FST - x, and we have src is in FST - x, which is a
     contradiction. *)
  >> qpat_x_assum ‘MEM _ _’ mp_tac >> simp[]
  >> irule mem_not_swap_first
  >> simp[]
  >> simp[mem_first_step_subpath]
QED

(* -------------------------------------------------------------------------- *)
(* If we take the union of all trees one level down, we get the entire tree   *)
(* except the root node.                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem bigunion_image_subtree:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph src.
    is_tree g ∧
    src ∈ nodes g ∧
    ¬selfloops_ok g ⇒
    BIGUNION (IMAGE (λdst. nodes (subtree g src dst))
                    (adjacent_nodes g src)
             ) = nodes g DELETE src
Proof
  rpt gen_tac >> strip_tac
  >> simp[EXTENSION]
  >> gen_tac
  >> EQ_TAC >> strip_tac
  >- (qpat_x_assum ‘x ∈ s’ mp_tac >> simp[] >> strip_tac
      >> ‘x ∈ nodes g’ by
        (qpat_x_assum ‘x ∈ nodes (subtree _ _ _)’ mp_tac >> simp[subtree_def])
      >> conj_tac >- pop_assum irule
      >> disch_tac
      >> qpat_x_assum ‘x ∈ nodes (subtree _ _ _)’ mp_tac
      >> simp[]
      >> irule src_not_in_subtree
      >> simp[]
      >> disch_tac
      >> qpat_x_assum ‘¬selfloops_ok g’ mp_tac
      >> PURE_ONCE_REWRITE_TAC[IMP_CLAUSES]
      >> PURE_ONCE_REWRITE_TAC[NOT_CLAUSES]
      >> irule adjacent_REFL_E
      >> qexists ‘dst’
      >> qpat_x_assum ‘adjacent g dst src’ mp_tac >> simp[])
  >> qabbrev_tac ‘dst = EL 1 (get_path g src x)’
  >> qexists ‘nodes (subtree g src dst)’
  >> conj_tac
  >- (Q.UNABBREV_TAC ‘dst’
      >> simp[subtree_def]
      >> irule EL_MEM
      >> simp[])
  >> qexists ‘dst’
  >> simp[]
  >> Q.UNABBREV_TAC ‘dst’
  >> conj_tac
  >- (irule first_step_in_nodes >> simp[])
  >> PURE_ONCE_REWRITE_TAC[adjacent_SYM]
  >> irule adjacent_first_step
  >> simp[]
QED

Theorem get_path_last_step:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    a ≠ b ⇒
    get_path g a (EL 1 (get_path g b a)) = FRONT (get_path g a b)
Proof
  rpt strip_tac
  >> qspecl_then [‘g’, ‘a’, ‘EL 1 (get_path g b a)’, ‘b’] assume_tac get_path_append
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> conj_tac
  >- (simp[]
      >> Q.SUBGOAL_THEN ‘get_path g b a = REVERSE (get_path g a b)’
          (fn th => PURE_ONCE_REWRITE_TAC[th])
      >- simp[get_path_reverse]
      >> simp[EL_REVERSE]
      >> irule EL_MEM
      >> Cases_on ‘LENGTH (get_path g a b)’ >> gvs[]
     )
  >> qmatch_abbrev_tac ‘ls = _’
  >> qsuff_tac ‘TL (get_path g (EL 1 (get_path g b a)) b) =
                [b]’
  >- (disch_then (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[FRONT_APPEND])
  >> DEP_PURE_ONCE_REWRITE_TAC[adjacent_get_path]
  >> conj_tac
  >- (PURE_ONCE_REWRITE_TAC[adjacent_SYM]
      >> simp[adjacent_first_step])
  >> simp[]
QED

(* Based on MEM_LAST_FRONT. Note that MEM_LAST_FRONT unnecessarily requries
   the stronger assumption MEM e l rather than MEM e (h::l) *)
Theorem MEM_LAST_FRONT_ALT:
  ∀x ls.
    MEM x ls ∧
    x ≠ LAST ls ⇒
    MEM x (FRONT ls)
Proof
  rpt strip_tac
  >> Cases_on ‘ls’ >> gvs[]
  >- (simp[FRONT_DEF] >> rw[] >> gvs[LAST_DEF])
  >> irule MEM_LAST_FRONT
  >> simp[]
QED

Theorem mem_front_get_path:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b x.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    a ≠ b ⇒
    (MEM x (FRONT (get_path g a b)) ⇔ MEM x (get_path g a b) ∧ x ≠ b)
Proof
  rpt strip_tac
  >> EQ_TAC >> disch_tac
  >- (Cases_on ‘x = b’
      >- (gvs[]
          >> pop_assum mp_tac >> simp[]
          >> irule MEM_FRONT_NOT_LAST_GEN
          >> simp[get_path_all_distinct]
         )
      >> simp[]
      >> irule MEM_FRONT_NOT_NIL
      >> simp[]
     )
  >> gvs[]
  >> irule MEM_LAST_FRONT_ALT
  >> simp[]
QED

Theorem mem_get_path_last_step:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b x.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    a ≠ b ⇒
    (MEM x (get_path g a (EL 1 (get_path g b a))) ⇔
       MEM x (get_path g a b) ∧ x ≠ b)
Proof
  rpt gen_tac >> strip_tac
  >> simp[get_path_last_step, mem_front_get_path]
QED

(* -------------------------------------------------------------------------- *)
(* If we have b - c - d, with adjacent b c, and also we have adjacent a b,    *)
(* and a ≠ c, then we have a - b - d. That is, we can extend a path at the    *)
(* front by one if the new adjacent node is different to the adjacent node    *)
(* that is already on the path.                                               *)
(* -------------------------------------------------------------------------- *)
Theorem extend_front_adjacent:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c d.
    is_tree g ∧
    d ∈ nodes g ∧
    adjacent g b c ∧
    adjacent g a b ∧
    a ≠ c ∧
    a ≠ b ∧ (* In most circumstances, follows from adjacent g a b *)
    b ≠ c ∧ (* In most circumstances, follows from adjacent g b c *)
    MEM c (get_path g b d) ⇒
    MEM b (get_path g a d)
Proof
  rpt strip_tac
  >> ‘a ∈ nodes g ∧ b ∈ nodes g ∧ c ∈ nodes g’ by metis_tac[adjacent_members]
  >> irule join_overlapping_paths_mem
  >> simp[]
  >> qexists ‘c’
  >> simp[]
  >> sg ‘get_path g a c = [a; b; c]’
  >- (irule adjacent_get_path_2_steps
      >> simp[])
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* a - b - c iff c - b - a                                                    *)
(* -------------------------------------------------------------------------- *)
Theorem mem_get_path_reverse:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    a ∈ nodes g ∧
    c ∈ nodes g ⇒
    (MEM b (get_path g a c) ⇔ MEM b (get_path g c a))
Proof
  rpt strip_tac
  >> metis_tac[get_path_reverse, MEM_REVERSE]
QED

(* -------------------------------------------------------------------------- *)
(* If a - b - d and b - c - d, then a - c - d                                 *)
(* -------------------------------------------------------------------------- *)
Theorem midpoint_push:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c d.
    is_tree g ∧
    a ∈ nodes g ∧
    d ∈ nodes g ∧
    MEM b (get_path g a d) ∧
    MEM c (get_path g b d) ⇒
    MEM c (get_path g a d)
Proof
  rpt strip_tac
  >> Cases_on ‘c = b’ >> simp[]
  >> ‘b ∈ nodes g’ by metis_tac[is_tree_exists_path, mem_get_path_in_nodes]
  >> ‘c ∈ nodes g’ by metis_tac[is_tree_exists_path, mem_get_path_in_nodes]
  >> qspecl_then [‘g’, ‘a’, ‘b’, ‘d’] assume_tac get_path_append
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> simp[]
  >> disj2_tac
  >> simp[MEM_TL_get_path]
QED

(* -------------------------------------------------------------------------- *)
(* If a - c - d and a - b - c, then a - b - d                                 *)
(* -------------------------------------------------------------------------- *)
Theorem midpoint_pull:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c d.
    is_tree g ∧
    a ∈ nodes g ∧
    d ∈ nodes g ∧
    MEM c (get_path g a d) ∧
    MEM b (get_path g a c) ⇒
    MEM b (get_path g a d)
Proof
  rpt strip_tac
  >> Cases_on ‘b = c’ >> simp[]
  >> ‘b ∈ nodes g’ by metis_tac[is_tree_exists_path, mem_get_path_in_nodes]
  >> ‘c ∈ nodes g’ by metis_tac[is_tree_exists_path, mem_get_path_in_nodes]
  >> qspecl_then [‘g’, ‘a’, ‘c’, ‘d’] assume_tac get_path_append
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* If we have a - b - d and b - c - d, then a - b - c                         *)
(* -------------------------------------------------------------------------- *)
Theorem restrict_overlapping_pull:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c d.
    is_tree g ∧
    a ∈ nodes g ∧
    d ∈ nodes g ∧
    MEM b (get_path g a d) ∧
    MEM c (get_path g b d) ⇒
    MEM b (get_path g a c)
Proof
  rpt strip_tac
  >> ‘b ∈ nodes g’ by (irule mem_get_path_in_nodes >> qexistsl [‘a’, ‘d’]
                       >> simp[])
  >> ‘c ∈ nodes g’ by (irule mem_get_path_in_nodes >> qexistsl [‘b’, ‘d’]
                       >> simp[])
  (* a - c - d by midpoint_push.
     Thus we can split up a - d into a - c ++ c - d
     So either a - b - d or c - b - d
     But the latter contradicts b - c - d *)
  >> ‘MEM c (get_path g a d)’ by metis_tac[midpoint_push]
  >> ‘get_path g a d = get_path g a c ++ TL (get_path g c d)’
    by (irule get_path_append >> simp[])
  >> gvs[]
  >> gvs[MEM_TL_get_path]
  >> metis_tac[mem_not_swap_first]
QED

(* -------------------------------------------------------------------------- *)
(* If we have a - b - c and b - c - d, then b - c - d                         *)
(* -------------------------------------------------------------------------- *)
Theorem restrict_overlapping_push:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c d.
    is_tree g ∧
    a ∈ nodes g ∧
    d ∈ nodes g ∧
    MEM b (get_path g a d) ∧
    MEM c (get_path g b d) ⇒
    MEM b (get_path g a c)
Proof
  metis_tac[restrict_overlapping_pull, mem_get_path_reverse]
QED

(* -------------------------------------------------------------------------- *)
(* If a ~ b then either b = EL 1 (a - c) or a = EL 1 (b - c)                  *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_is_first_step:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c.
    is_tree g ∧
    c ∈ nodes g ∧
    adjacent g a b ∧
    a ≠ b ⇒
    b = EL 1 (get_path g a c) ∨ a = EL 1 (get_path g b c)
Proof
  rpt strip_tac
  >> ‘a ∈ nodes g’ by (irule (cj 1 adjacent_members) >> qexists ‘b’ >> simp[])
  >> ‘b ∈ nodes g’ by (irule (cj 2 adjacent_members) >> qexists ‘a’ >> simp[])
  >> Cases_on ‘b = c’
  >- (gvs[]
      >> ‘get_path g a b = [a;b]’ by (irule adjacent_get_path >> simp[])
      >> simp[])
  (* We have a ~ b
     We have b ~ EL 1 (b - c)
     In case where EL 1 (b - c) = a we are done
     Otherwise, we get a ~ b ~ EL 1 (b - c)
     We also have b ~ EL 1 (b - c) - c
     We can join these together to get a ~ b - c
     Now our adjacent first step is a member of the path, so we can use
     adjacent_mem_get_path_first_step_alt to solve.
   *)
  >> ‘adjacent g b (EL 1 (get_path g b c))’
    by (irule adjacent_first_step >> simp[])
  >> Cases_on ‘a = EL 1 (get_path g b c)’ >> simp[]
  >> qmatch_asmsub_abbrev_tac ‘adjacent _ _ first_step’
  >> ‘first_step ∈ nodes g’
    by (unabbrev_all_tac >> irule first_step_in_nodes >> simp[])
  >> ‘get_path g a first_step = [a;b;first_step]’
    by (irule adjacent_get_path_2_steps >> simp[]
        >> disch_tac
        >> qpat_x_assum ‘Abbrev (first_step = _)’ mp_tac
        >> simp[Abbrev_def]
        >> DEP_PURE_ONCE_REWRITE_TAC[hd_not_first_step]
        >> simp[]
        >> disch_tac
        >> gvs[])
  >> ‘MEM b (get_path g a first_step)’ by simp[]
  >> ‘MEM first_step (get_path g b c)’
    by (simp[Abbr ‘first_step’] >> simp[MEM_EL] >> qexists ‘1’ >> simp[])
  >> ‘MEM b (get_path g a c)’
    by (irule join_overlapping_paths_mem
        >> simp[]
        >> qexists ‘first_step’
        >> simp[]
        >> disch_tac >> gvs[Abbrev_def])
  >> SYM_TAC
  >> irule adjacent_mem_get_path_first_step_alt
  >> simp[]
QED

Theorem first_step_is_last:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    a ≠ b ∧
    b = EL 1 (get_path g a b) ⇒
    adjacent g a b ∧ get_path g a b = [a; b]
Proof
  rpt gen_tac >> strip_tac
  >> ‘adjacent g a b’ suffices_by
    (disch_tac
     >> simp[]
     >> irule adjacent_get_path >> simp[])
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> irule adjacent_first_step
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* If a - b - c and adjacent c d, then a - b - d unless d is the first on     *)
(* b - a.                                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem move_end_to_adjacent:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c d.
    is_tree g ∧
    a ∈ nodes g ∧
    MEM b (get_path g a c) ∧
    adjacent g c d ∧
    EL 1 (get_path g b a) ≠ d ⇒
    MEM b (get_path g a d)
Proof
  rpt strip_tac
  >> ‘c ∈ nodes g’ by (irule (cj 1 adjacent_members) >> qexists ‘d’ >> simp[])
  >> ‘b ∈ nodes g’ by (irule mem_get_path_in_nodes >> qexistsl [‘a’, ‘c’]
                       >> simp[])
  >> ‘d ∈ nodes g’ by (irule (cj 2 adjacent_members) >> qexists ‘c’ >> simp[])
  (* Special case of b = d *)
  >> Cases_on ‘b = d’
  >- simp[]
  (* Special case of c = d *)
  >> Cases_on ‘c = d’
  >- gvs[]
  (* Special case of a = d *)
  >> Cases_on ‘a = d’
  >- (gvs[]
      >> ‘get_path g a c = [a;c]’ by
        (irule adjacent_get_path
         >> PURE_ONCE_REWRITE_TAC[adjacent_SYM] >> simp[])
      >> gvs[]
      >> ‘get_path g b a = [b;a]’ by
        (irule adjacent_get_path >> simp[])
      >> gvs[])
  (* We have a - b - c and c ~ d
     d is either just before c or just after. *)
  >> qspecl_then [‘g’, ‘c’, ‘d’, ‘a’]  mp_tac adjacent_is_first_step
  >> simp[]
  >> REVERSE strip_tac
  (* We have a - b - c and c = EL 1 (d - a).
     Therefore a - c - d
     Therefore a - b - d *)
  >- (sg ‘MEM c (get_path g a d)’
      >- (simp[]
          >> irule (iffLR mem_get_path_reverse)
          >> simp[]
          >> irule EL_MEM
          >> simp[])
      >> irule midpoint_pull >> simp[] >> qexists ‘c’ >> simp[])
  (* We have a - b - c and d = EL 1 (c - a) *)
  >> Cases_on ‘b = c’
  >- (qpat_x_assum ‘EL 1 _ ≠ d’ mp_tac >> simp[])
  >> Cases_on ‘a = c’
  >- (qpat_x_assum ‘MEM b (get_path g a c)’ mp_tac >> simp[])
  >> simp[]
  >> simp[mem_get_path_last_step]
QED

(* -------------------------------------------------------------------------- *)
(* If a - b - c and adjacent a b and adjacent c d, then a - b - d unless      *)
(* d = a.                                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem move_end_to_adjacent_adjacent:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c d.
    is_tree g ∧
    a ∈ nodes g ∧
    MEM b (get_path g a c) ∧
    adjacent g c d ∧
    adjacent g a b ∧
    a ≠ d ⇒
    MEM b (get_path g a d)
Proof
  rpt strip_tac
  >> ‘b ∈ nodes g’ by (irule (cj 2 adjacent_members) >> qexists ‘a’ >> simp[])
  >> ‘c ∈ nodes g’ by (irule (cj 1 adjacent_members) >> qexists ‘d’ >> simp[])
  >> ‘d ∈ nodes g’ by (irule (cj 2 adjacent_members) >> qexists ‘c’ >> simp[])
  >> Cases_on ‘a = b’
  >- (simp[] >> irule MEM_get_path_first >> simp[])
  >> irule move_end_to_adjacent
  >> simp[]
  >> ‘get_path g b a = [b;a]’
    by (irule adjacent_get_path
        >> PURE_ONCE_REWRITE_TAC[adjacent_SYM] >> simp[])
  >> simp[]
  >> qexists ‘c’ >> simp[]
QED

Theorem in_subtree_adjacent:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph x x' a b.
    is_tree g ∧
    a ∈ nodes g ∧
    adjacent g x x' ∧
    x ∈ nodes (subtree g a b) ∧
    x' ≠ EL 1 (get_path g b a) ⇒
    x' ∈ nodes (subtree g a b)
Proof
  rpt gen_tac >> PURE_REWRITE_TAC[GSYM AND_IMP_INTRO]  >> rpt disch_tac
  >> ‘x ∈ nodes g’ by (irule (cj 1 adjacent_members) >> qexists ‘x'’ >> simp[])
  >> ‘x' ∈ nodes g’ by (irule (cj 2 adjacent_members) >> qexists ‘x’ >> simp[])
  >> qpat_x_assum ‘x ∈ nodes (subtree _ _ _)’ mp_tac
  >> simp[subtree_def] >> disch_tac
  >> irule move_end_to_adjacent
  >> simp[]
  >> qexists ‘x’ >> simp[]
QED

Theorem in_subtree_adjacent_adjacent:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph x x' a b.
    is_tree g ∧
    a ∈ nodes g ∧
    adjacent g x x' ∧
    adjacent g a b ∧
    x ∈ nodes (subtree g a b) ∧
    x' ≠ a ⇒
    x' ∈ nodes (subtree g a b)
Proof
  rpt gen_tac >> PURE_REWRITE_TAC[GSYM AND_IMP_INTRO]  >> rpt disch_tac
  >> ‘x ∈ nodes g’ by (irule (cj 1 adjacent_members) >> qexists ‘x'’ >> simp[])
  >> ‘x' ∈ nodes g’ by (irule (cj 2 adjacent_members) >> qexists ‘x’ >> simp[])
  >> qpat_x_assum ‘x ∈ nodes (subtree _ _ _)’ mp_tac
  >> simp[subtree_def] >> disch_tac
  >> irule move_end_to_adjacent_adjacent
  >> simp[]
  >> qexists ‘x’ >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* If a node is in an edge which has nonzero multiplicty in the graph, then   *)
(* that node is a valid node.                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem core_incident_edgebag_nodes:
  ∀g e x.
    x ∈ core_incident e ∧
    BAG_IN e (edgebag g) ⇒
    x ∈ nodes g
Proof
  rpt gen_tac >> strip_tac
  >> drule core_incident_SUBSET_nodes
  >> simp[SUBSET_DEF]
QED

Theorem BAG_FILTER_CONG:
  ∀P Q B.
    BAG_FILTER P B = BAG_FILTER Q B ⇔
      (∀b. BAG_IN b B ⇒ P b = Q b)
Proof
  rpt gen_tac
  >> PURE_REWRITE_TAC[BAG_FILTER_DEF, FUN_EQ_THM]
  >> EQ_TAC
  >- (strip_tac
      >> rpt gen_tac >> strip_tac
      >> last_x_assum $ qspecl_then [‘b’] assume_tac
      >> Cases_on ‘P b’ >> Cases_on ‘Q b’ >> gvs[BAG_IN, BAG_INN])
  >> strip_tac
  >> qx_gen_tac ‘e’ >> simp[]
  >> last_x_assum $ qspecl_then [‘e’] assume_tac
  >> Cases_on ‘P e’ >> Cases_on ‘Q e’ >> gvs[BAG_IN, BAG_INN]
QED

Theorem removeNodes_restrict:
  ∀g ns.
    removeNodes ns g = removeNodes (ns ∩ nodes g) g
Proof
  rpt gen_tac
  >> simp[gengraph_component_equality]
  >> rpt conj_tac
  >- simp[DIFF_INTER2]
  >- (simp[BAG_FILTER_CONG]
      >> gen_tac >> strip_tac
      >> simp[DISJOINT_ALT]
      >> EQ_TAC >> strip_tac >> gen_tac >> strip_tac >> simp[]
      >> disch_tac
      >> last_x_assum drule
      >> simp[]
      >> irule core_incident_edgebag_nodes
      >> qexists ‘e’ >> simp[])
  >> PURE_REWRITE_TAC[FUN_EQ_THM]
  >> qx_gen_tac ‘e’
  >> simp[]
  >> Cases_on ‘e ∈ nodes g’ >> simp[]
QED
 
(* -------------------------------------------------------------------------- *)
(* This works with more general graphs than adjacent_removeNode               *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_removeNode_imp:
  ∀n g v1 v2.
    adjacent (removeNode n g) v1 v2 ⇒
    adjacent g v1 v2 ∧ v1 ≠ n ∧ v2 ≠ n
Proof
  rpt gen_tac >> strip_tac
  >> drule adjacent_members
  >> simp[]
  >> strip_tac
  >> gvs[adjacent_def]
  >> (qexistsl [‘e’, ‘ms’, ‘ns’] >> simp[])
QED

Theorem adjacent_removeNodes_imp:
  ∀ns g v1 v2.
    adjacent (removeNodes ns g) v1 v2 ⇒
    adjacent g v1 v2 ∧ v1 ∉ ns ∧ v2 ∉ ns
Proof
  rpt gen_tac >> strip_tac
  >> drule adjacent_members
  >> simp[]
  >> strip_tac
  >> gvs[adjacent_def]
  >> (qexistsl [‘e’, ‘ms’, ‘ns'’] >> simp[])
QED

(* -------------------------------------------------------------------------- *)
(* Tells us how adjacency changes when a node is removed.                     *)
(*                                                                            *)
(* We require that our graph is not a hypergraph, because in the case of a    *)
(* hypergraph, it may be that there's an edge between a, b, and c, and        *)
(* removing the node b removes this edge, hence causing a and c to become     *)
(* nonadjacent when previously they were adjacent.                            *)
(*                                                                            *)
(* TODO: Maybe this can be generalised to work with an arbitrary graph that   *)
(* satisfies ¬is_hypergraph g, rather than only with fsgraphs                  *)
(*                                                                            *)
(* Tag: Possibly move to different file                                       *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_removeNode:
  ∀n g : fsgraph v1 v2.
    adjacent (removeNode n g) v1 v2 ⇔
      adjacent g v1 v2 ∧ v1 ≠ n ∧ v2 ≠ n
Proof
  rpt gen_tac
  >> EQ_TAC >> strip_tac
  >- (irule adjacent_removeNode_imp >> simp[])
  >> gvs[adjacent_def]
  >> qexistsl [‘e’, ‘ms’, ‘ns’] >> simp[]
  >> Cases_on ‘e’ >> gvs[]
QED

Theorem adjacent_removeNodes:
  ∀ns g : fsgraph v1 v2.
    adjacent (removeNodes ns g) v1 v2 ⇔
      adjacent g v1 v2 ∧ v1 ∉ ns ∧ v2 ∉ ns
Proof
  rpt gen_tac
  >> EQ_TAC >> strip_tac
  >- (irule adjacent_removeNodes_imp >> simp[])
  >> gvs[adjacent_def]
  >> qexistsl [‘e’, ‘ms’, ‘ns'’] >> simp[]
  >> Cases_on ‘e’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* This works with more general graphs than walk_removeNode.                  *)
(* -------------------------------------------------------------------------- *)
Theorem walk_removeNode_imp_full:
  ∀n g ns.
    walk (removeNode n g) ns ⇒
    walk g ns ∧ ¬MEM n ns
Proof
  rpt gen_tac >> strip_tac
  >> gvs[walk_def]
  >> strip_tac
  >- (rpt gen_tac
      >> strip_tac
      >> last_x_assum drule
      >> strip_tac
      >> irule (cj 1 adjacent_removeNode_imp)
      >> qexists ‘n’ >> simp[])
  >> disch_tac
  >> last_x_assum drule
  >> simp[]
QED

Theorem walk_removeNode_imp:
  ∀n g vs.
    walk (removeNode n g) vs ⇒
    walk g vs
Proof
  rpt gen_tac >> strip_tac
  >> gvs[walk_def]
  >> rpt gen_tac
  >> strip_tac
  >> last_x_assum drule
  >> strip_tac
  >> irule (cj 1 adjacent_removeNode_imp)
  >> qexists ‘n’ >> simp[]
QED


(* -------------------------------------------------------------------------- *)
(* TODO: Maybe this can be generalised to work with an arbitrary graph that   *)
(* satisfies ¬is_hypergraph g, rather than only with fsgraphs                 *)
(* -------------------------------------------------------------------------- *)
Theorem walk_removeNode:
  ∀n g : fsgraph ns.
    walk (removeNode n g) ns ⇔
      walk g ns ∧ ¬MEM n ns
Proof
  rpt gen_tac
  >> EQ_TAC >> strip_tac
  >- (irule walk_removeNode_imp_full >> simp[])
  >> gvs[walk_def]
  >> rpt gen_tac
  >> strip_tac
  >> simp[adjacent_removeNode]
  >> ‘MEM v1 ns ∧ MEM v2 ns’
    suffices_by (strip_tac >> conj_tac >> disch_tac >> gvs[])
  >> irule adjacent_MEM
  >> simp[]
QED

Theorem path_removeNode_imp:
  ∀n g vs.
    path (removeNode n g) vs ⇒
    path g vs
Proof
  rpt gen_tac
  >> strip_tac
  >> gvs[path_def]
  >> irule walk_removeNode_imp >> qexists ‘n’ >> simp[]
QED

Theorem exists_path_removeNode_imp:
  ∀n g a b.
    exists_path (removeNode n g) a b ⇒
    exists_path g a b
Proof
  rpt gen_tac >> strip_tac
  >> gvs[exists_path_def]
  >> qexists ‘vs’
  >> simp[]
  >> irule path_removeNode_imp
  >> qexists ‘n’ >> pop_assum irule
QED

Theorem CARD_ONE_SING_DEF:
  ∀S.
    FINITE S ⇒
    (CARD S = 1 ⇔ ∃x. S = {x})
Proof
  gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[GSYM SING_DEF]
  >> simp[SING_IFF_CARD1]
QED

Theorem INSERT_EQ_SING:
  ∀l ls x.
    l INSERT ls = {x} ⇔ l = x ∧ (ls = ∅ ∨ ls = {x})
Proof
  rpt gen_tac
  >> Cases_on ‘l ∈ ls’
  >- (simp[ABSORPTION_RWT]
      >> EQ_TAC >> simp[]
      >> strip_tac
      >> gvs[])
  >> Cases_on ‘ls’ >> gvs[]
  >> sg ‘l INSERT x' INSERT t = {x} ⇔ F’
  >- (simp[]
      >> disch_then (fn th => assume_tac (GSYM th))
      >> ‘FINITE {x}’ by simp[]
      >> ‘CARD {x} = 1’ by simp[]
      >> NTAC 2 (pop_assum mp_tac)
      >> pop_assum (fn th => PURE_REWRITE_TAC[th])
      >> simp[])
  >> simp[]
  >> strip_tac
  >> gvs[]
  >> disch_tac
  >> gvs[]
QED

Theorem CARD_ONE_CHOOSE_ELT_OLD:
  ∀S.
    FINITE S ⇒
    (CARD S = 1 ⇔ S ≠ ∅ ∧ ∃x. ∀y. y ∈ S ⇒ y = x)
Proof
  gen_tac >> strip_tac
  >> simp[CARD_ONE_SING_DEF]
  >> EQ_TAC
  >- (strip_tac
      >> Cases_on ‘S'’ >> gvs[]
      >> qexists ‘x’ >> gen_tac >> strip_tac >> gvs[] >> gvs[INSERT_EQ_SING])
  >> strip_tac
  >> qexists ‘x’
  >> PURE_ONCE_REWRITE_TAC[EXTENSION]
  >> gen_tac
  >> EQ_TAC >> simp[]
  >> strip_tac
  >> Cases_on ‘S'’ >> gvs[]
QED

Theorem CARD_ONE_CHOOSE_ELT:
  ∀S.
    FINITE S ⇒
    (CARD S = 1 ⇔ ∃x. x ∈ S ∧ ∀y. y ∈ S ⇒ y = x)
Proof
  rpt gen_tac >> strip_tac
  >> simp[CARD_ONE_CHOOSE_ELT_OLD]
  >> Cases_on ‘S'’ >> simp[]
  >> EQ_TAC >> strip_tac
  >- (qexists ‘x’ >> simp[] >> gen_tac >> strip_tac >> last_x_assum irule >> simp[])
  >- (qexists ‘x’ >> gen_tac >> strip_tac >>
      first_x_assum $ qspecl_then [‘y’] assume_tac >> simp[])
  >> qexists ‘x’
  >> gen_tac >> strip_tac
  >> first_x_assum $ qspecl_then [‘x’] assume_tac >> gvs[]
QED

Theorem finite_in_fsgedges_with_specific_element[simp]:
  ∀g n.
    FINITE {e | e ∈ fsgedges g ∧ n ∈ e}
Proof
  rpt gen_tac
  >> irule SUBSET_FINITE
  >> qexists ‘fsgedges g’
  >> simp[SUBSET_DEF]
QED

Theorem degree_one_exists_adjacent:
  ∀g a.
    degree g a = 1 ⇒ ∃m. adjacent g a m
Proof
  rpt gen_tac
  >> strip_tac
  >> gvs[degree_def]
  >> gvs[CARD_ONE_CHOOSE_ELT]
  >> drule alledges_valid >> strip_tac
  >> gvs[]
  >- (qexists ‘b’
      >> qpat_x_assum ‘_ ∈ fsgedges _’ mp_tac
      >> PURE_ONCE_REWRITE_TAC[fsgedges_def]
      >> simp[]
      >> strip_tac
      >> gvs[INSERT2_lemma]
      >> PURE_ONCE_REWRITE_TAC[adjacent_SYM]
      >> simp[])
  >> qexists ‘a'’
  >> qpat_x_assum ‘_ ∈ fsgedges _’ mp_tac
  >> PURE_ONCE_REWRITE_TAC[fsgedges_def]
  >> simp[]
  >> strip_tac
  >> gvs[INSERT2_lemma]
  >> PURE_ONCE_REWRITE_TAC[adjacent_SYM]
  >> simp[]
QED

Theorem adjacent_imp_not_equal:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f, 'g, noSL) graph a b.
    adjacent g a b ⇒ a ≠ b
Proof
  rpt gen_tac >> strip_tac
  >> disch_tac >> gvs[]
QED

Theorem adjacent_el_el:
  ∀ls : α list n m.
    m < LENGTH ls ∧
    m = n + 1 ⇒
    adjacent ls (EL n ls) (EL m ls)
Proof
  Induct_on ‘ls’ >> gvs[]
  >> rpt gen_tac >> strip_tac
  >> Cases_on ‘ls’ >> gvs[]
  >> simp[adjacent_iff]
  >> last_x_assum $ qspecl_then [‘n - 1’] assume_tac
  >> gvs[ADD1]
  >> Cases_on ‘t’ >> gvs[]
  >- (Cases_on ‘n’ >> gvs[])
  >> Cases_on ‘n’ >> gvs[]
  >> gvs[GSYM ADD1]
  >> gvs[EL]
QED

(* -------------------------------------------------------------------------- *)
(* If a node has degree one and it is in a path, then it is the first or last *)
(* element                                                                    *)
(* -------------------------------------------------------------------------- *)
Theorem degree_one_hd_last_path:
  ∀g : fsgraph n vs.
    degree g n = 1 ∧
    path g vs ∧
    MEM n vs ⇒
    n = HD vs ∨ n = LAST vs
Proof
  rpt gen_tac
  >> strip_tac
  >> gvs[MEM_EL]
  >> Cases_on ‘vs = []’ >- gvs[]
  >> simp[LAST_EL]
  >> PURE_ONCE_REWRITE_TAC[GSYM (cj 1 EL)]
  >> CCONTR_TAC >> gvs[]
  >> ‘n' ≠ PRE (LENGTH vs)’ by (disch_tac >> gvs[])
  >> ‘n' ≠ 0’ by (disch_tac >> gvs[])
  (* EL (n' - 1) and EL (n' + 1) are both adjacent to EL n', but the
             degree is 1 so that's a contradiction. *)
  >> sg ‘adjacent g (EL (n' - 1) vs) (EL n' vs)’
  >- (gvs[path_def, walk_def]
      >> first_x_assum irule
      >> irule adjacent_el_el
      >> simp[]
     )
  >> sg ‘adjacent g (EL n' vs) (EL (n' + 1) vs)’
  >- (gvs[path_def, walk_def]
      >> first_x_assum irule
      >> irule adjacent_el_el
      >> simp[]
     )
  >> sg ‘EL (n' - 1) vs ≠ EL (n' + 1) vs’
  >- (gvs[path_def]
      >> gvs[EL_ALL_DISTINCT_EL_EQ])
  >> gvs[degree_def, CARD_ONE_CHOOSE_ELT]
  >> last_assum $ qspecl_then [‘{EL n' vs; EL (n' + 1) vs}’] assume_tac
  >> last_x_assum $ qspecl_then [‘{EL n' vs; EL (n' - 1) vs}’] assume_tac
  >> gvs[]
  >> sg ‘{EL n' vs; EL (n' + 1) vs} ∈ fsgedges g’
  >- (simp[fsgedges_def]
      >> qexistsl [‘EL n' vs’, ‘EL (n' + 1) vs’]
      >> simp[]
      >> gvs[])
  >> sg ‘{EL n' vs; EL (n' - 1) vs} ∈ fsgedges g’
  >- (simp[fsgedges_def]
      >> qexistsl [‘EL n' vs’, ‘EL (n' - 1) vs’]
      >> simp[]
      >> PURE_ONCE_REWRITE_TAC[adjacent_SYM]
      >> simp[])
  >> gvs[]
  >> gvs[INSERT2_lemma]
QED

Theorem path_removeNode_degree_one:
  ∀g : fsgraph n vs.
    degree g n = 1 ∧
    n ≠ HD vs ∧
    n ≠ LAST vs ⇒
    (path (removeNode n g) vs ⇔ path g vs)
Proof
  rpt gen_tac >> strip_tac
  >> EQ_TAC
  >- (strip_tac >> irule path_removeNode_imp >> qexists ‘n’ >> simp[])
  >> strip_tac
  (* If the removed node isn't in the path, we can simply use the same path, and
     it will remain a path *)
  >> REVERSE $ Cases_on ‘MEM n vs’ >> simp[]
  >- (gvs[path_def, walk_def]
      >> rpt gen_tac >> strip_tac
      >> simp[adjacent_removeNode]
      >> conj_tac >> disch_tac >> gvs[]
      >> drule adjacent_MEM
      >> simp[])
  (* If the removed node is in the path, since it has degree one, it must be
     either the first or last element *)
  >> drule_all degree_one_hd_last_path
  >> simp[]
QED

Theorem exists_path_removeNode_degree_one:
  ∀g : fsgraph n a b.
    degree g n = 1 ∧
    a ≠ n ∧
    b ≠ n ⇒
    (exists_path (removeNode n g) a b ⇔
       exists_path g a b)
Proof
  rpt gen_tac
  >> strip_tac
  >> EQ_TAC >> strip_tac
  >- (irule exists_path_removeNode_imp
      >> qexists ‘n’ >> simp[])
  >> gvs[exists_path_def]
  >> qexists ‘vs’ >> simp[path_removeNode_degree_one]
QED

Theorem connected_removeNode_degree_one:
  ∀g : fsgraph n.
    degree g n = 1 ⇒
  (connected (removeNode n g) ⇔ connected g)
Proof
  rpt gen_tac >> strip_tac
  >> simp[connected_exists_path]
  >> EQ_TAC >> strip_tac >> rpt gen_tac >> strip_tac
  >- (Cases_on ‘a ≠ n ∧ b ≠ n’
      >- (last_x_assum $ qspecl_then [‘a’, ‘b’] assume_tac
          >> gvs[]
          >> irule exists_path_removeNode_imp
          >> qexists ‘n’ >> pop_assum irule)
      >> wlog_tac ‘a = n’ [‘a’, ‘b’]
      >- (first_x_assum $ qspecl_then [‘b’, ‘a’] assume_tac
          >> PURE_ONCE_REWRITE_TAC[exists_path_sym]
          >> pop_assum irule
          >> simp[]
          >> gvs[])
      >> gvs[]
      >> drule degree_one_exists_adjacent >> strip_tac
      >> Cases_on ‘a = m’ >- gvs[]
      >> last_x_assum $ qspecl_then [‘m’, ‘b’] assume_tac
      >> ‘m ∈ nodes g’ by (irule (cj 2 adjacent_members) >> qexists ‘a’ >> simp[])
      >> gvs[]
      >> Cases_on ‘a = b’ >> gvs[]
      >> gvs[exists_path_def]
      (* a cannot be in vs because it is a path in removeNode a g) *)
      >> Cases_on ‘MEM a vs’
      >- (gvs[path_def, walk_def] >> last_x_assum drule >> simp[])
      >> qexists ‘a::vs’
      >> simp[path_cons]
      >> Cases_on ‘vs = []’ >- gvs[]
      >> drule path_removeNode_imp >> strip_tac
      >> simp[]
      >> Cases_on ‘vs’ >- gvs[] >> simp[]
     )
  >> last_x_assum $ qspecl_then [‘a’, ‘b’] assume_tac
  >> gvs[]
  >> simp[exists_path_removeNode_degree_one]
QED

Theorem cycle_removeNode_imp:
  ∀g n vs.
    cycle (removeNode n g) vs ⇒
    cycle g vs
Proof
  rpt gen_tac >> strip_tac
  >> gvs[cycle_def]
  >> irule walk_removeNode_imp >> qexists ‘n’ >> simp[]
QED

Theorem degree_one_adjacent_unique:
  ∀g n m1 m2.
    degree g n = 1 ∧
    adjacent g n m1 ∧
    adjacent g n m2 ⇒
    m1 = m2
Proof
  rpt gen_tac >> strip_tac
  >> gvs[degree_def]
  >> gvs[CARD_ONE_CHOOSE_ELT]
  >> last_assum $ qspecl_then [‘{n; m1}’] assume_tac
  >> last_x_assum $ qspecl_then [‘{n; m2}’] assume_tac
  >> gvs[adjacent_fsg]
  >> gvs[INSERT2_lemma]
QED

Theorem degree_one_alt:
  ∀g n.
    degree g n = 1 ⇔
      ∃m. adjacent g n m ∧ ∀m2. adjacent g n m2 ⇒ m2 = m
Proof
  rpt gen_tac
  >> EQ_TAC
  >- (strip_tac
      >> drule degree_one_exists_adjacent
      >> strip_tac
      >> qexists ‘m’
      >> simp[]
      >> gen_tac
      >> strip_tac
      >> irule degree_one_adjacent_unique >> qexistsl [‘g’, ‘n’] >> simp[])
  >> strip_tac
  >> simp[degree_def]
  >> simp[CARD_ONE_CHOOSE_ELT]
  >> qexists ‘{n; m}’
  >> conj_tac
  >- (simp[]
      >> simp[GSYM adjacent_fsg])
  >> gen_tac >> strip_tac
  >> gvs[fsgedges_def]
  >> simp[INSERT2_lemma]
  >> Cases_on ‘m' = n’ >- gvs[]
  >> simp[]
  >> qpat_x_assum ‘adjacent _ m' n’ mp_tac
  >> PURE_ONCE_REWRITE_TAC[adjacent_SYM]
  >> simp[]
QED

Theorem adjacent_el_el_graph:
  ∀g n m vs.
    path g vs ∧
    m = n + 1 ∧
    m < LENGTH vs ⇒
    adjacent g (EL n vs) (EL m vs) 
Proof
  rpt gen_tac >> strip_tac
  >> gvs[path_def, walk_def]
  >> last_x_assum irule
  >> irule adjacent_el_el
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* Removing a leaf node cannot affect a cycle                                 *)
(* -------------------------------------------------------------------------- *)
Theorem cycle_removeNode_degree_one:
  ∀g : fsgraph n vs.
    degree g n = 1 ⇒
    (cycle (removeNode n g) vs ⇔ cycle g vs)
Proof
  rpt gen_tac >> strip_tac
  >> EQ_TAC
  >- (strip_tac >> irule cycle_removeNode_imp >> qexists ‘n’ >> simp[])
  >> strip_tac
  >> gvs[cycle_alt]
  >> simp[adjacent_removeNode]
  >> DEP_PURE_ONCE_REWRITE_TAC[path_removeNode_degree_one]
  >> simp[]
  >> Cases_on ‘vs = []’ >- gvs[]
  >> simp[LAST_TL]
  >> ‘n ≠ HD (TL vs) ∧ n ≠ LAST vs’ suffices_by simp[]
  (* In each of these cases, we will be able to find two adjacent nodes in the
     cycle that are nonequal, contradicting the fact that n has degree 1 *)
  >> conj_tac
  >- (disch_tac 
      >> Q.SUBGOAL_THEN ‘HD (TL vs) = EL 1 vs’
          (fn th => gvs[th])
      >- (PURE_REWRITE_TAC[GSYM (cj 1 EL), GSYM (cj 2 EL), GSYM ONE] >> simp[])
      (* EL 0 and EL 2 are adjacent to EL 1 but not equal to each other,
         contradicting the fact EL 1 has degree one *)
      >> Cases_on ‘EL 0 vs = EL 2 vs’
      >- (gvs[path_def]
          >> gvs[EL_ALL_DISTINCT_EL_EQ]
          >> gvs[LAST_EL_LEN_MINUS_ONE]
          >> last_x_assum $ qspecl_then [‘LENGTH vs - 2’, ‘1’] assume_tac
          >> gvs[GSYM (cj 2 EL), ADD1]
         )
      >> sg ‘adjacent g (EL 0 vs) (EL 1 vs) ∧
             adjacent g (EL 1 vs) (EL 2 vs)’
      >- (conj_tac
          >- simp[EL]
          >> PURE_ONCE_REWRITE_TAC[ONE]
          >> PURE_ONCE_REWRITE_TAC[TWO]
          >> PURE_ONCE_REWRITE_TAC[EL]
          >> irule adjacent_el_el_graph
          >> simp[])
      >> qpat_x_assum ‘EL0 vs ≠ EL 2 vs’ mp_tac
      >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
      >> irule degree_one_adjacent_unique
      >> qexistsl [‘g’, ‘EL 1 vs’]
      >> simp[]
      >> gvs[EL, adjacent_SYM]
     )
  >> disch_tac >> Q.SUBGOAL_THEN ‘HD (TL vs) = EL 1 vs’
                   (fn th => gvs[th])
  >- (PURE_REWRITE_TAC[GSYM (cj 1 EL), GSYM (cj 2 EL), GSYM ONE] >> simp[])
  >> gvs[LAST_EL_LEN_MINUS_ONE]
  (* EL (LENGTH vs - 2) and EL 1 are adjacent to EL (LENGTH vs - 1), but not
     equal to each other, contradicting the fact that EL (LENGTH vs - 1) has
     degree 1 *)         
  >> Cases_on ‘EL (LENGTH vs - 2) vs = EL 1 vs’
  >- (gvs[path_def]
      >> gvs[EL_ALL_DISTINCT_EL_EQ]
      >> last_x_assum $ qspecl_then [‘LENGTH vs - 3’, ‘0’] assume_tac
      >> gvs[]
      >> gvs[GSYM (cj 2 EL), ADD1, HD_TL]
     )
  >> sg ‘adjacent g (EL (LENGTH vs - 2) vs) (EL (LENGTH vs - 1) vs) ∧
         adjacent g (EL (LENGTH vs - 1) vs) (EL 1 vs)’        
  >- (REVERSE conj_tac
      >- simp[]
      >> Cases_on ‘LENGTH vs - 2’ >- decide_tac
      >> Cases_on ‘LENGTH vs - 1’ >- decide_tac
      >> PURE_ONCE_REWRITE_TAC[EL]
      >> irule adjacent_el_el_graph
      >> simp[])
  >> qpat_x_assum ‘EL (LENGTH vs - 2) vs ≠ EL 1 vs’ mp_tac
  >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
  >> irule degree_one_adjacent_unique
  >> qexistsl [‘g’, ‘EL (LENGTH vs - 1) vs’]
  >> simp[]
  >> gvs[adjacent_SYM]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Maybe this can be generalised to work with an arbitrary graph that   *)
(* satisfies ¬is_hypergraph g, rather than only with fsgraphs                  *)
(* -------------------------------------------------------------------------- *)
Theorem is_tree_remove_leaf_is_tree:
  ∀g : fsgraph n.
    degree g n = 1 ⇒
    (is_tree g ⇔ is_tree (removeNode n g))
Proof
  rpt gen_tac >> strip_tac
  >> simp[is_tree_def]
  >> simp[connected_removeNode_degree_one]
  >> PURE_ONCE_REWRITE_TAC[pull_out_imp_l] >> strip_tac
  >> EQ_TAC
  >- (strip_tac
      >> gen_tac
      >> first_x_assum (qspecl_then [‘ns’] assume_tac)
      >> disch_tac
      >> qpat_x_assum ‘¬cycle g ns’ mp_tac
      >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
      >> irule cycle_removeNode_imp
      >> qexists ‘n’ >> simp[])
  >> strip_tac >> gen_tac
  >> gvs[cycle_removeNode_degree_one]
QED

(* -------------------------------------------------------------------------- *)
(* A more systematic but less descriptive name for the converse of the above  *)
(* theorem                                                                    *)
(* -------------------------------------------------------------------------- *)
Theorem is_tree_removeNode_degree_one:
  ∀g : fsgraph n.
    degree g n = 1 ⇒
    (is_tree (removeNode n g) ⇔ is_tree g)
Proof
  simp[is_tree_remove_leaf_is_tree]
QED

Theorem removeNodes_insert:
  ∀g n ns.
    removeNodes (n INSERT ns) g =
    removeNodes ns (removeNode n g)
Proof
  rpt gen_tac
  >> simp[gengraph_component_equality]
  >> rpt conj_tac
  >- (simp[EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac >> simp[])
  >- simp[bagTheory.BAG_FILTER_FILTER]
  >> simp[FUN_EQ_THM] 
  >> gen_tac
  >> rw[] >> simp[combinTheory.APPLY_UPDATE_THM] >> gvs[]
QED

Theorem removeNodes_insert_outer:
  ∀g n ns.
    removeNodes (n INSERT ns) g =
    removeNode n (removeNodes ns g)
Proof
  rpt gen_tac
  >> simp[gengraph_component_equality]
  >> rpt conj_tac
  >- (simp[EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac >> simp[])
  >- simp[bagTheory.BAG_FILTER_FILTER, CONJ_SYM]
  >> simp[FUN_EQ_THM]
  >> gen_tac
  >> rw[] >> simp[combinTheory.APPLY_UPDATE_THM] >> gvs[]
QED

Theorem fsgedges_removeNode:
  ∀g n.
    fsgedges (removeNode n g) = fsgedges g DIFF {e | e ∈ fsgedges g ∧ n ∈ e}
Proof
  rpt gen_tac
  >> simp[EXTENSION]
  >> qx_gen_tac ‘e’
  >> simp[fsgedges_def]
  >> REVERSE $ Cases_on ‘∃m n. e = {m;n}’
  >- gvs[]
  >> gvs[]
  >> simp[adjacent_removeNode]
  >> EQ_TAC >> strip_tac
  >- (conj_tac
      >- (qexistsl [‘m’, ‘n'’] >> gvs[INSERT2_lemma, adjacent_SYM])
      >> Cases_on ‘n = m’ >> simp[]
      >- (rpt gen_tac >> strip_tac
          >> gvs[INSERT2_lemma, adjacent_SYM])
      >> strip_tac
      >> rpt gen_tac >> strip_tac
      >> gvs[INSERT2_lemma, adjacent_SYM])
  >- (qexistsl [‘n'’, ‘m’]
      >> simp[]
      >> gvs[INSERT2_lemma])
  >> qexistsl [‘m’, ‘n'’]
  >> gvs[INSERT2_lemma, adjacent_SYM]
QED

Theorem degree_removeNode:
  ∀g n m.
    n ≠ m ⇒
    degree (removeNode n g) m =
    degree g m - (if adjacent g n m then 1 else 0)
Proof
  rpt gen_tac >> strip_tac
  >> simp[degree_def]
  >> qmatch_abbrev_tac ‘CARD smaller_set = CARD larger_set - _’
  >> qsuff_tac ‘larger_set = if adjacent g n m
                             then {n; m} INSERT smaller_set
                             else smaller_set’
  >- (strip_tac
      >> simp[]
      >> Cases_on ‘adjacent g n m’ >> simp[]
      >> ‘FINITE smaller_set’ by (unabbrev_all_tac >> simp[])
      >> simp[]
      >> sg ‘{n; m} ∉ smaller_set’
      >- (unabbrev_all_tac
          >> simp[]
          >> simp[GSYM adjacent_fsg]
          >> simp[adjacent_removeNode])
      >> simp[]
     )
  >> simp[EXTENSION]
  >> gen_tac
  >> Cases_on ‘adjacent g n m’
  >- (unabbrev_all_tac
      >> simp[]
      >> gvs[adjacent_fsg]
      >> Cases_on ‘x = {n;m}’ >> simp[]
      >> simp[fsgedges_removeNode]
      >> EQ_TAC >> simp[]
      >> strip_tac
      >> disch_tac
      >> gvs[fsgedges_def, INSERT2_lemma]
     )
  >> simp[]
  >> unabbrev_all_tac
  >> simp[pull_out_imp_r]
  >> strip_tac
  >> REVERSE $ Cases_on ‘∃a b. x = {a;b}’
  >- gvs[fsgedges_def]
  >> pop_assum mp_tac >> strip_tac
  >> simp[]
  >> simp[GSYM adjacent_fsg]
  >> simp[adjacent_removeNode]
  >> EQ_TAC >> simp[]
  >> strip_tac
  >> conj_tac >> disch_tac >> gvs[adjacent_SYM]
QED

Theorem degree_removeNode_same:
  ∀g n.
    n ∈ nodes g ⇒
    degree (removeNode n g) n = 0
Proof
  rpt gen_tac >> strip_tac
  >> simp[degree_def]
  >> simp[EXTENSION]
  >> gen_tac
  >> Cases_on ‘n ∈ x’ >> simp[]
  >> simp[fsgedges_removeNode]
QED

Theorem degree_card_adjacent_nodes:
  ∀g n.
    degree g n = CARD (adjacent_nodes g n)
Proof
  rpt gen_tac
  >> simp[degree_def]
  >> irule CARDEQ_CARD
  >> PURE_ONCE_REWRITE_TAC[CARD_EQ_SYM]
  >> simp[cardeq_def]
  >> qexists ‘λm. {n;m}’
  >> simp[BIJ_THM]
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> simp[GSYM adjacent_fsg, adjacent_SYM])
  >> gen_tac >> strip_tac
  >> simp[EXISTS_UNIQUE_THM]
  >> conj_tac
  >- (gvs[fsgedges_def]
      >- (qexists ‘n'’
          >> simp[adjacent_SYM]
          >> irule (cj 2 adjacent_members)
          >> qexists ‘m’ >> simp[])
      >> qexists ‘m’
      >> simp[INSERT2_lemma]
      >> irule (cj 1 adjacent_members)
      >> qexists ‘n’ >> simp[adjacent_SYM])
  >> rpt gen_tac >> strip_tac
  >> gvs[INSERT2_lemma]
QED

Theorem a_eq_a_minus_b:
  ∀a b : num.
    a = a - b ⇔ a = 0 ∨ b = 0
Proof
  rpt strip_tac
  >> decide_tac
QED

Theorem finite_adjacent_nodes_fsgraph[simp]:
  ∀g : fsgraph n.
    FINITE (adjacent_nodes g n)
Proof
  rpt gen_tac
  >> ‘adjacent_nodes g n ⊆ nodes g’ by simp[SUBSET_DEF]
  >> irule SUBSET_FINITE
  >> qexists ‘nodes g’
  >> simp[]
QED

Theorem one_leq_card:
  ∀S.
    FINITE S ⇒
    (1 ≤ CARD S ⇔ S ≠ ∅)
Proof
  gen_tac >> strip_tac
  >> EQ_TAC >> strip_tac
  >- (disch_tac >> gvs[])
  >> Cases_on ‘S'’ >> gvs[]
QED

Theorem degree_removeNodes:
  ∀g : fsgraph ns n.
    n ∉ ns ⇒
    degree (removeNodes ns g) n =
    degree g n - CARD (adjacent_nodes g n ∩ ns)
Proof
  (* We can't induct on ns because it may be infinite, but we can induct on
     the intersection of ns with nodes, which is finite, and the only relevant
     part. *)
  rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[removeNodes_restrict]
  >> qabbrev_tac ‘induct_var = ns ∩ nodes g’
  >> qpat_x_assum ‘Abbrev (induct_var = _)’ (fn th => assume_tac (REWRITE_RULE [Abbrev_def] th))
  >> sg ‘FINITE induct_var’
  >- (simp[]
      >> PURE_ONCE_REWRITE_TAC[INTER_COMM]
      >> irule INTER_FINITE
      >> simp[])
  >> rpt $ last_x_assum mp_tac >> disch_tac
  >> SPEC_ALL_TAC
  >> Induct_on ‘induct_var’
  >> conj_tac
  >- (rpt gen_tac >> rpt disch_tac
      >> simp[]
      >> simp[a_eq_a_minus_b]
      >> disj2_tac
      >> qpat_x_assum ‘∅ = _’ (fn th => assume_tac (GSYM th)) >> simp[]
      >> gvs[EXTENSION]
      >> gen_tac
      >> last_x_assum $ qspecl_then [‘x’] assume_tac
      >> gvs[]
     )
  >> gen_tac >> strip_tac
  >> gen_tac >> strip_tac
  >> rpt gen_tac >> rpt disch_tac
  >> simp[removeNodes_insert_outer]
  >> Cases_on ‘e = n’
  >- (gvs[]
      >> gvs[INTER_DEF, EXTENSION]
      >> first_x_assum $ qspec_then ‘e’ mp_tac
      >> simp[])
  >> simp[degree_removeNode]
  >> last_x_assum $ qspecl_then [‘g’, ‘n’, ‘ns DELETE e’]
                  (fn th => assume_tac (REWRITE_RULE [AND_IMP_INTRO] th))
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> conj_tac
  >- (simp[]
      >> simp[EXTENSION] >> gen_tac
      >> EQ_TAC >> strip_tac >> gvs[EXTENSION] >> metis_tac[])
  >> gvs[]
  >> cong_tac (SOME 1)
  >> Cases_on ‘adjacent (removeNodes induct_var g) e n’
  >- (simp[]
      >> PURE_ONCE_REWRITE_TAC[INTER_COMM]
      >> PURE_ONCE_REWRITE_TAC[DELETE_INTER]
      >> DEP_PURE_ONCE_REWRITE_TAC[CARD_DELETE]
      >> conj_tac
      >- (PURE_ONCE_REWRITE_TAC[INTER_COMM]
          >> irule INTER_FINITE
          >> simp[])
      >> Cases_on ‘e ∈ ns ∩ adjacent_nodes g n’ >> simp[]
      >- (simp[]
          >> DEP_PURE_ONCE_REWRITE_TAC[SUB_ADD]
          >> simp[]
          >> DEP_PURE_ONCE_REWRITE_TAC[one_leq_card]
          >> conj_tac
          >- (PURE_ONCE_REWRITE_TAC[INTER_COMM]
              >> irule INTER_FINITE
              >> simp[])
          >> disch_tac
          >> qpat_x_assum ‘e ∈ ns ∩ adjacent_nodes g n’ mp_tac
          >> pop_assum (fn th => PURE_REWRITE_TAC[th])
          >> simp[])
      >> pop_assum mp_tac
      >> simp[INTER_DEF]
      >> gvs[adjacent_removeNodes]
      >> gvs[EXTENSION] >> metis_tac[]
     )
  >> simp[]
  >> cong_tac (SOME 1)
  >> simp[EXTENSION]
  >> gen_tac
  >> EQ_TAC >> strip_tac >> simp[]
  >> disch_tac >> gvs[]
  >> gvs[adjacent_removeNodes]
  >> gvs[EXTENSION] >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* If we remove several leaf nodes from a graph at once, this conserves the   *)
(* property of whether or not it is a tree                                    *)
(* -------------------------------------------------------------------------- *)
Theorem is_tree_removeNodes_is_tree:
  ∀g : fsgraph ns.
    FINITE ns ∧
    (∀n. n ∈ ns ⇒ degree g n = 1) ∧
    (∀n m. n ∈ ns ∧ m ∈ ns ⇒ ¬adjacent g n m) ⇒
    (is_tree g ⇔ is_tree (removeNodes ns g))
Proof
  rpt gen_tac >> strip_tac
  >> Induct_on ‘ns’
  >> conj_tac
  >- simp[] (* Base case *)
  (* Inductive step *)
  >> gen_tac >> strip_tac
  >> gen_tac >> strip_tac
  >> strip_tac >> strip_tac
  >> simp[removeNodes_insert_outer]
  >> DEP_PURE_ONCE_REWRITE_TAC[is_tree_removeNode_degree_one]
  >> simp[]
  >> simp[degree_removeNodes]
  >> simp[SUB_EQ_EQ_0]
  >> simp[EXTENSION]
  >> gen_tac
  >> CCONTR_TAC >> gvs[]
QED

(* See comment for exists_path_adjacent_tc *)
(*Theorem adjacent_tc_exists_path:
  ∀g a b.
    (adjacent g)⁺ a b ⇔ exists_path g a b ∧
                        (if a = b then
                           adjacent g a a
                           ∨ (∃c. exists_path g a c ∧ exists_path g c a)
                         else T)
Proof
  rpt gen_tac
  >> simp[exists_path_adjacent_tc]
  >> Cases_on ‘a = b’ >> simp[]
  >> EQ_TAC >> simp[]
  >- (strip_tac
     )
  >> strip_tac
  >- simp[TC_DEF]
  >- (simp[TC_DEF]
      >> gen_tac
      >> strip_tac
      >> metis_tac[]
      >> gvs[TC_DEF]
     )
  >- gvs[]
  >- gvs[]
  >- (PURE_ONCE_REWRITE_TAC[TC_DEF]
      >> gen_tac
     )
     QED*)

(*Theorem adjacent_tc_exists_path_fsgraph:
  ∀g : fsgraph a b.
    (adjacent g)⁺ a b ⇔ exists_path g a b ∧ degree g a ≠ 0
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[exists_path_adjacent_tc]
  >> EQ_TAC >> simp[]
  >- (strip_tac >> simp[degree_def] >> simp[EXTENSION]
      >> 
      >> 
     )
                        >> strip_tac
                        >> gvs[]
                        >> simp[TC_DEF]
QED*)

Theorem connected_degree_zero:
  ∀g : fsgraph n m.
    connected g ∧
    n ∈ nodes g ∧
    degree g n = 0 ∧
    n ≠ m ⇒
    m ∉ nodes g
Proof
  rpt gen_tac >> strip_tac
  >> gvs[connected_exists_path]
  >> disch_tac
  >> last_x_assum $ qspecl_then [‘n’, ‘m’] assume_tac
  >> gvs[]
  >> gvs[degree_def]
  >> qpat_x_assum ‘_ = ∅’ mp_tac
  >> simp[EXTENSION]
  >> qexists ‘{n; EL 1 (get_path g n m)}’
  >> simp[GSYM adjacent_fsg]
QED

Theorem connected_sing:
  ∀g x.
    nodes g = {x} ⇒
    connected g
Proof
  rpt gen_tac >> strip_tac
  >> simp[connected_def]
QED

(* -------------------------------------------------------------------------- *)
(* A graph containing a single node is a tree.                                *)
(* -------------------------------------------------------------------------- *)
Theorem is_tree_sing:
  ∀g x.
    nodes g = {x} ⇒
    is_tree g
Proof
  rpt gen_tac >> strip_tac
  >> simp[is_tree_def, connected_sing]
  >> gen_tac
  >> disch_tac
  >> gvs[cycle_def]
  >> namedCases_on ‘ns’ ["", "n1 ns"] >> gvs[]
  >> namedCases_on ‘ns'’ ["", "n2 ns"] >> gvs[]
  >> namedCases_on ‘ns’ ["", "n3 ns"] >> gvs[]
  >> ‘n2 ≠ n3’ by (disch_tac >> gvs[])                 
  >> qsuff_tac ‘n2 ∈ nodes g ∧ n3 ∈ nodes g’
  >- (strip_tac >> gvs[])
  >> qpat_x_assum ‘walk _ _’ mp_tac >> rpt (pop_assum kall_tac) >> strip_tac
  >> gvs[walk_def]
QED

(* -------------------------------------------------------------------------- *)
(* If a graph is connected and every node has degree at most 2 and there is   *)
(* a node of degree 1, then the graph is a tree                               *)
(* -------------------------------------------------------------------------- *)
Theorem is_tree_degree_two:
  ∀g : fsgraph.
    connected g ∧
    (∃n. n ∈ nodes g ∧ degree g n = 1) ∧
    (∀n. n ∈ nodes g ⇒ degree g n ≤ 2) ⇒
    is_tree g            
Proof  
  (* Induct on the number of nodes in the graph *)
  gen_tac
  >> strip_tac
  >> ‘FINITE (nodes g)’ by simp[]
  >> qabbrev_tac ‘induct_var = CARD (nodes g)’
  >> pop_assum (fn th => assume_tac (REWRITE_RULE [Abbrev_def] th))
  >> rpt $ pop_assum mp_tac
  >> SPEC_ALL_TAC
  >> Induct_on ‘induct_var’
  >- simp[]
  >> rpt gen_tac >> rpt disch_tac
  (* We may remove the node n and this will preserve whether or not our graph
     is a tree, because n is a leaf node. *)
  >> drule is_tree_removeNode_degree_one
  >> disch_then (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
  (* We will be able to apply the inductive hypothesis on the smaller tree.
.
     But we can only do so when our new tree has a degree 1 node. This occurs
     when our previous degree 1 node was connected to a degree 2 node, which has
     now been decreased to degree 1.
.
     In the other case, where we have a degree 1 node, we will terminate
     (or otherwise violate connectedness)
.
     First step: find the adjacent node to the current degree 1 node.
   *)
  >> drule degree_one_exists_adjacent >> strip_tac
  >> ‘m ∈ nodes g’ by (irule (cj 2 adjacent_members) >> qexists ‘n’ >> simp[])
  >> ‘n ≠ m’ by (disch_tac >> qpat_x_assum ‘adjacent g n m’ mp_tac >> simp[])
  (* The case where this new node has degree 2, and thus we can apply the
     inductive hypothesis to the smaller tree: *)
  >> Cases_on ‘degree g m = 2’
  >- (last_x_assum irule
      >> rpt conj_tac
      >- (gen_tac >> strip_tac
          >> DEP_PURE_ONCE_REWRITE_TAC[degree_removeNode]
          >> conj_tac
          >- (disch_tac >> gvs[])
          >> ‘degree g n' ≤ 2’ suffices_by decide_tac
          >> last_x_assum irule
          >> gvs[nodes_removeNode]
         )
      >- simp[nodes_removeNode]
      >- simp[connected_removeNode_degree_one]
      >- simp[nodes_removeNode]
      >> qexists ‘m’
      >> simp[degree_removeNode]
     )
  (* We no longer need the inductive hypothesis *)
  >> qpat_x_assum ‘∀g n. _’ kall_tac
  (* If instead m has degree 0, we immediately contradict connectedness *)
  >> Cases_on ‘degree g m = 0’
  >- (drule connected_degree_zero
      >> disch_then (qspecl_then [‘m’, ‘n’] assume_tac)
      >> gvs[])
  (* If m has degree 1, we are in the terminating case. We cannot have any
     further nodes becuase this contradicts connectedness. Thus, our graph only
     has m in it. Thus, it is trivially a tree. *)
  >> Cases_on ‘degree g m = 1’              
  >- (irule is_tree_sing
      >> qexists ‘m’
      >> simp[EXTENSION]
      >> gen_tac
      >> REVERSE EQ_TAC
      >- (strip_tac >> gvs[])
      >> strip_tac
      >> CCONTR_TAC
      >> gvs[connected_exists_path]
      >> last_x_assum $ qspecl_then [‘n’, ‘x’] mp_tac
      >> simp[]
      >> disch_tac
      (* The zeroth element on n - x is n.
         The first element on n - x must be m, since that's the only option, as
         n has degree 1.
         The second element on n - x must be n, since that's the only option, as
         m has degree 1.
         But this contradicts the possibility that we have a path.
       *)
      (* Split up n - x into zeroth element followed by tail *)
      >> Cases_on ‘get_path g n x’ >- gvs[]                                         
      (* The zeroth element is n *)
      >> Q.SUBGOAL_THEN ‘h = n’ (fn th => gvs[th])
      >- (Q.SUBGOAL_THEN ‘HD (get_path g n x) = HD (h::t)’ mp_tac
          >- (pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th]) >> simp[])
          >> simp[])
      (* Split up the tail of n - x into first element followed by tail *)
      >> Cases_on ‘t’ >- gvs[]
      (* The first element is m *)
      >> Q.SUBGOAL_THEN ‘h = m’ (fn th => gvs[th])
      >- (Q.SUBGOAL_THEN ‘path g (get_path g n x)’ mp_tac >- simp[]
          >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
          >> simp[path_def, walk_def]
          >> strip_tac
          >> sg ‘adjacent g n h’
          >- (last_x_assum irule >> simp[])
          >> simp[]
          >> qpat_x_assum ‘degree g n = 1’ mp_tac
          >> simp[degree_one_alt] >> strip_tac
          >> ‘h = m'’ by (pop_assum irule >> simp[])
          >> ‘m = m'’ by (first_x_assum irule >> simp[])
          >> simp[])
      (* Split up the tail of n - x into second element followed by tail *)
      >> Cases_on ‘t'’
      >- (Q.SUBGOAL_THEN ‘LAST (get_path g n x) = x’ mp_tac >- simp[]
          >> simp[Excl "exists_path_last_get_path"])
      (* The second element is n *)
      >> Q.SUBGOAL_THEN ‘h = n’ (fn th => gvs[th])
      >- (sg ‘adjacent g m h’
          >- (Q.SUBGOAL_THEN ‘path g (get_path g n x)’ mp_tac >- simp[]
              >> PURE_REWRITE_TAC[path_def, walk_def]
              >> strip_tac
              >> first_x_assum irule
              >> simp[adjacent_iff])
          >> qpat_x_assum ‘degree g m = 1’ mp_tac
          >> simp[degree_one_alt] >> strip_tac
          >> ‘h = m'’ by (pop_assum irule >> simp[])
          >> ‘n = m'’ by (first_x_assum irule >>
                          PURE_ONCE_REWRITE_TAC[adjacent_SYM] >> simp[])
          >> simp[])
      (* This contradicts the fact that we have a path *)
      >> Q.SUBGOAL_THEN ‘path g (get_path g n x)’ mp_tac >- simp[]
      >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[path_def])
  >> ‘degree g m ≤ 2’ by simp[]
  >> decide_tac
QED

Theorem not_degree_one:
  ∀g n m1 m2.
    adjacent g n m1 ∧
    adjacent g n m2 ∧
    m1 ≠ m2 ⇒
    degree g n ≠ 1
Proof
  rpt gen_tac
  >> strip_tac
  >> simp[degree_one_alt]
  >> gen_tac
  >> Cases_on ‘adjacent g n m’ >> simp[]
  >> Cases_on ‘m1 = m’
  >- (qexists ‘m2’ >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
      >> simp[])
  >> qexists ‘m1’
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* Based on BIJ_INV                                                           *)
(* -------------------------------------------------------------------------- *)
Theorem graph_isomorphism_comm:
  ∀f g1 g2.
    graph_isomorphism f g1 g2 ⇒
    ∃g. graph_isomorphism g g2 g1 ∧
        (∀x. x ∈ (nodes g1) ⇒ (g (f x) = x)) ∧
        ∀x. x ∈ (nodes g2) ⇒ f (g x) = x
Proof
  rpt gen_tac >> simp[graph_isomorphism_def]
  >> strip_tac
  >> drule BIJ_INV
  >> strip_tac
  >> qexists ‘g’
  >> simp[]
  >> REVERSE conj_tac
  >- gvs[]
  >> rpt gen_tac >> strip_tac
  >> last_x_assum $ qspecl_then [‘g n’, ‘g m’] mp_tac
  >> gvs[BIJ_THM]
QED

Theorem graph_isomorphism_in_nodes:
  ∀f g1 g2 x.
    graph_isomorphism f g1 g2 ∧
    x ∈ nodes g1 ⇒
    f x ∈ nodes g2
Proof
  simp[graph_isomorphism_def, BIJ_THM]
QED

Theorem graph_isomorphism_adjacent:
  ∀f g1 g2 n m.
    graph_isomorphism f g1 g2 ∧
    adjacent g1 n m ⇒
    adjacent g2 (f n) (f m)
Proof
  rpt gen_tac >> simp[graph_isomorphism_def] >> strip_tac
  >> first_x_assum $ qspecl_then [‘n’, ‘m’] assume_tac
  >> drule adjacent_members >> strip_tac
  >> gvs[]
QED

Theorem graph_isomorphism_walk:
  ∀f g1 g2 vs.
    graph_isomorphism f g1 g2 ∧
    walk g1 vs ⇒
    walk g2 (MAP f vs)
Proof
  rpt gen_tac
  >> simp[walk_def]
  >> strip_tac
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> gvs[MEM_MAP]
      >> irule graph_isomorphism_in_nodes
      >> qexists ‘g1’
      >> simp[]
     )
  >> rpt gen_tac >> strip_tac
  >> gvs[adjacent_MAP]
  >> irule graph_isomorphism_adjacent
  >> qexists ‘g1’
  >> simp[]
QED

Theorem ALL_DISTINCT_MAP_INJ_FUNC:
  ∀f s t ls.
    INJ f s t ∧
    set ls ⊆ s ∧
    ALL_DISTINCT ls ⇒
    ALL_DISTINCT (MAP f ls)
Proof
  rpt gen_tac >> strip_tac
  >> irule ALL_DISTINCT_MAP_INJ
  >> simp[]
  >> rpt gen_tac >> strip_tac
  >> gvs[INJ_DEF]
  >> last_x_assum irule
  >> gvs[SUBSET_DEF]
QED

Theorem graph_isomorphism_path:
  ∀f g1 g2 vs.
    graph_isomorphism f g1 g2 ∧
    path g1 vs ⇒
    path g2 (MAP f vs)
Proof
  rpt gen_tac >> simp[path_def] >> strip_tac
  >> conj_tac
  >- (irule graph_isomorphism_walk
      >> qexists ‘g1’ >> simp[])
  >> irule ALL_DISTINCT_MAP_INJ_FUNC
  >> simp[]
  >> qexistsl [‘nodes g1’, ‘nodes g2’]
  >> conj_tac
  >- gvs[walk_def, SUBSET_DEF]
  >> gvs[graph_isomorphism_def, BIJ_DEF]
QED

Theorem graph_isomorphism_connected_reverse:
  ∀f g1 g2.
    connected g1 ∧
    graph_isomorphism f g1 g2 ⇒
    connected g2
Proof
  rpt gen_tac >> simp[connected_exists_path] >> strip_tac
  >> drule graph_isomorphism_comm >> strip_tac
  >> rpt gen_tac >> strip_tac
  >> last_x_assum $ qspecl_then [‘g a’, ‘g b’] mp_tac
  >> impl_tac
  >- metis_tac[graph_isomorphism_in_nodes]
  >> simp[exists_path_def]
  >> strip_tac
  >> qexists ‘MAP f vs’
  >> rpt conj_tac
  >- (irule graph_isomorphism_path >> qexists ‘g1’ >> simp[])
  >- (Cases_on ‘vs = []’ >- gvs[]
      >> simp[MAP_HD]
     )
  >> Cases_on ‘vs = []’ >- gvs[]
  >> simp[LAST_MAP]
QED

Theorem graph_isomorphism_connected:
  ∀f g1 g2.
    connected g1 ∧
    graph_isomorphism f g2 g1 ⇒
    connected g2
Proof
  rpt gen_tac >> strip_tac
  >> drule graph_isomorphism_comm
  >> strip_tac
  >> qspecl_then [‘g’, ‘g1’, ‘g2’] mp_tac graph_isomorphism_connected_reverse
  >> simp[]
QED

Theorem nodes_line_graph[simp]:
  ∀n.
    nodes (line_graph n) = IMAGE INR (count n)
Proof
  rpt gen_tac
  >> Induct_on ‘n’ >- simp[line_graph_def]
  >> Cases_on ‘n’ >> simp[line_graph_def]
  >- simp[COUNT_ONE]
  >> simp[COUNT_SUC]
QED

Theorem fsgedges_line_graph:
  ∀n.
    fsgedges (line_graph n) = IMAGE (λi. {INR i; INR (i - 1)}) (count n DELETE 0)
Proof
  rpt gen_tac
  >> Induct_on ‘n’ >- simp[line_graph_def]
  >> Cases_on ‘n’ >> simp[line_graph_def, COUNT_ONE]
  >> simp[fsgedges_fsgAddEdges]
  >> qmatch_abbrev_tac ‘added_edges ∪ _ = _’
  >> qsuff_tac ‘added_edges = {{INR (SUC n'); INR n'}}’               
  >- (strip_tac >> simp[]
      >> irule (iffRL EXTENSION) >> gen_tac >> EQ_TAC >> strip_tac >> simp[]
      >- (gvs[]
          >- (qexists ‘SUC n'’
              >> simp[])
          >> qexists ‘i’
          >> simp[])
      >> gvs[]
      >> simp[INSERT2_lemma]
     )
  >> Q.UNABBREV_TAC ‘added_edges’
  >> irule (iffRL EXTENSION)
  >> gen_tac >> EQ_TAC >> strip_tac >> gvs[]
  >> qexistsl [‘INR (SUC n')’, ‘INR n'’]
  >> simp[nodes_line_graph]
QED

(*
(* TODO: *)
Theorem fsgAddEdges_alt:
  ∀g es.
    fsgAddEdges es g =
    ITSET (λe. addUDEdge e () g) es
Proof
QED*)

Theorem INSERT2_sym:
  ∀a b.
    {a;b} = {b;a}
Proof
  rpt gen_tac
  >> simp[EXTENSION]
  >> gen_tac >> EQ_TAC >> strip_tac >> simp[]
QED

Theorem finite_directed_to_undirected_edge[simp]:
  ∀g es.
    FINITE es ⇒
    FINITE {(n, m) | {n;m} ∈ es}
Proof
  rpt gen_tac >> strip_tac
  >> Induct_on ‘es’
  >> conj_tac
  >- simp[]
  >> gen_tac >> strip_tac
  >> gen_tac >> strip_tac
  >> qmatch_abbrev_tac ‘FINITE new_es’
  >> Cases_on ‘∃n m. e = {n;m}’
  >- (gvs[]
      >> sg ‘new_es = (n,m) INSERT (m,n) INSERT {(n,m) | {n;m} ∈ es}’
      >- (Q.UNABBREV_TAC ‘new_es’
          >> PURE_ONCE_REWRITE_TAC[EXTENSION]
          >> gen_tac >> EQ_TAC >> strip_tac >> gvs[INSERT2_lemma]
         )
      >> simp[]
     )
  >> sg ‘new_es = {(n,m) | {n; m} ∈ es}’
  >- (Q.UNABBREV_TAC ‘new_es’
      >> irule (iffRL EXTENSION)
      >> gen_tac >> EQ_TAC >> strip_tac >> gvs[]
     )
  >> simp[]
QED
        
Theorem finite_directed_to_undirected_edge_additional_restrictions[simp]:
  ∀g es.
    FINITE es ⇒
    FINITE {(n,m) | n ≠ m ∧ n ∈ nodes g ∧ m ∈ nodes g ∧ {n; m} ∈ es}
Proof
  rpt gen_tac >> strip_tac
  (* This is a subset of all possible directed edges on the undirected edges es,
     which is also finite *)
  >> irule SUBSET_FINITE
  >> qexists ‘{(n,m) | {n;m} ∈ es}’
  >> simp[SUBSET_DEF]
  >> gen_tac >> strip_tac
  >> qexistsl [‘n’, ‘m’]
  >> simp[]
QED

Theorem union_idem[simp]:
  ∀s1 s2.
    s1 ∪ (s1 ∪ s2) = s1 ∪ s2
Proof
  rpt gen_tac
  >> simp[EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac >> simp[]
QED

(* TODO: Delete? instead use udedges_addUDEdge?
Theorem edgebag_addUDEdge:
  ∀ns lab g : ('a, undirectedG, 'ec, 'el, θ, 'nf, 'nl, 'sl) graph.
    edgebag (addUDEdge ns lab g) =
    if SING ns ∧ ¬itself2bool (:'sl) then edgebag g
    else if INFINITE ns ∧ itself2bool (:'nf) then edgebag g
    else if ¬itself2bool (:θ) ∧ (FINITE ns ⇒ 2 < CARD ns) then edgebag g
    else if ns = ∅ then edgebag g
    else
      ARB
Proof
  rpt gen_tac
  >> simp[addUDEdge_def, addUDEdge0_def]
  >> rw[graph_ABSREP]

  >> udedges_def
  >> udedges_addUDEdge
  >> nodes_addUDEdge
  >> adjacent_addUDEdge



     simp[udedges_def, oneEdge_max_def] >>
  xfer_back_tac[] >> simp[addUDEdge0_def] >> rw[] >> rw[] >> gvs[] >>
  Cases_on ‘m = n’ >> gvs[] >>
  simp[udfilter_insertedge_def, GSPEC_OR, AC CONJ_COMM CONJ_ASSOC] >>
  rename [‘itself2_ecv x’] >> Cases_on ‘itself2_ecv x’ >> gvs[] >>
  simp[Once EXTENSION] >> rw[] >>
  metis_tac[]
     
  >> simp[]
QED
 *)

Theorem addUDEdge_invalid:
  ∀ns g : ('a,'c,'b,'d,'e,'f) udgraph l.
    INFINITE ns ∨
    (¬selfloops_ok g ∧ CARD ns = 1) ∨
    (CARD ns ≠ 2 ∧ CARD ns ≠ 1) ⇒
    addUDEdge ns l g = g
Proof
  rpt gen_tac
  >> simp[addUDEdge_def, addUDEdge0_def]
  >> rw[graph_ABSREP]
  >> Cases_on ‘ns’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[]
  >> Cases_on ‘t'’ >> gvs[]
QED

(* Unfortunately this fails because udedges restricts the bag to a set which
   has maximum multiplicity 1.

Theorem udgraph_component_equality:
  ∀g1 g2 : ('a, 'c, 'b, 'd, 'e, 'f) udgraph.
    g1 = g2 ⇔
      nodes g1 = nodes g2 ∧ udedges g1 = udedges g2 ∧ nlabelfun g1 = nlabelfun g2
Proof
  rpt gen_tac
  >> simp[gengraph_component_equality]
  >> PURE_ONCE_REWRITE_TAC[pull_out_imp_l]
  >> PURE_ONCE_REWRITE_TAC[CONJ_SYM]
  >> PURE_ONCE_REWRITE_TAC[pull_out_imp_l]
  >> disch_tac >> disch_tac
  >> simp[udedges_def]
  >> EQ_TAC >> strip_tac
  >- (irule (iffRL EXTENSION) >> gen_tac >> EQ_TAC >> strip_tac >> gvs[])
  >> pop_assum mp_tac >> simp[EXTENSION] >> strip_tac
  >> irule (iffRL BAG_EXTENSION)
  >> rpt gen_tac
  >> 
         
  >> 
                       
  >> CCONTR_TAC >> qpat_x_assum ‘{he | _} = {he | _}’ mp_tac
QED*)

(* -------------------------------------------------------------------------- *)
(* TODO: Would be nicer to have udgraph_component_equality rather than only   *)
(* udul_component_equality, as this would allow this theorem to be more       *)
(* general                                                                    *)
(* -------------------------------------------------------------------------- *)
Theorem addUDEdge_idem[simp]:
  ∀ns lab g : (α,ν,σ) udulgraph.
    addUDEdge ns lab (addUDEdge ns lab g) = addUDEdge ns lab g
Proof
  rpt gen_tac     
  >> Cases_on ‘∃a b. ns = {a;b} ∧ a ≠ b’ >> gvs[]
  >- (simp[udul_component_equality]
      >> simp[udedges_addUDEdge]
      >> simp[EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac >> simp[]
      >- (disj2_tac
          >> qexists ‘x'’
          >> simp[])
      >> disj2_tac
      >> REVERSE conj_tac
      >- (qexists ‘x'’ >> simp[])
      >> disj2_tac
      >> qexists ‘x'’ >> simp[]
     )
  >> Cases_on ‘INFINITE ns ∨
               (¬itself2bool (:σ) ∧ CARD ns = 1) ∨
               (CARD ns ≠ 2 ∧ CARD ns ≠ 1)’
  >- (irule addUDEdge_invalid >> simp[])
  >> gvs[]
  >- (Cases_on ‘ns’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[])
  >> Cases_on ‘ns’ >> gvs[]
  >> simp[udul_component_equality]
  >> Q.SUBGOAL_THEN ‘{x} = {x;x}’ (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- simp[]
  >> conj_tac
  >- simp[nodes_addUDEdge]
  >> simp[udedges_addUDEdge]
  >> irule (iffRL EXTENSION) >> gen_tac >> EQ_TAC >> strip_tac >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Note: addUDEdge and fsgAddEdges behave differently in the case where a     *)
(* node in the edge being added is not already a node in the graph.           *)
(*                                                                            *)
(* addUDEdge will add the corresponding nodes to the graph so that the edge   *)
(* can be added in a valid way, while fsgAddEdges will ignore these nodes and *)
(* edges, leaving the graph unchanged.                                        *)
(* -------------------------------------------------------------------------- *)
Theorem fsgAddEdges_insert_addUDEdge:
  ∀g e es.
    e ⊆ nodes g ∧
    FINITE es ⇒
    fsgAddEdges (e INSERT es) g = addUDEdge e () (fsgAddEdges es g)
Proof
  rpt gen_tac >> strip_tac
  >> simp[fsgAddEdges_def]
  >> qmatch_abbrev_tac
     ‘ITSET _ edge_set_lhs g = addUDEdge _ _ (ITSET _ edge_set_rhs _)’
  >> sg ‘if ∃a b. a ≠ b ∧ a ∈ nodes g ∧ b ∈ nodes g ∧ e = {a;b}
         then
           let
             (a,b) = @(a,b). a ≠ b ∧ a ∈ nodes g ∧ b ∈ nodes g ∧ e = {a;b}
           in
             edge_set_lhs = (a,b) INSERT (b,a) INSERT edge_set_rhs
         else
           edge_set_lhs = edge_set_rhs
        ’
  >- (rw[]
      >- (SELECT_ELIM_TAC
          >> conj_tac
          >- (qexists ‘(a, b)’ >> simp[])
          >> gen_tac >> strip_tac
          >> namedCases_on ‘x’ ["a b"] >> gvs[]
          >> irule (iffRL EXTENSION)
          >> gen_tac >> EQ_TAC >> strip_tac >> simp[]
          >- (Q.UNABBREV_TAC ‘edge_set_lhs’ >> Q.UNABBREV_TAC ‘edge_set_rhs’
              >> gvs[]
              >> wlog_tac ‘m = a'’ [‘a'’, ‘b'’]
              >- (first_x_assum $ qspecl_then [‘b'’, ‘a'’] mp_tac
                  >> gvs[INSERT2_lemma]
                 )
              >> gvs[INSERT2_lemma]
             )
          >> Q.UNABBREV_TAC ‘edge_set_lhs’ >> Q.UNABBREV_TAC ‘edge_set_rhs’
          >> gvs[INSERT2_lemma]
         )
      >> Q.UNABBREV_TAC ‘edge_set_lhs’ >> Q.UNABBREV_TAC ‘edge_set_rhs’
      >> irule (iffRL EXTENSION) >> gen_tac >> EQ_TAC >> strip_tac >> simp[]
      >- (gvs[]
          >> last_x_assum $ qspecl_then [‘n’, ‘m’] mp_tac
          >> simp[INSERT2_sym]
         )
      >> gvs[]
     )
  >> Cases_on ‘∃a b. a ≠ b ∧ a ∈ nodes g ∧ b ∈ nodes g ∧ e = {a;b}’
  >- (gvs[]
      >> qmatch_asmsub_abbrev_tac
         ‘(λ(a,b). edge_set_lhs = (a,b) INSERT (b,a) INSERT edge_set_rhs) chosen_ab’
      >> namedCases_on ‘chosen_ab’ ["chosen_a chosen_b"]
      >> gvs[]
      >> qmatch_abbrev_tac ‘ITSET f _ _ = _’
      (* Our function f is commutative, which is required for ITSET_REDUCTION *)
      >> sg ‘∀x y z. f x (f y z) = f y (f x z)’
      >- (Q.UNABBREV_TAC ‘f’
          >> rpt gen_tac
          >> Cases_on ‘x’ >> simp[]
          >> Cases_on ‘y’ >> simp[]
          >> simp[addUDEdge_udul_LCOMM]
         )
      (* Delete the inserted elements from edge_set_rhs to ensure they aren't
         in it, so that we can apply ITSET_REDUCTION to drag the elments out *)
      >> Q.SUBGOAL_THEN
          ‘(chosen_a,chosen_b) INSERT (chosen_b,chosen_a) INSERT edge_set_rhs =
           (chosen_a,chosen_b) INSERT (chosen_b,chosen_a) INSERT
                               (edge_set_rhs DELETE (chosen_a, chosen_b)
                                             DELETE (chosen_b, chosen_a))’
          (fn th => PURE_ONCE_REWRITE_TAC[th])
      >- ASM_SET_TAC[]
      (* Nicer name of the edge set with the added elements removed *)
      >> qmatch_abbrev_tac ‘ITSET _ (_ INSERT _ INSERT edge_set_rhs_deleted) _ = _’
      (* Prove preconditions to apply ITSET_REDUCTION, so we can drag the added
         elements out of the LHS *)
      >> sg ‘(chosen_a, chosen_b) ∉ edge_set_rhs_deleted’
      >- (Q.UNABBREV_TAC ‘edge_set_rhs_deleted’ >> simp[])
      >> sg ‘(chosen_b, chosen_a) ∉ edge_set_rhs_deleted’
      >- (Q.UNABBREV_TAC ‘edge_set_rhs_deleted’ >> simp[])
      >> sg ‘FINITE edge_set_rhs_deleted’
      >- (Q.UNABBREV_TAC ‘edge_set_rhs_deleted’
          >> Q.UNABBREV_TAC ‘edge_set_rhs’
          >> simp[]
         )         
      >> sg ‘chosen_a ≠ chosen_b’
      >- (disch_tac >> gvs[]
          >> qpat_x_assum ‘_ = (chosen_a, chosen_a)’ mp_tac
          >> SELECT_ELIM_TAC
          >> conj_tac
          >- (qexists ‘(a,b)’
              >> simp[])
          >> gen_tac
          >> namedCases_on ‘x’ ["a' b'"] >> simp[]
          >> rpt disch_tac
          >> gvs[]
         )
      (* Drag the added elements out of the LHS: the repeated additions of the
         same edge collapse into one addition via idempotency *)
      >> simp[ITSET_REDUCTION]
      >> Q.UNABBREV_TAC ‘f’
      >> simp[INSERT2_sym]
      (* chosen_a and chosen_b correspond to a and b, in some order *)             
      >> qpat_x_assum ‘_ = (chosen_a, chosen_b)’ assume_tac
      >> Q.SUBGOAL_THEN ‘(a = chosen_a ∧ b = chosen_b) ∨
                         (b = chosen_a ∧ a = chosen_b)’ assume_tac
      >- (pop_assum mp_tac
          >> SELECT_ELIM_TAC
          >> conj_tac
          >- (qexists ‘(a, b)’ >> simp[])
          >> gen_tac
          >> namedCases_on ‘x’ ["x_a x_b"] >> simp[]
          >> simp[INSERT2_lemma]
          >> strip_tac >> simp[]
         )
      (* Without loss of generality, we can choose chosen_a = a and
      chosen_b = b *)
      >> wlog_tac ‘chosen_a = a’ [‘a’, ‘b’]
      >- (first_x_assum $ qspecl_then [‘b’, ‘a’] mp_tac
          >> Q.SUBGOAL_THEN ‘{b;a} = {a;b}’ (fn th => PURE_ONCE_REWRITE_TAC[th])
          >- simp[INSERT2_lemma]
          >> gvs[]
         )
      >> gvs[]
      (* Helpful assumption *)
      >> sg ‘FINITE edge_set_rhs’
      >- (Q.UNABBREV_TAC ‘edge_set_rhs_deleted’
          >> qpat_x_assum ‘FINITE (edge_set_rhs DELETE _ DELETE _)’ mp_tac
          >> simp[])
      (* We have dragged the (a,b) edges out of the LHS, but they may also have
         been present in the RHS. We should drag them out of the RHS too. *)
      >> Q.SUBGOAL_THEN
          ‘(addUDEdge {a; b} () (ITSET (λ(m,n) g. addUDEdge {m; n} () g)
                                       edge_set_rhs g)) =
             addUDEdge {a; b} () (ITSET (λ(m,n) g. addUDEdge {m; n} () g)
                                        (edge_set_rhs DELETE (a,b)) g)’
          (fn th => PURE_ONCE_REWRITE_TAC[th])            
      >- (REVERSE $ Cases_on ‘(a,b) ∈ edge_set_rhs’
          >- simp[DELETE_NON_ELEMENT_RWT]
          >> qmatch_abbrev_tac ‘_ = RHS’                               
          >> Q.SUBGOAL_THEN ‘edge_set_rhs =
                             (a,b) INSERT (edge_set_rhs DELETE (a,b))’
              (fn th => PURE_ONCE_REWRITE_TAC[th])
          >- simp[]
          >> simp[ITSET_REDUCTION, Excl "INSERT_DELETE"]
          >> Q.UNABBREV_TAC ‘RHS’
          >> simp[]
         )         
      (* Drag the second edge out of the RHS *)
      >> Q.UNABBREV_TAC ‘edge_set_rhs_deleted’
      >> REVERSE $ Cases_on ‘(b,a) ∈ edge_set_rhs’
      >- simp[DELETE_NON_ELEMENT_RWT]
      >> qmatch_abbrev_tac ‘LHS = _’                         
      >> Q.SUBGOAL_THEN ‘edge_set_rhs =
                         (b,a) INSERT (edge_set_rhs DELETE (b,a))’
          (fn th => PURE_ONCE_REWRITE_TAC[th])
      >- simp[]
      >> simp[DELETE_INSERT]
      >> DEP_PURE_ONCE_REWRITE_TAC[ITSET_REDUCTION]
      >> simp[ITSET_REDUCTION, Excl "INSERT_DELETE"]
      >> Q.UNABBREV_TAC ‘LHS’
      >> simp[INSERT2_sym, DELETE_COMM]
     )
  (* The case where we are adding an invalid edge *)
  >> gvs[]
  >> Cases_on ‘INFINITE e ∨ ¬selfloops_ok g ∧ CARD e = 1 ∨
               CARD e ≠ 2 ∧ CARD e ≠ 1’
  >- (SYM_TAC >> irule addUDEdge_invalid >> gvs[])
  >> gvs[]
  >> Cases_on ‘e’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[]
  (* One of the elements of the edge is not in the set of nodes, contradicting
     our assumption *)
  >> first_x_assum $ qspecl_then [‘x’, ‘x'’] mp_tac >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* Advantage over fsgAddEdges_insert_addUDEdge: doesn't require that the edge *)
(* being added is in the nodes of the graph.                                  *)
(*                                                                            *)
(* Disadvantage compared to fsgAddEdges_insert_addUDEdge: if applied as a     *)
(* simplification rule, goes into an infinite loop because the RHS is an      *)
(* instance of the LHS                                                        *)
(* -------------------------------------------------------------------------- *)
Theorem fsgAddEdges_insert:
  ∀g e es.
    FINITE es ⇒
    fsgAddEdges (e INSERT es) g = fsgAddEdges {e} (fsgAddEdges es g)
Proof
  rpt gen_tac >> strip_tac
  >> Cases_on ‘e ⊆ nodes g’
  >- simp[fsgAddEdges_insert_addUDEdge]
  >> simp[fsgAddEdges_def]
  >> qmatch_abbrev_tac ‘ITSET f s_total g = ITSET f s_hd (ITSET f s_tl g)’
  >> sg ‘s_hd = ∅’
  >- (simp[EXTENSION]
      >> gen_tac
      >> unabbrev_all_tac
      >> namedCases_on ‘x’ ["m n"]
      >> simp[]
      >> strip_tac
      >> gvs[SUBSET_DEF]
     )
  >> simp[]
  >> qpat_x_assum ‘s_hd = ∅’ kall_tac
  >> qpat_x_assum ‘Abbrev (s_hd = _)’ kall_tac
  >> cong_tac (SOME 1)
  >> unabbrev_all_tac
  >> irule (iffRL EXTENSION) >> gen_tac >> EQ_TAC >> strip_tac >> simp[]
  >> (namedCases_on ‘x’ ["m n"] >> simp[]
      >> gvs[])
QED

Theorem fsgAddEdges_fsgAddEdges:
  ∀g es1 es2.
    FINITE es1 ∧
    FINITE es2 ⇒
    fsgAddEdges es1 (fsgAddEdges es2 g) = fsgAddEdges (es1 ∪ es2) g
Proof
  rpt gen_tac >> strip_tac
  >> Induct_on ‘es1’ >> conj_tac
  >- simp[]
  >> gen_tac >> strip_tac >> gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[INSERT_UNION_EQ]
  >> simp[Once fsgAddEdges_insert, Cong LHS_CONG]
  >> simp[Once fsgAddEdges_insert, Cong RHS_CONG]
QED

Theorem removeNode_fsgAddEdges:
  ∀g n es.
    FINITE es ⇒
    removeNode n (fsgAddEdges es g) = fsgAddEdges (es ∩ {e | n ∉ e}) (removeNode n g)
Proof
  rpt gen_tac
  >> Induct_on ‘es’ using FINITE_INDUCT >> conj_tac
  >- simp[]
  >> gen_tac >> strip_tac >> gen_tac >> strip_tac
  >> simp[INSERT_INTER]
  >> rw[]       
  >- (simp[Once fsgAddEdges_insert]
      >> simp[Once fsgAddEdges_insert, Cong RHS_CONG]
      >> qpat_x_assum ‘removeNode _ _ = fsgAddEdges _ _’
                      (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
      >> simp[GSYM fsgAddEdges_insert]
      >> simp[fsgraph_component_equality]
      >> simp[fsgedges_fsgAddEdges, fsgedges_removeNode]
      >> irule (iffRL EXTENSION)
      >> gen_tac
      >> Cases_on ‘x = e’                  
      >- (simp[]
          >> EQ_TAC >> strip_tac
          >- (qpat_x_assum ‘{m; n'} = e’ kall_tac
              >> gvs[]
              >> disj1_tac
              >> qexistsl [‘m’, ‘n'’]
              >> simp[])
          >- (simp[]
              >> disj1_tac
              >> qexistsl [‘m’, ‘n'’]
              >> simp[]
              >> gvs[])
          >- simp[]
          >- (qpat_x_assum ‘{m; n'} = e’ kall_tac
              >> gvs[]
              >> disj1_tac
              >> qexistsl [‘m’, ‘n'’]
              >> simp[]
             )
          >- (disj1_tac
              >> qexistsl [‘m’, ‘n'’]
              >> simp[])
          >> simp[]
         )
      >> Cases_on ‘n ∈ x’
      >- (simp[]
          >> EQ_TAC >> strip_tac
          >- gvs[]
          >- (gnvs[]
              >> gvs[]
              >- (first_x_assum $ qspecl_then [‘m’, ‘n'’] assume_tac
                                >> gvs[])
              >> first_x_assum $ qspecl_then [‘m’, ‘n’] assume_tac
              >> gvs[]
             )
          >- gvs[]
          >> gvs[]
          >- (first_x_assum $ qspecl_then [‘m’, ‘n'’] assume_tac
              >> gvs[])
          >> first_x_assum $ qspecl_then [‘m’, ‘n’] assume_tac
          >> gvs[]
         )
      >> simp[]
      >> EQ_TAC >> strip_tac
      >- gvs[]
      >- (gvs[]
          >> disj2_tac
          >> disj1_tac
          >> qexistsl [‘m’, ‘n'’]
          >> simp[]
         )
      >- simp[]
      >- gvs[]
      >- (gvs[]
          >> disj1_tac
          >> qexistsl [‘m’, ‘n'’]
          >> simp[])
      >> simp[]
     )
  >> qpat_x_assum ‘removeNode _ _ = fsgAddEdges _ _’
                  (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
  >> simp[Once fsgAddEdges_insert]
  >> simp[fsgraph_component_equality]
  >> simp[fsgedges_removeNode, fsgedges_fsgAddEdges]
  >> irule (iffRL EXTENSION)
  >> gen_tac >> EQ_TAC >> strip_tac
  >- (gvs[]
      >- (qexistsl [‘m’, ‘n'’] >> simp[]
          >> last_x_assum $ qspecl_then [‘m’, ‘n'’] assume_tac
          >> gvs[]
         )
      >- (last_x_assum $ qspecl_then [‘m’, ‘n’] assume_tac
          >> gvs[])
      >- (first_x_assum $ qspecl_then [‘m’, ‘n'’] assume_tac
          >> gvs[])
      >> disj1_tac
      >> qexistsl [‘m’, ‘n'’]
      >> simp[])
  >> simp[]
  >> strip_tac
  >- (gvs[]
      >- (first_x_assum $ qspecl_then [‘m’, ‘n'’] assume_tac
          >> gvs[])
      >> disj2_tac
      >> disj1_tac
      >> qexistsl [‘m’, ‘n'’]
      >> simp[]
     )
  >> gvs[]
  >> Cases_on ‘n ≠ m ∧ n ≠ n'’ >> simp[]
  >> rpt gen_tac
  >> strip_tac >> strip_tac
  >> gvs[]
QED

Theorem removeNode_fsgAddNode:
  ∀g n.
    removeNode n (fsgAddNode n g) = removeNode n g
Proof
  rpt gen_tac
  >> simp[fsgraph_component_equality]
  >> conj_tac
  >- simp[DELETE_INSERT]
  >> simp[fsgedges_removeNode]
QED

Theorem walk_fsgAddEdges:
  ∀g es vs.
    walk g vs ⇒
    walk (fsgAddEdges es g) vs
Proof
  rpt gen_tac
  >> simp[walk_def]
QED

Theorem path_fsgAddEdges:
  ∀g es vs.
    path g vs ⇒
    path (fsgAddEdges es g) vs
Proof
  rpt gen_tac
  >> simp[path_def, walk_fsgAddEdges]
QED

Theorem exists_path_fsgAddEdges:
  ∀g es a b.
    exists_path g a b ⇒
    exists_path (fsgAddEdges es g) a b
Proof
  rpt gen_tac
  >> simp[exists_path_def]
  >> strip_tac
  >> qexists ‘vs’
  >> simp[path_fsgAddEdges]
QED

Theorem connected_fsgAddEdges:
  ∀g es.
    connected g ⇒
    connected (fsgAddEdges es g)
Proof
  rpt gen_tac
  >> strip_tac
  >> gvs[connected_exists_path]
  >> rpt gen_tac
  >> strip_tac
  >> last_x_assum $ qspecl_then [‘a’, ‘b’] mp_tac
  >> simp[exists_path_fsgAddEdges]
QED

Theorem line_graph_connected[simp]:
  ∀n.
    connected (line_graph n)
Proof
  gen_tac
  >> Induct_on ‘n’
  >- simp[line_graph_def]
  >> Cases_on ‘n’ >> simp[line_graph_def]
  >- (irule connected_sing
      >> qexists ‘INR 0’
      >> simp[])
  >> qmatch_abbrev_tac ‘connected g’
  >> qspecl_then [‘g’, ‘INR (SUC n')’]
                 (fn th => DEP_PURE_ONCE_REWRITE_TAC[GSYM th])
                 connected_removeNode_degree_one
  >> conj_tac
  >- (Q.UNABBREV_TAC ‘g’
      >> DEP_PURE_ONCE_REWRITE_TAC[degree_fsgAddEdges]
      >> conj_tac
      >- (simp[valid_edges_def]
          >> simp[nodes_line_graph])
      >> simp[]
      >> qmatch_abbrev_tac ‘CARD added_edges = 1’
      >> ‘added_edges = {{INR (SUC n'); INR n'}}’ suffices_by simp[]
      >> Q.UNABBREV_TAC ‘added_edges’
      >> PURE_ONCE_REWRITE_TAC[EXTENSION] >> gen_tac >> EQ_TAC >> simp[]
      >> strip_tac
      >> gvs[fsgedges_line_graph]
     )
  >> Q.UNABBREV_TAC ‘g’
  >> simp[removeNode_fsgAddEdges]
  >> simp[removeNode_fsgAddNode]
  >> simp[removeNode_NONMEMBER, nodes_line_graph]
  >> simp[connected_fsgAddEdges]
QED

Theorem line_graph_zero[simp]:
  line_graph 0 = emptyG
Proof
  simp[line_graph_def]
QED

Theorem line_graph_one[simp]:
  line_graph 1 = fsgAddNode (INR 0) emptyG
Proof
  PURE_REWRITE_TAC[ONE, line_graph_def, line_graph_zero]
  >> REFL_TAC
QED

Theorem adjacent_line_graph:
  ∀n a b.
    adjacent (line_graph n) a b ⇔
      case a of
        INL _ => F
      | INR a_val => case b of
                       INL _ => F
                     | INR b_val => a_val < n ∧
                                    b_val < n ∧
                                    (b_val = SUC a_val ∨ a_val = SUC b_val)
Proof  
  rpt gen_tac
  >> Induct_on ‘n’
  >- (rpt gen_tac >> Cases_on ‘a’ >- simp[] >> Cases_on ‘b’ >> simp[])
  >> Cases_on ‘n’
  >- (rpt gen_tac
      >> Cases_on ‘a’
      >- simp[]
      >> simp[]
      >> Cases_on ‘b’ >> simp[])
  >> rpt gen_tac
  >> Cases_on ‘a’
  >- (simp[line_graph_def, nodes_line_graph] >> gvs[]) 
  >> Cases_on ‘b’
  >- (simp[line_graph_def, nodes_line_graph] >> gvs[])
  >> gvs[line_graph_def, nodes_line_graph]
  >> pop_assum kall_tac
  >> EQ_TAC >> strip_tac >> gvs[] >> gvs[INSERT2_lemma]
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
