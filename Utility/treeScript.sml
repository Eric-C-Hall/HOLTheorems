
Theory tree

Ancestors arithmetic extreal fsgraph fundamental genericGraph indexedLists list marker pred_set product_order relation rich_list

Libs dep_rewrite ConseqConv donotexpandLib;

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
(* - "a ++ b" denotes appending two paths                                     *)
(* - We use (tr) to denote that the given theorem holds only for trees        *)
(*                                                                            *)
(* Most important theorems:                                                   *)
(*                                                                            *)
(* - Paths in a connected graph exist between any two points                  *)
(*   (connected_exists_path)                                                  *)
(* - Paths in a tree are unique (tr) (is_tree_path_unique)                    *)
(* - A walk may be restricted to a path (restrict_walk_to_path)               *)
(* - If c and d are on a - b, then c - d is a subpath of a - b (tr)           *)
(*   (get_path_drop_take)                                                     *)
(* - We have a - c = (a - b) ++ (b - c), so long as b is on a - c (tr).       *)
(*   (get_path_append)                                                        *)
(* - We may join together two overlapping paths: if we have a - c and b - d,  *)
(*   and c is in b - d and b is in a - c, then (join_overlapping_paths_mem)   *)
(* - If we have two nonequal paths that start with the same value, there is   *)
(*   a point at which they diverge (exists_point_of_divergence)               *)
(* - If we have two paths that start at different values but end in the same  *)
(*   (exists_point_of_convergence)                                            *)
(*                                                                            *)
(*                                                                            *)
(* - We may join together two overlapping paths: if we have a - c and b - d   *)
(* - A tree has no cycles (from definition)                                   *)
(*                                                                            *)
(*                                                                            *)
(*  adjacent_mem_get_path                                                     *)
(*  subtrees_distinct                                                         *)
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
  >- metis_tac[adjacent_members]
  >> rpt strip_tac
  >> Cases_on ‘v1 = a ∧ v2 = b’ >> gvs[]
  >> Cases_on ‘v1 = a’ >> gvs[adjacent_iff]
QED

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

Theorem is_tree_path_get_path:
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
      3 ≤ LENGTH vs ∧
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
  >- gvs[]
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
  >> simp[is_tree_path_get_path]
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

Theorem path_reverse:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph vs.
    path g vs ⇔ path g (REVERSE vs)
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

Theorem leq_len_get_path[simp]:
  ∀g a b.
    exists_path g a b ⇒
    1 ≤ LENGTH (get_path g a b)
Proof
  rpt strip_tac
  >> Cases_on ‘get_path g a b’ >> gvs[]
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

(* -------------------------------------------------------------------------- *)
(* If we have a path from a to b, and x is on this path and x is adjacent to  *)
(* a, then x must be the second node on the path.                             *)
(*                                                                            *)
(* This follows from uniqueness of paths: otherwise, we could choose either   *)
(* go directly to x or we could choose to take the long way via the path.     *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_mem_get_path:
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

(* -------------------------------------------------------------------------- *)
(* The subtree of nodes reachable by taking a certain edge from a certain     *)
(* node is disjoint from the subtree of nodes reachable by taking a different *)
(* edge from that node                                                        *)
(* -------------------------------------------------------------------------- *)
Theorem subtrees_distinct:
  ∀g root n m.
    adjacent g root n ∧
    adjacent g root m ∧
    n ≠ m ⇒
    nodes (subtree g root n) ∩ nodes (subtree g root m) = ∅
Proof
  rpt strip_tac
  >> gvs[subtree_def, subgraph_def]
  >> gvs[EXTENSION]
  >> rpt strip_tac
  >> CCONTR_TAC >> gvs[]
  >> sg ‘EL 2 (get_path g root' x) = n’
  >- (
  )
  >> gvs[]
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
(* We work by strong induction on the length of a-d.                          *)
(*                                                                            *)
(*       a ----------------- b ----------------- c ----------------- d        *)
(*                                                                            *)
(* If b is in a-d, then c is too, because the presence of b in a-d allows us  *)
(* to break it down into a-b and b-d, and we know that c is in b-d.           *)
(*                                                                            *)
(* Likewise, if c is in a-d, then b is too.                                   *)
(*                                                                            *)
(* So either b and c are both in a-d, or neither is in a-d.                   *)
(*                                                                            *)
(* We want to prove that both are in a-d, so we assume that neither is in     *)
(* a-d and seek to derive a contradiction.                                    *)
(*                                                                            *)
(* Because b is not in a-d, there must be some point e before b which is      *)
(* contained in a-c and also contained in a-d, because a-c and a-d start at   *)
(* the same point and must diverge at some point, and this point will be      *)
(* before b because b is not in a-d.                                          *)
(*                                                                            *)
(* Likewise, there is a point f after c which is contained in b-d and also    *)
(* contained in a-d.                                                          *)
(*                                                                            *)
(*     a -------- e -------- b ----------------- c -------- f -------- d      *)
(*                                                                            *)
(* Thus, using get_path_append:                                               *)
(* - We can split a-d into a-e and e-d                                        *)
(* - We can split a-c into a-e and e-c                                        *)
(* - We can split a-d into a-f and f-d                                        *)
(* - We can split b-d into b-f and f-d                                        *)
(*                                                                            *)
(* Now we can apply our inductive hypothesis to e-c and b-f. This follows     *)
(* from the fact that e-f is strictly shorter than a-d. We also need the fact *)
(* that b is in e-c, which follows from b is in e-c and b is not in a-e, and  *)
(* the fact that c is in b-f, which follows in a likewise manner.             *)
(*                                                                            *)
(* Thus, b is in e-c and hence is in a-c, deriving our desired contradiction. *)
(*                                                                            *)
(* QED                                                                        *)
(* -------------------------------------------------------------------------- *)
Theorem join_overlapping_paths_mem:
  ∀g : ('a, 'b, 'c, 'd, 'e, 'f) udgraph a b c d.
    is_tree g ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    c ∈ nodes g ∧
    d ∈ nodes g ∧
    MEM b (get_path g a c) ∧
    MEM c (get_path g b d) ∧
    b ≠ c ⇒
    MEM b (get_path g a d)
Proof
  (* Prepare for strong induction on the length of the path by creating a
     variable which tells us the length of the path *)
  rpt strip_tac
  >> qabbrev_tac ‘l = LENGTH (get_path g a d)’
  >> gs[Abbrev_def]
  >> rpt (pop_assum mp_tac) >> SPEC_ALL_TAC
  (* Perform strong induction on the length of the path *)
  >> completeInduct_on ‘l’
  (* Do not expand inductive hypothesis, in order to avoid causing the
     simplifier to waste time attempting and failing to use the inductive
     hypothesis *)
  >> donotexpand_tac
  (* We work by contradiction *)
  >> rpt strip_tac
  >> CCONTR_TAC
  (* Prove that c cannot be in a-d *)
  >> sg ‘¬MEM c (get_path g a d)’
  >- (CCONTR_TAC
      >> gvs[]
      (* Since c is in a-d, we can split a-d at c *)
      >> qspecl_then [‘g’, ‘a’, ‘c’, ‘d’] assume_tac get_path_append
      (* At this point, it's smart enough to automatically prove this subgoal *)
      >> gvs[]
     )
  (* We want to prove that the point e described in the proof sketch exists.
     We can do this using exists_point_of_divergence, if we can find some point
     at which To prove that

     
   In order to prove that the point e described in the proof sk

prove that there's a point prior to b at which divergence
     occurs, we need to prove that there's a point at which a-d differs from
     a-c. Because b is not in a-d but it is in a-c, that is a candidate point
     for this*)
     
  (* Because b is not in a-d but it is in a-c, we know that a-d and a-c differ
     at b (but are the same at a), so we can use exists_point_of_divergence to
     prove that there's a point prior to b at which divergence occurs *)
  >> qspecl_then [‘get_path g a c’,
                  ‘get_path g a d’,
                  ‘findi b (get_path g a c)’] assume_tac
                 exists_point_of_divergence
  >> gvs[]
  >> sg ‘findi b (get_path g a c) < ’
  >> findi b (get_path g a c)
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Update comments at start for this                                    *)
(* -------------------------------------------------------------------------- *)
Theorem join_overlapping_paths:

Proof
QED

Theorem subtree_subset:
  ∀g a b c.
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
  >> gvs[subgraph_def]
  >> gvs[PSUBSET_DEF]
  >> REVERSE conj_tac
  >- (gvs[EXTENSION] >> rpt strip_tac
      >> qexists ‘b’
      >> gvs[is_tree_get_path_same]
     )
  >> gvs[SUBSET_DEF]
  >> rpt strip_tac
  >> 


  >> sg ‘get_path g a x = get_path g a b ++ TL (get_path g b x)’
  >> irule get_path_append
  >> simp[]
QED

Theorem order_subtree_lt:
  ∀g a b c.
    is_tree g ∧
    a ≠ b ∧
    b ≠ c ∧
    a ∈ nodes g ∧
    b ∈ nodes g ∧
    c ∈ nodes (subtree g a b) ⇒
    order (subtree g b c) < order (subtree g a b)
Proof
  rpt strip_tac
QED

Theorem order_subtree_lt_adjacent:
  ∀g a b c.
    is_tree g ∧
    adjacent g a b ∧
    adjacent g b c ∧
    c ≠ a ⇒
    order (subtree g b c) < order (subtree g a b) 
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





