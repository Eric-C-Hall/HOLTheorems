open HolKernel Parse boolLib bossLib;

open probabilityTheory;
(*open listTheory;*)
open fsgraphTheory;
open pred_setTheory;
open finite_mapTheory;

open partite_eaTheory;

val _ = new_theory "factor_graphs";

(* -------------------------------------------------------------------------- *)
(* This file defines factor graphs, which are used to efficiently calculate   *)
(* marginal probabilities.                                                    *)
(*                                                                            *)
(* Factor graphs can be used to implement the BCJR algorithm, which can be    *)
(* used to decode convolutional codes. This is of particular importance in    *)
(* decoding turbo codes.                                                      *)
(*                                                                            *)
(* We use the abbreviation "fg" regularly throughout this file to refer to    *)
(* factor graphs.                                                             *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* This is largely based on modern coding theory by Tom Richardson and        *)
(* Rüdiger Urbanke.                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Graph representation:                                                      *)
(*                                                                            *)
(* We use a representation based on fsgraphScript.                            *)
(*                                                                            *)
(* Each node has a label, in the form of a natural number.                    *)
(*                                                                            *)
(* Our graph is bipartite, and can be split up into function nodes and        *)
(* variable nodes                                                             *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Function representation:                                                   *)
(*                                                                            *)
(* function label -> ([list of variable labels in order],                     *)
(*                    bool list -> extreal)                                   *)
(*                                                                            *)
(* Where the bool list is the list of values that the variable inputs take.   *)
(*                                                                            *)
(* So, for example, f(x_1,x_2,x_3) =                                          *)
(*                   if x_1 then 0.5 else (if x_2 then 0.2 else 0.3)          *)
(*     would be represented by:                                               *)
(* "f" -> (["x_1", "x_2", "x_3"],                                             *)
(*         \x_1, x_2, x_3. if x_1 then 0.5 else (if x_2 then 0.2 else 0.3))   *)
(*                                                                            *)
(* Where "f" denotes a function label corresponding to f, which may, for      *)
(* example, be a num.                                                         *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Factor Graph Datatype:                                                     *)
(*                                                                            *)
(* The "underlying_graph" variable represents the underlying factor graph.    *)
(*                                                                            *)
(* Our graph is bipartite, split into the sets "function_nodes" and           *)
(* "variable_nodes"                                                           *)
(*                                                                            *)
(* function_map maps a function node to its function representation, as       *)
(* described in the "Function representation" section above.                  *)
(*                                                                            *)
(* We restrict our attention to factor graphs with binary inputs and outputs  *)
(* which represent probabilities (of type extreal).                           *)
(*                                                                            *)
(* We expect the nodes of the factor graph to be consecutive natural numbers  *)
(* starting from 0.                                                           *)
(* -------------------------------------------------------------------------- *)
Datatype:
  factor_graph =
  <|
    underlying_graph : fsgraph;
    colouring_function : (unit + num) -> num;
    function_map : (unit + num) |-> (unit + num) list # (bool list -> extreal);
  |>
End

(* -------------------------------------------------------------------------- *)
(* Well-formedness of a factor graph.                                         *)
(*                                                                            *)
(* - the underlying graph should be bipartite with respect to the function    *)
(*   nodes and variable nodes, assuming we have function nodes at all         *)
(* - the outputs of each function should be probabilities, and thus between   *)
(*   0 and 1                                                                  *)
(* - the variables used as input to each function must be amongst the         *)
(*   variable_nodes.                                                          *)
(* - the nodes should be the consecutive natural numbers starting from 0      *)
(* - We currently don't require that the input to the function map itself has *)
(*   to be a function node, because this doesn't gel well with the            *)
(*   representation of functions in HOL, which requires a function to have a  *)
(*   value for all inputs                                                     *)
(* -------------------------------------------------------------------------- *)
Definition wffactor_graph_def:
  wffactor_graph fg =
  (
  (
  (fg.function_nodes = ∅ ∧ nodes fg.underlying_graph = fg.variable_nodes) ∨
  (fg.variable_nodes = ∅ ∧ nodes fg.underlying_graph = fg.function_nodes) ∨
  (gen_bipartite fg.underlying_graph fg.function_nodes fg.variable_nodes)
  ) ∧
  (∀f bs.
     f ∈ fg.function_nodes ⇒
     (let
        output = (SND (fg.function_map f)) bs;
     in
       0 ≤ output ∧ output ≤ 1
     )
  ) ∧
  (∀f.
     f ∈ fg.function_nodes ⇒
     (let
        variables = FST (fg.function_map f)
     in
       ∀x. x ∈ (set variables) ⇒ x ∈ fg.variable_nodes
     )
  ) ∧
  (∃n.
     fg.variable_nodes ∪ fg.function_nodes = {INR i | i ∈ count n}
  )
  )
End

(* -------------------------------------------------------------------------- *)
(* Create an empty factor graph                                               *)
(* -------------------------------------------------------------------------- *)
Definition fg_empty_def:
  fg_empty = <|
    underlying_graph := emptyG;
    function_nodes := {};
    variable_nodes := {};
    function_map := ARB;
  |>
End

(* -------------------------------------------------------------------------- *)
(* The empty graph is bipartite into the empty set and the empty set          *)
(*                                                                            *)
(* This theorem would be convenient, but isn't true, because a partition is   *)
(* only considered to be valid if each of the components is nonempty. I don't *)
(* think this should be how a partition is defined, but on the other hand,    *)
(* there is some precedent for this.                                          *)
(* -------------------------------------------------------------------------- *)
(*Theorem gen_bipartite_empty[simp]:
  gen_bipartite emptyG ∅ ∅
Proof
  gvs[gen_bipartite_def]
QED*)

(* -------------------------------------------------------------------------- *)
(* Prove that the empty factor graph is well-formed                           *)
(* -------------------------------------------------------------------------- *)
Theorem fg_empty_wf[simp]:
  wffactor_graph fg_empty
Proof
  gvs[fg_empty_def, wffactor_graph_def]
  >- (qexists ‘0’ >> gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* Add a variable node to the factor_graph.                                   *)
(*                                                                            *)
(* The first node added (variable or function) should be 0, the next node     *)
(* should be 1, etc.                                                          *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_variable_node_def:
  fg_add_variable_node fg =
  let
    new_node = (INR (CARD (nodes fg.underlying_graph)))
  in
    fg with
       <|
         underlying_graph := fsgAddNode new_node fg.underlying_graph;
         variable_nodes := new_node INSERT fg.variable_nodes
       |>
End

(* -------------------------------------------------------------------------- *)
(* Adds n variable nodes to the factor graph                                  *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_n_variable_nodes_def:
  fg_add_n_variable_nodes fg 0 = fg ∧
  fg_add_n_variable_nodes fg (SUC n) =
  fg_add_variable_node (fg_add_n_variable_nodes fg n)
End

(* -------------------------------------------------------------------------- *)
(* The next few theorems explore the properties of {INR i | i ∈ count n},    *)
(* which can equivalently be described as {INR i | i < n}                     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Fundamental inductive method used to produce a set of this form. This      *)
(* allows us to work by induction on this set.                                *)
(* -------------------------------------------------------------------------- *)
Theorem INR_COMP_SUC:
  ∀n : num.
    {INR i | i < SUC n} = (INR n) INSERT {INR i | i < n}
Proof
  rpt strip_tac
  >> irule (iffRL EXTENSION)
  >> rpt strip_tac
  >> Cases_on ‘x’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* In order to associate a finite cardinality with this set, we first need to *)
(* know that it's finite.                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem FINITE_INR_COMP[simp]:
  ∀n : num.
    FINITE {INR i | i < n}
Proof
  rpt strip_tac
  >> Induct_on ‘n’ >> gvs[]
  >> gvs[INR_COMP_SUC]
QED

(* -------------------------------------------------------------------------- *)
(* Useful for simplification in fg_add_variable_node_wf                       *)
(* -------------------------------------------------------------------------- *)
Theorem CARD_INR_COMP[simp]:
  ∀n.
    CARD {INR i | i < n} = n
Proof
  rpt strip_tac >> gvs[]
  >> Induct_on ‘n’ >> gvs[]
  >> gvs[INR_COMP_SUC]
QED

(* -------------------------------------------------------------------------- *)
(* Proof that after adding a variable node, the resulting factor graph will   *)
(* be well-formed.                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_variable_node_wf[simp]:
  ∀fg.
    wffactor_graph fg ⇒
    wffactor_graph (fg_add_variable_node fg)
Proof
  rpt strip_tac
  >> gvs[wffactor_graph_def, fg_add_variable_node_def]
  >- (qexists ‘SUC n’ >> gvs[INR_COMP_SUC])
  >- (conj_tac
      >- (Cases_on ‘n’ >> gvs[]
          >> disj2_tac
          >> gvs[gen_bipartite_def]
          >> gvs[INR_COMP_SUC]
          >> conj_tac
          >- (gvs[UNION_DEF, INSERT_DEF]
              >> irule (iffRL EXTENSION)
              >> rpt strip_tac >> Cases_on ‘x’ >> gvs[]
             )
          >> rpt strip_tac
          >> ‘F’ suffices_by gvs[] (* We cannot have any two edges in the orig *)

                                Cases_on ‘{INR i | i < n} = ∅’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Add a function node to the factor graph.                                    *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - f, the function to be added.                                             *)
(*                                                                            *)
(* Output:                                                                    *)
(* - the factor graph with the new function node. The edges to other variable *)
(* ts label will be the next  *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*   unused label.                                                            *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_function_node_def:
  fg_add_function_node fg f =
  let
    new_node = (INR (CARD (nodes fg.underlying_graph)))
  in
    fg with
       <|
         underlying_graph := fsgAddNode new_node fg.underlying_graph;
         function_nodes := new_node INSERT fg.variable_nodes;
         function_map := λfunction_label.
                           if function_label = new_node
                           then
                             f
                           else
                             fg.function_map function_label
       |>
End

(* -------------------------------------------------------------------------- *)
(* Adding a function node to a factor graph maintains well-formedness         *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_function_node_wf[simp]:
  ∀fg.
    wffactor_graph fg ⇒
    wffactor_graph (fg_add_variable_node fg)
Proof
  rpt strip_tac
  >> gvs[wffactor_graph_def, fg_add_variable_node_def]
QED

(* -------------------------------------------------------------------------- *)
(* Prove that two elements in a two-element set can be swapped                *)
(* -------------------------------------------------------------------------- *)
Theorem set_two_element_sym:
  ∀n1 n2.
    {n1; n2} = {n2; n1}
Proof
  rpt strip_tac
  >> gvs[INSERT_DEF]
  >> irule (iffRL EXTENSION)
  >> rpt strip_tac
  >> gvs[]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* Adds an edge between two nodes in the graph.                               *)
(*                                                                            *)
(* If the edge would be between a function node and a function node or a      *)
(* variable node and a variable node, this returns turns ARB, which should    *)
(* hopefully indicate that something has gone wrong.                          *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n1, the first node to                                                    *)
(* - n2, the second node                                                      *)
(*                                                                            *)
(* Output:                                                                    *)
(* - the updated factor graph                                                 *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_edge_def:
  fg_add_edge fg n1 n2 =
  if ((n1 ∈ fg.variable_nodes ∧ n2 ∈ fg.variable_nodes) ∨
      (n1 ∈ fg.function_nodes ∧ n2 ∈ fg.function_nodes))
  then
    ARB
  else
    fg with
       <|
         underlying_graph := fsgAddEdges {{n1; n2}} fg.underlying_graph
       |>
End

(* -------------------------------------------------------------------------- *)
(* Prove that adding an edge between two elements is the same regardless of   *)
(* which order the two elements are provided in                               *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_edge_sym:
  ∀fg n1 n2.
    fg_add_edge fg n1 n2 = fg_add_edge fg n2 n1
Proof
  rpt strip_tac
  >> gvs[fg_add_edge_def]
  >> rw[]
  >> Cases_on ‘n1 ∈ fg.variable_nodes’ >> Cases_on ‘n2 ∈ fg.variable_nodes’ >> Cases_on ‘n1 ∈ fg.function_nodes’ >> Cases_on ‘n2 ∈ fg.function_nodes’ >> gvs[]
  >> gvs[set_two_element_sym]
QED

Theorem fg_add_edge_wf_spec:
  ∀fg n1 n2.
    (n1 ∈ fg.variable_nodes ∧ n2 ∈ fg.function_nodes) ⇒
    wffactor_graph (fg_add_edge fg n1 n2)
Proof
  rpt strip_tac
  >> gvs[wffactor_graph_def, fg_add_edge_def]
  >> 
QED

Theorem fg_add_edge_wf:
  ∀fg n1 n2.
    ((n1 ∈ fg.variable_nodes ∧ n2 ∈ fg.function_nodes) ∨
     (n1 ∈ fg.function_nodes ∧ n2 ∈ fg.variable_nodes)) ⇒
    wffactor_graph (fg_add_edge fg n1 n2)
Proof
  rw[]
  >> metis_tac[fg_add_edge_wf_spec, fg_add_edge_sym]
QED

(* -------------------------------------------------------------------------- *)
(* Adds several variable and function nodes. This is intended to be much      *)
(* easier to use than manually calling fg_add_variable_node and               *)
(* fg_add_function_node repeatedly.                                            *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph to add the nodes to.                                *)
(* - nt::nts (aka. node types), a list of booleans, where the ith element is  *)
(*   T if we need to add a function node and F if we need to add a variable   *)
(*   node.                                                                    *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_variable_and_function_nodes:
  fg_add_variable_and_function_nodes fg [] = fg ∧
  fg_add_variable_and_function_nodes fg nt::nts =
  let
    recursive_call = fg_add_variable_and_function_nodes fg nts
  in
    if nt
    then
      fg_add_function_node      
    else
Proof
QED


(* -------------------------------------------------------------------------- *)
(* Example 2.2 from Modern Coding Theory:                                     *)
(*                                                                            *)
(* f(x_1, x_2, x_3, x_4, x_5, x_6) = f_1(x_1, x_2, x_3) f_2(x_1, x_4, x_6)    *)
(*                                   f_3(x_4) f_4(x_4, x_5)                   *)
(*                                                                            *)
(* Example 2.2 factor graph:                                                  *)
(*                                                                            *)
(*                            x_1                                             *)
(*                           /   \                                            *)
(*                          /     \                                           *)
(*                         f_1     f_2                                        *)
(*                        /  |     |  \                                       *)
(*                       /   |     |   \                                      *)
(*                     x_2  x_3    x_4  x_6                                   *)
(*                                /  \                                        *)
(*                               /    \                                       *)
(*                              f_3   f_4                                     *)
(*                                     |                                      *)
(*                                     |                                      *)
(*                                    x_5                                     *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(* The following example factor graph is based on Example 2.2.                *)
(* -------------------------------------------------------------------------- *)
Definition fg_example_factor_graph_def:
  fg_example_factor_graph = fg_add_variable_node ∘ fg_add_variable_node ∘ fg_add_function_node ∘ fg_add_variable_node fg_empty
End

Definition fg_example_functions_def:
  fg_example_functions =
  λf. if f = 1 then
        ([0, 2, 3], λxs. ARB)
      else if f = 4 then
        ([0, 5, 9], λxs. ARB)
      else if f = 6 then
        ([5], λxs. ARB)
      else if f = 7 then
        ([5, 8], λxs. ARB)
      else ARB
End

Definition fg_example_def:
  fg_example =
  <|
    functions := [ARB; ARB; ARB];
    num_variables := 6;
    edges := [
        (0, 0);
        (0, 1);
        (0, 2);
        (1, 0);
        (1, 3);
        (1, 5);
        (2, 3);
        (3, 3);
        (3, 4);
      ];
  |>
End

(* -------------------------------------------------------------------------- *)
(* The following is a manually designed example graph based on Example 2.2    *)
(* -------------------------------------------------------------------------- *)
Definition helloworld_graph_def:
  helloworld_graph : fsgraph =
  fsgAddEdges {
              {INR 0; INR 1;};
           {INR 1; INR 2;};
           {INR 1; INR 3;};
           {INR 0; INR 4;};
           {INR 4; INR 5;};
           {INR 5; INR 6;};
           {INR 5; INR 7;};
           {INR 7; INR 8;};
           {INR 4; INR 9;};
           } (fsgAddNodes {INR x | x ∈ count 10} emptyG)
End

(* -------------------------------------------------------------------------- *)
(* Gets the variable nodes adjacent to a given function node via one of the   *)
(* provided edges.                                                            *)
(*                                                                            *)
(* Input:                                                                     *)
(* - n, the index of the function node we want to find the connected variable *)
(*   nodes of                                                                 *)
(* - edges, the list of edges we may take                                     *)
(*                                                                            *)
(* Output:                                                                    *)
(* - The list of variable nodes which are connected to the funtion node via   *)
(*   an edge.                                                                 *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_variable_nodes_via_edges_def:
  fg_get_adjacent_variable_nodes_via_edges n [] = [] ∧
  fg_get_adjacent_variable_nodes_via_edges
  n ((function_index, variable_index)::remaining_edges) =
  let
    recursive_call = fg_get_adjacent_variable_nodes_via_edges n remaining_edges;
  in
    if (function_index = n)
    then (variable_index)::recursive_call
    else recursive_call
End

(* -------------------------------------------------------------------------- *)
(* Gets the variable nodes adjacent to a given function node                  *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n, the index of the function node we want to find the connected variable *)
(*   node of                                                                  *)
(*                                                                            *)
(* Output:                                                                    *)
(* - The list of variable nodes which are adjacent to the function node via   *)
(*   an edge in the factor graph                                              *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_variable_nodes_def:
  fg_get_adjacent_variable_nodes fg n =
  fg_get_adjacent_variable_nodes_via_edges n fg.edges
End

(* -------------------------------------------------------------------------- *)
(* Gets the function nodes adjacent to a particular variable node             *)
(*                                                                            *)
(* Input:                                                                     *)
(* - n, the index of the variable node we are finding the adjacent function   *)
(*   nodes for                                                                *)
(* - edges, the list of edges that we may take                                *)
(*                                                                            *)
(* Output:                                                                    *)
(* - The list of function nodes which are adjacent to the variable node via   *)
(*   one of the provided edges                                                *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_function_nodes_via_edges_def:
  fg_get_adjacent_function_nodes_via_edges n [] = [] ∧
  fg_get_adjacent_function_nodes_via_edges
  n ((function_index, variable_index)::remaining_edges) =
  let
    recursive_call = fg_get_adjacent_function_nodes_via_edges n remaining_edges;
  in
    if (variable_index = n)
    then (function_index)::recursive_call
    else recursive_call
End

(* -------------------------------------------------------------------------- *)
(* Gets the function nodes connected to a given variable node                 *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n, the index of the variable node we are finding the adjacent function   *)
(*   nodes for                                                                *)
(*                                                                            *)
(* Output:                                                                    *)
(* - The list of function node indices which are adjacent to the provided     *)
(* variable node.                                                             *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_function_nodes_def:
  fg_get_adjacent_function_nodes fg n =
  fg_get_adjacent_function_nodes_via_edges n fg.edges
End

(*Definition deduplicate_def:
  deduplicate [] = [] ∧
  deduplicate l::ls = if ()
                         End*)

(* -------------------------------------------------------------------------- *)
(* Gets the function nodes that are adjacent to nodes which themselves are    *)
(* adjacent to the given function node                                        *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n, the index of the variable node we start from                          *)
(*                                                                            *)
(* Output:                                                                    *)
(* - The list of function nodes which are adjacent to variable nodes which    *)
(* themselves are adjacent to the function node n (Duplicates may be present) *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_adjacent_function_nodes_def:
  fg_get_adjacent_adjacent_function_nodes fg n =
  FOLDR APPEND [] (MAP (fg_get_adjacent_function_nodes fg) (fg_get_adjacent_variable_nodes fg n))
End

(* -------------------------------------------------------------------------- *)
(* Deduplicate fg_get_adjacent_adjacent_function_nodes                        *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_adjacent_function_nodes_no_duplicates_def:
  fg_get_adjacent_adjacent_function_nodes_no_duplicates fg n =
End 

(* -------------------------------------------------------------------------- *)
(* Gets the function nodes that are adjacent to a particular                  *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_function_nodes_taboo_def:
  fg_get_adjacent_function_nodes_taboo fg
End

(* -------------------------------------------------------------------------- *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n, the index of the function node to find the connected region from      *)
(* - taboo_nodes, the list of function nodes that we cannot go to             *)
(* Output:                                                                    *)
(* - A list of node indexes that are contained in the connected region        *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_connected_region_taboo_def:
  fg_get_connected_region_taboo fg n taboo_nodes =
  
End

(* -------------------------------------------------------------------------- *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n, the index of the function node to find the connected region from      *)
(* Output:                                                                    *)
(* - A list of node indexes that are contained in the connected region        *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_connected_region_def:
  fg_get_connected_region fg n = fg_get_connected_region_taboo fg n []
End

Definition fg_split_into_trees_recursive_def:
  fg_split_into_trees_recursive fg [] = [] ∧
  fg_split_into_trees_recursive fg available_nodes =
  let
    (nodes_in_tree, other_nodes) = fg_get_nodes_in_tree fg (HD available_nodes)
  in
    nodes_in_tree::fg_split_into_trees_
End

(* *)
Definition fg_split_into_trees_def:
  fg_split_into_trees fg = fg_split_into_trees_recursive fg (COUNT (LENGTH fg.nodes))
End

Definition fg_identify_leaves_def:
  fg_identify_leaves = 
End

Definition fg_initialise_messages_def:
  fg_initialise_messages = 
End


Definition fg_calculate_data_def:
  fg_calculate_data = 
End





(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition fg_leaf_nodes_def:
  fg
End


(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition calculate_message_passing_def:


End

val _ = export_theory();
