open HolKernel Parse boolLib bossLib;

open probabilityTheory;
open listTheory;

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
(* TODO: Is there a union type in HOL4?                                       *)
(* TODO: Any pre-existing graph types?                                        *)
(* TODO: How do I represent the type of an arbitrary function, which can have *)
(* an arbitrary number of inputs?                                             *)
(* TODO: Should I use dir_graphTheory?                                        *)
(* TODO: How do I balance efficient implementation and usability?             *)
(*       In particular, defining a graph in terms of a set of nodes and a     *)
(*       set of edges is nice from a theoretical perspective, as it is a      *)
(*       relatively conceptually simple realisation, but if we want to find   *)
(*       the edges which connect to a node, this is relatively expensive.     *)
(*       Whereas defining a graph in terms of nodes, and describing the edges *)
(*       emanating from each node will make it easier to find the edges       *)
(*       connecting to that node, but we will either have to store the edge   *)
(*       in both directions, or finding the adjacent nodes will be hard again *)
(* TODO: Alternative representation could be defining a list of function nodes*)
(*       and a list of variable nodes independently. Then the edges could be  *)
(*       represented by pairs, where the first element of the pair represents *)
(*       the index of the function node and the second element of the pair    *)
(*       represents the index of the variable node.                           *)
(* TODO: In my initial interpretation, function nodes and variable nodes were *)
(*       each simply considered nodes, as the same kind of object, and each   *)
(*       node would have a boolean telling me whether it was a function or a  *)
(*       variable. However, the new version seems simpler: we don't have to   *)
(*       store whether each node is a variable or an object, and we can in    *)
(*       fact do away with all information within the variable nodes          *)
(*       completely, only storing the number of variable nodes.               *)
(* TODO: Should I change the list of (function, variable) pairs to some kind  *)
(*       of map?                                                              *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* We restrict our attention to factor graphs over a binary field,            *)
(* and to factor graphs which represent a probability distribution.           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Major question: How should I represent a function node?                    *)
(*                                                                            *)
(* I could represent a function node by a function which takes a list of      *)
(* (variable, value) pairs and returns a probability. Perhaps it should be a  *)
(* set of (variable, value) pairs, because the order doesn't matter? Perhaps  *)
(* we should prevent a particular variable from existing twice on the left    *)
(* hand side, because a variable can only be set to one value?                *)
(*                                                                            *)
(* A function over a single binary variable which outputs a probability can   *)
(* be represented as [output1, output2], where output1 is the probability     *)
(* represented on an input of 0, and output2 is the probability on an input   *)
(* of 1. This becomes more complicated (but still representable in the same   *)
(* way) if there are more than one input variable.                            *)
(*                                                                            *)
(* In a similar way, we could essentially represent a function like a big     *)
(* n-dimensional table, where n is the number of variables input to the       *)
(* function                                                                   *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* What do I want from my graph?                                              *)
(*                                                                            *)
(* - I want a graph object, which can be used to store all the data from the  *)
(*   graph, so I can provide it as input to another function                  *)
(* - I want a way to find the edges associated with a given node              *)
(* - I want a way to find the nodes associated with a given edge              *)
(* - I want a way to determine whether a given node is a function node or a   *)
(*   variable node                                                            *)
(* - I want a way to uniquely determine a variable node in the graph          *)
(* - I want a way to identify the function associated with a function node    *)
(* - I want a way of representing the message passing algorithm along that    *)
(*   graph, so that I can attach the appropriate data to the graph            *)
(*   -- This involves having a message passing in each direction along each   *)
(*      edge                                                                  *)
(*   -- This ought not to be directly part of the graph                       *)
(* - I want a way to go from an edge in the graph to the message passing data *)
(*   associated with that edge.                                               *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Graph design:                                                              *)
(*                                                                            *)
(* - The graph is a list of nodes and a list of edges.                        *)
(* - Each node is labelled according to its order in the list.                *)
(* - Each edge contains the label of the two nodes it connects. The edge is   *)
(*   not directed, so we do not need a second edge in the opposite direction. *)
(* - Each node contains a boolean which tells us whether it represents a      *)
(*   variable or a function                                                   *)
(* - If a node represents a function, it contains data representing the       *)
(*   function as per the "Function design" section.                           *)
(* - The message passing data is a function which takes the labels of the two *)
(*   nodes it connects and returns the message, which is a vector of length   *)
(*   two as is typical in the message passing algorithm.                      *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Function design:                                                           *)
(*                                                                            *)
(* We only need to store the marginals of the function with respect to each   *)
(* variable in the function. A single marginal can be stored as a vector of   *)
(* length two in the same way as a message is typically stored in the message *)
(* passing algorithm. We store each marginal in a list, starting with the     *)
(* marginal associated with the variable with the smallest label, and ending  *)
(* with the marginal associated with the variable with the largest label.     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* The factor graph                                                           *)
(* -------------------------------------------------------------------------- *)
Datatype:
  fg_type = <|
    functions : ((extreal list) list) list;
    num_variables : num;
    edges : (num # num) list;
  |>
End

(* -------------------------------------------------------------------------- *)
(* The data used by the message passing algorithm applied to the factor graph *)
(* -------------------------------------------------------------------------- *)
(*Datatype:
  fg_data = (num # num) -> (extreal list)
End*)

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
(* - The list of function nodes which are adjacent to the provided variable   *)
(*   node.                                                                    *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_function_nodes_def:
  fg_get_adjacent_function_nodes fg n =
  fg_get_adjacent_function_nodes_via_edges n fg.edges
End

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
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
