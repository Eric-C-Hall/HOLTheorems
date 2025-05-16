
(* -------------------------------------------------------------------------- *)
(* What do I want from my graph? (old)                                        *)
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
(* Graph design (old):                                                        *)
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
(* Function design (old):                                                     *)
(*                                                                            *)
(* Note: the following is false                                               *)
(*                                                                            *)
(*                                                                            *)
(* We only need to store the marginals of the function with respect to each   *)
(* variable in the function. A single marginal can be stored as a vector of   *)
(* length two in the same way as a message is typically stored in the message *)
(* passing algorithm. We store each marginal in a list, starting with the     *)
(* marginal associated with the variable with the smallest label, and ending  *)
(* with the marginal associated with the variable with the largest label.     *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* The factor graph (old)                                                     *)
(* -------------------------------------------------------------------------- *)
(*Datatype:
  fg_type = <|
    functions : ((extreal list) list) list;
    num_variables : num;
    edges : (num # num) list;
  |>
End*)

(* -------------------------------------------------------------------------- *)
(* The data used by the message passing algorithm applied to the factor graph *)
(* -------------------------------------------------------------------------- *)
(*Datatype:
  fg_data = (num # num) -> (extreal list)
End*)

(* -------------------------------------------------------------------------- *)
(* Prior suggestions for how to represent a function node                     *)
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
(* This theorem is very helpful in simplifying the above definition of        *)
(* gen_partite_ea if we happen to know that the empty set is not in v.        *)
(*                                                                            *)
(* Good to combine with gen_partite_empty_set_not_in                          *)
(* -------------------------------------------------------------------------- *)
Theorem simplify_set_of_nonempty_if_no_nonempty[simp] :
  ∀v.
    ∅ ∉ v ⇒ ({s | s ∈ v ∧ s ≠ ∅} = v)
Proof
  rpt strip_tac
  >> irule (iffRL EXTENSION)
  >> rpt strip_tac >> EQ_TAC >> rpt strip_tac >> gvs[]
  >> Cases_on ‘x’ >> gvs[]
QED




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
