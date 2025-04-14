open HolKernel Parse boolLib bossLib;

open probabilityTheory;
open dirGraphTheory;


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
(* - Each edge contains the label of the two nodes it connects.               *)
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
(* The type used by                                                           *)
(* -------------------------------------------------------------------------- *)
Datatype:
  fg_function = extreal list;
End

(* -------------------------------------------------------------------------- *)
(* is_function: boolean which tells us whether the node represents a variable *)
(*   or a function                                                            *)
(* function: if the node represents a function, this tells us which funciton  *)
(*   it represents                                                            *)
(* -------------------------------------------------------------------------- *)

Datatype:
  fg_node = <|
    is_function : bool;
    variable_index : num;
    function : fg_function;
  |>
End

Datatype:
  fg = <|
    nodes : fg_node list;
    edges : (fg_node × fg_node) list;
  |>
End

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
(* The following example factor graph is based on Example 2.2:                *)
(* -------------------------------------------------------------------------- *)
Definition fg_example_def:
  fg_example = [<|
                   is_function = false;

                   function = ARB;
                 |>;
                <|
                |>
                <|
                |>
                <|
                |>
               ]
End

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
