
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
