open HolKernel Parse boolLib bossLib;

open probabilityTheory;

val _ = new_theory "factor_graphs";

(* -------------------------------------------------------------------------- *)
(* TODO Is there a union type in HOL4?                                        *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* We restrict our attention to factor graphs over a binary field.            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* A factor graph is used to                                                                           *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* How should I represent a function?                                         *)
(*                                                                            *)
(* I could represent a function as a function which takes a                                            *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* is_function: boolean which tells us whether the node represents a variable *)
(*   or a function                                                            *)
(* variable_index: if the node represents a variable, this tells us which     *)
(*   variable it represents                                                   *)
(* function:                                                                  *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(*  *)
Datatype:
  factor_graph_node = <|
    is_function : bool;
    variable_index : num;
    function : real list
  |>
End

val _ = export_theory();
