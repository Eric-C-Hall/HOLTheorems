(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "relevant";

(* What definitions do I need to lift to the abstract layer, and what definitions should I leave in the representation layer? *)

(* Could the name underlying_graph_abs be improved? *)

(* extarctanh_def: *)

(* is there a way to write underlying_graph_respects without lambda functions? *)

(* See messy usage of simplify_set_of_nonempty_if_no_nonempty inside gen_partite_gen_partite_ea. Is it possible to use this automatically as intended? *)

val _ = export_theory();
