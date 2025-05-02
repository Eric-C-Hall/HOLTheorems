(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "relevant";

(* partite_ea should probably use a finite map, not a function                *)

(* See messy usage of simplify_set_of_nonempty_if_no_nonempty inside gen_partite_gen_partite_ea. Is it possible to use this automatically as intended? *)

val _ = export_theory();
