(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "relevant";

(* What definitions do I need to lift to the abstract layer, and what
   definitions should I leave in the representation layer? I find that there
   are a large number of definitions from the representation layer relating
   to fsgraphs which I don't want to re-implement in the abstraction layer. *)

(* extarctanh_def: *)

(* Maybe I should avoid dealing with INR i and instead deal with i itself.
   However, this may require writing many definitions which may expand the
   complexity of writing code for all the definitions *)

(* See messy usage of simplify_set_of_nonempty_if_no_nonempty inside
   gen_partite_gen_partite_ea. Is it possible to use this automatically as
   intended? *)

(* I am currently formalizing the log likelihood ratio version of the
   message passing algorithm, rather than the generalized version. *)

(* polar codes have been developed which are the first code to provably
   achieve/approach the Shannon limit. Maybe I should be working on them?
   However, apparently polar codes still have poor implementation in practice *)


val _ = export_theory();
