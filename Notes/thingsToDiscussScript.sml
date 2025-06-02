(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "relevant";

(* I would like to discuss with Reynald Affeldt . I also think it would be a good idea to have someone on my supervisory panel who is an expert in the error-correcting codes side of things. *)

(* Turns out I need to have more general variables in my factor graph? We should work out how we are going to do this. *)

(* What definitions do I need to lift to the abstract layer, and what
   definitions should I leave in the representation layer? I find that there
   are a large number of definitions from the representation layer relating
   to fsgraphs which I don't want to re-implement in the abstraction layer. *)

(* extarctanh_def: *)

(* Maybe I should avoid dealing with INR i and instead deal with i itself.
   However, this may require writing many definitions which may expand the
   complexity of writing code for all the definitions *)

(* I am currently formalizing the log likelihood ratio version of the
   message passing algorithm, rather than the generalized version. *)

(* polar codes have been developed which are the first code to provably
   achieve/approach the Shannon limit. Maybe I should be working on them?
   However, apparently polar codes still have poor implementation in practice *)

val _ = export_theory();
