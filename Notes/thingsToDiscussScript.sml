(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "relevant";

(* I am somewhat unclear on what theorems to prove for turbo codes.
   Proving that BCJR is an a posteriori decoder seems to be a good start.
   It is probably also a good idea to show that if the factor graph could be
   solved optimally instead of approximately, that would give us an a posteriori
   decoder for turbo codes. We could also show a correspondence between the
   factor graph interpreatation and the alternative interpretation.
 *)

(* There absolutely seems to be room for probability formalism here, in order
   to support my proofs and stuff.

   I get the feeling that all this probability formalism isn't completely
   explicit. Some things are commonly skimmed over, it's not always clear
   what the probability space is*)

(* Reliability: Turbo codes generally don't have the best reliability because
   the turbo decoding algorithm is heuristic in nature. Also, the choice of
   parity equations is typically done through computer search to find a good
   choice of parity equations rather than a principled and analytic approach,
   and the approach to Shannon's Limit is only what I believe to be an
   experimentally observed approach to within 0.7dB.

   I think it's good because it means that this isn't straightforward to
   formalise, giving rise to new novelty. *)

(* I would like to discuss with Reynald Affeldt . I also think it would be a
   good idea to have someone on my supervisory panel who is an expert in the
   error-correcting codes side of things. *)

(* Is it possible to define wfm_transition_fn in a better way which uses the
   lifting functionality to directly lift transition_fn? *)

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
