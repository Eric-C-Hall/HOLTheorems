(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "relevant";

(* proof might be too unweildy and messy at where, in map_decoder_convolutional_codeScript, it says:
   "Subsume e3, and introduce a factor to handle the case in which e3
         is being taken with regards to an invalid stat"
*)

(* ------------------------------------------------------------ *)

(* Would be cool if given:

{(bs,ns) |
         LENGTH bs = n ∧ LENGTH ns = m ∧
         encode_recursive_parity_equation_state (ps,qs) ts
           (TAKE (LENGTH σs) bs) =
         σ}

         we could do a transformation on the final conjunct which requires
         some of the previous conjuncts as a precondition.
 *)

(* If we have the assumption a ≤ b and the assumption b ≤ a (of type num), then
   if we introduce a = b, this is removed in favour of the other assumptions.
   Rather, the other assumptions should be removed in favour of a = b *)

(* How do I convert a theorem of the form
   a ⇒ b ⇒ c to the form
   a ∧ b ⇒ c
 *)

(* How do I automatically prove the following:

         i ≤ LENGTH x
   ------------------------------------
        i + (LENGTH x − (i + 1)) = LENGTH x − 1

        related to decide_tac
        *)


(* ------------------------------------------ *)

(* see the simpset fragment map_decoder_SS. Discuss. How do I add my own
   simpset to gvs? *)

(* How to ensure that my simpset is visible both inside and outside the file in which its defined *)

(* Is it possible to write a congruence rule or something to make it easier to
   simplify the interior of argmax_bool, creating a chain
   argmax_bool P1 = argmax_bool P2 = argmax_bool P3 = ...
.
   Similarly for simplifying Σ f1 S = Σ f2 S = Σ f3 S = ...
 *)

(* --------------------------------------------- *)

(* map_decoderScript has unnecessarily large subgoal in
   map_decoder_bitwise_sum_bayes *)

(* ----------------- *)

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
