(* Written by Eric Hall *)

Theory thingsToDiscuss

Ancestors extreal probability

Libs dep_rewrite;

Theorem cheat1:
  ∀val_map ns1 ns2 fg excl_val_map1 excl_val_map2.
    val_map ∈ val_map_assignments fg ns1 excl_val_map1 ∧
    ns2 ⊆ ns1 ∧
    excl_val_map2 ⊑ DRESTRICT excl_val_map1 ns2 ⇒
    DRESTRICT val_map ns2 ∈ val_map_assignments fg ns2 excl_val_map2
Proof
  cheat
QED

(* -------------------------------------------------------------------------- *)
(* This expression occurs naturally when sp_message is applied to something,  *)
(* so automatically simplify it.                                              *)
(* -------------------------------------------------------------------------- *)
Theorem cheat2:
  ∀fg f ns val_map.
    val_map ∈ val_map_assignments fg ns1 excl_val_map1 ∧
    ns ⊆ ns1 ⇒
    FUN_FMAP f (val_map_assignments fg ns FEMPTY) '
             (DRESTRICT val_map ns) = f (DRESTRICT val_map ns)
Proof
  cheat
QED

(* -------------------------------------------------------------------------- *)
(* I am trying to rewrite FUN_FMAP f _ ' x into f x. I have cheat1 and        *)
(* cheat2, but they each have a precondition that cannot be solved because it *)
(* has variables that aren't specified in the postcondition and thus need to  *)
(* be instantiated, as they are existential conditions.                       *)
(* -------------------------------------------------------------------------- *)
Theorem test1:
  is_tree (get_underlying_graph fg) ∧
  adjacent (get_underlying_graph fg) dst src ∧
  src ≠ dst ∧
  src ∈ nodes (get_underlying_graph fg) ∧
  dst ∈ nodes (get_underlying_graph fg) ∧
  (∀b. adjacent (get_underlying_graph fg) b src ⇒
       b ∉ get_function_nodes fg) ∧
  src ∈ get_function_nodes fg ∧
  excl_val_map ∈ val_map_assignments fg {dst} FEMPTY
  ⇒
  ∑
  (λval_map.
     get_function_map fg ' src ' val_map *
     ∏
     (λprev.
        FUN_FMAP
        (λexcl_val_map'.
           sum_prod fg
                    (nodes
                     (subtree (get_underlying_graph fg) src prev) ∪
                     {prev}) excl_val_map')
        (val_map_assignments fg {prev} FEMPTY) '
        (DRESTRICT val_map {prev}))
     {prev |
     (prev ∈ nodes (get_underlying_graph fg) ∧
      adjacent (get_underlying_graph fg) prev src) ∧ prev ≠ dst})
  (val_map_assignments fg (adjacent_nodes fg src) excl_val_map) =
  sum_prod fg
           (nodes (subtree (get_underlying_graph fg) dst src) ∪ {dst})
           excl_val_map
Proof
  rpt strip_tac
  >> ‘∀prev. prev ∈ nodes (get_underlying_graph fg) ∧ adjacent (get_underlying_graph fg) prev src ⇒ {prev} ⊆ adjacent_nodes fg src’ by cheat
  >> simp[Cong EXTREAL_SUM_IMAGE_CONG,
          Cong EXTREAL_PROD_IMAGE_CONG,
          SUBSET_DEF,
          SPEC “excl_val_map : unit + num |-> bool list”
               (GEN “excl_val_map1 : unit + num |-> bool list”
                    (SPEC “adjacent_nodes fg src : unit + num -> bool”
                          (GEN “ns1 : unit + num -> bool”
                               (SPEC “fg: α factor_graph” FUN_FMAP_val_map_assignments_DRESTRICT))))]
QED

(* I'm struggling with trying to perform a rewrite when the precondition has things that aren't in the postcondition. This is inside a ∑ f S, and we rely on the fact that x ∈ S to rewrite f. *)

(* How can I qspecl on things in the middle, while leaving the first untouched? *)

(* Review val_map_assignments_cong in message_passingScript: should I move
   the FDOM comparison into the next condition? *)

Theorem test2:
  ∀s f c.
    ∑ (λx. Normal c * f x) s = Normal c * ∑ f s
Proof
  cheat
QED

(* DEP_PURE_ONCE_REWRITE_TAC doesn't work in test2 but does in test3.
   This is expected behaviour and correct behaviour, but it's also
   interesting behaviour because it's unclear to me exactly how that's working
   *)
Theorem test2:
  ∑ (λx. Normal (K 2 x) * x) ARB = ARB
Proof
  DEP_PURE_ONCE_REWRITE_TAC[test1]
QED

Theorem test3:
  ∑ (λx. Normal (K 2 4) * x) ARB = ARB
Proof
  DEP_PURE_ONCE_REWRITE_TAC[test1]
QED

(* Second annual report due *)

(* Why isn't qid_spec_tac in the HOL reference? I rebuilt HOL and the reference to see if it was in the newest version, but it wasn't there. *)

(* Congruence rules seem really useful. Perhaps we can discuss them. *)
     
(* Lifting does seem convenient *)

(* Discuss my Zulip post *)

(* Suppose I want to prove P n m by induction, n and m are nums.
   I want my inductive hypothesis to be: P n m if either n OR m is smaller, and
   the other is at least as small. How would I go about doing this?

   Review my code kind of to this effect
 *)

(* Product order? Strict product order? Are these concepts defined in HOL4? *)

(* matchingScript is reaching the stack limit for gvs. Perhaps it could be
   made faster very easily by reducing the stack limit for that file or the
   slow proofs? How would one do that? *)

(* How do I use multiset comprehensions? The documentation says that multisets
   are represented by α -> num instead of α -> bool, where the num defines the
   multiplicity. In the multiset comprehension {_ || _ || _}, will it
   automatically take care of multiplicity for me if I use a function to bool
   in the last part? *)

(* --- ALREADY DISCUSSED --- *)

(* In sp_message, I add an if statement which isn't necessary, but it won't
   recognise termination without the information given by the if statement.
   Is it possible to avoid doing that?

 Answer: use congruence rules. These are explained in the description notes, and
         also examples have been written called EXTREAL_PROD_IMAGE_CONG,
         EXTREAL_SUM_IMAGE_CONG, and ITSET_CONG, as used in
         message_passingScript *)

(* I have defined sp_calculate_messages0 and proven that it always terminates.
   Can I induct on the recursive calls of this function? Some property holds on
   termination, therefore the property holds 1 call before termination,
   therefore the property holds 2 calls before termination, etc. I think I
   remember there being something along the lines of inductive definitions?

 Answer: when creating a definition which requires a termination proof, an
         induction theorem should be automatically generated. Try using that. *)



(* --- ALREADY DISCUSSED --- *)

(* I was actively working for about 61 hours and 12 minutes over the past 2
   weeks *)

(* Modified the message passing algorithm to work with the modified factor graph
   which allows variable nodes to have length other than 1.
   
   Added code to calculate the final result of message passing: previously it
   would just calculate the messages
   
   Fixed bug in the indexing of nodes in the factor graph

   In process: Relating factor graph to sum-product representation of MAP
   decoder

   Writing theorem relating the final result of the message passing algorithm
   to a sum of products

   Writing theorem relating the individual messages in the message passing
   algorithm to sums of products in the relevant subtree

   Needed to write code relating to trees in order to express this
   
   Fixed message passing algorithm to ensure that any messages outside the
   relevant domain are ignored

   Rewrote message passing algorithm in order to be less computational and
   more mathematical, in order to simplify the proof process.

   Added more definitions regarding trees. To show termination, I need to be
   able to show that the trees are shrinking, and thus I need to be able to
   express the diameter of the trees.

   My subtrees are expressed in terms of paths in the tree. To work with paths,
   I needed to show that a path is unique, and that a path exists between any
   two points.
   1. To prove this, I needed to prove that the transitive closure of adjacency
      is equivalent to the existance of a path between the given two points
   2. For which I needed to prove that the existance of a path is transitive
   3. For which I had to prove that if there is a walk between two points, then
      there is a path between them.

   Many helpful subtheorems proved throughout this process
*)

(* In sp_message, I add an if statement which isn't necessary, but it won't
   recognise termination without the information given by the if statement.
   Is it possible to avoid doing that? *)

(* Is there pre-existing code for trees? Induction on trees? Doesn't have to
   be connected to fsgraph, but it would be more convenient if it was *)

(* I'm not entirely confident in using inductive definitions. I think they
   might be useful in the message passing algorithm. *)

(* Induction in the message passing algorithm is kinda interesting. In a
   typical induction over a tree, we would do induction starting at the leaves
   of the tree, and go up to the top of the tree. In message passing induction,
   we essentially induct over all possible subtrees in the tree at once. No
   individual node is considered the root. So not only do we send messages up
   to any given "root", we also send messages down the tree. *)

(* I have defined sp_calculate_messages0 and proven that it always terminates.
   Can I induct on the recursive calls of this function? Some property holds on
   termination, therefore the property holds 1 call before termination,
   therefore the property holds 2 calls before termination, etc. I think I
   remember there being something along the lines of inductive definitions? *)

(* matchingScript is reaching the stack limit for gvs. Perhaps it could be
   made faster very easily by reducing the stack limit for that file or the
   slow proofs? How would one do that? *)

(* How do I use multiset comprehensions? The documentation says that multisets
   are represented by α -> num instead of α -> bool, where the num defines the
   multiplicity. In the multiset comprehension {_ || _ || _}, will it
   automatically take care of multiplicity for me if I use a function to bool
   in the last part? *)

(* Not sure if I should be lifting factor graphs to an abstract type. See message passing script *)

(* --- ALREADY DISCUSSED --- *)

(* Want to apply the assumption as irule:

    ∀x. b1 x ⇔ b2 x ⇒ ((∀x. b1 x) ⇔ ∀x. b2 x)
   ------------------------------------
        (∀x'. x' ∈ FDOM x ⇔ x' ∈ inputs) ⇔
        ∀x'.
          x' ∈ FDOM x ⇔
          (x' = INR (CARD (nodes fg.underlying_graph)) ∨
           x' ∈ nodes fg.underlying_graph) ∧
          x' ≠ INR (CARD (nodes fg.underlying_graph)) ∧
          (x' = INR (CARD (nodes fg.underlying_graph)) ∨
           x' ∈ nodes fg.underlying_graph) ∧
          ∃i. (∀x. x = x' ∨ x = INR (CARD (nodes fg.underlying_graph)) ⇔
                   x = i ∨ x = INR (CARD (nodes fg.underlying_graph))) ∧
              i ∈ inputs
 *)

(* Textbook recomendations for automated proof, learning about how best to
   theorem prove, *)

(* Is there something which applies a function f : α -> α repeatedly n times,
   within the world of HOL? *)

(* Review fg_add_variable_node0_respects *)

(* Review wffactor_graph, in particular the third requirement *)

(* Why use finite map rather than function? *)

(* Changed from function being defined as a tuple of the label orders and the
   function itself to assuming that the inputs are provided in order of
   labels (smallest to largest) *)

(* Arbitrary length words: words in factor graph implementation, need to be able
   to have different lengths of bitstrings. *)

(* Unclear: what variable type in factor graph? *)

(* Unclear how to interface MAP decoder with factor graphs *)

(* How do I easily apply a function to both sides of an equation. e.g. I have
   the assumption ls1 = ls2 and I want to prove LENGTH ls1 = LENGTH ls2 *)

(* Would be cool to be able to start with a left hand side, and apply rules
   until we reach a right hand side, and then add this as an assumption *)

(* -------------------------------------------------------------------------- *)
(* ALREADY DISCUSSED:                                                         *)
(* -------------------------------------------------------------------------- *)

(*In cond_prob_received_string_given_sent

  (* Not sure why this doesn't work by itself *)
  >> ‘r * r' / r = r'’ by gvs[] >> pop_assum (fn th => PURE_REWRITE_TAC[th])
 *)

(* It is not obvious how to search for terms like {bs | LENGTH bs = n ∧ cs ≼ enc bs} *)

(* Notice how slow definitions are. for example, in map_decoderScript *)

(* Does HOL have a profiling tool? *)

(* I enjoy learning and teaching more than I do research *)

(* -------------------------------------------------------------------------- *)
(* ALREADY DISCUSSED:                                                         *)
(* -------------------------------------------------------------------------- *)

(* Could build upon existing Kolmogorov complexity stuff *)

(* New header syntax for lib files? *)

(* It is intuitively obvious that if we have

cond_prob (received (SNOC d ds)) (sent (SNOC c cs)), this is equivalent to 
cond_prob (received d) (sent c) * cond_prob (received ds) (sent cs).

However, formally this is not easy to prove. Would it be novel to develop methods for proving this according to intution? Where variables that "do not affect each other" can be seen easily to be independent? ≤== Interesting *)


(* cond_prob_ecc_bsc_prob_space is a tricky use case for converting an extreal
   term into a real term

   Before:
    1 / 2 pow n * ∑ (sym_noise_mass_func p ∘ SND) (S1 ∩ S2) /
        (1 / 2 pow n * ∑ (sym_noise_mass_func p ∘ SND) S2) =
        ARB

   After:
        Normal (1 / 2 pow n) * ∑ (sym_noise_mass_func p ∘ SND) (S1 ∩ S2) /
        (Normal (1 / 2 pow n) * ∑ (sym_noise_mass_func p ∘ SND) S2) =
        ARB
 *)

(* How do I add bitstringTheory to probheap *)

(* If I worked on polarity search, is there potential for novelty in that direction?  Too much human interaction requied. May need ethics approval for human experinebts*)

(* How should I calculate the conditional probability for the event I'm
 working with? *)

(* What would I do if I did an internship *)

(* Shandong tutoring *)

(* EXTREAL_PROD_IMAGE_THM <- why did I write this here *)

(* -------------------------------------------------------------------------- *)
(* ALREADY DISCUSSED:                                                         *)
(* -------------------------------------------------------------------------- *)

(* How come the following works? Isn't PULL_FORALL Higher order logic? SIMP_RULE [PULL_FORALL] PROD_IMAGE_INSERT *)

(* Does higher order logic work in the theorem search? I tried a 1 = a 2 and it came up with a bunch of really weird results *)

(* proof might be too unweildy and messy at where, in map_decoder_convolutional_codeScript, it says:
   "Subsume e3, and introduce a factor to handle the case in which e3
         is being taken with regards to an invalid stat"
 *)

(* What's the best way to add an existing theorem to the stateful simpset *)

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
