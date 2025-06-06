open HolKernel Parse boolLib bossLib;

open arithmeticTheory;
open boolTheory;
open probabilityTheory;
(*open listTheory;*)
open fsgraphTheory;
open genericGraphTheory;
open pred_setTheory;
open finite_mapTheory;
open listTheory;
open transcTheory;
open prim_recTheory;
open integerTheory;

open factor_graphTheory;

open partite_eaTheory;
open hyperbolic_functionsTheory;

open donotexpandLib;

(* I find DEP_PURE_ONCE_REWRITE_TAC, etc to be very helpful *)
open dep_rewrite;

open ConseqConv;
open simpLib;

(* Lifting and transfer libraries *)
open liftLib liftingTheory transferLib transferTheory;

val _ = new_theory "message_passing_log_likelihood";

val _ = hide "S";

(* -------------------------------------------------------------------------- *)
(* This is largely based on "Modern Coding Theory" by Tom Richardson and      *)
(* Rüdiger Urbanke.                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* TODO: this contains many duplicate functions that are also contained in    *)
(* message_passingScript                                                      *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Message passing algorithm:                                                 *)
(*                                                                            *)
(* Messages are represented as follows:                                       *)
(* message_map : (unit + num) # (unit + num) |-> extreal                      *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Whether or not a particular node is a leaf                                 *)
(* -------------------------------------------------------------------------- *)
Overload is_leaf = “λg n. degree g n = 1”;

(* -------------------------------------------------------------------------- *)
(* The set of all leaves of a graph                                           *)
(* -------------------------------------------------------------------------- *)
Overload leaves = “λg. {n | n ∈ nodes g ∧ is_leaf g n}”;

(* -------------------------------------------------------------------------- *)
(* Calculate messages to be initially sent from the variable leaf nodes of    *)
(* the factor graph                                                           *)
(*                                                                            *)
(* When sending messages in the form of the log likelihood ratio between      *)
(* f(1) and f(-1), the message sent from each variable leaf node needs to be  *)
(* 0, which differs from what needs to be sent when the messages take the     *)
(* form of a function, where the message that is sent needs to be the         *)
(* constant function 1.                                                       *)
(* -------------------------------------------------------------------------- *)
Definition calculate_variable_leaf_messages_def:
  calculate_variable_leaf_messages fg =
  FUN_FMAP (λ_. Normal 0)
           {(l, k) | l ∈ leaves fg.underlying_graph ∧
                     l ∉ fg.function_nodes ∧
                     adjacent fg.underlying_graph l k}          
End

(* -------------------------------------------------------------------------- *)
(* Calculate messages to be initially sent from the function leaf nodes of    *)
(* the factor graph.                                                          *)
(*                                                                            *)
(* If messages were being sent in the form of a function, the function that   *)
(* would need to be sent as a message would be the function contained in the  *)
(* function node.                                                             *)
(*                                                                            *)
(* Thus, in terms of the log likelihood ratio, this is equal to               *)
(* ln(f(T) / f(F))                                                            *)
(* -------------------------------------------------------------------------- *)
Definition calculate_function_leaf_messages_def:
  calculate_function_leaf_messages fg =
  FUN_FMAP (λ(l, k).
              let
                (f_args, f_func) = fg.function_map ' l
              in
                ln (f_func [T] / f_func [F])
           )
           {(l, k) | l ∈ leaves fg.underlying_graph ∧
                     l ∈ fg.function_nodes ∧
                     adjacent fg.underlying_graph l k
           }
End

(* -------------------------------------------------------------------------- *)
(* Combine function leaf messages and variable leaf messages                  *)
(* -------------------------------------------------------------------------- *)
Definition calculate_leaf_messages_def:
  calculate_leaf_messages fg =
  calculate_function_leaf_messages fg ⊌ calculate_variable_leaf_messages fg
End

(* -------------------------------------------------------------------------- *)
(* The domain on which messages are sent. That is, all possible node pairs    *)
(* where one node pair is sending a message and one node is receiving the     *)
(* message.                                                                   *)
(*                                                                            *)
(* This overload is useful for my purposes, but it may overlap with the more  *)
(* general concept of "the set of all pairs of adjacent nodes" in a scenario  *)
(* where we aren't working with the message passing algorithm, so I hide it   *)
(* before exporting the theory.                                               *)
(*                                                                            *)
(* TODO: update this in the same way as it has been updated in                *)
(* message_passingScript                                                      *)
(* -------------------------------------------------------------------------- *)
Overload message_domain = “λfg. {(n,m) | n ∈ nodes fg.underlying_graph ∧
                                         m ∈ nodes fg.underlying_graph ∧
                                         adjacent fg.underlying_graph n m
                          }”;

(* -------------------------------------------------------------------------- *)
(* The domain of possible messages is finite                                  *)
(* -------------------------------------------------------------------------- *)
Theorem finite_message_domain[simp]:
  ∀fg.
    FINITE (message_domain fg)
Proof
  rw[]
  >> qsuff_tac ‘FINITE {(n, m) | n ∈ nodes fg.underlying_graph ∧
                                 m ∈ nodes fg.underlying_graph}’
  >- (rw[]
      >> irule SUBSET_FINITE
      >> qmatch_asmsub_abbrev_tac ‘FINITE S’
      >> qexists ‘S’
      >> gvs[]
      >> unabbrev_all_tac
      >> ASM_SET_TAC[]
     )
  >> gvs[FINITE_PRODUCT]
QED

(* -------------------------------------------------------------------------- *)
(* Calculate the message for a particular origin and destination, if possible *)
(*                                                                            *)
(* fg: factor graph                                                           *)
(* org: origin node for message                                               *)
(* dsf: destination node for message                                          *)
(* msgs: all previous messages that have been calculated                      *)
(*                                                                            *)
(* Output:                                                                    *)
(* - NONE     | if we haven't received incoming messages from all other nodes *)
(*              and thus we cannot calculate the message                      *)
(* - SOME msg | otherwise                                                     *)
(* -------------------------------------------------------------------------- *)
Definition calculate_message_def:
  calculate_message fg org dst msgs =
  let
    incoming_msg_edges = {(n, org) | n | n ∈ nodes fg.underlying_graph ∧
                                         adjacent fg.underlying_graph n org ∧
                                         n ≠ dst };
  in
    if ¬(incoming_msg_edges ⊆ FDOM msgs) then
      NONE
    else
      if org ∈ fg.function_nodes
      then
        SOME (2 * extarctanh (∏
                              (λmsg_edge. exttanh ((msgs ' msg_edge) / 2))
                              incoming_msg_edges
                             )
             )
      else
        (* sum of all input messages *)
        SOME (∑ ($' msgs) incoming_msg_edges)
End

(* Theorem for showing equivalence of finite maps: fmap_EQ_THM *)

(* -------------------------------------------------------------------------- *)
(* A map consisting of all messages that can be calculated based on the       *)
(* current messages (this may not include some of the provided messages if    *)
(* they cannot be calculated based on other provided messages)                *)
(*                                                                            *)
(* We expect FDOM msgs ⊆ message_domain fg                                   *)
(* -------------------------------------------------------------------------- *)
Definition calculate_messages_step_def:
  calculate_messages_step fg msgs =
  let
    calculated_messages =
    FUN_FMAP (λ(org, dst). calculate_message fg org dst msgs)
             (message_domain fg);
    restricted_messages = RRESTRICT calculated_messages {SOME x | T};
  in
    (* Change from option type into the underlying message type *)
    FMAP_MAP2 (THE ∘ SND) restricted_messages
End

(* -------------------------------------------------------------------------- *)
(* Restricting a domain gives you a domain which is a subset of the initial   *)
(* domain                                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem FDOM_RRESTRICT_SUBSET:
  FDOM (RRESTRICT f r) ⊆ FDOM f
Proof
  gvs[RRESTRICT_DEF]
  >> ASM_SET_TAC[]
QED

(* -------------------------------------------------------------------------- *)
(* If the domain of a finite map is a subset of S, then the domain of its     *)
(* restriction is also a subset of S                                          *)
(* -------------------------------------------------------------------------- *)
Theorem FDOM_RRESTRICT_SUBSET_IMPLIES:
  ∀f r S.
    FDOM f ⊆ S ⇒
    FDOM (RRESTRICT f r) ⊆ S
Proof
  rw[]
  >> irule SUBSET_TRANS
  >> metis_tac[FDOM_RRESTRICT_SUBSET]
QED

Theorem factor_graphs_FDOM_FMAP[simp] = FDOM_FMAP;

Theorem calculate_messages_step_in_message_domain:
  ∀fg msg.
    FDOM msg ⊆ message_domain fg ⇒ 
    FDOM (calculate_messages_step fg msg) ⊆ message_domain fg
Proof
  rw[calculate_messages_step_def]
  >> irule FDOM_RRESTRICT_SUBSET_IMPLIES
  >> gvs[RRESTRICT_DEF]
QED

(* -------------------------------------------------------------------------- *)
(* If our finite map already has a domain within the domain we are            *)
(* restricting to, then restricting does nothing.                             *)
(* -------------------------------------------------------------------------- *)
Theorem FDOM_SUBSET_DRESTRICT:
  ∀f r.
    FDOM f ⊆ r ⇒
    DRESTRICT f r = f
Proof
  rw[]
  >> rw[GSYM fmap_EQ_THM]
  >- (rw[DRESTRICT_DEF]
      >> ASM_SET_TAC[]
     )
  >> gvs[DRESTRICT_DEF]
QED

Theorem drestrict_calculate_messages_step_drestrict[simp]:
  ∀fg msgs.
    DRESTRICT (calculate_messages_step fg (DRESTRICT msgs (message_domain fg)))
              (message_domain fg) =
    calculate_messages_step fg (DRESTRICT msgs (message_domain fg))
Proof
  metis_tac[FDOM_SUBSET_DRESTRICT, calculate_messages_step_in_message_domain,
            FDOM_DRESTRICT, INTER_SUBSET]
QED

(* -------------------------------------------------------------------------- *)
(* Restricting the domain causes the cardinality of the domain to be bounded  *)
(* above by the cardinality of the set you restricted the domain to.          *)
(* -------------------------------------------------------------------------- *)
Theorem CARD_FDOM_DRESTRICT_LEQ:
  ∀f r.
    FINITE r ⇒
    CARD (FDOM (DRESTRICT f r)) ≤ CARD r
Proof
  rw[]
  >> gvs[FDOM_DRESTRICT]
  >> metis_tac[CARD_INTER_LESS_EQ, INTER_COMM]
QED

(* -------------------------------------------------------------------------- *)
(* A simpler version of DRESTRICTED_FUNION that is more symmetrical           *)
(* -------------------------------------------------------------------------- *)
Theorem DRESTRICTED_FUNION_ALT:
  ∀f1 f2 s.
    DRESTRICT (f1 ⊌ f2) s =
    DRESTRICT f1 s ⊌ DRESTRICT f2 s
Proof
  rw[GSYM fmap_EQ_THM]
  >- (gvs[DRESTRICT_DEF]
      >> ASM_SET_TAC[]
     )
  >> gvs[DRESTRICT_DEF]
  >> (gvs[FUNION_DEF]
      >> rw[]
      >> gvs[DRESTRICT_DEF]
     )
QED

(* -------------------------------------------------------------------------- *)
(* An expression of the cardinality of the intersection given in terms of the *)
(* cardinality of one of the sets and the cardinality of the difference.      *)
(*                                                                            *)
(* A rewriting of CARD_DIFF_EQN.                                              *)
(* -------------------------------------------------------------------------- *)
Theorem CARD_INTER_CARD_DIFF:
  ∀s t.
    FINITE s ⇒
    CARD (s ∩ t) = CARD s - CARD (s DIFF t)
Proof
  rw[CARD_DIFF_EQN, SUB_SUB]
QED

(* -------------------------------------------------------------------------- *)
(* The cardinality of a set is nonzero if and only if there is an element of  *)
(* the set (we require our set to be finite so that the cardinality is        *)
(* defined according to the definition we use)                                *)
(* -------------------------------------------------------------------------- *)
Theorem ZERO_LESS_CARD:
  ∀S.
    FINITE S ⇒
    (0 < CARD S ⇔ ∃s. s ∈ S)
Proof
  rw[]
  >> Cases_on ‘S’ >> gvs[]
  >> qexists ‘x’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* The union has no effect if and only if the added set is a subset of the    *)
(* original set                                                               *)
(* -------------------------------------------------------------------------- *)
Theorem UNION_EQ_FIRST:
  ∀s t.
    s ∪ t = s ⇔ t ⊆ s
Proof
  ASM_SET_TAC[]
QED

(* -------------------------------------------------------------------------- *)
(* Calculate all messages that can be calculated based on the messages that   *)
(* have been sent so far.                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem inter_lemma:
  x ∩ (x ∩ y) = x ∩ y
Proof
  SET_TAC[]
QED

(* -------------------------------------------------------------------------- *)
(* Taking the intersection of a set B with a set A will decrease the          *)
(* cardinality if and only if there is an element in the difference of the    *)
(* two sets                                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem card_inter_lemma:
  FINITE B ⇒
  (CARD (A ∩ B) < CARD B ⇔ B DIFF A ≠ ∅)
Proof
  rw[EQ_IMP_THM]
  >- (strip_tac>>
      ‘B ⊆ A’ by ASM_SET_TAC[] >>
      ‘A ∩ B = B’ by ASM_SET_TAC[]>>
      gvs[]) >>
  irule CARD_PSUBSET >> simp[] >>
  simp[PSUBSET_DEF] >> ASM_SET_TAC[]
QED

Theorem FUNION_NEQ_lemma:
  FUNION fm1 fm2 ≠ fm1 ⇒
  ∃k. k ∉ FDOM fm1 ∧ k ∈ FDOM fm2
Proof
  simp[fmap_EXT, FUNION_DEF, AllCaseEqs()] >>
  simp[SF CONJ_ss] >> strip_tac >>
  ‘FDOM fm1 ∪ FDOM fm2 ≠ FDOM fm1’
    by (strip_tac >> gvs[]>> pop_assum mp_tac>>
        ASM_SET_TAC[]) >>
  ASM_SET_TAC[]
QED

Theorem fdom_calculate_messages_step_in_message_domain:
  ∀msgs fg step_msg.
    FDOM msgs ⊆ message_domain fg ⇒
    step_msg ∈ FDOM (calculate_messages_step fg msgs) ⇒
    step_msg ∈ message_domain fg
Proof
  rw[]
  >> qspecl_then [‘fg’, ‘msgs’] assume_tac
                 calculate_messages_step_in_message_domain
  >> gvs[]
  >> gvs[SUBSET_DEF]
QED

Definition calculate_messages_loop_def:
  calculate_messages_loop fg msgs =
  let
    valid_msgs = DRESTRICT msgs (message_domain fg);
    new_msgs = valid_msgs ⊌ (calculate_messages_step fg valid_msgs)
  in
    if new_msgs = valid_msgs
    then
      msgs
    else
      calculate_messages_loop fg (new_msgs)
Termination
  (* At each stage, either a message is added, or we terminate because no
     message was added. Thus, if we count the number of edges without messages,
     this will strictly decrease in each recursive call, proving eventual
     termination.
.
     This is calculated as CARD (message_domain fg) - CARD (FDOM msgs).
     We add 1 to the first CARD in order to ensure that it is strictly greater
     than the second CARD, and not simply greater than or equal to it. This
     simplifies the working.
.     
     We use prim_recTheory.measure to turn this natural number into a
     well-founded relation.
   *)
  WF_REL_TAC ‘measure (λ(fg, msgs).
                         (CARD (message_domain fg)) + 1 -
                         CARD (FDOM (DRESTRICT msgs (message_domain fg)))
             )’
  >> REVERSE $ rw[]
  >- (gvs[GSYM SUB_LESS_0]
      >> gvs[GSYM LE_LT1]
      >> gvs[CARD_FDOM_DRESTRICT_LEQ]
     )
  >> gvs[DRESTRICTED_FUNION_ALT]
  >> qmatch_goalsub_abbrev_tac ‘upper_limit < new_card + (_ - old_card)’
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM LESS_EQ_ADD_SUB]
  >> REVERSE $ Cases_on ‘old_card ≤ upper_limit’ >> gvs[]
  >- (pop_assum mp_tac >> gvs[]
      >> unabbrev_all_tac
      >> metis_tac[CARD_FDOM_DRESTRICT_LEQ, LESS_EQ_SUC_REFL, ADD1, LE_TRANS,
                   finite_message_domain]
     )
  >> PURE_ONCE_REWRITE_TAC[ADD_COMM]
  >> DEP_PURE_ONCE_REWRITE_TAC[LESS_EQ_ADD_SUB]
  >> gvs[GSYM SUB_LESS_0]
  >> qsuff_tac ‘old_card < new_card’ >> gvs[]
  >> unabbrev_all_tac
  >> gvs[CARD_UNION_EQN]
  >> DEP_PURE_ONCE_REWRITE_TAC[LESS_EQ_ADD_SUB]
  >> conj_tac
  >- metis_tac[CARD_INTER_LESS_EQ, INTER_COMM, FDOM_FINITE]
  >> gvs[GSYM SUB_LESS_0]
  >> PURE_ONCE_REWRITE_TAC[INTER_COMM]
  >> DEP_PURE_ONCE_REWRITE_TAC[CARD_INTER_CARD_DIFF]
  >> conj_tac >- gvs[]
  >> qmatch_goalsub_abbrev_tac ‘n - at_least_one’
  >> gvs[Excl "CARD_DIFF"]
  (* Both of these conjuncts follow from the statement that there exists at
     least one message which is in the domain of the new messages but not the
     domain of the old messages *)
  >> sg ‘∃x. x ∈ FDOM (calculate_messages_step
                       fg (DRESTRICT msgs (message_domain fg))) ∧
             x ∉ FDOM (DRESTRICT msgs (message_domain fg))’
  >- (unabbrev_all_tac
      >> gvs[GSYM fmap_EQ_THM]
      >> qmatch_asmsub_abbrev_tac ‘prem ⇒ concl’
      >> Cases_on ‘prem’ >> gvs[]
      (* We have an x which is in the old messages, for which the value it is
         assigned in the new messages is different to the value it is assigned
         in the old messages. *)
      >- gvs[FUNION_DEF]
      (* We have an x which is in the new messages, for which the value it is
         assigned in the new messages is different to the value it is assigned
         in the old messages. *)
      >- (gvs[FUNION_DEF]
          >> rpt $ pop_assum mp_tac >> rw[] >> rpt strip_tac
          (* x is in the new messages, but not in the old messages, and the
             union of the domain of the new messasges with the domain of the
             old messages is equal to the domain of the old messages
              (contradiction) *)
          >> gvs[UNION_EQ_FIRST]
          >> ASM_SET_TAC[]
         )
      >> unabbrev_all_tac
      (* The union of the old messages with the new messages is not equal
         to the old messages, and we want to show that there exists a message
         in the new messages but not the old messages *)
      >> gvs[cj 1 $ GSYM FUNION_DEF, Excl "FDOM_FUNION"]
      >> gvs[EXTENSION, Excl "FDOM_FUNION"]
      >> qmatch_asmsub_abbrev_tac ‘b1 ⇔ b2’
      >> REVERSE $ Cases_on ‘b2’ >> gvs[Excl "FDOM_FUNION"]
      (* x ∈ new ∧ x ∉ old *)
      >- (qexists ‘x’ >> gvs[])
      (* x ∈ old domain but x ∉ new domain*)
      >> gvs[]
     )
  >> conj_tac
  >- (unabbrev_all_tac
      >> gvs[Excl "CARD_DIFF", ZERO_LESS_CARD]
      >> metis_tac[]
     )
  >> unabbrev_all_tac
  >> gvs[ZERO_LESS_CARD]
  >> metis_tac[]
(* -----------------------------------------------------
     Here is an unfinished alternative termination proof.
     ----------------------------------------------------- *)
(*WF_REL_TAC ‘measure (λ(fg, msgs).
                                     (CARD (message_domain fg)) + 1 -
                                     CARD (FDOM (DRESTRICT msgs (message_domain fg)))
                                  )’
    >> reverse $ rpt strip_tac
    >- (gvs[GSYM SUB_LESS_0]
    >> gvs[GSYM LE_LT1]
    >> gvs[CARD_FDOM_DRESTRICT_LEQ]
   )
  >> qmatch_abbrev_tac ‘X + 1n < Y + (X + 1 - Z)’
  >> ‘Z ≤ X + 1’
    by (simp[Abbr‘X’, Abbr‘Z’, FDOM_DRESTRICT] >>
        irule LE_TRANS >> ONCE_REWRITE_TAC[INTER_COMM] >>
        irule_at Any CARD_INTER_LESS_EQ >> simp[])
  >> ‘Z < Y’ suffices_by simp[]
  >> simp[Abbr‘Z’, Abbr‘Y’]
  >> simp[FDOM_DRESTRICT, ONCE_REWRITE_RULE[INTER_COMM] UNION_OVER_INTER]
  >> simp[Once INTER_ASSOC]
  >> simp[CARD_UNION_EQN, AC INTER_COMM INTER_ASSOC, inter_lemma,
          SF numSimps.ARITH_NORM_ss]
  >> qmatch_abbrev_tac ‘CARD (_ ∩ (_ ∩ FDOM XX)) < CARD (_ ∩ FDOM XX)’
  >> simp[GSYM INTER_ASSOC, card_inter_lemma] 
  >> simp[EXTENSION, PULL_EXISTS]
  >> drule FUNION_NEQ_lemma
  >> simp[FDOM_DRESTRICT, PULL_EXISTS]
  >> qx_gen_tac ‘k’ >> Cases_on ‘k ∈ FDOM msgs’
  >> simp[]
  >- (Cases_on ‘k’ >> simp[] >> strip_tac
      >- ((* contradiction as edge isn't in graph *) cheat
         (*unabbrev_all_tac
           >> drule fdom_calculate_messages_step_in_message_domain >> strip_tac*)
         )
      >- (* contradiction as edge isn't in graph *) cheat
      >- (* contradiction as edge isn't in adjacency relation *) cheat) >>
  strip_tac >> Cases_on ‘k’ >> simp[] >>
  (* have witness; need to know that calculate_messages_step only returns
     finite map with keys being edges actually in graph *)
  >> gvs[DRESTRICTED_FUNION_ALT]
  >> qmatch_goalsub_abbrev_tac ‘upper_limit < new_card + (_ - old_card)’
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM LESS_EQ_ADD_SUB]
  >> REVERSE $ Cases_on ‘old_card ≤ upper_limit’ >> gvs[]
  >- (pop_assum mp_tac >> gvs[]
      >> unabbrev_all_tac
      >> metis_tac[CARD_FDOM_DRESTRICT_LEQ, LESS_EQ_SUC_REFL, ADD1, LE_TRANS,
                   finite_message_domain]
     )
  >> PURE_ONCE_REWRITE_TAC[ADD_COMM]
  >> DEP_PURE_ONCE_REWRITE_TAC[LESS_EQ_ADD_SUB]
  >> gvs[GSYM SUB_LESS_0]
  >> qsuff_tac ‘old_card < new_card’ >> gvs[]*)
End

(* -------------------------------------------------------------------------- *)
(* Calculate messages over the factor graph                                   *)
(*                                                                            *)
(* 1. Send a message from each leaf node                                      *)
(* 2. Repeatedly determine what messages we can send, and send them.          *)
(*    When a node has received incoming messages from all but one of its      *)
(*    connected edges, we may send an outgoing message over the remaining     *)
(*    edge.                                                                   *)
(* -------------------------------------------------------------------------- *)
Definition calculate_messages_def:
  calculate_messages fg =
  calculate_messages_loop fg (calculate_leaf_messages fg)
End

(* -------------------------------------------------------------------------- *)
(* This overload is useful for my purposes, but it may overlap with the more  *)
(* general concept of "the set of all pairs of adjacent nodes" in a scenario  *)
(* where we aren't working with the message passing algorithm, so I hide it   *)
(* before exporting the theory.                                               *)
(* -------------------------------------------------------------------------- *)
val _ = hide "message_domain"

val _ = export_theory();
