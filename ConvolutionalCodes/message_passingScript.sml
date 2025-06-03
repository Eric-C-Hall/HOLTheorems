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

val _ = new_theory "message_passing";

val _ = hide "S";

(* -------------------------------------------------------------------------- *)
(* This is largely based on "Modern Coding Theory" by Tom Richardson and      *)
(* Rüdiger Urbanke.                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Message passing algorithm:                                                 *)
(*                                                                            *)
(* Messages are represented as follows:                                       *)
(* message_map : (unit + num) # (unit + num) |-> extreal # extreal            *)
(*                                                                            *)
(* This represents a function on binary values, where the first element       *)
(* represents the output when provided with the binary input true, and the    *)
(* second element represents the output when provided with the binary input   *)
(* false.                                                                     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* The domain on which messages are sent. That is, all possible node pairs    *)
(* where one node pair is sending a message and one node is receiving the     *)
(* message.                                                                   *)
(*                                                                            *)
(* This overload is useful for my purposes, but it may overlap with the more  *)
(* general concept of "the set of all pairs of adjacent nodes" in a scenario  *)
(* where we aren't working with the message passing algorithm, so I hide it   *)
(* before exporting the theory.                                               *)
(* -------------------------------------------------------------------------- *)
Overload message_domain = “λfg. {(n,m) | {m;n} ∈ fsgedges fg.underlying_graph}”;

(* -------------------------------------------------------------------------- *)
(* The domain of possible messages is finite                                  *)
(* -------------------------------------------------------------------------- *)
Theorem finite_message_domain[simp]:
  ∀fg.
    FINITE (message_domain fg)
Proof
  rw[]
  >> qmatch_goalsub_abbrev_tac ‘_ ∈ E’
  >> sg ‘FINITE E’ >- gvs[FINITE_fsgedges, Abbr ‘E’]
  >> sg ‘∀e. e ∈ E ⇒ (∃a b. e={a;b} ∧ a ≠ b)’
  >- (unabbrev_all_tac >> metis_tac[alledges_valid])
  >> last_x_assum kall_tac
  >> Induct_on ‘E’
  >> rw[]
  >> qmatch_goalsub_abbrev_tac ‘FINITE S’
  >> sg ‘S = {(n,m) | {m;n} = e} ∪ {(n,m) | {m;n} ∈ E}’
  >- (NTAC 4 (last_x_assum kall_tac) >> unabbrev_all_tac >> ASM_SET_TAC[])
  >> qpat_x_assum ‘Abbrev _’ kall_tac
  >> gvs[]
  >> pop_assum $ qspec_then ‘e’ assume_tac
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac ‘FINITE S’
  >> sg ‘S = {(a,b); (b,a)}’
  >- (unabbrev_all_tac >> ASM_SET_TAC[])
  >> qpat_x_assum ‘Abbrev _’ kall_tac
  >> gvs[]
(* Old proof for old definition
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
  >> gvs[FINITE_PRODUCT]*)
QED

(* -------------------------------------------------------------------------- *)
(* Partially applies a function to all variables other than a specified one,  *)
(* using a provided set of values                                             *)
(*                                                                            *)
(* Undefined behaviour if the specified variable is not in the input          *)
(* variables to the function                                                  *)
(*                                                                            *)
(* f: the function which is being partially applied                           *)
(* vs: the variables that are input to the function                           *)
(* dst: the variable which is not being set to a value                        *)
(* bs: the values that each of the remaining variables are set to             *)
(*                                                                            *)
(* Output: The new function after having partially applied all variables      *)
(*         other than dst in f, represented as a binary tuple, where the      *)
(*         first element represents the output of the function when dst is    *)
(*         true, and the second element represents the output when dst is     *)
(*         false.                                                             *)
(* -------------------------------------------------------------------------- *)
Definition sp_partially_apply_function_def:
  sp_partially_apply_function (vs, f) dst bs =
  let
    dst_index = INDEX_OF dst vs;
    (bs1, bs2) = (TAKE (THE dst_index) bs, DROP (THE dst_index) bs);
  in
    (f (bs1 ⧺ [T] ⧺ bs2), f (bs1 ⧺ [F] ⧺ bs2))
End

(* -------------------------------------------------------------------------- *)
(* Sum-product message calculation:                                           *)
(*                                                                            *)
(* Attempts to calculate the value of a single message on the factor graph    *)
(* using sum-product message passing.                                         *)
(*                                                                            *)
(* Calculates values for both function and variable nodes, and for both leaf  *)
(* and non-leaf nodes (outgoing messages from leaf nodes have                 *)
(* incoming_msg_edges = {}, so this function always returns a value for them) *)
(*                                                                            *)
(* fg: factor graph                                                           *)
(* org: origin node for message                                               *)
(* dst: destination node for message                                          *)
(* msgs: all previous messages that have been calculated                      *)
(*                                                                            *)
(* Output:                                                                    *)
(* - NONE     | if we haven't received incoming messages from all other nodes *)
(*              and thus we cannot calculate the message                      *)
(* - SOME msg | otherwise                                                     *)
(* -------------------------------------------------------------------------- *)
Definition sp_calculate_message_def:
  sp_calculate_message fg org dst msgs =
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
        (* Take the sum over all possible combinations of incoming edge
            values of the kernal multiplied by the incoming messages.
            Note that this works even in the case of a leaf node, as partially
            applying all other variables will partially apply nothing. *)
        SOME (iterate
              (λ(m1,m2) (n1,n2). (m1 + n1, m2 + n2))
              ({bs | LENGTH bs = LENGTH (FST (fg.function_map ' org)) - 1})
              (sp_partially_apply_function (fg.function_map ' org) dst)
             )
      else
        (* Multiply each message together pointwise.
           If there are no messages, returns (1, 1) *)
        SOME (ITSET
              (λmsg_edge (n1,n2).
                 let
                   (m1, m2) = msgs ' msg_edge
                 in
                   (m1 * n1 : extreal, m2 * n2 : extreal)
              )
              incoming_msg_edges
              (1, 1)
             )
End

(* Theorem for showing equivalence of finite maps: fmap_EQ_THM.
   We also have fmap_EXT, which I think is better. *)

(* -------------------------------------------------------------------------- *)
(* Using the sum-product message-passing algorithm, calculate all messages    *)
(* that can be calculated using the currently available messages (including   *)
(* those from leaf nodes)                                                     *)
(*                                                                            *)
(* fg: the factor graph                                                       *)
(* msgs: the map containing all messages that have been calculated so far     *)
(*                                                                            *)
(* Output: the map containing all messages that can be directly calculated    *)
(*         from the messages that have been calculated so far.                *)
(* -------------------------------------------------------------------------- *)
Definition sp_calculate_messages_step_def:
  sp_calculate_messages_step fg msgs =
  let
    calculated_messages =
    FUN_FMAP (λ(org, dst). sp_calculate_message fg org dst msgs)
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
  ∀f r.
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

Theorem sp_calculate_messages_step_in_message_domain[simp]:
  ∀fg msg.
    FDOM (sp_calculate_messages_step fg msg) ⊆ message_domain fg
Proof
  rw[sp_calculate_messages_step_def]
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

Theorem drestrict_sp_calculate_messages_step_drestrict[simp]:
  ∀fg msgs.
    DRESTRICT (sp_calculate_messages_step fg msgs) (message_domain fg) =
    sp_calculate_messages_step fg msgs
Proof
  metis_tac[FDOM_SUBSET_DRESTRICT, sp_calculate_messages_step_in_message_domain,
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
  ∀x y.
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
  ∀A B.
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
  ∀fm1 fm2.
    FUNION fm1 fm2 ≠ fm1 ⇒
    ∃k. k ∉ FDOM fm1 ∧ k ∈ FDOM fm2
Proof
  rpt gen_tac
  >> simp[fmap_EXT, FUNION_DEF, AllCaseEqs()] >>
  simp[SF CONJ_ss] >> strip_tac >>
  ‘FDOM fm1 ∪ FDOM fm2 ≠ FDOM fm1’
    by (strip_tac >> gvs[]>> pop_assum mp_tac>>
        ASM_SET_TAC[]) >>
  ASM_SET_TAC[]
QED

Theorem fdom_sp_calculate_messages_step_in_message_domain:
  ∀msgs fg step_msg.
    step_msg ∈ FDOM (sp_calculate_messages_step fg msgs) ⇒
    step_msg ∈ message_domain fg
Proof
  rw[]
  >> qspecl_then [‘fg’, ‘msgs’] assume_tac
                 sp_calculate_messages_step_in_message_domain
  >> ASM_SET_TAC[]
QED

(* -------------------------------------------------------------------------- *)
(* Uses the sum-product algorithm to calculate all messages in the factor     *)
(* graph, starting from a set of messages that have already been calculated.  *)
(*                                                                            *)
(* fg: the factor graph                                                       *)
(* msgs: the messages that have already been calculated. If no messages have  *)
(*       been calculated yet, then set this to the empty map.                 *)
(*                                                                            *)
(* Output: all messages on the factor graph as calculated by the sum-product  *)
(*         algorithm                                                          *)
(*                                                                            *)
(* We usually expect that msgs is of the form                                 *)
(* FUNPOW (sp_calculate_messages_step fg) n FEMPTY, for some n.               *)
(*                                                                            *)
(* A strictly weaker assumption that is also expected is that msgs is a       *)
(* subset of message_domain fg                                                *)
(*                                                                            *)
(* Note: I tried removing the FUNION, but this interferes with termination.   *)
(* Consider a factor graph consisting of a single loop of nodes, where a      *)
(* single message is sent from one of the nodes. This message will loop       *)
(* around the nodes forever, never terminating.                               *)
(*                                                                            *)
(* Termination is also harder to prove if we only terminate when the messages *)
(* themselves dont change, rather than when the domain of the messages        *)
(* doesn't change, because we may have a change in messages propogating       *)
(* around a circle in a never-ending cycle. In a previous iteration of this   *)
(* definition, I did manage to prove termination when defining termination in *)
(* this way, but that may be due to other differences in the definition       *)
(* (although to be honest I'm not sure what that might have been)             *)
(* -------------------------------------------------------------------------- *)
Definition sp_calculate_messages_def:
  sp_calculate_messages fg msgs =
  let
    new_msgs = sp_calculate_messages_step fg msgs ⊌ msgs
  in
    if FDOM new_msgs = FDOM msgs
    then
      msgs
    else
      sp_calculate_messages fg (new_msgs)
Termination
  (* We expect that at least one message will be added in each step. The number
     of possible messages is limited above by the (finite) number of pairs of
     nodes in the (finite) factor graph. Thus, this process will eventually end
     and we will terminate. We ignore any messages that happen to be in msgs
     but are not in message_domain fg.
.
     Thus, we expect CARD (message_domain fg) - CARD (FDOM msgs) to decrease
     by at least 1 in each step. We use this as the basis for our termination
     measure.
.    
     In practice, adding 1 to this value simplifies the proof process.
.
     Similarly, we have to take care of the special case in which the set of
     msgs is not 
.     
     We use prim_recTheory.measure to turn our termination measure into a
     well-founded relation.
   *)
  WF_REL_TAC ‘measure (λ(fg, msgs).
                         (CARD (message_domain fg) + 1) -
                         CARD (FDOM (DRESTRICT msgs (message_domain fg)))
                      )’
  >> REVERSE $ rw[]
  >- (gvs[GSYM SUB_LESS_0]
      >> gvs[GSYM LE_LT1]
      >> gvs[CARD_FDOM_DRESTRICT_LEQ]
     )
  >> qmatch_goalsub_abbrev_tac ‘const < new_num_messages + (const - old_num_messages)’
  >> sg ‘old_num_messages ≤ const’
  >- (unabbrev_all_tac
      >> gvs[FDOM_DRESTRICT]
      >> metis_tac[CARD_INTER_LESS_EQ, LE, ADD1, INTER_COMM,
                   finite_message_domain]
     )
  >> gvs[]
  >> qsuff_tac ‘old_num_messages < new_num_messages’
  >- gvs[]
  >> pop_assum kall_tac
  >> unabbrev_all_tac
  >> irule CARD_PSUBSET
  >> gvs[]
  >> gvs[PSUBSET_MEMBER]
  >> gvs[DRESTRICTED_FUNION_ALT]
  >> gvs[EXTENSION]
  >> Cases_on ‘x ∈ FDOM msgs’ >> gvs[]
  >> qexists ‘x’
  >> gvs[FDOM_DRESTRICT]
End

(* -------------------------------------------------------------------------- *)
(* This overload is useful for my purposes, but it may overlap with the more  *)
(* general concept of "the set of all pairs of adjacent nodes" in a scenario  *)
(* where we aren't working with the message passing algorithm, so I hide it   *)
(* before exporting the theory.                                               *)
(* -------------------------------------------------------------------------- *)
val _ = hide "message_domain"

val _ = export_theory();
