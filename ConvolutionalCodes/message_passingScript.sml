Theory message_passing

Ancestors arithmetic bool probability fsgraph genericGraph pred_set finite_map list transc prim_rec integer factor_graph partite_ea hyperbolic_functions lifting transfer

Libs donotexpandLib dep_rewrite ConseqConv simpLib liftLib transferLib;

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
(* Sum-product message calculation:                                           *)
(*                                                                            *)
(* Attempts to calculate the value of a single message on the factor graph    *)
(* using sum-product message passing.                                         *)
(*                                                                            *)
(* A message has type (bool list |-> α). Each message corresponds to          *)
(* precisely one free variable: it takes as input the value of that free      *)
(* variable and outputs the value of the message in the case that the free    *)
(* variable takes that value.                                                 *)
(*                                                                            *)
(* fg: factor graph                                                           *)
(* org: origin node for message                                               *)
(* dst: destination node for message                                          *)
(* msgs: all previous messages that have been calculated. A finite map from   *)
(*       message_domain to message option                                     *)
(*                                                                            *)
(* Returns a message option                                                   *)
(* -------------------------------------------------------------------------- *)
Definition sp_calculate_single_message0_def:
  sp_calculate_single_message0 fg org dst msgs =
  let
    adjacent_nodes_not_dst = {n | n ∈ adjacent_nodes fg org ∧
                                  n ≠ dst};
    incoming_msg_edges = {(n, org) | n | n ∈ adjacent_nodes_not_dst };
  in
    if ¬(incoming_msg_edges ⊆ FDOM msgs) then
      NONE (* Incoming messages aren't available yet *)
    else
      if org ∈ fg.function_nodes
      then
        SOME (FUN_FMAP
              (
              λdst_val.
                ∑ (λval_map.
                     (fg.function_map ' org) ' val_map *
                     ∏ (λcur_msg_edge.
                          msgs ' cur_msg_edge '
                               (val_map ' (FST cur_msg_edge))
                       ) incoming_msg_edges
                  )
                  {val_map | FDOM val_map = adjacent_nodes fg org ∧
                             (∀n. n ∈ adjacent_nodes fg org ⇒
                                  LENGTH (val_map ' n) =
                                  fg.variable_length_map ' n) ∧
                             val_map ' dst = dst_val
                         }                         
              ) (length_n_codes (fg.variable_length_map ' dst))
             )
      else
        SOME (FUN_FMAP
              (λorg_val.
                 ∏ (λcur_msg_edge. msgs ' cur_msg_edge ' org_val : extreal)
                   incoming_msg_edges)
              (length_n_codes (fg.variable_length_map ' org))
             )
End

Theorem sp_calculate_single_message0_respects:
  (fgequiv ===> (=) ===> (=) ===> (=) ===> (=))
  sp_calculate_single_message0 sp_calculate_single_message0
Proof
  gvs[FUN_REL_def]
  >> gvs[fgequiv_def]
QED

val _ = liftdef sp_calculate_single_message0_respects "sp_calculate_single_message";

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
Definition sp_calculate_messages_step0_def:
  sp_calculate_messages_step0 fg msgs =
  let
    calculated_messages =
    FUN_FMAP (λ(org, dst). sp_calculate_single_message0 fg org dst msgs)
             (message_domain fg);
    restricted_messages = RRESTRICT calculated_messages {SOME x | T};
  in
    (* Change from option type into the underlying message type *)
    FMAP_MAP2 (THE ∘ SND) restricted_messages
End

Theorem sp_calculate_messages_step0_respects:
  (fgequiv ===> (=) ===> (=))
  sp_calculate_messages_step0 sp_calculate_messages_step0 
Proof
  gvs[FUN_REL_def]
  >> gvs[fgequiv_def]
QED

val _ = liftdef sp_calculate_messages_step0_respects "sp_calculate_messages_step";

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
    FDOM (sp_calculate_messages_step0 fg msg) ⊆ message_domain fg
Proof
  rw[sp_calculate_messages_step0_def]
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

Theorem drestrict_sp_calculate_messages_step0_drestrict[simp]:
  ∀fg msgs.
    DRESTRICT (sp_calculate_messages_step0 fg msgs) (message_domain fg) =
    sp_calculate_messages_step0 fg msgs
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
    step_msg ∈ FDOM (sp_calculate_messages_step0 fg msgs) ⇒
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
Definition sp_calculate_messages0_def:
  sp_calculate_messages0 fg msgs =
  let
    new_msgs = sp_calculate_messages_step0 fg msgs ⊌ msgs
  in
    if FDOM new_msgs = FDOM msgs
    then
      msgs
    else
      sp_calculate_messages0 fg (new_msgs)
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

Theorem sp_calculate_messages0_respects:
  (fgequiv ===> (=) ===> (=))
  sp_calculate_messages0 sp_calculate_messages0
Proof
  gvs[FUN_REL_def]
  >> gvs[fgequiv_def]
QED

val _ = liftdef sp_calculate_messages0_respects "sp_calculate_messages";

(* -------------------------------------------------------------------------- *)
(* Runs the message passing algorithm on a factor graph and returns a         *)
(* finite map which takes a variable node and returns the final result of the *)
(* message passing algorithm at that node.                                    *)
(*                                                                            *)
(* fg: The factor graph to apply the message passing algorithm to             *)
(*                                                                            *)
(* The output at a given node has type (bool list |-> α), just like a         *)
(* message.                                                                   *)
(* -------------------------------------------------------------------------- *)
Definition sp_run_message_passing0_def:
  sp_run_message_passing0 fg =
  let
    msgs = sp_calculate_messages0 fg FEMPTY
  in
    FUN_FMAP
    (λcur_var_node.
       FUN_FMAP
       (λcur_var_node_val.
          ∏ (λcur_msg_edge. msgs ' cur_msg_edge ' cur_var_node_val : extreal)
            {(adj_node, cur_var_node)
          | adj_node ∈ adjacent_nodes fg cur_var_node}
       ) (length_n_codes (fg.variable_length_map ' cur_var_node))
    )
    (var_nodes fg)
End

Theorem sp_run_message_passing0_respects:
  (fgequiv ===> (=))
  sp_run_message_passing0 sp_run_message_passing0
Proof
  gvs[FUN_REL_def]
  >> gvs[fgequiv_def]
QED

val _ = liftdef sp_run_message_passing0_respects "sp_run_message_passing";

(* -------------------------------------------------------------------------- *)
(* This overload is useful for my purposes, but it may overlap with the more  *)
(* general concept of "the set of all pairs of adjacent nodes" in a scenario  *)
(* where we aren't working with the message passing algorithm, so I hide it   *)
(* before exporting the theory.                                               *)
(* -------------------------------------------------------------------------- *)
val _ = hide "message_domain"
