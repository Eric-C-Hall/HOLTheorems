Theory message_passing

Ancestors arithmetic bool factor_graph finite_map fsgraph fundamental genericGraph hyperbolic_functions integer list  lifting partite_ea probability pred_set prim_rec transc transfer tree

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

Theorem fdom_sp_calculate_messages_step_subset_message_domain[simp]:
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
  metis_tac[FDOM_SUBSET_DRESTRICT, fdom_sp_calculate_messages_step_subset_message_domain,
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
                 fdom_sp_calculate_messages_step_subset_message_domain
  >> ASM_SET_TAC[]
QED

Theorem drestrict_sp_calculate_messages_step0_message_domain[simp]:
  ∀fg msgs.
    DRESTRICT (sp_calculate_messages_step0 fg msgs) (message_domain fg) =
    sp_calculate_messages_step0 fg msgs
Proof
  rpt strip_tac
  >> irule FDOM_SUBSET_DRESTRICT
  >> gvs[fdom_sp_calculate_messages_step_subset_message_domain]
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
    restricted_msgs = DRESTRICT msgs (message_domain fg);
    new_msgs = sp_calculate_messages_step0 fg restricted_msgs ⊌ restricted_msgs;
  in
    if FDOM new_msgs = FDOM msgs
    then
      new_msgs
    else
      sp_calculate_messages0 fg (new_msgs)
Termination
  (* We expect that at least one message will be added in each step. The number
     of possible messages is limited above by the (finite) number of pairs of
     nodes in the (finite) factor graph. Thus, this process will eventually end
     and we will terminate.
.
     Thus, we expect CARD (message_domain fg) - CARD (FDOM msgs) to decrease
     by at least 1 in each step. We use this as the basis for our termination
     measure.
.    
     In practice, adding 1 to this value simplifies the proof process.
.
     If there are messages outside the valid message_domain, then they will be
     removed in the first call to this function. This may reduce the number of
     messages, but it will only happen on the first call. Thus, in this case,
     we treat it as though we have less than 0 messages, in order to ensure
     that the number of messages is always increasing
.     
     We use prim_recTheory.measure to turn our termination measure into a
     well-founded relation.
   *)
  WF_REL_TAC ‘measure (λ(fg, msgs).
                         (CARD (message_domain fg) + 2) -
                         (if FDOM msgs ⊆ message_domain fg
                          then
                            CARD (FDOM msgs) + 1
                          else 0
                         )
                      )’
  >> REVERSE (rpt strip_tac)
  >- (rw[]
      >> ‘CARD (FDOM msgs) ≤ CARD (message_domain fg)’ suffices_by simp[]
      >> simp[CARD_SUBSET]
     )
  >> qmatch_goalsub_abbrev_tac ‘const < new_val + (const - old_val)’
  >> qsuff_tac ‘old_val < new_val’
  >- gvs[]
  >> unabbrev_all_tac
  >> gvs[]
  >> rw[]
  >> irule CARD_PSUBSET
  >> gvs[]
  >> gvs[PSUBSET_MEMBER]
  >> gvs[FDOM_SUBSET_DRESTRICT]
  >> gvs[EXTENSION]
  >> Cases_on ‘x ∈ FDOM msgs’
  >- gvs[]
  >> gvs[]
  >> qexists ‘x’
  >> gvs[]
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
(* Calculate the message according to the message passing algorithm over the  *)
(* factor graph.                                                              *)
(*                                                                            *)
(* To ensure termination, this only returns a sensible result if the factor   *)
(* graph we are working on is a tree. If it is not a tree, we return the map  *)
(* which always returns 0.                                                    *)
(* -------------------------------------------------------------------------- *)
Definition sp_message_def:
  sp_message fg src dst =
  if is_tree fg.underlying_graph
  then
    if src ∈ fg.function_nodes
    then
      FUN_FMAP
      (λdst_val.
         ∑ (λval_map.
              fg.function_map ' src ' val_map *
              ∏ (λprev.
                   sp_message fg prev src '
                              (val_map ' prev)
                ) {prev | prev ∈ adjacent_nodes fg src ∧
                          prev ≠ dst})
           {val_map | FDOM val_map = adjacent_nodes fg src ∧
                      (∀n. n ∈ adjacent_nodes fg src ⇒
                           LENGTH (val_map ' n) =
                           fg.variable_length_map ' n) ∧
                      val_map ' dst = dst_val}
      ) (length_n_codes (fg.variable_length_map ' dst))
    else
      FUN_FMAP
      (λsrc_val.
         ∏ (λprev. sp_message fg prev src ' src_val)
           {prev | prev ∈ adjacent_nodes fg src ∧
                   prev ≠ dst})
      (length_n_codes (fg.variable_length_map ' src))
  else
    FUN_FMAP
    (λdst_val. 0 : extreal)
    (length_n_codes (fg.variable_length_map ' dst))
End
Termination
  (* At a leaf node, the subtree prior to our message is empty. At each step
     forward, the order of the subtree prior to our message increases by at
     least one (possibly more because the other branch may be deeper). Thus, we
     can use the 

As we step backwards through our computation, the subtree that from which
     we have collected our messages gets smalleris used to
  *)
  WF_REL_TAC ‘measure (λ(fg, src, dst).
                         order (subtree fg.underlying_graph dst src))’
  >> rpt strip_tac
  >> (pop_assum kall_tac
      >> qmatch_abbrev_tac ‘order prev_tree < order new_tree’
      >> ‘nodes prev_tree ⊂ nodes new_tree’
      >- (gvs[order_def]
         )
     )
      >> rpt strip_tac
      >- (
       )

         (diameter (subtree fg dst src))
         
         cheat
End

Theorem fdom_sp_calculate_messages0_subset[local]:
  ∀msgs fg.
    FDOM (sp_calculate_messages0 fg msgs) ⊆ message_domain fg
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[sp_calculate_messages0_def]
  >> rw[]
  >- (pop_assum (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
      >> gvs[UNION_SUBSET]
     )
  >> gvs[EXTENSION]
  >> Cases_on ‘x ∈ FDOM msgs’ >> gvs[]
QED


Theorem fdom_sp_calculate_messages0[simp]:
  ∀msgs fg.
    FDOM (sp_calculate_messages0 fg msgs) = message_domain fg
Proof
  rpt strip_tac
  >> PURE_REWRITE_TAC[EXTENSION]
  >> qx_gen_tac ‘dir_edge’
  >> EQ_TAC
  >- (PURE_ONCE_REWRITE_TAC[sp_calculate_messages0_def]
      >> gvs[]
      >> rw[]



      
      >> gvs[]
      >> PURE_ONCE_REWRITE_TAC[sp_calculate_messages0_def]
      >> gvs[]
      >> rw[]
      >- cheat

         
QED

(* -------------------------------------------------------------------------- *)
(* A message arriving at a variable node is the sum of products of all        *)
(* function nodes in that branch of the tree. Similarly, a message arriving   *)
(* at a function node is the sum of products of all function nodes in that    *)
(* branch of the tree.                                                        *)
(*                                                                            *)
(* We can work by induction to prove this. In the base case, we have a leaf   *)
(* node, and want to prove that our proposition holds. In the inductive step, *)
(* we have a set of child trees for which the proposition holds, and want to  *)
(* prove that it holds for the new tree consisting of the parent node and all *)
(* its child nodes.                                                           *)
(*                                                                            *)
(* In particular, our proposition is that the                                 *)
(*                                                                            *)
(* In the base case: if we have a variable node, then the product of all      *)
(* child functions will be 1                                                  *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem sp_calculate_messages0_sum_prod:
  ∀fg.
    sp_calculate_messages0 fg FEMPTY =
    FUN_FMAP
    (λdir_edge.
       let
         cur_var_node = if SND dir_edge ∈ var_nodes fg
                        then
                          SND dir_edge
                        else
                          FST dir_edge;
         cur_subtree = subtree fg.underlying_graph (SND dir_edge) (FST dir_edge);
       in
         FUN_FMAP
         (λcur_var_node_val.
            ∑ (λval_map.
                 ∏ (λfunc_node. (fg.function_map ' func_node)
                                ' (DRESTRICT val_map
                                             (adjacent_nodes fg cur_var_node)))
                   (fg.function_nodes ∩ nodes cur_subtree)
              ) {val_map | FDOM val_map = (var_nodes fg ∩ nodes cur_subtree) ∧
                           (∀n. n ∈ FDOM val_map ⇒
                                LENGTH (val_map ' n) =
                                fg.variable_length_map ' n) ∧
                           val_map ' cur_var_node = cur_var_node_val
                         }
         ) (length_n_codes (fg.variable_length_map ' (cur_var_node)))
    ) (message_domain fg)
Proof
  (* Want to prove equivalence for all choices of edge on fg.*)
  
  rpt strip_tac
  >> qmatch_abbrev_tac ‘f = g’
  >> gvs[GSYM fmap_EQ_THM]
  >> conj_tac
  >- (unabbrev_all_tac
      >> gvs[]
     )
  >> gvs[fmap_EQ_THM_ALT]
  >> qx_gen_tac ‘msg_dir_edge’

  >> unabbrev_all_tac >> gvs[]
  >> 
QED

(* -------------------------------------------------------------------------- *)
(* The message passing algorithm will give us the same result as summing over *)
(* the product of the terms in the factor graph.                              *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem sp_run_message_passing0_sum_prod:
  ∀fg.
    sp_run_message_passing0 fg =
    FUN_FMAP
    (λcur_var_node.
       FUN_FMAP
       (λcur_var_node_val.
          ∑ (λval_map.
               ∏ (λ(f,n). f ' (DRESTRICT val_map (adjacent_nodes fg n)))
                 { (f,n) | f = fg.function_map ' n}
            ) {val_map | FDOM val_map = var_nodes fg ∧
                         (∀n. n ∈ var_nodes fg ⇒
                              LENGTH (val_map ' n) =
                              fg.variable_length_map ' n) ∧
                         val_map ' cur_var_node = cur_var_node_val
                         }
       ) (length_n_codes (fg.variable_length_map ' cur_var_node))
    ) (var_nodes fg)
Proof
  (* Expand the definition of running the message passing algorithm *)
  qx_gen_tac ‘fg’
  >> gvs[sp_run_message_passing0_def]
  (* The creation of a finite map is boilerplate, and it is the same on both
     sides. We only really care that the actual function is equivalent on its
     domain. Use FUN_FMAP_EQ_THM to break it down so that we have to show that.
   *)
  >> DEP_PURE_ONCE_REWRITE_TAC[FUN_FMAP_EQ_THM]
  >> conj_tac >- gvs[]
  >> rpt strip_tac
  >> DEP_PURE_ONCE_REWRITE_TAC[FUN_FMAP_EQ_THM]
  >> conj_tac >- gvs[]
  >> rpt strip_tac
  (* *)
  >> 
QED

(* -------------------------------------------------------------------------- *)
(* This overload is useful for my purposes, but it may overlap with the more  *)
(* general concept of "the set of all pairs of adjacent nodes" in a scenario  *)
(* where we aren't working with the message passing algorithm, so I hide it   *)
(* before exporting the theory.                                               *)
(* -------------------------------------------------------------------------- *)
val _ = hide "message_domain"
