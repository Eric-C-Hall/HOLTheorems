Theory message_passing

Ancestors arithmetic bool combin ecc_prob_space extreal factor_graph finite_map fsgraph fundamental genericGraph hyperbolic_functions integer list lifting marker partite_ea probability pred_set prim_rec topology transc transfer tree

Libs donotexpandLib dep_rewrite ConseqConv simpLib liftLib transferLib;

val _ = augment_srw_ss [rewrites[FDOM_FMAP,
                                 FUN_FMAP_DEF,
                                 EXTREAL_PROD_IMAGE_EMPTY,
                                 PROD_IMAGE_EMPTY,
                                 EXTREAL_SUM_IMAGE_EMPTY,
                                 SUM_IMAGE_EMPTY,
                                 SUM_IMAGE_SING]];

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
(* EXTREAL_SUM_IMAGE_CONG, EXTREAL_PROD_IMAGE_CONG, and                       *)
(* extreal_sum_image_val_map_assignments_cong are particularly useful tools   *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* TODO: Consider moving generalised distributive law into its own file?      *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* The code in obsolete_message_passing seems relatively useful: it allows    *)
(* for a more computational and less mathematical perspective on message      *)
(* passing                                                                    *)
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

(* Theorem for showing equivalence of finite maps: fmap_EQ_THM.
   We also have fmap_EXT, which I think is better. *)

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

Theorem EXTREAL_SUM_IMAGE_CONG[cong]:
  ∀f g s1 s2.
    s1 = s2 ∧
    (∀x. x ∈ s2 ⇒ f x = g x) ⇒
    ∑ f s1 = ∑ g s2 : extreal
Proof
  rpt strip_tac
  >> Cases_on ‘FINITE s1’
  >- metis_tac[EXTREAL_SUM_IMAGE_EQ']
  >> gvs[EXTREAL_SUM_IMAGE_DEF, Once ITSET_def]
  >> gvs[Once ITSET_def]
QED

Theorem ITSET_CONG[cong]:
  ∀f g s1 s2 a1 a2.
    s1 = s2 ∧
    a1 = a2 ∧
    (∀x a. x ∈ s2 ⇒ f x a = g x a) ⇒
    ITSET f s1 a1 = ITSET g s2 a2
Proof
  rpt strip_tac
  >> Cases_on ‘FINITE s1’
  >- (gvs[]
      >> rpt (pop_assum mp_tac)
      >> MAP_EVERY qid_spec_tac [‘s1’, ‘a1’]
      >> Induct_on ‘CARD s1’
      >- (rw[]
          >> gvs[])
      >> ONCE_REWRITE_TAC[ITSET_def]
      >> rw[]
      >> Cases_on ‘s1’ >> gvs[]
      >> last_x_assum $ qspec_then ‘REST (x INSERT t)’ assume_tac
      >> gvs[CARD_REST]
      >> last_x_assum $ qspec_then ‘f (CHOICE (x INSERT t)) a1’ assume_tac
      >> gvs[]
      >> last_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[GSYM th])
      >> conj_tac
      >- (‘x INSERT t ≠ ∅’ by simp[]
          >> metis_tac[IN_INSERT, CHOICE_DEF])
      >> first_x_assum irule
      >> rpt strip_tac
      >> last_assum irule
      >> metis_tac[IN_INSERT, REST_DEF, IN_DELETE])
  >> PURE_ONCE_REWRITE_TAC[ITSET_def]
  >> rw[]
QED

Theorem EXTREAL_PROD_IMAGE_CONG[cong]:
  ∀f g s1 s2.
    s1 = s2 ∧
    (∀x. x ∈ s2 ⇒ f x = g x) ⇒
    ∏ f s1 = ∏ g s2 : extreal
Proof
  rpt strip_tac
  >> Cases_on ‘FINITE s1’
  >- metis_tac[EXTREAL_PROD_IMAGE_EQ]
  >> gvs[ext_product_def]
  >> gvs[iterateTheory.iterate]
  >> gvs[iterateTheory.support, SF CONJ_ss]
  >> rw[]
  >> irule ITSET_CONG
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* The set of all assignments to a particular set of variable nodes in a      *)
(* factor graph, where certain nodes are fixed to particular values.          *)
(*                                                                            *)
(* Assigning all possible values to only a single node should still be        *)
(* treated as a special case of this, in order to allow for consistency so    *)
(* that we can use the same theorems in this special case. Similarly, we      *)
(* should use this even if we have no need to fix certain nodes to certain    *)
(* values.                                                                    *)
(*                                                                            *)
(* fg: the factor graph                                                       *)
(* ns: the set of nodes                                                       *)
(* excl_val_map: a finite map from nodes to values. val_map is the same as    *)
(*               excl_val_map on these nodes. We expect that these values     *)
(*               have the appropriate lengths                                 *)
(*                                                                            *)
(* This currently overlaps with var_assignments. val_map_assignments works    *)
(* with an abstract factor graph, which is its advantage. By contrast,        *)
(* var_assignments is used in the definition of abstract factor graphs, so    *)
(* we can't combine the two definitions easily.                               *)
(*                                                                            *)
(* It is a common pattern to have an outer sum over all assignments to a      *)
(* subset of variables, and then within that sum, sum over all assignments to *)
(* a greater subset of variables while keeping the previous assignment fixed  *)
(* by including it in excl_val_map. This allows us to sum over a few          *)
(* variables at a time.                                                       *)
(* -------------------------------------------------------------------------- *)
Definition val_map_assignments_def:
  val_map_assignments fg ns excl_val_map =
  {val_map | FDOM val_map = ns ∩ var_nodes fg ∧
             (∀n. n ∈ FDOM val_map ⇒
                  LENGTH (val_map ' n : bool list) =
                  get_variable_length_map fg ' n) ∧
             (∀n. n ∈ FDOM val_map ∩ FDOM excl_val_map ⇒ val_map ' n = excl_val_map ' n)
                    }
End

(* -------------------------------------------------------------------------- *)
(* Our more convenient, more general definition for describing the set of     *)
(* assignments of variables to values is a subset of the more low-level       *)
(* definition.                                                                *)
(* -------------------------------------------------------------------------- *)
Theorem val_map_assignments_subset_var_assignments:
  ∀fg ns excl_val_map.
    ns ⊆ var_nodes fg ⇒
    val_map_assignments fg ns excl_val_map ⊆ var_assignments ns (get_variable_length_map fg)
Proof
  rpt strip_tac
  >> gvs[val_map_assignments_def, var_assignments_def]
  >> simp[SUBSET_DEF]
  >> qx_gen_tac ‘val_map’
  >> rpt strip_tac
  >> gvs[]
  >> metis_tac[SUBSET_INTER1]
QED

(* -------------------------------------------------------------------------- *)
(* Finding the assignements for a certain set of nodes is equivalent to       *)
(* finding the assignments for the subset of those nodes that are variable    *)
(* nodes in the factor graph.                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem val_map_assignments_restrict_nodes:
  ∀fg ns excl_val_map.
    val_map_assignments fg ns excl_val_map =
    val_map_assignments fg (ns ∩ var_nodes fg) excl_val_map
Proof
  rpt strip_tac
  >> gvs[val_map_assignments_def]
  >> simp[EXTENSION] >> rpt strip_tac >> EQ_TAC >> rpt strip_tac >> simp[]
  >> metis_tac[]
QED

Theorem finite_inter_var_nodes[simp]:
  ∀ns fg.
    FINITE (ns ∩ var_nodes fg)
Proof
  metis_tac[INTER_FINITE, INTER_COMM, var_nodes_finite]
QED

Theorem val_map_assignments_finite[simp]:
  ∀fg ns excl_val_map.
    FINITE (val_map_assignments fg ns excl_val_map)
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[val_map_assignments_restrict_nodes]
  >> irule SUBSET_FINITE
  >> qexists ‘var_assignments (ns ∩ var_nodes fg) (get_variable_length_map fg)’
  >> conj_tac >- gvs[]
  >> irule val_map_assignments_subset_var_assignments
  >> simp[]
QED

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
  if is_tree (get_underlying_graph fg) ∧
     adjacent (get_underlying_graph fg) src dst ∧
     src ≠ dst
  then
    if src ∈ get_function_nodes fg
    then
      FUN_FMAP
      (λdst_val_map.
         ∑ (λval_map.
              (get_function_map fg) ' src ' val_map *
              ∏ (λprev.
                   sp_message fg prev src ' (DRESTRICT val_map {prev})
                ) {prev | prev ∈ adjacent_nodes fg src ∧
                          prev ≠ dst})
           (val_map_assignments fg (adjacent_nodes fg src) dst_val_map)
      ) (val_map_assignments fg {dst} FEMPTY)
    else
      FUN_FMAP
      (λsrc_val_map.
         ∏ (λprev.
              sp_message fg prev src ' src_val_map
           )
           {prev | prev ∈ adjacent_nodes fg src ∧
                prev ≠ dst})
      (val_map_assignments fg {src} FEMPTY)
  else
    FUN_FMAP
    (λdst_val. 0 : extreal)
    (val_map_assignments fg ∅ FEMPTY)
Termination
  (* At a leaf node, there is no previous node, so we don't do any recursive
     calls. The message at a given step corresponds to a certain subtree:
     it makes recursive calls based on the prior messages. Each of these prior
     messages corresponds to a strictly smaller subtree. Thus, we can show that
     the size of the subtree gets smaller at each recursive call, and hence
     our function terminates.
   *)
  WF_REL_TAC ‘measure (λ(fg, src, dst).
                         order (subtree (get_underlying_graph fg) dst src))’
  >> rpt strip_tac
  >> (irule order_subtree_lt_adjacent
      >> gvs[]
      >> Cases_on ‘src = prev’ >> gvs[]
      >> gvs[adjacent_SYM])
End

(* -------------------------------------------------------------------------- *)
(* Tells us if a set of nodes contains all variable nodes associated with     *)
(* function nodes in the set of nodes                                         *)
(* -------------------------------------------------------------------------- *)
Definition contains_all_assoc_var_nodes_def:
  contains_all_assoc_var_nodes fg ns ⇔
    {n | ∃func_node. func_node ∈ ns ∧
                     func_node ∈ get_function_nodes fg ∧
                      adjacent (get_underlying_graph fg) n func_node} ⊆ ns
End

(* -------------------------------------------------------------------------- *)
(* Given a subset of the nodes in a factor graph, take the product of all     *)
(* these nodes while summing out the associated variable nodes, with the      *)
(* exception of some particular nodes which take particular values.           *)
(*                                                                            *)
(* We expect that the set of nodes provided contains all variable nodes that  *)
(* are associated with function nodes in the set. We may use                  *)
(* contains_all_assoc_var_nodes to check whether this is the case when using  *)
(* sum_prod                                                                   *)
(* -------------------------------------------------------------------------- *)
Definition sum_prod_def:
  sum_prod fg ns excl_val_map =
  ∑ (λval_map.
       ∏ (λfunc_node. (get_function_map fg ' func_node)
                      ' (DRESTRICT val_map
                                   (adjacent_nodes fg func_node)))
         (ns ∩ get_function_nodes fg) : extreal
    ) (val_map_assignments fg ns excl_val_map)
End

(* -------------------------------------------------------------------------- *)
(* A finite map corresponding to sum_prod which takes a specific value for    *)
(* the excluded node and returns the sum_prod when the excluded node takes    *)
(* that value.                                                                *)
(* -------------------------------------------------------------------------- *)
Definition sum_prod_map_def:
  sum_prod_map fg ns excl_nodes =
  FUN_FMAP
  (λexcl_val_map.
     sum_prod fg ns excl_val_map
  ) (val_map_assignments fg excl_nodes FEMPTY)
End

(* It's kinda interesting how this can be proven simply by applying
   gvs[factor_graph_ABSREP]. The second conjunct rewrites wffactor_graph as
   REP (ABS ...), and then the first conjunct simplifies the inner ABS (REP) *)
Theorem wffactor_graph_factor_graph_REP:
  ∀fg.
    wffactor_graph (factor_graph_REP fg)
Proof
  gvs[factor_graph_ABSREP]
QED

Theorem adjacent_in_function_nodes_not_in_function_nodes:
  ∀fg a b.
    adjacent (get_underlying_graph fg) a b ⇒
    (a ∈ get_function_nodes fg ⇔ b ∉ get_function_nodes fg)
Proof
  rpt strip_tac
  >> qspec_then ‘fg’ assume_tac wffactor_graph_factor_graph_REP
  >> drule_then assume_tac (cj 1 (iffLR wffactor_graph_def))
  >> gvs[gen_bipartite_ea_def, fsgedges_def, get_function_nodes_def,
         get_underlying_graph_def]
  >> metis_tac[]
QED

Theorem adjacent_nodes_subset_nodes_rep[simp]:
  ∀fg n.
    adjacent_nodes fg n ⊆ nodes fg.underlying_graph
Proof
  ASM_SET_TAC[]
QED

Theorem adjacent_nodes_subset_nodes_abs[simp]:
  ∀fg n.
    adjacent_nodes fg n ⊆ nodes (get_underlying_graph fg)
Proof
  gvs[get_underlying_graph_def]
QED

Theorem FINITE_adjacent_nodes[simp]:
  ∀fg src.
    FINITE (adjacent_nodes fg src)
Proof
  rpt strip_tac
  >> irule SUBSET_FINITE
  >> qexists ‘nodes (get_underlying_graph fg)’
  >> gvs[get_underlying_graph_def]
QED

Theorem exists_val_map:
  ∀fg n.
    ∃val_map : unit + num |-> bool list.
      FDOM val_map = adjacent_nodes fg n ∧
      ∀m. m ∈ FDOM val_map ⇒
          LENGTH (val_map ' m) = get_variable_length_map fg ' m
Proof
  rpt strip_tac
  >> qexists ‘FUN_FMAP
              (λm. REPLICATE (get_variable_length_map fg ' m) ARB)
              (adjacent_nodes fg n)’
  >> rpt strip_tac >> gvs[]
QED

Theorem exists_val_map_assignments:
  ∀fg ns excl_val_map.
    (∀n. n ∈ (ns ∩ var_nodes fg) ⇒
         LENGTH (excl_val_map ' n) = get_variable_length_map fg ' n) ⇒
    ∃val_map.
      val_map ∈ val_map_assignments fg ns excl_val_map
Proof
  rpt strip_tac
  >> gvs[val_map_assignments_def]
  >> qexists ‘FUN_FMAP
              (λm.
                 if m ∈ ns ∩ var_nodes fg then excl_val_map ' m
                 else
                   REPLICATE (get_variable_length_map fg ' m) ARB)
              (ns ∩ var_nodes fg)’
  >> gvs[finite_inter_var_nodes]
QED

(* -------------------------------------------------------------------------- *)
(* A congruence rule which tells the simplifier to only simplify the LHS of   *)
(* an equality.                                                               *)
(* -------------------------------------------------------------------------- *)
Theorem LHS_CONG:
  ∀LHS1 LHS2 RHS.
    LHS1 = LHS2 ⇒ (LHS1 = RHS ⇔ LHS2 = RHS)
Proof
  metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* A congruence rule which tells the simplifier to only simplify the RHS of   *)
(* an equality.                                                               *)
(* -------------------------------------------------------------------------- *)
Theorem RHS_CONG:
  ∀LHS RHS1 RHS2.
    RHS1 = RHS2 ⇒ (LHS = RHS1 ⇔ LHS = RHS2)
Proof
  metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* A congruence rule which tells the simplifier to not simplify within an     *)
(* equality.                                                                  *)
(* -------------------------------------------------------------------------- *)
Theorem IGNORE_EQ_CONG:
  ∀LHS RHS.
    LHS = RHS ⇔ LHS = RHS
Proof
  metis_tac[]
QED

(*
gvs[Cong LHS_CONG, sum_prod_def]
gvs[val_map_assignments_def]
*)

Theorem adjacent_nodes_inter_var_nodes_get_function_nodes[simp]:
  ∀fg src.
    src ∈ get_function_nodes fg ⇒
    adjacent_nodes fg src ∩ var_nodes fg = adjacent_nodes fg src
Proof
  rpt strip_tac
  >> gvs[EXTENSION]
  >> rpt strip_tac
  >> EQ_TAC >> gvs[]
  >> rpt strip_tac
  >> metis_tac[adjacent_in_function_nodes_not_in_function_nodes]
QED

Theorem adjacent_nodes_inter_var_nodes_var_nodes[simp]:
  ∀fg src.
    src ∈ var_nodes fg ⇒
    adjacent_nodes fg src ∩ var_nodes fg = ∅
Proof
  rpt strip_tac
  >> gvs[EXTENSION]
  >> rpt strip_tac
  >> CCONTR_TAC
  >> gvs[]
  >> metis_tac[adjacent_in_function_nodes_not_in_function_nodes]
QED

(* -------------------------------------------------------------------------- *)
(* More generalised verison of EXTREAL_SUM_IMAGE_EQ', which itself is more    *)
(* general that EXTREAL_SUM_IMAGE_EQ                                          *)
(* -------------------------------------------------------------------------- *)
Theorem EXTREAL_SUM_IMAGE_EQ3:
  ∀f g S.
    (∀x. x ∈ S ⇒ f x = g x) ⇒
    ∑ f S = ∑ g S : extreal
Proof
  rpt strip_tac
  >> Cases_on ‘FINITE S’ >- metis_tac[EXTREAL_SUM_IMAGE_EQ']
  >> gvs[EXTREAL_SUM_IMAGE_DEF]
  >> PURE_ONCE_REWRITE_TAC[ITSET_def]
  >> rw[]
QED

(* -------------------------------------------------------------------------- *)
(* Special version of congruence rule to use when summing over a set of       *)
(* assignments of variables to values, which allows us to bring the relevant  *)
(* information into our context during rewrites without having to expand out  *)
(* val_map_assignments                                                        *)
(* -------------------------------------------------------------------------- *)
Theorem extreal_sum_image_val_map_assignments_cong:
  ∀f g fg ns excl_val_map.
    (∀val_map.
       FDOM val_map = ns ∩ var_nodes fg ∧
       (∀n. n ∈ FDOM val_map ⇒
            LENGTH (val_map ' n) = get_variable_length_map fg ' n) ∧
       (∀n. n ∈ FDOM val_map ∩ FDOM excl_val_map ⇒
            val_map ' n = excl_val_map ' n) ⇒
       f val_map = g val_map)
    ⇒ ∑ f (val_map_assignments fg ns excl_val_map) =
      ∑ g (val_map_assignments fg ns excl_val_map) : extreal
Proof
  rpt strip_tac
  >> irule EXTREAL_SUM_IMAGE_CONG
  >> simp[val_map_assignments_def]
QED

(* -------------------------------------------------------------------------- *)
(* Congruence rule for the set of assignments to variables: the excl_val_map  *)
(* only needs to be the same when it is applied to values in the appropriate  *)
(* set                                                                        *)
(* -------------------------------------------------------------------------- *)
Theorem val_map_assignments_cong:
  ∀fg1 fg2 ns1 ns2 excl_val_map1 excl_val_map2.
    fg1 = fg2 ∧
    ns1 = ns2 ∧
    (FDOM excl_val_map1 ∩ ns2 = FDOM excl_val_map2 ∩ ns2) ∧
    (∀x. x ∈ ns2 ∧
         x ∈ FDOM excl_val_map1 ∧
         x ∈ FDOM excl_val_map2 ⇒ excl_val_map1 ' x = excl_val_map2 ' x) ⇒
    val_map_assignments fg1 ns1 excl_val_map1 =
    val_map_assignments fg2 ns2 excl_val_map2
Proof
  rpt strip_tac
  >> gvs[]
  >> simp[SET_EQ_SUBSET]
  (* Without loss of generality, we only need to prove that one is a subset
        of the other in one direction *)
  >> wlog_tac ‘¬(val_map_assignments fg1 ns1 excl_val_map1 ⊆
                                     val_map_assignments fg1 ns1 excl_val_map2)’
              [‘excl_val_map1’, ‘excl_val_map2’]
  >- (Cases_on ‘val_map_assignments fg1 ns1 excl_val_map2 ⊆
                val_map_assignments fg1 ns2 excl_val_map2’
      >> metis_tac[SET_EQ_SUBSET])
  >> gvs[]
  >> pop_assum mp_tac >> gvs[]
  (* Simplify using basic definitions *)
  >> simp[val_map_assignments_def]
  >> simp[SUBSET_DEF]
  >> qx_gen_tac ‘val_map’
  >> rpt strip_tac
  (* *)
  >> ‘n ∈ FDOM excl_val_map1’ by ASM_SET_TAC[]
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* If we restrict an assignment of variables to values to a smaller subset,   *)
(* we get an assignment of variables to values on that smaller subset.        *)
(* -------------------------------------------------------------------------- *)
Theorem drestrict_in_val_map_assignments:
  ∀val_map ns1 ns2 fg excl_val_map1 excl_val_map2.
    val_map ∈ val_map_assignments fg ns1 excl_val_map1 ∧
    ns2 ⊆ ns1 ∧
    DRESTRICT excl_val_map2 ns2 ⊑ DRESTRICT excl_val_map1 ns2 ⇒
    DRESTRICT val_map ns2 ∈ val_map_assignments fg ns2 excl_val_map2
Proof
  rpt strip_tac
  >> simp[val_map_assignments_def]
  >> rpt conj_tac >> gvs[DRESTRICT_DEF]
  >- (gvs[val_map_assignments_def]
      >> ASM_SET_TAC[]
     )
  >- gvs[val_map_assignments_def]
  >> rpt strip_tac
  >> gvs[SUBMAP_DEF, DRESTRICT_DEF]
  >> gvs[val_map_assignments_def]
QED

(* -------------------------------------------------------------------------- *)
(* This expression occurs naturally when sp_message is applied to something,  *)
(* so simplify it.                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem FUN_FMAP_val_map_assignments_DRESTRICT:
  ∀fg f ns val_map.
    val_map ∈ val_map_assignments fg ns1 excl_val_map1 ∧
    ns ⊆ ns1 ⇒
    FUN_FMAP f (val_map_assignments fg ns FEMPTY) '
             (DRESTRICT val_map ns) = f (DRESTRICT val_map ns)
Proof
  rpt strip_tac
  >> irule (cj 2 FUN_FMAP_DEF)
  >> simp[]
  >> simp[drestrict_in_val_map_assignments]
  >> irule drestrict_in_val_map_assignments
  >> qexistsl [‘excl_val_map1’, ‘ns1’]
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Congruence rule to specify that we would like to perform our rewrites      *)
(* within the function of a sum, and not within the set.                      *)
(* -------------------------------------------------------------------------- *)
Theorem EXTREAL_SUM_IMAGE_FUNC_CONG:
  ∀f1 f2 S.
    (∀x. x ∈ S ⇒ f1 x = f2 x) ⇒
    ∑ f1 S = ∑ f2 S : extreal
Proof
  gvs[EXTREAL_SUM_IMAGE_CONG]
QED

(* -------------------------------------------------------------------------- *)
(* Perform a repeated sum over a function which takes an assignment of nodes  *)
(* to values and returns an extreal                                           *)
(* -------------------------------------------------------------------------- *)
Definition rpt_val_map_assignments_sum_def:
  rpt_val_map_assignments_sum fg f [] val_map = f val_map : extreal ∧
  rpt_val_map_assignments_sum fg f (l::ls) val_map =  
  ∑ (λval_map_new. rpt_val_map_assignments_sum fg f ls val_map_new)
    (val_map_assignments fg (l ∪ FDOM val_map) val_map)
End

Theorem rpt_val_map_assignments_sum_empty[simp]:
  ∀fg f.
    rpt_val_map_assignments_sum fg f [] = f
Proof
  gvs[FUN_EQ_THM, rpt_val_map_assignments_sum_def]
QED

Theorem rpt_val_map_assignments_sum_sing:
  ∀fg f l val_map.
    rpt_val_map_assignments_sum fg f [l] val_map =
    ∑ f (val_map_assignments fg (l ∪ FDOM val_map) val_map)
Proof
  rpt strip_tac
  >> gvs[rpt_val_map_assignments_sum_def]
  >> gvs[SF ETA_ss]
QED

(* -------------------------------------------------------------------------- *)
(* Bigunion for finite maps: only works on finite sets of fmaps.              *)
(*                                                                            *)
(* Possible improvement: would be nice to have a version which works on       *)
(* infinite sets of fmaps.                                                    *)
(*                                                                            *)
(* FBIGUNION is pretty messy to use unless you know that all of the fmaps     *)
(* being operated on have disjoint domains. Otherwise, the chosen value at    *)
(* a point where the maps overlap is ambiguous, and may change as elements    *)
(* are added/removed from the set. Use disjoint_domains_def to test for this. *)
(* -------------------------------------------------------------------------- *)
Definition FBIGUNION_DEF:
  FBIGUNION S = ITSET FUNION S FEMPTY
End

Theorem FBIGUNION_EMPTY[simp]:
  FBIGUNION ∅ = FEMPTY
Proof
  gvs[FBIGUNION_DEF]
QED

Theorem val_map_assignments_empty[simp]:
  ∀fg excl_val_map.
    val_map_assignments fg ∅ excl_val_map = {FEMPTY}
Proof
  rpt strip_tac
  >> gvs[val_map_assignments_def]
  >> gvs[EXTENSION] >> qx_gen_tac ‘val_map’ >> EQ_TAC >> rpt strip_tac >> gvs[]
  >> gvs[GSYM fmap_EQ_THM]
  >> gvs[EXTENSION]
QED

Theorem FDOM_ITSET_FUNION_FEMPTY:
  ∀S acc.
    FINITE S ⇒
    FDOM (ITSET FUNION S acc) = BIGUNION (IMAGE FDOM S) ∪ FDOM acc
Proof
  (* Typical FINITE_INDUCT isn't sufficient in this case because we don't know
     which element ITSET will choose first when performing its iterations, and
     as a result, if our large instance is e INSERT S, our smaller instance may
     not be S, but rather an element other than e may have been removed. Thus,
     we instead induct on the cardinality of S. Thus, we introduce a variable
     to represent the cardinality of S.
.
     I initially tried proving FDOM_FBIGUNION directly, but it turns out we
     need our inductive hypothesis to work for an arbitrary accumulator, so I
     had to expand out FBIGUNION to allow for that *)
  rpt strip_tac
  >> qabbrev_tac ‘c = CARD S’ >> gs[Abbrev_def]
  >> rpt (pop_assum mp_tac) >> SPEC_ALL_TAC
  (* Induct on cardinality *)
  >> Induct_on ‘c’ >> rpt strip_tac >> gvs[]
  (* Perform one iteration, so that we may reduce to a smaller instance to use
     our inductive hypothesis *)
  >> PURE_ONCE_REWRITE_TAC[ITSET_def]
  >> simp[]
  >> Cases_on ‘S = ∅’ >> gvs[]
  (* Use inductive hypothesis on appropriate set *)
  >> last_x_assum $ qspecl_then
                  [‘REST S’, ‘CHOICE S ⊌ acc’]
                  assume_tac
  >> gvs[CARD_REST]
  (* *)
  >> simp[AC UNION_COMM UNION_ASSOC]
  >> qmatch_abbrev_tac ‘s1 ∪ s2 = s1 ∪ s3’
  >> ‘s2 = s3’ suffices_by simp[] >> simp[Abbr ‘s1’, Abbr ‘s2’, Abbr ‘s3’]
  >> PURE_ONCE_REWRITE_TAC[GSYM BIGUNION_INSERT]
  >> PURE_ONCE_REWRITE_TAC[GSYM IMAGE_INSERT]
  >> metis_tac[CHOICE_INSERT_REST]
QED

Theorem FDOM_FBIGUNION:
  ∀S.
    FINITE S ⇒
    FDOM (FBIGUNION S) =
    BIGUNION (IMAGE FDOM S)
Proof
  rpt strip_tac
  >> gvs[FBIGUNION_DEF]
  >> gvs[FDOM_ITSET_FUNION_FEMPTY]
QED

Theorem REST_INSERT:
  ∀x S.
    REST (x INSERT S) =
    (if CHOICE (x INSERT S) = x
     then
       S DELETE x
     else
       x INSERT (S DELETE (CHOICE (x INSERT S)))
    )
Proof
  rpt strip_tac
  >> rw[] >> gvs[REST_DEF, DELETE_INSERT, INSERT_DELETE]
QED

(* -------------------------------------------------------------------------- *)
(* A generalised version of COMMUTING_ITSET_INSERT                            *)
(*                                                                            *)
(* We only require the assumption of associativity and commutativity on the   *)
(* set we are iterating over, and not in general.                             *)
(* -------------------------------------------------------------------------- *)
Theorem COMMUTING_ITSET_INSERT_GEN:
  ∀f e S acc.
    (∀x y z.
       x ∈ e INSERT S ∧
       y ∈ e INSERT S ⇒
       f x (f y z) = f y (f x z)) ∧
    FINITE S ⇒
    ITSET f (e INSERT S) acc = ITSET f (S DELETE e) (f e acc)
Proof
  (* Prepare for induction on the cardinality of S *)
  rpt strip_tac
  >> qabbrev_tac ‘c = CARD S’
  >> gs[Abbrev_def, Excl "IN_INSERT"]
  >> rpt (pop_assum mp_tac) >> simp[AND_IMP_INTRO, Excl "IN_INSERT"]
  >> SPEC_ALL_TAC
  (* Induction on the cardinality of S *)
  >> completeInduct_on ‘c’ >> rpt strip_tac >> gvs[Excl "IN_INSERT"]
  (* We only need to prove the theorem in the case where e ∉ S, because if
     e ∈ S, then e INSERT S is equivalent to e INSERT (S DELETE e), and thus
     we can apply the version of the theorem which only works when e ∉ S to
     S DELETE e insead of S. *)
  >> wlog_tac ‘e ∉ S’ [‘c’, ‘e’, ‘S’]
  >- (gvs[iffLR ABSORPTION]
      >> Cases_on ‘S = ∅’ >> gvs[]
      >> ‘S = e INSERT (S DELETE e)’ by metis_tac[INSERT_DELETE]
      >> pop_assum (fn th => PURE_REWRITE_TAC[Once th])
      (* Handle case where S has cardinality 1 *)
      >> Cases_on ‘CARD S = 1’
      >- (Cases_on ‘S’ >> gvs[])
      (* Use case of theorem which requires that it isn't a member *)
      >> qpat_x_assum ‘∀e' S' acc. _ ∧ _ ∧ _ ∧ _ ⇒ _’
                      (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
      (* The final result is now trivial *)
      >> REVERSE conj_tac >- simp[]
      (* We now just need to prove the preconditions of the theorem in the
         case where it isn't a member *)
      >> simp[]
      >> conj_tac
      >- (rpt strip_tac >> gvs[])
      >> ‘∀m. m < CARD S - 1 ⇒ m < CARD S’ by decide_tac
      >> gen_tac >> disch_tac
      >> last_x_assum (qspec_then ‘m’ assume_tac)
      >> gvs[]
     )
  (* It's nice to know that S is nonempty *)
  >> Cases_on ‘S = ∅’ >> gvs[Excl "IN_INSERT"]
  (* Expand out according to the definition of ITSET once on the left hand side
     to reduce to a smaller set so we can use the inductive hypothesis. *)
  >> simp[Once ITSET_def, Cong LHS_CONG]
  (* The case where we chose e as our first choice to iterate over *)
  >> Cases_on ‘CHOICE (e INSERT S) = e’
  >- (simp[REST_DEF]
      >> simp[DELETE_INSERT])
  (* The case where we iterate over another element as our first choice.
     In this case, e is in the REST, so we can use our inductive hypothesis *)
  >> simp[REST_INSERT]
  >> last_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  (* Prove preconditions for inductive hypothesis *)
  >> conj_tac
  >- (qexists ‘CARD S - 1’ >> gvs[Excl "IN_INSERT"]
      >> conj_tac >- (Cases_on ‘S’ >> gvs[Excl "IN_INSERT"])
      >> Cases_on ‘CHOICE (e INSERT S) = e’ >> gvs[Excl "IN_INSERT"]
      >> ‘CHOICE (e INSERT S) ∈ S’ by metis_tac[CHOICE_DEF, IN_INSERT,
                                                NOT_INSERT_EMPTY]
      >> gvs[Excl "IN_INSERT"]
      (* Final precondition to use the inductive hypothesis *)
      >> rpt strip_tac
      >> gvs[])
  (* We can also use the inductive hypothesis on the RHS to take the chosen
     element from the set to the accumulator *)
  >> qabbrev_tac ‘e' = CHOICE (e INSERT S)’
  (* It's helpful to know e' ∈ S *)
  >> ‘e' ∈ S’ by metis_tac[CHOICE_DEF, IN_INSERT, NOT_INSERT_EMPTY]
  (* Rewrite set on RHS to make it clear that e' is contained in it so we can
     use the inductive hypothesis*)
  >> ‘S DELETE e = e' INSERT (S DELETE e DELETE e')’ by simp[INSERT_DELETE]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  (* Use inductive hypothesis on RHS *)
  >> last_x_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  (* Preconditions for inductive hypothesis *)
  >> conj_tac
  >- (simp[]
      >> conj_tac >- (Cases_on ‘S’ >> gvs[])
      >> rpt strip_tac >> gvs[]
      >> metis_tac[]
     )
  (* Simplify, and use commutativity assumption to solve *)
  >> gvs[DELETE_COMM]
QED

Theorem INSERT_DELETE_EQ:
  ∀s x y.
    x INSERT (s DELETE y) =
    if y = x then x INSERT s else (x INSERT s) DELETE y
Proof
  rpt strip_tac
  >> Cases_on ‘x = y’
  >- (gvs[]
      >> Cases_on ‘x ∈ s’
      >- simp[iffLR ABSORPTION]
      >> simp[DELETE_NON_ELEMENT_RWT]
     )
  >> simp[DELETE_INSERT]
QED

(* -------------------------------------------------------------------------- *)
(* A generalised version of COMMUTING_ITSET_RECURSES                          *)
(*                                                                            *)
(* We only require the assumption of associativity and commutativity on the   *)
(* set we are iterating over, and not in general.                             *)
(* -------------------------------------------------------------------------- *)
Theorem COMMUTING_ITSET_RECURSES_GEN:
  ∀e S f acc.
    (∀x y z.
       x ∈ e INSERT S ∧
       y ∈ e INSERT S ⇒
       f x (f y z) = f y (f x z)) ∧
    FINITE S ⇒
    ITSET f (e INSERT S) acc = f e (ITSET f (S DELETE e) acc)
Proof
  (* We induct over the size of e INSERT s. When we take an element out, if it
     is not e, then the inductive hypothesis applies: we use a lemma to move f
     from the accumulator to the outside. *)
  rpt strip_tac
  >> qabbrev_tac ‘c = CARD S’
  >> gs[Abbrev_def, Excl "IN_INSERT"]
  >> rpt $ pop_assum mp_tac >> simp[AND_IMP_INTRO, Excl "IN_INSERT"]
  >> SPEC_ALL_TAC
  (* Perform the induction *)
  >> completeInduct_on ‘c’ >> rpt strip_tac >> gvs[Excl "IN_INSERT"]
  (* We want to take an element other than e out of e INSERT s. First prove
     that such an element exists *)
  >> CCONTR_TAC
  >> sg ‘∃x. x ≠ e ∧ x ∈ S’
  >- (Cases_on ‘S’
      >- gvs[] (* S is size 0 *)
      >> Cases_on ‘t’
      >- (Cases_on ‘x = e’ >> gvs[]) (* S is size 1 *)
      >> Cases_on ‘x = e’ (* S has size 2 or more: choose appropriate elt *)
      >- (qexists ‘x'’ >> gvs[])
      >> qexists ‘x’ >> gvs[]
     )
  >> qpat_x_assum ‘ITSET _ _ _ ≠ f e (ITSET _ _ _)’ mp_tac >> simp[]
  (* Rewrite our set so that the element we would like to take out is at the
     front *)
  >> sg ‘e INSERT S = x INSERT (e INSERT S) DELETE x’
  >- metis_tac[INSERT_DELETE, IN_INSERT]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  (* Using COMMUTING_ITSET_INSERT_GEN, take our element x which is not e out of
     e INSERT S and into the accumulator *)
  >> DEP_PURE_ONCE_REWRITE_TAC[COMMUTING_ITSET_INSERT_GEN]
  >> conj_tac
  >- (simp[] >> rw[] >> simp[])
  >> simp[DELETE_DELETE]
  (* Now we can apply our inductive hypothesis, because we have a smaller set
     which still has e in it. *)
  >> simp[DELETE_INSERT]
  >> last_x_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  >> conj_tac
  >- (gvs[] >> rw[] >> gvs[] >> Cases_on ‘S’ >> gvs[]) 
  (* Use COMMUTING_ITSET_INSERT_GEN again to move x back into the set from the
     accumulator *)
  >> PURE_ONCE_REWRITE_TAC[DELETE_COMM]
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM COMMUTING_ITSET_INSERT_GEN]
  >> conj_tac
  >- (rw[] >> gvs[])
  >> gvs[INSERT_DELETE_EQ, iffLR ABSORPTION]
QED

(* -------------------------------------------------------------------------- *)
(* A generalised version of ITSET_REDUCTION.                                  *)
(*                                                                            *)
(* We only require the assumption of associativity and commutativity on the   *)
(* set we are iterating over, and not in general.                             *)
(*                                                                            *)
(* See also SUBSET_COMMUTING_ITSET_REDUCTION: this proves a similar thing,    *)
(* but it does not seem to suffice for my purposes.                           *)
(*                                                                            *)
(* It is tricky to try to prove this using induction. Initially, I was        *)
(* wanting to induct on the size of the set, apply a single iteration of      *)
(* ITSET on the LHS, and use the inductive hypothesis. However, this runs     *)
(* into two problems: firstly, if the iteration of ITSET chooses e, then      *)
(* e is suddenly in the accumulator, and because it isn't in the set, our     *)
(* inductive hypothesis doesn't apply, and it isn't obvious that applying f   *)
(* in the accumulator, in the innermost part of the sequence of function      *)
(* applications is equivalent to applying it in the outermost part of the     *)
(* sequence of function applications. Perhaps we could prove this by doing    *)
(* a second induction. This appears to be how the initial implementation of   *)
(* ITSET_REDUCTION The second issue is that if the iteration of ITSET     *)
(* chooses something other than e, then we can use the inductive hypothesis,  *)
(* but while we want to get the result ITSET f S b, we actually get           *)
(* ITSET f (S DELETE x) (f x b). It is unclear that these are equivalent      *)
(* because ITSETs on different sets may choose their elements in a different  *)
(* order. In particular, x was chosen from e INSERT S, but now that we are    *)
(* choosing an element from S instead, we may not                             *)
(*                                                                            *)
(* An alternative approach is to try to find a function which is equivalent   *)
(* to f if the first element is in the set (for all choices of second,        *)
(* argument, including those not in the set) but is otherwise modified to     *)
(* satisfy the required condition. Then we can use ITSET_REDUCTION to solve.  *)
(* Initially, I considered setting the function to a specific arbitrary value *)
(* not in the set if either argument was not in the set, but this fails       *)
(* because the function needs to be the same if the left element is in the    *)
(* set for arbitrary right elements. Perhaps if we know b is in the set and   *)
(* the set is closed under f, we would only need the function to be the same  *)
(* if both elements are in the set? Another problem is the fact that if       *)
(* we apply f to x and y in the set, we may end up with an element not in the *)
(* set, so if we naively change this function to always the same value if an  *)
(* input is not in the set, we may break the property we need.                *)
(* -------------------------------------------------------------------------- *)
Theorem ITSET_REDUCTION_GEN:
  ∀f S e acc.
    (∀x y z.
       x ∈ e INSERT S ∧
       y ∈ e INSERT S ⇒
       f x (f y z) = f y (f x z)) ∧
    FINITE S ∧
    e ∉ S ⇒
    ITSET f (e INSERT S) acc = f e (ITSET f S acc)
Proof
  rpt strip_tac
  >> DEP_PURE_ONCE_REWRITE_TAC[COMMUTING_ITSET_RECURSES_GEN]
  >> conj_tac
  >- (gvs[] >> rw[] >> gvs[])
  >> simp[DELETE_NON_ELEMENT_RWT]
QED

(* -------------------------------------------------------------------------- *)
(* If we have a function that is idempotent (when applied twice with the      *)
(* same first input) and is commuting (between possible orders of two first   *)
(* elements applied to a second element), then applying f with a first        *)
(* element that is in the set will have no effect on the ITSET                *)
(* -------------------------------------------------------------------------- *)
Theorem COMMUTING_ITSET_IDEMPOTENT_GEN:
  ∀f S e acc.
    (∀y. f e (f e y) = f e y) ∧
    (∀x y z.
       x ∈ e INSERT S ∧
       y ∈ e INSERT S ⇒
       f x (f y z) = f y (f x z)) ∧
    FINITE S ∧
    e ∈ S ⇒
    f e (ITSET f S acc) = ITSET f S acc
Proof
  rpt strip_tac
  >> ‘S = e INSERT (S DELETE e)’ by simp[]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> DEP_PURE_ONCE_REWRITE_TAC[ITSET_REDUCTION_GEN]
  >> conj_tac
  >- (gvs[] >> rw[] >> gvs[])
  >> gvs[]
QED

Theorem FUNION_IDEMPOT_2[simp]:
  ∀f g.
    f ⊌ (f ⊌ g) = f ⊌ g
Proof
  rpt strip_tac
  >> gvs[FUNION_ASSOC]
QED

(* -------------------------------------------------------------------------- *)
(* Returns true if the domains of the given fmaps are disjoint.               *)
(*                                                                            *)
(* Using disjoint (IMAGE FDOM S) doesn't work because if two of the fmaps     *)
(* have the same domain, then they will map to the same set, and so the       *)
(* resulting set of sets will only have one element and hence will be         *)
(* trivially disjoint, but we want them to not be considered disjoint in this *)
(* case as we have two fmaps with the same domain.                            *)
(* -------------------------------------------------------------------------- *)
Definition disjoint_domains_def:
  disjoint_domains S ⇔ pairwiseD (λf1 f2. DISJOINT (FDOM f1) (FDOM f2)) S
End

Theorem disjoint_domains_disjoint:
  ∀f g S.
    f ∈ S ∧
    g ∈ S ∧
    f ≠ g ∧
    disjoint_domains S ⇒
    DISJOINT (FDOM f) (FDOM g)
Proof
  rpt strip_tac
  >> gvs[disjoint_domains_def]
  >> gvs[pairwise]
QED

Theorem drag_out_precondition:
  ∀b1 b2 b3.
    (b1 ∧ b2 ⇔ b3 ∧ b2) ⇔ (b2 ⇒ (b1 ⇔ b3))
Proof
  metis_tac[]
QED

Theorem disjoint_domains_insert:
  ∀e S.
    disjoint_domains (e INSERT S) ⇔
      (∀x. x ∈ S ∧ x ≠ e ⇒ DISJOINT (FDOM e) (FDOM x)) ∧
      disjoint_domains S
Proof
  rpt strip_tac
  >> gvs[disjoint_domains_def]
  >> gvs[PAIRWISE_INSERT]
  >> gvs[drag_out_precondition]
  >> rpt strip_tac
  >> metis_tac[DISJOINT_SYM]
QED

Theorem FUNION_FBIGUNION_ABSORPTION:
  ∀e S.
    FINITE S ∧
    disjoint_domains S ∧
    e ∈ S ⇒
    e ⊌ FBIGUNION S = FBIGUNION S
Proof
  rpt strip_tac
  >> gvs[FBIGUNION_DEF]
  >> irule COMMUTING_ITSET_IDEMPOTENT_GEN
  >> gvs[]
  >> rpt gen_tac
  >> rpt disch_tac
  >> gnvs[FUNION_ASSOC]
  >> ‘x ⊌ y = y ⊌ x’ suffices_by metis_tac[]
  >> Cases_on ‘x = y’ >- metis_tac[]
  >> irule FUNION_COMM
  >> metis_tac[disjoint_domains_disjoint]
QED

(* -------------------------------------------------------------------------- *)
(* Taking the FBIGUNION of a set of finite maps is equivalent to FUNION-ing   *)
(* the first finite map with the FBIGUNION of the rest (assuming that all     *)
(* the maps have disjoint domains: otherwise the FBIGUNION is indeterminate   *)
(* on the shared points which may make these maps non-equivalent              *)
(* -------------------------------------------------------------------------- *)
Theorem FBIGUNION_INSERT:
  ∀e S.
    FINITE S ∧
    disjoint_domains (e INSERT S) ⇒
    FBIGUNION (e INSERT S) =
    FUNION e (FBIGUNION S)
Proof
  rpt strip_tac
  (* If e is not in S, this is a special case of ITSET_REDUCTION_GEN *)
  >> Cases_on ‘e ∉ S’
  >- (simp[FBIGUNION_DEF]
      >> irule ITSET_REDUCTION_GEN
      >> simp[Excl "IN_INSERT"]
      >> rpt strip_tac
      >> simp[FUNION_ASSOC, Excl "IN_INSERT"]
      >> ‘x ⊌ y = y ⊌ x’ suffices_by metis_tac[]
      >> Cases_on ‘x = y’ >- simp[]
      >> irule FUNION_COMM
      >> irule disjoint_domains_disjoint
      >> simp[]
      >> qexists ‘e INSERT S’
      >> simp[]
     )
  (* If e is in S, we can absorb it into S and into FBIGUNION S. *)
  >> gvs[iffLR ABSORPTION, FUNION_FBIGUNION_ABSORPTION]
QED

(* -------------------------------------------------------------------------- *)
(* Allow us to induct on the cardinality of a set, rather than the elements   *)
(* in that set.                                                               *)
(* -------------------------------------------------------------------------- *)
Theorem CARD_INDUCT:
  ∀P.
    P ∅ ∧
    (∀s. FINITE s ∧ (∀s2. FINITE s2 ∧ CARD s2 < CARD s ⇒ P s2) ⇒ P s) ⇒
    (∀s. FINITE s ⇒ P s)
Proof
  rpt strip_tac
  >> qabbrev_tac ‘c = CARD s’ >> gs[Abbrev_def]
  >> rpt (pop_assum mp_tac) >> SPEC_ALL_TAC
  >> completeInduct_on ‘c’ >> rpt strip_tac >> metis_tac[]
QED

Theorem disjoint_domains_image:
  ∀S r f.
    disjoint_domains S ⇒
    (disjoint_domains (IMAGE f S) ⇔
       ∀x y.
         x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ f x ≠ f y ⇒
         DISJOINT (FDOM (f x)) (FDOM (f y))
    )
Proof
  rpt strip_tac
  >> gvs[disjoint_domains_def]
  >> gvs[PAIRWISE_IMAGE]
  >> gvs[pairwise]
  >> metis_tac[]
QED

Theorem disjoint_domains_image_drestrict:
  ∀S r.
    disjoint_domains S ⇒
    disjoint_domains (IMAGE (λx. DRESTRICT x r) S)
Proof
  rpt strip_tac
  >> gvs[disjoint_domains_image] >> rpt strip_tac
  >> gvs[FDOM_DRESTRICT]
  >> irule sigma_algebraTheory.DISJOINT_RESTRICT_L
  >> metis_tac[disjoint_domains_disjoint]
QED

Theorem DIFF_NO_EFFECT:
  ∀S T.
    S DIFF T = S ⇔ T ∩ S = ∅
Proof
  ASM_SET_TAC[]
QED

Theorem DRESTRICT_FBIGUNION:
  ∀S r.
    FINITE S ∧
    disjoint_domains S ⇒
    DRESTRICT (FBIGUNION S) r = FBIGUNION (IMAGE (λx. DRESTRICT x r) S)
Proof
  (* Induct on S *)
  simp[GSYM AND_IMP_INTRO]
  >> simp[RIGHT_FORALL_IMP_THM]
  >> Induct_on ‘S’ using CARD_INDUCT >> rpt strip_tac >> simp[]
  >> gvs[AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM]
  >> Cases_on ‘S’ >> gvs[]
  (* Break down LHS so as to use inductive hypothesis *)
  >> gvs[FBIGUNION_INSERT]
  >> gvs[DRESTRICTED_FUNION]
  (* Use inductive hypothesis *)
  >> qpat_x_assum ‘∀S' r. _ ⇒ _’ (fn th => DEP_PURE_ONCE_REWRITE_TAC[th])
  (* Precondition for inductive hypothesis *)
  >> conj_tac
  >- (simp[] >> metis_tac[disjoint_domains_insert])
  (* Break down the RHS to match the LHS *)
  >> DEP_PURE_ONCE_REWRITE_TAC[FBIGUNION_INSERT]
  >> conj_tac
  >- (simp[]
      >> Q.SUBGOAL_THEN ‘DRESTRICT x r INSERT IMAGE (λx. DRESTRICT x r) t =
                         IMAGE (λx. DRESTRICT x r) (x INSERT t)’
          (fn th => PURE_ONCE_REWRITE_TAC[th])
      >- simp[]
      >> metis_tac[disjoint_domains_image_drestrict]
     )
  (* We only need to prove that restricting everything in t to r is equivalent
        to restricting everything in t to r without the domain of x, because
        the domain of x was disjoint with the domain of anything in r. *)
  >> ‘IMAGE (λx'. DRESTRICT x' (r DIFF FDOM x)) t = IMAGE (λx. DRESTRICT x r) t’
    suffices_by metis_tac[]
  >> irule IMAGE_CHANGE_FUN
  >> rpt strip_tac
  >> simp[FUN_EQ_THM] >> rpt strip_tac
  >> simp[DRESTRICT_EQ_DRESTRICT]
  >> simp[DIFF_INTER]
  >> simp[DIFF_NO_EFFECT]
  >> ‘FDOM x ∩ FDOM x' = ∅’ suffices_by ASM_SET_TAC[]
  >> simp[GSYM DISJOINT_DEF]
  >> irule disjoint_domains_disjoint
  >> Cases_on ‘x = x'’ >> gvs[]
  >> qexists ‘x INSERT t’
  >> simp[]
QED

Theorem disjoint_insert_iff:
  ∀e S.
    disjoint (e INSERT S) ⇔
      disjoint S ∧ (∀x. x ∈ S ∧ x ≠ e ⇒ DISJOINT e x)
Proof
  rpt strip_tac
  (* It is sufficient to prove this only for e not in S. If e is in S, then
     we can apply the version of the theorem which only works for e not in S on
     e INSERT (S DELETE e) *)
  >> wlog_tac ‘e ∉ S’ [‘e’, ‘S’]
  >- (gvs[iffLR ABSORPTION]
      >> last_x_assum (qspecl_then [‘e’, ‘S DELETE e’] assume_tac)
      >> gvs[ELT_IN_DELETE]
      >> metis_tac[]
     )
  >> REVERSE EQ_TAC
  >- (disch_tac
      >> irule disjoint_insert
      >> metis_tac[DISJOINT_SYM]
     )
  >> gvs[disjoint_def]
QED

Theorem DISJOINT_RESTRICT_LL:
  ∀a1 a2 b1.
    DISJOINT a1 b1 ⇒ DISJOINT (a1 ∩ a2) b1
Proof
  rpt strip_tac
  >> gvs[DISJOINT_DEF]
  >> gvs[EXTENSION]
  >> metis_tac[]
QED

Theorem DISJOINT_RESTRICT_LR:
  ∀a1 a2 b1.
    DISJOINT a2 b1 ⇒ DISJOINT (a1 ∩ a2) b1
Proof
  metis_tac[DISJOINT_RESTRICT_LL, DISJOINT_SYM, INTER_COMM]
QED

Theorem DISJOINT_RESTRICT_RL:
  ∀a1 b1 b2.
    DISJOINT a1 b1 ⇒ DISJOINT a1 (b1 ∩ b2)
Proof
  metis_tac[DISJOINT_RESTRICT_LL, DISJOINT_SYM, INTER_COMM]
QED

Theorem DISJOINT_RESTRICT_RR:
  ∀a1 b1 b2.
    DISJOINT a1 b2 ⇒ DISJOINT a1 (b1 ∩ b2)
Proof
  metis_tac[DISJOINT_RESTRICT_LL, DISJOINT_SYM, INTER_COMM]
QED

Theorem FBIGUNION_IN_DELETE:
  ∀e S.
    FINITE S ∧
    disjoint_domains S ∧
    e ∈ S ⇒
    FBIGUNION S = e ⊌ FBIGUNION (S DELETE e)
Proof
  rpt strip_tac
  >> Q.SUBGOAL_THEN ‘S = e INSERT S DELETE e’
      (fn th => PURE_ONCE_REWRITE_TAC[th]) >- simp[]
  >> DEP_PURE_ONCE_REWRITE_TAC[FBIGUNION_INSERT]
  >> simp[]
QED

Theorem disjoint_image_iff:
  ∀f S.
    INJ f S 𝕌(:β -> bool) ⇒
    (disjoint (IMAGE f S) ⇔
       (∀i j. i ∈ S ∧ j ∈ S ∧ i ≠ j ⇒ DISJOINT (f i) (f j)))
Proof
  rpt strip_tac
  >> gvs[disjoint_def, pairwise]
  >> EQ_TAC >> rpt strip_tac >> gvs[]
  >- metis_tac[INJ_DEF]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* The generalised distributive law.                                          *)
(*                                                                            *)
(* The basic idea is Π Σ f = Σ Π f.                                           *)
(* - In the LHS, the sum depends only on the variables appropriate to the     *)
(*   current choice of f, whereas in the RHS, the sum depends on all          *)
(*   variables in any f.                                                      *)
(* - no two choices of f can involve the same variables.                      *)
(*                                                                            *)
(* The "f" at the end of "nsf", "excl_val_mapf" stands for "function"         *)
(*                                                                            *)
(* fg: the factor graph of nodes assignments we're summing over               *)
(* S: The set of we're taking the product over                                *)
(* ff: a function from an element of S to the corresponding choice of f in    *)
(*     this term of the product. This takes a mapping from only the variables *)
(*     in the corresponding nsf to values, and returns an extreal.            *)
(* nsf: a function from an element of S to the set of variables that are      *)
(*      relevant to this term of the product                                  *)
(* excl_val_mapf: a function from an element of S to a map of variables that  *)
(*                take a fixed value in this term of the product.             *)
(* -------------------------------------------------------------------------- *)
Theorem generalised_distributive_law:
  ∀fg S ff nsf excl_val_mapf.
    FINITE S ∧
    INJ nsf S 𝕌(:unit + num -> bool) ∧
    disjoint (IMAGE nsf S) ∧
    (∀k x.
       x ∈ val_map_assignments fg (nsf k) (excl_val_mapf k) ⇒
       ff k x ≠ +∞ ∧ ff k x ≠ −∞) ⇒
    ∏ (λk. ∑ (ff k) (val_map_assignments fg (nsf k) (excl_val_mapf k))) S
    = ∑ (λval_map.
           ∏ (λk.
                ff k (DRESTRICT val_map (nsf k))
             ) S
        ) (val_map_assignments
           fg
           (BIGUNION (IMAGE nsf S))
           (FBIGUNION (IMAGE (λk. DRESTRICT (excl_val_mapf k) (nsf k)) S))
          ) : extreal
Proof

  (* Rewrite so that FINITE S is our only assumption, so we can use induction *)
  rpt strip_tac
  >> NTAC 3 (pop_assum mp_tac)
  >> SPEC_ALL_TAC
  (* Perform induction *)
  >> Induct_on ‘S’ using FINITE_INDUCT
  >> rpt strip_tac
  (* Base case: S is empty *)
  >- gvs[]
  (* Reduce to smaller instance of product to allow inductive hypothesis to be
     applied *)
  >> gvs[EXTREAL_PROD_IMAGE_PROPERTY, DELETE_NON_ELEMENT_RWT]
  (* Ready the inductive hypothesis to be applied *)
  >> last_x_assum (qspecl_then [‘excl_val_mapf’, ‘ff’, ‘fg’, ‘nsf’] assume_tac)
  >> gvs[disjoint_insert_iff]
  >> gvs[INJ_INSERT]
  (* The inductive hypothesis has been applied, so get rid of it *)
  >> qpat_x_assum ‘∏ _ _ = ∑ (λval_map. ∏ _ _) _’ kall_tac
  (* Move one sum into the other, as a constant *)
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM EXTREAL_SUM_IMAGE_CMUL_L_ALT]
  >> conj_tac
  >- (rpt conj_tac
      >- gvs[]
      >- (gvs[]
          >> irule EXTREAL_SUM_IMAGE_NOT_POSINF
          >> gvs[])
      >- (gvs[]
          >> irule EXTREAL_SUM_IMAGE_NOT_NEGINF
          >> gvs[])
      >> disj1_tac
      >> gen_tac >> disch_tac >> simp[]
      >> irule (cj 1 EXTREAL_PROD_IMAGE_NOT_INFTY)
      >> simp[]
      >> qx_gen_tac ‘k’ >> disch_tac
      >> PURE_ONCE_REWRITE_TAC[CONJ_COMM]
      >> last_x_assum irule       
      >> irule drestrict_in_val_map_assignments
      >> qmatch_asmsub_abbrev_tac ‘val_map ∈ val_map_assignments fg ns1 excl_val_map1’
      >> qexistsl [‘excl_val_map1’, ‘ns1’] >> simp[Abbr ‘excl_val_map1’, Abbr ‘ns1’]
      >> REVERSE conj_tac
      >- (simp[BIGUNION_IMAGE, SUBSET_DEF]
          >> metis_tac[])
      >> DEP_PURE_ONCE_REWRITE_TAC[DRESTRICT_FBIGUNION]
      >> conj_tac
      >- (simp[]
          >> gvs[disjoint_domains_def, pairwise]
          >> rpt strip_tac
          >> gvs[FDOM_DRESTRICT]
          >> irule DISJOINT_RESTRICT_RR
          >> irule DISJOINT_RESTRICT_LR
          >> gvs[disjoint_def]
          >> Cases_on ‘k' = k''’ >> gvs[]
          >> ‘nsf k' ≠ nsf k''’ by metis_tac[INJ_DEF]
          >> last_x_assum irule
          >> simp[]
          >> metis_tac[]
         )
      >> gvs[IMAGE_IMAGE]
      >> gvs[o_DEF]
      >> Q.SUBGOAL_THEN ‘S = k INSERT S DELETE k’
          (fn th => PURE_ONCE_REWRITE_TAC[th]) >- simp[]
      >> simp[]
      >> DEP_PURE_ONCE_REWRITE_TAC[FBIGUNION_INSERT]
      >> conj_tac
      >- (simp[]
          >> Q.SUBGOAL_THEN ‘DRESTRICT (excl_val_mapf k) (nsf k) INSERT
                             IMAGE (λk'. DRESTRICT (excl_val_mapf k') (nsf k' ∩ nsf k))
                             (S DELETE k) =
                             IMAGE (λk'. DRESTRICT (excl_val_mapf k') (nsf k' ∩ nsf k))
                                  (k INSERT S DELETE k)’ (fn th => PURE_ONCE_REWRITE_TAC[th]) >- simp[]
          >> simp[disjoint_domains_def, pairwise, Excl "IN_INSERT"]
          >> rpt gen_tac >> rpt disch_tac
          >> gvs[FDOM_DRESTRICT]
          >> irule DISJOINT_RESTRICT_LR
          >> irule DISJOINT_RESTRICT_LL
          >> irule DISJOINT_RESTRICT_RR
          >> irule DISJOINT_RESTRICT_RL
          >> gvs[disjoint_image_iff]
          >> metis_tac[]
         )
      >> irule SUBMAP_FUNION
      >> disj1_tac
      >> gvs[]
     )

  (* Move the product into the inner sum, as a constant *)
  >> EXTREAL_SUM_IMAGE_CMUL_R_ALT

  (* Combine the composed sums together *)
  >> 
QED

(*Theorem generalised_distributive_law:
  ∀fg S ff nsf exclf excl_valf.
    INJ nsf S 𝕌(:unit + num -> bool) ∧
    pairwise DISJOINT (IMAGE nsf S) ⇒
    ∏ (λk.
         ∑ (λval_map.
              ff k val_map
           ) (val_map_assignments fg (nsf k) (exclf k) (excl_valf k))
      ) S
    = ∑ (λval_map.
           ∏ (λk.
                ff k val_map
             ) S
        ) (val_map_assignments fg (BIGUNION (IMAGE nsf S)) ARB ARB)
Proof
QED*)

(* -------------------------------------------------------------------------- *)
(* A message sent on the factor graph is the sum of products of all function  *)
(* nodes in that branch of the tree, with respect to all choices of variable  *)
(* nodes in that branch of the tree, where the variable node which is an      *)
(* endpoint of the message takes a specific value and must be included as a   *)
(* variable in that branch of the tree if it is not already because it is the *)
(* root from which the branch extends.                                        *)
(*                                                                            *)
(*       X: function node.   O: variable node                                 *)
(*                                                                            *)
(*         ...   X - - ...                                                    *)
(*        /     /                                                             *)
(*       X - - O - - X - - ...                                                *)
(*        \     \                                                             *)
(*         ...   X - - ...                                                    *)
(*                                                                            *)
(* The message arriving at the leftmost function node from the variable node  *)
(* in the middle will be equal to the sum of products of all function nodes   *)
(* in that middle subtree with respect to all choices of variable node        *)
(* values in that subtree, where the source variable node takes a specific    *)
(* value.                                                                     *)
(*                                                                            *)
(*         ...   O - - ...                                                    *)
(*        /     /                                                             *)
(*       O - - X - - O - - ...                                                *)
(*        \     \                                                             *)
(*         ...   O - - ...                                                    *)
(*                                                                            *)
(* The message arriving at the leftmost variable node from the function node  *)
(* in the middle will be equal to the sum of products of all function nodes   *)
(* in that middle subtree with respect to all choices of variable node values *)
(* in that subtree, plus the choice of the destination variable node which    *)
(* takes a specific value.                                                    *)
(*                                                                            *)
(* We can work by induction to prove this. In the base case, we have a leaf   *)
(* node, and want to prove that our proposition holds. In the inductive step, *)
(* we have a set of child trees for which the proposition holds, and want to  *)
(* prove that it holds for the new tree consisting of the parent node and all *)
(* its child nodes.                                                           *)
(* -------------------------------------------------------------------------- *)
Theorem sp_message_sum_prod:
  ∀fg src dst.
    sp_message fg src dst =
    if is_tree (get_underlying_graph fg) ∧
       adjacent (get_underlying_graph fg) src dst ∧
       src ≠ dst
    then
      let
        msg_var_node = if src ∈ var_nodes fg then src else dst;
        cur_subtree = subtree (get_underlying_graph fg) dst src;
        sum_prod_ns = nodes cur_subtree ∪ {msg_var_node};
      in
        sum_prod_map fg sum_prod_ns {msg_var_node}
    else
      FUN_FMAP (λdst_val_map. 0) (val_map_assignments fg ∅ FEMPTY)
Proof
  
  (* Simplify special case of invalid input to sp_message *)
  rpt strip_tac
  >> REVERSE $ Cases_on ‘is_tree (get_underlying_graph fg) ∧
                         adjacent (get_underlying_graph fg) src dst ∧
                         src ≠ dst’
  >- simp[Once sp_message_def]
  >> simp[]
  >> ‘src ∈ nodes (get_underlying_graph fg) ∧
      dst ∈ nodes (get_underlying_graph fg)’ by metis_tac[adjacent_members]
  >> simp[]
  (* Prepare for induction over the inductive structure of messages. Note that
     fg, src, and dst need to be in the correct order for HO_MATCH_MP_TAC to
     recognise our theorem as an instance of sp_message_ind *)
  >> rpt $ pop_assum mp_tac
  >> MAP_EVERY qid_spec_tac [‘dst’, ‘src’, ‘fg’] 
  >> HO_MATCH_MP_TAC sp_message_ind
  >> rpt strip_tac
  (* Our assumptions are the inductive hypotheses that tell us what the value
     is when the destination is the current source. The first one relates
     to the definition of sp_message in the case where it is being sent from
     a function node, while the second one relates to the case where it is
     being sent from a variable node. *)
  (* Expand out one step of the definition of sp_message so that I can use the
     inductive hypothesis on the prior messages being sent into the current
     message *)
  >> PURE_ONCE_REWRITE_TAC[sp_message_def]
  (* It's often useful to know that nodes adjacent to src have the opposite
     function_nodes/var_nodes status *)
  >> qspecl_then [‘fg’, ‘src’] assume_tac
                 adjacent_in_function_nodes_not_in_function_nodes
  (* Case split on whether or not our source node is a function node *)
  >> Cases_on ‘src ∈ get_function_nodes fg’
              
  >- (gvs[]
      (* For some reason, our inductive hypothesis requires that we  know that
         there exists a possible mapping from variables to values, so we
         construct a mapping and satisfy this precondition *)
      >> gvs[Cong IGNORE_EQ_CONG, val_map_assignments_def]
      >> qspecl_then [‘fg’, ‘src’] assume_tac exists_val_map >> gvs[]
      >> last_x_assum $ qspecl_then [‘val_map : unit + num |-> bool list’,
                                     ‘FEMPTY’]
                      assume_tac >> gvs[]
      >> qpat_x_assum ‘FDOM val_map = _’ kall_tac
      >> qpat_x_assum ‘∀m. _ ⇒ LENGTH (val_map ' _) = _’ kall_tac
      (* In order to apply our inductive hypothesis, we need to know that any
         node adjacent to src is not src *)
      >> sg ‘∀x. adjacent (get_underlying_graph fg) x src ⇒ (x ≠ src ⇔ T)’
      >- (rpt strip_tac
          >> EQ_TAC >> gvs[]
          >> metis_tac[adjacent_irrefl]
         )
      (* Use EXTREAL_SUM_IMAGE_CONG and EXTREAL_PROD_IMAGE_CONG to use the
         inductive hypothesis to rewrite our incoming messages *)
      >> gvs[Cong EXTREAL_SUM_IMAGE_CONG, Cong EXTREAL_PROD_IMAGE_CONG]
      (* We have used our inductive hypothesis and no longer need it *)
      >> qpat_x_assum ‘∀src'. _ ⇒ sp_message _ _ _ = _’ kall_tac
      (* Expand out the definition of sum_prob_map. In the RHS, this allows us
         to simplify a FUN_FMAP that is on the LHS and the RHS. In the LHS,
         expanding out sum_prod_map allows us to simplify out an instance of
         FUN_FMAP followed by FAPPLY *)
      >> gvs[sum_prod_map_def]
      >> gvs[FUN_FMAP_EQ_THM]
      >> rpt strip_tac
      (* Simplify if-statement. The condition always applies in this scenario.
         Since we have adjacent _ src instead of adjacent src _, we need to use
         adjacent_SYM *)
      >> gvs[Cong extreal_sum_image_val_map_assignments_cong,
             Cong EXTREAL_PROD_IMAGE_CONG, adjacent_SYM]
      (* Simplify FUN_FMAP followed by FAPPLY. In order to do this, we need to
         know that the argument is in the domain. *)
      >> sg ‘∀prev val_map.
               prev ∈ nodes (get_underlying_graph fg) ∧
               adjacent (get_underlying_graph fg) prev src ∧
               val_map ∈ val_map_assignments fg (adjacent_nodes fg src) excl_val_map ⇒
               DRESTRICT val_map {prev} ∈ val_map_assignments fg {prev} FEMPTY’
      >- (rpt strip_tac
          >> irule drestrict_in_val_map_assignments
          >> qexistsl [‘excl_val_map’, ‘adjacent_nodes fg src’]
          >> gvs[]
         )
      >> gvs[Cong EXTREAL_SUM_IMAGE_CONG,
             Cong EXTREAL_PROD_IMAGE_CONG,
             val_map_assignments_finite,
             cj 2 FUN_FMAP_DEF]
      >> qpat_x_assum ‘∀prev val_map. _ ∧ _ ⇒ DRESTRICT _ _ ∈ _’ kall_tac
      (* Expand out sum_prod on the left so that we can see the place where
         we'll have to use the generalised distributive law. *)
      >> gvs[Cong LHS_CONG, sum_prod_def]
            
            

      (* -------------------------------------------------------------------- *)
      (* Π Σ f S T                                                            *)
      (*                                                                      *)
      (*                                                                      *)
      (* -------------------------------------------------------------------- *)

      >>
      
      
     )
  >> gvs[]



  >> PURE_ONCE_REWRITE_TAC[sp_message_def]
  >> gvs[]
  (* Consider the case where the source is a function node *)
  >> Cases_on ‘src ∈ get_function_nodes fg’

  (* Any node that is adjacent to src is a variable node *)
  >> sg ‘∀prev. adjacent (get_underlying_graph fg) prev src ⇒
                prev ∈ var_nodes fg’
  >- (rpt strip_tac
      >> gvs[]
      >> conj_tac >- metis_tac[adjacent_members]
      >> metis_tac[adjacent_in_function_nodes_not_in_function_nodes]
     )
     
  >- (gvs[]
      >> gvs[sum_prod_def]
      >> gvs[FUN_FMAP_EQ_THM]
      >> rpt gen_tac >> rpt disch_tac
      (* The left hand side is the sum of products of the incoming messages,
         with respect to only those variable nodes that are immediately
         relevant to the current function node.
           The right hand side is the sum of products over all function nodes
         in the relevant subtree.
           We first aim to use the inductive hypothesis to simplify the incoming
           messages. *)
      >> qmatch_goalsub_abbrev_tac ‘_ = RHS’
      >> qabbrev_tac ‘EXAMPLE_VAL_MAP = ARB : unit + num |-> bool list’
      >> last_x_assum (qspec_then ‘EXAMPLE_VAL_MAP’ assume_tac)
      >> sg ‘(FDOM EXAMPLE_VAL_MAP = adjacent_nodes fg src ∧
              ∀n. n ∈ FDOM EXAMPLE_VAL_MAP ⇒ LENGTH (EXAMPLE_VAL_MAP ' n) =
                                             get_variable_length_map fg ' n)’
      >- cheat
      >> gvs[]
      >> pop_assum kall_tac
      >> qpat_x_assum ‘FDOM EXAMPLE_VAL_MAP = _’ kall_tac
      >> qpat_x_assum ‘Abbrev (EXAMPLE_VAL_MAP = _)’ kall_tac
      >> gvs[]
      (* Use EXTREAL_SUM_IMAGE_CONG and EXTREAL_PROD_IMAGE_CONG to use the
         inductive hypothesis to rewrite our incoming messages *)
      >> gvs[Cong EXTREAL_SUM_IMAGE_CONG, Cong EXTREAL_PROD_IMAGE_CONG]
      (* We've used an inductive hypothesis and we no longer need either of
         them *)
      >> NTAC 2 (pop_assum kall_tac)
      (* Simplify out the test that prev ≠ src when prev is adjacent to src *)
      >> sg ‘∀x. adjacent (get_underlying_graph fg) x src ⇒ (x ≠ src ⇔ T)’
      >- (rpt strip_tac
          >> EQ_TAC >> gvs[]
          >> metis_tac[adjacent_irrefl]
         )
      >> pop_assum (fn th => simp[th, Cong EXTREAL_SUM_IMAGE_CONG,
                                  Cong EXTREAL_PROD_IMAGE_CONG])
      (* Any node that is adjacent to src is a variable node *)
      >> sg ‘∀prev. adjacent (get_underlying_graph fg) prev src ⇒
                    prev ∈ var_nodes fg’
      >- (rpt strip_tac
          >> gvs[]
          >> conj_tac >- metis_tac[adjacent_members]
          >> metis_tac[adjacent_in_function_nodes_not_in_function_nodes]
         )
      (* Simplify FUN_FMAP f P ' x.
         Proving that P is finite is trivial in this scenario.
         It's less trivial to show that x ∈ P.
         After adding the proof above that any node adjacent to src was a
         variable node, that seemed to be enough to get this to work.
       *)
      >> gvs[cj 2 FUN_FMAP_DEF, Cong EXTREAL_SUM_IMAGE_CONG,
             Cong EXTREAL_PROD_IMAGE_CONG,
             length_n_codes_finite]
            
     )
(* Now consider the case where the source is a variable node rather than a
     function node *)
QED

(* -------------------------------------------------------------------------- *)
(* The message passing algorithm gives us the same result as summing over the *)
(* product of the terms in the factor graph                                   *)
(* -------------------------------------------------------------------------- *)
Theorem sp_message_final_result:
  TODO_FINAL_RESULT = TODO_FINAL_RESULT
Proof
  cheat
QED

(* -------------------------------------------------------------------------- *)
(* This overload is useful for my purposes, but it may overlap with the more  *)
(* general concept of "the set of all pairs of adjacent nodes" in a scenario  *)
(* where we aren't working with the message passing algorithm, so I hide it   *)
(* before exporting the theory.                                               *)
(* -------------------------------------------------------------------------- *)
val _ = hide "message_domain"
