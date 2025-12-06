Theory message_passing

Ancestors arithmetic bool ecc_prob_space extreal factor_graph finite_map fsgraph fundamental genericGraph hyperbolic_functions integer list  lifting partite_ea probability pred_set prim_rec transc transfer tree

Libs donotexpandLib dep_rewrite ConseqConv simpLib liftLib transferLib;

val _ = augment_srw_ss [rewrites[FDOM_FMAP, FUN_FMAP_DEF]];

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
(* vals: a finite map from nodes to values. val_map is the same as vals on    *)
(*       these nodes. We expect that these values have the appropriate        *)
(*       lengths                                                              *)
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
(* Calculate the message according to the message passing algorithm over the  *)
(* factor graph.                                                              *)
(*                                                                            *)
(* To ensure termination, this only returns a sensible result if the factor   *)
(* graph we are working on is a tree. If it is not a tree, we return the map  *)
(* which always returns 0.                                                    *)
(*                                                                            *)
(* TODO: is it possible to remove the if-statements that are only added       *)
(*       because the termination proof doesn't recognise that certain         *)
(*       variables satisfy certain properties? Specifically, it doesn't       *)
(*       recognise that, for example,  Σ f S means that every input given to  *)
(*       f is in S.                                                           *)
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

Theorem finite_inter_var_nodes[simp]:
  ∀ns fg.
    FINITE (ns ∩ var_nodes fg)
Proof
  metis_tac[INTER_FINITE, INTER_COMM, var_nodes_finite]
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
  >> gvs[]
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

(* -------------------------------------------------------------------------- *)
(* The generalised distributive law.                                          *)
(*                                                                            *)
(* Σ over sets Σ                                                              *)
(*                                                                            *)
(*                                                                            *)
(* Richardson and Urbanke write this as something along the lines of          *)
(* Σ_~z Π_k=1^K g_k(z, ...) = Π_k=1^K Σ_~z g_k(z, ...), where the variables   *)
(* in each g_k are distinct, except for z.                                    *)
(*                                                                            *)
(* But HOL4 has no concept of a named variable, such as "x", "y", or "z", so  *)
(* it's not straightforward to sum out a function over a particular variable. *)
(* Rather, the arguments to a function are provided in a particular order.    *)
(*                                                                            *)
(* Thus, I use an alternative, more general representation of the generalised *)
(* distributive law.                                                          *)
(*                                                                            *)
(* Again, the basic idea is Σ Π f = Π Σ f, where the things being summed over *)
(* for one choice of f have no effect for any other choice of f.              *)
(*                                                                            *)
(* We split the sum up so that when it                                        *)
(*                                                                            *)
(*                                                                            *)
(* If we are taking a sum over a set of sets, over a sum over the current     *)
(* choice of set, over a product, then this is equivalent                     *)
(*                                                                            *)

(* -------------------------------------------------------------------------- *)
(*Theorem generalised_distributive_law:
  ∀f S' T.
    ∑ (λS. ∑ (λx. ∏ (λy. f x y) T) S) S' = ∏ (λy. ∑ (λx. f x y) (S' y)) T : extreal
Proof
  rpt strip_tac
  >> 
QED

∑ (λx. ∏ (λy. f x y) T) S = ∏ (λy. ∑ (λx. f x y) S) T : extreal
 *)

(* -------------------------------------------------------------------------- *)
(* Π Σ f = Σ Π f                                                              *)
(* where the variables summed over by the sums are disjoint, and the values   *)
(* of each function only depend on the variables in the corresponding sum.    *)
(*                                                                            *)
(* The "f" at the end of "nsf", "exclf", "excl_valf" stands for "function"    *)
(* -------------------------------------------------------------------------- *)
Theorem generalised_distributive_law:
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
        sum_prod_map fg sum_prod_ns msg_var_node
    else
      FUN_FMAP (λdst_val. 0) (length_n_codes 0)
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
      >> last_x_assum $ qspecl_then [‘val_map : unit + num |-> bool list’]
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
      >> gvs[val_map_assignments_def]
      >> gvs[Cong EXTREAL_SUM_IMAGE_CONG, Cong EXTREAL_PROD_IMAGE_CONG,
             adjacent_SYM]
      (* Unexpand val_map_assignments to make it easier to read *)
      >> qspecl_then [‘fg’, ‘adjacent_nodes fg src’, ‘dst’, ‘excl_var_node_val’]
                     assume_tac (GSYM val_map_assignments_def)
      >> gvs[]
      >> qpat_x_assum ‘_ = val_map_assignments _ _ _ _’ kall_tac
      (* *)
      >> gvs[Cong LHS_CONG, sum_prod_def]

      
     )




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
