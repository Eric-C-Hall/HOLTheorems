Theory factor_graph

Ancestors arithmetic bool ecc_prob_space probability fsgraph fundamental genericGraph pred_set finite_map list transc prim_rec integer partite_ea hyperbolic_functions lifting transfer words

Libs donotexpandLib wordsLib dep_rewrite ConseqConv simpLib liftLib transferLib;

val _ = hide "S";

val _ = augment_srw_ss [rewrites[fsgedges_addNode,
                                 FDOM_FMAP
                                ]
                       ];

(* -------------------------------------------------------------------------- *)
(* This is largely based on "Modern Coding Theory" by Tom Richardson and      *)
(* Rüdiger Urbanke.                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* This file defines factor graphs, which are used to efficiently calculate   *)
(* marginal probabilities.                                                    *)
(*                                                                            *)
(* Factor graphs can be used to implement the BCJR algorithm, which can be    *)
(* used to decode convolutional codes. This is of particular importance in    *)
(* decoding turbo codes.                                                      *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Factor Graph Datatype:                                                     *)
(*                                                                            *)
(* underlying_graph represents the underlying factor graph, as an fsgraph.    *)
(* The nodes have labels which are consecutive natural numbers starting from  *)
(* 0.                                                                         *)
(*                                                                            *)
(* function_nodes is the set of all nodes which represent function nodes.     *)
(* Our graph is bipartite between function nodes and variable nodes.          *)
(*                                                                            *)
(* Variable nodes represent variables that can take an n-bit value,           *)
(* represented as a bool list (I considered using a β word, but that would    *)
(* require all variables to be the same length, but in the BCJR algorithm, we *)
(* want some variables to be length 1 and some variables to be length l)      *)
(*                                                                            *)
(* variable_length_map maps a variable node to the number of bits in the values   *)
(* it can take. For example, a variable node with length 3 could take the     *)
(* value [1; 0; 0] or the value [1; 1; 1], etc.                               *)
(*                                                                            *)
(* function_map maps a function node to its function. The function takes the  *)
(* values associated with each of the input variables (represented as a       *)
(* finite map from the labels of the input variables to the values they take) *)
(* and outputs an α.                                                          *)
(* -------------------------------------------------------------------------- *)
Datatype:
  factor_graph_rep = 
  <|
    underlying_graph : fsgraph;
    function_nodes : (unit + num) -> bool;
    variable_length_map: (unit + num) |-> num;
    function_map : (unit + num) |-> (unit + num |-> bool list) |-> α
  |>
End

(* -------------------------------------------------------------------------- *)
(* TODO: These overloads are perhaps legacy: now we should perhaps use the    *)
(*       equivalent overloads for the abstract type version of factor graphs  *)
(* -------------------------------------------------------------------------- *)
Overload adjacent_nodes = “λfg cur_node.
                             {adj_node |
                             adj_node ∈ nodes fg.underlying_graph ∧
                             adjacent fg.underlying_graph adj_node cur_node }”;

Overload var_nodes = “λfg. {n | n ∈ nodes fg.underlying_graph ∧
                                n ∉ fg.function_nodes}”;

Theorem var_nodes_finite[simp]:
  ∀fg.
    FINITE (var_nodes fg)
Proof
  rpt strip_tac
  >> ‘var_nodes fg ⊆ nodes fg.underlying_graph’ by ASM_SET_TAC[]
  >> metis_tac[SUBSET_FINITE, FINITE_nodes]
QED

(* -------------------------------------------------------------------------- *)
(* All possible assignments to the variables adjacent to a node               *)
(*                                                                            *)
(* assign_nodes: a list of nodes that we are assigning values                 *)
(* assign_lengths: a map from nodes to variable lengths: must contain at      *)
(*                 least all nodes in assign_nodes. fg.variable_length_map is *)
(*                 a possible candidate for this argument.                    *)
(*                                                                            *)
(* Returns: a set of all possible finite maps that assign the given nodes to  *)
(*          values of the given lengths                                       *)
(*                                                                            *)
(* We require the type that is being assigned to the variables to be          *)
(*   bool list: we could allow more general types, but restricting to bool    *)
(*   list ensures that we have only finitely many assignments.                *)
(* -------------------------------------------------------------------------- *)
Definition var_assignments_def:
  var_assignments assign_nodes assign_lengths =
  {val_map | FDOM val_map = assign_nodes ∧
             (∀m. m ∈ FDOM val_map ⇒
                  LENGTH (val_map ' m : bool list) = assign_lengths ' m)
                   }
End

Theorem var_assignments_finite[simp]:
  ∀assign_nodes assign_lengths.
    FINITE assign_nodes ⇒ FINITE (var_assignments assign_nodes assign_lengths)
Proof
  rpt strip_tac
  >> Induct_on ‘assign_nodes’ using FINITE_INDUCT
  >> gvs[var_assignments_def]
  >> conj_tac
  (* Base case *)
  >- (qmatch_abbrev_tac ‘FINITE S’
      >> sg ‘S = {FEMPTY}’
      >- (rw[EXTENSION]
          >> unabbrev_all_tac >> EQ_TAC >> gvs[] >> rpt strip_tac
          >> gvs[FDOM_EQ_EMPTY]
         )
      >> gvs[]
     )
  (* Inductive step *)
  >> rpt strip_tac
  >> qmatch_asmsub_abbrev_tac ‘FINITE S_hyp’
  >> qmatch_abbrev_tac ‘FINITE S_ind’
  (* Split this set up into sets depeding on what value is taken at e. Since
     there are only finitely many of them, and they each have the same size as
     the inductive hypothesis, which is finite, this means that the ultimate
     result must be finite. *)
  >> qsuff_tac ‘S_ind = BIGUNION
                        (IMAGE (λval. IMAGE (λval_map. val_map |+ (e, val)) S_hyp)
                               {val | LENGTH val = assign_lengths ' e})’
  >- (rpt strip_tac
      >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> irule FINITE_BIGUNION
      >> conj_tac
      (* Each set we have split up into is finite *)
      >- (rpt strip_tac >> gvs[])
      (* We have split up into a finite number of sets in total*)
      >> irule IMAGE_FINITE
      >> gvs[]
     )
  (* This is a union of intersections, where a given set in the union is S_ind 
     intersected with the maps that take the value val at e. Thus, we try to
     go towards a form that can be simplified using INTER_BIGUNION *) 
  >> qsuff_tac ‘∀val.
                  LENGTH val = assign_lengths ' e ⇒
                  IMAGE (λval_map. val_map |+ (e,val)) S_hyp =
                  S_ind ∩ {val_map | val_map ' e = val}’
  >- (rpt strip_tac
      >> Q.SUBGOAL_THEN
          ‘IMAGE (λval. IMAGE (λval_map. val_map |+ (e,val)) S_hyp)
           (length_n_codes (assign_lengths ' e))
           = IMAGE (λval. S_ind ∩ {val_map | val_map ' e = val})
                   (length_n_codes (assign_lengths ' e))’
          (fn th => PURE_ONCE_REWRITE_TAC[th])
      >- (irule IMAGE_CHANGE_FUN
          >> rpt strip_tac
          >> gvs[]
         )
      >> simp[]
      >> simp[BIGUNION_IMAGE_INTER]
      >> qmatch_abbrev_tac ‘S_ind = S_ind ∩ BIGUNION (IMAGE f S)’
      >> Q.SUBGOAL_THEN ‘BIGUNION (IMAGE f S) =
                         {val_map | LENGTH (val_map ' e) = assign_lengths ' e}’
          (fn th => PURE_ONCE_REWRITE_TAC[th])
      >- (rw[EXTENSION]
          >> EQ_TAC >> rw[] >> gvs[]
          >- (unabbrev_all_tac >> gvs[IN_DEF])
          >> unabbrev_all_tac
          >> qexists ‘{val_map | val_map ' e = x ' e}’ >> gvs[]
          >> qexists ‘x ' e’ >> gvs[]
         )
      >> rw[EXTENSION]
      >> EQ_TAC >> gvs[]
      >> rpt strip_tac
      >> unabbrev_all_tac >> gvs[]
     )
  (* Prove that adding a mapping from e to val to every val_map in a bunch of
     nodes excluding e is equivalent to restricting the set of all choices of
     val_map in the nodes including e to just those which map e to val *)
  >> qx_gen_tac ‘val’ >> disch_tac
  >> simp[EXTENSION]
  >> qx_gen_tac ‘cur_map’
  >> EQ_TAC
  (* If the current map is in the set obtained by adding a mapping from e to
     val, then it is in the set obtained by restricting to mappings which map e
     to val *)
  >- (rpt strip_tac
      >> simp[Abbr ‘S_hyp’, Abbr ‘S_ind’]
      >> pop_assum (fn th => assume_tac (REWRITE_RULE [IN_DEF] th)) >> gvs[]
      >> qx_gen_tac ‘cur_node’ >> disch_tac
      >> gvs[]
      >> gvs[FAPPLY_FUPDATE_THM]
      >> rw[]
      >> ASM_SET_TAC[]
     )
  (* If the current map is in the set obtained by restricting to mappings
     which map e to val, then it is in the set obtained by adding a mapping
     from e to val *)
  >> rpt strip_tac
  >> qexists ‘DRESTRICT cur_map assign_nodes’
  >> REVERSE conj_tac
  >- (unabbrev_all_tac >> gvs[FDOM_DRESTRICT]
      >> conj_tac
      >- ASM_SET_TAC[]
      >> rpt strip_tac
      >> gvs[DRESTRICT_DEF]
     )
  >> unabbrev_all_tac >> gvs[]
  >> gvs[fmap_EXT]
  >> conj_tac
  >- (gvs[FDOM_DRESTRICT] >> ASM_SET_TAC[])
  >> qx_gen_tac ‘cur_node’
  >> rpt strip_tac
  >- gvs[]
  >> gvs[FAPPLY_FUPDATE_THM]
  >> rw[]
  >> gvs[DRESTRICT_DEF]
QED

(* -------------------------------------------------------------------------- *)
(* A special case of var_assignments_finite where we have                     *)
(* assign_nodes ⊆ var_nodes fg and we have                                   *)
(* assign_lengths = fg.variable_length_map. If we just used                   *)
(* var_assignments_finite, this wouldn't be automatically recognised by the   *)
(* simplifier because to determine FINITE inputs, we would need to use the    *)
(* fact that FINITE S /\ inputs SUBSET S implies FINITE inputs, but this      *)
(* would require choosing an S which the simplifier cannot do. However, this  *)
(* version of the theorem can be used by the simplifier.                      *)
(* -------------------------------------------------------------------------- *)
Theorem var_assignments_finite_subset_var_nodes[simp]:
  ∀fg assign_nodes.
    assign_nodes ⊆ var_nodes fg ⇒
    FINITE (var_assignments assign_nodes fg.variable_length_map)
Proof
  rpt strip_tac
  >> irule var_assignments_finite
  >> irule SUBSET_FINITE
  >> qexists ‘var_nodes fg’
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* Well-formedness of a factor graph.                                         *)
(*                                                                            *)
(* Used to create an abstract factor_graph type based on the underlying       *)
(* factor_graph_rep representation. A factor_graph is a factor_graph_rep      *)
(* which satisfies the well-formedness properties.                            *)
(*                                                                            *)
(* - the underlying graph should be bipartite with respect to the function    *)
(*   nodes and variable nodes                                                 *)
(* - the domain of variable_length_map should be the set of variable nodes    *)
(*   (i.e. nodes that are not function nodes)                                 *)
(* - the domain of function_map should be the set of function nodes           *)
(* - After applying function_map, the domain of the new map is the set of     *)
(*   all maps which have a domain equal to the adjacent nodes and each output *)
(*   has an appropriate length as per the variable length of that node.       *)
(* - the nodes should be the consecutive natural numbers starting from 0      *)
(* -------------------------------------------------------------------------- *)
Definition wffactor_graph_def:
  wffactor_graph (fg : α factor_graph_rep) ⇔
    (gen_bipartite_ea fg.underlying_graph fg.function_nodes) ∧
    FDOM fg.variable_length_map = var_nodes fg ∧
    FDOM fg.function_map = fg.function_nodes ∧
    (∀n. n ∈ FDOM fg.function_map ⇒
         FDOM (fg.function_map ' n) = var_assignments
                                      (adjacent_nodes fg n)
                                      (fg.variable_length_map)
    ) ∧
    nodes fg.underlying_graph = {INR i | i < order fg.underlying_graph}
End

(* -------------------------------------------------------------------------- *)
(* Simplify INR x ∈ nodes fg.underlying_graph                                *)
(* -------------------------------------------------------------------------- *)
Theorem inr_in_nodes_underlying_graph[simp]:
  ∀fg x.
    wffactor_graph fg ⇒
    (INR x ∈ nodes fg.underlying_graph ⇔ x < CARD (nodes fg.underlying_graph))
Proof
  rpt strip_tac
  >> gvs[wffactor_graph_def, genericGraphTheory.gsize_def]
  >> first_assum (fn th => PURE_REWRITE_TAC[Once th])
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Applying an updated version of function_map to a function from the         *)
(* unupdated version of function_map will provide the same result as applying *)
(* the unupdated version                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem fupdate_function_map[simp]:
  ∀fg f x.
    wffactor_graph fg ∧
    f ∈ nodes fg.underlying_graph ⇒
    (fg.function_map |+ (INR (CARD (nodes fg.underlying_graph)), x)) ' f =
    fg.function_map ' f
Proof
  rw[]
  >> irule NOT_EQ_FAPPLY
  >> rpt strip_tac
  >> gvs[]
  >> gvs[inr_in_nodes_underlying_graph]
QED

(* -------------------------------------------------------------------------- *)
(* The next few theorems explore the properties of {INR i | i ∈ count n},    *)
(* which can equivalently be described as {INR i | i < n}                     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Fundamental inductive method used to produce a set of this form.           *)
(* This allows us to work by induction on this set.                           *)
(* -------------------------------------------------------------------------- *)
Theorem INR_COMP_SUC:
  ∀n : num.
    {INR i | i < SUC n} = (INR n) INSERT {INR i | i < n}
Proof
  rpt strip_tac
  >> gvs[EXTENSION]
  >> rpt strip_tac
  >> Cases_on ‘x’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Automatically simplify when inserting a node into the underlying graph     *)
(* for a well-formed factor graph (as the node sets of well-formed factor     *)
(* graphs have this form                                                      *)
(*                                                                            *)
(* Note: similar to INR_COMP_SUC. I wrote these independently. I used one in  *)
(* one direction and the other in the other direction, and added one with the *)
(* [simp] attribute                                                           *)
(* -------------------------------------------------------------------------- *)
Theorem inr_comprehension_suc[simp]:
  ∀fg.
    wffactor_graph fg ⇒
    INR (CARD (nodes fg.underlying_graph)) INSERT
        {INR i | i < CARD (nodes fg.underlying_graph)} =
                 {INR i | i < SUC (CARD (nodes fg.underlying_graph))}
Proof
  rpt strip_tac
  >> gvs[EXTENSION]
  >> rw[]
  >> Cases_on ‘x’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Any edge is a finite set                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem finite_in_fsgedges:
  ∀g e.
    e ∈ fsgedges g ⇒ FINITE e
Proof
  rpt strip_tac
  >> gvs[fsgedges_def]
QED

(* -------------------------------------------------------------------------- *)
(* In order to associate a finite cardinality with this set, we first need to *)
(* know that it's finite.                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem FINITE_INR_COMP[simp]:
  ∀n : num.
    FINITE {INR i | i < n}
Proof
  rpt strip_tac
  >> Induct_on ‘n’ >> gvs[]
  >> gvs[INR_COMP_SUC]
QED

(* -------------------------------------------------------------------------- *)
(* Useful for simplification in fg_add_variable_node_wf                       *)
(* -------------------------------------------------------------------------- *)
Theorem CARD_INR_COMP[simp]:
  ∀n.
    CARD {INR i | i < n} = n
Proof
  rpt strip_tac >> gvs[]
  >> Induct_on ‘n’ >> gvs[]
  >> gvs[INR_COMP_SUC]
QED

(* -------------------------------------------------------------------------- *)
(* The empty factor_graph_rep object.                                         *)
(* -------------------------------------------------------------------------- *)
Definition fg_empty0_def:
  fg_empty0 : α factor_graph_rep =
  <|
    underlying_graph := emptyG;
    function_nodes := ∅;
    variable_length_map := FEMPTY;
    function_map := FEMPTY;
  |>
End

(* -------------------------------------------------------------------------- *)
(* The empty factor graph is well-formed                                      *)
(* -------------------------------------------------------------------------- *)
Theorem fg_empty_wf[simp]:
  wffactor_graph fg_empty0
Proof
  gvs[fg_empty0_def, wffactor_graph_def]
QED

(* -------------------------------------------------------------------------- *)
(* There exists at least one well-formed object of type factor_graph_rep.     *)
(*                                                                            *)
(* We need this in order to generate the abstract factor_graph type as a      *)
(* well-formed object of type factor_graph_rep                                *)
(* -------------------------------------------------------------------------- *)
Theorem factor_graphs_exist[local]:
  ∃fg. wffactor_graph fg
Proof
  qexists ‘fg_empty0’
  >> gvs[]
QED

val tydefrec = newtypeTools.rich_new_type { tyname = "factor_graph",
exthm  = factor_graphs_exist,
ABS = "factor_graph_ABS",
REP = "factor_graph_REP"};

(* -------------------------------------------------------------------------- *)
(* Defines the equivalence class of graphs that are equivalent to a           *)
(* well-formed graph, in this instance, we use ordinary equality.             *)
(*                                                                            *)
(* The above comment may be inaccurate: I'm not entirely confident how to use *)
(* the "lifting" code. My understanding is that we are essentially using      *)
(* "modulo" to create a congruence class, but in this case, the congruence    *)
(* class has exactly 1 element, so all of the elements without a congruence   *)
(* class are discarded and cannot be accessed in the abstract type.           *)
(* It's largely based on the code used by genericGraphScript.                 *)
(* -------------------------------------------------------------------------- *)
Definition fgequiv_def:
  fgequiv fg1 fg2 ⇔ fg1 = fg2 ∧ wffactor_graph fg2
End

(* -------------------------------------------------------------------------- *)
(* A relation which relates a well-formed representative of a factor graph to *)
(* its corresponding abstract value.                                          *)
(* -------------------------------------------------------------------------- *)
Definition fg_AR_def:
  fg_AR r a ⇔ wffactor_graph r ∧ r = factor_graph_REP a
End

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem wfgraph_relates[transfer_rule]:
  (fg_AR ===> (=)) wffactor_graph (K T)
Proof
  simp[FUN_REL_def, fg_AR_def]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem AReq_relates[transfer_rule]:
  (fg_AR ===> fg_AR ===> (=)) (=) (=)
Proof
  simp[fg_AR_def, FUN_REL_def, #termP_term_REP tydefrec, #term_REP_11 tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* A proof that fg_empty0 is equivalent to itself when considered as a member *)
(* of the well-formed members of the representative class, and thus it can be *)
(* lifted to become a member of the abstract type factor_graph                *)
(* (My understanding of lifting is limited)                                   *)
(* -------------------------------------------------------------------------- *)
Theorem fg_empty0_respects:
  fgequiv fg_empty0 fg_empty0
Proof
  simp[fgequiv_def]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem right_unique_fg_AR[transfer_simp]:
  right_unique fg_AR
Proof
  simp[right_unique_def, fg_AR_def, #term_REP_11 tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem surj_fg_AR[transfer_simp]:
  surj fg_AR
Proof
  simp[surj_def, fg_AR_def, #termP_term_REP tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem RDOM_AR[transfer_simp]:
  RDOM fg_AR = {gr | wffactor_graph gr}
Proof
  simp[relationTheory.RDOM_DEF, Once FUN_EQ_THM, fg_AR_def, SF CONJ_ss,
       #termP_term_REP tydefrec] >>
  metis_tac[#termP_term_REP tydefrec, #repabs_pseudo_id tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Not sure what this does, copy/pasted and modified from genericGraphScript  *)
(* -------------------------------------------------------------------------- *)
Theorem Qt_graphs[liftQt]:
  Qt fgequiv factor_graph_ABS factor_graph_REP fg_AR
Proof
  simp[Qt_alt, fg_AR_def, #absrep_id tydefrec, fgequiv_def, #termP_term_REP tydefrec]>>
  simp[SF CONJ_ss, #term_ABS_pseudo11 tydefrec] >>
  simp[SF CONJ_ss, FUN_EQ_THM, fg_AR_def, #termP_term_REP tydefrec,
       CONJ_COMM] >>
  simp[EQ_IMP_THM, #termP_term_REP tydefrec, #absrep_id tydefrec,
       #repabs_pseudo_id tydefrec]
QED

(* -------------------------------------------------------------------------- *)
(* Many of the theorems above were copy/pasted to get this to work.           *)
(* -------------------------------------------------------------------------- *)
val _ = liftdef fg_empty0_respects "fg_empty"

(* -------------------------------------------------------------------------- *)
(* Add a variable node with length l to the factor_graph.                     *)
(*                                                                            *)
(* The first node added (variable or function) should be 0, the next node     *)
(* should be 1, etc.                                                          *)
(*                                                                            *)
(* fg is the final argument to allow for easy composition.                    *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_variable_node0_def:
  fg_add_variable_node0 l fg =
  let
    new_node = (INR (CARD (nodes fg.underlying_graph)))
  in
    fg with
       <|
         underlying_graph updated_by (fsgAddNode new_node);
         variable_length_map updated_by (λf. FUPDATE f (new_node, l))
       |>
End

(* -------------------------------------------------------------------------- *)
(* Simplify order applied to a factor graph with a node added.                *)
(* -------------------------------------------------------------------------- *)
Theorem order_fsgAddNode:
  ∀n fg.
    order (fsgAddNode n fg) = order (fg) + (if n ∈ nodes fg then 0 else 1)
Proof
  rpt strip_tac
  >> gvs[gsize_def]
  >> rw[]
QED

(* -------------------------------------------------------------------------- *)
(* In a well-formed graph, anything labelled as a function node is a node in  *)
(* the underlying graph                                                       *)
(* -------------------------------------------------------------------------- *)
Theorem in_function_nodes_in_nodes_underlying_graph:
  ∀fg n.
    wffactor_graph fg ∧
    n ∈ fg.function_nodes ⇒
    n ∈ nodes (fg.underlying_graph)
Proof
  rpt strip_tac
  >> gvs[wffactor_graph_def, gen_bipartite_ea_def, SUBSET_DEF]
QED

(* -------------------------------------------------------------------------- *)
(* In a well-formed factor graph, the function nodes are a subset of the      *)
(* nodes                                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem function_nodes_subset_nodes:
  ∀fg.
    wffactor_graph fg ⇒
    fg.function_nodes ⊆ nodes (fg.underlying_graph)
Proof
  rpt strip_tac
  >> gvs[wffactor_graph_def]
  >> gvs[gen_bipartite_ea_def]
QED

(* -------------------------------------------------------------------------- *)
(* Statements of this form come up reasonably regularly                       *)
(*                                                                            *)
(* A combination of the fact that this is not a valid node, with the fact     *)
(* that function nodes are a subset of nodes. A little inefficient to have to *)
(* write a theorem to express this idea.                                      *)
(* -------------------------------------------------------------------------- *)
Theorem inr_card_not_in_function_nodes[simp]:
  ∀fg.
    wffactor_graph fg ⇒
    INR (CARD (nodes fg.underlying_graph)) ∉ fg.function_nodes
Proof
  rpt strip_tac
  >> drule function_nodes_subset_nodes >> disch_tac
  >> gvs[SUBSET_DEF]
  >> first_assum drule >> disch_tac
  >> gvs[inr_in_nodes_underlying_graph]
QED

(* -------------------------------------------------------------------------- *)
(* A newly added node is not in the function nodes of the graph before the    *)
(* node was added.                                                            *)
(*                                                                            *)
(* This version of this theorem works even when wffactor_graph has been       *)
(* expanded out.                                                              *)
(* -------------------------------------------------------------------------- *)
Theorem inr_card_not_in_function_nodes_expanded_wffactor_graph[simp]:
  ∀fg n.
    gen_bipartite_ea fg.underlying_graph fg.function_nodes ∧
    (nodes fg.underlying_graph = {INR i | i < n}) ⇒
    INR n ∉ fg.function_nodes                                    
Proof
  rpt strip_tac
  >> gvs[gen_bipartite_ea_def]
  >> gvs[SUBSET_DEF]
  >> last_x_assum drule
  >> rpt strip_tac
  >> ‘n = i’ by gvs[]
  >> gvs[]
QED

Theorem newly_added_not_adjacent[simp]:
  ∀fg n.
    wffactor_graph fg ⇒
    ¬adjacent fg.underlying_graph (INR (CARD (nodes fg.underlying_graph))) n ∧
    ¬adjacent fg.underlying_graph n (INR (CARD (nodes fg.underlying_graph)))
Proof
  rpt strip_tac
  >> (‘INR (CARD (nodes fg.underlying_graph)) ∉
       nodes fg.underlying_graph’ by gvs[]
      >> metis_tac[adjacent_members])
QED
        
(* -------------------------------------------------------------------------- *)
(* Adding a variable node maintains well-formedness                           *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_variable_node0_wf:
  ∀fg l.
    wffactor_graph fg ⇒
    wffactor_graph (fg_add_variable_node0 l fg)
Proof
  rpt strip_tac
  >> simp[wffactor_graph_def, fg_add_variable_node0_def]
  (* Prove each property of well-formedness one at a time *)
  >> rpt conj_tac
  (* Bipartite *)
  >- (gvs[gen_bipartite_ea_fsgAddNode]
      >> rw[inr_in_nodes_underlying_graph]
      >> metis_tac[DELETE_NON_ELEMENT_RWT,
                   inr_card_not_in_function_nodes,
                   wffactor_graph_def]
     )
  (* Valid domain of variable length map *)
  >- (gvs[EXTENSION] >> rpt strip_tac
      >> EQ_TAC >> rpt strip_tac >> gvs[wffactor_graph_def])
  (* Valid domain of function map *)
  >- gvs[wffactor_graph_def]
  (* Valid domain of map mapped to by function map *)
  >- (rpt strip_tac
      (* Use corresponding property of the original graph *)
      >> drule_then (fn th => gvs[th]) (cj 4 (iffLR wffactor_graph_def))
      (* This code was written before var_assignments was defined, so
         expand var_assignments out *)
      >> gvs[var_assignments_def]
      (* The left hand side and right hand side are mostly the same: we just
         need to show equivalence in the places where they differ. *)
      >> simp[EXTENSION] >> rpt strip_tac
      >> qmatch_goalsub_abbrev_tac ‘b_prev1 ∧ b_prev2 ⇔ b_new1 ∧ b_new2’
      (* Split up into showing the equivalence of the individual properties.
         The second property is easier to work with if we already know the
         first property. *)
      >> ‘(b_prev1 ⇔ b_new1) ∧
          (b_prev1 ∧ b_new1 ⇒ (b_prev2 ⇔ b_new2))’ suffices_by metis_tac[]
      (* Prove first property: *)
      >> conj_tac >> unabbrev_all_tac
      >- (‘∀x. x = INR (CARD (nodes fg.underlying_graph)) ⇒
               ¬adjacent fg.underlying_graph x n’ suffices_by metis_tac[]
          >> simp[newly_added_not_adjacent]
         )
      (* Prove second property *)
      >> rpt strip_tac
      >> qmatch_goalsub_abbrev_tac ‘fg.variable_length_map |+ new_pair’
      >> ‘∀m. m ∈ FDOM x ⇒ (fg.variable_length_map |+ new_pair) ' m =
                           fg.variable_length_map ' m’ suffices_by gvs[]
      >> unabbrev_all_tac >> rpt strip_tac
      >> gvs[FAPPLY_FUPDATE_THM]
      >> rw[]
      (* New node cannot be adjacent to n *)
      >> metis_tac[newly_added_not_adjacent]
     )
  (* The set of nodes is the set of consecutive natural numbers starting from
     zero. *)
  >- (drule_then (fn th => PURE_REWRITE_TAC[th])
                 (cj 5 (iffLR wffactor_graph_def))
      >> gvs[order_fsgAddNode]
      >> rw[]
      >- gvs[wffactor_graph_def]
      >> gvs[EXTENSION] >> rpt strip_tac >> EQ_TAC >> rpt strip_tac >> gvs[]
     )
QED

(* -------------------------------------------------------------------------- *)
(* A proof that if the inputs are equivalent as factor graphs, then the       *)
(* outputs are also equivalent as factor graphs, and thus we can lift         *)
(* fg_add_variable_node to our abstract type                                  *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_variable_node0_respects:
  ((=) ===> fgequiv ===> fgequiv) fg_add_variable_node0 fg_add_variable_node0
Proof
  rpt strip_tac
  >> gvs[FUN_REL_def]
  >> gvs[fgequiv_def]
  >> gvs[fg_add_variable_node0_wf]
QED

val _ = liftdef fg_add_variable_node0_respects "fg_add_variable_node"

(* -------------------------------------------------------------------------- *)
(* Adds n variable nodes to the factor graph                                  *)
(*                                                                            *)
(* fg is the last input to allow for easy composition: if the first input is  *)
(* given, our function becomes takes the form factor_graph -> factor_graph,   *)
(* And so we can easily string together several operations of this form using *)
(* the ∘ operator, in case we need to make several modifications to the same  *)
(* factor graph, e.g. adding both variable nodes and function nodes           *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_n_variable_nodes_def:
  fg_add_n_variable_nodes 0 l fg = fg ∧
  fg_add_n_variable_nodes (SUC n) l fg =
  fg_add_variable_node l (fg_add_n_variable_nodes n l fg)
End

(* -------------------------------------------------------------------------- *)
(* Called before adding a function node to the factor graph, to check that    *)
(* we have been given valid arguments. This way, we can ensure that adding a  *)
(* function node will always return a valid factor graph.                     *)
(* -------------------------------------------------------------------------- *)
(* Due to changes, this has been replaced with its first conjunct (the second
   conjunct is no longer necessary and so it is no longer necessary to have this
   definition, but I'm keeping it for now in case I change my mind again.) *)
(*Definition wf_fg_fn_def:
  wf_fg_fn inputs fn fg ⇔
    inputs ⊆ var_nodes fg ∧
    FDOM fn = var_assignments inputs fg.variable_length_map
End*)

(* -------------------------------------------------------------------------- *)
(* Add a function node to the factor graph.                                   *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fn, the function to be added. Takes a mapping from variables to values   *)
(*   and returns an output of type α. Not a map, but a function: this is      *)
(*   turned into a map after being added.                                     *)
(* - fg, the factor graph                                                     *)
(*                                                                            *)
(* Output:                                                                    *)
(* - the factor graph with the new function node, connected by edges to the   *)
(*   variable nodes it depends on. If the function isn't valid, the graph is  *)
(*   returned unchanged.                                                      *)
(*                                                                            *)
(* fg is the last input to allow for easy composition: see comment for        *)
(* fg_add_n_variable_nodes_def                                                *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_function_node0_def:
  fg_add_function_node0 inputs fn fg =
  let
    fn_fmap = FUN_FMAP fn (var_assignments inputs fg.variable_length_map);
    new_node = (INR (CARD (nodes fg.underlying_graph)));
  in
    if inputs ⊆ var_nodes fg
    then
      fg with
         <|
           underlying_graph updated_by
                            (fsgAddEdges (IMAGE (λi. {i; new_node}) inputs) ∘
                                         (fsgAddNode new_node)
                            );
           function_nodes updated_by ($INSERT new_node);
           function_map updated_by (λf. FUPDATE f (new_node, fn_fmap));
         |>
    else
      fg
End

(* -------------------------------------------------------------------------- *)
(* Insert a single edge at a time                                             *)
(*                                                                            *)
(* Nodes that {e} = e INSERT {}, which causes a loop when attempting to use   *)
(* this as a rewrite rule more than once                                      *)
(* -------------------------------------------------------------------------- *)
Theorem fsgAddEdges_insert:
  ∀e es.
    fsgAddEdges (e INSERT es) = (fsgAddEdges {e}) ∘ (fsgAddEdges es)
Proof
  rw[]
  >> gvs[FUN_EQ_THM]
  >> rw[]
  >> gvs[fsgraph_component_equality]
  >> gvs[fsgedges_fsgAddEdges]
  >> gvs[EXTENSION]
  >> rw[]
  >> EQ_TAC >> rw[]
  >- (disj1_tac >> qexistsl [‘m’,‘n’] >> gvs[])
  >- (disj2_tac >> disj1_tac >> qexistsl [‘m’,‘n’] >> gvs[])
  >- (disj2_tac >> disj2_tac >> gvs[])
  >- (disj1_tac >> qexistsl [‘m’,‘n’] >> gvs[])
  >- (disj1_tac >> qexistsl [‘m’,‘n’] >> gvs[])
  >- (disj2_tac >> gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* Adding edges once and then adding edges on top of that is equivalent to    *)
(* adding the union of the two sets of edges                                  *)
(* -------------------------------------------------------------------------- *)
Theorem fsgAddEdges_fsgAddEdges[simp]:
  ∀es ds g.
    fsgAddEdges es (fsgAddEdges ds g) = fsgAddEdges (es ∪ ds) g
Proof
  rw[]
  >> gvs[fsgraph_component_equality]
  >> gvs[fsgedges_fsgAddEdges]
  >> qmatch_goalsub_abbrev_tac ‘inEs ∪ (inDs ∪ _) = (inEsOrDs ∪ _)’
  >> gvs[UNION_ASSOC]
  >> ‘inEs ∪ inDs = inEsOrDs’ suffices_by gvs[]
  >> unabbrev_all_tac
  >> gvs[EXTENSION]
  >> rw[]      
  >> EQ_TAC >> rw[]
  >- (qexistsl[‘m’,‘n’] >> gvs[])
  >- (qexistsl[‘m’,‘n’] >> gvs[])
  >- (disj1_tac >> qexistsl[‘m’,‘n’] >> gvs[])
  >- (disj2_tac >> qexistsl[‘m’,‘n’] >> gvs[])
QED

(* -------------------------------------------------------------------------- *)
(* Adding the empty set of edges doesn't change anything                      *)
(* -------------------------------------------------------------------------- *)
Theorem fsgAddEdges_empty[simp]:
  ∀g.
    fsgAddEdges ∅ g = g
Proof
  gvs[fsgAddEdges_def]
QED

(* -------------------------------------------------------------------------- *)
(* If the edges being added aren't between nodes of the same type, then       *)
(* adding edges to a graph doesn't affect partiteness.                        *)
(* -------------------------------------------------------------------------- *)
(*Theorem gen_partite_ea_fg_add_edges_for_function_node0:
  ∀(vs : (unit + num) list) S g.
    (INR (CARD (nodes g) - 1)) ∈ S ∧
    (∀x. MEM x vs ⇒ x ∈ nodes g ∧ x ∉ S) ⇒
    (gen_bipartite_ea (fg_add_edges_for_function_node0 vs g) S ⇔
       gen_bipartite_ea g S)
Proof
  rw[]
  >> EQ_TAC
  >- (rw[]
      >> gvs[gen_bipartite_ea_def]
      >> rw[]
      >> Cases_on ‘e ∈ fsgedges (fg_add_edges_for_function_node0 vs g)’
      >- gvs[]
      >> Cases_on ‘e ⊆ nodes g ∧ CARD e = 2’
      >- gvs[in_fsgedges_fg_add_edges_for_function_node0]
      >> gvs[]
      >> Cases_on ‘CARD e = 2’
      >- (gvs[]
          >> drule alledges_valid >> strip_tac
          >> gvs[SUBSET_DEF]
         )
      >> gvs[]
      >> drule alledges_valid >> strip_tac
      >> gvs[]
     )
  >> rw[]
  >> gvs[gen_bipartite_ea_def]
  >> rw[]
  >> Cases_on ‘e ⊆ nodes g ∧ CARD e = 2’
  >- (qspecl_then [‘e’, ‘vs’, ‘g’] assume_tac in_fsgedges_fg_add_edges_for_function_node0
      >> gvs[]
      >> qexistsl [‘INR (CARD (nodes g) - 1)’, ‘v’]
      >> gvs[]
      >> gvs[INSERT_DEF, DISJ_SYM]
     )
  >> drule alledges_valid >> strip_tac
  >> gvs[]
QED*)

(* -------------------------------------------------------------------------- *)
(* Add nodes_fsgAddNode to the simpset                                        *)
(* -------------------------------------------------------------------------- *)
Theorem nodes_fsgAddNode_auto[simp]:
  ∀g n.
    nodes (fsgAddNode n g) = n INSERT nodes g
Proof
  gvs[nodes_fsgAddNode]
QED

(* -------------------------------------------------------------------------- *)
(* A way of computing the equality of edges using only boolean algebra        *)
(*                                                                            *)
(* genericGraphTheory.INSERT2_lemma serves a similar purpose, but is distinct *)
(* Surely genericGraphTheory.INSERT2_lemma can be simplified to remove the    *)
(* first conjunct, as it is subsumed within the second conjunct?              *)
(* -------------------------------------------------------------------------- *)
Theorem edges_equal:
  ∀a b c d.
    {a; b} = {c; d} ⇔ (a = c ∨ a = d) ∧ (b = c ∨ b = d) ∧
                      (a = c ∨ b = c) ∧ (a = d ∨ b = d)
Proof
  rpt strip_tac
  >> gvs[EXTENSION]
  >> EQ_TAC >> rw[]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* Theorem describing how the function nodes are updated after adding a       *)
(* function node                                                              *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_function_node0_function_nodes:
  ∀fn inputs fg.
    (fg_add_function_node0 inputs fn fg).function_nodes =
    if inputs ⊆ var_nodes fg 
    then
      (INR (CARD (nodes fg.underlying_graph))) INSERT fg.function_nodes
    else
      fg.function_nodes
Proof
  rpt strip_tac
  >> gvs[fg_add_function_node0_def]
  >> Cases_on ‘inputs ⊆ var_nodes fg’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Theorem describing how the function map is updated when adding a function  *)
(* node                                                                       *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_function_node0_function_map:
  ∀inputs fn fg.
    (fg_add_function_node0 inputs fn fg).function_map =
    if inputs ⊆ var_nodes fg 
    then
      fg.function_map |+ (INR (CARD (nodes fg.underlying_graph)),FUN_FMAP fn (var_assignments inputs fg.variable_length_map))
    else
      fg.function_map
Proof
  rpt strip_tac
  >> gvs[fg_add_function_node0_def]
  >> Cases_on ‘inputs ⊆ var_nodes fg’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Theorem describing how the edges are updated when adding a function node   *)
(* -------------------------------------------------------------------------- *)
Theorem fsgedges_fg_add_function_node0_underlying_graph:
  ∀inputs fn fg.
    wffactor_graph fg ⇒
    fsgedges (fg_add_function_node0 inputs fn fg).underlying_graph =
    if inputs ⊆ var_nodes fg 
    then
      fsgedges fg.underlying_graph ∪
               IMAGE (λv. {v; INR (CARD (nodes fg.underlying_graph))}) inputs
    else
      fsgedges fg.underlying_graph
Proof
  rpt strip_tac
  >> simp[fg_add_function_node0_def]
  >> rw[]
  >> simp[fsgedges_fsgAddEdges]
  >> gvs[EXTENSION] >> rpt strip_tac
  >> EQ_TAC >> rpt strip_tac >> simp[] >> gvs[]
  >- metis_tac[] >- metis_tac[] >- metis_tac[]
  >> qmatch_abbrev_tac ‘_ ∨ b’
  >> Cases_on ‘b’ >> gvs[]
  >> qexistsl [‘v’, ‘INR (CARD (nodes fg.underlying_graph))’]
  >> gvs[]
  >> conj_tac
  >- ASM_SET_TAC[]
  >> conj_tac
  >- (qexists ‘v’ >> gvs[])
  >> ‘v ∈ nodes fg.underlying_graph’ by ASM_SET_TAC[]
  >> CCONTR_TAC
  >> gvs[inr_in_nodes_underlying_graph]
QED

(* -------------------------------------------------------------------------- *)
(* Any edge in a well-formed factor graph has one function node and one       *)
(* variable node                                                              *)
(* -------------------------------------------------------------------------- *)
Theorem wffactor_graph_edges_in_not_in:
  ∀fg a b.
    wffactor_graph fg ∧
    {a; b} ∈ fsgedges fg.underlying_graph ⇒
        (a ∈ fg.function_nodes ⇔ b ∉ fg.function_nodes)
Proof
  rpt strip_tac
  >> gvs[wffactor_graph_def]
  >> gvs[gen_bipartite_ea_def]
  >> metis_tac[]
QED

Theorem nodes_wffactor_graph:
  ∀fg.
    wffactor_graph fg ⇒
    nodes fg.underlying_graph = {INR i | i < order fg.underlying_graph}
Proof
  gvs[wffactor_graph_def]
QED

Theorem INSERT2_lemma_alt:
  ∀a b m n.
    {a;b} = {m;n} ⇔ (a = m ∧ b = n) ∨ (a = n ∧ b = m)
Proof
  rpt strip_tac
  >> gvs[INSERT2_lemma]
  >> metis_tac[]
QED

Theorem not_inr_card_nodes_underlying_graph[simp]:
  ∀fg n.
    wffactor_graph fg ∧
    n ∈ nodes fg.underlying_graph ⇒
    (n ≠ INR (CARD (nodes fg.underlying_graph))) ∧
    (n ≠ INR (order fg.underlying_graph))
Proof
  rpt strip_tac
  >> gvs[wffactor_graph_def]
QED

(* -------------------------------------------------------------------------- *)
(* Adding a function node to a factor graph maintains well-formedness         *)
(*                                                                            *)
(* We require that the original graph is well-formed, the function being      *)
(* added outputs values in the range [0,1], and that the variables associated *)
(* with the newly added function are valid nodes and variable nodes.          *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_function_node0_wf[simp]:
  ∀inputs fg fn.
    wffactor_graph fg ⇒
    wffactor_graph (fg_add_function_node0 inputs fn fg)
Proof
  rpt strip_tac
  (* Handle situation in which input function is invalid *)
  >> Cases_on ‘¬(inputs ⊆ var_nodes fg)’
  >- gvs[fg_add_function_node0_def]
  >> gvs[]
  (* Prove each well-formedness property indivudually *)
  >> simp[wffactor_graph_def] >> rpt conj_tac
  (* Bipartiteness is retained *)
  >- (drule (cj 1 (iffLR wffactor_graph_def)) >> disch_tac
      (* Expand out definition of bipartiteness, and of adding a function node *)
      >> simp[gen_bipartite_ea_def, fg_add_function_node0_def]
      >> rpt strip_tac
      >- gvs[gen_bipartite_ea_def]
      (* Expand out fsgedges fsgAddEdges: our edge is either in the old
         graph (in which case bipartiteness is trivially maintained, or our
         edge was newly added *)
      >> qpat_x_assum ‘_ ∈ _’ mp_tac
      >> PURE_REWRITE_TAC[fsgedges_fsgAddEdges, fsgedges_addNode, IN_UNION]
      (* Use bipartiteness of the original graph in the case where our edge is
         in the old graph *)
      >> REVERSE (rpt strip_tac)
      >- (drule_then assume_tac fsgedges_members
          >> gvs[wffactor_graph_edges_in_not_in]
          >> metis_tac[wffactor_graph_edges_in_not_in]
         )
      (* Simplify (we are now in the case where our edge was newly added)  *)
      >> gnvs[]
      >> pop_assum mp_tac >> simp[]
      >> rpt strip_tac
      (* The newly added edge and {n1; n2} refer to the same edge: without
         loss of generality, choose m = n1 and n = n2 *)
      >> wlog_tac ‘m = n1 ∧ n = n2’ [‘n’, ‘m’]
      >- (gvs[INSERT2_lemma_alt] >> metis_tac[])
      >> gvs[]
      >> Cases_on ‘n = m’ >> gvs[]
      (* *)
      >> gvs[INSERT2_lemma]
      >> CCONTR_TAC >> gvs[] >> ASM_SET_TAC[]
     )
  (* Domain of function map is correct *)
  >- (gvs[fg_add_function_node0_def, wffactor_graph_def]
      >> rw[EXTENSION] >> EQ_TAC >> rw[]
     )
  (* Domain of function map is correct *)
  >- (gvs[fg_add_function_node0_def, wffactor_graph_def])
  (* Domain of map obtained after applying function map to a node is correct *)
  >- (rpt strip_tac
      >> gvs[fg_add_function_node0_def]
      (* First prove the case where the node we are applying the function map
         to is the newly added node *)
      >- (gvs[FDOM_FMAP]
          >> gvs[var_assignments_def]
          >> gvs[EXTENSION] >> rpt strip_tac
          >> qmatch_goalsub_abbrev_tac ‘b1_old ∧ b2_old ⇔ b1_new ∧ b2_old’
          >> ‘b2_old ⇒ (b1_old ⇔ b1_new)’ suffices_by metis_tac[]
          >> rpt strip_tac
          >> unabbrev_all_tac
          (* For each specific x, it satisfies the condition on the left if and
             only if it satisfies the condition on the right, which is certainly
             sufficient to prove this statement *)
          >> ‘∀x'. (x' ∈ FDOM x ⇔ x' ∈ inputs) ⇔
                     (x' ∈ FDOM x ⇔
                        (x' = INR (CARD (nodes fg.underlying_graph)) ∨
                         x' ∈ nodes fg.underlying_graph) ∧
                        x' ≠ INR (CARD (nodes fg.underlying_graph)) ∧
                        (x' = INR (CARD (nodes fg.underlying_graph)) ∨
                         x' ∈ nodes fg.underlying_graph) ∧
                        ∃i. (∀x. x = x' ∨ x = INR (CARD (nodes fg.underlying_graph)) ⇔
                                   x = i ∨ x = INR (CARD (nodes fg.underlying_graph))) ∧
                            i ∈ inputs)
             ’ suffices_by gvs[]
          >> rpt strip_tac
          (* *)
          >> qmatch_abbrev_tac ‘(b1_left ⇔ b2_left) ⇔ (b1_left ⇔ b2_right)’
          >> ‘b2_left ⇔ b2_right’ suffices_by (rpt (pop_assum kall_tac) >> metis_tac[])
          >> unabbrev_all_tac
          (* *)
          >> REVERSE EQ_TAC
          >- (rpt strip_tac >> metis_tac[])
          >> rpt strip_tac
          >- ASM_SET_TAC[]
          >- (‘x' ∈ nodes fg.underlying_graph’ by ASM_SET_TAC[]
              >> gvs[])
          >- ASM_SET_TAC[]
          >- metis_tac[]
         )
      (* Now prove the case where the node we are applying the function map to
         is not the newly added node *)
      (* Simplify because we are applying the map to a node that wasn't the
         recently added node *)
      >> DEP_PURE_ONCE_REWRITE_TAC[NOT_EQ_FAPPLY]
      >> conj_tac
      >- (CCONTR_TAC >> gvs[]
          >> gvs[wffactor_graph_def])
      (* Use this property from the original map *)
      >> drule_then (fn th => gvs[th]) (cj 4 (iffLR wffactor_graph_def))
      (*  *)
      >> gvs[var_assignments_def]
      (* This is quite similar to the proof we just did in the case where
         we are applying the function map to the newly added node, so we
         copy/paste some code from that proof *)
      (* BEGIN COPY/PASTED CODE *)
      >> gvs[EXTENSION] >> rpt strip_tac
      >> qmatch_goalsub_abbrev_tac ‘b1_old ∧ b2_old ⇔ b1_new ∧ b2_old’
      >> ‘b2_old ⇒ (b1_old ⇔ b1_new)’ suffices_by metis_tac[]
      >> rpt strip_tac
      >> unabbrev_all_tac
      (* See comments above in code copy/pasted from *)
      >> ‘∀x'. (x' ∈ FDOM x ⇔
                  x' ∈ nodes fg.underlying_graph ∧ adjacent fg.underlying_graph x' n) ⇔
                 (x' ∈ FDOM x ⇔
                    (x' = INR (CARD (nodes fg.underlying_graph)) ∨
                     x' ∈ nodes fg.underlying_graph) ∧
                    (adjacent fg.underlying_graph x' n ∨
                     x' ≠ n ∧
                     (x' = INR (CARD (nodes fg.underlying_graph)) ∨
                      x' ∈ nodes fg.underlying_graph) ∧
                     (n = INR (CARD (nodes fg.underlying_graph)) ∨
                      n ∈ nodes fg.underlying_graph) ∧
                     ∃i. (∀x. x = x' ∨ x = n ⇔
                                x = i ∨ x = INR (CARD (nodes fg.underlying_graph))) ∧
                         i ∈ inputs))
         ’ suffices_by gvs[]
      >> rpt strip_tac
      (* *)
      >> qmatch_abbrev_tac ‘(b1_left ⇔ b2_left) ⇔ (b1_left ⇔ b2_right)’
      >> ‘b2_left ⇔ b2_right’ suffices_by (rpt (pop_assum kall_tac) >> metis_tac[])
      >> unabbrev_all_tac
      (* *)
      >> EQ_TAC
      >- (rpt strip_tac >> metis_tac[])
      >> rpt strip_tac >> gvs[]
      (* END COPY/PASTED CODE *)
      >- (‘i = n’ by metis_tac[]
          >> gvs[wffactor_graph_def, SUBSET_DEF]
         )
      >- (‘i = n’ by metis_tac[] >> gvs[]
          >> gvs[wffactor_graph_def, SUBSET_DEF]
         )
      >- gvs[SUBSET_DEF, wffactor_graph_def]
      >> ‘x' = INR (CARD (nodes fg.underlying_graph)) ∨ x' = i’ by metis_tac[]
      >- gvs[]
      >> gvs[]
      >> ‘n = INR (CARD (nodes fg.underlying_graph)) ∨ n = i’ by metis_tac[]
      >- gvs[]
      >> gvs[]
     )
  (* The nodes have the correct labels *)
  >> gvs[fg_add_function_node0_def, wffactor_graph_def]
  >> rw[EXTENSION] >> EQ_TAC >> rw[] >> gvs[order_fsgAddNode]
QED

(* -------------------------------------------------------------------------- *)
(* Prove that two elements in a two-element set can be swapped                *)
(* Note: there is already a theorem called something along the lines of       *)
(* INSERT_COMM which does this                                                *)
(* -------------------------------------------------------------------------- *)
Theorem set_two_element_sym:
  ∀n1 n2.
    {n1; n2} = {n2; n1}
Proof
  rpt strip_tac
  >> gvs[INSERT_DEF]
  >> irule (iffRL EXTENSION)
  >> rpt strip_tac
  >> gvs[]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* If the input functions are equivalent and input factor graphs are          *)
(* equivalent as factor graphs, then the output factor graphs are equivalent  *)
(* as factor graphs                                                           *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_function_node0_respects:
  ((=) ===> (=) ===> fgequiv ===> fgequiv) fg_add_function_node0 fg_add_function_node0
Proof
  gvs[FUN_REL_def]
  >> gvs[fgequiv_def]
QED

val _ = liftdef fg_add_function_node0_respects "fg_add_function_node"

Theorem FDOM_FMAP_MAP2[simp] = GEN_ALL (cj 1 FMAP_MAP2_THM);

(* -------------------------------------------------------------------------- *)
(* If the factor graphs are equivalent then their underlying graphs are the   *)
(* same                                                                       *)
(*                                                                            *)
(* Is there a way to write underlying_graph_respects without lambda functions? *)
(* Kinda like how you can write $f rather than a f b for an infix operator?   *)
(* -------------------------------------------------------------------------- *)
Theorem get_underlying_graph0_respects:
  ∀fg.
    (fgequiv ===> (=)) (λfg. fg.underlying_graph) (λfg. fg.underlying_graph)
Proof
  gvs[FUN_REL_def]
  >> gvs[fgequiv_def]
QED

val _ = liftdef get_underlying_graph0_respects "get_underlying_graph"

(* -------------------------------------------------------------------------- *)
(* Allow the function nodes to be obtained in the abstract version of the     *)
(* factor graph.                                                              *)
(* -------------------------------------------------------------------------- *)
Theorem get_function_nodes0_respects:
  (fgequiv ===> (=))
  (λfg. fg.function_nodes) (λfg. fg.function_nodes )
Proof
  gvs[FUN_REL_def]
  >> gvs[fgequiv_def]
QED

val _ = liftdef get_function_nodes0_respects "get_function_nodes";

(* -------------------------------------------------------------------------- *)
(* Allow the function map to be obtained in the abstract version of the       *)
(* factor graph                                                               *)
(* -------------------------------------------------------------------------- *)
Theorem get_function_map0_respects:
  (fgequiv ===> (=)) (λfg. fg.function_map) (λfg. fg.function_map)
Proof
  gvs[FUN_REL_def, fgequiv_def]
QED

val _ = liftdef get_function_map0_respects "get_function_map";

(* -------------------------------------------------------------------------- *)
(* The representation hides variable_length_map, but this is useful when      *)
(* adding function nodes because we need to be able to determine the domain   *)
(* of the function being added which depends on the variable lengths, so we   *)
(* should expoise the variable length.                                        *)
(* -------------------------------------------------------------------------- *)
Theorem get_variable_length_map0_respects:
  (fgequiv ===> (=)) (λfg. fg.variable_length_map) (λfg. fg.variable_length_map)
Proof
  gvs[FUN_REL_def]
  >> gvs[fgequiv_def]
QED

val _ = liftdef get_variable_length_map0_respects "get_variable_length_map";

Overload adjacent_nodes = “λfg cur_node.
                             {adj_node |
                             adj_node ∈ nodes (get_underlying_graph fg) ∧
                             adjacent (get_underlying_graph fg) adj_node cur_node }”;

Overload var_nodes = “λfg. {n | n ∈ nodes (get_underlying_graph fg) ∧
                                n ∉ (get_function_nodes fg)}”;

(* -------------------------------------------------------------------------- *)
(* Example 2.2 from Modern Coding Theory:                                     *)
(*                                                                            *)
(* f(x_1, x_2, x_3, x_4, x_5, x_6) = f_1(x_1, x_2, x_3) f_2(x_1, x_4, x_6)    *)
(*                                   f_3(x_4) f_4(x_4, x_5)                   *)
(*                                                                            *)
(* Example 2.2 factor graph:                                                  *)
(*                                                                            *)
(*                            x_1                                             *)
(*                           /   \                                            *)
(*                          /     \                                           *)
(*                         f_1     f_2                                        *)
(*                        /  |     |  \                                       *)
(*                       /   |     |   \                                      *)
(*                     x_2  x_3    x_4  x_6                                   *)
(*                                /  \                                        *)
(*                               /    \                                       *)
(*                              f_3   f_4                                     *)
(*                                     |                                      *)
(*                                     |                                      *)
(*                                    x_5                                     *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(* This example factor graphtor graph is based on Example 2.2.                *)
(* -------------------------------------------------------------------------- *)
Definition fg_example_factor_graph_def:
  fg_example_factor_graph
  = let
      fg_with_var_nodes = (fg_add_n_variable_nodes 6 1) fg_empty;
    in
      ((fg_add_function_node {INR 0n; INR 1n; INR 2n} (λbs. Normal (1 / 8)))
       ∘ (fg_add_function_node {INR 0n; INR 3n; INR 5n} (λbs. Normal (1 / 8)))
       ∘ (fg_add_function_node {INR 3n} (λbs. Normal (1 / 2)))
       ∘ (fg_add_function_node {INR 3n; INR 4n} (λbs. Normal (1 / 4))))
      fg_with_var_nodes
End

