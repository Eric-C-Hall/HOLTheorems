open HolKernel Parse boolLib bossLib;

open probabilityTheory;
(*open listTheory;*)
open fsgraphTheory;
open pred_setTheory;
open finite_mapTheory;

open partite_eaTheory;

(* I find DEP_PURE_ONCE_REWRITE_TAC, etc to be very helpful *)
open dep_rewrite;

(* Lifting and transfer libraries *)
open liftLib liftingTheory transferLib transferTheory;

val _ = new_theory "factor_graphs";

(* -------------------------------------------------------------------------- *)
(* This file defines factor graphs, which are used to efficiently calculate   *)
(* marginal probabilities.                                                    *)
(*                                                                            *)
(* Factor graphs can be used to implement the BCJR algorithm, which can be    *)
(* used to decode convolutional codes. This is of particular importance in    *)
(* decoding turbo codes.                                                      *)
(*                                                                            *)
(* We use the abbreviation "fg" regularly throughout this file to refer to    *)
(* factor graphs.                                                             *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* This is largely based on modern coding theory by Tom Richardson and        *)
(* Rüdiger Urbanke.                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Graph representation:                                                      *)
(*                                                                            *)
(* We use a representation based on fsgraphScript.                            *)
(*                                                                            *)
(* Each node has a label, in the form of a natural number.                    *)
(*                                                                            *)
(* Our graph is bipartite, and can be split up into function nodes and        *)
(* variable nodes                                                             *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Function representation:                                                   *)
(*                                                                            *)
(* function label -> ([list of variable labels in order],                     *)
(*                    bool list -> extreal)                                   *)
(*                                                                            *)
(* Where the bool list is the list of values that the variable inputs take.   *)
(*                                                                            *)
(* So, for example, f(x_1,x_2,x_3) =                                          *)
(*                   if x_1 then 0.5 else (if x_2 then 0.2 else 0.3)          *)
(*     would be represented by:                                               *)
(* "f" -> (["x_1", "x_2", "x_3"],                                             *)
(*         \x_1, x_2, x_3. if x_1 then 0.5 else (if x_2 then 0.2 else 0.3))   *)
(*                                                                            *)
(* Where "f" denotes a function label corresponding to f, which may, for      *)
(* example, be a num.                                                         *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Factor Graph Datatype:                                                     *)
(*                                                                            *)
(* The "underlying_graph" variable represents the underlying factor graph.    *)
(*                                                                            *)
(* The "is_function_node" function takes a node and returns 1 if it is a      *)
(* function node, and 0 if it is a variable node. This may be used to split   *)
(* our graph into a set of function nodes and a set of variable nodes,        *)
(* showing that our graph is bipartite.                                       *)
(*                                                                            *)
(* function_map maps a function node to its function, as described in the     *)
(* "Function representation" section above.                                   *)
(*                                                                            *)
(* We restrict our attention to factor graphs which have binary inputs and    *)
(* have outputs that represent probabilities (probabilities are extreals).    *)
(*                                                                            *)
(* We expect the nodes of the factor graph to be consecutive natural numbers  *)
(* starting from 0.                                                           *)
(* -------------------------------------------------------------------------- *)
Datatype:
  factor_graph_rep =
  <|
    underlying_graph : fsgraph;
    is_function_node : (unit + num) |-> num;
    function_map : (unit + num) |-> (unit + num) list # (bool list -> extreal);
  |>
End

(* -------------------------------------------------------------------------- *)
(* Well-formedness of a factor graph.                                         *)
(*                                                                            *)
(* Used to create an abstract factor_graph type based on the underlying       *)
(* factor_graph_rep representation. A factor_graph is a factor_graph_rep      *)
(* which satisfies the well-formedness properties.                            *)
(*                                                                            *)
(* - the underlying graph should be bipartite with respect to the function    *)
(*   nodes and variable nodes, assuming we have function nodes at all         *)
(* - the outputs of each function should be probabilities, and thus between   *)
(*   0 and 1                                                                  *)
(* - the variables used as input to each function must be valid nodes and     *)
(*   they should be variable nodes.                                           *)
(* - the nodes should be the consecutive natural numbers starting from 0      *)
(* -------------------------------------------------------------------------- *)
Definition wffactor_graph_def:
  wffactor_graph (fg : factor_graph_rep) ⇔
    (gen_bipartite_ea fg.underlying_graph fg.is_function_node) ∧
    (∀f bs.
       f ∈ nodes fg.underlying_graph ∧
       fg.is_function_node ' f = 1 ⇒ 
       let
         (f_args, f_func) = fg.function_map ' f
       in
         LENGTH bs = LENGTH f_args ⇒
         0 ≤ f_func bs ∧ f_func bs ≤ 1
    ) ∧
    (∀f.
       f ∈ nodes fg.underlying_graph ∧
       fg.is_function_node ' f = 1 ⇒
       (let
          variables = FST (fg.function_map ' f)
        in
          ∀x. x ∈ (set variables) ⇒ (x ∈ nodes fg.underlying_graph ∧ fg.is_function_node ' x = 0)
       )
    ) ∧
    nodes fg.underlying_graph = {INR i | i < CARD (nodes fg.underlying_graph)}
End

(* -------------------------------------------------------------------------- *)
(* Simplify INR x ∈ nodes fg.underlying_graph                                *)
(* -------------------------------------------------------------------------- *)
Theorem inr_in_nodes_underlying_graph:
  ∀fg x.
    wffactor_graph fg ⇒
    (INR x ∈ nodes fg.underlying_graph ⇔ x < CARD (nodes fg.underlying_graph))
Proof
  rpt strip_tac
  >> gvs[wffactor_graph_def]
  >> first_assum (fn th => PURE_REWRITE_TAC[Once th])
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Suppose we have an updated is_function_node map, as a result of adding a   *)
(* new node to the graph (and hence the new node has the specific value which *)
(* is 1 more than any previous node). Then applying the updated map to a      *)
(* value in the old graph is equivalent to applying the old map to that value *)
(* -------------------------------------------------------------------------- *)
Theorem fupdate_is_function_node[simp]:
  ∀fg f x.
    wffactor_graph fg ∧
    f ∈ nodes fg.underlying_graph ⇒
    (fg.is_function_node |+ (INR (CARD (nodes fg.underlying_graph)), x)) ' f =
    fg.is_function_node ' f
Proof
  rw[]
  >> irule NOT_EQ_FAPPLY
  >> rpt strip_tac
  >> gvs[]
  >> gvs[inr_in_nodes_underlying_graph]
QED

(* -------------------------------------------------------------------------- *)
(* Similar to fupdate_is_function_node, but for function_map instead          *)
(* -------------------------------------------------------------------------- *)
Theorem fupdate_is_function_node[simp]:
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
  fg_empty0 : factor_graph_rep =
  <|
    underlying_graph := emptyG;
    is_function_node := FEMPTY;
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
(* The empty graph is bipartite into the empty set and the empty set          *)
(* -------------------------------------------------------------------------- *)
Theorem gen_bipartite_ea_fg_empty[simp]:
  gen_bipartite_ea emptyG FEMPTY
Proof
  gvs[gen_bipartite_ea_def]
QED

(* -------------------------------------------------------------------------- *)
(* Add a variable node to the factor_graph.                                   *)
(*                                                                            *)
(* The first node added (variable or function) should be 0, the next node     *)
(* should be 1, etc.                                                          *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_variable_node0_def:
  fg_add_variable_node0 fg =
  let
    new_node = (INR (CARD (nodes fg.underlying_graph)))
  in
    fg with
       <|
         underlying_graph := fsgAddNode new_node fg.underlying_graph;
         is_function_node updated_by (λf. FUPDATE f (new_node, 0));
       |>
End

(* -------------------------------------------------------------------------- *)
(* Adding a variable node maintains well-formedness                           *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_variable_node0_wf:
  ∀fg.
    wffactor_graph fg ⇒
    wffactor_graph (fg_add_variable_node0 fg)
Proof
  rpt strip_tac
  >> simp[wffactor_graph_def, fg_add_variable_node0_def]
  >> rw[]
  >- (drule (cj 1 (iffLR wffactor_graph_def))
      >> rw[]
      >> DEP_PURE_ONCE_REWRITE_TAC[gen_partite_fsgAddNode]
      >> gvs[]
      >> gvs[inr_in_nodes_underlying_graph]
     )
  >- gvs[]
  >- (gvs[] >> gvs[wffactor_graph_def]
     (*drule $ cj 2 (iffLR wffactor_graph_def)
       >> disch_tac
       >> gvs[]
       >> pop_assum irule
       >> gvs[]
       >> qpat_x_assum ‘_ ' f = 1’ (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
       >> SYM_TAC
       >> irule NOT_EQ_FAPPLY
       >> strip_tac
       >> gvs[]
       >> gvs[inr_in_nodes_underlying_graph]*)
  )
  >- gvs[FAPPLY_FUPDATE]
  >- gvs[FAPPLY_FUPDATE]
  >- (gvs[]
      >> disj2_tac
      >> gvs[]
      >> drule (cj 3 (iffLR wffactor_graph_def))
      >> rpt strip_tac
      >> pop_assum drule
      >> rw[]
     )
  >- (gvs[]
      >> drule (cj 3 (iffLR wffactor_graph_def))
      >> rw[]
      >> pop_assum drule
      >> rw[]
     )
  >- gvs[inr_in_nodes_underlying_graph]
  >- (gvs[inr_in_nodes_underlying_graph]
      >> drule (cj 4 (iffLR wffactor_graph_def))
      >> rw[]
      >> qmatch_abbrev_tac ‘donotexpand1 INSERT _ = donotexpand2’
      >> qpat_x_assum ‘nodes _ = _’ (fn th => PURE_REWRITE_TAC[Once th])
      >> unabbrev_all_tac
      >> gvs[]
     )
QED

(* -------------------------------------------------------------------------- *)
(* A proof that if the inputs are equivalent as factor graphs, then the       *)
(* outputs are also equivalent as factor graphs, and thus we can lift         *)
(* fg_add_variable_node to our abstract type                                  *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_variable_node0_respects:
  ∀fg.
    (fgequiv ===> fgequiv) fg_add_variable_node0 fg_add_variable_node0
Proof
  rpt strip_tac
  >> gvs[FUN_REL_def]
  >> gvs[fgequiv_def]
  >> gvs[fg_add_variable_node0_wf]
QED

val _ = liftdef fg_add_variable_node0_respects "fg_add_variable_node"

(* -------------------------------------------------------------------------- *)
(* Adds n variable nodes to the factor graph                                  *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_n_variable_nodes_def:
  fg_add_n_variable_nodes fg 0 = fg ∧
  fg_add_n_variable_nodes fg (SUC n) =
  fg_add_variable_node (fg_add_n_variable_nodes fg n)
End

(* -------------------------------------------------------------------------- *)
(* Add the edges between a function node being added to the graph and         *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_edges_for_function_node0_def:

End

(* -------------------------------------------------------------------------- *)
(* Add a function node to the factor graph.                                    *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - f, the function to be added.                                             *)
(*                                                                            *)
(* Output:                                                                    *)
(* - the factor graph with the new function node. The edges to other variable *)
(* ts label will be the next  *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*   unused label.                                                            *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_function_node0_def:
  fg_add_function_node0 fg fn =
  let
    new_node = (INR (CARD (nodes fg.underlying_graph)))
  in
    fg with
       <|
         underlying_graph := fsgAddNode new_node fg.underlying_graph;
         is_function_node updated_by (λf. FUPDATE f (new_node, 1));
         function_map updated_by (λf. FUPDATE f (new_node, fn));
       |>
End

(* -------------------------------------------------------------------------- *)
(* Adding a function node to a factor graph maintains well-formedness         *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_function_node0_wf[simp]:
  ∀fg fn.
    wffactor_graph fg ∧
    (∀bs. LENGTH bs = LENGTH (FST fn) ⇒ 0 ≤ (SND fn) bs ∧ (SND fn) bs ≤ 1) ⇒
    wffactor_graph (fg_add_function_node0 fg fn)
Proof
  rpt strip_tac
  >> simp[wffactor_graph_def, fg_add_function_node0_def]
  >> rw[]
  (* Much of this is copy/pasted from fg_add_variable_node0_wf *)
  >- (drule (cj 1 (iffLR wffactor_graph_def))
      >> rw[]
      >> DEP_PURE_ONCE_REWRITE_TAC[gen_partite_fsgAddNode]
      >> gvs[]
      >> gvs[inr_in_nodes_underlying_graph]
     )
  >- (gvs[]
      >> Cases_on ‘fn’ >> gvs[])
  >- (gvs[] >> gvs[wffactor_graph_def])
  >- (gvs[]
      >> drule (cj 3 (iffLR wffactor_graph_def))
      >> rpt strip_tac
     )
  >- gvs[FAPPLY_FUPDATE]
  >- (gvs[]
      >> disj2_tac
      >> gvs[]
      >> drule (cj 3 (iffLR wffactor_graph_def))
      >> rpt strip_tac
      >> pop_assum drule
      >> rw[]
     )
  >- (gvs[]
      >> drule (cj 3 (iffLR wffactor_graph_def))
      >> rw[]
      >> pop_assum drule
      >> rw[]
     )
  >- gvs[inr_in_nodes_underlying_graph]
  >- (gvs[inr_in_nodes_underlying_graph]
      >> drule (cj 4 (iffLR wffactor_graph_def))
      >> rw[]
      >> qmatch_abbrev_tac ‘donotexpand1 INSERT _ = donotexpand2’
      >> qpat_x_assum ‘nodes _ = _’ (fn th => PURE_REWRITE_TAC[Once th])
      >> unabbrev_all_tac
      >> gvs[]
     )
QED

(* -------------------------------------------------------------------------- *)
(* Prove that two elements in a two-element set can be swapped                *)
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
(* Adds an edge between two nodes in the graph.                               *)
(*                                                                            *)
(* If the edge would be between a function node and a function node or a      *)
(* variable node and a variable node, this returns turns ARB, which should    *)
(* hopefully indicate that something has gone wrong.                          *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n1, the first node to                                                    *)
(* - n2, the second node                                                      *)
(*                                                                            *)
(* Output:                                                                    *)
(* - the updated factor graph                                                 *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_edge_def:
  fg_add_edge fg n1 n2 =
  if ((n1 ∈ fg.variable_nodes ∧ n2 ∈ fg.variable_nodes) ∨
      (n1 ∈ fg.function_nodes ∧ n2 ∈ fg.function_nodes))
  then
    ARB
  else
    fg with
       <|
         underlying_graph := fsgAddEdges {{n1; n2}} fg.underlying_graph
       |>
End

(* -------------------------------------------------------------------------- *)
(* Prove that adding an edge between two elements is the same regardless of   *)
(* which order the two elements are provided in                               *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_edge_sym:
  ∀fg n1 n2.
    fg_add_edge fg n1 n2 = fg_add_edge fg n2 n1
Proof
  rpt strip_tac
  >> gvs[fg_add_edge_def]
  >> rw[]
  >> Cases_on ‘n1 ∈ fg.variable_nodes’ >> Cases_on ‘n2 ∈ fg.variable_nodes’ >> Cases_on ‘n1 ∈ fg.function_nodes’ >> Cases_on ‘n2 ∈ fg.function_nodes’ >> gvs[]
  >> gvs[set_two_element_sym]
QED

Theorem fg_add_edge_wf_spec:
  ∀fg n1 n2.
    (n1 ∈ fg.variable_nodes ∧ n2 ∈ fg.function_nodes) ⇒
    wffactor_graph (fg_add_edge fg n1 n2)
Proof
  rpt strip_tac
  >> gvs[wffactor_graph_def, fg_add_edge_def]
  >> 
QED

Theorem fg_add_edge_wf:
  ∀fg n1 n2.
    ((n1 ∈ fg.variable_nodes ∧ n2 ∈ fg.function_nodes) ∨
     (n1 ∈ fg.function_nodes ∧ n2 ∈ fg.variable_nodes)) ⇒
    wffactor_graph (fg_add_edge fg n1 n2)
Proof
  rw[]
  >> metis_tac[fg_add_edge_wf_spec, fg_add_edge_sym]
QED

(* -------------------------------------------------------------------------- *)
(* Adds several variable and function nodes. This is intended to be much      *)
(* easier to use than manually calling fg_add_variable_node and               *)
(* fg_add_function_node repeatedly.                                            *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph to add the nodes to.                                *)
(* - nt::nts (aka. node types), a list of booleans, where the ith element is  *)
(*   T if we need to add a function node and F if we need to add a variable   *)
(*   node.                                                                    *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_variable_and_function_nodes:
  fg_add_variable_and_function_nodes fg [] = fg ∧
  fg_add_variable_and_function_nodes fg nt::nts =
  let
    recursive_call = fg_add_variable_and_function_nodes fg nts
  in
    if nt
    then
      fg_add_function_node      
    else
Proof
QED


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
(* The following example factor graph is based on Example 2.2.                *)
(* -------------------------------------------------------------------------- *)
Definition fg_example_factor_graph_def:
  fg_example_factor_graph = fg_add_variable_node ∘ fg_add_variable_node ∘ fg_add_function_node ∘ fg_add_variable_node fg_empty
End

Definition fg_example_functions_def:
  fg_example_functions =
  λf. if f = 1 then
        ([0, 2, 3], λxs. ARB)
      else if f = 4 then
        ([0, 5, 9], λxs. ARB)
      else if f = 6 then
        ([5], λxs. ARB)
      else if f = 7 then
        ([5, 8], λxs. ARB)
      else ARB
End

Definition fg_example_def:
  fg_example =
  <|
    functions := [ARB; ARB; ARB];
    num_variables := 6;
    edges := [
        (0, 0);
        (0, 1);
        (0, 2);
        (1, 0);
        (1, 3);
        (1, 5);
        (2, 3);
        (3, 3);
        (3, 4);
      ];
  |>
End

(* -------------------------------------------------------------------------- *)
(* The following is a manually designed example graph based on Example 2.2    *)
(* -------------------------------------------------------------------------- *)
Definition helloworld_graph_def:
  helloworld_graph : fsgraph =
  fsgAddEdges {
              {INR 0; INR 1;};
           {INR 1; INR 2;};
           {INR 1; INR 3;};
           {INR 0; INR 4;};
           {INR 4; INR 5;};
           {INR 5; INR 6;};
           {INR 5; INR 7;};
           {INR 7; INR 8;};
           {INR 4; INR 9;};
           } (fsgAddNodes {INR x | x ∈ count 10} emptyG)
End

(* -------------------------------------------------------------------------- *)
(* Gets the variable nodes adjacent to a given function node via one of the   *)
(* provided edges.                                                            *)
(*                                                                            *)
(* Input:                                                                     *)
(* - n, the index of the function node we want to find the connected variable *)
(*   nodes of                                                                 *)
(* - edges, the list of edges we may take                                     *)
(*                                                                            *)
(* Output:                                                                    *)
(* - The list of variable nodes which are connected to the funtion node via   *)
(*   an edge.                                                                 *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_variable_nodes_via_edges_def:
  fg_get_adjacent_variable_nodes_via_edges n [] = [] ∧
  fg_get_adjacent_variable_nodes_via_edges
  n ((function_index, variable_index)::remaining_edges) =
  let
    recursive_call = fg_get_adjacent_variable_nodes_via_edges n remaining_edges;
  in
    if (function_index = n)
    then (variable_index)::recursive_call
    else recursive_call
End

(* -------------------------------------------------------------------------- *)
(* Gets the variable nodes adjacent to a given function node                  *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n, the index of the function node we want to find the connected variable *)
(*   node of                                                                  *)
(*                                                                            *)
(* Output:                                                                    *)
(* - The list of variable nodes which are adjacent to the function node via   *)
(*   an edge in the factor graph                                              *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_variable_nodes_def:
  fg_get_adjacent_variable_nodes fg n =
  fg_get_adjacent_variable_nodes_via_edges n fg.edges
End

(* -------------------------------------------------------------------------- *)
(* Gets the function nodes adjacent to a particular variable node             *)
(*                                                                            *)
(* Input:                                                                     *)
(* - n, the index of the variable node we are finding the adjacent function   *)
(*   nodes for                                                                *)
(* - edges, the list of edges that we may take                                *)
(*                                                                            *)
(* Output:                                                                    *)
(* - The list of function nodes which are adjacent to the variable node via   *)
(*   one of the provided edges                                                *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_function_nodes_via_edges_def:
  fg_get_adjacent_function_nodes_via_edges n [] = [] ∧
  fg_get_adjacent_function_nodes_via_edges
  n ((function_index, variable_index)::remaining_edges) =
  let
    recursive_call = fg_get_adjacent_function_nodes_via_edges n remaining_edges;
  in
    if (variable_index = n)
    then (function_index)::recursive_call
    else recursive_call
End

(* -------------------------------------------------------------------------- *)
(* Gets the function nodes connected to a given variable node                 *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n, the index of the variable node we are finding the adjacent function   *)
(*   nodes for                                                                *)
(*                                                                            *)
(* Output:                                                                    *)
(* - The list of function node indices which are adjacent to the provided     *)
(* variable node.                                                             *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_function_nodes_def:
  fg_get_adjacent_function_nodes fg n =
  fg_get_adjacent_function_nodes_via_edges n fg.edges
End

(*Definition deduplicate_def:
  deduplicate [] = [] ∧
  deduplicate l::ls = if ()
                         End*)

(* -------------------------------------------------------------------------- *)
(* Gets the function nodes that are adjacent to nodes which themselves are    *)
(* adjacent to the given function node                                        *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n, the index of the variable node we start from                          *)
(*                                                                            *)
(* Output:                                                                    *)
(* - The list of function nodes which are adjacent to variable nodes which    *)
(* themselves are adjacent to the function node n (Duplicates may be present) *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_adjacent_function_nodes_def:
  fg_get_adjacent_adjacent_function_nodes fg n =
  FOLDR APPEND [] (MAP (fg_get_adjacent_function_nodes fg) (fg_get_adjacent_variable_nodes fg n))
End

(* -------------------------------------------------------------------------- *)
(* Deduplicate fg_get_adjacent_adjacent_function_nodes                        *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_adjacent_function_nodes_no_duplicates_def:
  fg_get_adjacent_adjacent_function_nodes_no_duplicates fg n =
End 

(* -------------------------------------------------------------------------- *)
(* Gets the function nodes that are adjacent to a particular                  *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_adjacent_function_nodes_taboo_def:
  fg_get_adjacent_function_nodes_taboo fg
End

(* -------------------------------------------------------------------------- *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n, the index of the function node to find the connected region from      *)
(* - taboo_nodes, the list of function nodes that we cannot go to             *)
(* Output:                                                                    *)
(* - A list of node indexes that are contained in the connected region        *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_connected_region_taboo_def:
  fg_get_connected_region_taboo fg n taboo_nodes =
  
End

(* -------------------------------------------------------------------------- *)
(* Input:                                                                     *)
(* - fg, the factor graph                                                     *)
(* - n, the index of the function node to find the connected region from      *)
(* Output:                                                                    *)
(* - A list of node indexes that are contained in the connected region        *)
(* -------------------------------------------------------------------------- *)
Definition fg_get_connected_region_def:
  fg_get_connected_region fg n = fg_get_connected_region_taboo fg n []
End

Definition fg_split_into_trees_recursive_def:
  fg_split_into_trees_recursive fg [] = [] ∧
  fg_split_into_trees_recursive fg available_nodes =
  let
    (nodes_in_tree, other_nodes) = fg_get_nodes_in_tree fg (HD available_nodes)
  in
    nodes_in_tree::fg_split_into_trees_
End

(* *)
Definition fg_split_into_trees_def:
  fg_split_into_trees fg = fg_split_into_trees_recursive fg (COUNT (LENGTH fg.nodes))
End

Definition fg_identify_leaves_def:
  fg_identify_leaves = 
End

Definition fg_initialise_messages_def:
  fg_initialise_messages = 
End


Definition fg_calculate_data_def:
  fg_calculate_data = 
End





(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition fg_leaf_nodes_def:
  fg
End


(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition calculate_message_passing_def:


End

val _ = export_theory();
