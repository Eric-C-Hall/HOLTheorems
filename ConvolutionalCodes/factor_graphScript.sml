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

open partite_eaTheory;

open donotexpandLib;

(* I find DEP_PURE_ONCE_REWRITE_TAC, etc to be very helpful *)
open dep_rewrite;

open ConseqConv;
open simpLib;

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
    function_nodes : (unit + num) -> bool;
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
(* - the domain of function_map should be the set of function nodes           *)
(* - the set of function nodes should be a subset of the nodes                *)
(* - the outputs of each function should be probabilities, and thus between   *)
(*   0 and 1                                                                  *)
(* - the variables used as input to each function must be valid nodes and     *)
(*   they should be variable nodes, and one variable should not be used more  *)
(*   than once                                                                *)
(* - the edges in the graph should connect an function and variable if and    *)
(*   only if that variable is one of the inputs to that function              *)
(* - the nodes should be the consecutive natural numbers starting from 0      *)
(* -------------------------------------------------------------------------- *)
Definition wffactor_graph_def:
  wffactor_graph (fg : factor_graph_rep) ⇔
    (gen_bipartite_ea fg.underlying_graph fg.function_nodes) ∧
    FDOM fg.function_map = fg.function_nodes ∧
    (∀f bs.
       f ∈ fg.function_nodes ⇒ 
       let
         (f_args, f_func) = fg.function_map ' f
       in
         LENGTH bs = LENGTH f_args ⇒
         0 ≤ f_func bs ∧ f_func bs ≤ 1
    ) ∧
    (∀f.
       f ∈ fg.function_nodes ⇒
       (let
          variables = FST (fg.function_map ' f)
        in
          ∀x. MEM x variables ⇒ (x ∈ nodes fg.underlying_graph ∧
                                 x ∉ fg.function_nodes ∧
                                 UNIQUE x variables
                                )
       )
    ) ∧
    (∀e. e ∈ fsgedges fg.underlying_graph ⇔
           (∃f v. e = {f; v} ∧ f ∈ nodes fg.underlying_graph
                          ∧ v ∈ nodes fg.underlying_graph
                          ∧ f ∈ fg.function_nodes
                          ∧ v ∉ fg.function_nodes
                          ∧ MEM v (FST (fg.function_map ' f)))) ∧
    nodes fg.underlying_graph = {INR i | i < order fg.underlying_graph}
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
  >> gvs[wffactor_graph_def, genericGraphTheory.gsize_def]
  >> first_assum (fn th => PURE_REWRITE_TAC[Once th])
  >> gvs[]
QED

(*(* -------------------------------------------------------------------------- *)
(* Suppose we have an updated is_function_node map, as a result of adding a   *)
(* new node to the graph (and hence the new node has the specific value which *)
(* is 1 more than any previous node). Then applying the updated map to a      *)
(* value in the old graph is equivalent to applying the old map to that value *)
(* -------------------------------------------------------------------------- *)
Theorem fupdate_function_nodes_node[simp]:
  ∀fg f x.
    wffactor_graph fg ∧
    f ∈ nodes fg.underlying_graph ⇒
    (fg.function_nodes

       (INR (CARD (nodes fg.underlying_graph)), x)) ' f =
    fg.is_function_node ' f
Proof
  rw[]
  >> irule NOT_EQ_FAPPLY
  >> rpt strip_tac
  >> gvs[]
  >> gvs[inr_in_nodes_underlying_graph]
QED*)

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
  fg_empty0 : factor_graph_rep =
  <|
    underlying_graph := emptyG;
    function_nodes := ∅;
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
         underlying_graph updated_by (fsgAddNode new_node);
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
(* The node just beyond the current set of valid nodes is not a valid node,   *)
(* and thus, it cannot be one of the variables associated with a function     *)
(* node.                                                                      *)
(* -------------------------------------------------------------------------- *)
Theorem inr_card_not_in_mem_function_map[simp]:
  ∀fg f.
    wffactor_graph fg ∧
    f ∈ fg.function_nodes ⇒
    ¬MEM (INR (CARD (nodes fg.underlying_graph))) (FST (fg.function_map ' f))
Proof
  rpt strip_tac
  >> drule (cj 4 (iffLR wffactor_graph_def)) >> disch_tac
  >> pop_assum drule >> disch_tac
  >> gvs[]
  >> pop_assum drule >> disch_tac
  >> gvs[]
  >> gvs[inr_in_nodes_underlying_graph]
QED

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
  (* Prove each property of well-formedness one at a time *)
  >> rpt conj_tac
  >- (gvs[gen_bipartite_ea_fsgAddNode]
      >> rw[inr_in_nodes_underlying_graph]
      >> metis_tac[DELETE_NON_ELEMENT_RWT,
                   inr_card_not_in_function_nodes,
                   wffactor_graph_def]
              )
  >- gvs[wffactor_graph_def]
  >- (drule (cj 3 (iffLR wffactor_graph_def)) >> rw[]
      >> gvs[SUBSET_DEF])
  >- (drule (cj 4 (iffLR wffactor_graph_def)) >> disch_tac
      >> strip_tac >> strip_tac
      >> first_x_assum drule >> strip_tac
      >> gvs[]
     )
  >- (drule (cj 5 (iffLR wffactor_graph_def)) >> disch_tac
      >> gvs[]
      >> pop_assum kall_tac
      >> rw[]
      >> EQ_TAC
      >- (rw[] >> qexistsl [‘f’, ‘v’] >> gvs[])
      >- (strip_tac
          >- (qexistsl [‘f’, ‘v’] >> gvs[])
          >- gvs[inr_card_not_in_function_nodes]
          >- gvs[inr_card_not_in_function_nodes]
          >- (qexistsl [‘f’, ‘v’] >> gvs[])
         )
     )
  >- (drule (cj 6 (iffLR wffactor_graph_def)) >> disch_tac
      >> qmatch_goalsub_abbrev_tac ‘S1 INSERT _ = S2’
      >> simp[]
      >> unabbrev_all_tac
      >> pop_assum kall_tac
      >> gvs[order_fsgAddNode]
      >> rw[]
      >- gvs[wffactor_graph_def]
      >> gvs[gsize_def, ADD1]
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
(*                                                                            *)
(* fg is the last input to allow for easy composition: if the first input is  *)
(* given, our function becomes takes the form factor_graph -> factor_graph,   *)
(* And so we can easily string together several operations of this form using *)
(* the ∘ operator, in case we need to make several modifications to the same  *)
(* factor graph, e.g. adding both variable nodes and function nodes           *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_n_variable_nodes_def:
  fg_add_n_variable_nodes 0 fg = fg ∧
  fg_add_n_variable_nodes (SUC n) fg =
  fg_add_variable_node (fg_add_n_variable_nodes n fg)
End

(* -------------------------------------------------------------------------- *)
(* Add the edges between a function node being added to the graph and the     *)
(* variable nodes that it relies on.                                          *)
(*                                                                            *)
(* We assume that the related function node has only just been added to the   *)
(* graph, so that its label is CARD (nodes fg.underlying_graph) - 1           *)
(*                                                                            *)
(*                                                                            *)
(* fg is the last input to allow for easy composition: see comment for        *)
(* fg_add_n_variable_nodes_def                                                *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_edges_for_function_node0_def:
  fg_add_edges_for_function_node0 vs (g : fsgraph) =
  let
    currnode = INR (CARD (nodes g) - 1)
  in
    fsgAddEdges (LIST_TO_SET (MAP (λv. {v; currnode}) vs)) g
End

(* -------------------------------------------------------------------------- *)
(* Determine if a function is invalid with respect to a factor graph          *)
(* -------------------------------------------------------------------------- *)
Definition wf_fg_fn_def:
  wf_fg_fn fn fg ⇔ (∀bs. LENGTH bs = LENGTH (FST fn) ⇒
                         0 ≤ (SND fn) bs ∧
                         (SND fn) bs ≤ 1 : extreal) ∧
                   (∀x. MEM x (FST fn) ⇒
                        x ∈ nodes fg.underlying_graph ∧
                        x ∉ fg.function_nodes ∧
                        UNIQUE x (FST fn)
                   )
End

(* -------------------------------------------------------------------------- *)
(* Add a function node to the factor graph.                                   *)
(*                                                                            *)
(* Input:                                                                     *)
(* - fn, the function to be added, as a tuple (variable_labels, function)     *)
(*   we expect the variable labels to be valid nodes, which are variable      *)
(*   nodes, and we expect there to be no duplicates in these nodes.           *)
(*                                                                            *)
(* - fg, the factor graph                                                     *)
(*                                                                            *)
(* Output:                                                                    *)
(* - the factor graph with the new function node. The edges to the variable   *)
(*   nodes depended upon by this function are also added. If the function     *)
(*   which is being added is invalid, then we simply return the original      *)
(*   graph. It is invalid if its inputs aren't nodes in the graph, or they    *)
(*   are function nodes rather than variable nodes, or the same input is      *)
(*   provided twice, or there is an input to the function that would output   *)
(*   a value outside the valid range of probabilities, i.e. [0,1].            *)
(*                                                                            *)
(* fg is the last input to allow for easy composition: see comment for        *)
(* fg_add_n_variable_nodes_def                                                *)
(* -------------------------------------------------------------------------- *)
Definition fg_add_function_node0_def:
  fg_add_function_node0 fn fg =
  let
    new_node = (INR (CARD (nodes fg.underlying_graph)));
  in
    if wf_fg_fn fn fg
    then
      fg with
         <|
           underlying_graph updated_by ((fg_add_edges_for_function_node0 (FST fn))
                                        ∘ (fsgAddNode new_node));
           function_nodes updated_by ($INSERT new_node);
           function_map updated_by (λf. FUPDATE f (new_node, fn));
         |>
    else
      fg
End

(* -------------------------------------------------------------------------- *)
(* Adding edges doesn't affect the nodes of a graph                           *)
(* -------------------------------------------------------------------------- *)
Theorem nodes_fg_add_edges_for_function_node0[simp]:
  ∀m vs g.
    nodes (fg_add_edges_for_function_node0 vs g) = nodes g
Proof
  rpt strip_tac
  >> gvs[fg_add_edges_for_function_node0_def]
QED

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
(* Apply fg_add_edges_for_function_node0 for a single step                    *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_edges_for_function_node0_step:
  ∀v vs g.
    fg_add_edges_for_function_node0 (v::vs) g =
    fg_add_edges_for_function_node0
    vs (fsgAddEdges {{v; INR (CARD (nodes g) - 1)}} g)
Proof
  rw[]
  >> gvs[fg_add_edges_for_function_node0_def]
  >> gvs[UNION_DEF, INSERT_DEF, DISJ_SYM]
QED

(* -------------------------------------------------------------------------- *)
(* After adding edges, a edge is in the new graph if and only if it is either *)
(* in the old graph or it is one of the new edges that were added.            *)
(* -------------------------------------------------------------------------- *)
Theorem in_fsgedges_fg_add_edges_for_function_node0:
  ∀e vs g.
    e ⊆ nodes g ∧ CARD e = 2 ⇒
    (e ∈ fsgedges (fg_add_edges_for_function_node0 vs g) ⇔
       e ∈ fsgedges g ∨ (∃v. MEM v vs ∧ e = {v; INR (CARD (nodes g) - 1)}))
Proof  
  Induct_on ‘vs’ >> gvs[]
  >- rw[fg_add_edges_for_function_node0_def, fsgAddEdges_def]
  >> rw[]
  >> gvs[fg_add_edges_for_function_node0_step]
  >> EQ_TAC >> rw[]
  >- (gvs[fsgedges_fsgAddEdges]
      >> disj2_tac
      >> qexists ‘h’ >> gvs[])
  >- (disj2_tac
      >> qexists ‘v’ >> gvs[])
  >- (disj1_tac
      >> gvs[fsgedges_fsgAddEdges])
  >- (qmatch_goalsub_abbrev_tac ‘_ ∨ b’
      >> Cases_on ‘b’ >> gvs[]
      >> gvs[fsgedges_fsgAddEdges]
      >> Cases_on ‘{h; INR (CARD (nodes g) - 1)} ∈ fsgedges g’ >> gvs[]
      >> qexistsl [‘h’, ‘INR (CARD (nodes g) - 1)’]
      >> gvs[]
      >> CCONTR_TAC
      >> gs[]
     )
  >- (disj2_tac
      >> qexists ‘v’ >> gvs[]
     )
QED

(* -------------------------------------------------------------------------- *)
(* An expression for the new set of edges after adding the edges              *)
(* corresponding to a function node.                                          *)
(* -------------------------------------------------------------------------- *)
Theorem fsgedges_fg_add_edges_for_function_node0:
  ∀vs g.
    ¬MEM (INR (CARD (nodes g) - 1)) vs ∧
    set (vs) ⊆ nodes g ∧
    INR (CARD (nodes g) - 1) ∈ nodes g ⇒
    fsgedges (fg_add_edges_for_function_node0 vs g) =
    fsgedges g ∪ {{v; INR (CARD (nodes g) - 1)} | MEM v vs}
Proof
  rpt strip_tac
  >> gvs[EXTENSION]
  >> rw[]
  >> Cases_on ‘x ⊆ nodes g ∧ CARD x = 2’
  >- (DEP_PURE_ONCE_REWRITE_TAC[in_fsgedges_fg_add_edges_for_function_node0]
      >> gvs[]
      >> EQ_TAC
      >- (rw[] >> gvs[]
          >> Cases_on ‘v = INR (CARD (nodes g) - 1)’ >> gvs[]
          >> disj2_tac
          >> qexists ‘v’ >> gvs[]
         )
      >> rw[] >> gvs[]
      >> Cases_on ‘x ∈ fsgedges g’ >> gvs[]
      >> Cases_on ‘x = {v; INR (CARD (nodes g) - 1)}’
      >- (qexists ‘v’ >> gvs[])
      >> gvs[EXTENSION]
     )
  >> EQ_TAC
  >- (rpt strip_tac
      >> drule alledges_valid >> strip_tac
      >> gvs[]
     )
  >> rw[]
  >- (rpt strip_tac
      >> drule alledges_valid >> strip_tac
      >> gvs[]
     )
  >> sg ‘x = {v; INR (CARD (nodes g) - 1)}’
  >- gvs[EXTENSION]
  >> gvs[]
  >> Cases_on ‘v = INR (CARD (nodes g) - 1)’ >> gvs[]
  >> gvs[SUBSET_DEF]
QED

(* -------------------------------------------------------------------------- *)
(* An alternative, weaker expression for the new set of edges after adding    *)
(* edges to the                                                               *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem fsgedges_fg_add_edges_for_function_node0_wffactor_graph:
  ∀fg fn.
    wffactor_graph fg ∧
    wf_fg_fn fn fg ∧
    (INR (CARD (nodes fg.underlying_graph) - 1)) ∈ fg.function_nodes ∧
    fg.function_map ' (INR (CARD (nodes fg.underlying_graph) - 1)) = fn ⇒
    fsgedges (fg_add_edges_for_function_node0 (FST fn) fg.underlying_graph) =
    fsgedges fg.underlying_graph ∪ {{v; INR (CARD (nodes fg.underlying_graph) - 1)} | MEM v (FST fn)}
Proof
  rpt strip_tac
  >> Cases_on ‘CARD (nodes fg.underlying_graph) = 0’
  >- gvs[wffactor_graph_def]
  >> irule fsgedges_fg_add_edges_for_function_node0
  >> rpt conj_tac
  >- (drule (cj 4 (iffLR wffactor_graph_def)) >> strip_tac
      >> pop_assum drule >> strip_tac
      >> gvs[]
      >> CCONTR_TAC
      >> gvs[]
     )
  >- (gvs[inr_in_nodes_underlying_graph]
      >> CCONTR_TAC
      >> gvs[]
     )
  >- (gvs[wf_fg_fn_def]
      >> gvs[SUBSET_DEF]
     )
QED

(* -------------------------------------------------------------------------- *)
(* If the edges being added aren't between nodes of the same type, then       *)
(* adding edges to a graph doesn't affect partiteness.                        *)
(* -------------------------------------------------------------------------- *)
Theorem gen_partite_ea_fg_add_edges_for_function_node0:
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
QED

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
  ∀fn fg.
    (fg_add_function_node0 fn fg).function_nodes =
    if wf_fg_fn fn fg
    then
      (INR (CARD (nodes fg.underlying_graph))) INSERT fg.function_nodes
    else
      fg.function_nodes
Proof
  rpt strip_tac
  >> gvs[fg_add_function_node0_def]
  >> Cases_on ‘wf_fg_fn fn fg’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Theorem describing how the domain of the map from function nodes to        *)
(* functions is updated when adding a function node                           *)
(* -------------------------------------------------------------------------- *)
Theorem FDOM_fg_add_function_node0:
  ∀fn fg.
    FDOM (fg_add_function_node0 fn fg).function_map =
    if wf_fg_fn fn fg
    then
      (INR (CARD (nodes fg.underlying_graph))) INSERT FDOM (fg.function_map)
    else
      FDOM (fg.function_map)
Proof
  rpt strip_tac
  >> gvs[fg_add_function_node0_def]
  >> Cases_on ‘wf_fg_fn fn fg’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Theorem describing how the function map is updated when adding a function  *)
(* node                                                                       *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_function_node0_function_map:
  ∀fn fg.
    (fg_add_function_node0 fn fg).function_map =
    if wf_fg_fn fn fg
    then
      fg.function_map |+ (INR (CARD (nodes fg.underlying_graph)),fn)
    else
      fg.function_map
Proof
  rpt strip_tac
  >> gvs[fg_add_function_node0_def]
  >> Cases_on ‘wf_fg_fn fn fg’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Theorem describing how the edges are updated when adding a function node   *)
(* -------------------------------------------------------------------------- *)
Theorem fsgedges_fg_add_function_node0_underlying_graph:
  ∀fn fg.
    wffactor_graph fg ⇒
    fsgedges (fg_add_function_node0 fn fg).underlying_graph =
    if wf_fg_fn fn fg
    then
      fsgedges fg.underlying_graph ∪
               {{v; (INR (CARD (nodes fg.underlying_graph)))} | MEM v (FST fn)}
    else
      fsgedges fg.underlying_graph
Proof
  rpt strip_tac
  >> Cases_on ‘¬wf_fg_fn fn fg’ >- gvs[fg_add_function_node0_def]
  >> gvs[]
  >> gvs[fg_add_function_node0_def]
  >> gvs[fsgedges_fg_add_edges_for_function_node0]
  >> DEP_PURE_ONCE_REWRITE_TAC[fsgedges_fg_add_edges_for_function_node0]
  >> conj_tac
  >- (rw[]
      >- (gvs[wf_fg_fn_def]
          >> CCONTR_TAC >> gvs[]
          >> first_x_assum drule >> strip_tac
          >> gvs[inr_in_nodes_underlying_graph])
      >- (CCONTR_TAC >> gvs[]
          >> gvs[wf_fg_fn_def]
         )
      >- gvs[wf_fg_fn_def, SUBSET_DEF]
      >- (disj2_tac
          >> gvs[inr_in_nodes_underlying_graph]
         )
     )
  >> gvs[fsgedges_addNode]
  >> rw[]
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
  >> drule (cj 5 (iffLR wffactor_graph_def)) >> strip_tac
  >> pop_assum (fn th => drule (iffLR th)) >> strip_tac
  >> gvs[INSERT2_lemma]
QED

(* -------------------------------------------------------------------------- *)
(* Adding edges to a graph maintains the order of the graph                   *)
(* -------------------------------------------------------------------------- *)
Theorem order_fg_add_edges_for_function_node0[simp]:
  ∀fg vs.
    order (fg_add_edges_for_function_node0 vs fg) = order fg
Proof
  rpt strip_tac
  >> gvs[fg_add_edges_for_function_node0_def]
QED

(* -------------------------------------------------------------------------- *)
(* Adding a function node to a factor graph maintains well-formedness         *)
(*                                                                            *)
(* We require that the original graph is well-formed, the function being      *)
(* added outputs values in the range [0,1], and that the variables associated *)
(* with the newly added function are valid nodes and variable nodes.          *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_function_node0_wf[simp]:
  ∀fg fn.
    wffactor_graph fg ⇒
    wffactor_graph (fg_add_function_node0 fn fg)
Proof
  rpt strip_tac
  (* Handle situation in which input function is invalid*)
  >> Cases_on ‘¬wf_fg_fn fn fg’
  >- gvs[fg_add_function_node0_def]
  >> gvs[]
  (* Prove each well-formedness property indivudually *)
  >> simp[wffactor_graph_def] >> rpt conj_tac
  (* Bipartiteness is retained *)
  >- (drule (cj 1 (iffLR wffactor_graph_def)) >> disch_tac
      >> simp[fg_add_function_node0_def]
      (* Is there a nicer way to do this? Key: 842859 *)
      >> Cases_on ‘(INR (CARD (nodes (fsgAddNode (INR (CARD (nodes fg.underlying_graph))) fg.underlying_graph)) − 1) ∈ INR (CARD (nodes fg.underlying_graph)) INSERT fg.function_nodes ∧ ∀x. MEM x (FST fn) ⇒ x ∈ nodes (fsgAddNode (INR (CARD (nodes fg.underlying_graph))) fg.underlying_graph) ∧ x ∉ INR (CARD (nodes fg.underlying_graph)) INSERT fg.function_nodes)’
      >- (DEP_PURE_ONCE_REWRITE_TAC[gen_partite_ea_fg_add_edges_for_function_node0]
          >> (conj_tac >- gvs[]) >> pop_assum kall_tac
          >> gvs[gen_bipartite_ea_fsgAddNode]
          >> rw[]
          >- (irule gen_bipartite_ea_insert_new_node
              >> rw[]
              >> CCONTR_TAC
              >> gvs[]
              >> drule alledges_valid >> strip_tac
              >> gvs[edges_equal]
              >> gvs[inr_in_nodes_underlying_graph]
             )
          >> gvs[DELETE_INSERT]
          >> DEP_PURE_ONCE_REWRITE_TAC[DELETE_NON_ELEMENT_RWT]
          >> gvs[]
         )
      >> qmatch_asmsub_abbrev_tac ‘¬(last_node_is_function_node ∧
                                     all_input_nodes_are_valid_variable_nodes)’
      >> fs[]
      (* Prove contradiction in the case where the last node is not a function
         node *)
      >- (unabbrev_all_tac
          >> gvs[]
          >> qmatch_asmsub_abbrev_tac ‘if b then _ else _’
          >> Cases_on ‘b’ >> gvs[]
          >> gvs[inr_in_nodes_underlying_graph]
         )
      (* Prove contradiction in the case where there is an invalid variable
         node in the input to fn *)
      >- (unabbrev_all_tac
          >> gnvs[]
          >> gvs[]
          (* We have an invalid variable node in the input to fn because it is
             not in the underlying graph. *)
          >- gvs[wf_fg_fn_def]
          (* We have an invalid variable node in the input to fn because it is
             the newest node added, and thus is only just out of bounds of the
             underlying graph*)
          >- (gvs[wf_fg_fn_def]
              >> first_x_assum drule >> strip_tac
              >> gvs[inr_in_nodes_underlying_graph]
             )
          (* *)
          >- gvs[wf_fg_fn_def]
         )
     )
  (* Domain of function map is correct *)
  >- (gvs[wffactor_graph_def, fg_add_function_node0_def])
  (* All the functions are probability functions*)
  >- (rpt strip_tac
      >> Cases_on ‘f ∈ fg.function_nodes’
      >- (gvs[fg_add_function_node0_function_nodes,
              fg_add_function_node0_function_map]
          >> DEP_PURE_ONCE_REWRITE_TAC[NOT_EQ_FAPPLY]
          >> drule (cj 3 (iffLR wffactor_graph_def)) >> strip_tac
          >> gvs[]
          >> CCONTR_TAC
          >> gvs[]
         )
      >- (gvs[fg_add_function_node0_function_nodes,
              fg_add_function_node0_function_map]
          >> gvs[wf_fg_fn_def]
          >> namedCases_on ‘fn’ ["f_args f_func"]
          >> gvs[]
         )
     )
  (* All the functions have only variable nodes as inputs *)
  >- (gen_tac >> disch_tac >> gen_tac >> disch_tac
      >> gvs[fg_add_function_node0_def, wf_fg_fn_def]
      (* The current function was added just now by fg_add_function_node0 *)
      >- (CCONTR_TAC >> gvs[]
          >> first_x_assum drule >> strip_tac
          >> gvs[inr_in_nodes_underlying_graph])
      (* The current function node was already present before applying
         fg_add_function_node0 *)
      >- (DEP_PURE_ONCE_REWRITE_TAC[NOT_EQ_FAPPLY]
          >> conj_tac
          >- (CCONTR_TAC >> gvs[])
          >> pop_assum mp_tac
          >> DEP_PURE_ONCE_REWRITE_TAC[NOT_EQ_FAPPLY]
          >> conj_tac
          >- (CCONTR_TAC >> gvs[])
          >> drule (cj 4 (iffLR wffactor_graph_def)) >> strip_tac
          >> pop_assum drule >> strip_tac
          >> gvs[]
          >> rw[]
          >> CCONTR_TAC >> gvs[]
         )
     )
  >- (rw[]
      >> REVERSE EQ_TAC
      (* Prove that if we have f and v such that the variable node is an input
         to the funciton node, then the new graph has an edge between them *)
      >- (rw[]
          >> gnvs[fg_add_function_node0_def]
          >> Cases_on ‘f = v’ >- gvs[]
          >> DEP_PURE_ONCE_REWRITE_TAC[in_fsgedges_fg_add_edges_for_function_node0]
          >> conj_tac >- gvs[]
          >> gnvs[]
          >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
          >> Cases_on ‘b’ >> gnvs[inr_in_nodes_underlying_graph]
          >> qmatch_goalsub_abbrev_tac ‘b ∨ _’
          >> Cases_on ‘b’ >> gnvs[]
          >> Cases_on ‘f = INR (CARD (nodes fg.underlying_graph))’
          >- (qexists ‘v’
              >> gvs[swap_edge]
             )
          >> Cases_on ‘v = INR (CARD (nodes fg.underlying_graph))’
          >- gvs[]
          >> ‘F’ suffices_by gvs[]
          >> qpat_x_assum ‘MEM _ _’ mp_tac
          >> DEP_PURE_ONCE_REWRITE_TAC[NOT_EQ_FAPPLY]
          >> conj_tac >- gvs[inr_in_nodes_underlying_graph]
          >> strip_tac
          >> gvs[]
          >> drule (cj 5 (iffLR wffactor_graph_def)) >> strip_tac
          >> metis_tac[]
         )
      (* Prove that if we have an edge in the new graph, then f and v are
        valid function/variable nodes such that the variable node is an input
        to the function node*)
      >- (rw[]
          >> gvs[fsgedges_fg_add_function_node0_underlying_graph]
          (* The edge is in the underlying graph *)
          >- (drule alledges_valid >> strip_tac
              (* We have either a ∈ function_nodes or b ∈ function_nodes *)
              >> sg ‘¬(a ∉ fg.function_nodes ∧ b ∉ fg.function_nodes)’
              >- (CCONTR_TAC >> gvs[]
                  >> metis_tac[wffactor_graph_edges_in_not_in]
                 )
              (* Without loss of generality, we can take a ∈ function_nodes *)
              >> wlog_tac ‘a ∈ fg.function_nodes’ [‘a’, ‘b’]
              >- (first_x_assum irule
                  >> qexistsl [‘b’, ‘a’]
                  >> gvs[]
                  >> gvs[INSERT2_lemma]
                 )
              >> gvs[]
              (* If a ∈ function_nodes, then b ∉ function_nodes *)
              >> sg ‘b ∉ fg.function_nodes’
              >- metis_tac[wffactor_graph_edges_in_not_in]
              >> qexistsl [‘a’, ‘b’]
              >> gvs[]
              >> gvs[fg_add_function_node0_def]
              >> conj_tac
              >- (CCONTR_TAC >> gvs[]
                  >> gvs[inr_in_nodes_underlying_graph]
                 )
              >> gvs[cj 5 (iffLR wffactor_graph_def)]
              >> gvs[INSERT2_lemma]
             )
          (* The edge is newly added *)
          >- (qexistsl [‘INR (CARD (nodes fg.underlying_graph))’, ‘v’]
              >> gvs[INSERT2_lemma]
              >> rpt conj_tac
              >- gvs[fg_add_function_node0_def]
              >- gvs[fg_add_function_node0_def, wf_fg_fn_def]
              >- gvs[fg_add_function_node0_def]
              >- (gvs[fg_add_function_node0_def, wf_fg_fn_def]
                  >> CCONTR_TAC >> gvs[]
                  >> first_x_assum drule >> strip_tac
                  >> gvs[inr_in_nodes_underlying_graph]
                 )
              >- gvs[fg_add_function_node0_def]
             )
         )
     )
  (* The nodes of our new graph are of the correct form. *)
  >- (gvs[fg_add_function_node0_def]
      >> drule (cj 6 (iffLR wffactor_graph_def)) >> strip_tac
      >> gvs[order_fsgAddNode]
      >> gvs[EXTENSION] >> rw[]
      >> Cases_on ‘x’ >> gvs[]
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
