(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory bcjr_factor_graph

Ancestors binary_symmetric_channel combin donotexpand extreal factor_graph finite_map fsgraph fundamental genericGraph map_decoder_convolutional_code marker message_passing list range rich_list partite_ea pred_set prim_rec probability recursive_parity_equations state_machine tree wf_state_machine

Libs extreal_to_realLib donotexpandLib map_decoderLib realLib dep_rewrite ConseqConv;

(* -------------------------------------------------------------------------- *)
(* Main reference:"Modern Coding Theory" by Tom Richardson and Rüdiger        *)
(* Urbanke.                                                                   *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* The factor graph corresponding to a state machine.                         *)
(*                                                                            *)
(* P(x_i | y) = Σ P(x,σ|y)                                                    *)
(*            = Σ (P(x,σ,y) / P(y))                                           *)
(*            ∝ Σ P(x,σ,y)                                                   *)
(*            ∝ Σ P(y|x,σ) P(x,σ)                                            *)
(*            ∝ Σ P(y|x) P(x|σ) P(σ)                                         *)
(*            ∝ Σ P(y|x) P(x|σ) P(σ_0) (Π P(σ_(i+1), σ_i))                   *)
(*            ∝ Σ P(y|x) (Π P(x_(i+1)|σ_i, σ_(i+1))) P(σ_0)                  *)
(*                        (Π P(σ_(i+1), σ_i))                                 *)
(*     Not a tree: P(x_(i+1)|σ_i,σ_(i+1)) connects to σ_i and to σ_(i+1)      *)
(*     P(σ_(i+1),σ_i) also connects to these variables, thus creating a       *)
(*     loop. Should really combine these,                                     *)
(*            (Above was attempt 1: try different approach)                   *)
(*            ∝ Σ P(y|x,σ) P(x,σ)     (continued)                            *)
(*            ∝ Σ P(y|x) P(x,σ)                                              *)
(*            ∝ Σ P(y|x) P(                                                  *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*            ∝ Σ P(y|x) P(σ_0) Π P(x_(i+1),σ_(i+1)|x_i,σ_i) P(x_(i+1)       *)
(*                                                                           *)
(*                                                                            *)
(*      Note that each upwards branch is actually several different           *)
(*        branches: one per output bit which is produced in this step.        *)
(*        The P(x_1) component is only a part of the systematic component.    *)
(*                                                                            *)
(*                                                                            *)
(*           P(x_1)P(y_1|x_1)  P(x_2)P(y_2|x_2)           P(x_n)P(y_n|x_n)    *)
(*                  #                 #                          #            *)
(*                  |                 |                          |            *)
(*                  o x_1             o x_2                      o            *)
(*          σ_0     |       σ_1       |       σ_2                |     σ_n    *)
(*    # ---- o ---- # ------ o ------ # ------ o ------ ... ---- # ---- o     *)
(*  P(σ_0)   P(x_1,σ_1|x_0,σ_0) P(x_2,σ_2|x_1,σ_1)  P(x_n,σ_n|x_(n-1),σ_(n-1))*)
(*                                                                            *)
(*                                                                            *)
(*              σ_0                                                           *)
(*        # ---- o ---- #                                                     *)
(*      P(σ_0)                                                                *)
(*                                                                            *)
(* Based on "Modern Coding Theory" by Tom Richardson and Rüdiger Urbanke,     *)
(* with modifications to work with arbitrary state machines rather than just  *)
(* recursive convolutional codes.                                             *)
(*                                                                            *)
(* Number of variable nodes in this state machine:                            *)
(* - We start in state 0, and each input bit updates the state by 1, so we    *)
(*   have n+1 state variable nodes                                            *)
(*                                                                            *)
(* This seems like a cool formalism approach. In particular, formalize so     *)
(* that BCJR works for a general state machine. Then try to formalize the     *)
(* turbo code BCJR to use this.                                               *)
(*                                                                            *)
(*                                                                            *)
(* TODO: implement this                                                       *)
(* -------------------------------------------------------------------------- *)
(*Definition state_machine_factor_graph_def:
  state_machine_factor_graph m = fg_add_n_variable_nodes () fg_empty
End*)

(* -------------------------------------------------------------------------- *)
(* Decode assuming transmission over a binary symmetric channel               *)
(*                                                                            *)
(* m: the state machine used to encode the message                            *)
(* cs: the message to decode (bs represents the original message, and ds      *)
(*     represents the decoded message)                                        *)
(* p: the probability of an error when a bit is sent over the binary          *)
(*    symmetric channel.                                                      *)
(*                                                                            *)
(* TODO: implement this                                                       *)
(* -------------------------------------------------------------------------- *)
(*Definition BCJR_decode_def:
  BCJR_decode m cs p = ARB
                       (* TODO_message_passing applied to factor graph *)
End*)

(* -------------------------------------------------------------------------- *)
(* Add the function nodes corresponding to the initial input probabilities    *)
(* and errors in the systematic bits.                                         *)
(*                                                                            *)
(* n: the number of bits as input to the convolutional code                   *)
(* p: the probability of an error                                             *)
(* i: the current node being added. Initially should be 0, ranges up to n.    *)
(*    terminates at n or above.                                               *)
(* prior: a list of the prior probabilities of each input bit being 1         *)
(* ds_s: the received systematic bits                                         *)
(* fg: the factor graph we are modifying (fg is the last argument to make it  *)
(*     easier to compose this function with other functions)                  *)
(* -------------------------------------------------------------------------- *)
Definition rcc_factor_graph_add_func_nodes_input_sys_def:
  rcc_factor_graph_add_func_nodes_input_sys n p i prior ds_s fg =
  if n ≤ i
  then
    fg
  else
    (rcc_factor_graph_add_func_nodes_input_sys n p (i + 1) prior ds_s)
    (fg_add_function_node
     {INR i}
     (λval_map.
        (EL i prior) *
        (if [EL i ds_s] ≠ val_map ' (INR i) then p else 1 - p))
     fg)
Termination
  WF_REL_TAC ‘measure (λ(n,p,i,prior,ds_s,fg). n - i)’
End

(* -------------------------------------------------------------------------- *)
(* Add the function nodes corresponding to errors in the encoded bits         *)
(*                                                                            *)
(* n: the number of bits as input to the convolutional code                   *)
(* p: the probability of an error                                             *)
(* i: the current node being added. Initially should be 0, ranges up to n-1,  *)
(*    terminates at n or above.                                               *)
(* ds_p: the received parity bits                                             *)
(* fg: the factor graph we are modifying (fg is the last argument to make it  *)
(*     easier to compose this function with other functions)                  *)
(* -------------------------------------------------------------------------- *)
Definition rcc_factor_graph_add_func_nodes_enc_def:
  rcc_factor_graph_add_func_nodes_enc n p i ds_p fg =
  if n ≤ i
  then
    fg
  else
    (rcc_factor_graph_add_func_nodes_enc n p (i+1) ds_p)
    (fg_add_function_node
     {INR (n + i)}
     (λval_map. if [EL i ds_p] ≠ val_map ' (INR (n + i)) then p else 1 - p)
     fg)
Termination
  WF_REL_TAC ‘measure (λ(n,p,i,ds_s,fg). n - i)’
End

(* -------------------------------------------------------------------------- *)
(* Add the function node corresponding to the initial state. Probability 1    *)
(* if the initial state takes the appropriate initial value, and probability  *)
(* 0 otherwise.                                                               *)
(*                                                                            *)
(* n: length of input to recursive convolutional code                         *)
(* ts: initial state of recursive convolutional code                          *)
(* fg: factor graph                                                           *)
(* -------------------------------------------------------------------------- *)
Definition rcc_factor_graph_add_func_node_state_initial_def:
  rcc_factor_graph_add_func_node_state_initial n ts fg =
  fg_add_function_node ({INR (2 * n)})
                       (λval_map.
                          if val_map ' (INR (2 * n)) = ts then 1 else 0
                       )
                       fg
End

(* -------------------------------------------------------------------------- *)
(* The function represented by the function node which represents a           *)
(* transition between states.                                                 *)
(*                                                                            *)
(* n: length of input to recursive convolutional code                         *)
(* (ps,qs): parity equations for recursive convolutional code                 *)
(* i: the index of the function node. 0 represents the function node between  *)
(*    the initial state and the first state, 1 represents the function node   *)
(*    between the first and second states, etc.                               *)
(* -------------------------------------------------------------------------- *)
Definition func_node_state_fn_def:
  func_node_state_fn n (ps,qs) i =
  λval_map : unit + num |-> bool list.
    if encode_recursive_parity_equation_state
       (ps,qs) (val_map ' (INR (2*n + i))) (val_map ' (INR i)) =
       (val_map ' (INR (2*n + i + 1)))
       ∧ encode_recursive_parity_equation
         (ps,qs) (val_map ' (INR (2*n + i))) (val_map ' (INR i)) =
         val_map ' (INR (n + i))
    then
      1 : extreal
    else
      0 : extreal
End

(* -------------------------------------------------------------------------- *)
(* The indices of the nodes which are adjacent to the function node which     *)
(* represents a transition between states.                                    *)
(*                                                                            *)
(* n: the length of the input to the recursive convolutional code             *)
(* i: the index of the current function node.                                 *)
(* -------------------------------------------------------------------------- *)
Definition func_node_state_adjacent_nodes_def:
  func_node_state_adjacent_nodes n i =
  IMAGE INR ({i; n + i; 2 * n + i; 2 * n + i + 1}) : (unit + num -> bool)
End

(* -------------------------------------------------------------------------- *)
(* Add the function nodes corresponding to the state transitions              *)
(*                                                                            *)
(* n: the number of bits as input to the convolutional code                   *)
(* i: the current node being added. Initially should be 0, ranges up to n-1   *)
(* fg: the factor graph we are modifying (fg is the last argument to make it  *)
(*     easier to compose this function with other functions)                  *)
(* -------------------------------------------------------------------------- *)
Definition rcc_factor_graph_add_func_nodes_state_def:
  rcc_factor_graph_add_func_nodes_state n (ps,qs) ts i fg =
  if n ≤ i
  then
    fg
  else
    (rcc_factor_graph_add_func_nodes_state n (ps,qs) ts (i + 1))
    (fg_add_function_node
     (func_node_state_adjacent_nodes n i)
     (func_node_state_fn n (ps,qs) i)
     fg
    )
Termination
  WF_REL_TAC ‘measure (λ(n,(ps,qs),ts,i,fg). n + 1 - i)’
End

(* -------------------------------------------------------------------------- *)
(* The factor graph for a recursive systematic convolutional code with one    *)
(*   set of parity equations.                                                 *)
(*                                                                            *)
(*                                                     P(b_{n-1}) *           *)
(*          P(b_0)P(d_0|b_0)    P(b_1)P(d_1|b_1)       P(d_{n-1}|b_{n-1})     *)
(*                 #                 #                          #             *)
(*                 |                 |                          |             *)
(*                 o b_0             o b_1              b_{n-1} o             *)
(* P(σ_0)  σ_0     |       σ_1       |       σ_2                |    σ_{n}    *)
(*   # ---- o ---- # ------ o ------ # ------ o ------ ... ---- # ---- o      *)
(*          P(cp_0,σ_1|       P(cp_1,σ_2|                P(cpn-1,σn|          *)
(*                 b_0,σ_0)         b_1,σ_1)                   bn-1,σn-1)     *)
(*                 |                 |                          |             *)
(*                 o cp_0            o cp_1                     o cp_{n-1}    *)
(*                 |                 |                          |             *)
(*                 #                 #                          #             *)
(*            P(dp_0|cp_0)        P(cp_1|b_1)             P(cp_{n-1}|b_{n-1}) *)
(*                                                                            *)
(*                                                                            *)
(* The following ranges are inclusive:                                        *)
(*                                                                            *)
(* The n variable nodes relating to the inputs b_i have labels 0 through n-1  *)
(* The n variable nodes relating to the encoded inputs cp_i have labels       *)
(*   n through 2n-1                                                           *)
(* The (n + 1) variable nodes relating to the states σ_i have labels 2n       *)
(*   through 3n                                                               *)
(*                                                                            *)
(* The n function nodes relating to the probability of d_i given b_i have     *)
(*   labels 3n + 1 through 4n                                                 *)
(* The n function nodes relating to the probability of dp_i given cp_i have   *)
(*   labels 4n + 1 through 5n                                                 *)
(* The 1 function node which gives us the probability of the initial state    *)
(*   has the label 5n + 1.                                                    *)
(* The n function nodes relating to the probability of the next state and     *)
(*   output given the current state have labels 5n + 2 through 6n + 1         *)
(* -------------------------------------------------------------------------- *)
Definition rcc_factor_graph_def:
  rcc_factor_graph n p (ps,qs) ts prior (ds_s,ds_p) =
  ((rcc_factor_graph_add_func_nodes_state n (ps,qs) ts 0)
   ∘ (rcc_factor_graph_add_func_node_state_initial n ts)
   ∘ (rcc_factor_graph_add_func_nodes_enc n p 0 ds_p)
   ∘ (rcc_factor_graph_add_func_nodes_input_sys n p 0 prior ds_s)
   ∘ (fg_add_n_variable_nodes (n + 1) (LENGTH ts))
   ∘ (fg_add_n_variable_nodes n 1)
   ∘ (fg_add_n_variable_nodes n 1))
  fg_empty
End

(* -------------------------------------------------------------------------- *)
(* Given a received message ds, decode it to the most likely original message *)
(*                                                                            *)
(* p: the probability of error when a bit is sent over the noisy channel      *)
(* (ps,qs): the numerator and denominator parity equations for the recursive  *)
(*          convolutional code (lists of booleans)                            *)
(* ts: the initial state for the recursive convolutional code                 *)
(* ds: the received string to decode                                          *)
(* -------------------------------------------------------------------------- *)
Definition rcc_bcjr_fg_decode_def:
  rcc_bcjr_fg_decode p (ps,qs) ts ds =
  let
    m = LENGTH ds;
    n = m DIV 2;
    ds_s = TAKE n ds;
    ds_p = DROP n ds;
    prior = REPLICATE n (1 / &n);
    fg = rcc_factor_graph n p (ps,qs) ts prior (ds_s,ds_p);
  in
    MAP
    (λi. argmax_bool (λb. sp_output fg (INR i) ' (FUN_FMAP (λdst. [b]) {INR i}))
    ) (COUNT_LIST n)
End

Theorem var_nodes_fg_add_function_node0:
  ∀inputs fn fg.
    wffactor_graph fg ⇒
    var_nodes (fg_add_function_node0 inputs fn fg) = var_nodes fg
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[fg_add_function_node0_def]
  >> simp[]
  >> rw[]
  >> simp[EXTENSION]
  >> gen_tac
  >> REVERSE EQ_TAC >> simp[]
  >> strip_tac
  >> simp[]
QED

Theorem var_nodes_fg_add_function_node[simp]:
  ∀inputs fn fg.
    var_nodes (fg_add_function_node inputs fn fg) = var_nodes fg
Proof
  rpt gen_tac
  >> simp[fg_add_function_node_def, var_nodes_fg_add_function_node0]
  >> simp[get_underlying_graph_def, get_function_nodes_def]
QED

Theorem var_nodes_rcc_factor_graph_add_func_nodes_state[simp]:
  ∀n ps qs ts i fg.
    var_nodes (rcc_factor_graph_add_func_nodes_state n (ps,qs) ts i fg) =
    var_nodes fg
Proof
  (* Our base case is when i gets to n + 1. We then want to induct downwards on
     i. So we induct on n + 1 - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n + 1 - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> ‘n ≤ i - 1’ by decide_tac
      >> simp[LESS_EQ]
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
      >> simp[]
     )
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
  >> qmatch_goalsub_abbrev_tac ‘rcc_factor_graph_add_func_nodes_state _ _ _ _ fg'’
  >> last_x_assum (qspecl_then [‘fg'’, ‘i + 1’, ‘n’, ‘ps’, ‘qs’, ‘ts’] assume_tac)
  >> Cases_on ‘n ≤ i’ >> simp[]
  >> Q.UNABBREV_TAC ‘fg'’
  >> simp[]
QED

Theorem var_nodes_rcc_factor_graph_add_func_node_state_initial[simp]:
  ∀n ts fg.
    var_nodes (rcc_factor_graph_add_func_node_state_initial n ts fg)
    = var_nodes fg
Proof
  rpt gen_tac
  >> simp[rcc_factor_graph_add_func_node_state_initial_def]
QED

Theorem var_nodes_rcc_factor_graph_add_func_nodes_enc[simp]:
  ∀n p i ds_p fg.
    var_nodes (rcc_factor_graph_add_func_nodes_enc n p i ds_p fg) = var_nodes fg
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> ‘n ≤ i’ by decide_tac
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_enc_def]
      >> simp[]
     )
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_enc_def]
  >> rw[]
QED

Theorem var_nodes_rcc_factor_graph_add_func_nodes_input_sys[simp]:
  ∀n p i prior ds_s fg.
    var_nodes (rcc_factor_graph_add_func_nodes_input_sys n p i prior ds_s fg)
    = var_nodes fg
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_input_sys_def]
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_input_sys_def]
  >> simp[]
QED

Theorem var_nodes_rcc_factor_graph[simp]:
  ∀n p ps qs ts prior ds_s ds_p.
    var_nodes (rcc_factor_graph n p (ps, qs) ts prior (ds_s, ds_p)) =
    IMAGE INR (count (3 * n + 1))
Proof
  rpt gen_tac
  >> PURE_REWRITE_TAC[rcc_factor_graph_def]
  >> simp[o_DEF]
  >> simp[fg_add_n_variable_nodes_concat]
  >> simp[var_nodes_fg_add_n_variable_nodes]
  >> PURE_ONCE_REWRITE_TAC[GSYM IMAGE_UNION]
  >> simp[]
  >> Cases_on ‘n = 0’ >- simp[range_def, count_def]
  >> simp[range_union_swapped, range_0]
QED

Theorem order_rcc_factor_graph_add_func_nodes_state:
  ∀n ps qs ts i fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    order (get_underlying_graph (rcc_factor_graph_add_func_nodes_state
                                 n (ps, qs) ts i fg))
    = order (get_underlying_graph fg) + (n - i)
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
  >> Cases_on ‘n ≤ i’
  >- (‘n = i’ by (irule LESS_EQUAL_ANTISYM >> simp[])
      >> gvs[])
  >> simp[]
  (* The inductive hypothesis has been applied, and we no longer need it *)
  >> qpat_x_assum ‘∀fg i n ps qs ts. _ ⇒ _ ⇒ _’ kall_tac
  (* *)
  >> PURE_ONCE_REWRITE_TAC[order_fg_add_function_node]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’ >> simp[]
  >> pop_assum mp_tac
  >> PURE_REWRITE_TAC[Abbrev_def, EQ_CLAUSES, IMP_CLAUSES, NOT_CLAUSES]
  >> qpat_x_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[func_node_state_adjacent_nodes_def]
QED

Theorem get_function_nodes_rcc_factor_graph_add_func_nodes_state:
  ∀n ps qs ts i fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    get_function_nodes (rcc_factor_graph_add_func_nodes_state n (ps, qs) ts i fg)
    = (IMAGE INR (range
                  (order (get_underlying_graph fg))
                  (order (get_underlying_graph fg) + (n - i))
                 )
      ) ∪ get_function_nodes fg
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac >> strip_tac
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
      >> simp[]
      >> qpat_x_assum ‘0 = n - i’ (fn th => simp[GSYM th]))
  >> rpt gen_tac >> strip_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
  >> Cases_on ‘n ≤ i’ >- gvs[]
  >> simp[]
  (* We have applied the inductive hypothesis and so we no longer need it *)
  >> qpat_x_assum ‘∀fg i n ps qs ts. _ ⇒ _’ kall_tac
  (* *)
  >> PURE_ONCE_REWRITE_TAC[order_fg_add_function_node]
  >> qpat_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[func_node_state_adjacent_nodes_def]
  >> PURE_ONCE_REWRITE_TAC[get_function_nodes_fg_add_function_node]
  >> qpat_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[]
  >> simp[EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac >> simp[]
  >- gvs[range_def]
  >- (simp[range_def, gsize_def])
  >> gvs[range_def, gsize_def]
  >> decide_tac
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem get_function_map_fg_add_function_node0:
  ∀inputs fn fg.
    wffactor_graph fg ⇒
    (fg_add_function_node0 inputs fn fg).function_map =
    if
    inputs ⊆ var_nodes fg
    then
      fg.function_map |+
        (INR (order fg.underlying_graph),
         FUN_FMAP fn (var_assignments inputs fg.variable_length_map)
        )
    else
      fg.function_map
Proof
  rpt gen_tac >> strip_tac
  >> REVERSE $ Cases_on ‘inputs ⊆ var_nodes fg’ >> simp[]
  >- simp[fg_add_function_node_def, fg_add_function_node0_def,
          factor_graph_ABSREP]
  >> simp[fg_add_function_node0_def, gsize_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem get_function_map_fg_add_function_node:
  ∀inputs fn fg.
    get_function_map (fg_add_function_node inputs fn fg) =
    if
    inputs ⊆ var_nodes fg
    then
      (get_function_map fg)
      |+ (INR (order (get_underlying_graph fg)),
          FUN_FMAP fn (var_assignments inputs (get_variable_length_map fg)))
    else
      get_function_map fg
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[get_underlying_graph_def]
  >> simp[fg_add_function_node_def, get_function_map_def, get_variable_length_map_def]
  >> simp[get_function_map_fg_add_function_node0]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem FUNION_FUPDATE_SWAP:
  ∀f g x.
    (FST x ∈ FDOM f ⇒ f ' (FST x) = SND x) ⇒
    f ⊌ (g |+ x) = (f |+ x) ⊌ g
Proof
  rpt gen_tac >> strip_tac
  >> Cases_on ‘x’
  >> simp[GSYM fmap_EQ_THM]
  >> conj_tac
  >- (simp[EXTENSION] >> gen_tac >> EQ_TAC >> disch_tac >> gvs[])
  >> gen_tac >> strip_tac
  >- (gvs[]
      >> simp[FUNION_DEF]
      >> Cases_on ‘q = x’ >> simp[FAPPLY_FUPDATE_THM]
      >> gvs[])
  >- (gvs[]
      >> simp[FUNION_DEF, FAPPLY_FUPDATE_THM])
  >> simp[FUNION_DEF, FAPPLY_FUPDATE_THM]
  >> rw[] >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem get_variable_length_map_fg_add_function_node0[simp]:
  ∀inputs fn fg.
    (fg_add_function_node0 inputs fn fg).variable_length_map =
    fg.variable_length_map
Proof
  rpt gen_tac
  >> simp[fg_add_function_node0_def]
  >> rw[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem get_variable_length_map_fg_add_function_node[simp]:
  ∀inputs fn fg.
    get_variable_length_map (fg_add_function_node inputs fn fg) =
    get_variable_length_map fg
Proof
  rpt gen_tac
  >> simp[get_variable_length_map_def,
          get_variable_length_map_fg_add_function_node0,
          fg_add_function_node_def]
QED

Theorem finite_func_node_state_adjacent_nodes[simp]:
  ∀n i.
    FINITE (func_node_state_adjacent_nodes n i)
Proof
  rpt strip_tac
  >> simp[func_node_state_adjacent_nodes_def]
QED

Theorem get_function_map_rcc_factor_graph_add_func_nodes_state:
  ∀n ps qs ts i fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    get_function_map (rcc_factor_graph_add_func_nodes_state n (ps,qs) ts i fg) =
    FUN_FMAP (λfunc_node.
                FUN_FMAP (func_node_state_fn
                          n (ps,qs)
                          (OUTR func_node + i - order (get_underlying_graph fg))
                         ) (var_assignments
                            (func_node_state_adjacent_nodes
                             n (OUTR func_node + i - order (get_underlying_graph fg))
                            ) (get_variable_length_map fg)
                           )
             ) (IMAGE INR (range (order (get_underlying_graph fg))
                                 (order (get_underlying_graph fg) + (n - i))
                          )
               ) ⊌ (get_function_map fg)
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> pop_assum (fn th => assume_tac (GSYM th))
      >> simp[]
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac >> strip_tac
  >> qmatch_abbrev_tac ‘_ = RHS’
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
  >> Cases_on ‘n ≤ i’
  >- (‘F’ suffices_by simp[] >> gvs[])
  (* *)
  >> simp[]
  (* We have now applied the inductive hypothesis, so we no longer need it *)
  >> qpat_x_assum ‘∀fg i n ps qs ts. _ ⇒ _ ⇒ _’ kall_tac
  (* Simplify *)
  >> simp[order_fg_add_function_node]
  >> ‘func_node_state_adjacent_nodes n i ⊆ IMAGE INR (count (3 * n + 1))’
    by (simp[SUBSET_DEF, func_node_state_adjacent_nodes_def]
        >> gen_tac >> strip_tac >> simp[])
  >> simp[]
  (* Move the newly added function mapping into the collection of function
     mappings *)
  >> simp[get_function_map_fg_add_function_node]
  >> DEP_PURE_ONCE_REWRITE_TAC[FUNION_FUPDATE_SWAP]
  >> conj_tac
  >- (strip_tac
      >> gvs[]
      (* The newly added node isn't already in the collection of function
         mappings, which is why the precondition of FUNION_FUPDATE_SWAP holds:
         we don't need to worry about proving f ' (FST x) = SND x in the
         precondition of FUNION_FUPDATE_SWAP *)
      >> ‘F’ suffices_by simp[]
      >> gvs[range_def]
     )
  (* Now that we have rewritten so that the newly added node is being added to
     the collection of function mappings, we just need to prove that the
     collections of function mappings on the LHS and RHS are equivalent. *)
  >> Q.UNABBREV_TAC ‘RHS’
  >> cong_tac (SOME 1)
  (* Give things simple names *)
  >> qmatch_abbrev_tac ‘f |+ x = g’
  (* *)
  >> simp[GSYM fmap_EQ_THM]
  (* *)
  >> conj_tac
  >- (unabbrev_all_tac >> simp[EXTENSION] >> gen_tac >> EQ_TAC >> disch_tac
      >> gvs[range_def])
  >> gen_tac
  >> Cases_on ‘x’
  >> simp[FDOM_FUPDATE]
  >> strip_tac
  >- (simp[]
      >> sg ‘FDOM r = FDOM (g ' q)’
      >- (gvs[Abbrev_def]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- simp[range_def]
          >> simp[]
         )
      >> simp[]
      >> gen_tac >> strip_tac
      >> gvs[Abbrev_def]
      >> simp[cj 2 FUN_FMAP_DEF]
      >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
      >> conj_tac
      >- simp[range_def]
      >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
      >> conj_tac
      >- (conj_tac >- simp[]
          >> gvs[])
      >> simp[])
  >> sg ‘FDOM ((f |+ (q,r)) ' x') = FDOM (g ' x')’
  >- (Cases_on ‘x' = q’
      >- (simp[]
          >> gvs[Abbrev_def]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- (simp[] >> gvs[range_def])
          >> simp[FDOM_FMAP])
      >> simp[FAPPLY_FUPDATE_THM]
      >> gvs[Abbrev_def]
      >> simp[FUN_FMAP_DEF]
      >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
      >> conj_tac
      >- (simp[] >> gvs[range_def])
      >> simp[])
  >> simp[]
  >> gen_tac >> strip_tac
  >> Cases_on ‘x' = q’
  >- (simp[]
      >> gvs[Abbrev_def]
      >> simp[FUN_FMAP_DEF]
      >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
      >> conj_tac
      >- simp[range_def]
      >> simp[FUN_FMAP_DEF])
  >> simp[FAPPLY_FUPDATE_THM]
  >> gvs[Abbrev_def]
  >> simp[FUN_FMAP_DEF]
  >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
  >> conj_tac
  >- (simp[]
      >> qpat_x_assum ‘x ∈ FDOM (FUN_FMAP _ _ ' _)’ mp_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
      >> conj_tac
      >- (simp[] >> gvs[range_def])
      >> simp[]
     )
  >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
  >> conj_tac
  >- (simp[] >> gvs[range_def])
  >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
  >> conj_tac
  >- (simp[]
      >> qpat_x_assum ‘x ∈ FDOM (FUN_FMAP _ _ ' _)’ mp_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
      >> conj_tac
      >- (simp[] >> gvs[range_def])
      >> simp[])
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* An expression for the variable nodes as constructed by rcc_factor_graph    *)
(* -------------------------------------------------------------------------- *)
Theorem var_nodes_rcc_factor_graph_variable_nodes[simp]:
  ∀n ts.
    var_nodes
    (fg_add_n_variable_nodes
     (n + 1) (LENGTH ts)
     (fg_add_n_variable_nodes
      n 1
      (fg_add_n_variable_nodes n 1 fg_empty)
     )
    ) = IMAGE INR (count (3 * n + 1))
Proof
  rpt gen_tac
  >> simp[var_nodes_fg_add_n_variable_nodes]
  >> simp[range_def]
  >> simp[EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac >> gvs[]
QED

Theorem nodes_rcc_factor_graph_add_func_nodes_state:
  ∀n ps qs ts i fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    nodes (get_underlying_graph
           (rcc_factor_graph_add_func_nodes_state n (ps, qs) ts i fg)) =
    IMAGE INR (count (order (get_underlying_graph fg) + (n − i)))
Proof
  rpt gen_tac >> strip_tac
  >> simp[nodes_get_underlying_graph, order_rcc_factor_graph_add_func_nodes_state]
QED

Theorem order_rcc_factor_graph_add_func_node_state_initial:
  ∀n ts fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    order (get_underlying_graph
           (rcc_factor_graph_add_func_node_state_initial n ts fg)) =
    1 + order (get_underlying_graph fg)
Proof
  rpt gen_tac >> strip_tac
  >> PURE_REWRITE_TAC[rcc_factor_graph_add_func_node_state_initial_def,
                      order_fg_add_function_node]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[]
QED

Theorem nodes_rcc_factor_graph_add_func_node_state_initial:
  ∀n ts fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    nodes (get_underlying_graph
           (rcc_factor_graph_add_func_node_state_initial n ts fg)) =
    IMAGE INR (count (order (get_underlying_graph fg) + 1))
Proof
  rpt gen_tac >> strip_tac
  >> simp[nodes_get_underlying_graph,
          order_rcc_factor_graph_add_func_node_state_initial]
QED

Theorem function_nodes_rcc_factor_graph_add_func_node_state_initial:
  ∀n ts fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    get_function_nodes (rcc_factor_graph_add_func_node_state_initial n ts fg) =
    INR (CARD (nodes (get_underlying_graph fg))) INSERT get_function_nodes fg
Proof
  rpt gen_tac >> strip_tac
  >> PURE_REWRITE_TAC[rcc_factor_graph_add_func_node_state_initial_def,
                      get_function_nodes_fg_add_function_node]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[]
QED

Theorem order_rcc_factor_graph_add_func_nodes_enc:
  ∀n p i ds_p fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    order (get_underlying_graph
           (rcc_factor_graph_add_func_nodes_enc n p i ds_p fg)) =
    order (get_underlying_graph fg) + (n - i)
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> gvs[]
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_enc_def]
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_enc_def]
  >> simp[order_fg_add_function_node]
  >> qpat_x_assum ‘var_nodes fg = IMAGE INR _’ mp_tac
  >> simp[EXTENSION]
QED

Theorem nodes_rcc_factor_graph_add_func_nodes_enc:
  ∀n p i ds_p fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    nodes (get_underlying_graph
           (rcc_factor_graph_add_func_nodes_enc n p i ds_p fg)) =
    IMAGE INR (count (order (get_underlying_graph fg) + (n − i)))
Proof
  rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[nodes_get_underlying_graph]
  >> simp[order_rcc_factor_graph_add_func_nodes_enc]
QED

Theorem nodes_diff_get_function_nodes:
  ∀fg.
    nodes (get_underlying_graph fg) DIFF get_function_nodes fg = var_nodes fg
Proof
  gen_tac >> simp[EXTENSION]
QED

Theorem IMAGE_DIFF:
  ∀f : α -> β S1 S2.
    INJ f (S1 ∪ S2) (𝕌(:β)) ⇒
    (IMAGE f S1) DIFF (IMAGE f S2) = IMAGE f (S1 DIFF S2)
Proof
  rpt gen_tac >> strip_tac
  >> simp[EXTENSION]
  >> gen_tac >> EQ_TAC >> disch_tac >> gvs[]
  >- (qexists ‘x'’ >> simp[])
  >> strip_tac
  >- (qexists ‘x'’ >> simp[])
  >> gen_tac >> strip_tac
  >> disch_tac
  >> qpat_x_assum ‘INJ _ _ _’ mp_tac
  >> simp[INJ_DEF]
  >> qexistsl [‘x'’, ‘x''’]
  >> simp[]
  >> disch_tac >> gvs[]
QED

Theorem function_nodes_rcc_factor_graph_add_func_nodes_enc:
  ∀n p i ds_p fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    get_function_nodes (rcc_factor_graph_add_func_nodes_enc n p i ds_p fg) =
    IMAGE INR (range (3 * n + 1) (order (get_underlying_graph fg) + (n − i)))
Proof
  rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[GSYM nodes_diff_var_nodes]
  >> simp[nodes_rcc_factor_graph_add_func_nodes_enc]
  >> DEP_PURE_ONCE_REWRITE_TAC[IMAGE_DIFF]
  >> conj_tac
  >- simp[INJ_INR]
  >> cong_tac (SOME 1)
  >> simp[GSYM range_count_diff]
QED

Theorem order_rcc_factor_graph_add_func_nodes_input_sys:
  ∀n p i prior ds_s fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    order (get_underlying_graph
           (rcc_factor_graph_add_func_nodes_input_sys n p i prior ds_s fg)) =
    order (get_underlying_graph fg) + (n - i)
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> gvs[]
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_input_sys_def]
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_input_sys_def]
  >> simp[]
  >> PURE_ONCE_REWRITE_TAC[order_fg_add_function_node]
  >> qpat_x_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[]
QED

Theorem nodes_rcc_factor_graph_add_func_nodes_input_sys:
  ∀n p i prior ds_s fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    nodes (get_underlying_graph
           (rcc_factor_graph_add_func_nodes_input_sys n p i prior ds_s fg)) =
    IMAGE INR (count (order (get_underlying_graph fg) + (n − i)))
Proof
  rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[nodes_get_underlying_graph]
  >> simp[order_rcc_factor_graph_add_func_nodes_input_sys]
QED

Theorem function_nodes_rcc_factor_graph_add_func_nodes_input_sys:
  ∀n p i prior ds_s fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    get_function_nodes
    (rcc_factor_graph_add_func_nodes_input_sys n p i prior ds_s fg) =
    IMAGE INR (range (3 * n + 1) (order (get_underlying_graph fg) + (n − i)))
Proof
  rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[GSYM nodes_diff_var_nodes]
  >> simp[nodes_rcc_factor_graph_add_func_nodes_input_sys]
  >> DEP_PURE_ONCE_REWRITE_TAC[IMAGE_DIFF]
  >> conj_tac
  >- simp[INJ_INR]
  >> cong_tac (SOME 1)
  >> simp[GSYM range_count_diff]
QED

Theorem order_rcc_factor_graph[simp]:
  ∀n p ps qs ts prior ds_s ds_p.
    order (get_underlying_graph
           (rcc_factor_graph n p (ps, qs) ts prior (ds_s, ds_p))) =
    6 * n + 2
Proof
  rpt gen_tac
  >> simp[rcc_factor_graph_def]
  >> simp[order_rcc_factor_graph_add_func_nodes_state,
          order_rcc_factor_graph_add_func_node_state_initial,
          order_rcc_factor_graph_add_func_nodes_enc,
          order_rcc_factor_graph_add_func_nodes_input_sys]
QED

Theorem nodes_rcc_factor_graph[simp]:
  ∀n p ps qs ts prior ds_s ds_p.
    nodes (get_underlying_graph
           (rcc_factor_graph n p (ps, qs) ts prior (ds_s, ds_p))) =
    IMAGE INR (count (6 * n + 2))
Proof
  rpt gen_tac
  >> simp[nodes_get_underlying_graph]
QED

Theorem get_function_nodes_rcc_factor_graph[simp]:
  ∀n p ps qs ts prior ds_s ds_p.
    get_function_nodes (rcc_factor_graph n p (ps, qs) ts prior (ds_s, ds_p)) =
    IMAGE INR (range (3 * n + 1) (6 * n + 2))
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[GSYM nodes_diff_var_nodes]
  >> simp[]
  >> simp[IMAGE_DIFF, INJ_INR]
  >> simp[GSYM range_count_diff]
QED

Theorem get_variable_length_map_rcc_factor_graph_add_func_nodes_state[simp]:
  ∀n ps qs ts i fg.
    get_variable_length_map
    (rcc_factor_graph_add_func_nodes_state n (ps,qs) ts i fg) =
    get_variable_length_map fg
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> gvs[]
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
  >> simp[]
QED

Theorem get_variable_length_map_rcc_factor_graph_add_func_node_state_initial[simp]:
  ∀n ts fg.
    get_variable_length_map
    (rcc_factor_graph_add_func_node_state_initial n ts fg) =
    get_variable_length_map fg
Proof
  rpt gen_tac
  >> simp[rcc_factor_graph_add_func_node_state_initial_def]
QED

Theorem get_variable_length_map_rcc_factor_graph_add_func_nodes_enc[simp]:
  ∀n p i ds_p fg.
    get_variable_length_map
    (rcc_factor_graph_add_func_nodes_enc n p i ds_p fg) =
    get_variable_length_map fg
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> gvs[]
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_enc_def]
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_enc_def]
  >> simp[]
QED

Theorem get_variable_length_map_rcc_factor_graph_add_func_nodes_input_sys[simp]:
  ∀n p i prior ds_s fg.
    get_variable_length_map
    (rcc_factor_graph_add_func_nodes_input_sys n p i prior ds_s fg) =
    get_variable_length_map fg
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> gvs[]
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_input_sys_def]
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_input_sys_def]
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem variable_length_map_fg_add_variable_node0:
  ∀l fg.
    wffactor_graph fg ⇒
    (fg_add_variable_node0 l fg).variable_length_map =
    fg.variable_length_map |+ (INR (CARD (nodes fg.underlying_graph)),l)
Proof
  rpt gen_tac >> strip_tac
  >> simp[fg_add_variable_node0_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem get_variable_length_map_fg_add_variable_node:
  ∀l fg.
    get_variable_length_map (fg_add_variable_node l fg) =
    get_variable_length_map fg |+ (INR (CARD (nodes (get_underlying_graph fg))),l)
Proof
  rpt gen_tac
  >> simp[get_variable_length_map_def, fg_add_variable_node_def]
  >> simp[factor_graph_ABSREP, fg_add_variable_node0_wf]
  >> simp[variable_length_map_fg_add_variable_node0]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem get_variable_length_map_fg_add_n_variable_nodes:
  ∀n l fg.
    get_variable_length_map (fg_add_n_variable_nodes n l fg) =
    FUN_FMAP
    (λvar_node. l)
    (IMAGE INR (range
                (CARD (nodes (get_underlying_graph fg)))
                (CARD (nodes (get_underlying_graph fg)) + n)
               )
    ) ⊌ get_variable_length_map fg
Proof
  Induct_on ‘n’ >> simp[fg_add_n_variable_nodes_def]
  >> rpt gen_tac
  >> simp[get_variable_length_map_fg_add_variable_node]
  >> simp[GSYM FUNION_FUPDATE_1]
  >> cong_tac (SOME 1)
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM FUN_FMAP_INSERT]
  >> conj_tac
  >- simp[range_def]
  >> PURE_ONCE_REWRITE_TAC[GSYM IMAGE_INSERT]
  >> DEP_PURE_ONCE_REWRITE_TAC[insert_range]
  >> conj_tac >- simp[]
  >> simp[ADD1]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem get_variable_length_map_fg_empty[simp]:
  get_variable_length_map fg_empty = FEMPTY
Proof
  simp[fg_empty_def] >> simp[fg_empty0_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem FUN_FMAP_FUNION:
  ∀f g S1 S2.
    FINITE S1
    ∧ FINITE S2 ⇒
    FUN_FMAP f S1 ⊌ FUN_FMAP g S2 = FUN_FMAP
                                    (λx. if x ∈ S1 then f x else g x)
                                    (S1 ∪ S2)
Proof
  rpt gen_tac >> strip_tac
  >> simp[GSYM fmap_EQ_THM]
  >> gen_tac >> strip_tac
  >> simp[FUNION_DEF, FUN_FMAP_DEF]
QED

Theorem AND_IFF:
  ∀a b.
    a ∧ b ⇔ a ∧ (a ⇒ b)
Proof
  rpt gen_tac >> Cases_on ‘a’ >> simp[]
QED

Theorem get_variable_length_map_rcc_factor_graph_variable_nodes[simp]:
  ∀n ts.
    get_variable_length_map
    (fg_add_n_variable_nodes (n + 1) (LENGTH ts)
                             (fg_add_n_variable_nodes n 1
                                                      (fg_add_n_variable_nodes
                                                       n 1 fg_empty)
                             )
    ) = FUN_FMAP (λvar_node. if OUTR var_node < 2 * n then 1 else LENGTH ts)
                 (IMAGE INR (count (3 * n + 1)))
Proof
  rpt gen_tac
  >> simp[get_variable_length_map_fg_add_n_variable_nodes]
  >> simp[FUN_FMAP_FUNION]
  >> simp[FUN_FMAP_EQ_THM2]
  >> conj_tac
  >- (simp[EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac >> gvs[range_def])
  >> gen_tac >> strip_tac >> simp[] >> gvs[range_def]
QED

Theorem get_variable_length_map_rcc_factor_graph:
  ∀n p ps qs ts prior ds_s ds_p fg.
    get_variable_length_map
    (rcc_factor_graph n p (ps,qs) ts prior (ds_s, ds_p)) =
    FUN_FMAP (λvar_node. if OUTR var_node < 2 * n then 1 else LENGTH ts)
             (IMAGE INR (count (3 * n + 1)))
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_def]
  >> simp[o_DEF]
QED

Theorem get_function_map_rcc_factor_graph_add_func_node_state_initial:
  ∀n ts fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    get_function_map (rcc_factor_graph_add_func_node_state_initial n ts fg) =
    get_function_map fg |+ (INR (CARD (nodes (get_underlying_graph fg))),
                            FUN_FMAP
                            (λval_map. if val_map ' (INR (2 * n)) = ts
                                       then 1 else 0 : extreal)
                            (var_assignments {INR (2 * n)}
                                             (get_variable_length_map fg))
                           )
Proof
  rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_node_state_initial_def]
  >> PURE_ONCE_REWRITE_TAC[get_function_map_fg_add_function_node]
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[gsize_def]
QED

Theorem get_function_map_rcc_factor_graph_add_func_nodes_enc:
  ∀n p i ds_p fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    get_function_map (rcc_factor_graph_add_func_nodes_enc n p i ds_p fg) =
    FUN_FMAP (λfunc_node.
                let
                  j = OUTR func_node + i - order (get_underlying_graph fg);
                in
                  FUN_FMAP (λval_map.
                              if [EL j ds_p] ≠ val_map ' (INR (n + j))
                              then p else 1 - p
                           ) (var_assignments
                              {INR (n + j)} (get_variable_length_map fg)
                             )
             ) (IMAGE INR (range (order (get_underlying_graph fg))
                                 (order (get_underlying_graph fg) + (n - i))
                          )
               ) ⊌ (get_function_map fg)
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> gvs[]
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_enc_def]
      >> simp[]
      >> ‘n - i = 0’ by decide_tac
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_enc_def]
  >> simp[]
  (* Take the newly added function and move it into the first argument to the
     FUNION, so that the LHS becomes closer to the RHS *)
  >> PURE_ONCE_REWRITE_TAC[get_function_map_fg_add_function_node]
  >> qpat_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[]
  >> DEP_PURE_ONCE_REWRITE_TAC[FUNION_FUPDATE_SWAP]
  >> conj_tac
  >- (qmatch_abbrev_tac ‘(this_is_false_because_key_is_not_in_first_fmap ⇒ this_is_irrelevant)’
      >> ‘¬this_is_false_because_key_is_not_in_first_fmap’ suffices_by simp[]
      >> Q.UNABBREV_TAC ‘this_is_false_because_key_is_not_in_first_fmap’
      >> Q.UNABBREV_TAC ‘this_is_irrelevant’
      >> simp[]
      >> PURE_ONCE_REWRITE_TAC[order_fg_add_function_node]
      >> qpat_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[]
      >> simp[range_def])
  (* Now, all the added keys are in the first argument to FUNION, and the
   existing keys/values are in the second argument to FUNION. The existing keys
   are in the same form in the LHS and the RHS, so we only need to prove the
   equivalence of the expressions for the added keys on the LHS and RHS *)
  >> cong_tac (SOME 1)
  (* The added keys on the LHS are split into the most recently added key, and
     the rest of the keys. Split the set being mapped over on the RHS to match
     the LHS, so that the most recently added key is separate from the rest of
     the keys. *)
  >> Q.SUBGOAL_THEN
      ‘range
       (order (get_underlying_graph fg))
       (n + order (get_underlying_graph fg) - i) =
       (order (get_underlying_graph fg))
       INSERT range (order (get_underlying_graph fg) + 1)
       (n + order (get_underlying_graph fg) - i)’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- simp[insert_range_left]
  >> simp[]
  (* Split FUN_FMAP over the most recently added key and the rest *)
  >> DEP_PURE_ONCE_REWRITE_TAC[FUN_FMAP_INSERT]
  >> conj_tac
  >- (simp[] >> simp[range_def])
  (* Split into two goals: Proving that the added key is equivalent on the LHS
     and RHS and all the other keys are equivalent on the LHS and RHS *)
  >> cong_tac (SOME 1)
  (* *)
  >- (PURE_ONCE_REWRITE_TAC[order_fg_add_function_node]
      >> qpat_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[])
  >> simp[]
QED

Theorem get_function_map_rcc_factor_graph_add_func_nodes_input_sys:
  ∀n p i prior ds_s fg.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    get_function_map
    (rcc_factor_graph_add_func_nodes_input_sys n p i prior ds_s fg) =
    FUN_FMAP (λfunc_node.
                let
                  j = OUTR func_node + i - order (get_underlying_graph fg);
                in
                  FUN_FMAP (λval_map.
                              EL j prior *
                              if [EL j ds_s] ≠ val_map ' (INR j)
                              then p else 1 - p
                           ) (var_assignments
                              {INR j} (get_variable_length_map fg)
                             )
             ) (IMAGE INR (range (order (get_underlying_graph fg))
                                 (order (get_underlying_graph fg) + (n - i))
                          )
               ) ⊌ (get_function_map fg)
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac
      >> gvs[]
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_input_sys_def]
      >> simp[]
      >> ‘n - i = 0’ by decide_tac
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_input_sys_def]
  >> simp[]
  (* Take the newly added function and move it into the first argument to the
     FUNION, so that the LHS becomes closer to the RHS *)
  >> PURE_ONCE_REWRITE_TAC[get_function_map_fg_add_function_node]
  >> qpat_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[]
  >> DEP_PURE_ONCE_REWRITE_TAC[FUNION_FUPDATE_SWAP]
  >> conj_tac
  >- (qmatch_abbrev_tac ‘(this_is_false_because_key_is_not_in_first_fmap ⇒ this_is_irrelevant)’
      >> ‘¬this_is_false_because_key_is_not_in_first_fmap’ suffices_by simp[]
      >> Q.UNABBREV_TAC ‘this_is_false_because_key_is_not_in_first_fmap’
      >> Q.UNABBREV_TAC ‘this_is_irrelevant’
      >> simp[]
      >> PURE_ONCE_REWRITE_TAC[order_fg_add_function_node]
      >> qpat_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[]
      >> simp[range_def])
  (* Now, all the added keys are in the first argument to FUNION, and the
   existing keys/values are in the second argument to FUNION. The existing keys
   are in the same form in the LHS and the RHS, so we only need to prove the
   equivalence of the expressions for the added keys on the LHS and RHS *)
  >> cong_tac (SOME 1)
  (* The added keys on the LHS are split into the most recently added key, and
     the rest of the keys. Split the set being mapped over on the RHS to match
     the LHS, so that the most recently added key is separate from the rest of
     the keys. *)
  >> Q.SUBGOAL_THEN
      ‘range
       (order (get_underlying_graph fg))
       (n + order (get_underlying_graph fg) - i) =
       (order (get_underlying_graph fg))
       INSERT range (order (get_underlying_graph fg) + 1)
       (n + order (get_underlying_graph fg) - i)’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- simp[insert_range_left]
  >> simp[]
  (* Split FUN_FMAP over the most recently added key and the rest *)
  >> DEP_PURE_ONCE_REWRITE_TAC[FUN_FMAP_INSERT]
  >> conj_tac
  >- (simp[] >> simp[range_def])
  (* Split into two goals: Proving that the added key is equivalent on the LHS
     and RHS and all the other keys are equivalent on the LHS and RHS *)
  >> cong_tac (SOME 1)
  (* *)
  >- (PURE_ONCE_REWRITE_TAC[order_fg_add_function_node]
      >> qpat_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[])
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem fg_add_variable_node0_function_map[simp]:
  ∀l fg.
    (fg_add_variable_node0 l fg).function_map = fg.function_map
Proof
  rpt gen_tac >> simp[fg_add_variable_node0_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem get_function_map_fg_add_variable_node[simp]:
  ∀l fg.
    get_function_map (fg_add_variable_node l fg) = get_function_map fg
Proof
  rpt gen_tac
  >> simp[get_function_map_def, fg_add_variable_node_def,
          factor_graph_ABSREP, fg_add_variable_node0_wf]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem fg_empty0_function_map[simp]:
  fg_empty0.function_map = FEMPTY
Proof
  simp[fg_empty0_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem get_function_map_fg_empty[simp]:
  get_function_map fg_empty = FEMPTY
Proof
  simp[fg_empty_def, get_function_map_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem get_function_map_fg_add_n_variable_nodes[simp]:
  ∀n l fg.
    get_function_map (fg_add_n_variable_nodes n l fg) =
    get_function_map fg
Proof
  rpt gen_tac
  >> Induct_on ‘n’ >> simp[fg_add_n_variable_nodes_def]
QED

Theorem get_function_map_rcc_factor_graph:
  ∀n p ps qs ts prior ds_s ds_p.
    get_function_map (rcc_factor_graph n p (ps,qs) ts prior (ds_s, ds_p)) =
    let
      rcc_factor_graph_variable_length_map =
      FUN_FMAP (λvar_node. if OUTR var_node < 2 * n then 1 else LENGTH ts)
               (IMAGE INR (count (3 * n + 1)));
    in
      FUN_FMAP
      (λfunc_node.
         if (OUTR func_node) ≤ 4 * n
         then
           let
             j = OUTR func_node - (3 * n + 1);
           in
             FUN_FMAP (λval_map.
                         EL j prior *
                         if [EL j ds_s] ≠ val_map ' (INR j) then p else 1 − p)
                      (var_assignments {INR j}
                                       rcc_factor_graph_variable_length_map)
         else
           if (OUTR func_node) ≤ 5 * n
           then
             let
               j = OUTR func_node - (4 * n + 1);
             in
               FUN_FMAP (λval_map.
                           if [EL j ds_p] ≠ val_map ' (INR (n + j)) then p
                           else 1 − p) (var_assignments
                                        {INR (n + j)}
                                        rcc_factor_graph_variable_length_map)
           else
             if (OUTR func_node) = 5 * n + 1
             then
               FUN_FMAP (λval_map. if val_map ' (INR (2 * n)) = ts then 1 else 0)
                        (var_assignments {INR (2 * n)}
                                         rcc_factor_graph_variable_length_map)
             else
               let
                 j = OUTR func_node - (5 * n + 2)
               in
                 FUN_FMAP (func_node_state_fn n (ps,qs) j)
                          (var_assignments
                           (func_node_state_adjacent_nodes n j)
                           rcc_factor_graph_variable_length_map)
      ) (IMAGE INR (range (3 * n + 1) (6 * n + 2)))
Proof
  rpt gen_tac
  >> simp[rcc_factor_graph_def]
  >> irule (iffLR fmap_EQ_THM)
  >> REVERSE conj_tac
  >- (simp[get_function_map_rcc_factor_graph_add_func_nodes_state,
           get_function_map_rcc_factor_graph_add_func_node_state_initial,
           get_function_map_rcc_factor_graph_add_func_nodes_enc,
           get_function_map_rcc_factor_graph_add_func_nodes_input_sys,
           order_rcc_factor_graph_add_func_node_state_initial,
           order_rcc_factor_graph_add_func_nodes_enc,
           order_rcc_factor_graph_add_func_nodes_input_sys,
           nodes_rcc_factor_graph_add_func_nodes_enc,
           nodes_rcc_factor_graph_add_func_nodes_input_sys]
      >> simp[EXTENSION] >> gen_tac >> EQ_TAC >> disch_tac >> gvs[range_def]
     )
  >> gen_tac
  >> simp[get_function_map_rcc_factor_graph_add_func_nodes_state,
          get_function_map_rcc_factor_graph_add_func_node_state_initial,
          get_function_map_rcc_factor_graph_add_func_nodes_enc,
          get_function_map_rcc_factor_graph_add_func_nodes_input_sys,
          order_rcc_factor_graph_add_func_node_state_initial,
          order_rcc_factor_graph_add_func_nodes_enc,
          order_rcc_factor_graph_add_func_nodes_input_sys,
          nodes_rcc_factor_graph_add_func_nodes_enc,
          nodes_rcc_factor_graph_add_func_nodes_input_sys]
  (* Split proof according to which range of nodes we're in (corresponding to
     a particular type of function node) *)
  >> strip_tac
  >> (DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
      >> conj_tac
      >- (simp[] >> gvs[range_def])
      >> simp[FUNION_DEF, cj 2 FUN_FMAP_DEF, FAPPLY_FUPDATE_THM]
      >> gvs[range_def]
     )
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem nodes_fg_add_function_node0:
  ∀inputs fn fg.
    nodes (fg_add_function_node0 inputs fn fg).underlying_graph =
    if inputs ⊆ var_nodes fg
    then
      INR (order fg.underlying_graph) INSERT nodes fg.underlying_graph
    else
      nodes fg.underlying_graph
Proof
  rpt gen_tac
  >> simp[fg_add_function_node0_def]
  >> rw[gsize_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem nodes_fg_add_function_node:
  ∀inputs fn fg.
    nodes (get_underlying_graph (fg_add_function_node inputs fn fg)) =
    IMAGE INR (count (order (get_underlying_graph fg) +
                      if inputs ⊆ var_nodes fg then 1n else 0n))
Proof
  rpt gen_tac
  >> simp[nodes_get_underlying_graph, order_fg_add_function_node]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem nodes_fg_add_function_node_alt:
  ∀inputs fn fg.
    nodes (get_underlying_graph (fg_add_function_node inputs fn fg)) =
    if inputs ⊆ var_nodes fg
    then
      INR (CARD (nodes (get_underlying_graph fg))) INSERT nodes (get_underlying_graph fg)
    else
      nodes (get_underlying_graph fg)
Proof
  PURE_REWRITE_TAC[get_underlying_graph_def, fg_add_function_node_def]
  >> simp[]
  >> simp[nodes_fg_add_function_node0, gsize_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_fg_add_variable_node0[simp]:
  ∀l fg.
    adjacent (fg_add_variable_node0 l fg).underlying_graph =
    adjacent fg.underlying_graph
Proof
  rpt gen_tac
  >> simp[fg_add_variable_node0_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_fg_add_variable_node[simp]:
  ∀l fg.
    adjacent (get_underlying_graph (fg_add_variable_node l fg)) =
    adjacent (get_underlying_graph fg)
Proof
  rpt gen_tac
  >> simp[get_underlying_graph_def, fg_add_variable_node_def,
          factor_graph_ABSREP, fg_add_variable_node0_wf]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_fg_add_n_variable_nodes[simp]:
  ∀n l fg.
    adjacent (get_underlying_graph (fg_add_n_variable_nodes n l fg)) =
    adjacent (get_underlying_graph fg)
Proof
  Induct_on ‘n’ >> simp[fg_add_n_variable_nodes_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* Could potentially extend this theorem to work when fg is not necessarily   *)
(* well-formed?                                                               *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_fg_add_function_node0_lemma[local]:
  ∀inputs fn fg n1 n2.
    wffactor_graph fg ∧
    inputs ⊆ var_nodes fg ∧
    n1 ∈ nodes (fg_add_function_node0 inputs fn fg).underlying_graph ∧
    n2 ∈ nodes (fg_add_function_node0 inputs fn fg).underlying_graph ⇒
    (adjacent (fg_add_function_node0 inputs fn fg).underlying_graph n1 n2 ⇔
       (n1 = INR (CARD (nodes (fg.underlying_graph))) ∧ n2 ∈ inputs) ∨
       (n2 = INR (CARD (nodes (fg.underlying_graph))) ∧ n1 ∈ inputs) ∨
       adjacent fg.underlying_graph n1 n2
    )
Proof
  rpt gen_tac >> strip_tac
  >> simp[fg_add_function_node0_def]
  >> EQ_TAC >> strip_tac >> gvs[]
  >- (‘n2 = i’ by gvs[INSERT2_lemma]
      >> gvs[])
  >- (‘n1 = i’ by gvs[INSERT2_lemma]
      >> gvs[])
  >- gvs[INSERT2_lemma]
  >- (gvs[nodes_fg_add_function_node0, gsize_def]
      >- (gvs[SUBSET_DEF]
          >> last_x_assum drule
          >> qpat_x_assum ‘INR _ ∈ inputs’ kall_tac
          >> strip_tac
          >> gvs[wffactor_graph_def])
      >> metis_tac[swap_edge]
      >> qexists ‘n2’
      >> simp[swap_edge])
  (* Copy/pasted from above, but with n2 instead of n1*)
  >> gvs[nodes_fg_add_function_node0, gsize_def]
  >- (gvs[SUBSET_DEF]
      >> last_x_assum drule
      >> qpat_x_assum ‘INR _ ∈ inputs’ kall_tac
      >> strip_tac
      >> gvs[wffactor_graph_def])
  >> metis_tac[swap_edge]
  >> qexists ‘n1’
  >> simp[swap_edge]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_fg_add_function_node0:
  ∀inputs fn fg n1 n2.
    wffactor_graph fg ∧
    inputs ⊆ var_nodes fg ⇒
    (adjacent (fg_add_function_node0 inputs fn fg).underlying_graph n1 n2 ⇔
       (n1 = INR (CARD (nodes (fg.underlying_graph))) ∧ n2 ∈ inputs) ∨
       (n2 = INR (CARD (nodes (fg.underlying_graph))) ∧ n1 ∈ inputs) ∨
       adjacent fg.underlying_graph n1 n2
    )
Proof
  (* The additional assumption in adjacent_fg_add_function_node0_local is true
   on both the LHS and RHS of the iff, therefore we can assume it is true. *)
  rpt gen_tac >> strip_tac
  >> EQ_TAC
  >- (strip_tac
      >> irule (iffLR adjacent_fg_add_function_node0_lemma)
      >> simp[]
      >> qexists ‘fn’
      >> simp[]
      >> drule adjacent_members
      >> simp[])
  >> disch_tac
  >> irule (iffRL adjacent_fg_add_function_node0_lemma)
  >> simp[]
  >> simp[nodes_fg_add_function_node0]
  >> gvs[gsize_def]
  >- gvs[SUBSET_DEF]
  >- gvs[SUBSET_DEF]
  >> drule adjacent_members
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_fg_add_function_node:
  ∀inputs fn fg n1 n2.
    inputs ⊆ var_nodes fg ⇒
    (adjacent (get_underlying_graph (fg_add_function_node inputs fn fg)) n1 n2 ⇔
       (n1 = INR (CARD (nodes (get_underlying_graph fg))) ∧ n2 ∈ inputs) ∨
       (n2 = INR (CARD (nodes (get_underlying_graph fg))) ∧ n1 ∈ inputs) ∨
       adjacent (get_underlying_graph fg) n1 n2)
Proof
  rpt gen_tac
  >> PURE_REWRITE_TAC[get_underlying_graph_def, fg_add_function_node_def]
  >> simp[Excl "nodes_factor_graph_REP"]
  >> strip_tac
  >> irule adjacent_fg_add_function_node0
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem inr_card_nodes_in_nodes_fg_add_function_node[simp]:
  ∀inputs fn fg.
    inputs ⊆ var_nodes fg ⇒
    INR (CARD (nodes (get_underlying_graph fg))) ∈
        nodes (get_underlying_graph (fg_add_function_node inputs fn fg))
Proof
  rpt gen_tac >> strip_tac
  >> simp[nodes_fg_add_function_node]
  >> simp[gsize_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem inr_order_in_nodes_fg_add_function_node[simp]:
  ∀inputs fn fg.
    inputs ⊆ var_nodes fg ⇒
    INR (order (get_underlying_graph fg)) ∈
        nodes (get_underlying_graph (fg_add_function_node inputs fn fg))
Proof
  simp[gsize_def]
QED

Theorem drag_and_out_of_iff:
  ∀b1 b2 b3.
    (b1 ∧ b2 ⇔ b1 ∧ b3) ⇔ (b1 ⇒ (b2 ⇔ b3))
Proof
  rpt gen_tac
  >> Cases_on ‘b1’ >> simp[]
QED

Theorem adjacent_rcc_factor_graph_add_func_nodes_state:
  ∀n ps qs ts i fg n1 n2.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    (adjacent (get_underlying_graph
               (rcc_factor_graph_add_func_nodes_state n (ps,qs) ts i fg)) n1 n2 ⇔
       (n1 ∈ IMAGE INR (range
                        (CARD (nodes (get_underlying_graph fg)))
                        (CARD (nodes (get_underlying_graph fg)) + (n - i))
                       ) ∧
        let
          j = OUTR n1 + i - (CARD (nodes (get_underlying_graph fg)))
        in
          (n2 = INR j ∨
           n2 = INR (n + j) ∨
           n2 = INR (2 * n + j) ∨
           n2 = INR (2 * n + j + 1))
       ) ∨
       (n2 ∈ IMAGE INR (range
                        (CARD (nodes (get_underlying_graph fg)))
                        (CARD (nodes (get_underlying_graph fg)) + (n - i))
                       ) ∧
        let
          j = OUTR n2 + i - (CARD (nodes (get_underlying_graph fg)))
        in
          (n1 = INR j ∨
           n1 = INR (n + j) ∨
           n1 = INR (2 * n + j) ∨
           n1 = INR (2 * n + j + 1))
       ) ∨
       adjacent (get_underlying_graph fg) n1 n2)
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac >> strip_tac
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
      >> simp[]
      >> qpat_x_assum ‘0 = n - i’ (fn th => assume_tac (GSYM th))
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_state_def]
  >> simp[]
  (* Inductive hypothesis has now been applied and is no longer needed *)
  >> qpat_x_assum ‘∀fg i n n1 n2 ps qs ts. _ ⇒ _ ⇒ _’ kall_tac
  (* *)
  >> simp[GSYM gsize_def]
  >> simp[order_fg_add_function_node]
  >> simp[func_node_state_adjacent_nodes_def]
  (* The LHS has one of the newly added adjacency possibilities wrapped up with
     the possibility that it was adjacent in the original graph. Disentangle
     these possibilities to make it more similar to the RHS *)
  >> DEP_PURE_ONCE_REWRITE_TAC[adjacent_fg_add_function_node]
  >> conj_tac
  >- (qpat_assum ‘var_nodes _ = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[])
  (* The LHS and RHS are only in different forms when n1 or n2 is the newly
     added node. *)
  >> REVERSE (Cases_on ‘n1 = INR (CARD (nodes (get_underlying_graph fg))) ∨
                        n2 = INR (CARD (nodes (get_underlying_graph fg)))’)
  >- (gvs[]
      >> cong_tac (SOME 4)
      >- (simp[drag_and_out_of_iff]
          >> strip_tac
          >> gvs[]
          >> simp[EXTENSION, range_def, gsize_def] >> EQ_TAC >> strip_tac >> gvs[])
      >> simp[FUN_EQ_THM] >> gen_tac
      >> simp[drag_and_out_of_iff]
      >> strip_tac
      >> gvs[]
      >> simp[EXTENSION, range_def, gsize_def] >> EQ_TAC >> strip_tac >> gvs[]
     )
  (* Abbreviations to make things more readable *)
  >> PURE_REWRITE_TAC[gsize_def]
  >> qabbrev_tac ‘fg_ord = CARD (nodes (get_underlying_graph fg))’
  >> simp[]
  >> qabbrev_tac ‘is_adjacent_node =
                  λnode : unit + num other_node : unit + num.
                    (node = INR (i + OUTR other_node − fg_ord) ∨
                     node = INR (n + (i + OUTR other_node − fg_ord)) ∨
                     node = INR (2 * n + (i + OUTR other_node − fg_ord)) ∨
                     node = INR (2 * n + (i + OUTR other_node − fg_ord) + 1))
                 ’
  >> simp[]
  (* The same abbreviations that work in the case of the previously added nodes
     also work in the case of the currently added node *)
  >> Q.SUBGOAL_THEN
      ‘n1 = INR fg_ord ∧ (n2 = INR i ∨ n2 = INR (i + n) ∨ n2 = INR (i + 2 * n) ∨
                          n2 = INR (i + (2 * n + 1))) ⇔
         n1 = INR fg_ord ∧ is_adjacent_node n2 n1’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- (PURE_ONCE_REWRITE_TAC[drag_and_out_of_iff]
      >> strip_tac
      >> unabbrev_all_tac
      >> simp[]
     )
  >> Q.SUBGOAL_THEN
      ‘n2 = INR fg_ord ∧ (n1 = INR i ∨ n1 = INR (i + n) ∨ n1 = INR (i + 2 * n) ∨
                          n1 = INR (i + (2 * n + 1))) ⇔
         n2 = INR fg_ord ∧ is_adjacent_node n1 n2’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- (PURE_ONCE_REWRITE_TAC[drag_and_out_of_iff]
      >> strip_tac
      >> unabbrev_all_tac
      >> simp[]
     )
  (* In the case where our nodes are adjacent in the underlying graph, our
     iff immediately holds, thus we can simplify the iff *)
  >> Cases_on ‘adjacent (get_underlying_graph fg) n1 n2’ >> simp[]
  (* Rename components of expression to make it more understandable what each
     of the components mean *)
  >> qmatch_abbrev_tac ‘existing_adjacencies_n1 ∨
                        existing_adjacencies_n2 ∨
                        new_adjacency_n1 ∨
                        new_adjacency_n2 ⇔
                          all_adjacencies_n1 ∨
                          all_adjacencies_n2’
  (* Now we can clearly see that we really want to independently join together
     the added adjacency to the rest of the adjacencies *)
  >> ‘(existing_adjacencies_n1 ∨ new_adjacency_n1 ⇔ all_adjacencies_n1) ∧
      (existing_adjacencies_n2 ∨ new_adjacency_n2 ⇔ all_adjacencies_n2)’
    suffices_by (rpt (pop_assum kall_tac)
                 >> Cases_on ‘existing_adjacencies_n1’ >> simp[]
                 >> Cases_on ‘existing_adjacencies_n2’ >> simp[]
                )
  >> MAP_EVERY Q.UNABBREV_TAC
               [‘existing_adjacencies_n1’, ‘new_adjacency_n1’,
                ‘all_adjacencies_n1’, ‘existing_adjacencies_n2’,
                ‘new_adjacency_n2’, ‘all_adjacencies_n2’]
  >> conj_tac
  >- (EQ_TAC
      >- (strip_tac
          >- (simp[] >> qpat_x_assum ‘x ∈ range _ _’ mp_tac >> simp[range_def])
          >> simp[]
          >> simp[range_def])
      >> strip_tac
      >> simp[]
      >> qpat_x_assum ‘x ∈ range _ _’ mp_tac >> simp[range_def])
  (* Version prior to update to iff thing we need to prove*)
  >> EQ_TAC
  >- (strip_tac
      >- (simp[]
          >> qpat_x_assum ‘_ ∈ range _ _’ mp_tac >> simp[range_def])
      >> simp[]
      >> simp[range_def]
     )
  >> strip_tac
  >> simp[]
  >> Cases_on ‘x = fg_ord’ >> simp[]
  >> qpat_x_assum ‘x ∈ range _ _’ mp_tac
  >> simp[range_def]
QED

Theorem adjacent_rcc_factor_graph_add_func_node_state_initial:
  ∀n ts fg n1 n2.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    (adjacent (get_underlying_graph
               (rcc_factor_graph_add_func_node_state_initial n ts fg)) n1 n2 ⇔
       n1 = INR (CARD (nodes (get_underlying_graph fg))) ∧ n2 = INR (2 * n) ∨
       n2 = INR (CARD (nodes (get_underlying_graph fg))) ∧ n1 = INR (2 * n) ∨
       adjacent (get_underlying_graph fg) n1 n2
    )
Proof
  rpt strip_tac
  >> simp[rcc_factor_graph_add_func_node_state_initial_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[adjacent_fg_add_function_node]
  >> conj_tac
  >- (qpat_x_assum ‘var_nodes fg = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[])
  >> simp[]
QED

Theorem adjacent_rcc_factor_graph_add_func_nodes_enc:
  ∀n p i ds_p fg n1 n2.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    (adjacent (get_underlying_graph
               (rcc_factor_graph_add_func_nodes_enc n p i ds_p fg)
              ) n1 n2 ⇔
       (n1 ∈ IMAGE INR (range
                        (CARD (nodes (get_underlying_graph fg)))
                        (CARD (nodes (get_underlying_graph fg)) + (n - i))
                       ) ∧
        let
          j = OUTR n1 + i - (CARD (nodes (get_underlying_graph fg)))
        in
          n2 = INR (n + j)
       ) ∨
       (n2 ∈ IMAGE INR (range
                        (CARD (nodes (get_underlying_graph fg)))
                        (CARD (nodes (get_underlying_graph fg)) + (n - i))
                       ) ∧
        let
          j = OUTR n2 + i - (CARD (nodes (get_underlying_graph fg)))
        in
          n1 = INR (n + j)
       ) ∨
       adjacent (get_underlying_graph fg) n1 n2)
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac >> strip_tac
      >> qpat_x_assum ‘0 = n - i’ (fn th => assume_tac (GSYM th))
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_enc_def]
      >> simp[])
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_enc_def]
  >> simp[]
  (* We have applied the inductive hypothesis and no longer need it *)
  >> qpat_x_assum ‘∀ds_p fg i n n1 n2 p. _ ⇒ _ ⇒ _’ kall_tac
  (* Simplify *)
  >> PURE_REWRITE_TAC[GSYM gsize_def]
  >> PURE_REWRITE_TAC[order_fg_add_function_node]
  >> Q.SUBGOAL_THEN ‘{INR (i + n)} ⊆ var_nodes fg’
      (fn th => PURE_REWRITE_TAC[th])
  >- (qpat_assum ‘var_nodes _ = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[])
  >> simp[]
  (* *)
  >> DEP_PURE_ONCE_REWRITE_TAC[adjacent_fg_add_function_node]
  >> conj_tac
  >- (qpat_assum ‘var_nodes _ = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[])
  (* In the case where our nodes are adjacent in the underlying graph, our
     iff immediately holds, thus we can simplify the iff *)
  >> Cases_on ‘adjacent (get_underlying_graph fg) n1 n2’ >> simp[]
  (* Rename components of expression to make it more understandable what each
     of the components mean *)
  >> qmatch_abbrev_tac ‘existing_adjacencies_n1 ∨
                        existing_adjacencies_n2 ∨
                        new_adjacency_n1 ∨
                        new_adjacency_n2 ⇔
                          all_adjacencies_n1 ∨
                          all_adjacencies_n2’
  (* Now we can clearly see that we really want to independently join together
     the added adjacency to the rest of the adjacencies *)
  >> ‘(existing_adjacencies_n1 ∨ new_adjacency_n1 ⇔ all_adjacencies_n1) ∧
      (existing_adjacencies_n2 ∨ new_adjacency_n2 ⇔ all_adjacencies_n2)’
    suffices_by (rpt (pop_assum kall_tac)
                 >> Cases_on ‘existing_adjacencies_n1’ >> simp[]
                 >> Cases_on ‘existing_adjacencies_n2’ >> simp[]
                )
  >> MAP_EVERY Q.UNABBREV_TAC
               [‘existing_adjacencies_n1’, ‘new_adjacency_n1’,
                ‘all_adjacencies_n1’, ‘existing_adjacencies_n2’,
                ‘new_adjacency_n2’, ‘all_adjacencies_n2’]
  (* *)
  >> conj_tac
  >- (EQ_TAC
      >- (strip_tac
          >- (simp[]
              >> qpat_x_assum ‘_ ∈ range _ _’ mp_tac
              >> simp[range_def])
          >> simp[GSYM gsize_def]
          >> simp[range_def]
         )
      >> simp[]
      >> strip_tac
      >> Cases_on ‘x = order (get_underlying_graph fg)’
      >- simp[GSYM gsize_def]
      >> qpat_x_assum ‘_ ∈ range _ _’ mp_tac
      >> simp[range_def])
  >> EQ_TAC
  >- (strip_tac
      >- (simp[]
          >> qpat_x_assum ‘_ ∈ range _ _’ mp_tac
          >> simp[range_def])
      >> simp[GSYM gsize_def]
      >> simp[range_def]
     )
  >> strip_tac
  >> simp[]
  >> Cases_on ‘x = order (get_underlying_graph fg)’
  >- simp[GSYM gsize_def]
  >> qpat_x_assum ‘x ∈ range _ _’ mp_tac
  >> simp[range_def]
QED

Theorem adjacent_rcc_factor_graph_add_func_nodes_input_sys:
  ∀n p i prior ds_s fg n1 n2.
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    (adjacent (get_underlying_graph
               (rcc_factor_graph_add_func_nodes_input_sys n p i prior ds_s fg)
              ) n1 n2 ⇔
       (n1 ∈ IMAGE INR (range
                        (CARD (nodes (get_underlying_graph fg)))
                        (CARD (nodes (get_underlying_graph fg)) + (n - i))
                       ) ∧
        let
          j = OUTR n1 + i - (CARD (nodes (get_underlying_graph fg)))
        in
          n2 = INR j
       ) ∨
       (n2 ∈ IMAGE INR (range
                        (CARD (nodes (get_underlying_graph fg)))
                        (CARD (nodes (get_underlying_graph fg)) + (n - i))
                       ) ∧
        let
          j = OUTR n2 + i - (CARD (nodes (get_underlying_graph fg)))
        in
          n1 = INR j
       ) ∨
       adjacent (get_underlying_graph fg) n1 n2)
Proof
  (* Our base case is when i gets to n. We then want to induct downwards on
     i. So we induct on n - i. *)
  rpt gen_tac
  >> qabbrev_tac ‘indterm = n - i’
  >> pop_assum mp_tac >> simp[Abbrev_def]
  >> SPEC_ALL_TAC
  >> Induct_on ‘indterm’
  (* Base case *)
  >- (rpt gen_tac >> strip_tac >> strip_tac
      >> qpat_x_assum ‘0 = n - i’ (fn th => assume_tac (GSYM th))
      >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_input_sys_def]
      >> simp[]
     )
  (* Inductive step *)
  >> rpt gen_tac >> strip_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_add_func_nodes_input_sys_def]
  >> simp[]
  (* We have applied the inductive hypothesis and no longer need it *)
  >> qpat_x_assum ‘∀ds_s fg i n n1 n2 p prior. _ ⇒ _ ⇒ _’ kall_tac
  (* Simplify *)
  >> PURE_REWRITE_TAC[GSYM gsize_def]
  >> PURE_REWRITE_TAC[order_fg_add_function_node]
  >> Q.SUBGOAL_THEN ‘{INR i} ⊆ var_nodes fg’
      (fn th => PURE_REWRITE_TAC[th])
  >- (qpat_assum ‘var_nodes _ = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[])
  >> simp[]
  (* *)
  >> DEP_PURE_ONCE_REWRITE_TAC[adjacent_fg_add_function_node]
  >> conj_tac
  >- (qpat_assum ‘var_nodes _ = _’ (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[])
  (* In the case where our nodes are adjacent in the underlying graph, our
     iff immediately holds, thus we can simplify the iff *)
  >> Cases_on ‘adjacent (get_underlying_graph fg) n1 n2’ >> simp[]
  (* Rename components of expression to make it more understandable what each
     of the components mean *)
  >> qmatch_abbrev_tac ‘existing_adjacencies_n1 ∨
                        existing_adjacencies_n2 ∨
                        new_adjacency_n1 ∨
                        new_adjacency_n2 ⇔
                          all_adjacencies_n1 ∨
                          all_adjacencies_n2’
  (* Now we can clearly see that we really want to independently join together
     the added adjacency to the rest of the adjacencies *)
  >> ‘(existing_adjacencies_n1 ∨ new_adjacency_n1 ⇔ all_adjacencies_n1) ∧
      (existing_adjacencies_n2 ∨ new_adjacency_n2 ⇔ all_adjacencies_n2)’
    suffices_by (rpt (pop_assum kall_tac)
                 >> Cases_on ‘existing_adjacencies_n1’ >> simp[]
                 >> Cases_on ‘existing_adjacencies_n2’ >> simp[]
                )
  >> MAP_EVERY Q.UNABBREV_TAC
               [‘existing_adjacencies_n1’, ‘new_adjacency_n1’,
                ‘all_adjacencies_n1’, ‘existing_adjacencies_n2’,
                ‘new_adjacency_n2’, ‘all_adjacencies_n2’]
  (* *)
  >> conj_tac
  >- (EQ_TAC
      >- (strip_tac
          >- (simp[]
              >> qpat_x_assum ‘_ ∈ range _ _’ mp_tac
              >> simp[range_def])
          >> simp[GSYM gsize_def]
          >> simp[range_def]
         )
      >> simp[]
      >> strip_tac
      >> Cases_on ‘x = order (get_underlying_graph fg)’
      >- simp[GSYM gsize_def]
      >> qpat_x_assum ‘_ ∈ range _ _’ mp_tac
      >> simp[range_def])
  >> EQ_TAC
  >- (strip_tac
      >- (simp[]
          >> qpat_x_assum ‘_ ∈ range _ _’ mp_tac
          >> simp[range_def])
      >> simp[GSYM gsize_def]
      >> simp[range_def]
     )
  >> strip_tac
  >> simp[]
  >> Cases_on ‘x = order (get_underlying_graph fg)’
  >- simp[GSYM gsize_def]
  >> qpat_x_assum ‘x ∈ range _ _’ mp_tac
  >> simp[range_def]
QED

(* -------------------------------------------------------------------------- *)
(* Tells us what nodes are adajcent to what other nodes in the bcjr factor    *)
(* graph.                                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem adjacent_rcc_factor_graph:
  ∀n p ps qs ts prior ds_s ds_p n1 n2.
    (adjacent (get_underlying_graph
               (rcc_factor_graph n p (ps,qs) ts prior (ds_s, ds_p))) n1 n2 ⇔
       if n1 = INL () ∨ 6 * n + 2 ≤ OUTR n1
       then
         F
       else
         if OUTR n1 < n
         then
           n2 = INR (OUTR n1 + (3 * n + 1)) ∨ n2 = INR (OUTR n1 + 5 * n + 2)
         else
           if OUTR n1 < 2 * n
           then
             n2 = INR (OUTR n1 + (3 * n + 1)) ∨ n2 = INR (OUTR n1 + 4 * n + 2)
           else
             if OUTR n1 < 3 * n + 1
             then
               n2 = INR (OUTR n1 + (3 * n + 1)) ∨
               (n1 ≠ INR (3 * n) ∧ n2 = INR (OUTR n1 + (3 * n + 2)))
             else
               if OUTR n1 < 4 * n + 1
               then
                 n2 = INR (OUTR n1 - (3 * n + 1))
               else
                 if OUTR n1 < 5 * n + 1
                 then
                   n2 = INR (OUTR n1 - (3 * n + 1))
                 else
                   if OUTR n1 = 5 * n + 1
                   then
                     n2 = INR (2 * n)
                   else
                     n2 = INR (OUTR n1 - (5 * n + 2)) ∨
                     n2 = INR (OUTR n1 - (4 * n + 2)) ∨
                     n2 = INR (OUTR n1 - (3 * n + 2)) ∨
                     n2 = INR (OUTR n1 - (3 * n + 1))
    )
Proof
  rpt gen_tac
  >> REVERSE $ Cases_on ‘n1 ∈ nodes
                         (get_underlying_graph
                          (rcc_factor_graph n p (ps,qs) ts prior (ds_s, ds_p)))’
  >- (qmatch_abbrev_tac ‘_ ⇔ if b then _ else _’
      >> sg ‘b’ >> Q.UNABBREV_TAC ‘b’
      >- (gvs[nodes_rcc_factor_graph]
          >> Cases_on ‘n1’ >> gvs[])
      >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[]
      >> disch_tac
      >> drule adjacent_members
      >> simp[])
  >> qmatch_abbrev_tac ‘_ ⇔ if b then _ else _’
  >> sg ‘¬b’ >> Q.UNABBREV_TAC ‘b’
  >- gvs[nodes_rcc_factor_graph]
  >> simp[]
  >> qpat_x_assum ‘¬(_ ∨ _)’ kall_tac
  (* The above was added to this theorem later: initially, we required that
     n1 was in the nodes of the graph as a precondition, but I changed it so
     that this was included as an if statement in the expression for
     adjacent (rcc_factor_graph), so that I can apply this theorem even to nodes
     which aren't in the factor graph. By this point, I have modified the proof
     state to be equivalent to the proof state I had when I was initially
     writing this proof.*)
  >> gvs[nodes_rcc_factor_graph]
  >> simp[rcc_factor_graph_def, o_DEF]
  >> simp[adjacent_rcc_factor_graph_add_func_nodes_state,
          GSYM gsize_def,
          order_rcc_factor_graph_add_func_node_state_initial,
          order_rcc_factor_graph_add_func_nodes_enc,
          order_rcc_factor_graph_add_func_nodes_input_sys,
          adjacent_rcc_factor_graph_add_func_node_state_initial,
          adjacent_rcc_factor_graph_add_func_nodes_enc,
          adjacent_rcc_factor_graph_add_func_nodes_input_sys]
  >> EQ_TAC
  >- (strip_tac >> gvs[range_def])
  >> Cases_on ‘x < n’ >> simp[]
  >- (strip_tac >> gvs[range_def])
  >> Cases_on ‘x < 2 * n’ >> simp[]
  >- (strip_tac >> gvs[range_def])
  >> Cases_on ‘x < 3 * n + 1’ >> simp[]
  >- (strip_tac >> gvs[range_def])
  >> Cases_on ‘x < 4 * n + 1’ >> simp[]
  >- (strip_tac >> gvs[range_def])
  >> Cases_on ‘x < 5 * n + 1’ >> simp[]
  >- (strip_tac >> gvs[range_def])
  >> Cases_on ‘x = 5 * n + 1’ >> simp[]
  >- (strip_tac >> gvs[range_def])
QED

(* This was originally written for the first case, but I found that it also
 works for most of the other cases *)
val functions_noninfinite_rcc_factor_graph_solve_case_tac =
simp[]
>> DEP_PURE_ONCE_REWRITE_TAC [cj 2 FUN_FMAP_DEF]
>> conj_tac
>- (simp[]
    >> qmatch_asmsub_abbrev_tac ‘val_map ∈ val_map_assignments _ cur_adj_nodes _ ’
    >> sg ‘cur_adj_nodes ⊆ var_nodes (rcc_factor_graph n p (ps,qs) ts prior (ds_s, ds_p))’
    >- (simp[var_nodes_rcc_factor_graph]
        >> Q.UNABBREV_TAC ‘cur_adj_nodes’
        >> simp[SUBSET_DEF]
        >> gen_tac
        >> strip_tac
        >> Cases_on ‘x'’ >> gvs[]
        >> gvs[range_def, adjacent_rcc_factor_graph]
       )
    >> sg ‘FDOM val_map = cur_adj_nodes’
    >- (drule in_val_map_assignments_fdom
        >> disch_then irule
        >> simp[]
       )
    >> simp[var_assignments_def]
    >> qpat_x_assum ‘x ∈ range _ _’
                    (fn th => mp_tac (SIMP_RULE (srw_ss()) [range_def] th))
    >> strip_tac
    >> qmatch_abbrev_tac ‘cur_adj_nodes = adj_ns ∧ _’
    >> sg ‘cur_adj_nodes = adj_ns’ >> Q.UNABBREV_TAC ‘adj_ns’
    >- (Q.UNABBREV_TAC ‘cur_adj_nodes’
        >> simp[EXTENSION] >> gen_tac >> EQ_TAC >> gvs[adjacent_rcc_factor_graph]
        >> strip_tac
        >> simp[]
        >> pop_assum mp_tac >> simp[]
       )
    >> simp[]
    >> gvs[val_map_assignments_def]
    >> simp[get_variable_length_map_rcc_factor_graph]
   )
>> ‘1 - p ≠ +∞ ∧ 1 - p ≠ −∞’ by (irule probability_negation_not_infty >> simp[])
>> rw[];

fun functions_noninfinite_rcc_factor_graph_case1_cleanup_tac i
= irule (cj i mul_not_infty2)
>> simp[]
>> PURE_ONCE_REWRITE_TAC[CONJ_COMM]
>> last_x_assum irule
>> irule EL_MEM
>> doexpand_tac
>> simp[]
>> PURE_ONCE_REWRITE_TAC[GSYM NOT_ZERO]
>> disch_tac
>> gvs[range_def];

Theorem functions_noninfinite_rcc_factor_graph:
  ∀n p ps qs ts prior ds_s ds_p.
    p ≠ +∞ ∧
    p ≠ −∞ ∧
    (∀x. MEM x prior ⇒ x ≠ +∞ ∧ x ≠ −∞) ∧
    LENGTH prior = n ⇒
    functions_noninfinite (rcc_factor_graph n p (ps,qs) ts prior (ds_s,ds_p))
Proof
  rpt gen_tac >> strip_tac
  >> qpat_x_assum ‘LENGTH prior = n’ assume_tac >> donotexpand_tac
  >> simp[functions_noninfinite_def]
  >> rpt gen_tac >> strip_tac
  >> gvs[]
  >> simp[get_function_map_rcc_factor_graph]
  >> simp[cj 2 FUN_FMAP_DEF]
  >> Cases_on ‘x ≤ 4 * n’
  >- (functions_noninfinite_rcc_factor_graph_solve_case_tac
      >- (functions_noninfinite_rcc_factor_graph_case1_cleanup_tac 2)
      >- (functions_noninfinite_rcc_factor_graph_case1_cleanup_tac 2)
      >- (functions_noninfinite_rcc_factor_graph_case1_cleanup_tac 1)
      >> functions_noninfinite_rcc_factor_graph_case1_cleanup_tac 1
     )
  >> simp[]
  >> Cases_on ‘x ≤ 5 * n’
  >- functions_noninfinite_rcc_factor_graph_solve_case_tac
  >> simp[]
  >> Cases_on  ‘x = 5 * n + 1’
  >- functions_noninfinite_rcc_factor_graph_solve_case_tac
  >> simp[]
  (* Much more significant modifications need to be made for this case than for
     the other cases, so I copy/pasted the code and modified it *)
  >> simp[]
  >> DEP_PURE_ONCE_REWRITE_TAC [cj 2 FUN_FMAP_DEF]
  >> conj_tac
  >- (simp[]
      >> qmatch_asmsub_abbrev_tac ‘val_map ∈ val_map_assignments _ cur_adj_nodes _ ’
      >> sg ‘cur_adj_nodes ⊆ var_nodes (rcc_factor_graph n p (ps,qs) ts prior (ds_s, ds_p))’
      >- (simp[var_nodes_rcc_factor_graph]
          >> Q.UNABBREV_TAC ‘cur_adj_nodes’
          >> simp[SUBSET_DEF]
          >> gen_tac
          >> strip_tac
          >> Cases_on ‘x'’ >> gvs[]
          >> gvs[range_def, adjacent_rcc_factor_graph]
          (* Here is the first modification *)
          >> pop_assum mp_tac >> rw[]
          (* End of first modification *)
          >> all_tac
         )
      >> sg ‘FDOM val_map = cur_adj_nodes’
      >- (drule in_val_map_assignments_fdom
          >> disch_then irule
          >> simp[]
         )
      >> simp[var_assignments_def]
      >> qpat_x_assum ‘x ∈ range _ _’
                      (fn th => mp_tac (SIMP_RULE (srw_ss()) [range_def] th))
      >> strip_tac
      >> qmatch_abbrev_tac ‘cur_adj_nodes = adj_ns ∧ _’
      >> sg ‘cur_adj_nodes = adj_ns’ >> Q.UNABBREV_TAC ‘adj_ns’
      >- (Q.UNABBREV_TAC ‘cur_adj_nodes’
          (* Here is the second modification *)
          >> simp[func_node_state_adjacent_nodes_def]
          (* End of second modification *)
          >> simp[EXTENSION] >> gen_tac >> EQ_TAC >> gvs[adjacent_rcc_factor_graph]
          >> strip_tac
          (* Here is the third modification *)
          >> simp[adjacent_rcc_factor_graph]
          >> pop_assum mp_tac >> simp[] >> rw[]
          (* End of third modification *)
         )
      >> simp[]
      >> gvs[val_map_assignments_def]
      >> simp[get_variable_length_map_rcc_factor_graph]
     )
  >> ‘1 - p ≠ +∞ ∧ 1 - p ≠ −∞’ by (irule probability_negation_not_infty >> simp[])
  >> rw[]
  >> (simp[func_node_state_fn_def] >> rw[])
QED

Theorem degree_rcc_factor_graph:
  ∀n p ps qs ts prior ds_s ds_p x.
    degree (get_underlying_graph
            (rcc_factor_graph n p (ps,qs) ts prior (ds_s,ds_p))) x =
    if x = INL () ∨ 6 * n + 2 ≤ OUTR x
    then
      0
    else
      if OUTR x ∈ range (3 * n) (5 * n + 2)
      then
        1
      else
        if OUTR x ∈ range 0 (3 * n)
        then
          2
        else
          4
Proof
  rpt gen_tac
  >> simp[degree_def]
  (* Handle the case where x is not a valid node *)
  >> Cases_on ‘x = INL () ∨ 6 * n + 2 ≤ OUTR x’
  >- (simp[]
      (* In this case, we don't have a valid node *)
      >> sg ‘x ∉ nodes (get_underlying_graph
                        (rcc_factor_graph n p (ps,qs) ts prior (ds_s,ds_p)))’
      >- (simp[nodes_rcc_factor_graph]
          >> gen_tac >> strip_tac >> gvs[])
      (* We don't need the specific value of x, only that it isn't a valid
         node. Avoid accidental case splits on the or statement. *)
      >> qpat_x_assum ‘_ ∨ _’ kall_tac
      (* *)
      >> simp[EXTENSION]
      >> gen_tac
      >> Cases_on ‘x ∈ x'’ >> gvs[]
      >> simp[fsgedges_def]
      >> rpt gen_tac >> strip_tac
      >> disch_tac
      (* Without loss of generality, we may take INL () to be the first of the
         two elements, because the two elements are interchangable. *)
      >> wlog_tac ‘x = m’ [‘m’, ‘n'’]
      >- (last_x_assum $ qspecl_then [‘n'’, ‘m’] assume_tac
          >> gvs[INSERT2_lemma, adjacent_SYM])
      >> gvs[]
      >> drule adjacent_members
      >> simp[nodes_rcc_factor_graph]
     )
  (* Handle the cases where we have degree 1 *)
  >> Cases_on ‘OUTR x ∈ range (3 * n) (5 * n + 2)’
  >- (simp[]
      >> simp[fsgedges_def]
      >> simp[adjacent_rcc_factor_graph]
      >> qmatch_abbrev_tac ‘CARD edges_with_x = 1’
      (* The subcase where we have the node 3 * n *)
      >> Cases_on ‘OUTR x = 3 * n’
      >- (sg ‘edges_with_x = {{INR (3 * n); INR(3 * n + (3 * n + 1))}}’
          >- (irule (iffRL EXTENSION)
              >> gen_tac >> EQ_TAC >> strip_tac >> simp[]
              >- (Q.UNABBREV_TAC ‘edges_with_x’
                  >> gvs[]
                  >- (Cases_on ‘m’ >> gvs[])
                  >- (Cases_on ‘m’ >> gvs[])
                  >> Cases_on ‘m’ >> gvs[] >> Cases_on ‘n'’ >> gvs[]
                  >> Cases_on ‘y = 5 * n + 1’ >> gvs[]
                  >- gvs[range_def, INSERT2_lemma]
                  >> gvs[INSERT2_lemma]
                 )
              >> Q.UNABBREV_TAC ‘edges_with_x’
              >> Cases_on ‘x’ >> gvs[]
              >> qexistsl [‘INR (3 * n)’, ‘INR (3 * n + (3 * n + 1))’]
              >> simp[]
             )
          >> simp[]
         )
      (* The subcase where we have a node in 3n + 1 - 4n + 1 *)
      >> Cases_on ‘OUTR x ∈ range (3 * n + 1) (4 * n + 1)’
      >- (‘edges_with_x = {{x; INR (OUTR x - (3 * n + 1))}}’ suffices_by simp[]
          >> irule (iffRL EXTENSION)
          >> gen_tac >> EQ_TAC >> strip_tac >> Q.UNABBREV_TAC ‘edges_with_x’
          >- (gvs[range_def]
              >> Cases_on ‘m’ >> Cases_on ‘n'’ >> gvs[]
              >> simp[INSERT2_lemma])
          >> gvs[range_def]
          >> qexistsl [‘x’, ‘INR (OUTR x - (3 * n + 1))’]
          >> simp[]
         )
      (* The subcase wher we have a node in 4n + 1 to 5n + 1 *)
      >> Cases_on ‘OUTR x ∈ range (4 * n + 1) (5 * n + 1)’
      >- (gvs[range_def]
          >> qsuff_tac ‘edges_with_x = {{x; INR (OUTR x - (3 * n + 1))}}’
          >- simp[]
          >> irule (iffRL EXTENSION)
          >> gen_tac >> EQ_TAC >> strip_tac >> Q.UNABBREV_TAC ‘edges_with_x’
          >- (gvs[]
              >> Cases_on ‘m’ >> Cases_on ‘n'’ >> gvs[] >> simp[INSERT2_lemma])
          >> gvs[]
          >> qexistsl [‘x’, ‘INR (OUTR x - (3 * n + 1))’]
          >> simp[]
         )
      >> Cases_on ‘OUTR x = 5 * n + 1’
      >- (Cases_on ‘x’ >> gvs[range_def]
          >> qsuff_tac ‘edges_with_x = {{INR (5 * n + 1); INR (2 * n)}}’
          >- simp[]
          >> irule (iffRL EXTENSION)
          >> gen_tac >> EQ_TAC >> strip_tac >> Q.UNABBREV_TAC ‘edges_with_x’
          >- (gvs[]
              >> Cases_on ‘m’ >> gvs[] >> simp[INSERT2_lemma])
          >> gvs[]
          >> qexistsl [‘INR (5 * n + 1)’, ‘INR (2 * n)’]
          >> simp[]
         )
      >> gvs[range_def]
     )
  (* Handle the cases where we have degree 2 *)
  >> Cases_on ‘OUTR x ∈ range 0 (3 * n)’
  >- (simp[]
      >> simp[fsgedges_def, adjacent_rcc_factor_graph]
      >> Cases_on ‘x’ >> gvs[range_def]
      >> qmatch_abbrev_tac ‘CARD edges_with_inr_y = 2’
      (* Subcase of 0 - n *)
      >> Cases_on ‘y ∈ range 0 n’
      >- (qsuff_tac ‘edges_with_inr_y = {{INR y; INR (y + (3 * n + 1))};
                     {INR y; INR (y + 5 * n + 2)}}’
          >- (simp[] >> strip_tac >> simp[INSERT2_lemma])
          >> Q.UNABBREV_TAC ‘edges_with_inr_y’
          >> irule (iffRL EXTENSION)
          >> gen_tac >> EQ_TAC >> strip_tac
          >- (gvs[range_def]
              >> Cases_on ‘m’ >> gvs[]
              >> Cases_on ‘y' < 4 * n + 1’ >> gvs[]
              >> (simp[INSERT2_lemma])
             )
          >> gvs[]
          >- (qexistsl [‘INR y’, ‘INR (y + 3 * n + 1)’]
              >> simp[])
          >> qexistsl [‘INR y’, ‘INR (y + 5 * n + 2)’]
          >> simp[]
          >> gvs[range_def]
         )
      (* Subcase of n - 2 * n*)
      >> Cases_on ‘y ∈ range n (2 * n)’
      >- (qsuff_tac ‘edges_with_inr_y = {{INR y; INR (y + (3 * n + 1))};
                     {INR y; INR (y + (4 * n + 2))}}’
          >- (simp[] >> strip_tac >> simp[INSERT2_lemma])
          >> Q.UNABBREV_TAC ‘edges_with_inr_y’
          >> irule (iffRL EXTENSION)
          >> gen_tac >> EQ_TAC >> strip_tac
          >- (gvs[range_def]
              >> Cases_on ‘m’ >> gvs[]
              >> simp[INSERT2_lemma]
              >> pop_assum mp_tac >> rw[]
             )
          >> gvs[]
          >- (qexistsl [‘INR y’, ‘INR (y + 3 * n + 1)’]
              >> simp[])
          >> qexistsl [‘INR y’, ‘INR (y + 4 * n + 2)’]
          >> simp[]
          >> gvs[range_def]
         )
      (* Subcase of 2 * n - 3 * n *)
      >> ‘y ∈ range (2 * n) (3 * n)’ by gvs[range_def]
      >> qsuff_tac ‘edges_with_inr_y = {{INR y; INR (y + (3 * n + 1))};
                    {INR y; INR (y + (3 * n + 2))}}’
      >- (simp[] >> strip_tac >> simp[INSERT2_lemma])
      >> Q.UNABBREV_TAC ‘edges_with_inr_y’
      >> irule (iffRL EXTENSION)
      >> gen_tac >> EQ_TAC >> strip_tac
      >- (gvs[range_def]
          >> Cases_on ‘m’ >> gvs[]
          >> simp[INSERT2_lemma]
          >> pop_assum mp_tac >> rw[]
         )
      >> gvs[]
      >- (qexistsl [‘INR y’, ‘INR (y + 3 * n + 1)’]
          >> simp[])
      >> qexistsl [‘INR y’, ‘INR (y + 3 * n + 2)’]
      >> simp[]
      >> gvs[range_def]
     )
  (* Handle the remaining case, where we have degree 4 *)
  >> Cases_on ‘x’ >> gvs[range_def]
  >> simp[fsgedges_def, adjacent_rcc_factor_graph]
  >> qmatch_abbrev_tac ‘CARD edges_with_inr_y = 4’
  >> qsuff_tac ‘edges_with_inr_y
                = {{INR y; INR (y - (5 * n + 2))};
                {INR y; INR (y - (4 * n + 2))};
                {INR y; INR (y - (3 * n + 2))};
                {INR y; INR (y - (3 * n + 1))}}’
  >- (disch_tac
      >> gvs[Abbr ‘edges_with_inr_y’, INSERT2_lemma])
  >> Q.UNABBREV_TAC ‘edges_with_inr_y’
  >> irule (iffRL EXTENSION)
  >> gen_tac >> EQ_TAC >> strip_tac
  >- (gvs[range_def]
      >> Cases_on ‘m’ >> gvs[]
      >> simp[INSERT2_lemma]
      >> pop_assum mp_tac >> rw[]
     )
  >> gvs[]
  >- (qexistsl [‘INR y’, ‘INR (y - (5 * n + 2))’]
      >> simp[])
  >- (qexistsl [‘INR y’, ‘INR (y - (4 * n + 2))’]
      >> simp[])
  >- (qexistsl [‘INR y’, ‘INR (y - (3 * n + 2))’]
      >> simp[])
  >> qexistsl [‘INR y’, ‘INR (y - (3 * n + 1))’]
  >> simp[]
QED

Theorem EVEN_DOUBLE_ADD1[simp]:
  ∀n.
    ¬EVEN (2 * n + 1)
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[GSYM ADD1]
  >> PURE_ONCE_REWRITE_TAC[EVEN]
  >> simp[EVEN_DOUBLE]
QED

Theorem DOUBLE_ADD1_DIV2[simp]:
  ∀n.
    (2 * n + 1) DIV 2 = n
Proof
  gen_tac
  >> Induct_on ‘n’ >> simp[]
QED

Theorem NOT_EVEN_EXISTS:
  ∀n.
    ¬EVEN n ⇔ ∃k. n = 2 * k + 1
Proof
  gen_tac >> simp[EVEN_ODD, ODD_EXISTS, ADD1]
QED

Theorem DIV_ADD1_EQ_ORIG[simp]:
  ∀n.
    2 * (n DIV 2) + 1 = n ⇔ ¬EVEN n
Proof
  gen_tac
  >> Cases_on ‘EVEN n’ >> simp[]
  >- gvs[EVEN_EXISTS]
  >> gvs[NOT_EVEN_EXISTS]
QED

Theorem SUB_EQ_ORIG:
  ∀n m : num.
    n - m = n ⇔ n = 0 ∨ m = 0
Proof
  decide_tac
QED

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*       #   #   #         #                                                  *)
(*       o   o   o         o                                                  *)
(*   # o # o # o # o ... o # o                                                *)
(*       o   o   o         o                                                  *)
(*       #   #   #         #                                                  *)
(*                                                                            *)
(*  "#" represents a funciton node.    "o" represents a variable node         *)
(*                                                                            *)
(*  Removing a leaf node will conserve whether or not the graph is a tree.    *)
(*                                                                            *)
(*  1. Remove all the top function leaf nodes.                                *)
(*  2. Remove all the top variable nodes, which have become leaf nodes due    *)
(*     to step 1.                                                             *)
(*  3. Remove all the bottom function leaf nodes                              *)
(*  4. Remove all the bottom variable nodes, which have become leaf nodes due *)
(*     to step 3                                                              *)
(*  5. Repeatedly remove the leftmost node until we are left with only one    *)
(*     node, which is trivially a tree                                        *)
(* -------------------------------------------------------------------------- *)
Theorem is_tree_rcc_factor_graph:
  ∀n p ps qs ts prior ds_s ds_p.
    is_tree (get_underlying_graph
             (rcc_factor_graph n p (ps,qs) ts prior (ds_s, ds_p))
            )
Proof
  rpt gen_tac
  >> qmatch_abbrev_tac ‘is_tree g’
  (* First, remove the top row of function nodes,  *)
  >> qspecl_then [‘g’, ‘IMAGE INR (range (3 * n + 1) (4 * n + 1))’] assume_tac is_tree_removeNodes_is_tree
  >> Q.UNABBREV_TAC ‘g’
  >> pop_assum (fn th => irule (iffRL th))
  >> conj_tac
  >- (rpt gen_tac >> strip_tac
      >> simp[adjacent_rcc_factor_graph]
      >> Cases_on ‘n'’ >> gvs[range_def]
     )
  >> conj_tac
  >- (rpt gen_tac >> strip_tac
      >> simp[degree_one_alt]
      >> Cases_on ‘n'’ >> gvs[range_def]
      >> simp[adjacent_rcc_factor_graph])
  >> simp[]
  >> qmatch_abbrev_tac ‘is_tree new_g’
  (* Next, remove the row of variable nodes underneath the top row of function nodes *)
  >> qspecl_then [‘new_g’, ‘IMAGE INR (range 0 n)’] assume_tac is_tree_removeNodes_is_tree
  >> Q.UNABBREV_TAC ‘new_g’
  >> pop_assum (fn th => irule (iffRL th))
  >> conj_tac
  >- (rpt gen_tac >> strip_tac
      >> simp[adjacent_removeNodes]
      >> simp[adjacent_rcc_factor_graph]
      >> Cases_on ‘n'’ >> gvs[range_def]
     )
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> simp[degree_one_alt]
      >> Cases_on ‘n'’ >> gvs[range_def]
      >> qexists ‘INR (5 * n + (y + 2))’
      >> simp[adjacent_removeNodes]
      >> simp[adjacent_rcc_factor_graph]
      >> gen_tac >> strip_tac
      >> gvs[adjacent_rcc_factor_graph]
     )
  >> simp[]
  >> qmatch_abbrev_tac ‘is_tree new_g’
  (* Next, remove the bottom row of function nodes
     (Working based on previous case) *)
  >> qspecl_then [‘new_g’, ‘IMAGE INR (range (4 * n + 1) (5 * n + 1))’] assume_tac is_tree_removeNodes_is_tree
  >> Q.UNABBREV_TAC ‘new_g’
  >> pop_assum (fn th => irule (iffRL th))
  >> conj_tac
  >- (rpt gen_tac >> strip_tac
      >> simp[adjacent_removeNodes]
      >> simp[adjacent_rcc_factor_graph]
      >> Cases_on ‘n'’ >> gvs[range_def]
     )
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> simp[degree_one_alt]
      >> Cases_on ‘n'’ >> gvs[range_def]
      >> qexists ‘INR (y - (3 * n + 1))’
      >> simp[adjacent_removeNodes]
      >> simp[adjacent_rcc_factor_graph]
     )
  >> simp[]
  >> qmatch_abbrev_tac ‘is_tree new_g’
  (* Next, remove the row of variable nodes above the previously removed row
     of function nodes (Working based on previous case) *)
  >> qspecl_then [‘new_g’, ‘IMAGE INR (range n (2 * n))’] assume_tac is_tree_removeNodes_is_tree
  >> Q.UNABBREV_TAC ‘new_g’
  >> pop_assum (fn th => irule (iffRL th))
  >> conj_tac
  >- (rpt gen_tac >> strip_tac
      >> simp[adjacent_removeNodes]
      >> simp[adjacent_rcc_factor_graph]
      >> Cases_on ‘n'’ >> gvs[range_def]
     )
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> simp[degree_one_alt]
      >> Cases_on ‘n'’ >> gvs[range_def]
      >> qexists ‘INR (4 * n + (y + 2))’
      >> simp[adjacent_removeNodes]
      >> simp[adjacent_rcc_factor_graph]
      >> gen_tac >> strip_tac
      >> gvs[adjacent_rcc_factor_graph]
     )
  >> simp[]
  >> qmatch_abbrev_tac ‘is_tree new_g’
  (* *)
  >> irule is_tree_degree_two
  >> rpt conj_tac
  (* All nodes are of degree at most 2 *)
  >- (unabbrev_all_tac
      >> simp[]
      >> gen_tac >> strip_tac
      >> Cases_on ‘n'’ >> gvs[]
      (* Combine the remove nodes calls into one *)
      >> simp[removeNodes_removeNodes]
      >> qmatch_abbrev_tac ‘degree (removeNodes removed_nodes _) _ ≤ 2’
      >> Q.SUBGOAL_THEN
          ‘removed_nodes = IMAGE INR (range 0 (2 * n) ∪
                                            range (3 * n + 1) (5 * n + 1))’
          (fn th => PURE_ONCE_REWRITE_TAC[th])
      >- (Q.UNABBREV_TAC ‘removed_nodes’
          >> PURE_REWRITE_TAC[GSYM IMAGE_UNION]
          >> cong_tac (SOME 1)
          >> simp[EXTENSION, range_def])
      >> qpat_x_assum ‘Abbrev (removed_nodes = _)’ kall_tac
      (* Split on the possibilities for x *)
      >> sg ‘x ∈ range (2 * n) (3 * n + 1) ∨
             x = 5 * n + 1 ∨
             x ∈ range (5 * n + 2) (6 * n + 2)’
      >- gvs[range_def] >> gvs[range_def]
      >- (simp[degree_removeNodes, adjacent_removeNodes]
          >> simp[adjacent_rcc_factor_graph, degree_rcc_factor_graph, range_def])
      >- (simp[degree_removeNodes, adjacent_removeNodes]
          >> simp[adjacent_rcc_factor_graph, degree_rcc_factor_graph, range_def])
      >> simp[degree_removeNodes]
      >> simp[degree_rcc_factor_graph]
      >> rw[]
      >> gvs[range_def]
      >> qmatch_abbrev_tac ‘4 ≤ CARD ns + 2’
      >> ‘2 ≤ CARD ns’ suffices_by decide_tac
      >> pop_assum (fn th => assume_tac (REWRITE_RULE [Abbrev_def] th))
      (* We need to find the two nodes that have been removed next to x,
         bringing its degree down to 2.*)
      >> sg ‘INR (x - (5 * n + 2)) ∈ ns ∧
             INR ((x - (5 * n + 2)) + n) ∈ ns’
      >- gvs[adjacent_rcc_factor_graph]
      (* We also need to know that our set of removed nodes is finite to make
         sure the cardinality makes sense *)
      >> sg ‘FINITE ns’            
      >- (pop_assum kall_tac >> pop_assum kall_tac
          >> simp[]
          >> PURE_ONCE_REWRITE_TAC[INTER_COMM]
          >> irule INTER_FINITE
          >> simp[]
          >> simp[GSYM count_def]
         )
      (* We no longer need the explicit form of ns, we only need the *)
      >> qpat_x_assum ‘ns = _’ kall_tac
      >> Cases_on ‘ns’ >> gnvs[]
      >> Cases_on ‘t’ >> gnvs[]
     )
  (* There is a node of degree 1 *)     
  >- (qexists ‘INR (5 * n + 1)’
      >> Q.UNABBREV_TAC ‘new_g’
      >> conj_tac
      >- simp[nodes_removeNodes, range_def]
      >> simp[removeNodes_removeNodes]
      >> DEP_PURE_ONCE_REWRITE_TAC[degree_removeNodes]
      >> conj_tac
      >- simp[range_def]
      >> simp[degree_rcc_factor_graph]
      >> rw[range_def]
      >> simp[SUB_EQ_ORIG]
      >> qmatch_abbrev_tac ‘CARD ns = 0’
      >> sg ‘FINITE ns’
      >- (Q.UNABBREV_TAC ‘ns’
          >> PURE_ONCE_REWRITE_TAC[INTER_COMM]
          >> irule INTER_FINITE
          >> simp[GSYM count_def])
      >> simp[]
      >> pop_assum kall_tac >> unabbrev_all_tac
      >> simp[EXTENSION]
      >> gen_tac
      >> Cases_on ‘x’ >> simp[]
      >> simp[adjacent_rcc_factor_graph]
      >> rw[]
      )
  (* The reduced graph is connected. We prove this by showing that it is
     isomorphic to a graph which consists of a line of nodes, which is
     connected *)
  >> qspecl_then [‘λx. if OUTR x = 5 * n + 1
                       then INR 0
                       else if OUTR x ∈ range (2 * n) (3 * n + 1)
                       then INR ((OUTR x - 2 * n) * 2 + 1)
                       else INR ((OUTR x - (5 * n + 2)) * 2 + 2)’,
                  ‘line_graph (2 * n + 2)’, ‘new_g’] irule
                 graph_isomorphism_connected
  >> simp[] >> qexists ‘n’
  >> simp[graph_isomorphism_def]
  >> REVERSE conj_tac
  >- (rpt gen_tac >> strip_tac
      >> simp[adjacent_line_graph]
      >> Q.UNABBREV_TAC ‘new_g’
      >> gvs[adjacent_removeNodes, range_def, adjacent_rcc_factor_graph]
      >- (CCONTR_TAC >> gvs[]
          >> (gvs[ADD1]
              (* The LHS of this assumption is odd while the RHS is even: a
               contradiction *)
              >> qpat_x_assum ‘2 * _ + 1 = 2 * _ + 2’ mp_tac
              >> rpt (pop_assum kall_tac)
              >> qmatch_abbrev_tac ‘2 * k + 1n = 2 * k2 + 2 ⇒ F’
              >> pop_assum kall_tac >> pop_assum kall_tac
              >> Q.SUBGOAL_THEN ‘2 * k2 + 2 = 2 * (k2 + 1)’
                  (fn th => PURE_ONCE_REWRITE_TAC[th])
              >- simp[]
              >> qmatch_abbrev_tac ‘2 * k + 1n = 2 * k3 ⇒ F’
              >> pop_assum kall_tac
              >> strip_tac
              >> Q.SUBGOAL_THEN ‘EVEN (2 * k3)’ mp_tac
              >- simp[EVEN_DOUBLE]
              >> Q.SUBGOAL_THEN ‘¬EVEN (2 * k + 1)’ mp_tac
              >- simp[EVEN_DOUBLE_ADD1]
              >> simp[Excl "EVEN_DOUBLE_ADD1"]
             )
         )
      >- rw[]
      >- rw[]
      >> rw[]
      >> (gvs[]
          >> qmatch_abbrev_tac ‘2 * k1 + 2 ≠ SUC (2 * k2 + 2)’
          >> rpt (pop_assum kall_tac)
         (* The LHS of this assumption is odd while the RHS is even: a
               contradiction *)
          >> simp[ADD1]
          >> ‘2 * k1 ≠ 2 * k2 + 1’ suffices_by simp[]
          >> disch_tac
          >> qspec_then ‘k1’ mp_tac EVEN_DOUBLE
          >> qspec_then ‘k2’ mp_tac EVEN_DOUBLE_ADD1
          >> simp[]
         )
     )
  >> simp[BIJ_IFF_INV]
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> Q.UNABBREV_TAC ‘new_g’
      >> pop_assum mp_tac
      >> simp[nodes_removeNodes, range_def, nodes_line_graph]
      >> strip_tac
      >> rw[]
      >> gvs[]
      >> decide_tac
     )
  >> qexists ‘λx. if EVEN (OUTR x)
                  then
                    if x = INR 0
                    then
                      INR (5 * n + 1)
                    else
                      INR (5 * n + 1 + ((OUTR x) DIV 2))
                  else INR (2 * n + ((OUTR x) DIV 2))’
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> simp[]
      >> Q.UNABBREV_TAC ‘new_g’
      >> simp[nodes_removeNodes]
      >> rw[range_def]
      >> (‘x' ≤ 2 * n + 1’ by simp[]
          >> ‘x' DIV 2 ≤ (2 * n + 1) DIV 2’ by simp[DIV_LE_MONOTONE]
          >> gvs[])
     )
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> simp[]
      >> Q.UNABBREV_TAC ‘new_g’
      >> gvs[nodes_removeNodes, range_def]
      >> rw[]
      >> qpat_x_assum ‘¬EVEN _’ mp_tac
      >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
      >> rw[]
      >> qmatch_abbrev_tac ‘EVEN (2 * k + 2)’
      >> Q.SUBGOAL_THEN ‘2 * k + 2 = 2 * (k + 1)’
          (fn th => PURE_ONCE_REWRITE_TAC[th])
      >- simp[]
      >> irule (EVEN_DOUBLE)
     )
  >> gen_tac
  >> strip_tac
  >> Q.UNABBREV_TAC ‘new_g’
  >> gvs[]
  >> rw[]
  >- (pop_assum mp_tac
      >> rw[]
      >- (disch_tac
          >> gvs[parity_equations_helperTheory.DIV_2_0])
      >> Cases_on ‘x'’ >> gvs[ADD1]
      >> gvs[LESS_EQ, ADD1]
      >> sg ‘(n' + 1) DIV 2 ≤ n’
      >- (pop_assum kall_tac >> pop_assum kall_tac
          >> ‘(n' + 1) ≤ 2 * n + 1’ by simp[]
          >> last_x_assum kall_tac
          >> ‘(n' + 1) DIV 2 ≤ (2 * n + 1) DIV 2’ by simp[DIV_LE_MONOTONE]
          >> last_x_assum kall_tac
          >> gvs[]
         )
      >> decide_tac
     )
  >- gvs[range_def]
  >- (gvs[range_def]
      >> gvs[EVEN_EXISTS])
  >> gvs[range_def]
  >> gvs[EVEN_ODD, ODD_EXISTS, ADD1]
QED

Theorem connected_rcc_factor_graph:
  ∀n p ps qs ts prior ds_s ds_p.
    connected (get_underlying_graph
               (rcc_factor_graph n p (ps,qs) ts prior (ds_s, ds_p))
              )
Proof
  rpt gen_tac
  >> qspecl_then [‘n’, ‘p’, ‘ps’, ‘qs’, ‘ts’, ‘prior’, ‘ds_s’, ‘ds_p’]
                 mp_tac is_tree_rcc_factor_graph
  >> simp[is_tree_def]
QED

Theorem le_num_extreal[simp]:
  ∀a b : num.
    &a : extreal ≤ &b : extreal ⇔ a ≤ b
Proof
  simp[extreal_of_num_def]
QED

Theorem extreal_of_num_eq_zero[simp]:
  ∀n : num.
    &n = 0 ⇔ n = 0n
Proof
  rpt gen_tac
  >> REVERSE EQ_TAC >> strip_tac
  >- simp[]
  >> Cases_on ‘n’ >> gvs[]
  >> ‘1 ≤ SUC n'’ by simp[]
  >> ‘&1 ≤ &(SUC n')’ by simp[]
  >> gvs[Excl "le_num_extreal"]
  >> gvs[]
QED

(* We use SUC n instead of n because division by zero is invalid *)
Theorem reciprocal_extreal_of_num_not_infty[simp]:
  ∀n : num.
    1 / &(SUC n) ≠ +∞ ∧ 1 / &(SUC n) ≠ −∞
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[GSYM normal_1]
  >> irule div_not_infty
  >> disch_tac
  >> gvs[]
QED

Theorem rcc_bcjr_fg_decode_empty[simp]:
  ∀p ps qs ts.
    rcc_bcjr_fg_decode p (ps,qs) ts [] = []
Proof
  rpt gen_tac
  >> simp[rcc_bcjr_fg_decode_def]
QED

Theorem map_decoder_bitwise_zero_n[simp]:
  ∀enc m p ds.
    map_decoder_bitwise enc 0 m p ds = []
Proof
  simp[map_decoder_bitwise_def]
QED

(* -------------------------------------------------------------------------- *)
(* The BCJR decoding process is equal to the expression for the MAP decoder   *)
(* given by                                                                   *)
(* map_decoder_bitwise_encode_recursive_parity_equation_with_systematic       *)
(* -------------------------------------------------------------------------- *)
Theorem rcc_factor_graph_compute:
  ∀n m p ps qs ts prior ds.
    0 < p ∧ p < 1 ∧
    LENGTH ds = m ∧
    m = 2 * n ⇒
    rcc_bcjr_fg_decode p (ps,qs) ts ds
    = map_decoder_bitwise
      (encode_recursive_parity_equation_with_systematic (ps, qs) ts)
      n m p ds

Proof
  rpt strip_tac
  (* Handle the special case of n = 0 *)
  >> Cases_on ‘n = 0’
  >- gvs[]
  (* Definition of factor graph decode *)
  >> gvs[rcc_bcjr_fg_decode_def]
  (* Use form of MAP decoder which is closest to the factor graph definition *)
  >> gvs[map_decoder_bitwise_encode_recursive_parity_equation_with_systematic]
  (* We need to prove each individual decoded bit is identical *)
  >> gvs[MAP_EQ_f] >> qx_gen_tac ‘i’
  (* Simplify new assumption  *)
  >> disch_tac >> gvs[MEM_COUNT_LIST]
  (* The argmax bools are equal if they are equal to each other up to a
     multiplicative constant *)
  >> irule argmax_bool_mul_const
  (* In this case, the constant is simply 1. *)
  >> qexists ‘1’ >> gvs[]
  (* Prove that the function we are argmaxing over is the same for each choice
     of boolean b. *)
  >> simp[FUN_EQ_THM] >> qx_gen_tac ‘b’
  (* *)
  >> DEP_PURE_ONCE_REWRITE_TAC[sp_output_final_result]
  >> conj_tac
  >- (rpt conj_tac
      >- (irule functions_noninfinite_rcc_factor_graph
          >> simp[]
          >> Cases_on ‘p = +∞’ >> gvs[]
          >> Cases_on ‘p = −∞’ >> gvs[]
          >> Cases_on ‘n’ >> gvs[]
         )
      >- simp[is_tree_rcc_factor_graph]
      >> PURE_ONCE_REWRITE_TAC[var_nodes_rcc_factor_graph]
      >> simp[]
     )
     (* *)
     
QED

(* -------------------------------------------------------------------------- *)
(* Computing the factor graph can give us a                                   *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
