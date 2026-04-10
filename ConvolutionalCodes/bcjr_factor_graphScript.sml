(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory bcjr_factor_graph

Ancestors binary_symmetric_channel combin donotexpand ecc_prob_space extreal factor_graph finite_map fsgraph fundamental genericGraph map_decoder_convolutional_code marker message_passing list range rich_list partite_ea pred_set prim_rec probability recursive_parity_equations state_machine tree useful_theorems wf_state_machine

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
(*            P(dp_0|cp_0)      P(dp_1|cp_1)           P(dp_{n-1}|cp_{n-1})   *)
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
    ds_s = DROP n ds;
    ds_p = TAKE n ds;
    prior = REPLICATE n (1 / 2);
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

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem map_decoder_bitwise_zero_n[simp]:
  ∀enc m p ds.
    map_decoder_bitwise enc 0 m p ds = []
Proof
  simp[map_decoder_bitwise_def]
QED

Theorem EQ_INTER_SELF[simp]:
  ∀a b.
    a = a ∩ b ⇔ a ⊆ b
Proof
  rpt gen_tac
  >> EQ_TAC
  >- (simp[SUBSET_DEF, EXTENSION]
      >> strip_tac >> strip_tac
      >> pop_assum $ qspec_then ‘x’ assume_tac
      >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
      >> simp[])
  >> simp[SUBSET_DEF, EXTENSION]
  >> strip_tac >> strip_tac
  >> pop_assum $ qspec_then ‘x’ assume_tac
  >> Cases_on ‘x ∈ a’ >> gvs[]
QED

Theorem GENLIST_ID_IFF[simp]:
  ∀f x.
    GENLIST f (LENGTH x) = x ⇔ (∀i. i < LENGTH x ⇒ f i = EL i x)
Proof
  rpt gen_tac
  >> Induct_on ‘x’ using SNOC_INDUCT
  >- simp[]
  >> gen_tac
  >> simp[GENLIST]
  (* We have used the inductive hypothesis and no longer need it *)
  >> pop_assum kall_tac
  (* *)
  >> EQ_TAC >> strip_tac
  >- (gen_tac >> strip_tac
      >> Cases_on ‘i = LENGTH x’
      >- simp[EL_LENGTH_SNOC]
      >> simp[EL_SNOC]
     )
  >> conj_tac
  >- (pop_assum $ qspec_then ‘LENGTH x’ assume_tac
      >> gvs[EL_LENGTH_SNOC])
  >> gen_tac >> strip_tac
  >> last_x_assum $ qspec_then ‘i’ assume_tac
  >> gvs[EL_SNOC]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: move to other file (possibly map_decoder_convolutional_codeScript,   *)
(* as this expression occurs in                                               *)
(*  map_decoder_bitwise_encode_recursive_parity_equation_with_systematic)     *)
(*                                                                            *)
(* Split P(ds_p,ds_s | bs) into P(ds_p | enc bs) * P(ds_s | bs)               *)
(* -------------------------------------------------------------------------- *)
Theorem cond_prob_received_given_sent_recursive_parity_equation_with_systematic_split:
  ∀n p ps qs ts bs ds.
    0 < p ∧
    p < 1 ∧
    LENGTH bs = n ∧
    LENGTH ds = 2 * n ⇒
    ∏ (λj.
         cond_prob (ecc_bsc_prob_space n (2 * n) p)
                   (event_received_bit_takes_value
                    (encode_recursive_parity_equation_with_systematic
                     (ps,qs) ts) n (2 * n) j (EL j ds))
                   (event_sent_bit_takes_value
                    (encode_recursive_parity_equation_with_systematic
                     (ps,qs) ts) n (2 * n) j
                    (EL j (encode_recursive_parity_equation_with_systematic
                           (ps,qs) ts bs)))
      ) (count (2 * n)) =
    let
      enc1 = encode_recursive_parity_equation (ps,qs) ts;
      enc2 = I;
    in
      ∏ (λj.
           cond_prob (ecc_bsc_prob_space n n p)
                     (event_received_bit_takes_value
                      enc1
                      n n j (EL j (TAKE n ds))
                     )
                     (event_sent_bit_takes_value
                      enc1
                      n n j (EL j (enc1 bs))
                     )
        ) (count n) *
      ∏ (λj.
           cond_prob (ecc_bsc_prob_space n n p)
                     (event_received_bit_takes_value
                      enc2
                      n n j (EL j (DROP n ds))
                     )
                     (event_sent_bit_takes_value
                      enc2
                      n n j (EL j (enc2 bs))
                     )
        ) (count n)
Proof
  rpt gen_tac >> strip_tac >> simp[Excl "I_THM"]
  >> simp[prob_received_given_sent_bit]
  >> PURE_ONCE_REWRITE_TAC[encode_recursive_parity_equation_with_systematic_def]
  >> qmatch_abbrev_tac ‘_ = RHS’
  >> Q.SUBGOAL_THEN ‘ds = TAKE n ds ++ DROP n ds’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- simp[]
  >> simp[bxor_append, sym_noise_mass_func_append]
QED

(* -------------------------------------------------------------------------- *)
(* This form is more convenient than the form of mul_not_infty2, because      *)
(* grouping together proofs that a variable is not +∞ with the proof that a   *)
(* variable is not −∞ allows us to perform both proofs at the same time,      *)
(* using, for example, another instance of this theorem.                      *)
(*                                                                            *)
(* Unfortunately, irule messes with the bracketing, so this isn't actually    *)
(* helpful when applying using irule.                                         *)
(* -------------------------------------------------------------------------- *)
Theorem mul_not_infty2_alt:
  ∀x y.
    (x ≠ −∞ ∧ x ≠ +∞) ∧
    (y ≠ −∞ ∧ y ≠ +∞) ⇒
    x * y ≠ −∞ ∧ x * y ≠ +∞
Proof
  rpt gen_tac >> strip_tac
  >> irule mul_not_infty2
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: probabilityTheory.COND_PROB_FINITE should have the +∞ and −∞ swapped *)
(* in order to match mul_not_infty2, EXTREAL_PROD_IMAGE_NOT_INFTY,            *)
(* PROB_FINITE, etc                                                           *)
(* -------------------------------------------------------------------------- *)
Theorem COND_PROB_FINITE_ALT:
  ∀p A B.
    prob_space p ∧ A ∈ events p ∧ B ∈ events p ∧ prob p B ≠ 0 ⇒
    cond_prob p A B ≠ −∞ ∧ cond_prob p A B ≠ +∞
Proof
  metis_tac[COND_PROB_FINITE]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: move to appropriate location                                         *)
(* -------------------------------------------------------------------------- *)
Theorem event_state_takes_value_inter_event_input_bit_takes_value_nonzero_prob:
  ∀n m p ps qs ts i b σ.
    0 < p ∧
    p < 1 ∧
    (∃bs. LENGTH bs = n ∧
          EL i bs = b ∧
          encode_recursive_parity_equation_state (ps,qs) ts (TAKE i bs) = σ) ⇒
    prob (ecc_bsc_prob_space n m p)
         (event_state_takes_value n m (ps,qs) ts i σ ∩
                                  event_input_bit_takes_value n m i b) ≠ 0
Proof
  rpt gen_tac >> strip_tac
  >> ‘0 ≤ p ∧ p ≤ 1’ by simp[le_lt]
  >> simp[prob_ecc_bsc_prob_space_zero, EVENTS_INTER]
  >> simp[event_state_takes_value_def,
          event_input_bit_takes_value_def]
  >> simp[EXTENSION]
  >> qexists ‘(bs, REPLICATE m ARB)’
  >> simp[]
QED

Theorem event_input_string_starts_with_empty[simp]:
  ∀n m.
    event_input_string_starts_with n m [] = event_universal n m
Proof
  rpt gen_tac
  >> simp[event_input_string_starts_with_def]
QED

Theorem HD_FRONT:
  ∀ls.
    2 ≤ LENGTH ls ⇒
    HD (FRONT ls) = HD ls
Proof
  rpt gen_tac >> strip_tac
  >> Cases_on ‘ls’ >> gvs[]
  >> Cases_on ‘t’ >> gvs[]
QED

Theorem prob_event_state_takes_value_inter_event_input_string_starts_with_zero:
  ∀n m p ps qs ts bs i σ.
    0 < p ∧
    p < 1 ∧
    i ≤ LENGTH bs ∧
    LENGTH bs ≤ n ⇒
    (prob (ecc_bsc_prob_space n m p)
          ((event_state_takes_value n m (ps,qs) ts i σ)
           ∩ (event_input_string_starts_with n m bs)
          ) = 0 ⇔
       encode_recursive_parity_equation_state (ps,qs) ts (TAKE i bs) ≠ σ)
Proof
  rpt gen_tac >> strip_tac
  >> ‘0 ≤ p ∧ p ≤ 1’ by simp[le_lt]
  >> simp[prob_ecc_bsc_prob_space_zero, EVENTS_INTER]
  >> EQ_TAC >> strip_tac
  >- (disch_tac
      >> qpat_x_assum ‘_ = ∅’ mp_tac >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
      >> simp[EXTENSION]
      >> qexists ‘(bs ++ REPLICATE (n - LENGTH bs) ARB, REPLICATE m ARB)’
      >> simp[event_state_takes_value_def, event_input_string_starts_with_def]
      >> ‘i - LENGTH bs = 0’ by decide_tac
      >> simp[TAKE_APPEND])
  >> simp[EXTENSION]
  >> gen_tac
  >> CCONTR_TAC >> gvs[]
  >> namedCases_on ‘x’ ["bs_example ns_example"]
  >> gvs[event_state_takes_value_def, event_input_string_starts_with_def]
  >> qpat_x_assum ‘encode_recursive_parity_equation_state _ _ _ ≠
                   encode_recursive_parity_equation_state _ _ _’ mp_tac
  >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
  >> cong_tac (SOME 1)
  >> simp[TAKE_EQ_TAKE_EL]
  >> gen_tac >> strip_tac
  >> irule is_prefix_el
  >> simp[]
QED

Theorem neg_extreal_inv:
  ∀x.
    x ≠ 0 ⇒
    -x⁻¹ = (-x)⁻¹
Proof
  gen_tac >> strip_tac
  >> Cases_on ‘x’ >> simp[extreal_inv_def, extreal_ainv_def]
  >> ‘r ≠ 0’ by (disch_tac >> gvs[])
  >> simp[extreal_inv_def, extreal_ainv_def, REAL_NEG_INV']
QED

Theorem infty_div_alt:
  ∀r.
    r ≠ 0 ⇒
    −∞ / Normal r = (if 0 < r then −∞ else +∞) ∧
    +∞ / Normal r = (if 0 < r then +∞ else −∞)
Proof
  rpt gen_tac >> strip_tac
  >> Cases_on ‘0 < r’ >> simp[]
  >- simp[infty_div]
  >> simp[extreal_div_def]
  >> PURE_ONCE_REWRITE_TAC[mul_comm]
  >> simp[cj 3 (extreal_inv_def)]
  >> simp[extreal_mul_def]
QED

Theorem div_eq_zero:
  ∀x y.
    y ≠ 0 ∧
    (x ≠ −∞ ∧ x ≠ +∞ ∨ y ≠ −∞ ∧ y ≠ +∞) ⇒
    (x / y = 0 ⇔ x = 0 ∨ y = −∞ ∨ y = +∞)
Proof
  rpt gen_tac >> disch_tac
  >> Cases_on ‘x = 0’ >> simp[zero_div]
  >> Cases_on ‘y’
  >- (Cases_on ‘x’
      >- gvs[]
      >- gvs[]
      >- simp[extreal_div_def]
     )
  >- (Cases_on ‘x’
      >- gvs[]
      >- gvs[]
      >- simp[extreal_div_def]
     )
  >> gvs[]
  >> Cases_on ‘x’
  >- (simp[infty_div_alt] >> rw[])
  >- (simp[infty_div_alt] >> rw[])
  >> simp[extreal_div_def, extreal_inv_def]
QED

Theorem event_input_string_starts_with_subset:
  ∀n m bs1 bs2.
    bs1 ≼ bs2 ⇒
    event_input_string_starts_with n m bs2 ⊆
                                   event_input_string_starts_with n m bs1
Proof
  rpt gen_tac
  >> strip_tac
  >> simp[event_input_string_starts_with_def, SUBSET_DEF]
  >> gen_tac >> strip_tac
  >> Cases_on ‘x’ >> gvs[]
  >> irule isPREFIX_TRANS
  >> qexists ‘bs2’ >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* If two strings are both prefixes of the same string then they are          *)
(* prefixes of each other, if the lengths work out that way.                  *)
(* -------------------------------------------------------------------------- *)
Theorem IS_PREFIX_TRANS_SWAPPED:
  ∀x y z.
    x ≼ y ∧
    z ≼ y ∧
    LENGTH x ≤ LENGTH z ⇒
    x ≼ z
Proof
  rpt gen_tac >> strip_tac
  >> gvs[IS_PREFIX_EQ_TAKE]
  >> qexists ‘n’
  >> simp[TAKE_TAKE]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to appropriate location                                         *)
(* -------------------------------------------------------------------------- *)
Theorem encode_recursive_parity_equation_state_snoc:
  ∀ps qs ts b bs.
    encode_recursive_parity_equation_state (ps,qs) ts (SNOC b bs) =
    encode_recursive_parity_equation_state
    (ps,qs) (encode_recursive_parity_equation_state (ps,qs) ts bs) [b]
Proof
  rpt gen_tac
  >> simp[SNOC_APPEND, GSYM encode_recursive_parity_equation_state_encode_recursive_parity_equation_state]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to appropriate location                                         *)
(* -------------------------------------------------------------------------- *)
Theorem encode_recursive_parity_equation_state_sequence_cons:
  ∀ps qs ts b bs.
    encode_recursive_parity_equation_state_sequence (ps,qs) ts (b::bs) =
    ts::encode_recursive_parity_equation_state_sequence
      (ps,qs) (encode_recursive_parity_equation_state (ps,qs) ts [b]) bs
Proof
  rpt gen_tac
  >> simp[encode_recursive_parity_equation_state_sequence_def,
          encode_recursive_parity_equation_state_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to appropriate location                                         *)
(* -------------------------------------------------------------------------- *)
Theorem encode_recursive_parity_equation_state_sequence_append:
  ∀ps qs ts bs1 bs2.
    encode_recursive_parity_equation_state_sequence (ps,qs) ts (bs1 ++ bs2) =
    encode_recursive_parity_equation_state_sequence (ps,qs) ts bs1 ++
    TL (encode_recursive_parity_equation_state_sequence
        (ps,qs) (encode_recursive_parity_equation_state (ps,qs) ts bs1) bs2)
Proof
  Induct_on ‘bs1’
  >- (rpt gen_tac
      >> simp[]
      >> Cases_on ‘bs2’ >> simp[encode_recursive_parity_equation_state_sequence_def]
     )
  >> rpt gen_tac
  >> simp[encode_recursive_parity_equation_state_sequence_cons]
  >> simp[encode_recursive_parity_equation_state_def]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to appropriate location                                         *)
(* -------------------------------------------------------------------------- *)
Theorem encode_recursive_parity_equation_state_sequence_snoc:
  ∀ps qs ts b bs.
    encode_recursive_parity_equation_state_sequence (ps,qs) ts (SNOC b bs) =
    (encode_recursive_parity_equation_state_sequence (ps,qs) ts bs) ++
    TL (encode_recursive_parity_equation_state_sequence
        (ps,qs) (encode_recursive_parity_equation_state (ps,qs) ts bs) [b])
Proof
  rpt gen_tac
  >> simp[SNOC_APPEND, encode_recursive_parity_equation_state_sequence_append]
QED

(* -------------------------------------------------------------------------- *)
(* The probability of each subsequent step being valid, when comparing the    *)
(* given choice of σs to the given choice of σs, will be zero if and only if  *)
(* the overall probability of all the steps combined is zero.                 *)
(* -------------------------------------------------------------------------- *)
Theorem extreal_prod_image_state_given_input_zero:
  ∀n m p ps qs ts bs σs l.
    0 < p ∧
    p < 1 ∧
    HD σs = ts ∧
    LENGTH σs = LENGTH bs + 1 ∧
    l = LENGTH bs ∧
    LENGTH bs ≤ n ⇒
    (∏ (λi.
          cond_prob (ecc_bsc_prob_space n m p)
                   (event_state_takes_value n m (ps,qs) ts (i + 1) (EL (i + 1) σs))
                   ((event_state_takes_value n m (ps,qs) ts i (EL i σs))
                    ∩ event_input_bit_takes_value n m i (EL i bs))
      ) (count l) = 0 ⇔
      cond_prob (ecc_bsc_prob_space n m p)
              (event_state_sequence_starts_with n m (ps,qs) ts σs)
              (event_input_string_starts_with n m bs) = 0)
Proof
  Induct_on ‘l’
  >- (rpt gen_tac >> rpt disch_tac
      >> ‘0 ≤ p ∧ p ≤ 1’ by simp[le_lt]
      >> gvs[]
      >> Cases_on ‘σs’ >> gvs[]
      >> simp[event_state_sequence_starts_with_sing]
     )
  >> rpt gen_tac >> strip_tac
  (* Reduce to smaller l on the LHS *)
  >> PURE_ONCE_REWRITE_TAC[COUNT_SUC]
  >> simp[cj 2 EXTREAL_PROD_IMAGE_THM]
  (* Apply the inductive hypothesis to transform the LHS towards the RHS *)
  >> last_x_assum $ qspecl_then [‘n’, ‘m’, ‘p’, ‘ps’, ‘qs’, ‘ts’, ‘FRONT bs’, ‘FRONT σs’] assume_tac
  >> ‘0 ≤ p ∧ p ≤ 1’ by simp[le_lt]
  >> gvs[ADD1]
  >> Cases_on ‘σs = []’ >- gvs[]
  >> Cases_on ‘bs = []’ >- gvs[]
  >> qpat_x_assum ‘l + 1 = LENGTH bs’ (fn th => assume_tac (GSYM th))
  >> gvs[HD_FRONT, LENGTH_FRONT, PRE_SUB1]
  (* Rewrite the inductive term in the goal to match the inductive term in the
     inductive hypothesis, so we can apply it to transform the LHS towards the
     RHS. *)
  >> qmatch_abbrev_tac ‘(_ = 0 ∨ ind_term_goal = 0 : extreal) ⇔ _’
  >> qmatch_asmsub_abbrev_tac ‘ind_term_assum = 0 ⇔ cond_prob _ _ _ = 0’
  >> Q.SUBGOAL_THEN ‘ind_term_goal = ind_term_assum’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- (Q.UNABBREV_TAC ‘ind_term_goal’ >> Q.UNABBREV_TAC ‘ind_term_assum’
      >> irule EXTREAL_PROD_IMAGE_EQ
      >> gen_tac >> strip_tac
      >> simp[EL_FRONT, LENGTH_FRONT, NULL_EQ_NIL]
      >> pop_assum mp_tac >> simp[] >> disch_tac
      >> simp[EL_FRONT, NULL_EQ_NIL, LENGTH_FRONT, PRE_SUB1]
     )
  >> simp[]
  (* We've applied the inductive hypothesis and no longer need it. *)
  >> qpat_x_assum ‘ind_term_assum = 0 ⇔ _’ kall_tac
  >> Q.UNABBREV_TAC ‘ind_term_goal’ >> Q.UNABBREV_TAC ‘ind_term_assum’
  (* Break apart the RHS to reduce to a smaller σs, to match the LHS *)
  >> qmatch_abbrev_tac ‘LHS = _’
  >> Q.SUBGOAL_THEN ‘σs = SNOC (LAST σs) (FRONT σs)’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- simp[SNOC_LAST_FRONT]
  >> simp[event_state_sequence_starts_with_snoc, LENGTH_FRONT, PRE_SUB1]
  (* *)
  >> PURE_REWRITE_TAC[cond_prob_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[div_eq_zero]
  >> conj_tac
  >- (conj_tac
      >- (irule event_input_string_starts_with_nonzero_prob
          >> simp[])
      >> disj2_tac
      >> irule PROB_FINITE
      >> simp[])
  >> simp[PROB_FINITE, SNOC_LAST_FRONT]
  (* *)
  >> Q.UNABBREV_TAC ‘LHS’
  >> qmatch_abbrev_tac ‘ldisj ∨ _ ⇔ _’
  >> PURE_REWRITE_TAC[cond_prob_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[div_eq_zero]
  >> conj_tac
  >- (conj_tac
      >- (irule event_input_string_starts_with_nonzero_prob
          >> simp[LENGTH_FRONT])
      >> disj2_tac
      >> irule PROB_FINITE
      >> simp[]
     )
  >> simp[PROB_FINITE]
  (* Handle the case where there is an inconsistency between bs and σs within
     the front of bs. In this case, the LHS is true, and this is clearly a
     subcase of the RHS so the RHS is also true.
     The only remaining cases are that there is an inconsistency between them
     in the last of bs, or that there is no inconsistency. *)
  >> Cases_on ‘prob (ecc_bsc_prob_space n m p)
               ((event_state_sequence_starts_with n m (ps,qs) (HD σs) (FRONT σs))
                ∩ event_input_string_starts_with n m (FRONT bs)) = 0’ >> simp[]
  >- (irule (iffLR le_antisym)
      >> REVERSE conj_tac
      >- (irule PROB_POSITIVE
          >> simp[EVENTS_INTER])
      >> qpat_x_assum ‘prob _ (_ ∩ _) = 0’
                      (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
      >> irule PROB_INCREASING
      >> simp[EVENTS_INTER]
      >> conj_tac
      >- simp[SUBSET_DEF]
      >> irule INTER_SUBSET_ALT
      >> disj2_tac
      >> irule event_input_string_starts_with_subset
      >> simp[IS_PREFIX_BUTLAST'])
  (* *)
  >> Q.UNABBREV_TAC ‘ldisj’
  (* We now know that bs and σs are valid if we fix all but the last bits of
     bs and σs.
.
     Therefore, if we fix the second last bit of σs and the last bit of bs, then
     this is possible and has probability nonzero (using the prior choice of
     all but the last of bs and σs, and we may fix an additional bit of bs
     without any problems).
.
     Therefore, we may safely cancel out the denominator of the conditional
     probability. *)
  >> PURE_ONCE_REWRITE_TAC[cond_prob_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[div_eq_zero]
  >> conj_tac
  >- (simp[EVENTS_INTER]
      >> conj_tac
      >- (gvs[prob_ecc_bsc_prob_space_zero, EVENTS_INTER]
          >> gvs[EXTENSION]
          >> namedCases_on ‘x’ ["bs_given ns"]
          (* bs_given starts with the front of bs and creates the front of σs *)
          >> gvs[event_state_sequence_starts_with_def,
                 event_input_string_starts_with_def,
                 event_state_takes_value_def,
                 event_input_bit_takes_value_def]
          (* We now need our bits to be fixed to start with the entirety of bs,
             and ns doesn't matter. *)
          >> qexists ‘(bs ++ REPLICATE (LENGTH bs_given - LENGTH bs) F, ns)’
          >> simp[]
          >> REVERSE conj_tac
          >- simp[EL_APPEND]
          >> simp[GSYM el_encode_recursive_parity_equation_state_sequence]
          (* We want to use is_prefix_el_better, so rewrite our lists to be in
             the appropriate form so that our precondition matches our existing
             assumption after applying that. *)
          >> SYM_TAC
          >> Q.SUBGOAL_THEN ‘EL l σs = EL l (FRONT σs)’
              (fn th => PURE_ONCE_REWRITE_TAC[th])
          >- (DEP_PURE_ONCE_REWRITE_TAC[FRONT_EL]
              >> simp[LENGTH_FRONT])
          >> qmatch_abbrev_tac ‘_ = EL _ σs_goal’
          >> qmatch_asmsub_abbrev_tac ‘FRONT σs ≼ σs_asm’
          >> Q.SUBGOAL_THEN ‘EL l σs_goal = EL l σs_asm’
              (fn th => PURE_ONCE_REWRITE_TAC[th])
          >> Q.UNABBREV_TAC ‘σs_goal’ >> Q.UNABBREV_TAC ‘σs_asm’
          >- (simp[el_encode_recursive_parity_equation_state_sequence]
              >> cong_tac (SOME 1)
              >> simp[TAKE_EQ_TAKE_EL]
              >> gen_tac >> strip_tac
              >> simp[EL_APPEND]
              >> Q.SUBGOAL_THEN ‘EL i bs = EL i (FRONT bs)’
                  (fn th => PURE_ONCE_REWRITE_TAC[th])
              >- (DEP_PURE_ONCE_REWRITE_TAC[FRONT_EL]
                  >> simp[LENGTH_FRONT])
              >> irule is_prefix_el_better
              >> simp[LENGTH_FRONT]
             )
          >> irule is_prefix_el_better
          >> simp[LENGTH_FRONT]
         )
      >> disj1_tac
      >> irule PROB_FINITE
      >> simp[EVENTS_INTER]
     )
  >> simp[PROB_FINITE, EVENTS_INTER]
  (* First, prove that if the front of the sequence is valid but the last step
     of the sequence is invalid, then the overall sequence is invalid. *)
  >> EQ_TAC >> strip_tac
  >- (qpat_x_assum ‘prob _ _ ≠ 0’ kall_tac
      >> gvs[prob_ecc_bsc_prob_space_zero, EVENTS_INTER, EXTENSION]
      >> gen_tac
      >> namedCases_on ‘x’ ["bs2 ns2"]
      >> pop_assum $ qspec_then ‘(bs2, ns2)’ mp_tac >> strip_tac
      >- (disj1_tac >> disj2_tac
          >> simp[LAST_EL, PRE_SUB1])
      >- (disj1_tac >> disj1_tac
          >> gvs[event_state_takes_value_def,
                 event_state_sequence_starts_with_def]
          >> rpt strip_tac >> gvs[]
          >> drule is_prefix_el
          >> disch_then $ qspec_then ‘l’ mp_tac
          >> simp[LENGTH_FRONT]
          >> simp[FRONT_EL, LENGTH_FRONT]
          >> simp[el_encode_recursive_parity_equation_state_sequence]
         )
      >> disj2_tac
      >> gvs[event_input_bit_takes_value_def,
             event_input_string_starts_with_def]
      >> rpt strip_tac >> gvs[]
      >> drule is_prefix_el
      >> disch_then $ qspec_then ‘l’ mp_tac
      >> simp[]
     )
  (* Now we prove that if the front of the sequence is valid and the last
     step of the sequence is valid, then the sequence as a whole is valid. *)
  >> CCONTR_TAC
  >> qpat_x_assum ‘prob _ _ = 0’ mp_tac
  >> PURE_ONCE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
  >> gvs[prob_ecc_bsc_prob_space_zero, EVENTS_INTER]
  >> gvs[EXTENSION]
  >> namedCases_on ‘x’ ["bs2 ns2"]
  >> namedCases_on ‘x'’ ["bs3 ns3"]
  >> qexists ‘(bs ++ REPLICATE (n - LENGTH bs) F, REPLICATE m F)’
  >> gvs[event_state_sequence_starts_with_def,
         event_input_string_starts_with_def,
         event_state_takes_value_def,
         event_input_bit_takes_value_def]
  >> conj_tac
  >- (qsuff_tac ‘FRONT σs ≼ encode_recursive_parity_equation_state_sequence
                 (ps,qs) (HD σs) (FRONT bs) ∧
                 encode_recursive_parity_equation_state_sequence
                 (ps,qs) (HD σs) (FRONT bs) ≼
                 encode_recursive_parity_equation_state_sequence (ps,qs) (HD σs)
                 (bs ⧺ REPLICATE (LENGTH bs2 − (l + 1)) F)’
      >- (strip_tac
          >> irule isPREFIX_TRANS
          >> qexists ‘encode_recursive_parity_equation_state_sequence
                      (ps,qs) (HD σs) (FRONT bs)’
          >> simp[]
         )
      >> conj_tac
      >- (irule IS_PREFIX_TRANS_SWAPPED
          >> simp[LENGTH_FRONT]
          >> qexists ‘encode_recursive_parity_equation_state_sequence
                      (ps,qs) (HD σs) bs2’
          >> simp[encode_recursive_parity_equation_state_sequence_prefix_mono]
         )
      >> irule encode_recursive_parity_equation_state_sequence_prefix_mono
      >> irule isPREFIX_TRANS
      >> qexists ‘bs’
      >> simp[IS_PREFIX_BUTLAST']
     )
  >> simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, LAST_EL, PRE_SUB1]
  (* The second to last element of σs is reached through the process of applying
     bs2, which matches with the front of bs. The last element is reached
     through the process of applying the appropriate element of bs3, which
     starts from the same state as applying the front of bs.
.
     1. Rewrite σs[l + 1] as the state reached via bs3
     2. Break down the state reached via bs3 into all the first steps followed
        by the last step
     3. Rewrite all the first steps as σs[l]
     4. Similarly break down the left hand side into all the first steps of bs
        followed by the last step of bs
     5. The first steps of bs matches with σs[l]. The last step of bs matches
        with the same step of bs3.
   *)
  (* Step 1 *)
  >> qpat_x_assum ‘_ = EL (l + 1) σs’ (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
  (* Step 2 *)
  >> simp[TAKE_EL_SNOC]
  >> simp[encode_recursive_parity_equation_state_snoc]
  (* Step 3 (automatically performed already) *)
  (* Step 4 *)
  >> Q.SUBGOAL_THEN ‘bs = SNOC (LAST bs) (FRONT bs)’
      (fn th => simp[Once th, Cong LHS_CONG])
  >- simp[SNOC_LAST_FRONT]
  >> simp[encode_recursive_parity_equation_state_snoc]
  (* Step 5 *)
  >> simp[LAST_EL, PRE_SUB1]
  >> cong_tac (SOME 1)
  >> simp[FRONT_BY_TAKE]
  >> simp[GSYM el_encode_recursive_parity_equation_state_sequence]
  >> Q.SUBGOAL_THEN ‘EL l σs = EL l (FRONT σs)’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- simp[FRONT_EL, LENGTH_FRONT]
  >> Q.SUBGOAL_THEN
      ‘EL l (encode_recursive_parity_equation_state_sequence
             (ps,qs) (HD σs) bs) =
       EL l (encode_recursive_parity_equation_state_sequence
             (ps,qs) (HD σs) (FRONT bs))’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- (SYM_TAC
      >> irule is_prefix_el_better
      >> simp[LENGTH_FRONT]
      >> irule encode_recursive_parity_equation_state_sequence_prefix_mono
      >> simp[IS_PREFIX_BUTLAST'])
  >> irule is_prefix_el_better
  >> simp[LENGTH_FRONT]
  >> irule IS_PREFIX_TRANS_SWAPPED
  >> simp[LENGTH_FRONT]
  >> qexists ‘encode_recursive_parity_equation_state_sequence
              (ps,qs) (HD σs) bs2’
  >> simp[]
  >> irule encode_recursive_parity_equation_state_sequence_prefix_mono
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* A version of extreal_prod_image_state_given_input which works even for     *)
(* probabilities other than zero.                                             *)
(*                                                                            *)
(* Possible improvement: could allow this theorem to work when producting     *)
(* only up to a part of the state sequence, rather than the entire state      *)
(* sequence.                                                                  *)
(* -------------------------------------------------------------------------- *)
(* TODO: Finish this                                                          *)
(* -------------------------------------------------------------------------- *)
(*Theorem extreal_prod_image_state_given_input:
  ∀n m p ps qs ts bs σs l.
    0 < p ∧
    p < 1 ∧
    HD σs = ts ∧
    LENGTH σs = LENGTH bs + 1 ∧
    l = LENGTH bs ∧
    LENGTH bs ≤ n ⇒
    ∏ (λi.
         (* TODO: consider uncommenting this if and else *)
         (*if (event_state_takes_value n m (ps,qs) ts i (EL i σs))
             ∩ event_input_bit_takes_value n m i (EL i bs) ≠ ∅
         then*)
         cond_prob (ecc_bsc_prob_space n m p)
                   (event_state_takes_value n m (ps,qs) ts (i + 1) (EL (i + 1) σs))
                   ((event_state_takes_value n m (ps,qs) ts i (EL i σs))
                    ∩ event_input_bit_takes_value n m i (EL i bs))
      (* else
           0*)
      ) (count l) =
    cond_prob (ecc_bsc_prob_space n m p)
              (event_state_sequence_starts_with n m (ps,qs) ts σs)
              (event_input_string_starts_with n m bs)

Proof

  Induct_on ‘l’
  >- (rpt gen_tac >> rpt disch_tac
      >> ‘0 ≤ p ∧ p ≤ 1’ by simp[le_lt]
      >> gvs[]
      >> Cases_on ‘σs’ >> gvs[]
      >> simp[event_state_sequence_starts_with_sing]
     )
  >> rpt gen_tac >> strip_tac
  (* Reduce to smaller l on the LHS *)
  >> PURE_ONCE_REWRITE_TAC[COUNT_SUC]
  >> simp[cj 2 EXTREAL_PROD_IMAGE_THM]
  (* Apply the inductive hypothesis to transform the LHS towards the RHS *)
  >> last_x_assum $ qspecl_then [‘n’, ‘m’, ‘p’, ‘ps’, ‘qs’, ‘ts’, ‘FRONT bs’, ‘FRONT σs’] assume_tac
  >> ‘0 ≤ p ∧ p ≤ 1’ by simp[le_lt]
  >> gvs[ADD1]
  >> qpat_x_assum ‘l + 1 = LENGTH bs’ (fn th => assume_tac (GSYM th))
  >> Cases_on ‘σs = []’ >- gvs[]
  >> Cases_on ‘bs = []’ >- gvs[]
  >> gvs[HD_FRONT, LENGTH_FRONT, PRE_SUB1]
  (* Rewrite the inductive term in the goal to match the inductive term in the
     inductive hypothesis, so we can apply it to transform the LHS towards the
     RHS. *)
  >> qmatch_abbrev_tac ‘_ * ind_term_goal = _ : extreal’
  >> qmatch_asmsub_abbrev_tac ‘ind_term_assum = cond_prob _ _ _’
  >> Q.SUBGOAL_THEN ‘ind_term_goal = ind_term_assum’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- (Q.UNABBREV_TAC ‘ind_term_goal’ >> Q.UNABBREV_TAC ‘ind_term_assum’
      >> irule EXTREAL_PROD_IMAGE_EQ
      >> gen_tac >> strip_tac
      >> simp[EL_FRONT, LENGTH_FRONT, NULL_EQ_NIL]
      >> pop_assum mp_tac >> simp[] >> disch_tac
      >> simp[EL_FRONT, NULL_EQ_NIL, LENGTH_FRONT, PRE_SUB1]
     )
  >> simp[]
  (* We've applied the inductive hypothesis and no longer need it. *)
  >> qpat_x_assum ‘ind_term_assum = _’ kall_tac
  >> Q.UNABBREV_TAC ‘ind_term_goal’ >> Q.UNABBREV_TAC ‘ind_term_assum’
  (* Break apart the RHS to reduce to a smaller σs, to match the LHS *)
  >> qmatch_abbrev_tac ‘LHS = _’
  >> Q.SUBGOAL_THEN ‘σs = SNOC (LAST σs) (FRONT σs)’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- simp[SNOC_LAST_FRONT]
  >> simp[event_state_sequence_starts_with_snoc, LENGTH_FRONT, PRE_SUB1]
  (* Want to prove:
     P(σs | bs) = P(FRONT σs | FRONT bs) * P(LAST σs | SND_LAST σs, SND_LAST bs)
     P(σs | bs) = P(FRONT σs | bs) * P(LAST σs | FRONT σs, bs)
     P(σs | bs) = P(FRONT σs, LAST σs | bs)     <- we are here, working upwards
                = P(σs | bs)
.
     So we see our method for proving what we want to prove.
.
     So we want to apply apply COND_PROB_INTER_SPLIT to split up our
     probability as indicated by the above working. We first rename our events
     to nicer names, prove useful statements about these events, and handle the
     special case in which we cannot apply COND_PROB_INTER_SPLIT.
 *)
  >> qmatch_abbrev_tac ‘LHS = cond_prob _ (B ∩ A) C’
  (* Swap A and B to get the appropriate ordering for COND_PROB_INTER_SPLIT *)
  >> PURE_ONCE_REWRITE_TAC[INTER_COMM]
  (* Generally useful theorems about A, B, and C *)
  >> ‘A ∈ events (ecc_bsc_prob_space n m p)’ by simp[Abbr ‘A’]
  >> ‘B ∈ events (ecc_bsc_prob_space n m p)’ by simp[Abbr ‘B’]
  >> ‘C ∈ events (ecc_bsc_prob_space n m p)’ by simp[Abbr ‘C’]
  >> sg ‘prob (ecc_bsc_prob_space n m p) C ≠ 0’
  >- (MAP_EVERY Q.UNABBREV_TAC [‘A’, ‘B’, ‘C’]
      >> irule event_input_string_starts_with_nonzero_prob
      >> simp[LENGTH_FRONT, GSYM ADD1])
  (* Consider the special case where we can't split P(A ∩ B | C) into
     P(A | B ∩ C) * P(B | C) because B ∩ C is empty and hence P(A | B ∩ C) has
     denominator zero.
.
     On the right hand side, we get P(A ∩ B ∩ C) / P (C). The numerator
     is zero because P(B ∩ C) = 0, while the denominator is nonzero.
.
     On the left hand side, *)
  >> Cases_on ‘prob (ecc_bsc_prob_space n m p) (B ∩ C) = 0’
  (* ---
     Note: here I could possibly use extreal_prod_image_state_given_input_zero,
     the version fo this theorem that holds for probability zero?
     --- *)

  >- (sg ‘prob (ecc_bsc_prob_space n m p) (A ∩ B ∩ C) = 0’
      >- (irule (iffLR le_antisym)
          >> REVERSE conj_tac
          >- (irule PROB_POSITIVE
              >> simp[EVENTS_INTER, Abbr ‘A’, Abbr ‘B’, Abbr ‘C’])
          >> qpat_x_assum ‘prob _ (B ∩ C) = 0’
                          (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
          >> irule PROB_INCREASING
          >> simp[EVENTS_INTER]
          >> simp[SUBSET_DEF]
         )
      >> simp[cond_prob_def, zero_div]
      (* Now we simplify the LHS *)
      >> Q.UNABBREV_TAC ‘LHS’
      >> qmatch_abbrev_tac ‘cond_prob _ A_lhs C_lhs_sing * cond_prob _ B_lhs C_lhs_mul = 0’
      >> ‘C_lhs_mul ∈ events (ecc_bsc_prob_space n m p)’ by simp[Abbr ‘C_lhs_mul’]
      >> gvs[SNOC_LAST_FRONT]
      >> simp[cond_prob_def]
      >> sg ‘prob (ecc_bsc_prob_space n m p) C_lhs_mul ≠ 0’
      >- (Q.UNABBREV_TAC ‘C_lhs_mul’
          >> irule event_input_string_starts_with_nonzero_prob
          >> simp[LENGTH_FRONT])
      >> qmatch_abbrev_tac ‘disj1 ∨ _’
      >> DEP_PURE_ONCE_REWRITE_TAC[div_eq_zero]
      >> conj_tac
      >- (simp[]
          >> disj1_tac
          >> irule PROB_FINITE
          >> simp[EVENTS_INTER, Abbr ‘B’, Abbr ‘C_lhs_mul’]
         )
      >> simp[PROB_FINITE, Abbr ‘disj1’]
      (* Since P(B, C) = 0, the bs are incompatible with the front of the σs.
         Either the front of the bs is incompatible with the front of the σs, or
         the front of the bs is compatible with the front of the σs and the last
         of the bs is incompatible with the front of the σs.
.
         In the first case, our second disjunct holds.
         In the second case, our first disjunct holds.
 *)
      >> Cases_on ‘prob (ecc_bsc_prob_space n m p) (B ∩ C_lhs_mul) = 0’ >> simp[]

      (* *)
      >> DEP_PURE_ONCE_REWRITE_TAC[div_eq_zero]
      >> conj_tac
      >- (conj_tac
          >-
         )
      >>
      >>
     )
  (* We can now split our probability into a product of the probability of the
     current step multiplied by the probability of all the previous steps, as
     per our plan, because we have handled the special case in which the
     precondition of this theorem fails. *)
  >> DEP_PURE_ONCE_REWRITE_TAC[COND_PROB_INTER_SPLIT]
  >> conj_tac
  >- simp[Abbr ‘A’, Abbr ‘B’, Abbr ‘C’]
  (* Now we remove unnecssary information from the denominator, as planned *)



        (* Reduce to smaller l on the RHS *)
        >>
QED*)

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem zero_div_alt:
  ∀x y.
    x = 0 ∧
    y ≠ 0 ⇒
    x / y = 0
Proof
  simp[zero_div]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem DRESTRICT_FUN_FMAP:
  ∀f S1 S2.
    FINITE S1 ∧
    FINITE S2 ⇒
    DRESTRICT (FUN_FMAP f S1) S2 = FUN_FMAP f (S1 ∩ S2)
Proof
  rpt gen_tac >> strip_tac
  >> irule (iffLR fmap_EQ_THM)
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> gvs[FDOM_DRESTRICT, FUN_FMAP_DEF, DRESTRICT_DEF]
     )
  >> simp[FDOM_DRESTRICT]
QED

Theorem EXTREAL_PROD_IMAGE_MUL:
  ∀s f g.
    FINITE s ⇒
    ∏ f s * ∏ g s = ∏ (λx. f x * g x) s
Proof
  rpt gen_tac >> strip_tac
  >> Induct_on ‘s’ using FINITE_INDUCT
  >> conj_tac
  >- simp[]
  >> gen_tac >> strip_tac >> gen_tac >> strip_tac
  >> simp[EXTREAL_PROD_IMAGE_PROPERTY]
  >> simp[DELETE_NON_ELEMENT_RWT]
  >> simp[AC mul_assoc mul_comm]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to other file                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem IFF_SYM:
  ∀a b.
    (a ⇔ b) ⇔ (b ⇔ a)
Proof
  rpt gen_tac
  >> Cases_on ‘a’ >> simp[]
QED

(* TODO: Finish something along these lines *)
(*Theorem cond_prob_event_state_sequence_starts_with_event_input_string_starts_with:
  ∀n m p ps qs ts bs σs.
    cond_prob (ecc_bsc_prob_space n m p)
              (event_state_sequence_starts_with n m (ps,qs) ts σs)
              (event_input_string_starts_with n m bs) = 0 ⇔
      σs = encode_recursive_parity_equation_state_sequence (ps,qs) ts bs
Proof
QED*)

(* -------------------------------------------------------------------------- *)
(* TODO: Move to better file                                                  *)
(* -------------------------------------------------------------------------- *)
Theorem length_el_encode_recursive_parity_equation_state_sequence[simp]:
  ∀ps qs ts bs i.
    i ≤ LENGTH bs ⇒
    LENGTH (EL i (encode_recursive_parity_equation_state_sequence (ps,qs) ts bs)) =
    LENGTH ts
Proof
  rpt gen_tac
  >> Induct_on ‘i’
  >- simp[]
  >> strip_tac
  >> simp[el_encode_recursive_parity_equation_state_sequence]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to better file                                                  *)
(* -------------------------------------------------------------------------- *)
Theorem el_encode_recursive_parity_equation:
  ∀ps qs ts bs i.
    i + 1 ≤ LENGTH bs ⇒
    EL i (encode_recursive_parity_equation (ps,qs) ts bs) =
    HD (encode_recursive_parity_equation
        (ps,qs)
        (encode_recursive_parity_equation_state (ps,qs) ts (TAKE i bs))
        [EL i bs])
Proof
  rpt gen_tac >> strip_tac
  >> simp[encode_recursive_parity_equation_take_el_sing]
QED

Theorem event_universal_subset:
  ∀n m p e.
    e ∈ events (ecc_bsc_prob_space n m p) ⇒
    (event_universal n m ⊆ e ⇔ e = event_universal n m)
Proof
  rpt gen_tac >> strip_tac
  >> EQ_TAC >> strip_tac
  >- (PURE_REWRITE_TAC[EXTENSION]
      >> gen_tac
      >> EQ_TAC >> strip_tac
      >- (Cases_on ‘x’ >> simp[]
          >> gvs[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
          >> last_x_assum drule
          >> simp[])
      >> gvs[SUBSET_DEF])
  >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to better file                                                  *)
(* -------------------------------------------------------------------------- *)
Theorem subset_event_universal:
  ∀n m p e.
    e ∈ events (ecc_bsc_prob_space n m p) ⇒
    e ⊆ event_universal n m
Proof
  rpt gen_tac >> strip_tac
  >> gvs[events_ecc_bsc_prob_space, POW_DEF, SUBSET_DEF]
  >> gen_tac >> strip_tac
  >> last_x_assum $ qspec_then ‘x’ assume_tac
  >> gvs[]
  >> Cases_on ‘x’ >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Move to better file                                                  *)
(* -------------------------------------------------------------------------- *)
Theorem prob_ecc_bsc_prob_space_one:
  ∀n m p e.
    0 < p ∧
    p < 1 ∧
    e ∈ events (ecc_bsc_prob_space n m p) ⇒
    (prob (ecc_bsc_prob_space n m p) e = 1 ⇔ e = event_universal n m)
Proof
  rpt gen_tac
  >> strip_tac
  >> ‘0 ≤ p ∧ p ≤ 1’ by simp[le_lt]
  >> Q.SUBGOAL_THEN
      ‘prob (ecc_bsc_prob_space n m p) e = 1 ⇔
         prob (ecc_bsc_prob_space n m p) (event_universal n m DIFF e) = 0’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- (DEP_PURE_ONCE_REWRITE_TAC[PROB_DIFF_SUBSET]
      >> conj_tac
      >- (simp[]
          >> irule subset_event_universal
          >> qexists ‘p’
          >> simp[])
      >> simp[]
      >> DEP_PURE_ONCE_REWRITE_TAC[eq_sub_radd]
      >> simp[]
      >> irule PROB_FINITE
      >> simp[]
     )
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> conj_tac
  >- (simp[]
      >> PURE_REWRITE_TAC[GSYM p_space_ecc_bsc_prob_space]
      >> irule EVENTS_COMPL
      >> simp[])
  >> simp[SUBSET_DIFF_EMPTY]
  >> irule event_universal_subset
  >> qexists ‘p’
  >> simp[]
QED

Theorem prob_inter_eq:
  ∀n m p e1 e2.
    0 < p ∧
    p < 1 ∧
    e1 ∈ events (ecc_bsc_prob_space n m p) ∧
    e2 ∈ events (ecc_bsc_prob_space n m p) ⇒
    (prob (ecc_bsc_prob_space n m p) (e1 ∩ e2) =
     prob (ecc_bsc_prob_space n m p) e2 ⇔
       e2 ⊆ e1)
Proof
  rpt gen_tac >> strip_tac
  >> ‘0 ≤ p ∧ p ≤ 1’ by simp[le_lt]
  >> qmatch_abbrev_tac ‘prob1 = prob2 ⇔ _’
  >> sg ‘prob1 ≠ −∞ ∧ prob1 ≠ +∞’
  >- (Q.UNABBREV_TAC ‘prob1’
      >> irule PROB_FINITE
      >> simp[EVENTS_INTER])
  >> sg ‘prob2 ≠ −∞ ∧ prob2 ≠ +∞’
  >- (Q.UNABBREV_TAC ‘prob2’
      >> irule PROB_FINITE
      >> simp[EVENTS_INTER])
  >> Q.SUBGOAL_THEN ‘prob1 = prob2 ⇔ prob2 - prob1 = 0’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- simp[eq_sub_radd, EQ_SYM_EQ]
  >> unabbrev_all_tac
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM PROB_DIFF_SUBSET]
  >> conj_tac
  >- simp[EVENTS_INTER]
  >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
  >> conj_tac
  >- (simp[]
      >> irule EVENTS_DIFF
      >> simp[EVENTS_INTER])
  >> simp[SUBSET_DIFF_EMPTY]
QED

Theorem cond_prob_one:
  ∀n m p e1 e2.
    0 < p ∧
    p < 1 ∧
    e1 ∈ events (ecc_bsc_prob_space n m p) ∧
    e2 ∈ events (ecc_bsc_prob_space n m p) ∧
    e2 ≠ ∅ ⇒
    (cond_prob (ecc_bsc_prob_space n m p) e1 e2 = 1 ⇔ e2 ⊆ e1)
Proof
  rpt gen_tac >> strip_tac
  >> ‘0 ≤ p ∧ p ≤ 1’ by simp[le_lt]
  >> REVERSE EQ_TAC >> strip_tac
  >- (DEP_PURE_ONCE_REWRITE_TAC[GSYM COND_PROB_INTER_ID]
      >> conj_tac
      >- simp[EVENTS_INTER]
      >> drule (iffRL (cj 2 INTER_SUBSET_EQN))
      >> simp[] >> strip_tac
      >> irule COND_PROB_ITSELF
      >> simp[]
      >> DEP_PURE_ONCE_REWRITE_TAC[prob_ecc_bsc_prob_space_zero]
      >> simp[])
  >> pop_assum mp_tac
  >> PURE_REWRITE_TAC[cond_prob_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[ldiv_eq]
  >> conj_tac
  >- (conj_tac
      >- (PURE_REWRITE_TAC[lt_le]
          >> simp[prob_ecc_bsc_prob_space_zero, PROB_POSITIVE])
      >> simp[PROB_FINITE])
  >> simp[]
  >> simp[prob_inter_eq]
QED

(* -------------------------------------------------------------------------- *)
(* The BCJR decoding process is equal to the expression for the MAP decoder   *)
(* given by                                                                   *)
(* map_decoder_bitwise_encode_recursive_parity_equation_with_systematic       *)
(* -------------------------------------------------------------------------- *)
(* TODO: Can any theorems be extracted from here? e.g., if we have a valid    *)
(* bs σs cs_p, then certain events take probability 1? if we have an invalid  *)
(* bs σs cs_p, then certain events take probability 0?                        *)
(* In particular, would be nice to have a general theorem relating            *)
(* probabilities in the factor graph world to probabilities in the            *)
(* sum of products world.                                                     *)
(* Similar working is repeated several times in here                          *)
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
  >> ‘0 ≤ p ∧ p ≤ 1’ by simp[lt_imp_le]
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
  (* Rewrite the output of the sum-product algorithm in terms of a sum of
     products *)
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
  (* Simplify application of FUN_FMAP *)
  >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
  >> conj_tac
  >- (simp[]
      >> simp[val_map_assignments_def]
      >> simp[cj 2 FUN_FMAP_DEF, get_variable_length_map_rcc_factor_graph]
     )
  (* *)
  >> simp[nodes_rcc_factor_graph]
  >> simp[sum_prod_def]
  (* TODO: Probably a bad idea to do this, because I would have to do this
     on the right hand side as well. *)
  (* Get rid of all the terms with invalid cs_p on the left hand side: in these
     cases, our sum will be zero *)
  (*>> qmatch_abbrev_tac ‘∑ f _ = RHS : extreal’
  >> Q.SUBGOAL_THEN
      ‘∑ f (mdr_summed_out_values_2 n ts i b) =
       ∑ f ((mdr_summed_out_values_2 n ts i b)
            ∩ {(bs, σs, cs_p) | cs_p = encode_recursive_parity_equation
                                       (ps,qs) ts bs})’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- (SYM_TAC
      >> irule EXTREAL_SUM_IMAGE_INTER_ELIM
      >> REVERSE conj_tac
      >- (simp[]
          >> disj1_tac
          >> gen_tac >> strip_tac
          >> Q.UNABBREV_TAC ‘f’
          >> namedCases_on ‘x’ ["bs', σs', cs_p'"]
          >> simp[]
         )
         EXTREAL_SUM_IMAGE_INTER_NONZERO
         EXTREAL_SUM_IMAGE_INTER_ELIM
     )
  >> Q.UNABBREV_TAC ‘f’ >> Q.UNABBREV_TAC ‘RHS’*)
  (* *)
  >> irule EXTREAL_SUM_IMAGE_CHANGE_SET
  >> rpt conj_tac
  >- simp[]
  >- (disj1_tac
      >> gen_tac >> strip_tac
      >> namedCases_on ‘x’ ["bs σs cs_p"]
      >> simp[]
      >> qmatch_abbrev_tac ‘x1 * x2 * x3 * x4 ≠ −∞’
      (* The case where the starting state of σs is incorrect is a special
         case that we have to handle separately, because then our expression
         is invalid and we have denominator 0. *)
      >> REVERSE $ Cases_on ‘HD σs = ts’
      >- (‘x1 = 0’ suffices_by simp[]
          >> MAP_EVERY Q.UNABBREV_TAC [‘x1’, ‘x2’, ‘x3’, ‘x4’]
          >> simp[entire]
          >> disj2_tac
          >> simp[event_state_takes_value_def]
         )
      (* The case where σs is invalid with respect to bs has to be handled with
         caution, because in this case, we may have denominator 0.
         We use a part of input_state_parity_valid. *)
      >> REVERSE $ Cases_on
                 ‘σs = encode_recursive_parity_equation_state_sequence
                       (ps,qs) ts bs’
      >- (‘x2 = 0’ suffices_by simp[] (* In this case, x2 = 0 *)
          >> MAP_EVERY Q.UNABBREV_TAC [‘x1’, ‘x2’, ‘x3’, ‘x4’]
          >> DEP_PURE_ONCE_REWRITE_TAC[extreal_prod_image_state_given_input_zero]
          >> conj_tac
          >- gvs[mdr_summed_out_values_2_def]
          >> simp[cond_prob_def]
          >> irule zero_div_alt
          >> conj_tac
          >- (irule event_input_string_starts_with_nonzero_prob
              >> simp[]
              >> gvs[mdr_summed_out_values_2_def]
             )
          >> simp[prob_ecc_bsc_prob_space_zero, EVENTS_INTER]
          >> irule (iffRL EXTENSION) >> gen_tac >> simp[]
          >> CCONTR_TAC >> gvs[]
          >> gvs[event_state_sequence_starts_with_def,
                 event_input_string_starts_with_def,
                 mdr_summed_out_values_2_def]
          >> ‘bs = bs'’ by (irule (iffLR IS_PREFIX_LENGTH_ANTI) >> simp[])
          >> qpat_x_assum ‘bs ≼ bs'’ kall_tac
          >> qpat_x_assum ‘LENGTH bs' = LENGTH bs’ kall_tac
          >> gvs[]
          >> qpat_x_assum ‘σs ≠ _’ mp_tac
          >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
          >> irule (iffLR IS_PREFIX_LENGTH_ANTI)
          >> simp[]
         )
      >> ‘x1 ≠ −∞ ∧ x1 ≠ +∞ ∧
          x2 ≠ −∞ ∧ x2 ≠ +∞ ∧
          x3 ≠ −∞ ∧ x3 ≠ +∞ ∧
          x4 ≠ −∞ ∧ x4 ≠ +∞’ suffices_by (strip_tac >> simp[mul_not_infty2])
      >> MAP_EVERY Q.UNABBREV_TAC [‘x1’, ‘x2’, ‘x3’, ‘x4’]
      >> rpt conj_tac
      >- simp[mul_not_infty2, EXTREAL_PROD_IMAGE_NOT_INFTY, PROB_FINITE]
      >- simp[mul_not_infty2, EXTREAL_PROD_IMAGE_NOT_INFTY, PROB_FINITE]
      >- (irule (cj 1 EXTREAL_PROD_IMAGE_NOT_INFTY)
          >> simp[]
          >> gen_tac >> strip_tac
          >> irule COND_PROB_FINITE_ALT
          >> simp[EVENTS_INTER]
          >> irule event_state_takes_value_inter_event_input_bit_takes_value_nonzero_prob
          >> simp[]
          >> qexists ‘bs’
          >> gvs[mdr_summed_out_values_2_def]
          >> simp[el_encode_recursive_parity_equation_state_sequence]
         )
      >- (irule (cj 2 EXTREAL_PROD_IMAGE_NOT_INFTY)
          >> simp[]
          >> gen_tac >> strip_tac
          >> irule COND_PROB_FINITE_ALT
          >> simp[EVENTS_INTER]
          >> irule event_state_takes_value_inter_event_input_bit_takes_value_nonzero_prob
          >> simp[]
          >> qexists ‘bs’
          >> gvs[mdr_summed_out_values_2_def]
          >> simp[el_encode_recursive_parity_equation_state_sequence]
         )
      >- (irule (cj 1 EXTREAL_PROD_IMAGE_NOT_INFTY)
          >> simp[]
          >> gen_tac >> strip_tac
          >> irule COND_PROB_FINITE_ALT
          >> simp[EVENTS_INTER]
          >> irule event_state_takes_value_inter_event_input_bit_takes_value_nonzero_prob
          >> simp[]
          >> qexists ‘bs’
          >> gvs[mdr_summed_out_values_2_def]
          >> simp[el_encode_recursive_parity_equation_state_sequence]
         )
      >- (irule (cj 2 EXTREAL_PROD_IMAGE_NOT_INFTY)
          >> simp[]
          >> gen_tac >> strip_tac
          >> irule COND_PROB_FINITE_ALT
          >> simp[EVENTS_INTER]
          >> irule event_state_takes_value_inter_event_input_bit_takes_value_nonzero_prob
          >> simp[]
          >> qexists ‘bs’
          >> gvs[mdr_summed_out_values_2_def]
          >> simp[el_encode_recursive_parity_equation_state_sequence]
         )
      >- (irule (cj 1 EXTREAL_PROD_IMAGE_NOT_INFTY)
          >> simp[]
          >> gen_tac >> strip_tac
          >> irule COND_PROB_FINITE_ALT
          >> simp[]
          >> simp[prob_event_sent_bit_takes_value_nonzero]
          >> gvs[mdr_summed_out_values_2_def]
         )
      >> irule (cj 2 EXTREAL_PROD_IMAGE_NOT_INFTY)
      >> simp[]
      >> gen_tac >> strip_tac
      >> irule COND_PROB_FINITE_ALT
      >> simp[]
      >> simp[prob_event_sent_bit_takes_value_nonzero]
      >> gvs[mdr_summed_out_values_2_def]
     )
  >> qexists ‘λ(bs,σs,cs_p).
                FUN_FMAP (λx.
                            if OUTR x ∈ range 0 n
                            then [EL (OUTR x) bs]
                            else if OUTR x ∈ range n (2 * n)
                            then [EL (OUTR x - n) cs_p]
                            else EL (OUTR x - 2 * n) σs
                         )
                         (IMAGE INR (range 0 (3 * n + 1)))’
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> namedCases_on ‘x’ ["bs σs cs_p"]
      >> simp[]
      (* Simplify set being producted over on the RHS *)
      >> qmatch_abbrev_tac ‘_ = EXTREAL_PROD_IMAGE _ (node_set ∩ fun_node_set)’
      >> Q.SUBGOAL_THEN ‘node_set ∩ fun_node_set = fun_node_set’
          (fn th => PURE_ONCE_REWRITE_TAC[th])
      >-  (Q.UNABBREV_TAC ‘node_set’ >> Q.UNABBREV_TAC ‘fun_node_set’
           >> irule SUBSET_ANTISYM
           >> conj_tac
           >- simp[]
           >> simp[SUBSET_DEF, range_def]
          )
      >> Q.UNABBREV_TAC ‘node_set’
      (* The LHS is split up into:
         ∏ P(b_i) *
         P(σ_0) *
         ∏ P(σ_{i+1} | σ_i, b_i) *
         ∏ P(c_i | σ_i, b_i) *
         ∏ P(d_s_i, d_p_i | c_s_i, c_p_i)
.
         b: the original message
         c_s: the systematic encoded bits
         c_p: the parity encoded bits
         d_s: the systematic recevied bits
         d_p: the parity received bits
.
         We can split the last product into
         ∏ P(d_s_i | c_s_i) * ∏ P(d_p_i | c_p_i)
.
         Then ∏ P(b_i) ∏ P(d_s_i | c_s_i) is equivalent to the product of the
         top row of nodes in the factor graph, and P(σ_0) is equivalent to the
         leftmost node in the factor graph, and  ∏ P(σ_{i+1} | σ_i, b_i) *
         ∏ P(c_i | σ_i, b_i) is equivalent to the middle row of nodes in the
         factor graph, and ∏ P(d_p_i | c_p_i) is equivalent to
         the  bottom row of nodes in the factor graph.
.
         So we start by splitting up the last product on the LHS in the way
         mentioned above
       *)
      >> DEP_PURE_ONCE_REWRITE_TAC[cond_prob_received_given_sent_recursive_parity_equation_with_systematic_split]
      >> conj_tac
      >- gvs[mdr_summed_out_values_2_def]
      >> simp[]
      (* Now we split the RHS up so as to match the LHS, according to the
         working above *)
      >> Q.SUBGOAL_THEN ‘fun_node_set =
                         IMAGE INR (range (3 * n + 1) (4 * n + 1)) ∪
                               IMAGE INR (range (4 * n + 1) (5 * n + 1)) ∪
                               {INR (5 * n + 1)} ∪
                               IMAGE INR (range (5 * n + 2) (6 * n + 2))’
          (fn th => PURE_ONCE_REWRITE_TAC[th]) >> Q.UNABBREV_TAC ‘fun_node_set’
      >- (simp[range_def, EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac >> simp[])
      (* Finish splitting up the RHS (so we have a product, not a union) *)
      >> DEP_PURE_REWRITE_TAC[EXTREAL_PROD_IMAGE_DISJOINT_UNION]
      >> conj_tac
      >- (simp[DISJOINT_ALT, range_def]
          >> rpt conj_tac
          >> (gen_tac >> strip_tac >> gen_tac >> strip_tac >> gvs[]))
      >> PURE_REWRITE_TAC[mul_assoc]
      (* We need to prove the equivalence of like terms on the LHS and RHS *)
      >> qmatch_abbrev_tac
         ‘input_probs * initial_state_prob * transition_probs * encoded_probs *
          encoded_noise_probs * systematic_noise_probs
          =
          systematic_node_probs * encoded_node_probs * initial_state_node_prob
          * state_node_probs : extreal’
      >>  ‘input_probs * systematic_noise_probs = systematic_node_probs ∧
           initial_state_prob = initial_state_node_prob ∧
           (if input_state_parity_valid (ps,qs) ts (bs, σs, cs_p)
            then
              transition_probs * encoded_probs = state_node_probs ∧
              encoded_noise_probs = encoded_node_probs
            else
              transition_probs * encoded_probs = 0 ∧ state_node_probs = 0 ∨
              initial_state_prob = 0 ∧ initial_state_node_prob = 0
           )
          ’ suffices_by
        (REVERSE $ Cases_on ‘input_state_parity_valid (ps,qs) ts (bs, σs, cs_p)’
         >> simp[]
         >- (rpt (pop_assum kall_tac) >> strip_tac >> simp[])
         >> rpt (pop_assum kall_tac) >> strip_tac >> gvs[AC mul_comm mul_assoc]
        )
      >> rpt conj_tac
      (* Equivalence of expressions for systematic component *)
      >- (unabbrev_all_tac
          >> simp[EXTREAL_PROD_IMAGE_MUL]
          >> irule EXTREAL_PROD_IMAGE_CONG_DIFF_SETS
          >> simp[]
          >> qexists ‘λx. INR (3 * n + 1 + x)’
          >> conj_tac
          >- (simp[BIJ_THM]
              >> conj_tac >> simp[range_def]
              >> gen_tac >> strip_tac
              >> simp[EXISTS_UNIQUE_THM]
              >> qexists ‘x - 1 - 3 * n’
              >> simp[]
             )
          >> gen_tac >> strip_tac
          >> simp[]
          >> DEP_PURE_ONCE_REWRITE_TAC[DRESTRICT_FUN_FMAP]
          >> conj_tac
          >- (simp[]
              >> irule SUBSET_FINITE
              >> qexists ‘IMAGE INR (count (6 * n + 2))’
              >> simp[SUBSET_DEF])
          >> qmatch_abbrev_tac ‘_ = _ ' (FUN_FMAP _ cur_adj_nodes)’
          >> Q.SUBGOAL_THEN ‘cur_adj_nodes = {INR x}’
              (fn th => PURE_ONCE_REWRITE_TAC[th])
          >- (Q.UNABBREV_TAC ‘cur_adj_nodes’
              >> simp[EXTENSION]
              >> gen_tac
              >> Cases_on ‘x'’ >> simp[range_def]
              >> Cases_on ‘y = x’ >> gvs[]
              >- simp[adjacent_rcc_factor_graph]
              >> CCONTR_TAC >> gvs[]
              >> gvs[adjacent_rcc_factor_graph]
             )
          >> qpat_x_assum ‘Abbrev (cur_adj_nodes = _)’ kall_tac
          >> simp[get_function_map_rcc_factor_graph]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- simp[range_def]
          >> simp[]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- (simp[var_assignments_def]
              >> simp[cj 2 FUN_FMAP_DEF]
              >> rw[]
              >> gvs[range_def])
          >> simp[cj 2 FUN_FMAP_DEF]
          >> simp[range_def]
          >> DEP_PURE_ONCE_REWRITE_TAC[cond_prob_event_received_bit_takes_value_event_sent_bit_takes_value]
          >> conj_tac
          >- (simp[]
              >> qexists ‘bs’
              >> simp[]
              >> gvs[mdr_summed_out_values_2_def])
          >> simp[EL_TAKE]
          >> simp[EL_DROP]
          >> simp[sym_noise_mass_func_def]
          >> simp[IFF_SYM]
         )
      (* Equivalence of expressions for initial state component *)
      >- (unabbrev_all_tac
          >> simp[]
          >> simp[get_function_map_rcc_factor_graph]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- simp[range_def]
          >> simp[]
          >> DEP_PURE_ONCE_REWRITE_TAC[DRESTRICT_FUN_FMAP]
          >> conj_tac
          >- (simp[]
              >> irule SUBSET_FINITE
              >> qexists ‘IMAGE INR (count (6 * n + 2))’
              >> simp[SUBSET_DEF])
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- (simp[]
              >> simp[var_assignments_def]
              >> conj_tac
              >- (simp[EXTENSION]
                  >> gen_tac
                  >> REVERSE EQ_TAC >> strip_tac
                  >- simp[adjacent_rcc_factor_graph, range_def]
                  >> gvs[adjacent_rcc_factor_graph, range_def])
              >> gen_tac >> strip_tac
              >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
              >> conj_tac
              >- (simp[] >> gvs[range_def])
              >> gvs[range_def]
              >> simp[cj 2 FUN_FMAP_DEF]
              >> rw[]
              >> gvs[mdr_summed_out_values_2_def]
              >> first_x_assum irule
              >> irule EL_MEM
              >> simp[]
             )
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- (simp[range_def]
              >> simp[adjacent_rcc_factor_graph])
          >> simp[range_def]
          >> simp[event_state_takes_value_def] >> rw[]
         )
      (* Special case where the head of σs is invalid *)
      >> REVERSE $ Cases_on ‘HD σs = ts’
      >- (sg ‘¬input_state_parity_valid (ps,qs) ts (bs,σs,cs_p)’
          >- (simp[input_state_parity_valid_def]
              >> Cases_on ‘σs’ >> Cases_on ‘bs’ >> gvs[encode_recursive_parity_equation_state_sequence_def])
          >> simp[]
          >> disj2_tac
          >> unabbrev_all_tac
          >> conj_tac
          >- simp[event_state_takes_value_def]
          >> irule EXTREAL_PROD_IMAGE_0
          >> simp[]
          >> DEP_PURE_ONCE_REWRITE_TAC[DRESTRICT_FUN_FMAP]
          >> conj_tac
          >- (simp[]
              >> irule SUBSET_FINITE
              >> qexists ‘IMAGE INR (count (6 * n + 2))’
              >> simp[SUBSET_DEF]
             )
          >> qmatch_abbrev_tac ‘_ ' (FUN_FMAP _ cur_adj_nodes) = _’
          >> Q.SUBGOAL_THEN ‘cur_adj_nodes = {INR (2 * n)}’
              (fn th => PURE_ONCE_REWRITE_TAC[th])
          >- (Q.UNABBREV_TAC ‘cur_adj_nodes’
              >> simp[EXTENSION]
              >> gen_tac
              >> Cases_on ‘x’ >> gvs[]
              >> simp[range_def]
              >> Cases_on ‘y = 2 * n’ >> gvs[]
              >- simp[adjacent_rcc_factor_graph]
              >> CCONTR_TAC
              >> gvs[]
              >> gvs[adjacent_rcc_factor_graph]
             )
          >> qpat_x_assum ‘Abbrev (cur_adj_nodes = _)’ kall_tac
          >> simp[get_function_map_rcc_factor_graph]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- simp[range_def]
          >> simp[]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- (simp[]
              >> simp[var_assignments_def]
              >> simp[cj 2 FUN_FMAP_DEF]
              >> simp[range_def]
              >> gvs[mdr_summed_out_values_2_def]
              >> first_x_assum irule
              >> Cases_on ‘σs’ >- gvs[]
              >> simp[]
             )
          >> rw[]
          >> simp[cj 2 FUN_FMAP_DEF]
          >> simp[range_def]
         )
      (* Special case where the rest of σs is invalid *)
      >> REVERSE $ Cases_on
                 ‘σs = encode_recursive_parity_equation_state_sequence
                       (ps,qs) ts bs’
      >- (simp[input_state_parity_valid_def]
          >> disj1_tac
          >> conj_tac
          >- (disj1_tac
              >> unabbrev_all_tac
              >> DEP_PURE_ONCE_REWRITE_TAC
                 [extreal_prod_image_state_given_input_zero]
              >> conj_tac
              >- (simp[] >> gvs[mdr_summed_out_values_2_def])
              >> PURE_REWRITE_TAC[cond_prob_def]
              >> DEP_PURE_ONCE_REWRITE_TAC[div_eq_zero]
              >> conj_tac
              >- (conj_tac
                  >- (irule event_input_string_starts_with_nonzero_prob
                      >> simp[]
                      >> gvs[mdr_summed_out_values_2_def])
                  >> disj1_tac
                  >> irule PROB_FINITE
                  >> simp[EVENTS_INTER]
                 )
              >> disj1_tac
              >> simp[prob_ecc_bsc_prob_space_zero, EVENTS_INTER]
              >> simp[EXTENSION]
              >> gen_tac
              >> CCONTR_TAC
              >> gvs[event_state_sequence_starts_with_def,
                     event_input_string_starts_with_def]
              >> gvs [mdr_summed_out_values_2_def]
              >> sg ‘σs = encode_recursive_parity_equation_state_sequence
                          (ps,qs) (HD σs) bs'’
              >- (irule (iffLR IS_PREFIX_LENGTH_ANTI)
                  >> simp[])
              >> sg ‘bs = bs'’
              >- (irule (iffLR IS_PREFIX_LENGTH_ANTI)
                  >> simp[])
              >> qpat_x_assum ‘σs = _’ mp_tac >> qpat_x_assum ‘σs ≠ _’ mp_tac
              >> simp[]
             )
          >> qspecl_then [‘σs’, ‘encode_recursive_parity_equation_state_sequence
                                 (ps,qs) ts bs’] mp_tac
                         exists_point_of_divergence_nonequal_list
          >> simp[]
          >> sg ‘LENGTH σs = LENGTH bs + 1’
          >- gvs[mdr_summed_out_values_2_def]
          >> simp[]
          >> strip_tac
          >> unabbrev_all_tac
          >> irule EXTREAL_PROD_IMAGE_0
          >> simp[]
          >> qexists ‘INR (5 * n + 2 + j)’
          >> simp[]
          >> conj_tac
          >- (simp[range_def] >> gvs[mdr_summed_out_values_2_def])
          (* *)
          >> DEP_PURE_ONCE_REWRITE_TAC[DRESTRICT_FUN_FMAP]
          >> conj_tac
          >- (simp[]
              >> irule SUBSET_FINITE
              >> qexists ‘IMAGE INR (count (6 * n + 2))’
              >> simp[SUBSET_DEF]
             )
          >> qmatch_abbrev_tac ‘_ ' (FUN_FMAP _ s) = 0’
          >> sg ‘s = {INR j; INR (n + j); INR (2 * n + j); INR (2 * n + 1 + j)}’
          >- (Q.UNABBREV_TAC ‘s’
              >> simp[EXTENSION]
              >> gen_tac
              >> Cases_on ‘x = INR j’
              >- (simp[adjacent_rcc_factor_graph, range_def]
                  >> gvs[mdr_summed_out_values_2_def])
              >> Cases_on ‘x = INR (j + n)’
              >- (simp[adjacent_rcc_factor_graph, range_def]
                  >> gvs[mdr_summed_out_values_2_def])
              >> Cases_on ‘x = INR (j + 2 * n)’
              >- (simp[adjacent_rcc_factor_graph, range_def]
                  >> gvs[mdr_summed_out_values_2_def])
              >> Cases_on ‘x = INR (j + 2 * n + 1)’
              >- (simp[adjacent_rcc_factor_graph, range_def]
                  >> gvs[mdr_summed_out_values_2_def])
              >> gvs[]
              >> CCONTR_TAC >> gvs[]
              >> gvs[adjacent_rcc_factor_graph]
             )
          >> simp[get_function_map_rcc_factor_graph]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- (simp[]
              >> simp[range_def]
              >> gvs[mdr_summed_out_values_2_def]
             )
          >> simp[]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- (simp[]
              >> simp[var_assignments_def]
              >> conj_tac
              >- simp[func_node_state_adjacent_nodes_def]
              >> gen_tac
              >> strip_tac
              >> simp[cj 2 FUN_FMAP_DEF]
              >> simp[range_def]
              >> simp[el_encode_recursive_parity_equation_state_sequence]
              >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
              >> conj_tac
              >- (simp[] >> gvs[mdr_summed_out_values_2_def])
              >> simp[]
              >> rw[]
              >> gvs[mdr_summed_out_values_2_def]
              >> last_x_assum irule
              >> simp[EL_MEM]
             )
          >> qpat_x_assum ‘s = _’ kall_tac
          >> qpat_x_assum ‘Abbrev (s = _)’ kall_tac
          >> simp[func_node_state_fn_def]
          >> simp[cj 2 FUN_FMAP_DEF]
          >> simp[range_def]
          >> ‘j < n’ by gvs[mdr_summed_out_values_2_def]
          >> simp[]
          >> simp[el_encode_recursive_parity_equation_state_sequence]
          >> strip_tac
          >> simp[]
          >> strip_tac
          (* EL (j + 1) σs ≠ _ contradicts the other expression for EL (j + 1) σs *)
          >> qpat_x_assum ‘EL (j + 1) σs ≠ _’ mp_tac
          >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
          >> qpat_x_assum ‘_ = EL (j + 1) σs’
                          (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
          >> simp[el_encode_recursive_parity_equation_state_sequence]
          >> simp[encode_recursive_parity_equation_state_encode_recursive_parity_equation_state]
          >> simp[TAKE_EL_SNOC]
         )
       (* Special case where cs_p is invalid *)
       >> REVERSE $ Cases_on ‘cs_p =
                              encode_recursive_parity_equation (ps,qs) ts bs’
      >- (‘¬input_state_parity_valid (ps,qs) ts (bs,σs,cs_p)’
            by simp[input_state_parity_valid_def]
          >> simp[]
          >> disj1_tac
          >> conj_tac >> unabbrev_all_tac
          >- (disj2_tac
              >> irule EXTREAL_PROD_IMAGE_0
              >> simp[]
              >> CCONTR_TAC
              >> qpat_x_assum ‘cs_p ≠ _’ mp_tac
              >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
              >> simp[LIST_EQ_REWRITE]
              >> conj_tac >- gvs[mdr_summed_out_values_2_def]
              >> gen_tac >> strip_tac
              >> CCONTR_TAC
              >> qpat_x_assum ‘¬∃x._’ mp_tac
              >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
              >> qexists ‘x’
              >> sg ‘x < n’
              >- gvs[mdr_summed_out_values_2_def]
              >> qpat_x_assum
                 ‘σs = encode_recursive_parity_equation_state_sequence _ _ _’
                 (fn th => assume_tac (GSYM th))
              >> simp[cond_prob_def]
              >> DEP_PURE_ONCE_REWRITE_TAC[div_eq_zero]
              >> conj_tac
              >- (conj_tac
                  >- (simp[]
                      >> irule event_state_takes_value_inter_event_input_bit_takes_value_nonzero_prob
                      >> simp[]
                      >> qexists ‘bs’
                      >> conj_tac >- gvs[mdr_summed_out_values_2_def]
                      >> simp[]
                      >> qpat_x_assum ‘_ = σs’ (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
                      >> DEP_PURE_ONCE_REWRITE_TAC[el_encode_recursive_parity_equation_state_sequence]
                      >> gvs[mdr_summed_out_values_2_def]
                     )
                  >> disj1_tac
                  >> irule PROB_FINITE
                  >> simp[EVENTS_INTER]
                 )
              >> disj1_tac
              >> simp[prob_ecc_bsc_prob_space_zero, EVENTS_INTER]
              >> simp[EXTENSION]
              >> gen_tac
              >> simp[event_srcc_parity_bit_takes_value_def,
                      event_state_takes_value_def,
                      event_input_bit_takes_value_def]
              >> CCONTR_TAC >> gvs[]
              (* Now we find a contradiction in the two equations involving
                 EL x cs_p *)
              >> qpat_x_assum ‘EL x cs_p ⇎ _’ mp_tac
              >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
              >> qpat_x_assum ‘_ ⇔ EL x cs_p’
                              (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
              >> simp[el_encode_recursive_parity_equation]
              (* Taking x of bs' brings us to EL x σs. Taking x of bs brings us
                 to EL x σs. Then the subsequent element of bs' is equal to the
                 corresponding element of bs, so we have our result. *)
              >> ‘x + 1 ≤ LENGTH bs’ by gvs[mdr_summed_out_values_2_def]
              >> simp[el_encode_recursive_parity_equation]
              >> qpat_x_assum ‘_ = σs’ (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
              >> simp[el_encode_recursive_parity_equation_state_sequence]
             )
          >> irule EXTREAL_PROD_IMAGE_0
          >> simp[]
          (* The node which returns 0 will be the one for which cs_p is not
             equal to the encoding of bs. *)
          >> CCONTR_TAC
          >> qpat_x_assum ‘cs_p ≠ _’ mp_tac
          >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
          >> simp[LIST_EQ_REWRITE]
          >> conj_tac >- gvs[mdr_summed_out_values_2_def]
          >> gen_tac >> strip_tac
          >> CCONTR_TAC
          >> qpat_x_assum ‘¬∃x._’ mp_tac
          >> PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES]
          >> qexists ‘INR (5 * n + 2 + x)’
          >> simp[]
          >> sg ‘x < n’
          >- gvs[mdr_summed_out_values_2_def]
          >> conj_tac >- simp[range_def]
          >> DEP_PURE_ONCE_REWRITE_TAC[DRESTRICT_FUN_FMAP]
          >> conj_tac
          >- (simp[]
              >> irule SUBSET_FINITE
              >> qexists ‘IMAGE INR (count (6 * n + 2))’
              >> simp[]
              >> simp[SUBSET_DEF]
             )
           >> qmatch_abbrev_tac ‘_ ' (FUN_FMAP _ s) = 0’
          >> Q.SUBGOAL_THEN
              ‘s = {INR x; INR (n + x); INR (2 * n + x); INR (2 * n + 1 + x)}’
              (fn th => PURE_ONCE_REWRITE_TAC[th]) >> Q.UNABBREV_TAC ‘s’
          >- (simp[EXTENSION]
              >> gen_tac
              >> Cases_on ‘x' = INR x’
              >- (simp[adjacent_rcc_factor_graph] >> simp[range_def])
              >> Cases_on ‘x' = INR (n + x)’
              >- (simp[adjacent_rcc_factor_graph] >> simp[range_def])
              >> Cases_on ‘x' = INR (2 * n + x)’
              >- (simp[adjacent_rcc_factor_graph] >> simp[range_def])
              >> Cases_on ‘x' = INR (2 * n + (x + 1))’
              >- (simp[adjacent_rcc_factor_graph] >> simp[range_def])
              >> simp[]
              >> CCONTR_TAC >> gvs[]
              >> gvs[adjacent_rcc_factor_graph]
             )
          >> simp[get_function_map_rcc_factor_graph]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- simp[range_def]
          >> simp[]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- (simp[]
              >> simp[var_assignments_def]
              >> conj_tac
              >- simp[func_node_state_adjacent_nodes_def]
              >> gen_tac
              >> simp[FUN_FMAP_DEF]
              >> simp[range_def]
              >> strip_tac >> simp[]
              >> simp[FUN_FMAP_DEF] (*HERE *)
              >> DEP_PURE_ONCE_REWRITE_TAC[el_encode_recursive_parity_equation_state_sequence]
              >> conj_tac >- gvs[mdr_summed_out_values_2_def]
              >> simp[]
              >> gvs[mdr_summed_out_values_2_def]
             )
          >> simp[func_node_state_fn_def]
          >> simp[cj 2 FUN_FMAP_DEF]
          >> simp[range_def]
          >> sg ‘x + 1 ≤ LENGTH bs’
          >- gvs[mdr_summed_out_values_2_def]
          >> simp[el_encode_recursive_parity_equation_state_sequence]
          >> simp[encode_recursive_parity_equation_take_el_sing]
         )
      (* The above cases combine to tell us that the input, state, and parity
         bits are valid *)
      >> sg ‘input_state_parity_valid (ps,qs) ts (bs,σs,cs_p)’
      >- simp[input_state_parity_valid_def]
      >> simp[]
      >> conj_tac
      (* Equivalence of expressions for non-initial state components *)
      >- (unabbrev_all_tac
          >> simp[EXTREAL_PROD_IMAGE_MUL]
          >> irule EXTREAL_PROD_IMAGE_CONG_DIFF_SETS
          >> simp[]
          >> qexists ‘λx. INR (x + 5 * n + 2)’
          >> conj_tac
          >- (simp[BIJ_THM]
              >> simp[range_def]
              >> gen_tac >> strip_tac
              >> Cases_on ‘y’ >> gvs[]
              >> simp[EXISTS_UNIQUE_DEF]
              >> qexists ‘x - 5 * n - 2’
              >> simp[]
             )
          >> gen_tac
          >> strip_tac
          >> DEP_PURE_ONCE_REWRITE_TAC[DRESTRICT_FUN_FMAP]
          >> conj_tac
          >- (simp[]
              >> irule SUBSET_FINITE
              >> qexists ‘IMAGE INR (count (6 * n + 2))’
              >> simp[SUBSET_DEF]
             )
          >> simp[]
          >> qmatch_abbrev_tac ‘_ = _ ' (FUN_FMAP _ cur_adj_nodes)’
          >> Q.SUBGOAL_THEN ‘cur_adj_nodes = {INR x; INR (n + x);
                             INR (2 * n + x); INR (2 * n + 1 + x)}’
              (fn th => PURE_ONCE_REWRITE_TAC[th])
          >- (Q.UNABBREV_TAC ‘cur_adj_nodes’
              >> simp[EXTENSION]
              >> gen_tac
              >> simp[range_def]
              >> Cases_on ‘x' = INR x’
              >- simp[adjacent_rcc_factor_graph]
              >> Cases_on ‘x' = INR (n + x)’
              >- simp[adjacent_rcc_factor_graph]
              >> Cases_on ‘x' = INR (2 * n + x)’
              >- simp[adjacent_rcc_factor_graph]
              >> Cases_on ‘x' = INR (2 * n + 1 + x)’
              >- simp[adjacent_rcc_factor_graph]
              >> gvs[]
              >> CCONTR_TAC
              >> gvs[]
              >> gvs[adjacent_rcc_factor_graph]
             )
          >> qpat_x_assum ‘Abbrev (cur_adj_nodes = _)’ kall_tac
          (* *)
          >> simp[get_function_map_rcc_factor_graph]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- simp[range_def]
          >> simp[]
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- (simp[]
              >> simp[var_assignments_def]
              >> conj_tac
              >- simp[func_node_state_adjacent_nodes_def]
              >> gen_tac >> strip_tac
              >> simp[cj 2 FUN_FMAP_DEF]
              >> simp[range_def]
              >> gvs[mdr_summed_out_values_2_def]
              >> first_x_assum irule
              >> simp[EL_MEM]
             )
          >> qpat_x_assum ‘cs_p = _’ (fn th => assume_tac (GSYM th))
          >> simp[]
          (* *)
          >> simp[func_node_state_fn_def]
          >> simp[cj 2 FUN_FMAP_DEF]
          >> simp[range_def]
          (* We already know that our bs, σs, and cs_p are valid, so this
             precondition holds *)
          >> qmatch_abbrev_tac ‘_ = if cond then 1 else 0’
          >> sg ‘cond’ >> Q.UNABBREV_TAC ‘cond’
          >- (sg ‘x + 1 ≤ LENGTH bs’ >- gvs[mdr_summed_out_values_2_def]
              >> conj_tac
              >- (simp[el_encode_recursive_parity_equation_state_sequence]
                  >> simp[encode_recursive_parity_equation_state_encode_recursive_parity_equation_state]
                  >> simp[TAKE_EL_SNOC])
              >> simp[el_encode_recursive_parity_equation_state_sequence]
              >> simp[encode_recursive_parity_equation_take_el_sing]
             )
          >> simp[]
          >> qmatch_abbrev_tac ‘p1 * p2 = 1’
          >> ‘p1 = 1 ∧ p2 = 1’ suffices_by simp[]
          >> Q.UNABBREV_TAC ‘p1’ >> Q.UNABBREV_TAC ‘p2’
          >> DEP_PURE_REWRITE_TAC[cond_prob_one]
          >> conj_tac
          >- (simp[EVENTS_INTER]
              >> simp[EXTENSION]
              >> qexists ‘(bs, REPLICATE (2 * n) F)’
              >> simp[event_state_takes_value_def,
                      event_input_bit_takes_value_def]
              >> gvs[mdr_summed_out_values_2_def]
              >> simp[el_encode_recursive_parity_equation_state_sequence])
          >> conj_tac             
          >- (simp[SUBSET_DEF]
              >> gen_tac
              >> simp[event_state_takes_value_def,
                      event_input_bit_takes_value_def]
              >> namedCases_on ‘x'’ ["bs_new ns_new"]
              >> simp[]
              >> ‘x + 1 ≤ LENGTH bs’ by gvs[mdr_summed_out_values_2_def]
              >> simp[el_encode_recursive_parity_equation_state_sequence]
              >> strip_tac
              >> simp[TAKE_EL_SNOC]
              >> simp[encode_recursive_parity_equation_state_snoc]
             )
          >> simp[SUBSET_DEF]
          >> gen_tac
          >> simp[event_state_takes_value_def,
                  event_input_bit_takes_value_def,
                  event_srcc_parity_bit_takes_value_def]
          >> namedCases_on ‘x'’ ["bs_new ns_new"]
          >> simp[]
          >> ‘x + 1 ≤ LENGTH bs’ by gvs[mdr_summed_out_values_2_def]
          >> simp[el_encode_recursive_parity_equation_state_sequence]
          >> strip_tac
          >> gvs[]
          >> simp[el_encode_recursive_parity_equation]
         )
      (* Equivalence of expressions for encoded component.
         Working based on that used for equivalence of expressions for
         systematic component. *)
      >> unabbrev_all_tac
      >> irule EXTREAL_PROD_IMAGE_CONG_DIFF_SETS
      >> simp[]
      >> qexists ‘λx. INR (4 * n + 1 + x)’
      >> conj_tac
      >- (simp[BIJ_THM]
          >> conj_tac >> simp[range_def]
          >> gen_tac >> strip_tac
          >> simp[EXISTS_UNIQUE_THM]
          >> qexists ‘x - 1 - 4 * n’
          >> simp[]
         )
      >> gen_tac >> strip_tac
      >> simp[]
      >> DEP_PURE_ONCE_REWRITE_TAC[DRESTRICT_FUN_FMAP]
      >> conj_tac
      >- (simp[]
          >> irule SUBSET_FINITE
          >> qexists ‘IMAGE INR (count (6 * n + 2))’
          >> simp[SUBSET_DEF])
      >> qmatch_abbrev_tac ‘_ = _ ' (FUN_FMAP _ cur_adj_nodes)’
      >> Q.SUBGOAL_THEN ‘cur_adj_nodes = {INR (n + x)}’
          (fn th => PURE_ONCE_REWRITE_TAC[th])
      >- (Q.UNABBREV_TAC ‘cur_adj_nodes’
          >> simp[EXTENSION]
          >> gen_tac
          >> Cases_on ‘x'’ >> simp[range_def]
          >> Cases_on ‘y = n + x’ >> gvs[]
          >- simp[adjacent_rcc_factor_graph]
          >> CCONTR_TAC >> gvs[]
          >> gvs[adjacent_rcc_factor_graph]
         )
      >> qpat_x_assum ‘Abbrev (cur_adj_nodes = _)’ kall_tac
      >> simp[get_function_map_rcc_factor_graph]
      >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
      >> conj_tac
      >- simp[range_def]
      >> simp[]
      >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
      >> conj_tac
      >- (simp[var_assignments_def]
          >> simp[cj 2 FUN_FMAP_DEF]
          >> rw[]
          >> gvs[range_def])
      >> simp[cj 2 FUN_FMAP_DEF]
      >> simp[range_def]
      >> DEP_PURE_ONCE_REWRITE_TAC[cond_prob_event_received_bit_takes_value_event_sent_bit_takes_value]
      >> conj_tac
      >- (simp[]
          >> qexists ‘bs’
          >> simp[]
          >> gvs[mdr_summed_out_values_2_def])
      >> simp[EL_TAKE]
      >> simp[EL_DROP]
      >> simp[sym_noise_mass_func_def]
      >> gvs[mdr_summed_out_values_2_def]
      >> simp[IFF_SYM]
     )
  >> simp[BIJ_IFF_INV]
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> namedCases_on ‘x’ ["bs σs cs_p"]
      >> simp[]
      >> simp[val_map_assignments_def]
      >> rpt conj_tac
      >- (simp[range_def, EXTENSION]
          >> gen_tac >> EQ_TAC >> strip_tac >> simp[])
      >- (gen_tac >> strip_tac
          >> simp[cj 2 FUN_FMAP_DEF]
          >> rw[]
          >> (simp[get_variable_length_map_rcc_factor_graph]
              >> gvs[range_def]
              >> simp[cj 2 FUN_FMAP_DEF])
          >> gvs[mdr_summed_out_values_2_def]
          >> first_x_assum irule
          >> simp[]
          >> irule EL_MEM
          >> simp[]
         )
      >> strip_tac
      >> simp[cj 2 FUN_FMAP_DEF]
      >> rw[] >> gvs[range_def, mdr_summed_out_values_2_def]
     )
  >> qexists ‘λval_map.
                (MAP (λi. HD (val_map ' (INR i))) (COUNT_LIST n),
                 MAP (λi. val_map ' (INR (i + 2 * n))) (COUNT_LIST (n + 1)),
                 MAP (λi. HD (val_map ' (INR (i + n)))) (COUNT_LIST n))
             ’
  >> conj_tac
  >- (qx_gen_tac ‘val_map’
      >> strip_tac
      >> simp[mdr_summed_out_values_2_def]
      >> rpt conj_tac
      >- simp[LENGTH_COUNT_LIST]
      >- (simp[EL_MAP, LENGTH_COUNT_LIST]
          >> simp[EL_COUNT_LIST]
          >> gvs[val_map_assignments_def]
          >> simp[cj 2 FUN_FMAP_DEF])
      >- simp[LENGTH_COUNT_LIST]
      >- (gen_tac >> strip_tac
          >> gvs[val_map_assignments_def, get_variable_length_map_rcc_factor_graph]
          >> gvs[MAP_COUNT_LIST, MEM_GENLIST]
          >> first_x_assum $ qspec_then ‘INR (i' + 2 * n)’ assume_tac
          >> gvs[]
          >> simp[cj 2 FUN_FMAP_DEF]
         )
      >> simp[LENGTH_COUNT_LIST]
     )
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> namedCases_on ‘x’ ["bs σs cs_p"]
      >> gvs[mdr_summed_out_values_2_def]
      (* We don't need this, and repeatedly attempting to rewrite anything of
         the form LENGTH σ causes slowdown *)
      >> qpat_x_assum ‘∀σ. MEM σ σs ⇒ LENGTH σ = LENGTH ts’ kall_tac
      >> rpt conj_tac
      >- (simp[MAP_COUNT_LIST]
          >> gen_tac >> strip_tac
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- simp[range_def]
          >> rw[] >> gvs[range_def])
      >- (qpat_x_assum ‘LENGTH σs = LENGTH bs + 1’
                       (fn th => assume_tac (GSYM th))
          >> simp[MAP_COUNT_LIST]
          >> gen_tac >> strip_tac
          >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
          >> conj_tac
          >- simp[range_def]
          >> rw[]
          >- gvs[range_def]
          >> gvs[range_def]
         )
      >> qpat_x_assum ‘LENGTH cs_p = LENGTH bs’ (fn th => assume_tac (GSYM th))
      >> simp[MAP_COUNT_LIST]
      >> gen_tac >> strip_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
      >> conj_tac
      >- simp[range_def]
      >- (simp[]
          >> rw[] >> gvs[range_def])
     )
  >> qx_gen_tac ‘val_map’
  >> strip_tac
  >> simp[]
  >> PURE_ONCE_REWRITE_TAC[GSYM fmap_EQ_THM]
  >> conj_tac
  >- (simp[]
      >> drule in_val_map_assignments_fdom_inter
      >> simp[] >> strip_tac
      >> simp[range_def, count_def, EXTENSION]
      >> gen_tac >> EQ_TAC >> strip_tac >> simp[]
     )
  >> gen_tac
  >> simp[]
  >> Cases_on ‘x’ >> simp[range_def]
  >> strip_tac
  >> DEP_PURE_ONCE_REWRITE_TAC[cj 2 FUN_FMAP_DEF]
  >> conj_tac
  >- simp[GSYM count_def]
  >> rw[]
  >> (simp[MAP_COUNT_LIST]
      >> gvs[val_map_assignments_def]
      >> simp[get_variable_length_map_rcc_factor_graph]
      >> simp[cj 2 FUN_FMAP_DEF]
     )
QED

(* -------------------------------------------------------------------------- *)
(* Computing the factor graph can give us a                                   *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
