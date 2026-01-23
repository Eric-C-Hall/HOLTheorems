(* Written by Eric Hall, under the guidance of Michael Norrish *)

Theory bcjr_factor_graph

Ancestors binary_symmetric_channel combin extreal factor_graph genericGraph map_decoder_convolutional_code marker message_passing list range rich_list pred_set prim_rec probability recursive_parity_equations state_machine wf_state_machine

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
     ({INR i; INR (n + i); INR (2*n + i); INR (2*n + i + 1)})
     (λval_map.
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
     )
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
(*            P(dp_0|cp_0)        P(cp_1|b_1)             P(cp_{n-1}|b_{n-1})  *)
(*                                                                            *)
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


Theorem is_tree_rcc_factor_graph:
  ∀n p ps qs ts prior ds_s ds_p.
    is_tree (get_underlying_graph
             (rcc_factor_graph n p (ps,qs) ts prior (ds_s, ds_p))
            )
Proof
  rpt gen_tac
  >> cheat
QED

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

(* -------------------------------------------------------------------------- *)
(* TODO: double check: is the condition i ≤ n + 1 necessary?                  *)
(* -------------------------------------------------------------------------- *)
Theorem order_rcc_factor_graph_add_func_nodes_state:
  ∀n ps qs ts i fg.
    i ≤ n ∧
    var_nodes fg = IMAGE INR (count (3 * n + 1)) ⇒
    order (get_underlying_graph (rcc_factor_graph_add_func_nodes_state
                                 n (ps, qs) ts i fg))
    = order (get_underlying_graph fg) + n - i
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
  >> simp[]
QED

Theorem get_function_nodes_rcc_factor_graph_add_func_nodes_state:

Proof
QED

Theorem order_rcc_factor_graph[simp]:
  ∀n p ps qs ts prior ds_s ds_p.
    order (get_underlying_graph
           (rcc_factor_graph n p (ps, qs) ts prior (ds_s, ds_p))) =
    ARB
Proof
  simp[rcc_factor_graph_def]
  >>
QED


Theorem nodes_rcc_factor_graph[simp]:
  ∀n p ps qs ts prior ds_s ds_p.
    nodes (get_underlying_graph
           (rcc_factor_graph n p (ps, qs) ts prior (ds_s, ds_p))) =
    ARB
Proof
  rpt gen_tac
  >> simp[nodes_get_underlying_graph]
QED

Theorem get_function_nodes_rcc_factor_graph[simp]:
  ∀n p ps qs ts prior ds_s ds_p.
    get_function_nodes (rcc_factor_graph n p (ps, qs) ts prior (ds_s, ds_p)) =
    ARB
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[GSYM nodes_diff_var_nodes]
  >> simp[nodes_get_underlying_graph]
  >> PURE_ONCE_REWRITE_TAC[rcc_factor_graph_def]
  >> simp[o_DEF]
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
      >- (cheat
         )
      >- simp[is_tree_rcc_factor_graph]
      >> PURE_ONCE_REWRITE_TAC[var_nodes_rcc_factor_graph]
     )
QED

(* -------------------------------------------------------------------------- *)
(* Computing the factor graph can give us a                                   *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
