Theory repeat_channel

Ancestors arithmetic bitstring bxor_lemmas interleave jared_yeager_prod_list lifting list measure memoryless_channel pispace pred_set probability rich_list sigma_algebra transfer trivial

Libs dep_rewrite liftLib realLib transferLib;

val _ = hide "W";

(* TODO: move the definitions that help to define prod_list based on
   pi_measure_space into their own file, perhaps *)

(* -------------------------------------------------------------------------- *)
(* TODO: find this definition somewhere                                       *)
(* Probably apply general_cross from martingaleTheory?                        *)
(*                                                                            *)
(* TODO: redefine this as                                                     *)
(*                                                                            *)
(*                                                                            *)
(* See {xs | LENGTH xs = n ∧ EVERY (combin$C (IN) (mcdomain0 W)) xs}. This    *)
(* how it's defined in repeatChannel. If this is different, probably also     *)
(* change it there.                                                           *)
(*                                                                            *)
(* TODO: ensure that there must be exactly num_prod elements in each list in  *)
(* the output, no more, and no less.                                          *)
(* -------------------------------------------------------------------------- *)
Definition TODO_prod_set_def:
  TODO_prod_set (set : α -> bool) (num_prod : num) =
  {xs | LENGTH xs = num_prod ∧
        EVERY (combin$C (IN) set) xs} : α list -> bool
End

(*
Theorem TODO_prod_set_alt:
  ∀set num_prod.
    TODO_prod_set set num_prod =  xs | LENGTH xs = n ∧ EVERY (combin$C (IN) (mcdomain0 W)) xs}
Proof
QED
*)

(* -------------------------------------------------------------------------- *)
(* TODO: the reason we need these definitions, and can't just use the         *)
(* standard probability space product, is because the probability measure is  *)
(* defined with a specific measure, but we need to use a different measure.   *)
(* Could we avoid this by defining the split channel using a random variable  *)
(* on the combined channel?                                                   *)
(*                                                                            *)
(* TODO: I'm not fully sure how the product sigma algebra should be defined.  *)
(* -------------------------------------------------------------------------- *)
Definition TODO_prod_sigma_algebra_def:
  TODO_prod_sigma_algebra (A : α -> bool -> bool) (num_prod : num) =
  ARB : α list -> bool -> bool
End

(* -------------------------------------------------------------------------- *)
(* Given a memoryless channel, transform it into n parallel instances of that *)
(* channel.                                                                   *)
(* -------------------------------------------------------------------------- *)
Definition repeat_channel0_def:
  repeat_channel0 (W : (α -> bool) # (α -> β m_space)) (n : num) =
  (TODO_prod_set (mcdomain0 W) n,
   λrepeated_inputs.
     prod_list (MAP (mcchannel0 W) repeated_inputs)
  )
  : (α list -> bool) # (α list -> β list m_space)
End

Theorem wf_memoryless_channel_repeat_channel0:
  ∀W n.
    wf_memoryless_channel W ⇒
    wf_memoryless_channel (repeat_channel0 W n)
Proof
  rpt gen_tac >> strip_tac
  >> namedCases_on ‘W’ ["channel_dom channel_func"]
  >> gvs[wf_memoryless_channel_def]
  >> conj_tac
  (* Each input is mapped to a probability distribution *)
  >- (gen_tac
      >> gvs[repeat_channel0_def, mcchannel0_def, mcdomain0_def]
      >> strip_tac
      >> irule prob_space_prod_list
      >> simp[ALL_EL_MAP]
      >> simp[EVERY_MEM]
      >> gen_tac >> strip_tac
      >> last_x_assum (fn th => irule (cj 1 th))
      >> gvs[TODO_prod_set_def]
      >> gvs[EVERY_MEM]
      >> last_x_assum dxrule
      >> simp[mcdomain0_def]
     )
  (* Each probability distribution has the same sample space and sigma algebra *)
  >> rpt gen_tac >> strip_tac
  >> simp[repeat_channel0_def, mcchannel0_def]
  >> cheat
QED

Theorem repeat_channel0_respects:
  (memoryless_channelequiv ===> (=) ===> (memoryless_channelequiv)) repeat_channel0 repeat_channel0
Proof
  simp[FUN_REL_def]
  >> rpt gen_tac
  >> simp[memoryless_channelequiv_def, wf_memoryless_channel_repeat_channel0]
QED

val (repeat_channel_def, repeat_channel_relates) = liftdef repeat_channel0_respects "repeat_channel";
