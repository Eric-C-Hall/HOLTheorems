Theory repeat_channel

Ancestors arithmetic bitstring bxor_lemmas interleave jared_yeager_prod_list lifting list measure memoryless_channel pispace pred_set probability rich_list sigma_algebra transfer trivial

Libs dep_rewrite liftLib realLib transferLib;

val _ = hide "W";

(* TODO: move the definitions that help to define prod_list based on
   pi_measure_space into their own file, perhaps *)

(* -------------------------------------------------------------------------- *)
(* Given a memoryless channel, transform it into n parallel instances of that *)
(* channel.                                                                   *)
(* -------------------------------------------------------------------------- *)
Definition repeat_channel0_def:
  repeat_channel0 (W : (α -> bool) # (α -> β m_space)) (n : num) =
  (cross_list (REPLICATE n (mcdomain0 W)),
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
      >> qpat_x_assum ‘∀x y. _ ∧ _ ⇒ m_space _ = m_space _ ∧ _’ kall_tac
      >> 
                      
      >> cheat
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
