Theory repeat_channel

Ancestors arithmetic bitstring bxor_lemmas combin interleave jared_yeager_prod_list lifting list martingale measure memoryless_channel pispace pred_set probability rich_list sigma_algebra transfer trivial

Libs ConseqConv dep_rewrite liftLib realLib transferLib;

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

Theorem mcdomain0_repeat_channel0:
  ∀W n.
    mcdomain0 (repeat_channel0 W n) = cross_list (REPLICATE n (mcdomain0 W))
Proof
  simp[mcdomain0_def, repeat_channel0_def]
QED

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
      >> drule_all in_cross_list_mem >> strip_tac
      >> gvs[]
      >> ‘LENGTH x = n’ by (drule length_in_cross_list >> simp[])
      >> gvs[]
      >> gvs[EL_REPLICATE]
     )
  (* Each probability distribution has the same sample space and sigma algebra *)
  >> rpt gen_tac >> strip_tac
  >> gvs[mcdomain0_def, mcchannel0_def, repeat_channel0_def]
  (* Prove that x and y have the same length, to help us when inducting on x,
     so we can simultaneously break down y. *)
  >> sg ‘LENGTH x = LENGTH y’
  >- (NTAC 2 (dxrule length_in_cross_list)
      >> simp[])
  (* Induct on x *)
  >> NTAC 3 (pop_assum mp_tac)
  >> SPEC_ALL_TAC
  >> Induct_on ‘x’
  >- (Cases_on ‘y’ >> simp[])
  >> rpt gen_tac
  >> Cases_on ‘y’
  >- simp[]
  >> simp[]
  >> NTAC 3 disch_tac
  (* Move the cons out, so that we can prove our result separately for the
     head and tail. *)
  >> simp[m_space_prod_list]
  >> conj_tac
  (* Prove the spaces are equivalent; after this, we will prove that the
     measurable sets are equivalent. *)

  >- (simp[cross_list_eq]
      (* The spaces are individually the same, we don't need to rely on any
         spaces being empty *)
      >> disj1_tac
      >> conj_tac
      (* First, prove it for the head *)
         
      >- (qpat_x_assum ‘∀x y. _ ⇒ m_space _ = m_space _ ∧ _’
                       $ qspecl_then [‘h’, ‘h'’] (fn th => irule (cj 1 th))
          >> Cases_on ‘n’
          >- gvs[]
          >> gvs[]
         )
      (* Now prove it for the tail*)
      >> simp[MAP_MAP_o]
             
                   
      >> gen_tac
     )
  >> disj1_tac
  >> qspecl_then [‘m_space ∘ channel_func’, ‘m_space ∘ channel_func’] assume_tac MAP_EQ_f
  >> irule (iffRL MAP_EQ_f)
  >> conj_tac
  >> 
  >> 
     )
     
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
