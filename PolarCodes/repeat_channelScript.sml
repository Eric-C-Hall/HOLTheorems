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
  (* Step 1: Prove that each input is mapped to a probability distribution *)
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
  (* Step 2: Prove that each probability distribution has the same sample space
     and sigma algebra *)
  >> rpt gen_tac >> strip_tac
  (* We don't need to know that our inductive part is a probability space: we've
     already proven that we have a probability space, now we are proving the
     second part *)
  >> qpat_x_assum ‘∀x. _ ⇒ prob_space _’ kall_tac
  (* Expand basic relevant definitions, to simplify *)
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
  (* If n is zero, contradiction. So break down n. *)
  >> Cases_on ‘n’
  >- gvs[]
  (* Instantiate the inductive hypothesis with the appropriate values *)
  >> qpat_x_assum ‘∀n y. _ ⇒ _ ⇒ _ ⇒ _ ∧ _’
                  (qspecl_then [‘n'’, ‘t’] assume_tac)
  (* Simplify *)
  >> gvs[]
  (* Prove preconditions of inductive hypothesis *)
  >> sg ‘x ∈ cross_list (REPLICATE n' channel_dom) ∧
         t ∈ cross_list (REPLICATE n' channel_dom)’
  >- (pop_assum kall_tac >> pop_assum kall_tac
      >> NTAC 2 (dxrule cons_in_cross_list)
      >> rpt (pop_assum kall_tac)
      >> simp[])
  (* Simplify preconditions of inductive hypothesis *)
  >> gvs[]
  (* Apply the fact that the individual channels are well-formed to the head,
     so as to prove a single step of our induction *)
  >> qpat_x_assum ‘∀x y. _ ⇒ m_space _ = m_space _ ∧ _’
                  $ qspecl_then [‘h’, ‘h'’] assume_tac
  (* Prove necessary prerequisites of this fact*)
  >> sg ‘h ∈ channel_dom ∧ h' ∈ channel_dom’
  >- (NTAC 2 (dxrule cons_in_cross_list)
      >> rpt (pop_assum kall_tac) >> simp[])
  (* Simplify prerequisites *)
  >> gvs[]
  (* Now we know that the inductive space and measurable sets are equal, and
     the individual head space and measurable sets are equal. We just need to
     use this to prove that cons-ing these together is equal.
.
     First prove the spaces are equivalent, then that the measurable sets are
     equivalent.
   *)
  >> conj_tac
  >- gvs[m_space_prod_list, cross_list_eq]
  >> 
  
QED

Theorem repeat_channel0_respects:
  (memoryless_channelequiv ===> (=) ===> (memoryless_channelequiv)) repeat_channel0 repeat_channel0
Proof
  simp[FUN_REL_def]
  >> rpt gen_tac
  >> simp[memoryless_channelequiv_def, wf_memoryless_channel_repeat_channel0]
QED

val (repeat_channel_def, repeat_channel_relates) = liftdef repeat_channel0_respects "repeat_channel";
