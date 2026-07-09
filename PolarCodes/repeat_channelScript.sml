Theory repeat_channel

Ancestors arithmetic bitstring bxor_lemmas interleave jared_yeager_pi_measure_space_list lifting measure memoryless_channel pispace polar_encode pred_set probability sigma_algebra transfer trivial

Libs dep_rewrite realLib liftLib transferLib;

val _ = hide "W";

(* TODO: move the definitions that help to define pi_measure_space_list based on
   pi_measure_space into their own file, perhaps *)

(* -------------------------------------------------------------------------- *)
(* Given a memoryless channel, transform it into n parallel instances of that *)
(* channel.                                                                   *)
(* -------------------------------------------------------------------------- *)
Definition repeat_channel0_def:
  repeat_channel0 (W : (α -> bool) # (α -> β m_space)) (n : num) =
  ({xs | LENGTH xs = n},
   λrepeated_inputs.
     pi_measure_space_list (MAP (mcchannel0 W) repeated_inputs)
  )
  : (α list -> bool) # (α list -> β list m_space)
End

Theorem wf_memoryless_channel_repeat_channel0:
  ∀W n.
    wf_memoryless_channel W ⇒
    wf_memoryless_channel (repeat_channel0 W n)
Proof
  rpt gen_tac
  >> namedCases_on ‘W’ ["channel_dom channel_func"]
  >> simp[wf_memoryless_channel_def, mcdomain0_def, mcchannel0_def]
  >> strip_tac >> gen_tac
  >> simp[repeat_channel0_def, mcchannel0_def]
  >> strip_tac
  >> irule sigma_finite_measure_space_pi_measure_space_list
  >> 
  
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

(* -------------------------------------------------------------------------- *)
(* Given a memoryless channel                                                 *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Definition repeat_channel_def:
  repeat_channel (W : (α, β) memoryless_channel) [] = [] ∧
  repeat_channel (W : (α, β) memoryless_channel) (x::xs : α list)
  = () × repeat_channel W xs
End
