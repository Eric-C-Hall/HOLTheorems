Theory split_channel

Ancestors arithmetic bitstring bxor_lemmas combine_channel interleave memoryless_channel

Libs dep_rewrite realLib;

(* -------------------------------------------------------------------------- *)
(* Based on "Channel polarization: A method for constructing                  *)
(* capacity-achieving codes for symmetric binary-input memoryless channels    *)
(* by Erdal Arıkan                                                            *)
(*                                                                            *)
(* Based on "Polar Codes: from theory to practice" by Mohammad Rowshan and    *)
(* Emanuele Viterbo                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* TODO: find this definition somewhere                                       *)
(* Probably apply general_cross from martingaleTheory?                        *)
(*                                                                            *)
(* See {xs | LENGTH xs = n ∧ EVERY (combin$C (IN) (mcdomain0 W)) xs}. This    *)
(* how it's defined in repeatChannel. If this is different, probably also     *)
(* change it there.                                                           *)
(* -------------------------------------------------------------------------- *)
Definition TODO_prod_set_def:
  TODO_prod_set (set : α -> bool) (num_prod : num) = ARB : α list -> bool
End

(* -------------------------------------------------------------------------- *)
(* The split channel step in Polar Coding                                     *)
(*                                                                            *)
(* Not produced through straightforward operations on simpler channels so we  *)
(* need to define it using the underlying representation type.                *)
(*                                                                            *)
(* Initial channel input: bool                                                *)
(* Initial channel output: β                                                  *)
(*                                                                            *)
(* Split channel input: bool                                                  *)
(* Split channel output: β list # bool list                                   *)
(*                                                                            *)
(* Channel is a (domain, transition function) pair.                           *)
(*                                                                            *)
(* Split channel domain:                                                      *)
(* TODO: are these comments necessary? Improve htem?                          *)
(*                                                                            *)
(* Inputs:                                                                    *)
(* - W: the underlying channel                                                *)
(* - num_inputs: the combined channel size N                                  *)
(* - i: the index of the current split channel                                *)
(* -------------------------------------------------------------------------- *)
Definition split_channel0_def:
  split_channel0 (W : (bool -> bool) # (bool -> β m_space))
  (num_inputs : num) (i : num) =
  (TODO_prod_set (mcdomain W) i,
   λcurrent_chosen_value.
     (TODO_PROD (TODO_prod_set () ()) (TODO_prod_set () ()),
      (Product sigma algebra on left) (Product sigma algebra on right),
      λ(, later_chosen_values).
        EXTREAL_SUM_IMAGE
        (λprior_chosen_values.
           (1 / 2 ** (num_inputs - 1)) *
           (mcchannel (combine_channel W num_inputs)
                      (prior_chosen_values ++ [current_chosen_value] ++
                       later_chosen_values)
           )
        )
     ) 
      (TODO_prod_set (mcdomain W) (num_inputs - i - 1))
  )
  : (bool list -> bool) # (bool -> ((β list) # (bool list)) m_space)
End

Theorem wf_memoryless_channel_split_channel0:
  ∀W n.
    wf_memoryless_channel W ⇒
    wf_memoryless_channel (split_channel0 W n i)
Proof
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Lifting when we have requirements on n and i?                        *)
(* -------------------------------------------------------------------------- *)

Theorem split_channel0_respects:
  (memoryless_channelequiv ===> (=) ===> (=) ===> (memoryless_channelequiv))
  split_channel0 split_channel0
Proof
  simp[FUN_REL_def]
  >> rpt gen_tac
  >> simp[memoryless_channelequiv_def, wf_memoryless_channel_split_channel0]
QED

val (repeat_channel_def, repeat_channel_relates) = liftdef repeat_channel0_respects "repeat_channel";

