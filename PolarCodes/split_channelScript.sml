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
(* Split channel domain: {T;F}                                                *)
(* Split channel transition function:                                         *)
(* - Takes the current input bit                                              *)
(* - Returns a probability distribution over the outputs and the prior inputs *)
(* - Averages over the future inputs.                                         *)
(*                                                                            *)
(* The probability distribution has                                           *)
(* - event space equal to product of event spaces of the noisy channel with   *)
(*   the event space of the future inputs                                     *)
(* - sigma algebra equal to the product of the sigma algebra of the noisy     *)
(*   channel with the sigma algebra of the future inputs                      *)
(* -                                                                          *)
(*                                                                            *)
(* Inputs:                                                                    *)
(* - W: the underlying channel                                                *)
(* - num_inputs: the combined channel size N                                  *)
(* - i: the index of the current split channel                                *)
(* -------------------------------------------------------------------------- *)
(* THE FOLLOWING IS UNTRUE AS THE DISTRIBUTION SHOULD ALSO CONTAIN ADDITIONAL *)
(* PROBABILITIES UNIFORMLY DISTRIBUTED OVER THE FUTURE INPUTS                 *)
(* The split channel probability distribution may be represented as the       *)
(* distribution of a random variable. The random variable takes the event of  *)
(* the combined channel (which should represent the noise added by the        *)
(* channel, and combining this with the input which we already know when      *)
(* constructing the distribution, the output of our random variable is the    *)
(* output                                                                     *)
(* -------------------------------------------------------------------------- *)
Definition split_channel0_def:
  split_channel0 (W : (bool -> bool) # (bool -> β m_space))
  (num_inputs : num) (i : num) =
  let
    combined_channel = combine_channel W num_inputs
  in
    (𝕌(:bool),
     λcurrent_chosen_value.
       ((TODO_prod_set () ()) × (TODO_prod_set () ()),
        (TODO_prod_sigma_algebra ) × (TODO_prod_sigma_algebra),
        λ(noise, later_chosen_values).
          EXTREAL_SUM_IMAGE
          (λprior_chosen_values.
             (1 / 2 ** (num_inputs - 1)) *
             (mcchannel (combine_channel W num_inputs)
                        (prior_chosen_values ++ [current_chosen_value] ++
                         later_chosen_values)
             )
          ) (TODO_prod_set (mcdomain W) (num_inputs - i - 1))
       ) 
    )
    : (bool -> bool) # (bool -> ((β list) # (bool list)) m_space)
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

