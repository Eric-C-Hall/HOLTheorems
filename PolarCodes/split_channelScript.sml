Theory split_channel

Ancestors arithmetic bitstring bxor_lemmas combine_channel interleave memoryless_channel

Libs dep_rewrite realLib;

val _ = hide "W";

(* -------------------------------------------------------------------------- *)
(* Based on "Channel polarization: A method for constructing                  *)
(* capacity-achieving codes for symmetric binary-input memoryless channels    *)
(* by Erdal Arıkan                                                            *)
(*                                                                            *)
(* Based on "Polar Codes: from theory to practice" by Mohammad Rowshan and    *)
(* Emanuele Viterbo                                                           *)
(* -------------------------------------------------------------------------- *)

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
(* We assume that the input channel's domain is finite, so that we may use    *)
(* the power set of the domain as the sigma algebra.                          *)
(*                                                                            *)
(* We assume that the output's sigma algebra includes any singleton set       *)
(* containing an output, so that we may determine the probability of any      *)
(* individual output.                                                         *)
(*                                                                            *)
(* Inputs:                                                                    *)
(* - W: the underlying channel                                                *)
(* - num_inputs: the combined channel size N                                  *)
(* - i: the index of the current split channel                                *)
(* -------------------------------------------------------------------------- *)
Definition split_channel0_def:
  split_channel0 (W : (bool, β) memoryless_channel)
  (num_inputs : num) (i : num) =
  let
    (output_sample_space, output_sigma_algebra) =
    (sigma_list (REPLICATE num_inputs (mcoutput_space W, mcoutput_sigma_algebra W))
                × sigma_list (REPLICATE i (mcdomain W, POW (mcdomain W)))
    ) : (β list # bool list) algebra
  in
    (𝕌(:bool),
     λcurrent_chosen_value.
       (output_sample_space,
        output_sigma_algebra,
        EXTREAL_SUM_IMAGE
        (λ(output, prior_chosen_values).
           EXTREAL_SUM_IMAGE
           (λlater_chosen_values.
              (1 / 2 pow (num_inputs - 1)) *
              (prob (mcchannel (combine_channel W num_inputs)
                               (prior_chosen_values ++ [current_chosen_value] ++
                                later_chosen_values))
                    {output}
              )
           ) (cross_list (REPLICATE (num_inputs - i - 1) (mcdomain W)))
        ) : (β list # bool list) measure
       ) : (β list # bool list) m_space
    ) : (bool -> bool) # (bool -> (β list # bool list) m_space)
End


Theorem mcdomain0_split_channel0[simp]:
  ∀W : (bool,β) memoryless_channel n i.
    mcdomain0 (split_channel0 W n i) = {T;F}
Proof
  rpt gen_tac
  >> gvs[split_channel0_def, mcdomain0_def]
  >> qmatch_abbrev_tac ‘FST (_ argument) = _’
  >> Cases_on ‘argument’
  >> simp[]
QED

Theorem wf_memoryless_channel_split_channel0:
  ∀W n i.
    wf_memoryless_channel (split_channel0 W n i)
Proof
  rpt gen_tac
  >> simp[wf_memoryless_channel_def]
  >> conj_tac
  (* Every output space is a probability space *)
  >- (gen_tac
      >> gvs[mcdomain0_def, split_channel0_def]
     )
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



Theorem mcoutput_space_split_channel:
  ∀.
    mcoutput_space (split_channel W n i) =
    cross_list (REPLICATE num_inputs (mcoutput_space W))
               × (cross_list (REPLICATE i (mcdomain W)))
Proof
QED
