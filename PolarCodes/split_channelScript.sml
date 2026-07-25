Theory split_channel

Ancestors arithmetic bitstring bxor_lemmas combine_channel interleave measure memoryless_channel probability transfer

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
  >> simp[split_channel0_def, mcdomain0_def]
  >> qmatch_abbrev_tac ‘FST (_ argument) = _’
  >> Cases_on ‘argument’
  >> simp[]
QED

Theorem mcchannel0_split_channel0:
  ∀W n i.
    mcchannel0 (split_channel0 W n i) =
    let
      (output_sample_space, output_sigma_algebra) =
      sigma_list (REPLICATE n (mcoutput_space W,mcoutput_sigma_algebra W)) ×
                 sigma_list (REPLICATE i (mcdomain W,POW (mcdomain W)))
    in
      λcurrent_chosen_value.
        (output_sample_space,
         output_sigma_algebra,
         ∑ (λ(output,prior_chosen_values).
              ∑ (λlater_chosen_values.
                   1 / 2 pow (n − 1)
                   * prob (mcchannel (combine_channel W n)
                                     (prior_chosen_values
                                      ⧺ [current_chosen_value]
                                      ⧺ later_chosen_values)
                          ) {output}
                ) (cross_list (REPLICATE (n − (i + 1)) (mcdomain W)))
           )
        )
Proof
  rpt gen_tac
  >> simp[split_channel0_def, mcchannel0_def]
  >> qmatch_abbrev_tac ‘SND (_ argument) = _’
  >> Cases_on ‘argument’
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* TODO: do I really need to know that the split channel is a memoryless      *)
(* channel in the sense that its outputs are probability spaces and its       *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem wf_memoryless_channel_split_channel0:
  ∀W n i.
    i < n ⇒
    wf_memoryless_channel (split_channel0 W n i)
Proof
  rpt gen_tac >> strip_tac
  >> simp[wf_memoryless_channel_def]
  >> conj_tac
  (* Every output space is a probability space *)
  >- (gen_tac
      >> simp[mcchannel0_split_channel0]
      >> simp[prob_space_def]
      >> conj_tac
      >- (cheat
         )
      >> cheat
     )
  >> rpt gen_tac
  >> cheat
QED

(* -------------------------------------------------------------------------- *)
(* TODO: Lifting when we have requirements on n and i?                        *)
(* -------------------------------------------------------------------------- *)

(*Theorem split_channel0_respects:
  ((=) ===> (=) ===> (=) ===> (memoryless_channelequiv))
    split_channel0 split_channel0
Proof
  simp[FUN_REL_def]
  >> rpt gen_tac
  >> simp[memoryless_channelequiv_def, wf_memoryless_channel_split_channel0]
QED

val (split_channel_def, split_channel_relates) = liftdef split_channel0_respects "split_channel";*)

(*Theorem mcoutput_space_split_channel:
  ∀.
    mcoutput_space (split_channel W n i) =
    cross_list (REPLICATE num_inputs (mcoutput_space W))
               × (cross_list (REPLICATE i (mcdomain W)))
Proof
QED
 *)
