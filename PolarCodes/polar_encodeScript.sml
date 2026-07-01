Theory polar_encode

Ancestors arithmetic bitstring bxor_lemmas interleave

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
(* Unlike in Arıkan's original Polar Codes paper, we use the computer science *)
(* convention of 0-indexed lists rather than the mathematical convention of   *)
(* 1-indexed lists                                                            *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Important theorems:                                                        *)
(* - Theorem 1: the channels polarize                                         *)
(* - Proposition 2: bound on probability of block error                       *)
(* - Theorem 4: asymptotic bound on block error probability with respect to N *)
(* - Encoding and decoding are both O(n log n)                                *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Polar encoding:                                                            *)
(* polar_encode = polar_encode (even_inputs bitwise_XOR odd_inputs) ++        *)
(*                polar_encode odd_inputs                                     *)
(*                                                                            *)
(* Undefined behaviour if length of input is not a power of two.              *)
(* -------------------------------------------------------------------------- *)
Definition polar_encode_def:
  polar_encode (inputs : bool list) =
  if LENGTH inputs ≤ 1 then inputs
  else
    let
      even_odd_inputs = deinterleave 2 inputs;
      even_inputs = EL 0 even_odd_inputs;
      odd_inputs = EL 1 even_odd_inputs;
    in
      polar_encode (bxor even_inputs odd_inputs) ++ polar_encode odd_inputs
Termination
  WF_REL_TAC ‘measure (LENGTH)’
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> simp[length_el_deinterleave]
      >> rw[]
      (* 2 ≤ LENGTH inputs MOD 2 is a contradiction because anything mod 2 is
         less than 2. *)
      >> ‘F’ suffices_by strip_tac
      >> sg ‘LENGTH inputs MOD 2 < 2’
      >- simp[]
      >> simp[])
  >> gen_tac >> strip_tac
  >> pop_assum mp_tac >> PURE_ONCE_REWRITE_TAC[NOT_LE] >> disch_tac
  >> simp[bxor_length]
  >> simp[hd_deinterleave, el_deinterleave]
  >> simp[length_get_every_nth_element]
  >> Cases_on ‘LENGTH inputs MOD 2 = 0’
  >- simp[]
  >> Cases_on ‘LENGTH inputs MOD 2 = 1’              
  >- (simp[]
      (* It turns out to be easier to prove if we manually prove some small
         cases, which turn out to be kinda special cases. In particular, note
         that for LENGTH inputs = 2, we have
         LENGTH inputs DIV 2 + 1 ≤ LENGTH inputs, whereas we will end up
         wanting LENGTH inputs DIV 2 + 1 < LENGTH inputs *)
      >> Cases_on ‘LENGTH inputs = 2’
      >- gvs[]
      >> Cases_on ‘LENGTH inputs = 3’
      >- simp[]
      (* We want to prove that 1 < LENGTH inputs DIV 2, which will then get us
         LENGTH inputs DIV 2 + 1 < LENGTH inputs.
         This is easier to represent by breaking down the inequality we are
         trying to prove into two inqualities *)
      >> qsuff_tac ‘LENGTH inputs DIV 2 + 1 <
                    LENGTH inputs DIV 2 + LENGTH inputs DIV 2 ∧
                    LENGTH inputs DIV 2 + LENGTH inputs DIV 2 ≤
                    LENGTH inputs’
      >- simp[]
      >> conj_tac
      >- (simp[LT_ADD_LCANCEL]
          >> ‘3 < LENGTH inputs’ by simp[]
          >> gvs[]
          >> qsuff_tac ‘2 * 1 < 2 * (LENGTH inputs DIV 2)’
          >- simp[]
          >> PURE_ONCE_REWRITE_TAC[bitTheory.DIV_MULT_THM2]
          >> simp[])
      >> simp[GSYM TIMES2]
      >> simp[bitTheory.DIV_MULT_THM2]
     )
  >> ‘F’ suffices_by strip_tac
  >> sg ‘LENGTH inputs MOD 2 < 2’
  >- simp[]
  >> simp[]
End

(* -------------------------------------------------------------------------- *)
(* Combines polar encoding with a channel, resulting in                       *)
(* -------------------------------------------------------------------------- *)
(*Definition polar_encode_channel_def:
  polar_encode_channel num_inputs = 
End*)


(* -------------------------------------------------------------------------- *)
(* Hand-written calculations indicate that polar_encode with the input:       *)
(*   [T;F;F;F;T;F;T;T]                                                        *)
(* Should have the output:                                                    *)
(*   [F;T;F;F;T;T;T;T]                                                        *)
(* Double check consistency of formal definition with hand calculations.      *)
(* -------------------------------------------------------------------------- *)
Theorem polar_encode_unit_test_1:
  polar_encode [T;F;F;F;T;F;T;T] = [F;T;F;F;T;T;T;T]
Proof
  EVAL_TAC
QED



