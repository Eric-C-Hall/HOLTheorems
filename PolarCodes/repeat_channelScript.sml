Theory repeat_channel

Ancestors arithmetic bitstring bxor_lemmas interleave polar_encode

Libs dep_rewrite realLib;

(*Definition repeat_channel_def:
  repeat_channel (W : (bool, β) memoryless_channel) (num_inputs : num)
  (input : bool list)
  = if (num_inputs = 0) then []
    else
      ((memoryless_channel_REP W) (HD input))::(repeat_channel W (num_inputs - 1) (TL input)
                                                : (β list) mspace
                                                           End*)


(* -------------------------------------------------------------------------- *)
(* Same naming convention as PROD_IMAGE, EXTREAL_PROD_IMAGE, REAL_PROD_IMAGE, *)
(* etc                                                                        *)
(* -------------------------------------------------------------------------- *)
(*Definition prod_measure_space_image_def:
  prod_measure_space_image S = ITSET prod_measure_space S (ARB)
                               : (α m_space -> bool)
End*)

(*Definition prod_measure_space_map_def:
  prod_measure_space_map [] = ARB ∧
  prod_measure_space_map (m::(ms : (α m_space) list))
  = ARB
    : (α list) m_space
End*)

(* -------------------------------------------------------------------------- *)
(* Converts a list of measure spaces into the product measure space over      *)
(* lists of the values taken by each measure space.                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* The pre-existing prod_measure_space doesn't work for this purpose because  *)
(* it changes the type of the output: we start with α and β and produce       *)
(* α # β. Thus, the type output by this function would depend on the length   *)
(* of the list given as input, so we cannot just apply prod_measure_space     *)
(* naively.                                                                   *)
(* -------------------------------------------------------------------------- *)
Definition prod_measure_space_map_def:
  prod_measure_space_map (ms : (α m_space) list) =
  ({xs | LENGTH xs = LENGTH ms ∧
         ∀n. EL n xs ∈ ⇒ ∧
                         ∀n. EL n ∧
                             ∀n} space ,)
  : (α list) m_space
End

(* -------------------------------------------------------------------------- *)
(* Given a memoryless channel, transform it into n parallel instances of that *)
(* channel.                                                                   *)
(* -------------------------------------------------------------------------- *)
Definition repeat_channel0_def:
  repeat_channel0 (W : (α -> bool) # (α -> β m_space)) (n : num) =
  ({xs | LENGTH xs = n},
   λrepeated_inputs.
     (MAP (mcchannel W) repeated_inputs)
  )
  : (α list -> bool) # (α list -> β list m_space)
End

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
