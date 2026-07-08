Theory repeat_channel

Ancestors arithmetic bitstring bxor_lemmas interleave pispace polar_encode

Libs dep_rewrite realLib;

(* -------------------------------------------------------------------------- *)
(* Convert a list to an alternative representation as a function, where the   *)
(* natural number n is mapped to the nth element of the list.                 *)
(* -------------------------------------------------------------------------- *)
Definition list_to_function_def:
  list_to_function xs = λn. EL n xs
End

(* -------------------------------------------------------------------------- *)
(* Converts from a function-based product of measure spaces (as defined in    *)
(* pispace$pi_measure_space by Jared Yeager) into a list-based product of     *)
(* measure spaces                                                             *)
(* -------------------------------------------------------------------------- *)
Definition pi_measure_space_to_pi_list_measure_space_def:
  pi_measure_space_to_pi_list_measure_space
  (n : num) (m : (num -> α) m_space) =
  ({xs | list_to_function xs ∈ m_space m},
   {xss | IMAGE list_to_function xss ∈ measurable_sets m},
   (λxss. measure m (IMAGE list_to_function xss))
  )
  : (α list) m_space
End

(* -------------------------------------------------------------------------- *)
(* Converts a list of measure spaces into the product measure space over      *)
(* lists of the values taken by each measure space.                           *)
(*                                                                            *)
(* We build this on top of pispace$pi_measure_space by Jared Yeager.          *)
(*                                                                            *)
(* prod_measure_space doesn't work for this purpose because                   *)
(* it changes the type of the output: we start with α and β and produce       *)
(* α # β. Thus, the type output by this function would depend on the length   *)
(* of the list given as input, so we cannot just apply prod_measure_space     *)
(* naively.                                                                   *)
(* -------------------------------------------------------------------------- *)
Definition pi_list_measure_space_def:
  pi_list_measure_space (ms : (α m_space) list) =
  pi_measure_space_to_pi_list_measure_space
  (LENGTH ms) (pi_measure_space (LENGTH ms) (λn. EL n ms))
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
