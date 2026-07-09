Theory pi_measure_space_list_alt

Ancestors arithmetic bitstring bxor_lemmas interleave jared_yeager_listspace lifting measure memoryless_channel pispace polar_encode pred_set probability sigma_algebra transfer trivial

Libs dep_rewrite realLib liftLib transferLib;

(* -------------------------------------------------------------------------- *)
(* Convert a list to an alternative representation as a function, where the   *)
(* natural number n is mapped to the nth element of the list.                 *)
(*                                                                            *)
(* All unassigned elements are set to ARB, for consistency with pi_rect_def.  *)
(* -------------------------------------------------------------------------- *)
Definition list_to_function_def:
  list_to_function xs = λn. if n < LENGTH xs then EL n xs else ARB
End

(* -------------------------------------------------------------------------- *)
(* Converts from a function-based product of measure spaces (as defined in    *)
(* pispace$pi_measure_space by Jared Yeager) into a list-based product of     *)
(* measure spaces.                                                            *)
(*                                                                            *)
(* We assume that all functions are meaningful up to the value n, and beyond  *)
(* this point, all elements are set to ARB. This is because it isn't possible *)
(* to tell the difference between, for example:                               *)
(* 0 -> a; 1 -> b; (of length 2, followed by an infinite string of ARBs)      *)
(* and                                                                        *)
(* 0 -> a; 1 -> b; 2 -> ARB (of length 3, followed by an infinite string of   *)
(* ARBs.)                                                                     *)
(* So we have to somehow work out what lengths are appropriate: for this      *)
(* application, we want to always choose the same length n.                   *)
(*                                                                            *)
(* We also have to be careful to restrict ourselves only to lists of length   *)
(* n, because [1] and [1;ARB] will both map to the same function.             *)
(* -------------------------------------------------------------------------- *)
Definition pi_measure_space_to_pi_measure_space_list_def:
  pi_measure_space_to_pi_measure_space_list
  (n : num) (m : (num -> α) m_space) =
  ({xs | LENGTH xs = n ∧ list_to_function xs ∈ m_space m},
   {xss | (∀xs. xs ∈ xss ⇒ LENGTH xs = n) ∧
          IMAGE list_to_function xss ∈ measurable_sets m},
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
Definition pi_measure_space_list_def:
  pi_measure_space_list (ms : (α m_space) list) =
  pi_measure_space_to_pi_measure_space_list
  (LENGTH ms) (pi_measure_space (LENGTH ms) (λn. EL n ms))
  : (α list) m_space
End
