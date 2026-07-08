Theory repeat_channel

Ancestors arithmetic bitstring bxor_lemmas interleave lifting measure memoryless_channel pispace polar_encode pred_set probability sigma_algebra transfer

Libs dep_rewrite realLib liftLib transferLib;

val _ = hide "W";

(* TODO: move the definitions that help to define pi_measure_space_list based on
   pi_measure_space into their own file, perhaps *)

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

Theorem list_to_function_inj:
  ∀x y.
    LENGTH x = LENGTH y ∧
    list_to_function x = list_to_function y ⇒
    x = y
Proof
  Induct_on ‘x’ >> Cases_on ‘y’ >> simp[]
  >> gen_tac >> strip_tac
  >> gvs[list_to_function_def, FUN_EQ_THM]
  >> conj_tac
  (* Handle the head case by applying assumption at n = 0 *)
  >- (pop_assum $ qspec_then ‘0’ assume_tac
      >> gvs[])
  (* Use the inductive hypothesis *)
  >> last_x_assum $ qspec_then ‘t’ irule
  >> simp[]
  >> gen_tac
  >> rw[]
  (* Apply assumption at the appropriate index *)
  >> first_x_assum $ qspec_then ‘SUC x'’ assume_tac
  >> gvs[]
QED

Theorem list_to_function_empty[simp]:
  list_to_function [] = (λx. ARB)
Proof
  simp[list_to_function_def]
QED

Theorem list_to_function_cons:
  ∀ls l.
    list_to_function (l::ls) = λn. if n = 0
                                   then l
                                   else (list_to_function ls) (n - 1)
Proof
  rpt gen_tac
  >> simp[list_to_function_def]
  >> simp[FUN_EQ_THM]
  >> gen_tac
  >> Cases_on ‘n’ >> simp[]
  >> rw[] >> gvs[]
QED

Theorem list_to_function_snoc:
  ∀ls l.
    list_to_function (SNOC l ls) = λn. (if n = LENGTH ls
                                        then l
                                        else (list_to_function ls) n)
Proof
  Induct_on ‘ls’ >> simp[]
  >- (gen_tac >> simp[list_to_function_def])
  >> rpt gen_tac
  >> simp[list_to_function_cons]
  >> simp[FUN_EQ_THM]
  >> gen_tac
  >> Cases_on ‘n = 0’ >> simp[]
  >> simp[ADD1]
  >> rw[] >> gvs[]
QED

(* If the function is entirely ARB after the index n, it can be represented as
   a finite list of length n. *)
Theorem list_to_function_surj:
  ∀y n.
    (∀i. n ≤ i ⇒ y i = ARB) ⇒
    (∃x. LENGTH x = n ∧
         list_to_function x = y)
Proof
  Induct_on ‘n’ >> simp[]
  >- (gen_tac >> strip_tac >> simp[FUN_EQ_THM])
  >> gen_tac >> strip_tac
  (* Use the inductive hypothesis on our list y, but with the final element
     replaced by ARB so that it is applicable *)
  >> last_x_assum $ qspec_then ‘λinput. if input = n then ARB else y input’
                  assume_tac
  >> gs[]
  >> qexists ‘SNOC (y n) x’
  >> simp[]
  >> simp[list_to_function_snoc]
  >> simp[FUN_EQ_THM]
  >> gen_tac
  >> rw[]
QED

Theorem isomorphic_pi_measure_space_to_pi_measure_space_list:
  ∀n m.
    measure_space m ⇒
    isomorphic m (pi_measure_space_to_pi_measure_space_list n m)
Proof
  rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[isomorphic_sym]
  >> simp[isomorphic_def]
  >> qexists ‘list_to_function’
  >> simp[pispaceTheory.measure_preserving_def]
  >> conj_tac
  >- (simp[measurability_preserving_def]
      >> rpt conj_tac
      >- (simp[pi_measure_space_to_pi_measure_space_list_def]
          >> cheat
         )
      >- (simp[pi_measure_space_to_pi_measure_space_list_def]
          >> simp[BIJ_DEF]
          >> conj_tac
          >- (simp[INJ_DEF]
              >> rpt gen_tac >> rpt strip_tac
              >> simp[list_to_function_inj])
          >> simp[SURJ_DEF]
          >> gen_tac >> strip_tac
          >> 
         )
     )
  >> simp[pi_measure_space_to_pi_measure_space_list_def]
QED

Theorem measure_space_pi_measure_space_to_pi_measure_space_list:
  ∀n m.
    measure_space m ⇒
    measure_space (pi_measure_space_to_pi_measure_space_list n m)
Proof
  rpt gen_tac >> strip_tac
  >> simp[pi_measure_space_to_pi_measure_space_list_def]
  >> simp[measure_space_def]
  >> cheat
QED

Theorem pi_measure_space_to_pi_measure_space_list_measure_entire_space:
  ∀m.
    measure m (m_space m) = 1 ⇒
    measure (pi_measure_space_to_pi_measure_space_list n m)
            (m_space (pi_measure_space_to_pi_measure_space_list n m)) =
    1
Proof
  gen_tac
  >> simp[pi_measure_space_to_pi_measure_space_list_def]
  >> ‘IMAGE list_to_function {xs | list_to_function xs ∈ m_space m}
                                   = m_space m’ suffices_by simp[]
  >> simp[FUN_EQ_THM]
  >> gen_tac
  >> EQ_TAC
  >- (strip_tac
      >> ASM_SET_TAC[])
  >> strip_tac
  >> qexists ‘list_to_function x’
QED

Theorem prob_space_pi_measure_space_to_pi_measure_space_list:
  ∀n m.
    prob_space m ⇒
    prob_space (pi_measure_space_to_pi_measure_space_list n m)
Proof
  rpt gen_tac
  >> simp[prob_space_def, measure_space_pi_measure_space_to_pi_measure_space_list]
  >> 
  >> gs[prob_space_def]
  >> simp[pi_measure_space_to_pi_measure_space_list_def]
  >> gs[prob_space_def]
  >> conj_tac
  >- (simp[measure_space_def]
     )
QED

Theorem prob_space_pi_measure_space_list:
  ∀ms.
    (∀m. MEM m ms ⇒ prob_space m) ⇒
    prob_space (pi_measure_space_list ms)
Proof
  rpt gen_tac >> strip_tac
  >> simp[pi_measure_space_list_def]
QED

Theorem wf_memoryless_channel_repeat_channel0:
  ∀W n.
    wf_memoryless_channel W ⇒
    wf_memoryless_channel (repeat_channel0 W n)
Proof
  rpt gen_tac
  >> namedCases_on ‘W’ ["channel_dom channel_func"]
  >> simp[wf_memoryless_channel_def, mcdomain0_def, mcchannel0_def]
  >> strip_tac
  >> gen_tac
  >> simp[repeat_channel0_def, mcchannel0_def]
  >> strip_tac
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
