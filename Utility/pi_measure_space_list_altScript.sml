Theory pi_measure_space_list_alt

Ancestors arithmetic bitstring bxor_lemmas lifting measure pispace pred_set probability sigma_algebra transfer trivial

Libs dep_rewrite realLib liftLib transferLib;

val _ = hide "S";

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

(*Theorem sigma_algebra_measurable_space_pi_measure_space_to_pi_measure_space_list:
  ∀n m.
    sigma_algebra (measurable_space m) ∧
    (∀f. f ∈ m_space m ⇒ (∀i. n ≤ i ⇒ f i = ARB)) ⇒
    sigma_algebra (measurable_space
                   (pi_measure_space_to_pi_measure_space_list n m))
Proof
  rpt gen_tac >> strip_tac
  >> simp[pi_measure_space_to_pi_measure_space_list_def]
  >>
  TRACE_SIGMA_ALGEBRA probably not useful,
        

        
        >> gvs[measure_space_def]
        >> simp[sigma_algebra_def]
        >> conj_tac
        >- (cheat
           )
        >> gen_tac
        >> strip_tac
QED*)

(* -------------------------------------------------------------------------- *)
(* Converting a measure space from function form to list form will result in  *)
(* an isomorphic result if the initial measure space in function form is      *)
(* valid: i.e. all values after the final index n are ARB.                    *)
(* -------------------------------------------------------------------------- *)
(*Theorem isomorphic_pi_measure_space_to_pi_measure_space_list:
  ∀n m.
    measure_space m ∧
    (∀f. f ∈ m_space m ⇒ (∀i. n ≤ i ⇒ f i = ARB)) ⇒
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
          >> simp[sigma_algebra_def]
          >> conj_tac
          >- (cheat
             )
         )
      >- (simp[pi_measure_space_to_pi_measure_space_list_def]
          >> simp[BIJ_DEF]
          >> conj_tac
          >- (simp[INJ_DEF]
              >> rpt gen_tac >> rpt strip_tac
              >> simp[list_to_function_inj])
          >> simp[SURJ_DEF]
          >> gen_tac >> strip_tac
          >> qspecl_then [‘x’, ‘n’] assume_tac list_to_function_surj
          >> metis_tac[]
         )
      >- (gen_tac >> simp[pi_measure_space_to_pi_measure_space_list_def])
      >> simp[pi_measure_space_to_pi_measure_space_list_def]
      >> gen_tac >> strip_tac
      >> DEP_PURE_ONCE_REWRITE_TAC[BIJ_IMAGE_PREIMAGE]
      >> conj_tac
      >- (qexists ‘m_space m’
          >> REVERSE conj_tac
          >- (Cases_on ‘m’ >> Cases_on ‘r’ >> gvs[]
              >> gvs[measure_space_def]
              >> qspecl_then [‘(q,q')’, ‘s’] assume_tac SIGMA_ALGEBRA_SUBSET_SPACE
              >> gvs[]
             )
          >> simp[BIJ_DEF]
          >> conj_tac
          >- (simp[INJ_DEF]
              >> rpt gen_tac >> rpt strip_tac
              >> simp[list_to_function_inj])
          >> simp[SURJ_DEF]
          >> gen_tac >> strip_tac
          >> metis_tac[list_to_function_surj]
         )
      >> simp[]
     ) 
  >> simp[pi_measure_space_to_pi_measure_space_list_def]
QED*)

(*Theorem measure_space_pi_measure_space_to_pi_measure_space_list:
  ∀n m.
    measure_space m ⇒
    measure_space (pi_measure_space_to_pi_measure_space_list n m)
Proof
  rpt gen_tac >> strip_tac
  >> simp[pi_measure_space_to_pi_measure_space_list_def]
  >> simp[measure_space_def]
  >> cheat
QED*)

(*
Theorem pi_measure_space_to_pi_measure_space_list_measure_entire_space:
  ∀m.
    measure m (m_space m) = 1 ⇒
    measure (pi_measure_space_to_pi_measure_space_list n m)
            (m_space (pi_measure_space_to_pi_measure_space_list n m)) =
    1
Proof
  gen_tac
  >> simp[pi_measure_space_to_pi_measure_space_list_def]
  >> qmatch_goalsub_abbrev_tac ‘_ ⇒ measure _ (IMAGE _ S) = _’
  >> ‘IMAGE list_to_function S = m_space m’ suffices_by simp[]
  >> simp[FUN_EQ_THM, Abbr ‘S’]
  >> gen_tac
  >> EQ_TAC
  >- (strip_tac
      >> ASM_SET_TAC[])
  >> strip_tac
  >> cheat (* >> qexists ‘list_to_function x’*)
QED
*)

(*Theorem prob_space_pi_measure_space_to_pi_measure_space_list:
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
QED*)

(*Theorem prob_space_pi_measure_space_list:
  ∀ms.
    (∀m. MEM m ms ⇒ prob_space m) ⇒
    prob_space (pi_measure_space_list ms)
Proof
  rpt gen_tac >> strip_tac
  >> simp[pi_measure_space_list_def]
QED
*)
