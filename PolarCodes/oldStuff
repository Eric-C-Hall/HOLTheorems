
(* -------------------------------------------------------------------------- *)
(* Possible improvement: extract this to library                              *)
(*                                                                            *)
(* See also: probabilityTheory.prob_on_finite_set                             *)
(* -------------------------------------------------------------------------- *)
(*Theorem finite_countably_additive_finite_additive:
  ∀m.
    FINITE (m_space m) ∧
    positive m ∧
    ∅ ∈ measurable_sets m ⇒
    (countably_additive m ⇔ finite_additive m)

Proof

  gen_tac >> strip_tac
  >> EQ_TAC
  >- (strip_tac
      >> irule COUNTABLY_ADDITIVE_FINITE_ADDITIVE
      >> simp[])
  >> strip_tac
  >> gvs[finite_additive_def]
  >> simp[countably_additive_def]
  >> gen_tac >> strip_tac
  >> gvs[FUNSET]
  >> cheat (* TODO Ask Chun *)
  
QED*)

(* -------------------------------------------------------------------------- *)
(* Possible improvement: extract this to library                              *)
(*                                                                            *)
(* See also: probabilityTheory.prob_on_finite_set                             *)
(* -------------------------------------------------------------------------- *)
(*Theorem finite_countably_additive:
  ∀m.
    FINITE (m_space m) ∧
    (∀S T. S ∈ measurable_sets m ∧
           T ∈ measurable_sets m ∧
           DISJOINT S T ⇒
           measure m S + measure m T = measure m (S ∪ T)) ⇒
    countably_additive m
                       
Proof
  
  gen_tac >> strip_tac
  >> simp[countably_additive_def] 
  >> gen_tac >> strip_tac
  
  >> cheat (* TODO Ask Chun *)
QED*)
