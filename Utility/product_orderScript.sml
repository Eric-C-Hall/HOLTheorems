Theory product_order

Ancestors arithmetic relation prim_rec

Libs useful_tacticsLib dep_rewrite;

(* -------------------------------------------------------------------------- *)
(* Return the product order of two orders.                                    *)
(*                                                                            *)
(* (a1, b1) ≤ (a2, b2) under the product order if and only if:                *)
(* - a1 ≤ a2 AND                                                              *)
(* - b1 ≤ b2                                                                  *)
(*                                                                            *)
(* This works for both strict orders (returning a strict order), and orders   *)
(* that are not strict (returning a order that is not strict).                *)
(* -------------------------------------------------------------------------- *)
Definition product_order_def:
  product_order ord1 ord2 (a1, b1) (a2, b2) ⇔ ord1 a1 a2 ∧ ord2 b1 b2
End

(* -------------------------------------------------------------------------- *)
(* The product order of two well-founded orders is well-founded.              *)
(* -------------------------------------------------------------------------- *)
Theorem WF_product_order:
  ∀ord1 ord2.
    WF ord1 ∧
    WF ord2 ⇒
    WF (product_order ord1 ord2)
Proof
  rpt strip_tac
  >> gvs[WF_DEF]
  >> rpt strip_tac
  (* We have a nonempty set B, and want to prove that it has a minimal element
     with respect to the product ordering.
.
     Consider the set B2 of all FST elements corresponding to SND elements which
     are minimal with respect to ord2. By well-foundedness of ord1, if there is
     an element of B2, then there is an element of B2 which is minimal with
     respect to ord1. Since we also already know that this element is minimal
     with respect to ord2, it must be minimal with respect to the product order.
   *)
  >> last_x_assum $ qspecl_then [‘{w1 | w1, min_2 | B (w1, min_2) ∧
                                                    (∀b. ord2 (SND b) min_2 ⇒
                                                            ¬B b)}’] assume_tac
  >> qmatch_asmsub_abbrev_tac ‘exists_in_new_set ⇒ exists_min_in_new_set’
  (* There exists an element in the new set by well-foundedness of of ord2 *)
  >> sg ‘exists_in_new_set’
  >- (unabbrev_all_tac
      >> pop_assum kall_tac
      (* Apply well-foundedness of ord2 to the set of SND elements in B *)
      >> last_x_assum $ qspecl_then [‘IMAGE SND B’] assume_tac
      >> gvs[]
      (* The set of SND elements in B is nonempty because B is nonempty. *)
      >> qmatch_asmsub_abbrev_tac ‘exists_in_set ⇒ _’
      >> ‘exists_in_set’ by (unabbrev_all_tac >> qexists ‘w’ >> ASM_SET_TAC[])
      >> gs[]
      (* We have found the minimum SND element, now we choose this element
         along with the corresponding FST element to show the existance of an
         element in the set of minimal *)
      >> Cases_on ‘x’
      >> qexistsl [‘q’, ‘(q, min)’]
      >> gvs[]
      >> ASM_SET_TAC[]
     )
  (* We have now found a minimal first element that corresponds to a
     minimal second element. Choose these minimal elements as our minimal
     element with respect to the product order *)
  >> gvs[]
  >> Cases_on ‘x’
  >> qexists ‘(min, r)’
  >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘b’ >> gvs[product_order_def]
  >> gvs[product_order_def]
  >> rpt strip_tac
  >> gvs[product_order_def]
QED

Theorem WF_product_order_num[simp]:
  WF (product_order ($< : num -> num -> bool) ($< : num -> num -> bool))
Proof
  metis_tac[WF_product_order, WF_LESS]
QED

(* -------------------------------------------------------------------------- *)
(* Takes an order and returns a strict order                                  *)
(* -------------------------------------------------------------------------- *)
Definition to_strict:
  to_strict ord a b ⇔ ord a b ∧ a ≠ b
End

(* -------------------------------------------------------------------------- *)
(* If we have two well-formed orders, then the strictified product order of   *)
(* the un-strictified orders is well-formed.                                  *)
(*                                                                            *)
(* This order is defined by:                                                  *)
(* (a1,b1) < (a2,b2) <=> a1 ≤ a2 /\ b1 ≤ b2 /\ (a1,b1) ≠ (a2,b2)              *)
(*                                                                            *)
(* Or alternatively:                                                          *)
(* (a1,b1) < (a2,b2) <=> (a1 < a2 \/ b1 < b2) /\ a1 ≤ a2 /\ b1 ≤ b2           *)
(*                                                                            *)
(* This allows us to increase the strength of our inductive hypothesis.       *)
(*                                                                            *)
(* When using the product order of two strict orders, our inductive           *)
(*   hypothesis would be:                                                     *)
(* a_prev < a_cur /\ b_prev < b_cur ==> P a_prev b_prev                       *)
(*                                                                            *)
(* When using the strictified product order of unstricitified orders, our     *)
(*   inductive hypothesis would be:                                           *)
(* a_prev ≤ a_cur /\  b_prev ≤ b_cur /\ (a_prev, b_prev) ≠ (a_cur, b_cur)     *)
(*   which is stronger.                                                       *)
(* -------------------------------------------------------------------------- *)
(*Theorem WF_to_strict_product_order:
  ARB
Proof
  
QED*)
