Theory product_order

Ancestors arithmetic relation

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
Definition product_order:
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
     Consider the set B2 of all minimal elements with respect to ord2. By
     well-foundedness of ord1, if there is an element of B2, then there is an
     element of B2 which is minimal with respect to ord1. Since we also already
     know that this element is minimal with respect to ord2, it must be minimal
     with respect to the product order. *)
  >> last_x_assum $ qspecl_then [‘{min_2 | B (INR min_2)}’] assume_tac
  (* *)
         
  (* There exists a minimal element of B with respect to one of the orderings.
   *)
  >> first_x_assum $ qspecl_then [‘IMAGE SND B’] assume_tac
  >> gvs[]
  >> Q.SUBGOAL_THEN ‘∃x. x ∈ B’ assume_tac
  >- (qexists ‘w’ >> ASM_SET_TAC[])
  >> gs[]
  (* Consider the set of all minimal elements with respect to the first
     ordering. Then there exists a minimal element of this set with respect to
     the other ordering.*)
  >> last_x_assum $ qspecl_then [‘{}’]
  >> gvs[]
  (* Now we know that our *)


        
  (* We have a set of minimal elements with respect to ord1.
     This set has a minimal element with respect to ord2. *)
  >> 
         
         
  GSYM IN_DEF]
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
