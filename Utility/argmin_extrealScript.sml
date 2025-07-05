open HolKernel Parse boolLib bossLib;

val _ = new_theory "argmin_extreal";

open extrealTheory;
open pred_setTheory;
open dep_rewrite;

(* -------------------------------------------------------------------------- *)
(* I attempted using iterate and ITSET for this, however, they require a base *)
(* case for when argmin is applied to the empty set, but argmin applied to    *)
(* the empty set doesn't really have a sensible ouput.                        *)
(*                                                                            *)
(* I also attempted defining an inductive definition, but I didn't know how   *)
(* to do this for sets. It's much easier for lists, since you can choose the  *)
(* first element of the list at each stage, but with sets this is harder.     *)
(*                                                                            *)
(* So I ended up using a definition based on the choice operator.             *)
(* -------------------------------------------------------------------------- *)
Definition argmin_def:
  argmin (f : α -> extreal) xs = (@x. x ∈ xs ∧ (∀y. y ∈ xs ⇒ f x ≤ f y))
End

Definition argmax_def:
  argmax f xs = argmin (λx. -(f x)) xs
End

(* -------------------------------------------------------------------------- *)
(* Whether or not argmin has a valid value                                    *)
(* -------------------------------------------------------------------------- *)
Definition argmin_valid_def:
  argmin_valid (f : α -> extreal) xs = (∃x. x ∈ xs ∧ (∀y. y ∈ xs ⇒ f x ≤ f y))
End

Theorem argmin_sing[simp]:
  ∀f x.
    argmin f {x} = x
Proof
  rw[]
  >> gvs[argmin_def]
  >> SELECT_ELIM_TAC
  >> rw[]
QED

Theorem argmax_sing[simp]:
  ∀f x.
    argmax f {x} = x
Proof
  rw[argmin_sing, argmax_def]
QED

(* -------------------------------------------------------------------------- *)
(* Inserting an element maintains validity of argmin                          *)
(* -------------------------------------------------------------------------- *)
Theorem argmin_valid_insert:
  ∀f x xs.
    argmin_valid f xs ⇒
    argmin_valid f (x INSERT xs)
Proof
  rw[]
  >> gvs[argmin_valid_def]
  >> Cases_on ‘f x ≤ f x'’
  >- (qexists ‘x’ >> gvs[]
      >> rw[]
      >- gvs[]
      >> metis_tac[le_trans]
     )
  >> sg ‘f x' ≤ f x’
  >- metis_tac[le_lt, lt_le, extreal_lt_def]
  >> qpat_x_assum ‘¬_’ kall_tac
  >> qexists ‘x'’
  >> gvs[]
  >> rw[]
  >- gvs[]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* An empty set does not have a valid argmin                                  *)
(* -------------------------------------------------------------------------- *)
Theorem argmin_valid_empty[simp]:
  ∀f.
    argmin_valid f ∅ = F
Proof
  rw[argmin_valid_def]
QED

(* -------------------------------------------------------------------------- *)
(* A singleton set has a valid argmin                                         *)
(* -------------------------------------------------------------------------- *)
Theorem argmin_valid_sing[simp]:
  ∀f x.
    argmin_valid f {x} = T
Proof
  rw[]
  >> gvs[argmin_valid_def]
QED

(* -------------------------------------------------------------------------- *)
(* The argmin is in the set it is provided with as input                      *)
(* -------------------------------------------------------------------------- *)
Theorem argmin_in:
  ∀f xs.
    argmin_valid f xs ⇒
    argmin f xs ∈ xs
Proof
  rw[]
  >> gvs[argmin_def]
  >> SELECT_ELIM_TAC
  >> rw[]
  >> metis_tac[argmin_valid_def]
QED

(* -------------------------------------------------------------------------- *)
(* The argmin is leq than any of the provided input                           *)
(* -------------------------------------------------------------------------- *)
Theorem argmin_le:
  ∀f x xs.
    x ∈ xs ∧
    argmin_valid f xs ⇒
    f (argmin f xs) ≤ f x
Proof
  rw[]
  >> gvs[argmin_def]
  >> SELECT_ELIM_TAC
  >> rw[]
  >> metis_tac[argmin_valid_def]
QED
        
(* -------------------------------------------------------------------------- *)
(* A finite set has a valid argmin                                            *)
(* -------------------------------------------------------------------------- *)
Theorem argmin_valid_finite:
  ∀f xs.
    xs ≠ ∅ ∧
    FINITE xs ⇒
    argmin_valid f xs
Proof
  rw[]
  >> last_x_assum mp_tac
  >> Induct_on ‘xs’
  >> rw[]
  >> Cases_on ‘xs’
  >- gvs[]
  >> gvs[]
  >> simp[argmin_valid_def]
  >> Cases_on ‘f e ≤ f x ∧ (∀x'. x' ∈ t ⇒ f e ≤ f x')’
  >- (qexists ‘e’
      >> rw[] >> gvs[]
     )
  >> sg ‘∃m. m ∈ x INSERT t ∧ f m ≤ f e’
  >- (gvs[]
      >> metis_tac[lt_le, le_lt, extreal_lt_def]
     )
  >> qpat_x_assum ‘¬_’ kall_tac
  >> qexists ‘argmin f (x INSERT t)’
  >> conj_tac
  >- (Cases_on ‘argmin f (x INSERT t) = x’ >> gvs[]
      >> drule argmin_in
      >> gvs[]
     )
  >> rw[]
  >> metis_tac[argmin_le, le_trans, IN_INSERT]
QED

(* -------------------------------------------------------------------------- *)
(* Argmin over x INSERT xs is certainly equal to either x or the argmin over  *)
(* xs, but we do not in general know which one it is equal to, as they may    *)
(* each be minimal choices.                                                   *)
(*                                                                            *)
(* This was another failed proof (see below for the first one). It still      *)
(* doesn't necessarily have to equal either x or argmin f xs, because there   *)
(* every other element in xs may be a potential option for argmin, since it   *)
(* is possible that they are all minimal values.                              *)
(* -------------------------------------------------------------------------- *)
(*Theorem argmin_insert:
  ∀f x xs.
    argmin_valid f xs ⇒
    argmin f (x INSERT xs) = x ∨
    argmin f (x INSERT xs) = argmin f xs
Proof
  rw[]
  >> sg ‘argmin_valid f (x INSERT xs)’ >- gvs[argmin_valid_insert]
  >> PURE_REWRITE_TAC[argmin_def]
  >> SELECT_ELIM_TAC
  >> conj_tac
  >- metis_tac[argmin_valid_def]
  >> rw[]
  >> Cases_on ‘x' = x’ >> gvs[]
  >> SELECT_ELIM_TAC
  >> conj_tac >- metis_tac[argmin_valid_def]
  >> rw[]
QED*)

(* -------------------------------------------------------------------------- *)
(* The following attempt at an argmin_insert theorem failed because if the    *)
(* value of f for x and xs is the same, we don't know which one of them is    *)
(* the argmin, we only know that one of them must be.                         *)
(* -------------------------------------------------------------------------- *)
(*
Theorem argmin_insert:
  ∀f x xs.
    (∃x. x ∈ xs ∧ (∀y. y ∈ xs ⇒ f x ≤ f y)) ⇒
    argmin f (x INSERT xs) = if f x < f (argmin f xs)
                             then x
                             else argmin f xs
Proof
  rpt strip_tac
  >> gvs[argmin_def]
  >> SELECT_ELIM_TAC
  >> conj_tac
  >- (Cases_on ‘f x' ≤ f x’
      >- (qexists ‘x'’
          >> gvs[]
          >> rw[]
          >- gvs[]
          >> metis_tac[]
         )
      >> qexists ‘x’
      >> gvs[]
      >> rw[]
      >- gvs[]
      >> sg ‘f x ≤ f x'’
      >- metis_tac[extreal_lt_def, le_lt, lt_le]
      >> metis_tac[le_trans])
  >> rpt strip_tac
  >- (SELECT_ELIM_TAC
      >> rpt strip_tac
      >- metis_tac[]
      >> gvs[]
      >> rw[]
     )
QED*)

(* -------------------------------------------------------------------------- *)
(* Finding the bits that maximize the probability of receiving that bit,      *)
(* given that we received a particular message, is equivalent to finding the  *)
(* bits that maximize the probably that we both received that bit and         *)
(* received that message.                                                     *)
(*                                                                            *)
(* In more generality, if we are finding an argmax over a conditional         *)
(* probability where only the first event depends on the variable we are      *)
(* applying the argmax to, then the conditional probability can be reduced    *)
(* to an intersection.                                                        *)
(*                                                                            *)
(* This theorem fails, because what if both choices of bit have an equal      *)
(* probability? Since a bit is being chosen arbitrarily, we don't know if the *)
(* bit is equialent to the other bit chosen arbitrarily.                      *)
(* -------------------------------------------------------------------------- *)
(*Theorem argmax_cond_prob:
  ∀p_space P e s.
    s ≠ ∅ ∧ FINITE s ⇒
    argmax (λx. cond_prob p_space (P x) e) s =
    argmax (λx. prob p_space ((P x) ∩ e)) s
Proof
  rw[]
  >> last_x_assum mp_tac
  >> SPEC_ALL_TAC
  >> Induct_on ‘s’
  >> rw[]
  >> Cases_on ‘s’
  >- gvs[]
  >> gvs[]
  >> 
QED*)

(* -------------------------------------------------------------------------- *)
(* The above failed proofs show that generally, it's probably a good idea to  *)
(* steer away from using argmin. In particular, it does not have a defined    *)
(* result in the case of the empty set, and it does not have a clear way of   *)
(* deciding between two options that are equally minimal, and this second     *)
(* problem in particular tends to make it hard to prove things about          *)
(* something defined in terms of argmin, because you won't be able to prove   *)
(* its equality with another expression, only the fact that the result will   *)
(* be minimal.                                                                *)
(* -------------------------------------------------------------------------- *)


val _ = export_theory();
