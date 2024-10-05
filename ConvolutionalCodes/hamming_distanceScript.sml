open HolKernel Parse boolLib bossLib;

open arithmeticTheory;
open bitstringTheory;
open listTheory;

open dep_rewrite;

val _ = new_theory "hamming_distance";

val _ = set_mapped_fixity{fixity = Infixl 500, term_name = "bxor", tok = "⊕"}
                                                                  
Definition hamming_weight_def:
  hamming_weight [] = 0 ∧
  hamming_weight (b::bs) = (if b then 1 else 0) + hamming_weight bs
End

Definition hamming_distance_def:
  hamming_distance l1 l2 = hamming_weight (l1 ⊕ l2)
End

Theorem bitwise_cons:
  ∀f b bs c cs.
  LENGTH bs = LENGTH cs ⇒
  bitwise f (b::bs) (c::cs) = (f b c)::(bitwise f bs cs)
Proof
  rpt strip_tac
  >> gvs[bitwise_def]
QED

Theorem bxor_cons:
  ∀b bs c cs.
  LENGTH bs = LENGTH cs ⇒
  bxor (b::bs) (c::cs) = (b ⇎ c) :: bxor bs cs
Proof
  rpt strip_tac
  >> gvs[bxor_def]
  >> gvs[bitwise_cons]
QED

Theorem bitwise_commutative:
  ∀f bs cs.
  (∀b c. f b c = f c b) ⇒
  bitwise f bs cs = bitwise f cs bs
Proof
  rpt strip_tac
  >> gvs[bitwise_def]
  >> gvs[SPECL [“LENGTH bs”, “LENGTH cs”] MAX_COMM]
  >> qmatch_goalsub_abbrev_tac `ZIP (bs', cs')`
  >> sg ‘LENGTH bs' = LENGTH cs'’
  >- (unabbrev_all_tac
      >> gvs[])
  >> pop_assum mp_tac
  >> NTAC 2 (pop_assum kall_tac)
  >> SPEC_TAC (“cs' : bool list”, “cs' : bool list”)
  >> Induct_on ‘bs'’ >> rpt strip_tac >> gvs[]
  >> Cases_on ‘cs'’ >> gvs[]
  >> first_x_assum $ qspec_then ‘t’ assume_tac
  >> gvs[]
QED

Theorem bxor_commutative:
  ∀bs cs. bxor bs cs = bxor cs bs
Proof
  rpt strip_tac
  >> gvs[bxor_def]
  >> irule bitwise_commutative
  >> rpt strip_tac
  >> gvs[]
  >> decide_tac
QED

Theorem hamming_distance_self[simp]:
  ∀bs. hamming_distance bs bs = 0
Proof
  rpt strip_tac
  >> gvs[hamming_distance_def]
  >> Induct_on ‘bs’
  >- EVAL_TAC
  >> rpt strip_tac
  >> DEP_PURE_ONCE_REWRITE_TAC[bxor_cons]
  >> gvs[]
  >> gvs[hamming_weight_def]
QED

Theorem hamming_distance_symmetric:
  ∀bs cs. hamming_distance bs cs = hamming_distance cs bs
Proof
  rpt strip_tac
  >> gvs[hamming_distance_def]
  >> gvs[bxor_commutative]
QED

(*Theorem hamming_distance_triangle_inequality:
  ∀bs cs ds.
  LENGTH bs = LENGTH cs ∧
  LENGTH cs = LENGTH ds ⇒
  hamming_distance bs ds ≤ hamming_distance bs cs + hamming_distance cs ds
Proof
  rpt strip_tac
QED*)

Theorem hamming_distance_cons:
  ∀b bs c cs.
  LENGTH bs = LENGTH cs ⇒
  hamming_distance (b::bs) (c::cs) = (if b = c then 0 else 1) + hamming_distance bs cs
Proof
  rpt strip_tac
  >> gvs[hamming_distance_def]
  >> gvs[bxor_cons]
  >> gvs[hamming_weight_def]
  >> Cases_on ‘b’ >> Cases_on ‘c’ >> gvs[]
QED

Theorem hamming_distance_append_left:
  ∀bs cs ds.
  LENGTH bs + LENGTH cs = LENGTH ds ⇒
  hamming_distance (bs ⧺ cs) ds = hamming_distance bs (TAKE (LENGTH bs) ds) + hamming_distance cs (DROP (LENGTH bs) ds)
Proof
  Induct_on ‘ds’
  >- (Cases_on ‘bs’ >> Cases_on ‘cs’ >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘bs’
  >- gvs[]
  >> gvs[APPEND]
  >> gvs[hamming_distance_cons]
QED

Theorem hamming_distance_append_right:
  ∀bs cs ds.
  LENGTH bs = LENGTH cs + LENGTH ds ⇒
  hamming_distance bs (cs ⧺ ds) = hamming_distance (TAKE (LENGTH cs) bs) cs + hamming_distance (DROP (LENGTH cs) bs) ds
Proof
  metis_tac[hamming_distance_append_left, hamming_distance_symmetric]
QED

(* -------------------------------------------------------------------------- *)
(* Unit tests                                                                 *)
(* -------------------------------------------------------------------------- *)

Theorem bxor_test:
  [F; T; T; F; T; F; F] ⊕ [T; T; F; F; T; T; F] = [T; F; T; F; F; T; F] ∧
  [F; F; F; F; F; F; F] ⊕ [T; F; F; T; T; F; F] = [T; F; F; T; T; F; F] ∧
  [T; T; T; T; F; F; F] ⊕ [F; F; F; T; T; T; T] = [T; T; T; F; T; T; T]
Proof
  EVAL_TAC  
QED

Theorem hamming_weight_test:
  hamming_weight [F; T; F; F; F; F; F; F; F; T; T; F; F; F; F; T] = 4 ∧
  hamming_weight [] = 0 ∧
  hamming_weight [T; T; T] = 3 ∧
  hamming_weight [F; T; F; T] = 2
Proof
  EVAL_TAC
QED

Theorem hamming_distance_test:
  hamming_distance [F; T; T; F; T; F; F] [T; T; F; F; T; T; F] = 3 ∧
  hamming_distance [F; F; F] [T; T; T] = 3 ∧
  hamming_distance [F; T; F; T; F] [F; T; F; T; F] = 0
Proof
  EVAL_TAC
QED

val _ = export_theory();
