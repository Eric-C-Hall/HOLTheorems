Theory hamming_distance

Ancestors arithmetic bitstring fundamental list

Libs dep_rewrite;

Definition hamming_distance_def:
  hamming_distance [] cs = 0n ∧
  hamming_distance bs [] = 0n ∧
  hamming_distance (b::bs) (c::cs) = hamming_distance bs cs + if b = c then 0n else 1n
End

(* -------------------------------------------------------------------------- *)
(* I accidentally defined hamming distance again without realising that it    *)
(* was already defined, so I moved it here                                    *)
(* -------------------------------------------------------------------------- *)
Definition hamming_distance_alt1_def:
  hamming_distance_alt1 (l1 : α list) (l2 : α list) = FOLDR ($+) 0n (MAP (λpair. if (FST pair = SND pair) then 0n else 1n) (ZIP (l1, l2)))
End

(* -------------------------------------------------------------------------- *)
(* I accidentally defined hamming distance again without realising that it    *)
(* was already defined, so I moved it here                                    *)
(* -------------------------------------------------------------------------- *)
Definition hamming_distance_alt2_def[simp]:
  hamming_distance_alt2 [] (l2 : α list) = 0 ∧
  hamming_distance_alt2 (l1 : α list) [] = 0 ∧
  hamming_distance_alt2 (h1::t1 : α list) (h2::t2 : α list) =
  (if (h1 = h2) then 0n else 1n) + hamming_distance_alt2 t1 t2
End

Theorem hamming_distance_cons[simp]:
  ∀b bs c cs.
    hamming_distance (b::bs) (c::cs) = (if b = c then 0 else 1) + hamming_distance bs cs
Proof
  rpt strip_tac
  >> gvs[hamming_distance_def]
QED

Theorem hamming_distance_alt1_cons:
  ∀b bs c cs.
    hamming_distance_alt1 (b::bs) (c::cs) = (if b = c then 0 else 1) + hamming_distance_alt1 bs cs
Proof
  rpt strip_tac
  >> gvs[hamming_distance_alt1_def]
QED

Theorem hamming_distance_alt1_alt2_equivalent:
  ∀bs cs.
    hamming_distance_alt1 bs cs = hamming_distance_alt2 bs cs
Proof
  Induct_on ‘bs’
  >- simp[hamming_distance_alt1_def, ZIP_def]
  >> rpt gen_tac
  >> Cases_on ‘cs’
  >- simp[hamming_distance_alt2_def, hamming_distance_alt1_def, ZIP_def]
  >> simp[hamming_distance_alt1_cons]
QED

Theorem hamming_distance_alt2_equivalent:
  ∀bs cs.
    hamming_distance_alt2 bs cs = hamming_distance bs cs
Proof
  Induct_on ‘bs’
  >- simp[hamming_distance_def]
  >> Cases_on ‘cs’
  >- simp[hamming_distance_def]
  >> gen_tac
  >> simp[]
QED

Theorem hamming_distance_alt1_equivalent:
  ∀bs cs.
    hamming_distance_alt1 bs cs = hamming_distance bs cs
Proof
  metis_tac[hamming_distance_alt1_alt2_equivalent, hamming_distance_alt2_equivalent]
QED

Theorem hamming_distance_empty_left[simp]:
  ∀cs. hamming_distance [] cs = 0
Proof
  gvs[hamming_distance_def]
QED

Theorem hamming_distance_empty_right[simp]:
  ∀bs. hamming_distance bs [] = 0
Proof
  Cases_on ‘bs’
  >> gvs[hamming_distance_def]
QED

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

Theorem hamming_distance_append:
  ∀bs cs ds es.
    LENGTH bs = LENGTH ds ⇒
    hamming_distance (bs ⧺ cs) (ds ⧺ es) = hamming_distance bs ds + hamming_distance cs es
Proof
  Induct_on ‘bs’ >> Cases_on ‘ds’ >> gvs[]
  >> rpt strip_tac
  >> last_x_assum $ qspecl_then [‘cs’, ‘t’, ‘es’] assume_tac
  >> gvs[]
  >> gvs[hamming_distance_def]
QED

Theorem hamming_distance_restrict:
  ∀bs cs.
    hamming_distance bs cs =
    hamming_distance (TAKE (LENGTH cs) bs) (TAKE (LENGTH bs) cs)
Proof
  rpt strip_tac
  >> Cases_on ‘LENGTH bs ≤ LENGTH cs’
  >- (gvs[TAKE_LENGTH_TOO_LONG]
      >> qspecl_then [‘LENGTH bs’, ‘cs’] assume_tac TAKE_DROP
      >> pop_assum (fn th => PURE_REWRITE_TAC [Once (GSYM th)])
      >> PURE_REWRITE_TAC[Once (GSYM APPEND_NIL)]
      >> gvs[hamming_distance_append])
  >> ‘LENGTH cs < LENGTH bs’ by gvs[] >> gvs[]
  >> gvs[TAKE_LENGTH_TOO_LONG]
  >> qspecl_then [‘LENGTH cs’, ‘bs’] assume_tac TAKE_DROP
  >> pop_assum (fn th => PURE_REWRITE_TAC [Once (GSYM th)])
  >> ‘cs = cs ⧺ []’ by gvs[] >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> gvs[hamming_distance_append]
QED

Theorem hamming_distance_self[simp]:
  ∀bs. hamming_distance bs bs = 0
Proof
  rpt strip_tac
  >> Induct_on ‘bs’
  >> gvs[hamming_distance_def]
QED

Theorem hamming_distance_symmetric_equal_length:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    hamming_distance bs cs = hamming_distance cs bs
Proof
  Induct_on ‘bs’ >> Cases_on ‘cs’ >> gvs[]
  >> rpt strip_tac
  >> gvs[hamming_distance_def]
  >> gvs[EQ_SYM_EQ]
  >> last_x_assum irule
  >> gvs[]
QED

Theorem hamming_distance_symmetric:
  ∀bs cs. hamming_distance bs cs = hamming_distance cs bs
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[hamming_distance_restrict]
  >> irule hamming_distance_symmetric_equal_length
  >> gvs[LENGTH_TAKE_EQ]
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
  >> gvs[hamming_distance_def]
QED

Theorem hamming_distance_append_right:
  ∀bs cs ds.
    LENGTH bs = LENGTH cs + LENGTH ds ⇒
    hamming_distance bs (cs ⧺ ds) = hamming_distance (TAKE (LENGTH cs) bs) cs + hamming_distance (DROP (LENGTH cs) bs) ds
Proof
  metis_tac[hamming_distance_append_left, hamming_distance_symmetric]
QED

Theorem hamming_distance_positivity:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    0 ≤ hamming_distance bs cs ∧
    (hamming_distance bs cs = 0 ⇔ bs = cs)
Proof
  rpt strip_tac
  >- gvs[hamming_distance_def]
  >> ‘∀cs. LENGTH bs = LENGTH cs ⇒ (hamming_distance bs cs = 0 ⇔ bs = cs)’ suffices_by gvs[]
  >> pop_assum kall_tac
  >> Induct_on ‘bs’ >> rpt strip_tac >> Cases_on ‘cs’ >> gvs[]
  >> EQ_TAC >> rpt strip_tac >> gvs[]
  >> Cases_on ‘h = h'’ >> gvs[]
QED

Theorem hamming_distance_length:
  ∀bs cs.
    hamming_distance bs cs ≤ LENGTH bs
Proof
  strip_tac
  >> gvs[hamming_distance_def]
  >> Induct_on ‘bs’ >> gvs[ZIP_def]
  >> strip_tac
  >> Cases_on ‘cs’ >> gvs[ZIP_def]
  >> pop_assum $ qspec_then ‘t’ assume_tac
  >> Cases_on ‘h = h'’ >> gvs[]
QED

(* -------------------------------------------------------------------------- *)
(* Initially I thought that the hamming distance between two points precisely *)
(* satisfied the triangle equality if and only if the middle point was one    *)
(* of the endpoints, but this is not necessarily the case.                    *)
(*                                                                            *)
(* hamming (0, 1) (1, 0) = 2                                                  *)
(* hamming (0, 1) (0, 0) + hamming (0, 0) (1, 0) = 1 + 1 = 2                  *)
(* -------------------------------------------------------------------------- *)
Theorem hamming_distance_triangle_inequality:
  ∀bs cs ds.
    (LENGTH bs = LENGTH cs ∧ LENGTH cs = LENGTH ds) ⇒
    hamming_distance bs ds ≤ hamming_distance bs cs + hamming_distance cs ds
Proof
  rpt strip_tac
  >> ‘∀bs ds. LENGTH bs = LENGTH cs ∧ LENGTH cs = LENGTH ds ⇒ hamming_distance bs ds ≤ hamming_distance bs cs + hamming_distance cs ds’ suffices_by gvs[]
  >> rpt $ pop_assum kall_tac
  >> Induct_on ‘cs’ >> rpt strip_tac >> Cases_on ‘bs’ >> Cases_on ‘ds’ >> gvs[]
  >> first_x_assum $ qspecl_then [‘t’, ‘t'’] assume_tac
  >> Cases_on ‘h = h''’ >> Cases_on ‘h' = h’ >> Cases_on ‘h' = h''’ >> gvs[]
QED

Theorem hamming_distance_bnot[simp]:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    hamming_distance (bnot bs) (bnot cs) = hamming_distance bs cs
Proof
  Induct_on ‘bs’ >> Cases_on ‘cs’ >> gvs[]
  >> rpt strip_tac
  >> last_x_assum $ qspec_then ‘t’ assume_tac
  >> pop_assum (drule_then assume_tac)
  >> simp[bnot_cons, hamming_distance_cons]
QED

Theorem hamming_distance_bnot_1[simp]:
  ∀bs.
    hamming_distance (bnot bs) bs = LENGTH bs
Proof
  Induct_on ‘bs’
  >- simp[]
  >> gen_tac
  >> simp[bnot_cons]
QED

Theorem hamming_distance_bnot_2[simp]:
  ∀bs.
    hamming_distance bs (bnot bs) = LENGTH bs
Proof
  metis_tac[hamming_distance_symmetric, hamming_distance_bnot_1]
QED

(* -------------------------------------------------------------------------- *)
(* Unit tests                                                                 *)
(* -------------------------------------------------------------------------- *)

Theorem hamming_distance_test:
  hamming_distance [F; T; T; F; T; F; F] [T; T; F; F; T; T; F] = 3 ∧
  hamming_distance [F; F; F] [T; T; T] = 3 ∧
  hamming_distance [F; T; F; T; F] [F; T; F; T; F] = 0
Proof
  EVAL_TAC
QED
