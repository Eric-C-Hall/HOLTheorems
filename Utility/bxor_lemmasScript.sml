Theory bxor_lemmas

Ancestors arithmetic bitstring list rich_list

Libs dep_rewrite realLib;

(* -------------------------------------------------------------------------- *)
(* Theorems regarding bxor, bitwise, bnot, extend, and fixwidth               *)
(*                                                                            *)
(* Also NOT_IFF_INV and NOT_IFF                                               *)
(* -------------------------------------------------------------------------- *)

(* Provide a nicer interpretation of bitwise than its original definition *)
Theorem bitwise_el:
  ∀f bs cs x.
    LENGTH bs = LENGTH cs ∧ x < LENGTH bs ⇒
    ((EL x (bitwise f bs cs)) ⇔ f (EL x bs) (EL x cs))
Proof
  rpt strip_tac
  >> gvs[bitwise_def, EL_MAP, EL_ZIP]
QED

Theorem bitwise_length:
  ∀f bs cs.
    LENGTH (bitwise f bs cs) = MAX (LENGTH bs) (LENGTH cs)
Proof
  simp[bitwise_def]
QED

Theorem bitwise_eq:
  ∀f bs cs ds.
    LENGTH bs = LENGTH cs ∧ LENGTH cs = LENGTH ds ⇒
    (bitwise f bs cs = ds ⇔ (∀x. x < LENGTH bs ⇒ f (EL x bs) (EL x cs) = EL x ds))
Proof
  rpt strip_tac
  >> EQ_TAC >> rpt strip_tac >> gvs[]
  >- (irule EQ_SYM
      >> irule bitwise_el
      >> gvs[])
  >> irule $ iffRL LIST_EQ_REWRITE
  >> REVERSE conj_tac
  >> gvs[bitwise_length]
  >> rpt strip_tac
  >> first_x_assum $ qspec_then ‘x’ (fn th => gvs[GSYM th])
  >> irule bitwise_el
  >> gvs[]
QED

Theorem NOT_IFF_INV[simp]:
  ∀b c.
    (b ⇎ (b ⇎ c)) ⇔ c
Proof
  rpt strip_tac
  >> Cases_on ‘b’ >> gvs[]
QED

Theorem bxor_inv:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    bxor bs (bxor bs cs) = cs
Proof
  rpt strip_tac
  >> gvs[bxor_def]
  >> irule $ iffRL bitwise_eq
  >> gvs[bitwise_length]
  >> rpt strip_tac
  >> DEP_PURE_ONCE_REWRITE_TAC [bitwise_el]
  >> simp[]
QED

Theorem bxor_length:
  ∀bs cs.
    LENGTH (bxor bs cs) = MAX (LENGTH bs) (LENGTH cs)
Proof
  simp[bxor_def, bitwise_length]
QED

Theorem bxor_cons[simp]:
  ∀b bs c cs.
    LENGTH bs = LENGTH cs ⇒
    bxor (b::bs) (c::cs) = (b ⇎ c)::(bxor bs cs)
Proof
  simp[bxor_def, bitwise_def]
QED

Theorem bitwise_fixwidth:
  ∀f bs cs.
    bitwise f bs cs =
    bitwise f
            (fixwidth (MAX (LENGTH bs) (LENGTH cs)) bs)
            (fixwidth (MAX (LENGTH bs) (LENGTH cs)) cs)
Proof
  rw[]
  >> gvs[bitwise_def]
QED

Theorem bxor_fixwidth:
  ∀bs cs.
    bxor bs cs =
    bxor (fixwidth (MAX (LENGTH bs) (LENGTH cs)) bs)
         (fixwidth (MAX (LENGTH bs) (LENGTH cs)) cs)
Proof
  gvs[bxor_def, GSYM bitwise_fixwidth]
QED

Theorem bitwise_cons[simp]:
  ∀f b bs c cs.
    LENGTH bs = LENGTH cs ⇒
    bitwise f (b::bs) (c::cs) = (f b c)::(bitwise f bs cs)
Proof
  gvs[bitwise_def]
QED

(* A helper function to solve bitwise_comm, for the special case of same-length
   inputs *)
Theorem bitwise_comm_same_length[local]:
  ∀f bs cs.
    (∀x y. f x y = f y x) ∧
    LENGTH bs = LENGTH cs ⇒
    bitwise f bs cs = bitwise f cs bs
Proof
  Induct_on ‘bs’ >> Cases_on ‘cs’ >> rw[]
  >> last_x_assum irule >> simp[]
QED

Theorem bitwise_comm:
  ∀f bs cs.
    (∀x y. f x y = f y x) ⇒
    bitwise f bs cs = bitwise f cs bs
Proof
  rw[]
  >> PURE_ONCE_REWRITE_TAC[bitwise_fixwidth]
  >> gvs[bitwise_comm_same_length, length_fixwidth, MAX_COMM]
QED

Theorem bxor_comm:
  ∀bs cs.
    bxor bs cs = bxor cs bs
Proof
  rw[bxor_def]
  >> DEP_PURE_ONCE_REWRITE_TAC[bitwise_comm]
  >> rw[]
  >> metis_tac[]
QED

Theorem bnot_length[simp]:
  ∀bs.
    LENGTH (bnot bs) = LENGTH bs
Proof
  rpt strip_tac
  >> Induct_on ‘bs’ >> gvs[bnot_def]
QED

Theorem bnot_bxor_1:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    bnot (bxor bs cs) = bxor (bnot bs) cs
Proof
  strip_tac
  >> Induct_on ‘bs’
  >> gvs[bnot_def, bxor_def, bitwise_def]
  >> rpt strip_tac
  >> gvs[bnot_def]
  >> Cases_on ‘cs’ >> gvs[]
  >> Cases_on ‘h’ >> Cases_on ‘h'’ >> gvs[]
QED

Theorem bnot_bxor_2:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    bnot (bxor bs cs) = bxor bs (bnot cs)
Proof
  rpt strip_tac
  >> qspecl_then [‘bs’, ‘bnot cs’] assume_tac bxor_comm
  >> gvs[]
  >> DEP_PURE_ONCE_REWRITE_TAC[bxor_comm]
  >> gvs[bnot_bxor_1]
QED

Theorem bxor_empty[simp]:
  bxor [] [] = []
Proof
  EVAL_TAC
QED

Theorem bitwise_empty[simp]:
  ∀f bs cs.
    bitwise f [] [] = []
Proof
  EVAL_TAC >> simp[]
QED

Theorem bxor_replicate_f_left_same_width:
  ∀bs n.
    LENGTH bs = n ⇒
    bxor (REPLICATE n F) bs = bs
Proof
  Induct_on ‘n’ >> Cases_on ‘bs’ >> rw[]
QED

Theorem extend_append:
  ∀n v bs.
    extend v n bs = REPLICATE n v ++ bs
Proof
  Induct_on ‘n’ >> rw[] >> gvs[extend_def]
  >> gvs[GSYM SNOC_APPEND]
QED

Theorem extend_snoc:
  ∀v n b bs.
    extend v n (SNOC b bs) = SNOC b (extend v n bs)
Proof
  rw[]
  >> gvs[extend_append]
QED

Theorem fixwidth_empty:
  ∀n.
    fixwidth n [] = REPLICATE n F
Proof
  Induct_on ‘n’ >> rw[]
  >> gvs[fixwidth]
  >> pop_assum mp_tac >> rw[] >> gvs[NOT_LT_ZERO_EQ_ZERO, extend_def]
  >> qsuff_tac ‘extend F n [F] = SNOC F (extend F n []) ∧
                F::REPLICATE n F = SNOC F (REPLICATE n F)’
  >- simp[]
  >> REVERSE conj_tac >- gvs[]
  >> PURE_REWRITE_TAC[GSYM extend_snoc]
  >> gvs[]
QED

Theorem bitwise_empty_left:
  ∀f bs.
    bitwise f [] bs = bitwise f (REPLICATE (LENGTH bs) F) bs
Proof
  rw[]
  >> PURE_ONCE_REWRITE_TAC[bitwise_fixwidth]
  >> gvs[]
  >> gvs[fixwidth_empty]
QED

Theorem bitwise_empty_right:
  ∀f bs.
    bitwise f bs [] = bitwise f bs (REPLICATE (LENGTH bs) F)
Proof
  rw[]
  >> PURE_ONCE_REWRITE_TAC[bitwise_fixwidth]
  >> gvs[]
  >> gvs[fixwidth_empty]
QED

Theorem bxor_empty_left[simp]:
  ∀bs.
    bxor [] bs = bs
Proof
  rw[]
  >> PURE_ONCE_REWRITE_TAC[bxor_fixwidth]
  >> gvs[]
  >> gvs[fixwidth_empty]
  >> gvs[bxor_replicate_f_left_same_width]
QED

Theorem bxor_empty_right[simp]:
  ∀bs.
    bxor bs [] = bs
Proof
  metis_tac[bxor_empty_left, bxor_comm]
QED

Theorem take_bxor:
  ∀n bs cs.
    LENGTH bs = LENGTH cs ⇒
    TAKE n (bxor bs cs) = bxor (TAKE n bs) (TAKE n cs)
Proof
  Induct_on ‘n’ >> rw[]
  >> Cases_on ‘bxor bs cs’ >> gvs[TAKE]
  >- (Cases_on ‘bs’ >> Cases_on ‘cs’ >> gvs[bxor_def])
  >> Cases_on ‘bs’ >> Cases_on ‘cs’ >> gvs[]
  >> DEP_PURE_ONCE_REWRITE_TAC[bxor_cons]
  >> gvs[]
  >> gvs[LENGTH_TAKE_EQ]
QED

Theorem bnot_cons[simp]:
  ∀b bs.
    bnot (b::bs) = (¬b)::(bnot bs)
Proof
  gvs[bnot_def]
QED

Theorem bnot_empty[simp]:
  bnot [] = []
Proof
  EVAL_TAC
QED

Theorem bnot_append[simp]:
  ∀bs cs.
    bnot (bs ⧺ cs) = bnot bs ⧺ bnot cs
Proof
  Induct_on ‘bs’ >> gvs[]
QED

Theorem NOT_IFF[simp]:
  ∀b. (¬b ⇔ b) ⇔ F
Proof
  Cases_on ‘b’ >> gvs[]
QED

Theorem drop_bxor:
  ∀n bs cs.
    LENGTH bs = LENGTH cs ⇒
    DROP n (bxor bs cs) = bxor (DROP n bs) (DROP n cs)
Proof
  Induct_on ‘n’ >> rpt strip_tac >> gvs[DROP]
  >> Cases_on ‘bs’ >> Cases_on ‘cs’ >> gvs[]
QED

Theorem el_drop_hd:
  ∀i bs.
    i < LENGTH bs ⇒
    EL i bs = HD (DROP i bs)
Proof
  Induct_on ‘i’ >> rpt strip_tac >> gvs[]
  >> Cases_on ‘bs’ >> gvs[]
QED

Theorem hd_bxor:
  ∀bs cs.
    LENGTH bs = LENGTH cs ∧
    bs ≠ [] ⇒
    HD (bxor bs cs) = (HD bs ⇎ HD cs)
Proof
  rpt strip_tac
  >> Cases_on ‘bs’ >> Cases_on ‘cs’ >> gvs[]
QED

Theorem el_bxor:
  ∀i bs cs.
    LENGTH bs = LENGTH cs ∧
    i < LENGTH bs ⇒
    EL i (bxor bs cs) = (EL i bs ⇎ EL i cs)
Proof
  rpt strip_tac
  >> gvs[el_drop_hd, bxor_length, drop_bxor, hd_bxor]
QED
