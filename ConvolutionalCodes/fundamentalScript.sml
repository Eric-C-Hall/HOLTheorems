Theory fundamental

Ancestors arithmetic bitstring pair pred_set probability extreal real rich_list sigma_algebra lebesgue list martingale measure topology

Libs extreal_to_realLib donotexpandLib useful_tacticsLib realLib dep_rewrite ConseqConv;

(* -------------------------------------------------------------------------- *)
(* TAKE-ing can only decrease lengths                                         *)
(* -------------------------------------------------------------------------- *)
Theorem EQ_TAKE_LENGTH_IMP_LENGTH_LEQ:
  ∀k l1 l2.
    l2 = TAKE k l1 ⇒ LENGTH l2 ≤ LENGTH l1
Proof
  rpt strip_tac
  >> gvs[]
  >> gvs[LENGTH_TAKE_EQ]
QED

(* -------------------------------------------------------------------------- *)
(* This is probably simply a better theorem than IS_PREFIX_EQ_TAKE, because   *)
(* it avoids the existential quantifier                                       *)
(* -------------------------------------------------------------------------- *)
Theorem IS_PREFIX_EQ_TAKE_2:
  ∀l l1.
    l1 ≼ l ⇔
      l1 = TAKE (LENGTH l1) l
Proof
  rpt strip_tac
  >> gvs[IS_PREFIX_EQ_TAKE]
  >> EQ_TAC
  >- (rpt strip_tac >> gvs[LENGTH_TAKE_EQ])
  >> rpt strip_tac
  >> qexists ‘LENGTH l1’
  >> gvs[]
  >> metis_tac[EQ_TAKE_LENGTH_IMP_LENGTH_LEQ]
QED

Theorem bitwise_append:
  ∀f bs1 bs2 cs1 cs2.
    LENGTH bs1 = LENGTH bs2 ∧
    LENGTH cs1 = LENGTH cs2 ⇒
    bitwise f (bs1 ++ cs1) (bs2 ++ cs2) = bitwise f bs1 bs2 ++ bitwise f cs1 cs2
Proof
  rpt strip_tac
  >> gvs[bitwise_def]
  >> gvs[GSYM ZIP_APPEND, MAP_APPEND]
QED

Theorem bxor_append:
  ∀bs1 bs2 cs1 cs2.
    LENGTH bs1 = LENGTH bs2 ∧
    LENGTH cs1 = LENGTH cs2 ⇒
    bxor (bs1 ++ cs1) (bs2 ++ cs2) = bxor bs1 bs2 ++ bxor cs1 cs2
Proof
  gvs[bxor_def, bitwise_append]
QED
