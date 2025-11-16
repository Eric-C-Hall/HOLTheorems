Theory fundamental

Ancestors arithmetic bitstring pair pred_set probability extreal finite_map real rich_list sigma_algebra lebesgue list martingale measure topology

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

Theorem BIGUNION_IMAGE_INTER:
  ∀S1 S2 F.
    BIGUNION (IMAGE (λx. S1 ∩ F x) S2) = S1 ∩ BIGUNION (IMAGE (λx. F x) S2)
Proof
  rpt strip_tac
  >> simp[EXTENSION, Excl "IN_BIGUNION"]
  >> rpt strip_tac
  >> EQ_TAC
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >> rpt strip_tac
  >> gvs[]
  >> qexists ‘S1 ∩ F' x'’
  >> conj_tac >- simp[]
  >> qexists ‘x'’ >> simp[]
QED

Theorem IMAGE_CHANGE_FUN:
  ∀f g S.
    (∀x. x ∈ S ⇒ f x = g x) ⇒
    IMAGE f S = IMAGE g S
Proof
  rpt strip_tac
  >> ASM_SET_TAC[]
QED

Theorem FUN_FMAP_EQ_THM:
  ∀f g S.
    FINITE S ⇒
    (FUN_FMAP f S = FUN_FMAP g S ⇔ (∀x. x ∈ S ⇒ f x = g x))
Proof
  rpt strip_tac
  >> EQ_TAC >> rpt strip_tac
  >- (qpat_x_assum ‘FUN_FMAP f S' = FUN_FMAP g S'’ (fn th => assume_tac (Q.AP_TERM ‘λf. f ' x’ th)) >> gvs[]
      >> gvs[FUN_FMAP_DEF]
     )
  >> irule (iffLR fmap_EQ_THM)
  >> rpt strip_tac >> gvs[]
  >> gvs[FUN_FMAP_DEF]
QED

Theorem fmap_EQ_THM_ALT:
  ∀f g.
    f = g ⇔ (∀x. x ∈ FDOM f ⇔ x ∈ FDOM g ∧ (x ∈ FDOM f ⇒ f ' x = g ' x))
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (rpt strip_tac >> gvs[GSYM fmap_EQ_THM])
  >> rpt strip_tac
  >> gvs[GSYM fmap_EQ_THM]
  >> gvs[EXTENSION]
  >> metis_tac[]
QED

Theorem FDOM_DRESTRICT_SUBSET[simp]:
  ∀f S.
    FDOM (DRESTRICT f S) ⊆ S
Proof
  rpt strip_tac
  >> gvs[FDOM_DRESTRICT]
QED
