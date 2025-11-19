Theory fundamental

Ancestors arithmetic bitstring pair pred_set probability extreal finite_map fsgraph genericGraph real rich_list sigma_algebra lebesgue list martingale measure topology

Libs donotexpandLib useful_tacticsLib realLib dep_rewrite ConseqConv;

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

(* Similar to CARD_PSUBSET *)
Theorem order_psubset:
  ∀g1 : fsgraph g2 : fsgraph.
    nodes g1 ⊂ nodes g2 ⇒ order g1 < order g2
Proof
  rpt strip_tac
  >> gvs[gsize_def]
  >> gvs[CARD_PSUBSET]
QED

Theorem ALL_DISTINCT_PREFIX:
  ∀ls1 ls2.
    ls1 ≼ ls2 ∧
    ALL_DISTINCT ls2 ⇒
    ALL_DISTINCT ls1
Proof
  rpt strip_tac
  >> metis_tac[ALL_DISTINCT_TAKE, IS_PREFIX_EQ_TAKE']
QED

Theorem prefix_mem:
  ∀vs1 vs2 v.
    vs1 ≼ vs2 ∧
    MEM v vs1 ⇒
    MEM v vs2
Proof
  Induct_on ‘vs1’ >> gvs[]
  >> rpt gen_tac
  >> disch_tac
  >> Cases_on ‘vs2’ >> gvs[]
QED

Theorem adjacent_prefix:
  ∀vs1 vs2 v1 v2.
    vs1 ≼ vs2 ∧
    adjacent vs1 v1 v2 ⇒
    adjacent vs2 v1 v2
Proof
  Induct_on ‘vs2’ >> gvs[] >> rpt strip_tac
  >> namedCases_on ‘vs1’ ["", "v vs1"] >> gvs[]
  >> namedCases_on ‘vs2’ ["", "v vs2"] >> gvs[]
  >> gvs[adjacent_iff]
  >> Cases_on ‘h = v1 ∧ v = v2’ >> gvs[]
  >> disj2_tac
  >> last_x_assum irule
  >> qexists ‘vs1'’
  >> gvs[]
  >> namedCases_on ‘vs1'’ ["", "v vs1"] >> gvs[]
  >> gvs[adjacent_iff]
QED

Theorem walk_subwalk_prefix:
  ∀g vs1 vs2.
    vs1 ≠ [] ∧
    vs1 ≼ vs2 ∧
    walk g vs2 ⇒
    walk g vs1
Proof
  rpt strip_tac
  >> gvs[walk_def]
  >> Cases_on ‘vs1’ >> gvs[]
  >> Cases_on ‘vs2’ >> gvs[]
  >> conj_tac
  >- (rpt strip_tac
      >- metis_tac[]
      >> metis_tac[prefix_mem]
     )
  >> rpt strip_tac
  >> first_x_assum irule
  >> irule adjacent_prefix
  >> qexists ‘h::t’
  >> gvs[]
QED

Theorem path_subpath_prefix:
  ∀g vs1 vs2.
    vs1 ≠ [] ∧
    vs1 ≼ vs2 ∧
    path g vs2 ⇒
    path g vs1
Proof
  rpt strip_tac
  >> gvs[path_def]
  >> conj_tac
  >- metis_tac[walk_subwalk_prefix]
  >> metis_tac[ALL_DISTINCT_PREFIX]
QED

Theorem TAKE_IS_PREFIX[simp]:
  ∀n ls.
    TAKE n ls ≼ ls
Proof
  rpt strip_tac
  >> metis_tac[IS_PREFIX_EQ_TAKE']
QED

Theorem path_take[simp]:
  ∀g vs i.
    i ≠ 0 ∧
    path g vs ⇒
    path g (TAKE i vs)
Proof
  rpt strip_tac
  >> irule path_subpath_prefix
  >> Cases_on ‘i’ >> Cases_on ‘vs’ >> gvs[]
  >- gvs[path_def, walk_def]
  >> qexists ‘h::t’ >> gvs[]
QED

Theorem LAST_TAKE:
  ∀i ls.
    i ≠ 0 ∧
    i ≤ LENGTH ls ⇒
    LAST (TAKE i ls) = EL (i - 1) ls
Proof
  Induct_on ‘ls’ >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘i’ >> gvs[]
  >> Cases_on ‘n’ >> gvs[]
  >> Cases_on ‘ls’ >> gvs[]
  >> last_x_assum $ qspecl_then [‘n' + 1’] assume_tac
  >> gvs[]
QED


Theorem walk_empty_not[simp]:
  ∀g.
    walk g [] ⇔ F
Proof
  gvs[walk_def]
QED

Theorem path_empty_not[simp]:
  ∀g.
    path g [] ⇔ F
Proof
  gvs[path_def]
QED

Theorem walk_cons:
  ∀g v vs.
    walk g (v::vs) ⇔ (vs = [] ∧ v ∈ nodes g ∨
                      walk g vs ∧ adjacent g v (HD vs))
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (Cases_on ‘vs’ >> gvs[]
      >> rw[] >> gvs[walk_def]
      >> conj_tac
      >- metis_tac[]
      >> rw[]
      >> gvs[adjacent_rules]
     )
  >> rw[] >> gvs[walk_def]
  >> conj_tac
  >- (REVERSE $ rpt strip_tac
      >- simp[]
      >> gvs[]
      >> metis_tac[adjacent_members]
     )
  >> rpt strip_tac
  >> namedCases_on ‘vs’ ["", "v' vs"] >> gvs[]
  >> gvs[adjacent_iff]
QED

Theorem path_cons:
  ∀g v vs.
    path g (v::vs) ⇔ (vs = [] ∧ v ∈ nodes g ∨
                      path g vs ∧ adjacent g v (HD vs) ∧ ¬MEM v vs)
Proof
  rpt strip_tac
  >> gvs[path_def]
  >> gvs[walk_cons]
  >> EQ_TAC >> rw[] >> gvs[]
QED

Theorem not_all_distinct_last[simp]:
  ∀v vs.
    ALL_DISTINCT (LAST (v::vs)::(v::vs)) ⇔ F
Proof
  rpt strip_tac
  >> gvs[]
  >> metis_tac[MEM_LAST, MEM]
QED

Theorem not_path_last[simp]:
  ∀g v vs.
    path g ((LAST (v::vs))::(v::vs)) ⇔ F
Proof
  rpt strip_tac
  >> gvs[path_def, Excl "ALL_DISTINCT"]
QED

Theorem walk_append:
  ∀g ls1 ls2.
    ls1 ≠ [] ∧ ls2 ≠ [] ⇒
    (walk g (ls1 ++ ls2) ⇔
       (walk g ls1 ∧ walk g ls2 ∧ adjacent g (LAST ls1) (HD ls2))
    )
Proof
  Induct_on ‘ls1’ >> gvs[]
  >> rpt strip_tac
  >> gvs[walk_cons]
  >> namedCases_on ‘ls1’ ["", "l ls1"] >> gvs[]
  >- metis_tac[adjacent_members]
  >> metis_tac[]
QED

Theorem walk_drop:
  ∀g n ls.
    n ≤ LENGTH ls - 1 ∧
    walk g ls ⇒
    walk g (DROP n ls)
Proof
  Induct_on ‘n’ >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘ls’ >> gvs[]
  >> last_x_assum irule
  >> gvs[ADD1]
  >> gvs[walk_cons]
QED

Theorem walk_take:
  ∀g n ls.
    1 ≤ n ∧
    walk g ls ⇒
    walk g (TAKE n ls)
Proof
  Induct_on ‘n’ >> gvs[]
  >> Cases_on ‘ls’ >> gvs[]
  >> rpt strip_tac
  >> gvs[walk_cons]
  >> Cases_on ‘(n = 0 ∨ t = []) ∧ h ∈ nodes g’ >> gvs[]
  >- gvs[HD_TAKE]
  >> REVERSE conj_tac
  >- (Cases_on ‘n’ >> Cases_on ‘t’ >> gvs[HD_TAKE]
      >> metis_tac[adjacent_members]
     )
  >> last_x_assum irule
  >> gvs[]
  >> Cases_on ‘n’ >> gvs[]
  >> metis_tac[adjacent_members]
QED

