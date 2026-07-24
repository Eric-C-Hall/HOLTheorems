(* -------------------------------------------------------------------------- *)
(* Written by Jared Yeager                                                    *)
(* Edits and additions by Eric Hall                                           *)
(* -------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;
open simpLib;
open markerTheory;
open combinTheory;
open pairTheory;
open pred_setTheory;
open arithmeticTheory;
open listTheory;
open realTheory;
open realLib;
open limTheory;
open seqTheory;
open transcTheory;
open real_sigmaTheory;
open extrealTheory;
open sigma_algebraTheory;
open measureTheory;
open borelTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;

open fundamentalTheory;

open ConseqConv;

val _ = new_theory "jared_yeager_prod_list";

val _ = reveal "C";

(***** Crosses *****)

(*
Definition LIST_CROSS_DEF:
    LIST_CROSS = LIST_REL LET
End

Theorem LIST_CROSS_ALT_REC:
    ([] ∈ LIST_CROSS []) ∧
    (∀h t. (h::t) ∉ LIST_CROSS []) ∧
    (∀sh st. [] ∉ LIST_CROSS (sh::st)) ∧
    (∀h t sh st. (h::t) ∈ LIST_CROSS (sh::st) ⇔ h ∈ sh ∧ t ∈ LIST_CROSS st)
Proof
    simp[IN_APP,LIST_CROSS_DEF,LIST_REL_def]
QED

Theorem LIST_CROSS_ALT:
    ∀l sl. l ∈ LIST_CROSS sl ⇔ LENGTH sl = LENGTH l ∧ ∀i. i < LENGTH l ⇒ EL i l ∈ EL i sl
Proof
    csimp[IN_APP,LIST_CROSS_DEF,LIST_REL_EL_EQN]
QED

Definition LIST_PROD_SETS_DEF:
    LIST_PROD_SETS = IMAGE LIST_CROSS ∘ LIST_CROSS
End
*)

(***** Sigma Algebra *****)

(*
Definition list_sig_alg_def:
    list_sig_alg sal = sigma (LIST_CROSS (MAP space sal)) (LIST_PROD_SETS (MAP subsets sal))
End

Theorem sigma_algebra_list_sig_alg:
    ∀sal. EVERY sigma_algebra sal ⇒ sigma_algebra (list_sig_alg sal)
Proof
    rw[list_sig_alg_def] >> irule SIGMA_ALGEBRA_SIGMA >>
    simp[subset_class_def] >> qx_gen_tac ‘ls’ >>
    simp[LIST_PROD_SETS_DEF,LIST_CROSS_ALT,SUBSET_DEF,PULL_EXISTS] >>
    qx_gen_tac ‘sl’ >> strip_tac >>
    qx_gen_tac ‘l’ >> rw[] >> gs[EL_MAP] >>
    ntac 2 $ first_x_assum $ drule_then assume_tac >>
    irule SIGMA_ALGEBRA_IN_SPACE >> gs[EVERY_EL] >>
    qexists ‘EL i sl’ >> simp[]
QED
*)

(***** Measure Space *****)

(*
Definition list_measure_rec_lex_def:
    list_measure_rec_lex (INL l) = (LENGTH l,0) ∧
    list_measure_rec_lex (INR l) = (LENGTH l,SUC 0)
End

Definition list_measure_rec_def[local]:
    list_measure [] = C 𝟙 [] ∧
    list_measure (mh::mt) = (λls. ∫⁺ mh (λh. ∫⁺ (list_measure_space mt) (λt. 𝟙 ls (h::t)))) ∧
    list_measure_space ml =
        (LIST_CROSS (MAP m_space ml),subsets (list_sig_alg (MAP measurable_space ml)),list_measure ml)
Termination
    WF_REL_TAC `inv_image ($< LEX $<) list_measure_rec_lex` >> simp[list_measure_rec_lex_def]
End

Theorem list_measure_def:
    list_measure ([]: α m_space list) = C 𝟙 [] ∧
    ∀(mh: α m_space) mt. list_measure (mh::mt) = (λls. ∫⁺ mh (λh. ∫⁺ (list_measure_space mt) (λt. 𝟙 ls (h::t))))
Proof
    simp[list_measure_rec_def]
QED

Theorem list_measure_space_def:
    ∀ml. list_measure_space ml =
        (LIST_CROSS (MAP m_space ml),subsets (list_sig_alg (MAP measurable_space ml)),list_measure ml)
Proof
    simp[list_measure_rec_def]
QED
*)

(***** Hold on, Martingale has MACHINERY *****)

(* Should be canon *)
Theorem pos_fn_integral_cmul_indicator_general:
    ∀m s c. measure_space m ∧ s ∈ measurable_sets m ∧ 0 ≤ c ⇒
       ∫⁺ m (λx. c * 𝟙 s x) = c * measure m s
Proof
    rw[] >>
    resolve_then Any irule pos_fn_integral_cmul_general EQ_TRANS >>
    irule_at Any IN_MEASURABLE_BOREL_INDICATOR >> simp[INDICATOR_FN_POS] >>
    first_assum $ irule_at Any >> simp[pos_fn_integral_indicator]
QED

(* Should be canon *)
Theorem general_prod_measure_rect:
    ∀cons car cdr m1 m2 A B. pair_operation cons car cdr ∧
        measure_space m1 ∧ measure_space m2 ∧
        A ∈ measurable_sets m1 ∧ B ∈ measurable_sets m2 ⇒
        general_prod_measure cons m1 m2 (general_cross cons A B) = measure m1 A * measure m2 B
Proof
    rw[general_prod_measure_def] >>
    drule_then (simp o single) indicator_fn_general_cross >>
    resolve_then Any irule pos_fn_integral_cmul_indicator_general EQ_TRANS >>
    simp[MEASURE_POSITIVE] >>
    irule pos_fn_integral_cong >>
    dsimp[] >> simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
    qx_gen_tac ‘y’ >> strip_tac >>
    irule_at Any pos_fn_integral_pos >>
    simp[le_mul,MEASURE_POSITIVE,INDICATOR_FN_POS] >>
    qspec_then ‘𝟙 B y’ (mp_tac) (GSYM mul_comm) >> disch_then $ simp o single >>
    irule pos_fn_integral_cmul_indicator_general >>
    simp[INDICATOR_FN_POS]
QED

(* Maybe should be canon *)
Theorem SUBSET_LE:
    ∀f i j. (∀n. f n ⊆ f (SUC n)) ∧ i ≤ j ⇒ f i ⊆ f j
Proof
    rw[] >> ‘j = i + (j - i)’ by simp[] >>
    pop_assum SUBST1_TAC >> irule SUBSET_ADD >> simp[]
QED

(*
HAVE: measure_space_general_prod_measure
*)
(* Should be canon *)
Theorem sigma_finite_measure_space_general_prod_measure:
    ∀(cons: α -> β -> γ) car cdr m1 m2. pair_operation cons car cdr ∧
        sigma_finite_measure_space m1 ∧ sigma_finite_measure_space m2 ⇒
        sigma_finite_measure_space (general_prod_measure_space cons m1 m2)
Proof
    rw[] >> simp[sigma_finite_measure_space_def] >>
    irule_at Any measure_space_general_prod_measure >> simp[] >>
    first_assum $ irule_at Any >>
    gs[sigma_finite_measure_space_def,sigma_finite_def] >>
    rename [‘(general_prod_measure_space _ m1 m2)’,‘∀n. measure m1 (f n) < +∞’,‘∀n. measure m2 (g n) < +∞’] >>
    gs[FUNSET] >> simp[general_prod_measure_space_def,GSYM general_prod_measure_def] >>
    qexists_tac ‘λn. general_cross cons (f n) (g n)’ >>
    simp[general_prod_measure_rect,SF SFY_ss] >> rw[]
    >- (simp[general_sigma_def] >> irule IN_SIGMA >>
        simp[general_prod_def] >> irule_at Any EQ_REFL >> simp[])
    >- (gs[SUBSET_DEF,IN_general_cross,PULL_EXISTS] >>
        rw[] >> irule_at Any EQ_REFL >> simp[])
    >- (gs[EXTENSION,IN_BIGUNION_IMAGE] >>
        ntac 2 $ qpat_x_assum ‘∀x. _ ⇔ _ ∈ _’ $ assume_tac o GSYM >>
        rw[EQ_IMP_THM,general_cross_def] >> irule_at Any EQ_REFL
        >- (ntac 2 $ pop_assum $ irule_at Any) >>
        rename [‘∃n. a ∈ f n ∧ b ∈ g n’,‘a ∈ f m’,‘b ∈ g n’] >>
        qexists_tac ‘MAX m n’ >> ntac 2 $ dxrule_then assume_tac SUBSET_LE >>
        gs[SUBSET_DEF] >> ntac 4 $ pop_assum $ irule_at Any >>
        simp[])
    >- (ntac 2 $ qpat_x_assum ‘∀n. _ < +∞’ $ qspec_then ‘n’ mp_tac >>
        map_every (fn tms => qspecl_then tms mp_tac MEASURE_POSITIVE) [[‘m1’,‘f n’],[‘m2’,‘g n’]] >>
        simp[GSYM normal_0] >>
        Cases_on ‘measure m1 (f n)’ >> simp[extreal_le_simps,extreal_lt_simps] >>
        Cases_on ‘measure m2 (g n)’ >> simp[extreal_le_simps,extreal_lt_simps] >>
        simp[extreal_mul_def,extreal_lt_simps])
QED

(* -------------------------------------------------------------------------- *)
(* TODO: The name fails to mention that we are taking the product of          *)
(* probability spaces. This name could refer to any product over a list, e.g. *)
(* a product of sets, sigma algebras, or numbers                              *)
(* -------------------------------------------------------------------------- *)
Definition prod_list_def:
  prod_list [] = ({[]}, POW {[]}, C 𝟙 []) ∧
  prod_list (mh::mt) = general_prod_measure_space CONS mh (prod_list mt)
End

(* -------------------------------------------------------------------------- *)
(* Input: list of sets                                                        *)
(* Output: cross product of each set, represented as a list where the ith     *)
(*         element is an element from the ith set                             *)
(* TODO: Don't you think general_cross should be instead called general_cart? *)
(*       it's a cartesian product, not a cross product. Also find naming of   *)
(*       general_sigma a bit dubious.                                         *)
(* -------------------------------------------------------------------------- *)
Definition cross_list_def:
  cross_list [] = {[]} ∧
  cross_list (h::t) = general_cross CONS h (cross_list t)
End

(* -------------------------------------------------------------------------- *)
(* Input: list of sigma algebras                                              *)
(* Output: product sigma algebra, where the underlying spaces are combined    *)
(*         using cross_list                                                   *)
(* -------------------------------------------------------------------------- *)
Definition sigma_list_def:
  sigma_list [] = ({[]}, {{}; {[]}}) ∧
  sigma_list (h::t) = general_sigma CONS h (sigma_list t)
End

Theorem sigma_finite_measure_space_dirac_measure:
    ∀sa x. sigma_algebra sa ⇒ sigma_finite_measure_space (space sa,subsets sa,C 𝟙 x)
Proof
    rw[sigma_finite_measure_space_def,measure_space_dirac_measure,sigma_finite_def] >>
    qexists ‘K (space sa)’ >> simp[FUNSET,SIGMA_ALGEBRA_SPACE] >>
    reverse conj_tac >- (rw[indicator_fn_def]) >>
    rw[EXTENSION,IN_BIGUNION_IMAGE]
QED

Theorem sigma_finite_measure_space_prod_list:
  ∀ml. EVERY sigma_finite_measure_space ml ⇒ sigma_finite_measure_space (prod_list ml)
Proof
    Induct_on ‘ml’
    >- (rw[EVERY_DEF,prod_list_def] >>
        qspec_then ‘{[]}’ assume_tac POW_SIGMA_ALGEBRA >>
        dxrule sigma_finite_measure_space_dirac_measure >> simp[]) >>
    rw[EVERY_DEF,prod_list_def] >> rename [‘_ CONS mh (_ mt)’] >>
    irule sigma_finite_measure_space_general_prod_measure >> gs[] >>
    irule_at Any pair_operation_CONS
QED

Theorem prob_space_dirac_measure:
  ∀sa x.
    sigma_algebra sa ∧
    x ∈ space sa ⇒
    prob_space (space sa,subsets sa,C 𝟙 x)
Proof
  rpt gen_tac >> strip_tac
  >> simp[prob_space_def]
  >> simp[measure_space_dirac_measure]
  >> simp[indicator_fn_def]
QED

(* TODO: Add this to canon
   Edit: apparently this may already be somewhere in HOL4-Theorem-Library? *)
Theorem prob_space_sigma_finite_measure_space:
  ∀p.
    prob_space p ⇒ sigma_finite_measure_space p
Proof
  gen_tac
  >> strip_tac
  >> simp[sigma_finite_measure_space_def]
  >> gvs[prob_space_def]
  >> simp[sigma_finite_def]
  >> qexists ‘λn. m_space p’
  >> rpt conj_tac
  >- simp[IN_FUNSET, MEASURE_SPACE_SPACE]
  >- (gen_tac >> simp[SUBSET_DEF])
  >- (simp[EXTENSION]
      >> gen_tac
      >> EQ_TAC
      >- (strip_tac >> metis_tac[])
      >> strip_tac
      >> qexists ‘m_space p’
      >> simp[])
  >> gen_tac
  >> simp[]
QED

(*Theorem measure_prod_list_m_space:
  ∀ml.
    EVERY prob_space ml ⇒
    measure (pi_measure_space ml) (m_space prod_list ml) = 1
Proof
QED

Theorem prob_space_prod_list:
  ∀ml.
    EVERY prob_space ml ⇒
    prob_space (prod_list ml)
Proof
  gen_tac >> strip_tac
  >> simp[prob_space_def]
  >> conj_tac
  >- (sg ‘EVERY sigma_finite_measure_space ml’
      >- (gvs[EVERY_MEM]
          >> gen_tac >> strip_tac
          >> last_x_assum dxrule
          >> simp[prob_space_sigma_finite_measure_space])
      >> dxrule sigma_finite_measure_space_prod_list
      >> simp[sigma_finite_measure_space_def]
     )
  >>

QED
 *)

(*
HAVE: measure_space_general_prod_measure
*)
(* Should be canon *)
Theorem prob_space_general_prod_measure:
  ∀(cons: α -> β -> γ) car cdr m1 m2. pair_operation cons car cdr ∧
                                      prob_space m1 ∧ prob_space m2 ⇒
                                      prob_space (general_prod_measure_space cons m1 m2)
Proof
  rw[] >> simp[prob_space_def] >>
  simp[measure_space_general_prod_measure,prob_space_sigma_finite_measure_space,SF SFY_ss] >>
  gs[prob_space_def] >>
  simp[general_prod_measure_space_def,GSYM general_prod_measure_def] >>
  resolve_then Any irule general_prod_measure_rect EQ_TRANS >>
  last_x_assum $ irule_at Any >> simp[MEASURE_SPACE_SPACE]
QED

Theorem prob_space_prod_list:
  ∀ml. EVERY prob_space ml ⇒ prob_space (prod_list ml)
Proof
  Induct_on ‘ml’
  >- (rw[EVERY_DEF,prod_list_def] >>
      qspec_then ‘{[]}’ assume_tac POW_SIGMA_ALGEBRA >>
      dxrule prob_space_dirac_measure >> simp[]) >>
  rw[EVERY_DEF,prod_list_def] >> rename [‘_ CONS mh (_ mt)’] >>
  irule prob_space_general_prod_measure >> gs[] >>
  irule_at Any pair_operation_CONS
QED

(* -------------------------------------------------------------------------- *)
(* The ith element of any list in the cross of a bunch of lists will be in    *)
(* the ith list that was crossed.                                             *)
(*                                                                            *)
(* ds: domains of the respective elements of the list                         *)
(* ls: chosen list in the product                                             *)
(* i: index                                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem cross_list_el:
  ∀ds ls i.
    ls ∈ cross_list ds ∧
    i < LENGTH ls ⇒
    EL i ls ∈ EL i ds
Proof
  Induct_on ‘ds’
  >- simp[cross_list_def]
  >> rpt gen_tac >> strip_tac
  >> Cases_on ‘i’
  >- (simp[]
      >> Cases_on ‘ls’
      >- gvs[]
      >> gvs[cross_list_def, general_cross_def]
     )
  >> gvs[cross_list_def, general_cross_def]
QED

(* -------------------------------------------------------------------------- *)
(* Extend cross_list_el to the situation where you don't know at which index  *)
(* in the list your element is at                                             *)
(* -------------------------------------------------------------------------- *)
Theorem cross_list_mem:
  ∀ds ls l.
    ls ∈ cross_list ds ∧
    MEM l ls ⇒
    ∃i.
      i < LENGTH ls ∧
      EL i ls = l ∧
      l ∈ EL i ds
Proof
  rpt gen_tac >> strip_tac
  >> gvs[MEM_EL]
  >> qexists ‘n’
  >> simp[]
  >> simp[cross_list_el]
QED

Theorem length_in_cross_list:
  ∀ls ds.
    ls ∈ cross_list ds ⇒
    LENGTH ls = LENGTH ds
Proof
  Induct_on ‘ds’
  >- simp[cross_list_def]
  >> rpt gen_tac >> strip_tac
  >> gvs[cross_list_def, general_cross_def]
QED

Theorem m_space_prod_list:
  ∀ls.
    m_space (prod_list ls) = cross_list (MAP m_space ls)
Proof
  Induct_on ‘ls’
  >- simp[prod_list_def, cross_list_def]
  >> gen_tac
  >> gvs[prod_list_def, cross_list_def, general_cross_def, general_prod_measure_space_def]
QED

Theorem cross_list_empty[simp]:
  cross_list [] = {[]}
Proof
  simp[cross_list_def]
QED

Theorem cross_list_cons_eq_empty:
  ∀l ls.
    cross_list (l::ls) = ∅ ⇔ l = ∅ ∨ cross_list ls = ∅
Proof
  rpt gen_tac
  >> simp[cross_list_def, general_cross_def]
  >> EQ_TAC
  >- (simp[EXTENSION]
      >> CCONTR_TAC >> gvs[]
      >> last_x_assum mp_tac >> simp[]
      >> qexistsl [‘x’, ‘x'’] >> simp[])
  >> strip_tac
  >- simp[]
  >> simp[]
QED

Theorem cross_list_eq_empty:
  ∀ls.
    cross_list ls = ∅ ⇔ MEM ∅ ls
Proof
  gen_tac
  >> Induct_on ‘ls’
  >- simp[]
  >> gen_tac
  >> simp[cross_list_cons_eq_empty]
QED

Theorem cross_list_sing:
  ∀l.
    cross_list [l] = {[x] | x ∈ l}
Proof
  gen_tac
  >> simp[cross_list_def, general_cross_def]
  >> simp[EXTENSION]
QED

Theorem cross_list_sing_alt:
  ∀l.
    cross_list [l] = IMAGE (combin$C CONS []) l
Proof
  gen_tac
  >> simp[cross_list_def, general_cross_def, EXTENSION]
QED

Theorem boolean_rearrangement_lemma_1[local]:
  ∀b1 b2.
    (b1 ∨ b2 ⇔ b1) ⇔ b1 ∨ ¬b2
Proof
  metis_tac[]
QED

Theorem cross_list_cons_eq:
  ∀l1 ls1 l2 ls2.
    cross_list (l1::ls1) = cross_list (l2::ls2) ⇔
      (l1 = l2 ∧ cross_list ls1 = cross_list ls2) ∨
      (MEM ∅ (l1::ls1) ∧ MEM ∅ (l2::ls2))
Proof
  rpt gen_tac
  (* Handle the special case in which either list contains the empty set *)
  >> Cases_on ‘MEM ∅ (l1::ls1) ∨ MEM ∅ (l2::ls2)’
  >- (gvs[GSYM cross_list_eq_empty]
      >> (EQ_TAC >> simp[]
          >> strip_tac
          >> gvs[cross_list_cons_eq_empty])
     )
  >> gvs[]
  >> gvs[GSYM cross_list_eq_empty]
  (* Expand out the cons in the cross_list *)
  >> simp[cross_list_def, general_cross_def]
  (* Prove easy direction *)
  >> REVERSE EQ_TAC
  >- simp[]
  (* Our set equality assumption says that if we have an element in l1 followed
     by a list in cross_list ls1, this is an element in l2 followed by a list in
     cross_list ls2, and vice versa.
.
     We have an element in l1 and and element in cross_list ls1, by our
     assumptions. Therefore, these elements are in l2 and cross_list ls2,
     respectively.
.
     Combining this fact with the previous fact, we can prove that any element
     in l1 is in l2, and vice versa, and any element in cross_list ls1 is in
     cross_list ls2, and vice versa. *)
  >> ‘∃a. a ∈ l1’ by ASM_SET_TAC[]
  >> ‘∃b. b ∈ cross_list ls1’ by ASM_SET_TAC[]
  >> simp[EXTENSION]
  >> strip_tac
  >> sg ‘a ∈ l2 ∧ b ∈ cross_list ls2’
  >- (pop_assum $ qspec_then ‘a::b’ assume_tac
      >> gvs[])
  >> conj_tac
  >- (gen_tac
      >> first_x_assum $ qspec_then ‘x::b’ assume_tac
      >> gvs[])
  >> gen_tac
  >> first_x_assum $ qspec_then ‘a::x’ assume_tac
  >> gvs[]
QED

Theorem cross_list_eq:
  ∀ls1 ls2.
    (cross_list ls1 = cross_list ls2 ⇔
       ls1 = ls2 ∨ (MEM ∅ ls1 ∧ MEM ∅ ls2)
    )
Proof
  rpt gen_tac
  (* Handle the special case in which either list contains the empty set *)
  >> Cases_on ‘MEM ∅ ls1 ∨ MEM ∅ ls2’
  >- (gvs[GSYM cross_list_eq_empty]
      >> (EQ_TAC >> simp[]
          >> strip_tac
          >> gvs[])
     )
  >> gvs[]
  (* Thus, neither cross can be empty *)
  >> gvs[GSYM cross_list_eq_empty]
  (* We prove that the lists have the same length by way of contradiction.
     If they had different lengths then the RHS is clearly F, so we need to
     disprove the LHS. Take an element of ls1, since it is nonempty. This
     element has the same length of ls1 by length_in_cross_list, and thus it
     cannot be in ls2 because then it would have to have the same length as
     ls2, and we are assuming by way of contradiction that the length of ls1 is
     not the length of ls2. *)
  >> Cases_on ‘LENGTH ls1 ≠ LENGTH ls2’
  >- (‘ls1 ≠ ls2’ by (strip_tac >> gvs[])
      >> simp[]
      >> qpat_x_assum ‘ls1 ≠ ls2’ kall_tac
      >> qpat_x_assum ‘cross_list ls2 ≠ ∅’ kall_tac
      >> gvs[EXTENSION]
      >> qexists ‘x’
      >> simp[]
      >> metis_tac[length_in_cross_list]
     )
  >> pop_assum mp_tac >> PURE_REWRITE_TAC[NOT_CLAUSES,IMP_CLAUSES] >> strip_tac
  (* Now we know the lists have the same length. This makes it easier to induct
     on them. *)
  >> rpt (pop_assum mp_tac)
  >> SPEC_ALL_TAC
  >> Induct_on ‘ls1’
  >- simp[]
  >> rpt strip_tac
  (* Split up ls2 to match the way ls1 has been split up *)
  >> namedCases_on ‘ls2’ ["", "h2 ls2"]
  >- (‘F’ suffices_by strip_tac >> pop_assum mp_tac >> simp[])
  (* The appropriate term to apply the inductive hypothesis to is the reduced
     ls2, to match the reduced ls1. *)
  >> last_x_assum $ qspec_then ‘ls2'’ assume_tac
  (* Simplify *)
  >> gvs[]
  (* Handle the case where ls1 is the empty list. Once we've handled this case
     and we know that ls1 is not the empty list, we'll be able to derive the
     prerequisites to apply the inductive hypothesis *)
  >> Cases_on ‘ls1 = []’
  >- (gvs[]
      >> REVERSE EQ_TAC
      >- simp[]
      (* cross_list [h] is an injection mapping each element x to [x], so
         if the crosses are equal, the original sets are equal. *)
      >> simp[cross_list_sing]
      >> simp[EXTENSION]
      >> strip_tac
      >> gen_tac
      >> pop_assum $ qspec_then ‘[x]’ assume_tac
      >> gvs[]
     )
  (* Now we know ls1 is not the empty list, we are in the case where we can
     apply the inductive hypothesis *)
  >> sg ‘cross_list ls1 ≠ ∅ ∧
         cross_list ls2' ≠ ∅’
  >- (qpat_x_assum ‘_ ⇒ _ ⇒ _’ kall_tac
      >> gvs[cross_list_cons_eq_empty])
  >> gvs[]
  (* Use the inductive hypothesis to bring the RHS closer to the LHS,
     so that we only have to prove a single inductive step, adding a single
     element to the head *)
  >> qpat_x_assum ‘cross_list ls1 = cross_list ls2' ⇔ ls1 = ls2'’
                  (fn th => PURE_ONCE_REWRITE_TAC[GSYM th])
  (* *)
  >> PURE_ONCE_REWRITE_TAC[cross_list_cons_eq]
  >> PURE_ONCE_REWRITE_TAC[boolean_rearrangement_lemma_1]
  >> disj2_tac
  >> gvs[cross_list_eq_empty]
QED

val _ = export_theory();
