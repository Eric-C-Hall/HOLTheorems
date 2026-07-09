(* -------------------------------------------------------------------------- *)
(* Code sent to me by Jared Yeager (I'm pretty sure he wrote it, too)         *)
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

val _ = new_theory "jared_yeager_listspace";

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

Definition list_measure_space_def:
    list_measure_space [] = ({[]}, POW {[]}, C 𝟙 []) ∧
    list_measure_space (mh::mt) = general_prod_measure_space CONS mh (list_measure_space mt)
End

Theorem sigma_finite_measure_space_dirac_measure:
    ∀sa x. sigma_algebra sa ⇒ sigma_finite_measure_space (space sa,subsets sa,C 𝟙 x)
Proof
    rw[sigma_finite_measure_space_def,measure_space_dirac_measure,sigma_finite_def] >>
    qexists ‘K (space sa)’ >> simp[FUNSET,SIGMA_ALGEBRA_SPACE] >>
    reverse conj_tac >- (rw[indicator_fn_def]) >>
    rw[EXTENSION,IN_BIGUNION_IMAGE]
QED

Theorem sigma_finite_measure_space_list_measure_space:
    ∀ml. EVERY sigma_finite_measure_space ml ⇒ sigma_finite_measure_space (list_measure_space ml)
Proof
    Induct_on ‘ml’
    >- (rw[EVERY_DEF,list_measure_space_def] >>
        qspec_then ‘{[]}’ assume_tac POW_SIGMA_ALGEBRA >>
        dxrule sigma_finite_measure_space_dirac_measure >> simp[]) >>
    rw[EVERY_DEF,list_measure_space_def] >> rename [‘_ CONS mh (_ mt)’] >>
    irule sigma_finite_measure_space_general_prod_measure >> gs[] >>
    irule_at Any pair_operation_CONS
QED

val _ = export_theory();
