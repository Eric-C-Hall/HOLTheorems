Definition subset_to_code_def:
  subset_to_code 0n (s : num -> bool) (acc : bool list) = acc ∧
  subset_to_code (SUC i) (s : num -> bool) (acc : bool list) =
    if (i ∈ s) then (SNOC T (subset_to_code i s acc)) else (SNOC F (subset_to_code i s acc))
End

Theorem code_to_subset_SNOC:
  ∀b : bool. ∀bs : bool list.
  code_to_subset (SNOC b bs) =
    let s = (code_to_subset bs) ∘ (λn : num. n - 1) in
    if b then (0 INSERT s) else (s DIFF {0})
Proof
  rpt strip_tac
  >> gvs[]
  >> Induct_on `bs`
  >- (gvs[code_to_subset_def]
      >> `∀f : num -> num. ∅ ∘ f = ∅` by gvs[EQ_EXT]
      >> pop_assum $ qspecl_then [`λn : num. n - 1`] assume_tac
      >> gvs[])
  >> gvs[code_to_subset_def]
  >> rpt strip_tac
  >> Cases_on `h` >> gvs[]
  >> 
 
Cases_on `b` >> gvs[]
  >> Cases_on `b` >> gvs[] >> rpt strip_tac
  >> 
QED


(* -------------------------------------------------------------------------- *)
(* helper function used by subset_to_code                                     *)
(* subset_to_code_helper l i s                                                *)
(* l: length of code                                                          *)
(* i: current element being tested for                                        *)
(* s: input subset                                                            *)
(* -------------------------------------------------------------------------- *)
Definition subset_to_code_helper_def:
  subset_to_code_helper (l : num) 0n (∅ : num -> bool) = acc ∧
  subset_to_code_helper (SUC i) (s : num -> bool) (acc : bool list) =


Theorem subset_to_code_is_right_inverse:
  ∀n s : num -> bool.
  s ∈ POW(count n) ⇒
  code_to_subset (subset_to_code n s []) = s
Proof
  strip_tac
  >> Induct_on `n`
  >- (gvs[POW_EQNS, code_to_subset_def, subset_to_code_def])
  >> rpt strip_tac
  >> simp[subset_to_code_def]
  >> last_x_assum $ qspec_then `s` assume_tac
  >> Cases_on `s ∈ POW (count n)` >> gvs[]
  >> Cases_on `n ∈ s` >> gvs[code_to_subset_def]

(* TODO *)
QED



(* Takes a starting number a and an ending number b and returns the list of
  consecutive numbers between a and b (inclusive of a, exclusive of b) *)
Definition ConsecutiveList_def:
  ConsecutiveList (s : num) (e : num) = (if (s == e) then [] else s::(ConsecutiveList (s + 1n) e))
End


(*Theorem LIST_PERMUTATION_PRODUCT:
  ∀l1 l2 : num list.
    is_permutation l1 l2 ⇒
    FOLDL ($*) 1 l1 = FOLDL ($*) 1 l2
Proof
  strip_tac
  >> Induct_on `l1` >> rpt strip_tac
  >- gvs[is_permutation_def]
  >> simp[FOLDL_MUL_FROM_HEAD_TO_FRONT]
  >> drule $ iffLR is_permutation_def >> pop_assum kall_tac >> rpt strip_tac
  >> sg ``
gvs[]
sg `h * FOLDL $* 1n l1 = FOLDL $* 1n l2` suffices_by gvs[]
QED*)

(* Theorem IS_PERMUTATION_TRANS:
  ∀l1 l2 l3 : num list.
    is_permutation l1 l2 ⇒ is_permutation l2 l3 ⇒ is_permutation l1 l3
Proof
QED*)

(*Theorem IS_PERMUTATION_HEAD:
  ∀l1 l2 : num list.
    (l1 != []) ⇒
    (is_permutation l1 l2) ⇒
    ∃l2' l2'' : num list.
      l2 = l2' ⧺ ((HEAD l1) :: l2'')
Proof
QED*)


(*Theorem IS_PERMUTATION_SYM:
  ∀l1 l2 : num list.
    is_permutation l1 l2 ⇒ is_permutation l2 l1
Proof
  rpt strip_tac
  >> drule $ iffLR is_permutation_def >> pop_assum kall_tac >> rpt strip_tac
  >> irule $ iffRL is_permutation_def
  >> 
QED*)

(*Definition inverse_perm_def:
  inverse_perm perm*)



Definition is_permutation_def:
  is_permutation l1 l2 ⇔
  (∃perm : num list.
    (* Permutation must map elements to identical elements *)
    (∀i : num. i < LENGTH perm ⇒ EL (EL i perm) l1 = EL i l2) ∧
    (* Permutation may not map two elements to the same element *)
    (∀x y : num. x < LENGTH perm ⇒ y < LENGTH perm ⇒ ¬(x = y) ⇒ ¬(EL x perm = EL y perm)) ∧
    (* Permutation must map all elements to some element *)
    LENGTH perm = LENGTH l1 ∧
    (* Permutation must be between two lists of the same length *)
    LENGTH l1 = LENGTH l2
)
End

Definition identity_perm_def:
  (identity_perm 0n = []) ∧
  (identity_perm (SUC n) = SNOC n (identity_perm n))
End

Theorem IDENTITY_PERM_LENGTH:
  ∀n : num.
  LENGTH (identity_perm n) = n
Proof
  rpt strip_tac
  >> Induct_on `n` >> gvs[identity_perm_def]
QED

Theorem IDENTITY_PERM_EL:
  ∀i n : num.
    i < n ⇒
    EL i (identity_perm n) = i
Proof
  strip_tac >> strip_tac
  >> `∀i : num. i < n ⇒ EL i (identity_perm n) = i` suffices_by gvs[]
  >> Induct_on `n`
  >- gvs[]
  >> rpt strip_tac
  >> simp[identity_perm_def]
  >> Cases_on `i = n`
  >- (`i = LENGTH (identity_perm i)` by gvs[IDENTITY_PERM_LENGTH]
      >> gvs[]
      >> metis_tac[EL_LENGTH_SNOC])
  >> `i < n` by gvs[]
  >> gvs[]
  >> first_x_assum $ qspec_then `i` assume_tac
  >> gvs[]
  >> `EL i (SNOC n (identity_perm n)) = EL i (identity_perm n)` suffices_by simp[]
  >> irule EL_SNOC
  >> metis_tac[IDENTITY_PERM_LENGTH]
QED

Theorem IS_PERMUTATION_REFL:
  ∀l : num list.
    is_permutation l l
Proof
  strip_tac
  >> irule $ iffRL is_permutation_def
  >> qexists `identity_perm (LENGTH l)`
  >> gvs[]
  >> conj_tac
  >- (rpt strip_tac
      >> qspecl_then [`i`, `LENGTH l`] assume_tac IDENTITY_PERM_EL
      >> gvs[IDENTITY_PERM_LENGTH])
  >> conj_tac
  >- (rpt strip_tac
      >> gvs[IDENTITY_PERM_EL, IDENTITY_PERM_LENGTH])
  >- gvs[IDENTITY_PERM_LENGTH]
QED



Theorem FOLDL_MUL_FROM_HEAD_TO_FRONT:
  ∀n i : num. ∀l : num list.
    FOLDL ($*) i (n::l) = n * FOLDL ($*) i l
Proof
  `∀l : num list. ∀n i : num. FOLDL ($*) i (n::l) = n * FOLDL ($*) i l` suffices_by
  (rpt strip_tac
   >> pop_assum $ qspecl_then [`l`, `n`, `i`] assume_tac
   >> gvs[])
  >> strip_tac
  >> Induct_on `l` >> rpt strip_tac >> gvs[]
QED

Theorem FOLDL_MUL_TO_FRONT:
  ∀l1 l2 : num list. ∀n : num.
    FOLDL ($*) 1 (l1 ⧺ n::l2) = n * FOLDL ($*) 1 (l1 ⧺ l2)
Proof
  rpt strip_tac
  >> Induct_on `l1`
  >- gvs[FOLDL_MUL_FROM_HEAD_TO_FRONT]
  >> rpt strip_tac
  >> simp[FOLDL_MUL_FROM_HEAD_TO_FRONT]
QED

(* 
Theorem CARD_0_FINITE:
  ∀s : α -> bool.
  CARD s = 0 ⇒ FINITE s
Proof
  Cases_on `CARD`

  rpt strip_tac
  >> irule $ iffRL FINITE_DEF
  >> rpt strip_tac

  >> Cases_on `s` >> gvs[]
  >> gvs[CARD_INSERT]
  >> strip_tac
  gvs[]
  >- gvs[]
QED

Theorem CARD_0_EMPTY:
  ∀s : α -> bool.
  CARD s = 0 ⇒ s = ∅
Proof
QED*)

(* -------------------------------------------------------------------------- *)
(* Since every element of l1 is less than length l1, we have                  *)
(* l1 is a subset of [0, ..., (length l1) - 1]                                *)
(*                                                                            *)
(* Consider EL [0, ... l - 1] to [0, ... l - 1] - [x]. Since CARD t < CARD s  *)
(* we can use pred_setTheory.PHP (the pigeonhole principle for sets) to prove *)
(* that f is not injective.                                                   *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(*Theorem EVERY_LESS_LENGTH_ALL_DISTINCT_IMPLIES_MEM:
  ∀x : num.
  EVERY (λx. x < (LENGTH l1)) l1 ⇒
  ALL_DISTINCT l1 ⇒
  x < (LENGTH l1) ⇒
  MEM x l1
Proof
  rpt strip_tac >>
  qspecl_then [``, `λx : num. x < `] assume_tac FINITE_INJ_BIJ

FILTER (λx. )

  (λi : num. EL i l1)

  (* not member implies identity has smaller domain
  
QED*)
