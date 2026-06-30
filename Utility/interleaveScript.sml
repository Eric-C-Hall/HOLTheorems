Theory interleave

Ancestors arithmetic divides list marker modeq_thms rich_list

Libs ConseqConv dep_rewrite;

(* ConseqConv: SPEC_ALL_TAC *)

(* -------------------------------------------------------------------------- *)
(* Takes a list of lists. Interleaves these lists.                            *)
(*                                                                            *)
(* e.g. [[a;a;a];[b;b;b];[c;c;c]] becomes [a;b;c;a;b;c;a;b;c]                 *)
(*                                                                            *)
(* If any list is shorter than the others, truncates the remaining lists to   *)
(* match.                                                                     *)
(*                                                                            *)
(* Note: not easy to use as a rewrite rule because it has the LHS within the  *)
(*       RHS. Perhaps there's a better definition?                            *)
(* -------------------------------------------------------------------------- *)
Definition interleave_def:
  interleave ls = if MEM [] ls ∨ ls = []
                  then
                    []
                  else
                    (MAP HD ls) ++ interleave (MAP TL ls)
Termination
  WF_REL_TAC ‘measure (λls. MIN_LIST (MAP LENGTH ls))’
  >> rw[]
  >> Induct_on ‘ls’ >> rw[]
  >> qabbrev_tac ‘l=h’ >> qpat_x_assum ‘Abbrev _’ kall_tac
  >> gvs[]
  >> ‘0 < LENGTH l’ by gvs[LENGTH_NON_NIL]
  >> Cases_on ‘ls’ >> gvs[LENGTH_TL]
  >> qabbrev_tac ‘l2=h’ >> qpat_x_assum ‘Abbrev _’ kall_tac
  >> gvs[MIN_DEF]
End

(* -------------------------------------------------------------------------- *)
(* Gets every nth element of a list                                           *)
(*                                                                            *)
(* ls: the list to get every nth element from                                 *)
(* n: the value of n to get every nth element for                             *)
(* i: an offset to start getting every nth element from. 0 if we want to      *)
(*    include the 0th element of the list, 1 if we want to start from the     *)
(*    1st element of the list, and so on.                                     *)
(*                                                                            *)
(* Be careful of behaviour when n = 0. This is an unexpected input. The       *)
(* practical behaviour in this case is defined by                             *)
(* get_every_nth_element_zero_n                                               *)
(*                                                                            *)
(* get_every_nth_element_alt is a particularly useful alternate definition    *)
(* which helps with induction, allowing us to instead perform the operation   *)
(* dropping the first n elmenets and taking the mth at each step.             *)
(* -------------------------------------------------------------------------- *)
Definition get_every_nth_element_def:
  get_every_nth_element [] _ _ = [] ∧
  get_every_nth_element (l::ls) n 0 = l::(get_every_nth_element ls n (n - 1)) ∧
  get_every_nth_element (l::ls) (n) (SUC i) = get_every_nth_element ls n i
End


(* -------------------------------------------------------------------------- *)
(* Takes an interleaved list, and the number of lists that it is comprised    *)
(* of, and returns the original, deinterleaved lists.                         *)
(*                                                                            *)
(* e.g. deinterleave 3 [[a;a;a];[b;b;b];[c;c;c]] returns [a;b;c;a;b;c;a;b;c]  *)
(*                                                                            *)
(* If the length of the list is not a multiple of the number of lists, then   *)
(* the output lists may be of different lengths to each other.                *)
(* -------------------------------------------------------------------------- *)
Definition deinterleave_def:
  deinterleave n ls =
  MAP (get_every_nth_element ls n) (COUNT_LIST n)
End

Theorem interleave_empty[simp]:
  interleave [] = []
Proof
  gvs[Once interleave_def]
QED

Theorem get_every_nth_element_empty[simp]:
  ∀n i.
    get_every_nth_element [] n i = []
Proof
  gvs[get_every_nth_element_def]
QED

Theorem MAP_REPLICATE_FORALL:
  ∀f ls n x.
    MAP f ls = REPLICATE n x ⇔ (∀l. MEM l ls ⇒ f l = x) ∧ LENGTH ls = n
Proof
  rw[]
  >> EQ_TAC
  >- (disch_tac
      >> sg ‘LENGTH ls = n’
      >- (rpt $ pop_assum mp_tac >> SPEC_ALL_TAC
          >> Induct_on ‘n’ >- gvs[]
          >> rw[]
          >> Cases_on ‘ls’ >> gvs[]
          >> metis_tac[]
         )
      >> gvs[]
      >> rpt $ pop_assum mp_tac >> SPEC_ALL_TAC
      >> Induct_on ‘ls’ >- gvs[]
      >> rw[]
      >> metis_tac[]
     )
  >> rw[]
  >> rpt $ pop_assum mp_tac >> SPEC_ALL_TAC
  >> Induct_on ‘ls’ >- gvs[]
  >> rw[]
QED

Theorem deinterleave_empty[simp]:
  ∀n.
    deinterleave n [] = REPLICATE n []
Proof
  rw[deinterleave_def]
  >> gvs[MAP_REPLICATE_FORALL]
  >> gvs[LENGTH_COUNT_LIST]
QED

Theorem interleave_replicate_empty[simp]:
  ∀n.
    interleave (REPLICATE n []) = []
Proof
  rw[Once interleave_def]
QED

Theorem COUNT_LIST_EMPTY[simp]:
  ∀n.
    COUNT_LIST n = [] ⇔ n = 0
Proof
  rw[]
  >> Cases_on ‘n’
  >> gvs[COUNT_LIST_def]
QED

(* -------------------------------------------------------------------------- *)
(* Deinterleaving followed by interleaving is the identity.                   *)
(* -------------------------------------------------------------------------- *)
(*Theorem interleave_deinterleave:
  ∀n ls.
    divides n (LENGTH ls) ⇒
    interleave (deinterleave n ls) = ls
Proof
  rw[]
  >> gvs[divides_def]
  >> pop_assum mp_tac >> SPEC_ALL_TAC
  >> Induct_on ‘q’ >- rw[]
  >> rw[]
  >> PURE_REWRITE_TAC[deinterleave_def]
  >> PURE_REWRITE_TAC[Once interleave_def]
  >> gvs[]
QED*)

(* -------------------------------------------------------------------------- *)
(* Interleaving followed by deinterleaving is the identity                    *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(*Theorem deinterleave_interleave:

Proof
QED*)

(*Theorem length_get_every_nth_element_zero[local]:
  ∀ls n m.
    LENGTH (get_every_nth_element ls n 0) =
    (LENGTH ls) DIV n
Proof
QED*)

Theorem get_every_nth_element_sing_m_1[simp]:
  ∀l n.
    get_every_nth_element [l] n 1 = []
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[ONE]
  >> simp[get_every_nth_element_def]
QED

Theorem get_every_nth_element_suc_m:
  ∀ls n m.
    get_every_nth_element ls n (SUC m) = get_every_nth_element (TL ls) n m
Proof
  Cases_on ‘ls’ >> rpt gen_tac
  >- simp[]
  >> simp[get_every_nth_element_def]
QED

(* -------------------------------------------------------------------------- *)
(* The case of n = 0 is a special case, with no clear expected behaviour      *)
(* (perhaps it should be an infinite string of the element at index m?        *)
(*                                                                            *)
(* This theorem makes it more clear what the behaviour precisely is in the    *)
(* definition I use.                                                          *)
(* -------------------------------------------------------------------------- *)
Theorem get_every_nth_element_zero_n:
  ∀ls m.
    get_every_nth_element ls 0 m = DROP m ls
Proof
  Induct_on ‘ls’
  >- simp[]
  >> rpt gen_tac
  >> Cases_on ‘m’
  >- simp[get_every_nth_element_def]
  >> simp[]
  >> simp[get_every_nth_element_suc_m]
QED

(* -------------------------------------------------------------------------- *)
(* An alternate definition of get_every_nth_element.                          *)
(*                                                                            *)
(* Takes off the first n elements and chooses the mth one.                    *)
(*                                                                            *)
(* Particularly useful for induction, as in each step, we perform the same    *)
(* action (taking off the first n elements), whereas the steps vary in the    *)
(* other definition (either counting down by 1, or adding the element and     *)
(* resetting the counter)                                                     *)
(*                                                                            *)
(* The process of taking off the first n elements never terminates in the     *)
(* case of n = 0, so we have to treat that case specially. We define it to    *)
(* take the same value as in the original definition.                         *)
(* -------------------------------------------------------------------------- *)
Theorem get_every_nth_element_alt:
  ∀ls n m.
    get_every_nth_element ls n m =
    if LENGTH ls ≤ m
    then
      []
    else
      if n = 0
      then
        DROP m ls
      else
        (EL m ls)::(get_every_nth_element (DROP n ls) n m)
Proof
  (* Strong induct on the length of the list ls *)
  rpt gen_tac
  >> qabbrev_tac ‘len_ls = LENGTH ls’
  >> pop_assum mp_tac >> PURE_ONCE_REWRITE_TAC[Abbrev_def]
  >> SPEC_ALL_TAC
  >> completeInduct_on ‘len_ls’
  (* *)
  >> rpt gen_tac >> strip_tac
  (* The case where m = 0, and hence get_every_nth_element wraps around, is
     different in nature to the case where m ≠ 0 *)
  >> Cases_on ‘m = 0’              
  >- (gvs[]
      >> Cases_on ‘ls’
      >- simp[]
      >> PURE_ONCE_REWRITE_TAC[get_every_nth_element_def]
      (* Avoid infinite loop due to repeated application of inductive hypothesis *)
      >> pop_assum (fn th => assume_tac (REWRITE_RULE [Once (GSYM Abbrev_def)] th))
      (* *)
      >> simp[]
      >> rw[]
      >- (simp[get_every_nth_element_def] >> rw[])
      (* Apply inductive hypothesis once on the left hand side, which has been
         reduced: this should drop n elements from t, bringing it more in line
         with the RHS *)
      >> last_x_assum (fn th => assume_tac (REWRITE_RULE [Abbrev_def] th))
      >> pop_assum $ qspec_then ‘LENGTH t’ assume_tac
      >> gvs[]
      (* We have now applied the inductive hypothesis
         Split over cases *)
      >> rw[]
      >- (sg ‘DROP (n - 1) t = []’
          >- simp[]
          >> simp[])
      (* The LHS is currently one below the RHS: bring the RHS one down to
         match the LHS *)
      >> Cases_on ‘DROP (n - 1) t’
      >- gvs[]
      >> simp[get_every_nth_element_def]
      >> conj_tac
      >- (sg ‘HD (DROP (n - 1) t) = h’
          >- simp[]
          >> qpat_x_assum ‘DROP _ _ = _’ kall_tac
          >> gvs[]
          >> simp[HD_DROP])
      >> sg ‘DROP n t = t'’
      >- (sg ‘TL (DROP (n - 1) t) = t'’
          >- simp[]
          >> qpat_x_assum ‘DROP _ _ = _’ kall_tac
          >> gvs[]
          >> simp[TAIL_BY_DROP]
          >> simp[DROP_DROP])
      >> simp[]
     )
  (* Case where m ≠ 0 *)
  >> simp[]
  (* Reduce to smaller ls to apply induction *)
  >> Cases_on ‘ls’
  >- simp[]
  (* Break down m so we can use the definition of get_every_nth_element, to
     reduce to a smaller case *)
  >> Cases_on ‘m’
  >- simp[]
  (* Apply definition of get_every_nth_element to get to a smaller case *)
  >> simp[get_every_nth_element_def]
  (* Apply the inductive hypothesis *)
  >> last_x_assum $ qspec_then ‘len_ls - 1’ assume_tac
  >> gvs[]
  (* Inductive hypothesis has been applied, no need for it any more *)
  >> last_x_assum kall_tac
  (* Split into cases and automatically solve where possible *)
  >> rw[]
  (* *)
  >> simp[get_every_nth_element_suc_m]
  (* Consider the case where we can swap TL and DROP *)
  >> Cases_on ‘n - 1 < LENGTH t’
  >- (simp[TL_DROP] >> Cases_on ‘t’ >> simp[])
  >> gvs[]
  (* If we can't swap TL and DROP, then certainly the DROP must be [] *)
  >> sg ‘DROP (n - 1) t = []’
  >- simp[]
  (* Apply this *)
  >> simp[]
  (* If DROP (n - 1) t = [], then certainly DROP n t = [] *)
  >> sg ‘DROP n t = []’
  >- simp[]
  >> simp[]
QED

Theorem length_get_every_nth_element:
  ∀ls n m.
    m < n ⇒
    LENGTH (get_every_nth_element ls n m) =
    (LENGTH ls) DIV n + if m < (LENGTH ls MOD n) then 1 else 0
Proof
  rpt gen_tac >> strip_tac
  (* Special case of n = 0 *)
  >> Cases_on ‘n = 0’
  >- simp[]
  (* Do complete induction on the length of ls: we want to apply
     get_every_nth_element_alt and use the inductive hypothesis on the
     smaller version with the first n elements removed *)
  >> qabbrev_tac ‘len_ls = LENGTH ls’
  >> pop_assum mp_tac >> PURE_ONCE_REWRITE_TAC[Abbrev_def]
  >> rpt (pop_assum mp_tac)
  >> SPEC_ALL_TAC
  >> completeInduct_on ‘len_ls’                       
  >> rpt gen_tac >> rpt disch_tac
  (* Apply get_every_nth_element_alt once to simplify get_every_nth_element to
     remove the first n elements of the list *)
  >> simp[Once get_every_nth_element_alt]
  (* Handle various cases *)
  >> Cases_on ‘LENGTH ls ≤ m’
  >- (simp[]
      >> simp[DIV_EQUAL_0])
  >> simp[]
  (* Apply inductive hypothesis *)
  >> gvs[]
  (* Now inductive hypothesis has been applied it is no longer necessary *)
  >> last_x_assum kall_tac
  (* *)
  >> simp[ADD1]
  >> gvs[NOT_LE]
  (* The case where LENGTH ls ≤ n seems like a special case, so lets handle
     that case. *)
  >> Cases_on ‘LENGTH ls ≤ n’
  >- (simp[]
      >> sg ‘LENGTH ls - n = 0’
      >- simp[]
      >> simp[]
      >> Cases_on ‘LENGTH ls < n’
      >- (sg ‘LENGTH ls MOD n = LENGTH ls’
          >- simp[]
          >> simp[]
          >> simp[DIV_EQUAL_0])
      >> sg ‘LENGTH ls = n’
      >- simp[]
      >> simp[]
     )
  (* Simplify NOT of ≤ *)
  >> gvs[NOT_LE]
  (* Now we can apply SUB_DIV *)
  >> simp[SUB_DIV]
  (* *)
  >> Cases_on ‘m < (LENGTH ls - n) MOD n’
  >- (simp[]
      >> simp[SUB_RIGHT_ADD]
      >> Cases_on ‘LENGTH ls DIV n ≤ 1’
      >- (Cases_on ‘LENGTH ls DIV n = 0’
          >- (simp[] >> gvs[DIV_EQUAL_0])
          >> sg ‘LENGTH ls DIV n = 1’
          >- simp[]
          >> simp[]
          >> rw[]
          >> gvs[NOT_LT]
          >> gvs[SUB_MOD])
      >> simp[]
      >> gvs[NOT_LE]
      >> rw[]
      >> gvs[NOT_LT]
      >> gvs[SUB_MOD]
     )
  (* *)
  >> gvs[NOT_LT]
  >> gvs[SUB_MOD]
  >> Cases_on ‘1 ≤ LENGTH ls DIV n’
  >- simp[SUB_ADD]
  >> gvs[NOT_LE]
  >> gvs[DIV_EQUAL_0]
QED

Theorem el_deinterleave:
  ∀m n ls.
    m < n ⇒
    EL m (deinterleave n ls) = get_every_nth_element ls n m
Proof
  rpt gen_tac
  >> simp[deinterleave_def]
  >> simp[el_map_count]
QED

Theorem el_deinterleave_snoc:
  ∀n m l ls.
    m < n ⇒
    EL m (deinterleave n (SNOC l ls))
    = if (LENGTH ls) MOD n = m
      then SNOC l (EL m (deinterleave n ls))
      else EL m (deinterleave n ls)
Proof  
  rpt gen_tac >> strip_tac
  >> simp[el_deinterleave]
  >> pop_assum mp_tac
  >> SPEC_ALL_TAC
  >> Induct_on ‘ls’
  >- (rpt gen_tac
      >> simp[]
      >> rw[] >> simp[get_every_nth_element_def]
      >> Cases_on ‘m’ >> simp[get_every_nth_element_def])
  >> rpt gen_tac >> strip_tac
  >> simp[]
  >> Cases_on ‘m’
  >- (simp[get_every_nth_element_def]
      >> rw[]
      >- (simp[GSYM SNOC_APPEND]
          (* Inductive hypothesis was automatically applied here, get rid of
             it *)
          >> last_x_assum kall_tac
          >> rw[]
          >> gvs[ADD1]
          >> pop_assum mp_tac
          >> simp[]
          (* Convert assumption and goal to MODEQ *)
          >> sg ‘MODEQ n (LENGTH ls + 1) 0’
          >- simp[MODEQ_NONZERO_MODEQUALITY]
          >> qpat_x_assum ‘_ = 0’ kall_tac
          >> qsuff_tac ‘MODEQ n (LENGTH ls) (n - 1)’
          >- simp[]
          (* *)
          >> gvs[Once MODEQ_ADD_BASE_RIGHT]
          >> simp[Once MODEQ_ADD_ONE_BOTH_SIDES]
         )
      (* Apply the inductive hypothesis to the LHS *)
      >> last_x_assum $ qspecl_then [‘l’, ‘n - 1’, ‘n’] assume_tac
      >> gvs[]
      >> simp[GSYM SNOC_APPEND]
      >> pop_assum kall_tac
      (* *)
      >> rw[]
      >> gvs[ADD1]
      >> qpat_x_assum ‘_ ≠ _’ mp_tac >> simp[]
      (* Convert to MODEQ form *)
      >> sg ‘MODEQ n (LENGTH ls) (n - 1)’
      >- simp[MODEQ_THM]
      >> qpat_x_assum ‘_ = n - 1’ kall_tac
      >> qsuff_tac ‘MODEQ n (LENGTH ls + 1) 0’
      >- simp[]
      (* *)
      >> qspecl_then [‘n’, ‘LENGTH ls + 1’, ‘0’, ‘n - 1’] 
                     (fn th => PURE_ONCE_REWRITE_TAC[th]) MODEQ_ADD_BOTH_SIDES
      >> simp[]
      >> PURE_ONCE_REWRITE_TAC[ADD_COMM]
      >> simp[GSYM MODEQ_ADD_BASE_LEFT]
     )
  >> simp[get_every_nth_element_def]
  (* Apply the inductive hypothesis to the LHS *)
  >> simp[GSYM SNOC_APPEND]
  (* Remove the inductive hypothesis now that it has been applied *)
  >> last_x_assum kall_tac
  (* *)
  >> rw[]
  >- (gvs[ADD1]
      >> qpat_x_assum ‘_ ≠ _’ mp_tac >> simp[]
      >> PURE_ONCE_REWRITE_TAC[GSYM MOD_PLUS]
      >> simp[X_MOD_Y_EQ_X])
  >> qpat_x_assum ‘_ ≠ _’ mp_tac >> simp[]
  >> rpt (pop_assum mp_tac) >> PURE_ONCE_REWRITE_TAC[ADD1] >> rpt disch_tac
  (* Convert to MODEQ *)
  >> qsuff_tac ‘MODEQ n (LENGTH ls) n'’
  >- simp[]
  (* Add one to both sides *)
  >> PURE_ONCE_REWRITE_TAC[MODEQ_ADD_ONE_BOTH_SIDES]
  (* Convert back to mod *)
  >> simp[MODEQ_THM]
QED

Theorem length_el_deinterleave:
  ∀n m ls.
    m < n ⇒
    LENGTH (EL m (deinterleave n ls)) =
    LENGTH ls DIV n +
    (if m + 1 ≤ LENGTH ls MOD n then 1 else 0) 
Proof
  rpt gen_tac >> strip_tac
  >> simp[el_deinterleave]
  >> simp[length_get_every_nth_element]
QED

Theorem hd_deinterleave:
  ∀n m ls.
    n ≠ 0 ⇒
    HD (deinterleave n ls) = get_every_nth_element ls n 0
Proof
  rpt gen_tac >> strip_tac
  >> PURE_ONCE_REWRITE_TAC[GSYM EL]
  >> simp[el_deinterleave, Excl "EL_restricted"]
QED
