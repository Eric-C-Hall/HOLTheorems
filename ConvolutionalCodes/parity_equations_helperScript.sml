Theory parity_equations_helper

Ancestors arithmetic list rich_list logroot numposrep bitstring state_machine

Libs dep_rewrite;

(* -------------------------------------------------------------------------- *)
(* Note: There are two LOG2's. One is an overloading for logroot$LOG applied  *)
(* to the value 2, and the other is bit$LOG. I only want to use logroot$LOG,  *)
(* because that one can be evaluated using EVAL_TAC when applied to a         *)
(* constant, whereas the other cannot.                                        *)
(* -------------------------------------------------------------------------- *)
Theorem v2n_lt_imp:
  ∀v l.
    LENGTH v ≤ l ⇒ v2n v < 2 ** l
Proof
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac ‘LHS < RHS’
  >> ‘2 ** LENGTH v ≤ RHS’ by gvs[Abbr ‘RHS’]
  >> ‘LHS < 2 ** LENGTH v’ by gvs[Abbr ‘LHS’, v2n_lt]
  >> metis_tac[LESS_LESS_EQ_TRANS]
QED

(* -------------------------------------------------------------------------- *)
(* In my opinion, this is a better candidate to be length_zero_extend,        *)
(* largely because it is an unconditional rewrite rule, whereas               *)
(* length_zero_extend is conditional                                          *)
(* -------------------------------------------------------------------------- *)
Theorem length_zero_extend_2:
  ∀bs l.
    LENGTH (zero_extend l bs) = MAX (LENGTH bs) l
Proof
  rpt strip_tac
  >> Induct_on ‘l’ >> gvs[zero_extend_def, PAD_LEFT]
  >> gvs[ADD1]
  >> gvs[MAX_DEF]
QED

Theorem boolify_length:
  ∀a v.
    LENGTH (boolify a v) = LENGTH a + LENGTH v
Proof
  Induct_on ‘v’ >> gvs[boolify_def]
QED

(* Seems relevant: LOG2_PROPERTY *)

Theorem LOG_POW_LT:
  ∀n m b.
    n ≠ 0 ∧
    n < b ** m ⇒
    LOG b n < m
Proof
  rpt strip_tac
  >> qspecl_then [‘n’,‘m’,‘b’] assume_tac (GEN_ALL LT_EXP_LOG)
  >> gvs[]
QED

(* Potentially useful:

 LT_EXP_LOG
 LOG2_UNIQUE
 LOG_DIV
 LOG_EVAL
 LOG_LE_MONO
 LOG_POWER
 LOG_TEST
 LOG_THM
 LOG_UNIQUE
 TWO_EXP_LOG2_LE*)

Theorem SUC_LOG_LE:
  ∀n l b.
    n ≠ 0 ∧
    n < b ** l ⇒
    SUC (LOG b n) ≤ l
Proof
  rpt strip_tac
  >> gvs[GSYM LESS_EQ]
  >> gvs[LOG_POW_LT]
QED

Theorem bitstring_n2v_length_le:
  ∀n l.
    0 < l ∧
    n < 2 ** l ⇒
    LENGTH (n2v n) ≤ l
Proof
  rpt strip_tac
  >> gvs[n2v_def]
  >> gvs[boolify_length]
  >> gvs[LENGTH_n2l]
  >> rw[]
  >> gvs[SUC_LOG_LE]
QED

Theorem PAD_LEFT_SUC:
  ∀c n ls.
    PAD_LEFT c (SUC n) ls = (if LENGTH ls < SUC n then [c] else []) ⧺ PAD_LEFT c n ls
Proof
  rpt strip_tac
  >> gvs[PAD_LEFT]
  >> gvs[GSYM REPLICATE_GENLIST]
  >> gvs[SUB]
  >> rw[]
QED

Theorem zero_extend_suc:
  ∀n bs.
    zero_extend (SUC n) bs = (if LENGTH bs < SUC n then [F] else []) ⧺ (zero_extend n bs)
Proof
  rpt strip_tac
  >> gvs[zero_extend_def]
  >> gvs[PAD_LEFT_SUC]
QED

Theorem if_add_0_right:
  ∀b l n.
    (if b then l + n else l) = (l + if b then n else 0)
Proof
  rpt strip_tac
  >> rw[]
QED

Theorem if_add:
  ∀b l n m.
    (if b then l + n else l + m) = (l + if b then n else m)
Proof
  rpt strip_tac
  >> rw[]
QED

Theorem v2n_zero_extend[simp]:
  ∀l bs.
    v2n (zero_extend l bs) = v2n bs
Proof
  rpt strip_tac
  >> Induct_on ‘l’
  >- gvs[zero_extend_def, PAD_LEFT]
  >> gvs[zero_extend_suc]
  >> gvs[v2n_APPEND]
  >> rw[v2n]
QED

(* -------------------------------------------------------------------------- *)
(* Want to prove: natural numbers between 2 ** (l - 1) (inclusive) and        *)
(* 2 ** l (exclusive) correspond precisely to vectors of length l that start  *)
(* with 1, except in the special case where 0 is considered to have length 1  *)
(* despite not starting with 1.                                               *)
(*                                                                            *)
(* That is:                                                                   *)
(* - correct_length v ==> correct_size (v2n v)                                *)
(* - correct_length v <== correct_size (v2n v)                                *)
(* - correct_length (n2v n) ==> correct_size n                                *)
(* - correct_length (n2v n) <== correct_size n                                *)
(*                                                                            *)
(* I'm not 100% certain of the specifics, but I believe that an upper bound   *)
(* one direction can be shown equivalent to a lower bound in the other        *)
(* direction or something. <- hmm... this assertion seems dubious             *)
(*                                                                            *)
(* Alternatively want to prove (and then the above would follow): natural     *)
(* numbers less than 2 ** l correspond precisely to vectors of length at      *)
(* most l.                                                                    *)
(*                                                                            *)
(* That is:                                                                   *)
(* - upper_bound_length v ==> upper_bound_size (v2n v)                        *)
(* - upper_bound_length v <== upper_bound_size (v2n v)                        *)
(* - upper_bound_length (n2v n) ==> upper_bound_size n                        *)
(* - upper_bound_length (n2v n) <== upper_bound_size n                        *)
(*                                                                            *)
(* We already have:                                                           *)
(* - upper_bound_length v ==> upper_bound_size (v2n v)                        *)
(*     (from v2n_lt_imp/v2n_lt)                                               *)
(* - upper_bound_length (n2v n) <== upper_bound_size n                        *)
(*     (from n2v_length_le)                                                   *)
(*                                                                            *)
(* Thus, we want to prove one of the remaining implications, from which the   *)
(* other will likely follow.                                                  *)
(* -------------------------------------------------------------------------- *)

Theorem v2n_zero:
  ∀v.
    v2n v = 0 ⇔ (∃n. v = REPLICATE n F)
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (rpt strip_tac
      >> Induct_on ‘v’ >> gvs[] >> rpt strip_tac
      >> Cases_on ‘h’ >> gvs[]
      >- gvs[v2n]
      >> gvs[v2n]
      >> qexists ‘SUC n’ >> gvs[]
     )
  >> disch_tac
  >> Induct_on ‘v’ >> gvs[v2n]
  >> rpt strip_tac
  >> rw[]
  >- (Cases_on ‘n’ >> gvs[REPLICATE])
  >> Cases_on ‘n’ >> gvs[REPLICATE]
  >> pop_assum irule
  >> qexists ‘n'’ >> gvs[]
QED

(* For some reason, l2n takes input in little-endian form whereas v2n takes
   input in big-endian form. bitify reverses the order of its input in the
   process of performing the conversion. *)

(*
Theorem v2n_lt_imp2:
  ∀v l.
    v ≠ [F] ∧
    v2n v < 2 ** l ⇒
    LENGTH v ≤ l
Proof
  Induct_on ‘l’ >> rpt strip_tac >> gvs[]
  >- (Cases_on ‘v’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[v2n]
      >> Cases_on ‘h’ >> gvs[]
      >> Cases_on ‘h'’ >> gvs[]




                             Induct_on ‘v’ >> rpt strip_tac >> gvs[]
      >> gvs[v2n]
      >> sg ‘v2n v < 2 ** l’
      >- (qmatch_asmsub_abbrev_tac ‘m < 2 ** l’
          >> qsuff_tac ‘v2n v ≤ m’
          >- (rpt strip_tac
              >> gvs[])
          >> unabbrev_all_tac
          >> Cases_on ‘h’ >> gvs[]
         )
      >> gvs[]
      >> last_assum $ qspec_then ‘l’ assume_tac
      >> last_x_assum assume_tac
      >> qmatch_asmsub_abbrev_tac ‘donotexpand’
      >> gvs[]



      >> rw[]
      >> gvs[]


      >> Cases_on ‘l’  >> gvs[]
      >- (gvs[v2n]
          >> Cases_on ‘h’ >> gvs[]
          >> gvs[v2n_zero]
          >> last_x_assum $ qspec_then ‘0’ assume_tac
          >> gvs[]
          >> Cases_on ‘n’ >> gvs[]
QED*)

(*Theorem v2n_lt_iff:
  v ≠ [F] ⇒
  (v2n v < 2 ** l ⇔ LENGTH v ≤ l)
Proof
  rpt strip_tac
  >> EQ_TAC >> gvs[v2n_lt_imp, v2n_lt_imp2]
QED*)

(*
Theorem zero_extend_n2v_v2n:
  ∀v.
    v ≠ [] ⇒
    zero_extend (LENGTH v) (n2v (v2n v)) = v
Proof
  Induct_on ‘v’ >> rpt strip_tac
  >- gvs[]
  >> Cases_on ‘v’ >> gvs[]
  >- (Cases_on ‘h’ >> EVAL_TAC)
  >> simp[Once zero_extend_suc]
  >>


  >> rw[]
  >- (Cases_on ‘h’ >> gvs[]

      >> simp[Once v2n]
      >> gvs[if_add_0_right]
      >> rw[]
      >> simp[zero_extend_def


              >> Cases_on ‘h’ >> gvs[bitify_def]
QED
              *)


(* -------------------------------------------------------------------------- *)
(* These four theorems are probably a little messy: ADD_DIV_LEFT_EQ,          *)
(* ADD_DIV_RIGHT_EQ, SUC_SUC_DIV_2, DIV_2_0. I say this because they are      *)
(* strictly less general than ADD_DIV_ADD_DIV. However, I found it difficult  *)
(* to use a more general theorem like ADD_DIV_ADD_DIV directly, so maybe they *)
(* are useful anyway.                                                         *)
(* -------------------------------------------------------------------------- *)
Theorem ADD_DIV_LEFT_EQ:
  ∀n m.
    0 < m ⇒
    (m + n) DIV m = n DIV m + 1
Proof
  rpt strip_tac
  >> ‘m = 1 * m’ by gvs[]
  >> pop_assum (fn th => PURE_REWRITE_TAC[Once th])
  >> gvs[ADD_DIV_ADD_DIV]
QED

Theorem boolify_acc:
  ∀a v.
    boolify a v = boolify [] v ⧺ a
Proof
  Induct_on ‘v’ >> rpt strip_tac >> gvs[]
  >- EVAL_TAC
  >> PURE_REWRITE_TAC[boolify_def]
  >> last_assum $ qspec_then ‘(h ≠ 0)::a’ assume_tac
  >> last_x_assum $ qspec_then ‘[h ≠ 0]’ assume_tac
  >> gvs[]
QED

Theorem ADD_DIV_RIGHT_EQ:
  ∀n m.
    0 < m ⇒
    (n + m) DIV m = n DIV m + 1
Proof
  rpt strip_tac
  >> gvs[ADD_COMM, ADD_DIV_LEFT_EQ]
QED

Theorem SUC_SUC_DIV_2:
  ∀n.
    SUC (SUC n) DIV 2 = (n DIV 2) + 1
Proof
  rpt strip_tac
  >> gvs[ADD1]
  >> gvs[ADD_DIV_RIGHT_EQ]
QED

Theorem DIV_2_0:
  ∀n.
    n DIV 2 = 0 ⇔ n = 0 ∨ n = 1
Proof
  rpt strip_tac
  >> REVERSE EQ_TAC >> gvs[]
  >- (rw[] >> EVAL_TAC)
  >> rpt strip_tac
  >> Cases_on ‘n’ >> gvs[]
  >> Cases_on ‘n'’ >> gvs[]
  >> gvs[SUC_SUC_DIV_2]
QED

Theorem v2n_tl:
  ∀bs.
    bs ≠ [] ⇒
    v2n (TL bs) = (v2n bs) - (if (HD bs) then 2 ** (LENGTH bs - 1) else 0)
Proof
  rpt strip_tac
  >> Cases_on ‘bs’ >> gvs[]
  >> gvs[v2n]
  >> rw[]
QED

Theorem v2n_empty[simp]:
  v2n [] = 0
Proof
  gvs[v2n]
QED

Theorem v2n_append:
  ∀bs bs'.
    v2n (bs ⧺ bs') = 2 ** (LENGTH bs') * (v2n bs) + v2n bs'
Proof
  rpt strip_tac
  >> Induct_on ‘bs’
  >- gvs[]
  >> rpt strip_tac
  >> gvs[v2n]
  >> rw[]
  >> gvs[EXP_ADD]
QED

Theorem v2n_snoc:
  ∀b bs.
    v2n (SNOC b bs) = 2 * (v2n bs) + if b then 1 else 0
Proof
  gvs[SNOC_APPEND]
  >> gvs[v2n_append]
  >> rpt strip_tac
  >> rw[v2n]
QED

Theorem v2n_front:
  ∀v.
    v ≠ [] ⇒
    v2n (FRONT v) = (v2n v) DIV 2
Proof
  rpt strip_tac
  >> sg ‘v2n v = v2n ((FRONT v) ⧺ [LAST v])’
  >- (gvs[APPEND_FRONT_LAST])
  >> gvs[]
  >> gvs[v2n_append]
  >> Cases_on ‘LAST v’ >> gvs[v2n]
QED

Theorem zero_extend_empty[simp]:
  ∀n.
    zero_extend n [] = REPLICATE n F
Proof
  rpt strip_tac
  >> Induct_on ‘n’
  >- EVAL_TAC
  >> gvs[zero_extend_suc, REPLICATE]
QED

Theorem v2n_suc_F[simp]:
  ∀v.
    v2n (F::v) = v2n v
Proof
  rpt strip_tac
  >> gvs[v2n]
QED

Theorem v2n_replicate_f[simp]:
  ∀n.
    v2n (REPLICATE n F) = 0
Proof
  rpt strip_tac
  >> Induct_on ‘n’ >> gvs[]
QED

Theorem HD_SNOC:
  ∀l ls.
    HD (SNOC l ls) = if ls = [] then l else HD ls
Proof
  rpt strip_tac
  >> Cases_on ‘ls’ >> gvs[]
QED

Theorem PAD_LEFT_0[simp]:
  ∀c bs. PAD_LEFT c 0 bs = bs
Proof
  rpt strip_tac
  >> gvs[PAD_LEFT]
QED

Theorem zero_extend_0[simp]:
  ∀bs.
    zero_extend 0 bs = bs
Proof
  rpt strip_tac
  >> gvs[zero_extend_def]
QED

Theorem zero_extend_equals_empty[simp]:
  ∀n bs.
    zero_extend n bs = [] ⇔ n = 0 ∧ bs = []
Proof
  rpt strip_tac
  >> Cases_on ‘n’ >> gvs[]
  >> gvs[zero_extend_suc]
  >> rw[]
  >> Cases_on ‘bs’ >> gvs[]
  >> Induct_on ‘n'’ >> gvs[zero_extend_suc]
QED

(* our vector must start with true because leading zeros have no impact on
  v2n but do increase the length of v *)
Theorem le_v2n:
  ∀v.
    2 ** (LENGTH v) ≤ v2n (T::v)
Proof
  rpt strip_tac
  >> Cases_on ‘v’ >> gvs[v2n]
QED
