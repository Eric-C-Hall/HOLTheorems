Theory range

Ancestors arithmetic pred_set

Libs dep_rewrite ConseqConv simpLib;

(* -------------------------------------------------------------------------- *)
(* The set containing the range of natural numbers in [n, ..., m)             *)
(*                                                                            *)
(* Does this definition already exist somewhere?                              *)
(* -------------------------------------------------------------------------- *)
Definition range_def:
  range n m = {i : num | n ≤ i ∧ i < m}
End

Theorem range_count_diff:
  ∀n m.
    range n m = count m DIFF count n
Proof
  rpt gen_tac
  >> simp[range_def, count_def, EXTENSION]
QED

Theorem finite_range[simp]:
  ∀n m.
    FINITE (range n m)
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[range_count_diff]
  >> irule FINITE_DIFF
  >> irule FINITE_COUNT
QED

Theorem count_inter[simp]:
  ∀n m.
    count n ∩ count m = count (MIN n m)
Proof
  rpt gen_tac
  >> simp[EXTENSION]
QED

Theorem card_range[simp]:
  ∀n m.
    CARD (range n m) = m - n
Proof
  rpt gen_tac
  >> PURE_ONCE_REWRITE_TAC[range_count_diff]
  >> DEP_PURE_ONCE_REWRITE_TAC[CARD_DIFF]
  >> simp[]
  >> simp[MIN_DEF]
QED

Theorem range_same[simp]:
  ∀n.
    range n n = ∅
Proof
  rpt gen_tac >> simp[range_def, EXTENSION]
QED
