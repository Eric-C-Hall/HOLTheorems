Theory modeq_thms

Ancestors arithmetic divides fundamental list marker rich_list

Libs ConseqConv dep_rewrite;

(* -------------------------------------------------------------------------- *)
(* Helpful theorems to make working with modulo arithmetic easier.            *)
(*                                                                            *)
(* Are there already automatic tactics similar to decide_tac for modulo       *)
(* arithmetic somewhere?                                                      *)
(*                                                                            *)
(* Probably would make most sense to make modulo arithemetic based on         *)
(* integers rather than natural numbers so that we don't have to do weird     *)
(* stuff when subtractions lead to negative numbers, or based on thier own,   *)
(* modulo type. Probably exists somewhere.                                    *)
(* -------------------------------------------------------------------------- *)

Theorem MODEQ_ADD_BASE_LEFT:
  ∀n a b.
    MODEQ n a b ⇔ MODEQ n (a + n) b
Proof
  rpt gen_tac
  >> simp[MODEQ_THM]
  >> EQ_TAC >> strip_tac>> simp[]
  >> gvs[ADD_MODULUS_LEFT]
QED

Theorem MODEQ_ADD_BASE_RIGHT:
  ∀n a b.
    MODEQ n a b ⇔ MODEQ n a (b + n)
Proof
  metis_tac[MODEQ_ADD_BASE_LEFT, MODEQ_SYM]
QED

Theorem MODEQ_ADD_MULT_BASE_LEFT:
  ∀n a b c.
    MODEQ n a b ⇔ MODEQ n (a + c * n) b
Proof
  Induct_on ‘c’
  >- simp[]
  >> rpt gen_tac
  >> pop_assum $ qspecl_then [‘n’, ‘a’, ‘b’] assume_tac
  >> pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])
  >> simp[MULT_SUC]
  >> Q.SUBGOAL_THEN ‘a + (n + c * n) = (a + c * n) + n’
      (fn th => PURE_ONCE_REWRITE_TAC[th])
  >- simp[]
  >> simp[]
  >> simp[Cong LHS_CONG, Once MODEQ_ADD_BASE_LEFT]
QED

Theorem MODEQ_ADD_MULT_BASE_RIGHT:
  ∀n a b c.
    MODEQ n a b ⇔ MODEQ n a (b + c * n)
Proof
  metis_tac[MODEQ_ADD_MULT_BASE_LEFT, MODEQ_SYM]
QED

