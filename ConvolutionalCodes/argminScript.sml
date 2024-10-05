
open HolKernel Parse boolLib bossLib;

val _ = new_theory "argmin";

open infnumTheory;

(* -------------------------------------------------------------------------- *)
(* Infnum argmin for pairs of elements                                        *)
(* -------------------------------------------------------------------------- *)
Definition inargmin2_def:
  inargmin2 f x y = if (f x < f y) then x else y
End

(* -------------------------------------------------------------------------- *)
(* Infnum argmin                                                              *)
(*                                                                            *)
(* Undefined if there are no elements in the list.                            *)
(*                                                                            *)
(* Defined using an if statement instead of having two definitions, one for   *)
(* the argument f [x] and one for the argument f (x::xs), because if it were  *)
(* defined that way, the second definition would be automatically expanded    *)
(* out to a definition in terms of the arguments f (v5::v6::xs) in order to   *)
(* avoid conflicts with the definition in terms of the arguments f (x::[]). I *)
(* find this new definition ugly, since I don't necessarily want to be        *)
(* breaking down the tail into its own head and tail.                         *)
(*                                                                            *)
(* This function can alternatively be defined as returning the element which  *)
(* satisfies the two following defining properties:                           *)
(* - it is an element of the input list                                       *)
(* - f applied to this element is minimal, in the sense that it is less than  *)
(*   or equal to f applied to an arbitrary element of the list.               *)
(*                                                                            *)
(* However, the above definition would be non-constructive, and would suffer  *)
(* from issues such as:                                                       *)
(* - How would we evaluate which element to pick? If we wanted to use         *)
(*   EVAL_TAC to compute the specific argmin element, we wouldn't be able to  *)
(*   do so.                                                                   *)
(* - which specific element do we pick? If we don't have information about    *)
(*   which element is picked, this may make it harder to prove things. If we  *)
(*   pick elements in a nice, patterned but arbitrary way, for example,       *)
(*   always choosing earlier instances over later instances, that property    *)
(*   may be handy in later proofs, even if not entirely principled based on   *)
(*   the concept of an argmin.                                                *)
(*                                                                            *)
(* This is why the following constructive definition is used instead, which   *)
(* provides an easy process for calulating the specific result for a given    *)
(* list and function.                                                         *)
(*                                                                            *)
(* However, the non-constructive properties are useful and proven in the      *)
(* functions inargmin_mem and inargmin_inle                                   *)
(* -------------------------------------------------------------------------- *)
Definition inargmin_def:
  inargmin f (x::xs) = if (xs = [])
                       then x
                       else inargmin2 f x (inargmin f xs)
End

(* -------------------------------------------------------------------------- *)
(* First defining property of inargmin: the result is an element of the list  *)
(* that we took the argmin over                                               *)
(* -------------------------------------------------------------------------- *)
Theorem inargmin_mem:
  ∀f ls.
  ls ≠ [] ⇒
  MEM (inargmin f ls) ls
Proof
  rpt strip_tac
  >> Induct_on ‘ls’ >> gvs[]
  >> rpt strip_tac
  >> gns[inargmin_def]
  >> gns[inargmin2_def]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’ >> gns[]
  >> Cases_on ‘ls’ >> gns[]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’ >> gns[]
QED

(* -------------------------------------------------------------------------- *)
(* Second defining property of inargmin: the result has a lower value of f    *)
(* than any other member of the list we took the argmin over                  *)
(* -------------------------------------------------------------------------- *)
Theorem inargmin_inle:
  ∀f l ls.
  MEM l ls ⇒
  f (inargmin f ls) ≤ f l
Proof
  rpt strip_tac
  >> Induct_on ‘ls’ >> gns[]
  >> rpt gen_tac
  >> rpt disch_tac
  >> gvs[]
  >- (gns[inargmin_def]
      >> Cases_on ‘ls’ >> gns[]
      >> gns[inargmin2_def]
      >> qmatch_asmsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gns[])
  >> gns[inargmin_def]
  >> qmatch_asmsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’ >> gns[]
  >> gns[inargmin2_def]
  >> qmatch_asmsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’ >> gns[]
  >> Cases_on ‘f l’ >> Cases_on ‘f h’ >> Cases_on ‘f (inargmin f ls)’ >> gns[]
QED

(* -------------------------------------------------------------------------- *)
(* Associativity of inargmin2                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem inargmin2_assoc:
  ∀f x y z.
  inargmin2 f x (inargmin2 f y z) = inargmin2 f (inargmin2 f x y) z
Proof
  rpt strip_tac
  >> gns[inargmin2_def]
  >> rpt (qmatch_goalsub_abbrev_tac ‘if b then _ else _’ >> Cases_on ‘b’ >> gns[])
  >> rpt (qmatch_asmsub_abbrev_tac ‘if b then _ else _’ >> Cases_on ‘b’ >> gns[])
  >> Cases_on ‘f x’ >> Cases_on ‘f y’ >> Cases_on ‘f z’ >> gns[]
QED

(* -------------------------------------------------------------------------- *)
(* Taking the argmin of two appended nonempty lists is equivalent to          *)
(* individually taking the argmin of each list, and then choosing the lesser  *)
(* of the results.                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem inargmin_append:
  ∀f xs ys.
  xs ≠ [] ∧
  ys ≠ [] ⇒
  inargmin f (xs ⧺ ys) = inargmin2 f (inargmin f xs) (inargmin f ys)
Proof
  Induct_on ‘xs’ >> gns[inargmin_def]
  >> rpt strip_tac
  >> Cases_on ‘xs = []’ >> gns[]
  >> gns[inargmin2_assoc]
QED

val _ = export_theory();
