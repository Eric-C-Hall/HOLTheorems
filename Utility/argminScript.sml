Theory argmin

Ancestors infnum

Libs useful_tacticsLib dep_rewrite;

(* -------------------------------------------------------------------------- *)
(* Infnum argmin for pairs of elements                                        *)
(* -------------------------------------------------------------------------- *)
Definition argmin2_def:
  argmin2 f x y = if (f x < f y) then x else y
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
(* functions argmin_mem and argmin_inle                                   *)
(* -------------------------------------------------------------------------- *)
(* Would it be better for this to return an option type?                      *)
(* -------------------------------------------------------------------------- *)
Definition argmin_def:
  argmin f (x::xs) = if (xs = [])
                       then x
                       else argmin2 f x (argmin f xs)
End

Theorem argmin_singleton[simp]:
  ∀f x.
  argmin f [x] = x
Proof
  simp[argmin_def] 
QED

Theorem argmin_cons_cons[simp]:
  ∀f x x' xs.
  argmin f (x::x'::xs) = argmin2 f x (argmin f (x'::xs))
Proof
  gvs[argmin_def]
QED

Theorem argmin2_le[simp]:
  ∀f x y z.
  f (argmin2 f x y) ≤ f z ⇔ f x ≤ f z ∨ f y ≤ f z
Proof
  rw[argmin2_def, EQ_IMP_THM]
  >> metis_tac[inlt_inle, inle_TRANS]
QED

(* -------------------------------------------------------------------------- *)
(* First defining property of argmin: the result is an element of the list  *)
(* that we took the argmin over                                               *)
(* -------------------------------------------------------------------------- *)
Theorem argmin_mem[simp]:
  ∀f ls.
  ls ≠ [] ⇒
  MEM (argmin f ls) ls
Proof
  rpt strip_tac
  >> Induct_on ‘ls’ >> gvs[]
  >> rpt strip_tac
  >> gns[argmin_def]
  >> gns[argmin2_def]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’ >> gns[]
  >> Cases_on ‘ls’ >> gns[]
  >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
  >> Cases_on ‘b’ >> gns[]
QED

(* -------------------------------------------------------------------------- *)
(* Second defining property of argmin: the result has a lower value of f    *)
(* than any other member of the list we took the argmin over                  *)
(* -------------------------------------------------------------------------- *)
Theorem argmin_inle[simp]:
  ∀f ls l.
    MEM l ls ⇒
    f (argmin f ls) ≤ f l
Proof
  Induct_on ‘ls’ >> rw[argmin_def]
  >> simp[]
QED

(* -------------------------------------------------------------------------- *)
(* Associativity of argmin2                                                 *)
(* -------------------------------------------------------------------------- *)
Theorem argmin2_assoc:
  ∀f x y z.
    argmin2 f x (argmin2 f y z) = argmin2 f (argmin2 f x y) z
Proof
  rpt strip_tac
  >> gns[argmin2_def]
  >> rpt (qmatch_goalsub_abbrev_tac ‘if b then _ else _’ >> Cases_on ‘b’ >> gns[])
  >> rpt (qmatch_asmsub_abbrev_tac ‘if b then _ else _’ >> Cases_on ‘b’ >> gns[])
  >> Cases_on ‘f x’ >> Cases_on ‘f y’ >> Cases_on ‘f z’ >> gns[]
QED

(* -------------------------------------------------------------------------- *)
(* Taking the argmin of two appended nonempty lists is equivalent to          *)
(* individually taking the argmin of each list, and then choosing the lesser  *)
(* of the results.                                                            *)
(* -------------------------------------------------------------------------- *)
Theorem argmin_append:
  ∀f xs ys.
  xs ≠ [] ∧
  ys ≠ [] ⇒
  argmin f (xs ⧺ ys) = argmin2 f (argmin f xs) (argmin f ys)
Proof
  Induct_on ‘xs’ >> gns[argmin_def]
  >> rpt strip_tac
  >> Cases_on ‘xs = []’ >> gns[]
  >> gns[argmin2_assoc]
QED

(* -------------------------------------------------------------------------- *)
(* If two functions are the same on every element of the list, then the       *)
(* result of applying argmin on those functions over the list will be the     *)
(* same, even if the functions are not identical on elements which are not    *)
(* contained in the list.                                                     *)
(* -------------------------------------------------------------------------- *)
Theorem argmin_domain:
  ∀f g ls.
  ls ≠ [] ∧
  (∀l. MEM l ls ⇒ f l = g l) ⇒
  argmin f ls = argmin g ls 
Proof
  rpt strip_tac
  >> Induct_on ‘ls’
  >- gvs[]
  >> rpt strip_tac
  >> gvs[argmin_def]
  >> Cases_on ‘ls’ >> gvs[]
  >> gvs[argmin2_def]
  >> pop_assum $ qspec_then ‘argmin g (h'::t)’ assume_tac
  >> Cases_on ‘argmin g (h'::t) = h'’ >> gvs[]
  >> swap_assums
  >> pop_assum (fn th => DEP_PURE_ONCE_REWRITE_TAC [th])
  >> gvs[]
  >> disj2_tac
  >> qspecl_then [‘g’, ‘h'::t’] assume_tac argmin_mem
  >> gvs[Excl "argmin_mem"]
QED

Theorem argmin_mem_inle:
  ∀f l ls.
    MEM l ls ⇒ f (argmin f ls) ≤ f l
Proof
  rpt strip_tac
  >> Induct_on ‘ls’ >> gvs[]
QED

Theorem argmin_inle_mem:
  ∀f ls i.
    ls ≠ [] ⇒
    (f (argmin f ls) ≤ i ⇔ ∃l. MEM l ls ∧ f l ≤ i)
Proof
  rpt strip_tac
  >> EQ_TAC
  >- (rpt strip_tac
      >> qexists ‘argmin f ls’
      >> gvs[])
  >> rpt strip_tac
  >> drule_all inlet_TRANS
  >> rpt strip_tac
  >> gvs[]
QED
