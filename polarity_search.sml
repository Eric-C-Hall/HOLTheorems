(* Written by Eric Hall, under the guidance of Michael Norrish *)

(* Michael Norrish wrote the basis for dest_polarity, dtc', although there was also some modification *)

open HolKernel Parse DB Hol_pp;

val test_term : term = (concl $ fst $ snd $ hd $ matchp (fn th => true) [])
val test_term_2 : term = (concl $ fst $ snd $ el 3 $ matchp (fn th => true) [])
val test_term_3 : term = concl $ arithmeticTheory.DIV_DIV_DIV_MULT
val test_term_4 : term = concl $ arithmeticTheory.LESS_SUC_NOT
val test_term_5 : term = concl $ arithmeticTheory.LESS_ANTISYM
val test_term_6 : term = concl $ arithmeticTheory.num_CASES
val test_term_7 : term = concl $ quotientTheory.RIGHT_RES_FORALL_REGULAR

fun dtc' (t : term) =
    let val {Thy, Name, ...} = dest_thy_const t in
        SOME (Thy, Name)
    end handle HOL_ERR _ => NONE

fun tuple_list_map (f : 'a -> 'b) (tuple : 'a list * 'a list) =
    let
      val (t1, t2) = tuple
    in
      (map f t1, map f t2)
    end

fun tuple_list_concat tuple_1 tuple_2 : 'a list * 'a list =
    let
        val (a1, a2) = tuple_1
        val (b1, b2) = tuple_2
    in
        (a1 @ b1, a2 @ b2)
    end

(* -------------------------------------------------------------------------- *)
(* dest_polarity:                                                             *)
(*                                                                            *)
(* The general idea of this function is to split a term into its conclusion   *)
(* and its premises.                                                          *)
(*                                                                            *)
(* This function will be used to allow the user to search for theorems        *)
(* matching a certain pattern in either the premises or in the conclusion.    *)
(*                                                                            *)
(* More precisely, it splits a term into a set of "positive" terms and        *)
(* "negative" terms. (Thanks to Michael Norrish for this idea. I'm not sure   *)
(* whether or not he himself got the idea from someplace else). "positive"    *)
(* terms are essentially those which stand in the conclusion (e.g. p),        *)
(* whereas "negative" terms are essentially those for which the negation      *)
(* stands in the conclusion (e.g. ¬p). This characterisation derives from the *)
(* fact that a ==> b can be transformed into b \/ ¬a. Also, if we have a as a *)
(* premise, we can use the contrapositive to derive a theorem with ¬a in the  *)
(* conclusion, and similarly, if we have ¬a in the conclusion, we can use     *)
(* the contrapositive to derive a theorem with a in the premises.             *)
(*                                                                            *)
(* The positive terms are in a conjunction with each other (i.e. it is        *)
(* possible to prove a /\ b /\ c ... using the theorem.                       *)
(*                                                                            *)
(* The negative terms are in a disjunction with each other (i.e. it is        *)
(* possible to prove something meaningful if you know a \/ b \/ c ...         *)
(*                                                                            *)
(* Alternative general idea for the search function: break down into          *)
(* conjunctive normal form, negated terms are premises, non-negated terms are *)
(* conclusions.                                                               *)
(*                                                                            *)
(* Thanks also to Michael Norrish for writing the basis for the code for this *)
(* function and related functions                                             *)
(*                                                                            *)
(* Term -> Term List * Term List                                              *)
(*                                                                            *)
(* The first term list contains the positive terms, while the second term     *)
(* list contains the negative terms.                                          *)
(* -------------------------------------------------------------------------- *)
fun dest_polarity (t : term) (polarity : bool) : term list * term list =
    let
        val (f, xs) = strip_comb t
    in
        case (dtc' f) of
        (* ------------------------------------------------------------------*)
        (* Forall case:                                                      *)
        (*                                                                   *)
        (* Consider ∀x. (P(x) ⇒ Q(x)). The conclusion is true for all x.    *)
        (* The premises hold if there exists an x. So negative terms         *)
        (* should have ∃ appended to them while positive terms should        *)
        (* have ∀ appended to them.                                          *)
        (*                                                                   *)
        (* Consider also ∀x. ¬P(x). This can be treated as ∀x. P(x) ⇒ F.    *)
        (* Thus, we can derive false if there exists an x such that P(x).    *)
        (* So adding an ∃ also makes sense in this case.                     *)
        (* ------------------------------------------------------------------*)
        SOME ("bool", "!") =>
            (let
                val (bound_variable, quantified_expression) = dest_forall t
                val recursive_result  = dest_polarity quantified_expression polarity
                val (positive_terms, negative_terms) = recursive_result
                val mk_exists' = (curry mk_exists) bound_variable
                val mk_forall' = (curry mk_forall) bound_variable
            in
                (map mk_forall' positive_terms, map mk_exists' negative_terms)
            end)
        (* ----------------------------------------------------------------- *)
        (* Exists case:                                                      *)
        (*                                                                   *)
        (* Consider ∃x. (P(x) ⇒ Q(x)). There exists an x such that the      *)
        (* conclusion is true. We cannot guarantee that the premises are     *)
        (* true unless we know that for all x, P(x) holds. If we only know   *)
        (* P(x) for one choice of x, that isn't sufficient, because we might *)
        (* not have P(x) for the correct choice of x, as defined by the ∃    *)
        (* quantifier.                                                       *)
        (*                                                                   *)
        (* Consider ∃x. ¬P(x). This can be traeted as ∃x. P(x) ⇒ F.         *)
        (* Thus, we can derive F if we know that P(x) holds for every choice *)
        (* of x (but we cannot derive it if we know that it holds for just   *)
        (* one choice of x.)                                                 *)
        (* ----------------------------------------------------------------- *)
        | SOME ("bool", "?") =>
            (let
                val (bound_variable, quantified_expression) = dest_exists t
                val recursive_result = dest_polarity quantified_expression polarity
                val (positive_terms, negative_terms) = recursive_result
                val mk_exists' = (curry mk_exists) bound_variable
                val mk_forall' = (curry mk_forall) bound_variable
            in
                (map mk_exists' positive_terms, map mk_forall' negative_terms)
            end)
        (* ----------------------------------------------------------------- *)
        (* Not case:                                                         *)
        (*                                                                   *)
        (* Applying a not simply changes the polarity of the term            *)
        (* Note that the not doesn't need to added to the output term,       *)
        (* because it has already been taken into account by the changed     *)
        (* polarity.                                                         *)
        (* ----------------------------------------------------------------- *)
        | SOME ("bool", "~") =>
            (let
                val recursive_result = dest_polarity (dest_neg t) (not polarity)
            in
                (* tuple_list_map (mk_neg) *)
                recursive_result
            end)
        (* ----------------------------------------------------------------- *)
        (* And case:                                                         *)
        (*                                                                   *)
        (* Consider a => a' /\ b => b'. We ought to have the seperate terms  *)
        (* a and b as premises and the terms a' and b' as conclusions. If    *)
        (* either a or b is valid, we can deduce something meaningful. It is *)
        (* also possible to deduce either a' or b' given the correct premises*)
        (*                                                                   *)
        (* Thus, the resulting positive terms should include all positive    *)
        (* terms from each operand, and the resulting negative terms should  *)
        (* include all negative terms from each operand                      *)
        (*                                                                   *)
        (* Note: we could treat this as two separate theorms that are both   *)
        (* true.                                                             *)
        (* ------------------------------------------------------------------*)
        | SOME ("bool", "/\\") =>
            (let
                val (t1, t2) = dest_conj t
                val recursive_result_1 = dest_polarity t1 polarity
                val recursive_result_2 = dest_polarity t2 polarity
            in
                tuple_list_concat recursive_result_1 recursive_result_2                
            end)
        (* ----------------------------------------------------------------- *)
        (* Or case:                                                          *)
        (*                                                                   *)
        (* Consider a => a' \/ b => b'.                                      *)
        (*                                                                   *)
        (* This is equivalent to ¬(¬a' => ¬a /\ ¬b' => ¬b)                   *)
        (*                                                                   *)
        (* Thus, a is a positive term, and a' is a negative term             *)
        (*                                                                   *)
        (*                                                                   *)
        (*                                                                   *)
        (*                                                                   *)
        (*                                                                   *)
        (* ----------------------------------------------------------------- *)
        | SOME ("bool", "\\/") =>
            (let
                val (t1, t2) = dest_disj t
                val recursive_result_1 = dest_polarity t1 polarity
                val recursive_result_2 = dest_polarity t2 polarity
            in
                tuple_list_concat recursive_result_1 recursive_result_2
            end)
        | SOME ("min", "==>") =>
            (let
                val (t1, t2) = dest_imp t
                val recursive_result_1 = dest_polarity t1 polarity
                val recursive_result_2 = dest_polarity t2 polarity
                val swapped_recursive_result_1 = (snd recursive_result_1, fst recursive_result_1)
            in
                tuple_list_concat swapped_recursive_result_1 recursive_result_2
            end)
        | NONE => if polarity then ([t], []) else ([], [t])
        | _ => if polarity then ([t], []) else ([], [t])
    end handle HOL_ERR _ => (print("Error occurred destructing term: "); print (term_to_string t); print("\n"); if polarity then ([t], []) else ([], [t]));

dest_polarity test_term true;
dest_polarity test_term_2 true;
dest_polarity test_term_3 true;
dest_polarity test_term_4 true;
dest_polarity test_term_5 true;
dest_polarity test_term_6 true;
dest_polarity test_term_7 true;

fun polarity_match (polarity : bool) (match_term : term) (th : thm) =
    (let
      val theorem_term = concl th
      val polarity_terms = dest_polarity theorem_term true
      val match_predicate = can ((ho_match_term [] empty_tmset) match_term)
      val match_results = map (can (find_term match_predicate)) (if polarity then fst polarity_terms else snd polarity_terms)
    in
         List.exists (fn x => x) match_results
    end)

signature polarity_search = sig
    val polarity_search : bool -> term -> public_data list
end

structure polarity_search :> polarity_search = struct
    fun polarity_search (polarity : bool) (match_term : term) =
        matchp (polarity_match polarity match_term) []
end

polarity_search true `

(* -------------------------------------------------------------------------- *)
(* Useful match-related functions:                                            *)
(* ----------                                                                 *)
(* Hol_pp.sml                                                                 *)
(* ----------                                                                 *)
(* print_match                                                                *)
(*                                                                            *)
(* ----------                                                                 *)
(* DB.sml                                                                     *)
(* ----------                                                                 *)
(* matchp                                                                     *)
(* match_primitive                                                            *)
(* matcher                                                                    *)
(* match                                                                      *)
(* matches                                                                    *)
(*                                                                            *)
(* -------------                                                              *)
(* HolKernal.sml                                                              *)
(* -------------                                                              *)
(* ho_match_term                                                              *)
(* ho_match_term0                                                             *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Defined in DB.sml                                                          *)
(*                                                                            *)
(* fun matches pat th =                                                       *)
(*   can (find_term (can (match_primitive pat))) (concl th) ;                 *)
(* -------------------------------------------------------------------------- *)

(*
val match_primitive = ho_match_term [] empty_tmset
*)

(* matcher match_primitive [] (Term`a = SUC b`);*)

(* matchp (fn th => can (find_term (can (match_primitive (Term`a = SUC b`)))) (concl th)) []; *)