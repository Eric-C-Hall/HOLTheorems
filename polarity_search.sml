(* Written by Eric Hall, under the guidance of Michael Norrish *)

(* Michael Norrish wrote the basis for dest_polarity, dtc', although there was also some modification *)

open HolKernel Parse DB;

val test_term : term = (concl $ fst $ snd $ hd $ matchp (fn th => true) [])
val test_term_2 : term = (concl $ fst $ snd $ el 3 $ matchp (fn th => true) [])
val test_term_3 : term = concl $ arithmeticTheory.DIV_DIV_DIV_MULT
val test_term_4 : term = concl $ ConseqConv.COND_CLAUSES_TF

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

(* -------------------------------------------------------------------------- *)
(* dest_polarity:                                                             *)
(*                                                                            *)
(* The general idea of this function is to split a term into its conclusion   *)
(* and its premises.                                                          *)
(*                                                                            *)
(* This function will be used to allow the user to search for theorems        *)
(* matching a certain pattern in either the premises or in the conclusion.   *)
(*                                                                            *)
(* More precisely, it splits a term into a set of "positive" terms and        *)
(* "negative" terms. (Thanks to Michael Norrish for this idea. I'm not sure   *)
(* whether or not he himself got the idea from someplace else). "positive"    *)
(* terms are essentially those which stand in the conclusion (e.g. p),        *)
(* whereas "negative" terms are essentially those for which the negation      *)(* stands in the conclusion (e.g. ¬p). This characterisation derives from the *)
(*fact that a ==> b can be transformed into b \/ ¬a. Also, if we have a as a  *)(* premise, we can use the contrapositive to derive a theorem with ¬a in the  *)(*  conclusion, and similarly, if we have ¬a in the conclusion, we can use    *)(* the contrapositive to derive a theorem with a in the premises.             *)
(*                                                                            *)
(* Thanks also to Michael Norrish for writing the basis for the code for this *)
(* function and related functions                                             *)
(*                                                                            *)
(* Term -> Term List * Term List                                              *)
(* -------------------------------------------------------------------------- *)
fun dest_polarity (t : term) (polarity : bool) : term list * term list =
    let
        val (f, xs) = strip_comb t
    in
        case (dtc' f) of
        SOME ("bool", "!") =>
            (let
                val (bound_variable, quantified_expression) = dest_forall t
                val recursive_result  = dest_polarity quantified_expression polarity
            in
                tuple_list_map ((curry mk_forall) bound_variable) recursive_result
            end) 
        | SOME ("bool", "?") =>
            (let
                val (bound_variable, quantified_expression) = dest_exists t
                val recursive_result = dest_polarity quantified_expression polarity
            in
                tuple_list_map ((curry mk_exists) bound_variable) recursive_result          
            end)
        | SOME ("bool", "~") =>
            (let
                val (
            in
          
            end)
        | SOME ("bool", "/\\") => ([t], [])
        | SOME ("bool", "\\/") => ([t], [])
        | SOME ("bool", "==>") => ([t], [])
        | NONE => ([t], [])
        | _ => ([t], [])
    end

dest_polarity test_term true
dest_polarity test_term_3 true


snd $ dest_forall $ snd $ dest_forall test_term_3
mk_forall $ dest_forall test_term_3

dtc' $ fst $ strip_comb $ hd $ snd $ strip_comb test_term_3

    (*case (total dest_forall t) of
    NONE =>
       (case (total dest_exists t) of
        NONE =>
           (case (total dest_conj t) of
            NONE =>
               (case (total dest_disj t) of
                NONE =>
                   (case (total dest_disj t) of
                    NONE => ([], [])
                    | SOME (t1 : term, t2 : term) => dest_polarity t1 polarity)
                | SOME (t1 : term, t2 : term) => dest_polarity t1 polarity)
            | SOME (t1 : term, t2 : term) => dest_polarity t1 polarity)
        | SOME (t1 : term, t2 : term) => dest_polarity t2 polarity)
    | SOME (t1 : term, t2 : term) => dest_polarity t2 polarity *)

fun polarity_match (match_term : term) (th : thm) =
    let
      val theorem_term = concl th
      val WIP = dest_polarity_wip theorem_term
      val match_predicate = can ((ho_match_term [] empty_tmset) match_term)
    in
        can (find_term match_predicate) WIP
    end

(*HolKernal.sml, DB.sml, Hol_pp.sml *)

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
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

can (find_term (can ((ho_match_term [] empty_tmset) pat))) (concl th) ;

(*
val match_primitive = ho_match_term [] empty_tmset
*)

(* matcher match_primitive [] (Term`a = SUC b`);*)



DB.match_primitive

(* matchp (fn th => can (find_term (can (match_primitive (Term`a = SUC b`)))) (concl th)) []; *)