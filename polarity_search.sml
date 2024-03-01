(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse DB;

(* -------------------------------------------------------------------------- *)
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
(*                                                                            *)
(*                                                                            *)
(* Term -> Term List * Term List                                              *)
(* -------------------------------------------------------------------------- *)
fun dest_polarity (t : term) (polarity : bool) : term list * term list =
    case (total dest_comb t) of
    NONE => ([t], [])
    | SOME (operator, term) => ([], [])

SOME (`$!`, t2) => ([(Term`a`)],[])
    | _ => ([], [])
    

strip_comb
test_term

dest_thy_const $ fst $ strip_comb test_term
dtc'

fst $ dest_comb $ fst $ dest_comb (Term`a /\ b`)


    case (total dest_forall t) of
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
    | SOME (t1 : term, t2 : term) => dest_polarity t2 polarity

case (total dest_exists t) of
             NONE => ([(Term`a == b`)], [(Term`b ==> a`)])
             | SOME (t1s : term, t2s : term) => dest_polarity (hd t2s) polarity
case (total dest_conj t) of
                      NONE => ([Term`a == b`], [])
                      | SOME (t1 : term, t2 : term) => dest_polarity t2 polarity

val test_term : term = (concl $ fst $ snd $ hd $ matchp (fn th => true) [])

val SOME (t1, t2) = total dest_forall test_term

dest_polarity test_term true

dest_comb test_term

dest_thy_type test_term

fun polarity_match (match_term : term) (th : thm) =
    let
      val theorem_term = concl th
      val WIP = dest_polarity_wip theorem_term
      val match_predicate = can ((ho_match_term [] empty_tmset) match_term)
    in
        can (find_term match_predicate) WIP
    end

matchp (polarity_match (Term`a == b`)) []

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

(*
fun matches pat th =
  can (find_term (can (match_primitive pat))) (concl th) ;
*)

can (find_term (can ((ho_match_term [] empty_tmset) pat))) (concl th) ;

(*
val match_primitive = ho_match_term [] empty_tmset
*)

(* matcher match_primitive [] (Term`a = SUC b`);*)



DB.match_primitive

(* matchp (fn th => can (find_term (can (match_primitive (Term`a = SUC b`)))) (concl th)) []; *)