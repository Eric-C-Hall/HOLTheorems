structure useful_tacticsLib = struct 

open HolKernel Parse boolLib bossLib;

(* -------------------------------------------------------------------------- *)
(* This seems like a particularly useful function that could potentially be   *)
(* added to HOL, although I haven't spent much time polishing it              *)
(*                                                                            *)
(* Todo: check whether or not this handles multiple implications correctly.   *)
(* Should probably work on the innermost implication rather than the          *)
(* outermost? Handle there-exists correctly.                                  *)
(* -------------------------------------------------------------------------- *)
fun GCONTRAPOS th = GEN_ALL (CONTRAPOS (SPEC_ALL th));

val Cases_on_if_goal = qmatch_goalsub_abbrev_tac ‘if jwlifmn then _ else _’ >> Cases_on ‘jwlifmn’;

val Cases_on_if_asm = qmatch_asmsub_abbrev_tac ‘if jwlifmn then _ else _’ >> Cases_on ‘jwlifmn’;

val imp_prove = qmatch_asmsub_abbrev_tac ‘jwlifmn ⇒ _’ >> sg ‘jwlifmn’ >> asm_simp_tac bool_ss [Abbr ‘jwlifmn’];

val conj_prove = qmatch_goalsub_abbrev_tac ‘jwlifmn ∧ _’ >> sg ‘jwlifmn’ >> asm_simp_tac bool_ss [Abbr ‘jwlifmn’];

fun with_all_in_goal t = rpt (pop_assum mp_tac) >> t >> rpt disch_tac;

(* I don't think this works, th is still at the top at the time when t is run *)
fun ignoring_top t = pop_assum (fn th => (t >> assume_tac th))

fun assume_at th n = (if n = 0 then assume_tac th else pop_assum (fn th2 => assume_at th (n - 1) >> assume_tac th2));

fun assume_bottom th = ASSUM_LIST (fn ths => assume_at th (length ths));
val bury_assum = pop_assum assume_bottom;

val duplicate_assum = pop_assum (fn th => NTAC 2 (assume_tac th));

val swap_assums = pop_assum (fn th => pop_assum (fn th2 => assume_tac th >> assume_tac th2));

fun delete_nth_assumption n = (if (n = 0) then pop_assum kall_tac else pop_assum (fn th => delete_nth_assumption (n - 1) >> assume_tac th))

val EXT_ALL_TAC = rpt (irule EQ_EXT >> gen_tac)

(* TODO: write a function to negate both sides of an if and only if statement, even in the presence of quantifiers *)

end