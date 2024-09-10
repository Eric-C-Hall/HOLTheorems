
(* REAL_ARITH_TAC *)

(* ARB *)

(* EQ_LENGTH_INDUCT_TAC *)

(* When writing tactics, it may be useful to use nested lambda expressions, and use the arguments from the outer lambda expression in the inner lambda expression. e.g.

pop_assum (fn th => pop_assum (fn th2 => assume_tac th >> assume_tac th2))

It may also be useful to provide something from the outer function as an argument to a recursive inner function, for example:

(Though this doesn't work exactly, as it will place the theorem at every stage instead of just the bottom, it shows the idea)
val bury_assumption_helper th = pop_assum (fn th2 => bury_assumption_helper th >> assume_tac th >> assume_tac th2)
val bury_assumption = pop_assum (fn th => bury_asusmption_helper th)
*)

(* If you want a function which takes an argument or a recursive function, use fun instead of val. Because val will require it to be a lambda expression, in whcih case, inside the lambda expresison, teh value hasn't been defined yet, causing an error when it attempts to access the outer variable name outside the inner lambda expression *)

(* Maybe it's a good idea to induct on the length of a list sometimes. Strong induction. *)

(* when using search, Cntl-W will add the next few characters of the currently selected text to the search. Allows you to choose what to search by selecting it from the text rather than typing it out manually. *)