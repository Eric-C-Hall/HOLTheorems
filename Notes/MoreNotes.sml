(* To pull quantifiers to front and convert multiple implications to ands: SIMP_RULE bool_ss [AND_IMP_INTRO, PULL_FORALL] PROD_IMAGE_INSERT *)

(* May be a good idea to use theorem provers to poke holes in existing practice.
 In a way, disproving existing ideas is the "productive" and "novel" half of using theorem provers. Replicating pre-existing results is less novel *)

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

(* C-x C-space: select everything up until top*)

(* USE_SG_THEN *)

(* RES_TAC *)

(* Make sure to keep code clean. If there's a clear, straightforward change you can make to improve the cleanliness of the code, it's probably a good idea to do it *)

(* PATH: instructs ubuntu in which directories to find executables. Set in .profile or .bashrc *)

(* It appears as though you can queue up commands in the HOL interactive thing *)

(* Use qabbrev_tac even if the abbreviation you want to make isn't yet contained as a pattern in the goal or assumptions, e.g. if you just want to define a new name for convenience *)

(* if you want to hide it manually (and unhide later), this might work (?): qpat_abbrev_tac`snoc = SNOC` *)

(* Underneath all HOL type definitions is a call to new_type_definition, which asks the caller to show that a specified subset of an existing type is inhabited. If it is, then the call introduces functions mapping from the subset to the new type (the "abs"), and from the new type to the subset (the "rep"). Based on the bare minimum returned by new_type_definition there are other functions that prove more properties of the rep and abs functions. I think this is what is going on here. *)

(* I recommend doing help "new_type_definition" and help "define_new_type_bijections" for detailed information. I think rich_new_type is bundling up a bunch of boilerplate commonly used to move from the initial introduction of a new type to a useful set of theorems for working with that type. *)

(* Use "Theorem foo[local]:" to define a local theorem *) 

(* The "graph" type seems to correspond to the subset of the "graphrep" type which consists of well-formed graphs*)

(* Automatically simplify a theorem: SIMP_RULE (srw_ss()) [] *)

(* The following allows the subgoal to be added without being automatically split: Q.SUBGOAL_THEN ‘x = x' \/ x = x''’ assume_tac *)

(* AllCaseEqs(), fmap_EXT *)

(* M-h M-t: display elapsed times for HOL commands *)