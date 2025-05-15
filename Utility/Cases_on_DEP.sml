(* Cases_on_precondition (lhs o #2 o dest_imp) (FREEZE_THEN (ONCE_REWRITE_TAC o single)) gen_partite_ea_fg_add_edges_for_function_node0; *)

fun Cases_on_precondition f ttac th0 (asl, w) = 
  let val th = SPEC_ALL th0
      val pat = f (concl th)
  in
    case gen_find_term (fn (_, t) => total (match_term pat) t) w of
      NONE => raise mk_HOL_ERR "foo" "TRYPC" "No match"
    | SOME (tmsig, tysig) => 
      let
        val th' = th |> INST_TYPE tysig |> INST tmsig
        val (p, _) = dest_imp (concl th')
      in 
        ASM_CASES_TAC p THENL [
          first_assum (ttac o MATCH_MP th'),
          ALL_TAC
        ]
      end     
   end (asl, w)