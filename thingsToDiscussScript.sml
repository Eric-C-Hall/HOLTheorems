(* Written by Eric Hall *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "thingsToDiscuss";

(* Completed code for finding input required to pass between two states *)

(* Added placeholder testing values *)

(* Completed Viterbi decode definition *)

(* Rewrote main theorem *)

(* Wrote basic hamming distnance theorems *)

(* Unit tests for viterbi trellis data *)

(* Issue: could not compute due to choice fuction, therefore modified to use a specific choice so as to provide a process for computation *)



(* The following has an unclear error:

   SPEC “example_state_machine” viterbi_trellis_data_def

   The following also:

   SPECL [“example_state_machine”, “test_path”, “2”, “4”] viterbi_trellis_data_def

   when viterbi_trellis_data_def has the following defintion:

   Definition viterbi_trellis_data_def:
  viterbi_trellis_data m bs s 0 : α viterbi_node_datatype =
  (if s = m.init then
     <| num_errors := N0; prev_state := NONE |>
   else <| num_errors := INFINITY; prev_state := NONE |>) ∧
  viterbi_trellis_data m bs s (SUC t) : α viterbi_node_datatype =
  let
    relevant_input = TAKE m.output_length (DROP (t * m.output_length) bs);
    get_num_errors = λr. (viterbi_trellis_data m bs r.origin t).num_errors +
                         N (hamming_distance (m.transition_fn r).output relevant_input);
    origin_leads_to_s = λr. ((m.transition_fn r).destination = s);
    best_origin =  @r. origin_leads_to_s r ∧
                       ∀r2. origin_leads_to_s r2 ⇒
                            get_num_errors r ≤ get_num_errors r2;
  in
    <| num_errors := get_num_errors best_origin;
       prev_state := SOME best_origin.origin |>
End
 *)

(* Working on parity equation implementation of convolutional codes *)

(* Bringing out WF theorems and donotexpand theorems into their own sublibraries *)

(* Proving termination condition *)


val _ = export_theory();


