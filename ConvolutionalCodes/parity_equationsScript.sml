open HolKernel Parse boolLib bossLib;

val _ = new_theory "parity_equations";

(* -------------------------------------------------------------------------- *)
(* This theory is currently unused. It houses code to do with the parity      *)
(* equations interpretation of convolutional codes.                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* CONVOLUTIONAL PARITY EQUATION ENCODING                                     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* A parity equation is represented as a bit-string of which bits in the      *)
(* window are included in the linear expression.                              *)
(*                                                                            *)
(* A parity equation can be equivalently represented as the same equation     *)
(* with an arbitary number of zeros after it, so any parity equation can be   *)
(* treated as a parity equation of longer length. Therefore, in situations    *)
(* where we are provided with multiple equations of different lengths, pad    *)
(* the shorter parity equations with F's at the end.                          *)
(* -------------------------------------------------------------------------- *)
Datatype:
  (* Placeholder while waiting for better parity equation definition *)
  parity_equation = <| temp_p : bool list; |>;

  (* Why doesn't the following work: *)
  (* parity_equation = bool list; *)
  (* parity_equation = (min$bool list$list); *)
  (* parity_equation = “:bool list”; *)
  (* parity_equation = “(:bool list)”; *)
  (* parity_equation = (“:min$bool list$list”); *)
End

(* type_of “a : bool list” *)

Definition test_parity_equation_def:
  test_parity_equation = <| temp_p := [T; T; T]|>
End

Definition test_parity_equation2_def:
  test_parity_equation2 = <| temp_p := [F; T; T]|>
End

Definition test_parity_equations_def:
  test_parity_equations = [test_parity_equation; test_parity_equation2]
End

(* -------------------------------------------------------------------------- *)
(* Returns the length of a parity equation                                    *)
(* -------------------------------------------------------------------------- *)
Definition parity_equation_length_def:
  parity_equation_length p = LENGTH p.temp_p
End

Theorem test_parity_equation_length:
  parity_equation_length test_parity_equation = 3 ∧
  parity_equation_length test_parity_equation2 = 3
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* Returns the maximum length of a set of parity equations                    *)
(* -------------------------------------------------------------------------- *)
Definition parity_equations_max_length_def:
  parity_equations_max_length [] = 0 ∧
  parity_equations_max_length (p::ps) = MAX (parity_equation_length p) (parity_equations_max_length ps)
End

Theorem test_parity_equations_max_length:
  parity_equations_max_length test_parity_equations = 3
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* Treats a bitstring as a parity equation, and applies it to a bitstring     *)
(* with a sufficiently large window length                                    *)
(*                                                                            *)
(* p::ps represents the bitstring that is being treated as a parity equation. *)
(* bs represents the bitstring that the parity equation is applied to.        *)
(* -------------------------------------------------------------------------- *)
Definition apply_bitstring_as_parity_equation_def:
  apply_bitstring_as_parity_equation [] bs = F ∧
  apply_bitstring_as_parity_equation (p::ps) (b::bs) = ((p ∧ b) ⇎ (apply_bitstring_as_parity_equation ps bs))
End

(* -------------------------------------------------------------------------- *)
(* Applies a single parity equation to a bitstring with a sufficiently large  *)
(* window length                                                              *)
(* -------------------------------------------------------------------------- *)
Definition apply_parity_equation_def:
  apply_parity_equation p bs = apply_bitstring_as_parity_equation p.temp_p bs
End

Theorem test_apply_parity_equation:
  apply_parity_equation <| temp_p := [T; F; T] |> [F; F; T] = T ∧
  apply_parity_equation <| temp_p := [F; F; F] |> [T; T; T] = F ∧
  apply_parity_equation <| temp_p := [T; T; T] |> [T; T; T] = T ∧
  apply_parity_equation <| temp_p := [T; T; T] |> [T; F; T] = F ∧
  apply_parity_equation <| temp_p := [T; T; T; F; F] |> [T; F; T; F; T] = F ∧
  apply_parity_equation <| temp_p := [T; F; T; F; T] |> [F; F; F; T; T] = T ∧
  apply_parity_equation <| temp_p := [T; T; T] |> [T; F; T; F; T] = F
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* Applies a bunch of parity equations to a bitstring with a sufficiently     *)
(* large window length                                                        *)
(* -------------------------------------------------------------------------- *)
Definition apply_parity_equations_def:
  apply_parity_equations [] bs = [] ∧
  apply_parity_equations (p::ps) bs = (apply_parity_equation p bs)::(apply_parity_equations ps bs)
End

(* -------------------------------------------------------------------------- *)
(* Takes a number of parity equations and a bitstring, and encodes the        *)
(* bitstring according to the parity equations                                *)
(* -------------------------------------------------------------------------- *)
Definition convolutional_parity_encode_def:
  convolutional_parity_encode ps bs =
  let
    window_length = parity_equations_max_length ps;
  in
    (* Note: if the window length is 0, then LENGTH bs < window_length will
       never be true and thus we will never terminate. Therefore, we also
       terminate if bs = []. *)
    if (LENGTH bs < window_length ∨ bs = []) then [] else
      let
        first_window = TAKE window_length bs;
        step_values = apply_parity_equations ps first_window;
        remaining_bitstring = DROP 1 bs;
        remaining_values = convolutional_parity_encode ps remaining_bitstring;
      in
        step_values ⧺ remaining_values
Termination
  WF_REL_TAC ‘measure (LENGTH ∘ SND)’
  >> gvs[]
  >> rpt strip_tac
  >> Cases_on ‘bs’ >> gvs[]
End

Theorem test_convolutional_parity_encode:
  convolutional_parity_encode test_parity_equations [F; F; F; T; T; F; T; F; T; T; T] = [F; F; T; T; F; F; F; T; F; T; T; T; F; T; F; F; T; F]
Proof
  EVAL_TAC
QED




(* -------------------------------------------------------------------------- *)
(* Function for converting from a list of parity equations to a corresponding *)
(* state machine                                                              *)
(* -------------------------------------------------------------------------- *)
Definition parity_equations_to_gen_state_machine_def:
  parity_equations_to_gen_state_machine ps =
  let
    num_parity_equations = LENGTH ps;
    window_length = parity_equations_max_length ps;
    memory_length = window_length - 1;
    num_memory_configurations = 2 ** memory_length;
  in
    <|
      states := {s | LENGTH s = memory_length} : (bool list) set;
      transition_fn := (λorigin.
                          <| destination := TL (SNOC origin.input origin.origin);
                             output := apply_parity_equations ps (SNOC origin.input origin.origin) |>
                       ) : (bool list) gen_transition_origin -> (bool list) gen_transition_destination;
      init := REPLICATE window_length F : (bool list);
      output_length := num_parity_equations : num;
    |>
End


val _ = export_theory();
