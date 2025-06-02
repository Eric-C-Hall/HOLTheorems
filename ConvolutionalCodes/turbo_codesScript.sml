open HolKernel Parse boolLib bossLib;

open recursive_parity_equationsTheory;

val _ = new_theory "turbo_codesScript";

(* -------------------------------------------------------------------------- *)
(* This is largely based on "Modern Coding Theory" by Tom Richardson and      *)
(* Rüdiger Urbanke.                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* An implementation of parallel turbo codes                                  *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* TODO: Encode the recursive parity equation in a way which is sensible, in  *)
(* particular with regards to the ininitialization and termination schemes    *)
(* -------------------------------------------------------------------------- *)
Definition encode_parallel_turbo_code_def:
  encode_parallel_turbo_code (ps1, qs1) (ps2, qs2) bs =
  let
    state_length =
    MAX (MAX (LENGTH ps1) (LENGTH qs1)) (MAX (LENGTH ps2) (LENGTH qs2));
    initial_state = replicate 
  in
    run_recursive_parity_equation (ps1, qs1) bs
End



Definition decode_recursive_parity_equation_def:
  decode_recursive_parity_equation rs bs = 
End

(* -------------------------------------------------------------------------- *)
(* Encoding and decoding a recursive parity equation using the BCJR algorithm *)
(* will return the original data again                                        *)
(* -------------------------------------------------------------------------- *)
Theorem encode_decode_recursive_parity_equation:
  (encode_recursive_parity_equation rs) ∘
  (decode_recursive_parity_equation rs) = I
Proof
QED


(* -------------------------------------------------------------------------- *)
(* Ensure that the decoding procedure for a recursive parity equation encoder *)
(* implements an a posteriori encoder (TODO: check that I have my terminology *)
(* correct)                                                                   *)
(* -------------------------------------------------------------------------- *)
Theorem decode_recursive_parity_equation_a_posteriori:
  (decode_recursive_parity_equation rs)
Proof
QED

val _ = export_theory();
