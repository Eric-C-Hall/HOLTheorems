open HolKernel Parse boolLib bossLib;

open recursive_parity_equationsTheory;

val _ = new_theory "turbo_codes";

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
    (* TODO: This definition is not complete *)
    ARB run_recursive_parity_equation (ps1, qs1) bs
End


(* -------------------------------------------------------------------------- *)
(* TODO: Is this at all helpful in defining the above or completely unhelpful?*)
(* -------------------------------------------------------------------------- *)
(*Definition parallel_convolutional_code_encode_def:
  parallel_convolutional_code_encode
  (ps1, qs1) (ps2, qs2) bs =
  (bs,
   convolve_recursive_parity_equation code1 bs,
   convolve_recursive_parity equation code2 bs)
End
 *)

(* TODO: define this*)
Definition decode_parallel_turbo_code_def:
  decode_parallel_turbo_code rs bs = ARB
End

(* -------------------------------------------------------------------------- *)
(* Encoding and decoding a recursive parity equation using the BCJR algorithm *)
(* will return the original data again                                        *)
(*                                                                            *)
(* TODO: complete this                                                        *)
(* -------------------------------------------------------------------------- *)
(*Theorem encode_decode_parallel_turbo_code:
  (encode_parallel_turbo_code rs) ∘
  (decode_parallel_turbo_code rs) = I
Proof
QED*)

(* -------------------------------------------------------------------------- *)
(* Ensure that the decoding procedure for a recursive parity equation encoder *)
(* implements an a posteriori encoder (TODO: check that I have my terminology *)
(* correct)                                                                   *)
(*                                                                            *)
(* TODO: complete this                                                        *)
(* -------------------------------------------------------------------------- *)
(*Theorem decode_parallel_turbo_code_a_posteriori:
  (decode_parallel_turbo_code rs)
Proof
QED*)


val _ = export_theory();
