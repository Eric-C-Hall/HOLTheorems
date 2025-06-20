(* Written by Eric Hall, under the guidance of Michael Norrish *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "map_decoder";

(* -------------------------------------------------------------------------- *)
(* The bitwise MAP decoder is defined to be the choice of x_i which maximizes *)
(* the probability of x_i given the received message. This probability is     *)
(* taken with respect to a prior probability distribution on the originally   *)
(* sent data and a probability distribution on the noise which is added to    *)
(* the message.                                                               *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)

(* -------------------------------------------------------------------------- *)
Definition map_decoder_bitwise_def:
  map_decoder_bitwise = prob p e
End


val _ = export_theory();
