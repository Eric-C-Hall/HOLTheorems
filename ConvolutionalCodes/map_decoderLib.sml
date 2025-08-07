structure map_decoderLib = struct 

open HolKernel Parse boolLib bossLib;

open simpLib;
open map_decoderTheory;
open probabilityTheory;
open extrealTheory;

(* -------------------------------------------------------------------------- *)
(* This is currently duplicated from map_decoderScript, which is undesirable, *)
(* but I'm not sure how to ensure that this will be visible both from within  *)
(* map_decoderScript, based on theorems defined within map_decoderScript, as  *)
(* well as outside it. If I defined it in map_decoderScript, then it cannot   *)
(* be accessed from outside. If I defined it outside, then it cannot both be  *)
(* dependent on map_decoderScript as well as having map_decoderScript         *)
(* dependent on it.                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Simpset which collects some commonly used theorems regarding MAP decoders. *)
(*                                                                            *)
(* Based on real_SS from realSimps.sml.                                       *)
(* -------------------------------------------------------------------------- *)
val map_decoder_SS =
SSFRAG
{
name = SOME"map_decoder",
ac = [],
congs = [],
convs = [],
dprocs = [],
filter = NONE,
rewrs = map
        (fn s => (SOME {Thy = "map_decoder", Name = s},
                  DB.fetch "map_decoder" s
                 )
        )
        ["event_input_bit_takes_value_is_event",
         "event_input_string_takes_value_is_event",
         "event_sent_string_takes_value_is_event",
         "event_received_string_takes_value_is_event",
         "event_input_bit_takes_value_nonzero_prob",
         "event_input_string_takes_value_nonzero_prob",
         "event_sent_string_takes_value_nonzero_prob",
         "event_received_string_takes_value_nonzero_prob",
         "event_sent_string_takes_value_nonzero_prob_explicit",
         "event_sent_string_takes_value_zero_prob",
         "event_input_string_and_received_string_take_values_is_event",
         "event_input_string_and_received_string_take_values_nonzero_prob",
         "event_input_string_takes_value_disjoint",
         "event_sent_string_takes_value_disjoint"
        ]
};

val ecc_prob_space_SS =
SSFRAG
{
name = SOME"ecc_prob_space",
ac = [],
congs = [],
convs = [],
dprocs = [],
filter = NONE,
rewrs = map
        (fn s => (SOME {Thy = "ecc_prob_space", Name = s},
                  DB.fetch "ecc_prob_space" s
                 )
        )
        ["ecc_bsc_prob_space_is_prob_space"
        ]
};

(* -------------------------------------------------------------------------- *)
(* My rewrites relevant to error-correcting codes that you will almost always *)
(* want to use, but have a precondition so I don't want to include them in    *)
(* the stateful simpset                                                       *)
(* -------------------------------------------------------------------------- *)
val ecc_ss = (srw_ss()) ++ map_decoder_SS ++ ecc_prob_space_SS;

(* -------------------------------------------------------------------------- *)
(* Add some rewrites from other libraries that you will almost always want to *)
(* use, but have preconditions so I don't want to include them in the         *)
(* stateful simpset                                                           *)
(* -------------------------------------------------------------------------- *)
val ecc2_ss = ecc_ss ++ rewrites[PROB_POSITIVE,
                                 PROB_FINITE,
                                 COND_PROB_BOUNDS,
                                 COND_PROB_FINITE];
                                
(* -------------------------------------------------------------------------- *)
(* Add some more rewrites that may be a bit more time-intensive, or you may   *)
(* not always want to use.                                                    *)
(* -------------------------------------------------------------------------- *)
val ecc3_ss = ecc2_ss ++ rewrites[mul_not_infty2,
                                  prob_zero_cond_prob_zero,
                                  PROB_ZERO_INTER,
                                  length_n_codes_ith_eq_codes,
                                  length_n_codes_ith_eq_codes_valid_inverse_codes,
                                  div_mul_refl_alt];

End

end