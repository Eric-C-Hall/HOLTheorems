Theory ecc_probability

(* Want to prove: if the probability of an arbitrary bit flipping is less than
   0.5, and the probabilities of each bit flipping are i.i.d, then if the
   hamming distance between x and y is less than or equal to the hamming
   distance between x and z, then if x is sent through the noisy channel, there
   is a higher probability of y being the message recieved than z *)

(* At some point it would be good to prove this kind of thing using probability
   theory, but I haven't done it for now because probability theory is a
   complicated, heavyweight instrument, and it would involve using complicated
   definitions to use, and it is unclear if this would actually provide a more
   useful result than simply minimizing the number of errors, because the final
   result may actually be less easily interpretable. *)
