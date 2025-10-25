Theory easy_prob

(* A dependency on ecc_prob_space may be too much, but it's more convenient to have access
   to too much than to too little. When this is more developed, reduce dependencies. *)

Ancestors ecc_prob_space

Libs extreal_to_realLib ConseqConv dep_rewrite simpLib realLib;


(* -------------------------------------------------------------------------- *)
(* If I have two events that each refer to a substring of disjoint bits, I    *)
(* want to be able to prove that they are independent of each other.          *)
(*                                                                            *)
(* Requirements: the probability function I'm using treats each bit as an     *)
(* independent random variable.                                               *)
(*                                                                            *)
(* In particular, I'm working with binomial distributions, which treats each  *)
(* bit as an independent and identically distributed random variable.         *)
(*                                                                            *)
(* I should prove that sym_noise_mass_func is equivalent to a binomial        *)
(* distribution.                                                              *)
(*                                                                            *)
(* I should prove that length_n_codes_uniform_prob_space is equivalent to a   *)
(* binomial distribution.                                                     *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* Would be cool to have automatic theorem proving over binomial              *)
(* distributions.                                                             *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* I want to be easily able to treat substrings of my α list as products of   *)
(* each other                                                                 *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* We have                                                                    *)
(* (α list -> bool, α list -> bool -> bool, α list -> bool -> extreal)        *)
(*                                                                            *)
(* All lists in the space have the same size.                                 *) 
(*                                                                            *) 
(* This is effectively the combination of two similar spaces which have all   *) 
(* lists in those spaces                                                      *) 
(*                                                                            *) 
(* The resulting space is isomorphic to the product space of these two        *) 
(* spaces, assuming that                                                      *) 
(*                                                                            *) 
(* They combine in the same way as                                            *) 
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(*Definition combine_prod_measure_space_def:
  combine_prod_measure_space (sp : (α list # α list) m_space) =
  (space
  )  
End

Theorem sym_noise_prob_space_cross:
  ∀n1 n2 m p.
    m = n1 + n2 ⇒
    ARB =
    sym_noise_prob_space n1 p × sym_noise_prob_space n2 p
Proof
QED

Theorem sym_noise_prob_space_:
n1 + n2 = m ⇒
        prob (sym_noise_prob_space m p) S =
        prob (sym_noise_prob_space n1 p) ()
Proof
QED*)


(*
∀m p k ns_pre.
   0 ≤ p ∧ p ≤ 1 ∧ LENGTH ns_pre = k ⇒
   ∑ (sym_noise_mass_func p)
   {ns | LENGTH ns = m ∧ TAKE k ns = ns_pre}
   = sym_noise_mass_func p ns_pre: proof

There is a bijection between this set and    

The sum of all these elements is equal to the sum of applying the function
to the prefix multiplied by applying the function 
   
I want to be able to easily say that the sum of all these 
   
*)

(* Proof ended up being based on the fact that sym_noise_mass_func (_ ++ _) = sym_noise_mass_func _ * sym_noise_mass_func _, and using the fact that the set we were summing over all had the same prefix prepended to it, thus we could use a theorem of extreals to move the IMAGE in the set to a concatenation in the function, and then it was straightforward from there. 
 *)

(* -------------------------------------------------------------------------- *)
(* In particular, in a conditional probability, it would be nice to be able   *)
(* to use the fact that is "given" to narrow down the event we are taking the *)
(* probability of, somehow. Like, we are assuming the given fact, right, and  *)
(* we want to find the appropriate probability. In particular, a conditional  *)
(* probability can be seen as saying "in every scenario where we have _, we   *)
(* have a _ probability of the first event"                                   *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Choosing any selection of k bits from anywhere in the string should be     *)
(* easily calculable as p^k probability                                       *)
(* -------------------------------------------------------------------------- *)
