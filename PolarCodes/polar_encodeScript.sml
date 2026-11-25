(* ========================================================================= *)
(*   Edited and extended by Gemini (Google DeepMind AI agent):               *)
(*                                                                           *)
(*   Preserved polar_encode_def, polar_encode_channel_def, and               *)
(*   polar_encode_unit_test_1 unmodified. Added verified theorems for        *)
(*   2-way interleave/deinterleave roundtrips, bxor algebra and bijections,  *)
(*   polar_encode length preservation, dual-block butterfly identity         *)
(*   (polar_encode_append_interleave), involution (polar_encode_involutive), *)
(*   bijection on length_n_codes (2 ** n) (polar_encode_bij), and            *)
(*   GF(2)-linearity (polar_encode_bxor).                                    *)
(* ========================================================================= *)

Theory polar_encode

Ancestors arithmetic bitstring bxor_lemmas ecc_prob_space fundamental
          interleave list pair pred_set repeat_channel rich_list
          transform_input_channel

Libs dep_rewrite realLib;

(* -------------------------------------------------------------------------- *)
(* Based on "Channel polarization: A method for constructing                  *)
(* capacity-achieving codes for symmetric binary-input memoryless channels    *)
(* by Erdal Arıkan                                                            *)
(*                                                                            *)
(* Based on "Polar Codes: from theory to practice" by Mohammad Rowshan and    *)
(* Emanuele Viterbo                                                           *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Unlike in Arıkan's original Polar Codes paper, we use the computer science *)
(* convention of 0-indexed lists rather than the mathematical convention of   *)
(* 1-indexed lists                                                            *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Important theorems:                                                        *)
(* - Theorem 1: the channels polarize                                         *)
(* - Proposition 2: bound on probability of block error                       *)
(* - Theorem 4: asymptotic bound on block error probability with respect to N *)
(* - Encoding and decoding are both O(n log n)                                *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Polar encoding:                                                            *)
(* polar_encode = polar_encode (even_inputs bitwise_XOR odd_inputs) ++        *)
(*                polar_encode odd_inputs                                     *)
(*                                                                            *)
(* Undefined behaviour if length of input is not a power of two.              *)
(* -------------------------------------------------------------------------- *)
Definition polar_encode_def:
  polar_encode (inputs : bool list) =
  if LENGTH inputs ≤ 1 then inputs
  else
    let
      even_odd_inputs = deinterleave 2 inputs;
      even_inputs = EL 0 even_odd_inputs;
      odd_inputs = EL 1 even_odd_inputs;
    in
      polar_encode (bxor even_inputs odd_inputs) ++ polar_encode odd_inputs
Termination
  WF_REL_TAC ‘measure (LENGTH)’
  >> conj_tac
  >- (gen_tac >> strip_tac
      >> simp[length_el_deinterleave]
      >> rw[]
      (* 2 ≤ LENGTH inputs MOD 2 is a contradiction because anything mod 2 is
         less than 2. *)
      >> ‘F’ suffices_by strip_tac
      >> sg ‘LENGTH inputs MOD 2 < 2’
      >- simp[]
      >> simp[])
  >> gen_tac >> strip_tac
  >> pop_assum mp_tac >> PURE_ONCE_REWRITE_TAC[NOT_LE] >> disch_tac
  >> simp[bxor_length]
  >> simp[hd_deinterleave, el_deinterleave]
  >> simp[length_get_every_nth_element]
  >> Cases_on ‘LENGTH inputs MOD 2 = 0’
  >- simp[]
  >> Cases_on ‘LENGTH inputs MOD 2 = 1’              
  >- (simp[]
      (* It turns out to be easier to prove if we manually prove some small
         cases, which turn out to be kinda special cases. In particular, note
         that for LENGTH inputs = 2, we have
         LENGTH inputs DIV 2 + 1 ≤ LENGTH inputs, whereas we will end up
         wanting LENGTH inputs DIV 2 + 1 < LENGTH inputs *)
      >> Cases_on ‘LENGTH inputs = 2’
      >- gvs[]
      >> Cases_on ‘LENGTH inputs = 3’
      >- simp[]
      (* We want to prove that 1 < LENGTH inputs DIV 2, which will then get us
         LENGTH inputs DIV 2 + 1 < LENGTH inputs.
         This is easier to represent by breaking down the inequality we are
         trying to prove into two inqualities *)
      >> qsuff_tac ‘LENGTH inputs DIV 2 + 1 <
                    LENGTH inputs DIV 2 + LENGTH inputs DIV 2 ∧
                    LENGTH inputs DIV 2 + LENGTH inputs DIV 2 ≤
                    LENGTH inputs’
      >- simp[]
      >> conj_tac
      >- (simp[LT_ADD_LCANCEL]
          >> ‘3 < LENGTH inputs’ by simp[]
          >> gvs[]
          >> qsuff_tac ‘2 * 1 < 2 * (LENGTH inputs DIV 2)’
          >- simp[]
          >> PURE_ONCE_REWRITE_TAC[bitTheory.DIV_MULT_THM2]
          >> simp[])
      >> simp[GSYM TIMES2]
      >> simp[bitTheory.DIV_MULT_THM2]
     )
  >> ‘F’ suffices_by strip_tac
  >> sg ‘LENGTH inputs MOD 2 < 2’
  >- simp[]
  >> simp[]
End

(* -------------------------------------------------------------------------- *)
(* Combines polar encoding with a channel, resulting in                       *)
(*                                                                            *)
(* Does not handle any bit-freezing                                           *)
(* -------------------------------------------------------------------------- *)
Definition polar_encode_channel_def:
  polar_encode_channel (W : (bool,β) memoryless_channel) (num_inputs : num)
  = transform_input_channel polar_encode
                            (length_n_codes num_inputs)
                            (repeat_channel W num_inputs)
End

(* -------------------------------------------------------------------------- *)
(* Hand-written calculations indicate that polar_encode with the input:       *)
(*   [T;F;F;F;T;F;T;T]                                                        *)
(* Should have the output:                                                    *)
(*   [F;T;F;F;T;T;T;T]                                                        *)
(* Double check consistency of formal definition with hand calculations.      *)
(* -------------------------------------------------------------------------- *)
Theorem polar_encode_unit_test_1:
  polar_encode [T;F;F;F;T;F;T;T] = [F;T;F;F;T;T;T;T]
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------------------------- *)
(* Two-way interleave and deinterleave 2 structural and roundtrip lemmas      *)
(* -------------------------------------------------------------------------- *)

(* Base cases for interleaving two lists when either list is empty.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem interleave_two_nil[simp]:
  (∀ys. interleave [[]; ys] = []) ∧
  (∀xs. interleave [xs; []] = [])
Proof
  conj_tac >> gen_tac >> simp[Once interleave_def]
QED

(* Step rule for interleaving two non-empty lists.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem interleave_two_cons[simp]:
  ∀x xs y ys.
    interleave [x::xs; y::ys] = x :: y :: interleave [xs; ys]
Proof
  rpt gen_tac >> simp[Once interleave_def]
QED

(* Length of interleaving two equal-length lists.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem length_interleave_two:
  ∀xs ys.
    LENGTH xs = LENGTH ys ⇒
    LENGTH (interleave [xs; ys]) = 2 * LENGTH xs
Proof
  Induct_on ‘xs’ >> Cases_on ‘ys’ >> simp[]
QED

(* Distributivity of two-way interleave over list append for equal-length prefixes.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem interleave_two_append:
  ∀a1 a2 b1 b2.
    LENGTH a1 = LENGTH b1 ⇒
    interleave [a1 ++ a2; b1 ++ b2] =
      interleave [a1; b1] ++ interleave [a2; b2]
Proof
  Induct_on ‘a1’ >> Cases_on ‘b1’ >> simp[]
QED

(* Element-wise indexing of two-way interleave.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem el_interleave_two:
  ∀xs ys i.
    LENGTH xs = LENGTH ys ∧ i < 2 * LENGTH xs ⇒
    EL i (interleave [xs; ys]) =
      if EVEN i then EL (i DIV 2) xs else EL (i DIV 2) ys
Proof
  Induct_on ‘xs’ >> Cases_on ‘ys’ >> simp[]
  >> rpt gen_tac >> strip_tac
  >> Cases_on ‘i’ >- simp[]
  >> Cases_on ‘n’ >- simp[]
  >> simp[EVEN]
  >> ‘SUC (SUC n') = n' + 1 * 2’ by simp[]
  >> ‘SUC (SUC n') DIV 2 = SUC (n' DIV 2)’
       by (pop_assum SUBST1_TAC >> simp[ADD_DIV_RWT, ADD1])
  >> pop_assum SUBST1_TAC
  >> simp[]
  >> first_x_assum irule >> simp[]
QED

(* Two-element step rules for get_every_nth_element with stride 2.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem get_every_2nd_cons[simp]:
  (∀x y xs.
     get_every_nth_element (x::y::xs) 2 0 =
       x :: get_every_nth_element xs 2 0) ∧
  (∀x y xs.
     get_every_nth_element (x::y::xs) 2 1 =
       y :: get_every_nth_element xs 2 1)
Proof
  conj_tac >> rpt gen_tac
  >- (simp[get_every_nth_element_def]
      >> PURE_ONCE_REWRITE_TAC[ONE]
      >> simp[get_every_nth_element_def])
  >- (PURE_ONCE_REWRITE_TAC[ONE]
      >> simp[get_every_nth_element_def])
QED

(* Explicit 2-element list expansion of deinterleave 2.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem deinterleave_2_eq:
  ∀ls.
    deinterleave 2 ls =
      [get_every_nth_element ls 2 0; get_every_nth_element ls 2 1]
Proof
  gen_tac
  >> ‘COUNT_LIST 2 = [0; 1]’ by EVAL_TAC
  >> simp[deinterleave_def]
QED

(* Half-length lemma for the two branches of deinterleave 2 on an even-length list.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem length_deinterleave_2_half:
  ∀u k.
    LENGTH u = 2 * k ⇒
    LENGTH (EL 0 (deinterleave 2 u)) = k ∧
    LENGTH (EL 1 (deinterleave 2 u)) = k
Proof
  rpt strip_tac
  >> simp[length_el_deinterleave]
  >> ‘2 * k = k * 2’ by simp[]
  >> pop_assum SUBST1_TAC
  >> simp[MULT_DIV, MOD_EQ_0]
QED

(* Element-wise indexing of get_every_nth_element with stride 2.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem el_get_every_2nd:
  ∀k xs i.
    LENGTH xs = 2 * k ∧ i < k ⇒
    EL i (get_every_nth_element xs 2 0) = EL (2 * i) xs ∧
    EL i (get_every_nth_element xs 2 1) = EL (2 * i + 1) xs
Proof
  Induct_on ‘k’ >- simp[]
  >> rpt gen_tac >> strip_tac
  >> Cases_on ‘xs’ >- gvs[]
  >> Cases_on ‘t’ >- gvs[]
  >> gvs[]
  >> Cases_on ‘i’
  >- (PURE_ONCE_REWRITE_TAC[ONE] >> simp[])
  >> simp[MULT_CLAUSES]
  >> ‘2 * n + 2 = SUC (SUC (2 * n)) ∧ 2 * n + 3 = SUC (SUC (2 * n + 1))’ by simp[]
  >> simp[]
QED

(* Element-wise indexing of EL 0 and EL 1 of deinterleave 2.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem el_deinterleave_2:
  ∀xs k i.
    LENGTH xs = 2 * k ∧ i < k ⇒
    EL i (EL 0 (deinterleave 2 xs)) = EL (2 * i) xs ∧
    EL i (EL 1 (deinterleave 2 xs)) = EL (2 * i + 1) xs
Proof
  rpt strip_tac >> simp[el_deinterleave] >> metis_tac[el_get_every_2nd]
QED

(* Roundtrip: interleaving the 2-way deinterleaving of an even-length list recovers it.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem interleave_deinterleave_2:
  ∀xs.
    EVEN (LENGTH xs) ⇒
    interleave (deinterleave 2 xs) = xs
Proof
  gen_tac
  >> completeInduct_on ‘LENGTH xs’
  >> rpt strip_tac
  >> Cases_on ‘xs’ >- simp[deinterleave_2_eq]
  >> Cases_on ‘t’ >- gvs[EVEN]
  >> gvs[EVEN, deinterleave_2_eq]
QED

(* Unpacked 2-element roundtrip matching polar_encode_def's EL 0 / EL 1 pattern.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem interleave_el_deinterleave_2:
  ∀xs.
    EVEN (LENGTH xs) ⇒
    interleave [EL 0 (deinterleave 2 xs); EL 1 (deinterleave 2 xs)] = xs
Proof
  rpt strip_tac
  >> ‘[EL 0 (deinterleave 2 xs); EL 1 (deinterleave 2 xs)] = deinterleave 2 xs’
       by simp[deinterleave_2_eq]
  >> simp[interleave_deinterleave_2]
QED

(* Unpacked stride-2 roundtrip in terms of get_every_nth_element.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem interleave_get_every_2nd:
  ∀xs.
    EVEN (LENGTH xs) ⇒
    interleave [get_every_nth_element xs 2 0; get_every_nth_element xs 2 1] = xs
Proof
  rpt strip_tac
  >> drule interleave_deinterleave_2
  >> simp[deinterleave_2_eq]
QED

(* Stride-2 extraction on interleave [a; b] recovers a and b when LENGTH a = LENGTH b.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem get_every_2nd_interleave[simp]:
  ∀a b.
    LENGTH a = LENGTH b ⇒
    get_every_nth_element (interleave [a; b]) 2 0 = a ∧
    get_every_nth_element (interleave [a; b]) 2 1 = b
Proof
  Induct_on ‘a’ >> Cases_on ‘b’ >> simp[]
QED

(* Roundtrip: 2-way deinterleaving of two interleaved equal-length lists recovers them.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem deinterleave_2_interleave[simp]:
  ∀a b.
    LENGTH a = LENGTH b ⇒
    deinterleave 2 (interleave [a; b]) = [a; b]
Proof
  rpt strip_tac >> simp[deinterleave_2_eq]
QED

(* First component of deinterleave 2 on interleave [a; b].
   Written by Gemini (Google DeepMind AI agent) *)
Theorem el_0_deinterleave_2_interleave[simp]:
  ∀a b.
    LENGTH a = LENGTH b ⇒
    EL 0 (deinterleave 2 (interleave [a; b])) = a
Proof
  rpt strip_tac >> simp[deinterleave_2_interleave]
QED

(* Second component of deinterleave 2 on interleave [a; b].
   Written by Gemini (Google DeepMind AI agent) *)
Theorem el_1_deinterleave_2_interleave[simp]:
  ∀a b.
    LENGTH a = LENGTH b ⇒
    EL 1 (deinterleave 2 (interleave [a; b])) = b
Proof
  rpt strip_tac >> simp[deinterleave_2_interleave]
QED

(* Two-way interleave is a bijection from pairs of length-k bitstrings to length-(2 * k) bitstrings.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem BIJ_interleave_two:
  ∀k. BIJ (λ(l0, l1). interleave [l0; l1])
          (length_n_codes k × length_n_codes k)
          (length_n_codes (2 * k))
Proof
  gen_tac >> simp[BIJ_IFF_INV]
  >> conj_tac >- simp[FORALL_PROD, length_interleave_two]
  >> qexists_tac ‘λ(ls : bool list). (get_every_nth_element ls 2 0, get_every_nth_element ls 2 1)’
  >> rpt conj_tac
  >- (qx_gen_tac ‘x’ >> strip_tac
      >> drule length_deinterleave_2_half
      >> simp[deinterleave_2_eq])
  >- simp[FORALL_PROD]
  >- (qx_gen_tac ‘x’ >> strip_tac
      >> ‘EVEN (LENGTH x)’ by (simp[] >> metis_tac[EVEN_DOUBLE])
      >> simp[interleave_get_every_2nd])
QED

(* Distributivity of stride-2 extraction over append when the left list has even length.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem get_every_2nd_append_even:
  ∀xs ys.
    EVEN (LENGTH xs) ⇒
    get_every_nth_element (xs ++ ys) 2 0 =
      get_every_nth_element xs 2 0 ++ get_every_nth_element ys 2 0 ∧
    get_every_nth_element (xs ++ ys) 2 1 =
      get_every_nth_element xs 2 1 ++ get_every_nth_element ys 2 1
Proof
  gen_tac
  >> completeInduct_on ‘LENGTH xs’
  >> rpt strip_tac
  >> Cases_on ‘xs’ >> simp[]
  >> Cases_on ‘t’ >- gvs[EVEN]
  >> gvs[EVEN]
QED

(* Distributivity of deinterleave 2 components over append when the left list has even length.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem deinterleave_2_append_even:
  ∀xs ys.
    EVEN (LENGTH xs) ⇒
    EL 0 (deinterleave 2 (xs ++ ys)) =
      EL 0 (deinterleave 2 xs) ++ EL 0 (deinterleave 2 ys) ∧
    EL 1 (deinterleave 2 (xs ++ ys)) =
      EL 1 (deinterleave 2 xs) ++ EL 1 (deinterleave 2 ys)
Proof
  rpt strip_tac >> simp[deinterleave_2_eq, get_every_2nd_append_even]
QED

(* -------------------------------------------------------------------------- *)
(* Bitwise XOR algebraic and bijection lemmas on length_n_codes n             *)
(* -------------------------------------------------------------------------- *)

(* Right-cancellation of bxor on equal-length bitstrings.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bxor_inv_right:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    bxor (bxor bs cs) cs = bs
Proof
  rpt strip_tac >> metis_tac[bxor_comm, bxor_inv]
QED

(* Self-XOR produces all-F bitstring of the same length.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bxor_self:
  ∀bs. bxor bs bs = REPLICATE (LENGTH bs) F
Proof
  Induct_on ‘bs’ >> simp[]
QED

(* Associativity of bxor on equal-length bitstrings.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bxor_assoc:
  ∀as bs cs.
    LENGTH as = LENGTH bs ∧ LENGTH bs = LENGTH cs ⇒
    bxor (bxor as bs) cs = bxor as (bxor bs cs)
Proof
  Induct_on ‘as’ >> Cases_on ‘bs’ >> Cases_on ‘cs’ >> simp[bxor_length]
  >> rpt strip_tac
  >> Cases_on ‘h’ >> Cases_on ‘h'’ >> Cases_on ‘h''’ >> simp[]
QED

(* Bitwise XOR on the left with a fixed length-n vector is a bijection on length_n_codes n.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bxor_bij:
  ∀n bs.
    LENGTH bs = n ⇒
    BIJ (bxor bs) (length_n_codes n) (length_n_codes n)
Proof
  rpt strip_tac >> simp[BIJ_IFF_INV]
  >> conj_tac >- simp[bxor_length]
  >> qexists_tac ‘bxor bs’
  >> simp[bxor_length, bxor_inv]
QED

(* Bitwise XOR on the right with a fixed length-n vector is a bijection on length_n_codes n.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem bxor_right_bij:
  ∀n cs.
    LENGTH cs = n ⇒
    BIJ (λbs. bxor bs cs) (length_n_codes n) (length_n_codes n)
Proof
  rpt strip_tac >> simp[BIJ_IFF_INV]
  >> conj_tac >- simp[bxor_length]
  >> qexists_tac ‘λbs. bxor bs cs’
  >> simp[bxor_length, bxor_inv_right]
QED

(* Stride-2 extraction commutes with bxor on equal-length bitstrings.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem get_every_2nd_bxor:
  ∀xs ys.
    LENGTH xs = LENGTH ys ⇒
    get_every_nth_element (bxor xs ys) 2 0 =
      bxor (get_every_nth_element xs 2 0) (get_every_nth_element ys 2 0) ∧
    get_every_nth_element (bxor xs ys) 2 1 =
      bxor (get_every_nth_element xs 2 1) (get_every_nth_element ys 2 1)
Proof
  gen_tac
  >> completeInduct_on ‘LENGTH xs’
  >> rpt gen_tac >> strip_tac >> gvs[PULL_FORALL]
  >> qx_gen_tac ‘ys’ >> strip_tac
  >> Cases_on ‘xs’ >> Cases_on ‘ys’ >> gvs[]
  >> Cases_on ‘t’ >> Cases_on ‘t'’ >> gvs[]
  >- simp[get_every_nth_element_def]
  >> simp[length_get_every_nth_element]
QED

(* Two-way deinterleaving commutes componentwise with bxor on equal-length bitstrings.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem deinterleave_2_bxor:
  ∀xs ys.
    LENGTH xs = LENGTH ys ⇒
    EL 0 (deinterleave 2 (bxor xs ys)) =
      bxor (EL 0 (deinterleave 2 xs)) (EL 0 (deinterleave 2 ys)) ∧
    EL 1 (deinterleave 2 (bxor xs ys)) =
      bxor (EL 1 (deinterleave 2 xs)) (EL 1 (deinterleave 2 ys))
Proof
  rpt strip_tac >> simp[deinterleave_2_eq, get_every_2nd_bxor]
QED

(* -------------------------------------------------------------------------- *)
(* Polar encoding length, dual-block, involution, bijection, and linearity    *)
(* -------------------------------------------------------------------------- *)

(* Polar encoding preserves list length for any input bitstring.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_length_any:
  ∀u. LENGTH (polar_encode u) = LENGTH u
Proof
  gen_tac
  >> completeInduct_on ‘LENGTH u’
  >> rpt strip_tac >> gvs[PULL_FORALL]
  >> Cases_on ‘LENGTH u ≤ 1’
  >- simp[Once polar_encode_def]
  >> CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [polar_encode_def])))
  >> simp[LET_THM, deinterleave_2_eq]
  >> qabbrev_tac ‘e = get_every_nth_element u 2 0’
  >> qabbrev_tac ‘o_in = get_every_nth_element u 2 1’
  >> ‘LENGTH u MOD 2 < 2’ by simp[]
  >> ‘LENGTH e = LENGTH u DIV 2 + (if 0 < LENGTH u MOD 2 then 1 else 0) ∧
      LENGTH o_in = LENGTH u DIV 2’
       by simp[Abbr ‘e’, Abbr ‘o_in’, length_get_every_nth_element]
  >> ‘LENGTH (bxor e o_in) = LENGTH e’
       by (simp[bxor_length, MAX_DEF] >> rw[])
  >> ‘LENGTH u = (LENGTH u DIV 2) * 2 + LENGTH u MOD 2’
       by metis_tac[DIVISION, DECIDE “0 < 2n”]
  >> ‘LENGTH e + LENGTH o_in = LENGTH u ∧
      LENGTH (bxor e o_in) < LENGTH u ∧
      LENGTH o_in < LENGTH u’
       by (rw[] >> decide_tac)
  >> first_assum (qspec_then ‘bxor e o_in’ mp_tac)
  >> first_x_assum (qspec_then ‘o_in’ mp_tac)
  >> simp[]
QED

(* Polar encoding preserves power-of-two block length 2 ** n.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_length:
  ∀n u. LENGTH u = 2 ** n ⇒ LENGTH (polar_encode u) = 2 ** n
Proof
  rpt strip_tac >> simp[polar_encode_length_any]
QED

(* Dual-block identity for polar_encode on concatenated equal power-of-two blocks:
   (u1, u2) G_{2N} = interleave [u1 G_N + u2 G_N; u2 G_N].
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_append_interleave:
  ∀n u1 u2.
    LENGTH u1 = 2 ** n ∧ LENGTH u2 = 2 ** n ⇒
    polar_encode (u1 ++ u2) =
      interleave [bxor (polar_encode u1) (polar_encode u2); polar_encode u2]
Proof
  Induct_on ‘n’
  >- (rpt strip_tac
      >> Cases_on ‘u1’ >> gvs[]
      >> Cases_on ‘u2’ >> gvs[]
      >> Cases_on ‘h’ >> Cases_on ‘h'’ >> EVAL_TAC)
  >> rpt strip_tac
  >> ‘0n < 2 ** n’ by simp[ZERO_LESS_EXP]
  >> ‘LENGTH u1 = 2 * 2 ** n ∧ LENGTH u2 = 2 * 2 ** n’ by gvs[EXP]
  >> ‘EVEN (LENGTH u1)’ by (simp[] >> metis_tac[EVEN_DOUBLE])
  >> ‘¬(LENGTH u1 ≤ 1) ∧ ¬(LENGTH u2 ≤ 1) ∧ ¬(LENGTH (u1 ++ u2) ≤ 1)’
       by (simp[EXP] >> decide_tac)
  >> qabbrev_tac ‘e1 = get_every_nth_element u1 2 0’
  >> qabbrev_tac ‘o1 = get_every_nth_element u1 2 1’
  >> qabbrev_tac ‘e2 = get_every_nth_element u2 2 0’
  >> qabbrev_tac ‘o2 = get_every_nth_element u2 2 1’
  >> ‘LENGTH e1 = 2 ** n ∧ LENGTH o1 = 2 ** n ∧ LENGTH e2 = 2 ** n ∧ LENGTH o2 = 2 ** n’
       by (qspecl_then [‘u1’, ‘2 ** n’] mp_tac length_deinterleave_2_half
           >> qspecl_then [‘u2’, ‘2 ** n’] mp_tac length_deinterleave_2_half
           >> simp[deinterleave_2_eq, Abbr ‘e1’, Abbr ‘o1’, Abbr ‘e2’, Abbr ‘o2’])
  >> sg ‘polar_encode (u1 ++ u2) =
         polar_encode (bxor e1 o1 ++ bxor e2 o2) ++ polar_encode (o1 ++ o2)’
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [polar_encode_def]))
      >> simp[LET_THM, deinterleave_2_eq, get_every_2nd_append_even,
              Abbr ‘e1’, Abbr ‘o1’, Abbr ‘e2’, Abbr ‘o2’]
      >> DEP_PURE_ONCE_REWRITE_TAC[fundamentalTheory.bxor_append]
      >> simp[])
  >> pop_assum SUBST1_TAC
  >> sg ‘polar_encode u1 = polar_encode (bxor e1 o1) ++ polar_encode o1’
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [polar_encode_def]))
      >> simp[LET_THM, deinterleave_2_eq, Abbr ‘e1’, Abbr ‘o1’])
  >> pop_assum SUBST1_TAC
  >> sg ‘polar_encode u2 = polar_encode (bxor e2 o2) ++ polar_encode o2’
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [polar_encode_def]))
      >> simp[LET_THM, deinterleave_2_eq, Abbr ‘e2’, Abbr ‘o2’])
  >> pop_assum SUBST1_TAC
  >> ‘LENGTH (bxor e1 o1) = 2 ** n ∧ LENGTH (bxor e2 o2) = 2 ** n’ by simp[bxor_length]
  >> qabbrev_tac ‘A1 = polar_encode (bxor e1 o1)’
  >> qabbrev_tac ‘A2 = polar_encode (bxor e2 o2)’
  >> qabbrev_tac ‘B1 = polar_encode o1’
  >> qabbrev_tac ‘B2 = polar_encode o2’
  >> ‘LENGTH A1 = 2 ** n ∧ LENGTH A2 = 2 ** n ∧ LENGTH B1 = 2 ** n ∧ LENGTH B2 = 2 ** n’
       by metis_tac[polar_encode_length]
  >> ‘polar_encode (bxor e1 o1 ++ bxor e2 o2) = interleave [bxor A1 A2; A2]’
       by metis_tac[]
  >> ‘polar_encode (o1 ++ o2) = interleave [bxor B1 B2; B2]’
       by metis_tac[]
  >> simp[]
  >> DEP_PURE_ONCE_REWRITE_TAC[GSYM interleave_two_append]
  >> simp[bxor_length]
  >> DEP_PURE_ONCE_REWRITE_TAC[fundamentalTheory.bxor_append]
  >> simp[]
QED

(* Polar encoding is an involution (G_N * G_N = I_N over GF(2)) on blocks of length 2 ** n.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_involutive:
  ∀n u. LENGTH u = 2 ** n ⇒ polar_encode (polar_encode u) = u
Proof
  Induct_on ‘n’
  >- (rpt strip_tac
      >> ‘LENGTH u ≤ 1’ by simp[]
      >> ‘polar_encode u = u’ by simp[Once polar_encode_def]
      >> simp[])
  >> rpt strip_tac
  >> ‘0n < 2 ** n’ by simp[ZERO_LESS_EXP]
  >> ‘LENGTH u = 2 * 2 ** n’ by gvs[EXP]
  >> ‘EVEN (LENGTH u)’ by (simp[] >> metis_tac[EVEN_DOUBLE])
  >> ‘¬(LENGTH u ≤ 1)’ by (simp[EXP] >> decide_tac)
  >> qabbrev_tac ‘e = get_every_nth_element u 2 0’
  >> qabbrev_tac ‘o_in = get_every_nth_element u 2 1’
  >> ‘LENGTH e = 2 ** n ∧ LENGTH o_in = 2 ** n’
       by (qspecl_then [‘u’, ‘2 ** n’] mp_tac length_deinterleave_2_half
           >> simp[deinterleave_2_eq, Abbr ‘e’, Abbr ‘o_in’])
  >> ‘LENGTH (bxor e o_in) = 2 ** n’ by simp[bxor_length]
  >> sg ‘polar_encode u = polar_encode (bxor e o_in) ++ polar_encode o_in’
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [polar_encode_def]))
      >> simp[LET_THM, deinterleave_2_eq, Abbr ‘e’, Abbr ‘o_in’])
  >> pop_assum SUBST1_TAC
  >> qabbrev_tac ‘v1 = polar_encode (bxor e o_in)’
  >> qabbrev_tac ‘v2 = polar_encode o_in’
  >> ‘LENGTH v1 = 2 ** n ∧ LENGTH v2 = 2 ** n’ by metis_tac[polar_encode_length]
  >> DEP_PURE_ONCE_REWRITE_TAC[polar_encode_append_interleave]
  >> conj_tac >- (qexists_tac ‘n’ >> simp[])
  >> ‘polar_encode v1 = bxor e o_in ∧ polar_encode v2 = o_in’ by metis_tac[]
  >> simp[bxor_inv_right, Abbr ‘e’, Abbr ‘o_in’, interleave_get_every_2nd]
QED

(* Polar encoding is a bijection on length_n_codes (2 ** n).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_bij:
  ∀n. BIJ polar_encode (length_n_codes (2 ** n)) (length_n_codes (2 ** n))
Proof
  gen_tac >> simp[BIJ_IFF_INV]
  >> conj_tac >- simp[polar_encode_length]
  >> qexists_tac ‘polar_encode’
  >> simp[polar_encode_length, polar_encode_involutive]
QED

(* GF(2)-linearity of polar_encode: polar_encode (bxor u1 u2) = bxor (polar_encode u1) (polar_encode u2).
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_bxor:
  ∀n u1 u2.
    LENGTH u1 = 2 ** n ∧ LENGTH u2 = 2 ** n ⇒
    polar_encode (bxor u1 u2) = bxor (polar_encode u1) (polar_encode u2)
Proof
  Induct_on ‘n’
  >- (rpt strip_tac
      >> Cases_on ‘u1’ >> gvs[]
      >> Cases_on ‘u2’ >> gvs[]
      >> Cases_on ‘h’ >> Cases_on ‘h'’ >> EVAL_TAC)
  >> rpt strip_tac
  >> ‘0n < 2 ** n’ by simp[ZERO_LESS_EXP]
  >> ‘LENGTH u1 = 2 * 2 ** n ∧ LENGTH u2 = 2 * 2 ** n’ by gvs[EXP]
  >> ‘LENGTH (bxor u1 u2) = 2 * 2 ** n’ by simp[bxor_length]
  >> ‘¬(LENGTH u1 ≤ 1) ∧ ¬(LENGTH u2 ≤ 1) ∧ ¬(LENGTH (bxor u1 u2) ≤ 1)’
       by (simp[EXP] >> decide_tac)
  >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [polar_encode_def]))
  >> CONV_TAC (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [polar_encode_def])))
  >> CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [polar_encode_def])))
  >> simp[LET_THM, deinterleave_2_eq, get_every_2nd_bxor]
  >> qabbrev_tac ‘e1 = get_every_nth_element u1 2 0’
  >> qabbrev_tac ‘o1 = get_every_nth_element u1 2 1’
  >> qabbrev_tac ‘e2 = get_every_nth_element u2 2 0’
  >> qabbrev_tac ‘o2 = get_every_nth_element u2 2 1’
  >> ‘LENGTH e1 = 2 ** n ∧ LENGTH o1 = 2 ** n ∧ LENGTH e2 = 2 ** n ∧ LENGTH o2 = 2 ** n’
       by (qspecl_then [‘u1’, ‘2 ** n’] mp_tac length_deinterleave_2_half
           >> qspecl_then [‘u2’, ‘2 ** n’] mp_tac length_deinterleave_2_half
           >> simp[deinterleave_2_eq, Abbr ‘e1’, Abbr ‘o1’, Abbr ‘e2’, Abbr ‘o2’])
  >> sg ‘bxor (bxor e1 e2) (bxor o1 o2) = bxor (bxor e1 o1) (bxor e2 o2)’
  >- (simp[LIST_EQ_REWRITE, bxor_length, el_bxor]
      >> rw[] >> Cases_on ‘EL x e1’ >> Cases_on ‘EL x e2’
      >> Cases_on ‘EL x o1’ >> Cases_on ‘EL x o2’ >> simp[])
  >> pop_assum SUBST1_TAC
  >> ‘LENGTH (bxor e1 o1) = 2 ** n ∧ LENGTH (bxor e2 o2) = 2 ** n’ by simp[bxor_length]
  >> ‘LENGTH (polar_encode (bxor e1 o1)) = 2 ** n ∧
      LENGTH (polar_encode (bxor e2 o2)) = 2 ** n ∧
      LENGTH (polar_encode o1) = 2 ** n ∧
      LENGTH (polar_encode o2) = 2 ** n’ by metis_tac[polar_encode_length]
  >> DEP_PURE_ONCE_REWRITE_TAC[fundamentalTheory.bxor_append]
  >> simp[]
QED

(* Polar encoding maps the all-zero (all-F) vector to itself.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_replicate_F:
  ∀n. polar_encode (REPLICATE (2 ** n) F) = REPLICATE (2 ** n) F
Proof
  gen_tac
  >> qspecl_then [‘n’, ‘REPLICATE (2 ** n) F’, ‘REPLICATE (2 ** n) F’]
       mp_tac polar_encode_bxor
  >> simp[bxor_self, polar_encode_length_any]
QED

(* Empty and singleton boundary behavior of polar_encode.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_nil_sing:
  polar_encode [] = [] ∧
  ∀b. polar_encode [b] = [b]
Proof
  conj_tac >> rpt gen_tac >> simp[Once polar_encode_def]
QED

(* Arikan 2x2 basic polarization kernel F = [1 0; 1 1] action of polar_encode on 2-bit blocks.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_2:
  ∀b0 b1. polar_encode [b0; b1] = [b0 ⇎ b1; b1]
Proof
  Cases >> Cases >> EVAL_TAC
QED

(* Injectivity of polar_encode on power-of-two blocks of length 2 ** n.
   Written by Gemini (Google DeepMind AI agent) *)
Theorem polar_encode_inj:
  ∀n u1 u2.
    LENGTH u1 = 2 ** n ∧ LENGTH u2 = 2 ** n ⇒
    (polar_encode u1 = polar_encode u2 ⇔ u1 = u2)
Proof
  rpt strip_tac >> EQ_TAC >> strip_tac >> simp[]
  >> metis_tac[polar_encode_involutive]
QED

