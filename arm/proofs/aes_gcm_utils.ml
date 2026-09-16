(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared definitions, lemmas and tactics for the software-pipelined AES-GCM *)
(* x4 kernel proofs (the encrypt _swp_S and decrypt _swp variants).          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "common/fips197.ml";;
needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;
needs "arm/proofs/consttime.ml";;

(* ------------------------------------------------------------------------- *)
(* Some specification concepts.                                              *)
(* ------------------------------------------------------------------------- *)

let ctr_block = new_definition
 `ctr_block nonce ctr :int128 = word_join (nonce:96 word) (word ctr:int32)`;;

(**** This is the form that we actually XOR little-endian bytes with
 **** in the algorithm, so we switch back out of NIST big-endian
 ****)

let aes_ctr_block = new_definition
 `aes_ctr_block nonce rk i =
    word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 2)) rk)`;;

(* The i-th ciphertext block: keystream XOR plaintext - little-endian *)

let cipher_block = new_definition
 `cipher_block nonce rk inblock i =
    word_xor (aes_ctr_block nonce rk i) (inblock i)`;;

(* The NIST convention is big-endian, however *)

let nist_cipher_block = new_definition
 `nist_cipher_block nonce rk inblock i =
        word_reversefields 8 (cipher_block nonce rk inblock i)`;;

(* Restricted Htable predicate: only the entries the kernel actually reads.
   The x4-unrolled loop uses H^1..H^4 and their Karatsuba mid terms (the
   first 6 entries = offsets 0..80 of the full htable_mem layout).
   The tail loop only uses H^1..H^2 (offsets 0..32) but we assert all four
   here since the outer loop needs them and the precondition is shared. *)

let htable_mem_4 = new_definition
 `htable_mem_4 (h:int128) (ptr:int64) (s:armstate) <=>
  read (memory :> bytes128 ptr) s =
    byteswap128(h_power h 0) /\
  read (memory :> bytes128 (word_add ptr (word 16))) s =
    word_join (karatsuba_mid(h_power h 1) : 64 word)
              (karatsuba_mid(h_power h 0) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 32))) s =
    byteswap128(h_power h 1) /\
  read (memory :> bytes128 (word_add ptr (word 48))) s =
    byteswap128(h_power h 2) /\
  read (memory :> bytes128 (word_add ptr (word 64))) s =
    word_join (karatsuba_mid(h_power h 3) : 64 word)
              (karatsuba_mid(h_power h 2) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 80))) s =
    byteswap128(h_power h 3)`;;

(* ------------------------------------------------------------------------- *)
(* Equivalences between the FIPS197 specs and the ARM hardare specs.         *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_REVERSEFIELDS = prove
 (`word_subword (word_reversefields 8 x) (0,8):byte = word_subword x (120,8) /\
   word_subword (word_reversefields 8 x) (8,8):byte = word_subword x (112,8) /\
   word_subword (word_reversefields 8 x) (16,8):byte = word_subword x (104,8) /\
   word_subword (word_reversefields 8 x) (24,8):byte = word_subword x (96,8) /\
   word_subword (word_reversefields 8 x) (32,8):byte = word_subword x (88,8) /\
   word_subword (word_reversefields 8 x) (40,8):byte = word_subword x (80,8) /\
   word_subword (word_reversefields 8 x) (48,8):byte = word_subword x (72,8) /\
   word_subword (word_reversefields 8 x) (56,8):byte = word_subword x (64,8) /\
   word_subword (word_reversefields 8 x) (64,8):byte = word_subword x (56,8) /\
   word_subword (word_reversefields 8 x) (72,8):byte = word_subword x (48,8) /\
   word_subword (word_reversefields 8 x) (80,8):byte = word_subword x (40,8) /\
   word_subword (word_reversefields 8 x) (88,8):byte = word_subword x (32,8) /\
   word_subword (word_reversefields 8 x) (96,8):byte = word_subword x (24,8) /\
   word_subword (word_reversefields 8 x) (104,8):byte = word_subword x (16,8) /\
   word_subword (word_reversefields 8 x) (112,8):byte = word_subword x (8,8) /\
   word_subword (word_reversefields 8 x:int128) (120,8):byte =
   word_subword x (0,8)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_SHIFT_ROWS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (aes_shift_rows x) =
              aes_shift_rows (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[aes_sub_bytes_select; LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let WORD_XOR_REVERSEFIELDS = prove
 (`!x y:int128.
        word_xor (word_reversefields 8 x) (word_reversefields 8 y) =
        word_reversefields 8 (word_xor x y)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_REVERSEFIELDS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (word_reversefields 8 x) =
              word_reversefields 8 (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_sub_bytes_select; word_join_list_16_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  CONV_TAC WORD_BLAST);;

let FIPS197_EQ_SHIFT_ROWS = prove
 (`!x:int128.
        fips197_shift_rows x =
        word_reversefields 8 (aes_shift_rows (word_reversefields 8 x))`,
  REWRITE_TAC[fips197_shift_rows; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

let FIPS197_EQ_MIX_COLUMNS = prove
 (`!x:int128.
        fips197_mix_columns x =
        word_reversefields 8 (aes_mix_columns  (word_reversefields 8 x))`,
  REWRITE_TAC[aes_mix_columns; fips197_mix_columns;
              word_join_list_16_8; aes_mix_word] THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Reconstruction of high-level concepts from the computed expressions.      *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN_COMBINE_LEMMA = prove
 (`(!(x:N word) pos1 pos2.
        pos1 + 8 = pos2
        ==> word_join (word_subword x (pos2,8):byte)
                      (word_subword x (pos1,8):byte):int16 =
            word_subword x (pos1,16)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 16 = pos2
        ==> word_join (word_subword x (pos2,16):int16)
                      (word_subword x (pos1,16):int16):int32 =
            word_subword x (pos1,32)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 32 = pos2
        ==> word_join (word_subword x (pos2,32):int32)
                      (word_subword x (pos1,32):int32):int64 =
            word_subword x (pos1,64)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 64 = pos2
        ==> word_join (word_subword x (pos2,64):int64)
                      (word_subword x (pos1,64):int64):int128 =
            word_subword x (pos1,128)) /\
   (!x:int128. word_subword x (0,128) = x)`,
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_BLAST] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_16; DIMINDEX_32;
              DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_SUBWORD;
        DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_SUBWORD_REVERSEFIELDS_32 = prove
 (`word_subword (word_reversefields 32 x:int128) (0,32):int32 =
   word_subword x (96,32) /\
   word_subword (word_reversefields 32 x:int128) (32,32):int32 =
   word_subword x (64,32) /\
   word_subword (word_reversefields 32 x:int128) (64,32):int32 =
   word_subword x (32,32) /\
   word_subword (word_reversefields 32 x:int128) (96,32):int32 =
   word_subword x (0,32)`,
  CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_BYTESWAP128 = prove
 (`(!x. word_subword (byteswap128 x) (0,64):int64 = word_subword x (64,64)) /\
   (!x. word_subword (byteswap128 x) (64,64):int64 = word_subword x (0,64))`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_CTR_BLOCK_32 = prove
 (`word_subword (ctr_block nonce cnt) (0,32):int32 = word cnt /\
   word_subword (ctr_block nonce cnt) (32,32):int32 =
     word_subword nonce (0,32) /\
   word_subword (ctr_block nonce cnt) (64,32):int32 =
     word_subword nonce (32,32) /\
   word_subword (ctr_block nonce cnt) (96,32):int32 =
     word_subword nonce (64,32)`,
  REWRITE_TAC[ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Scalar counter representation.  Unlike the vector-IV kernels, this variant *)
(* keeps the counter block in scalar registers: after "ldp x11,x12,[x4]" the *)
(* two 64-bit halves of the (little-endian) IV live in X11 (low) and X12      *)
(* (high); the running counter is byte-reversed out of X12's top word into    *)
(* X13.  The loop rebuilds the reversed counter block via                     *)
(*   w14 = rev(w13);  x14 = orr x12 (w14 lsl 32);  Q0 = word_join x14 x11.     *)
(* These lemmas connect that scalar reconstruction back to ctr_block.         *)

let SCALAR_IV_SPLIT = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = w
   ==> ivlo = word_subword w (0,64) /\ ivhi = word_subword w (64,64)`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;

(* Setup-block obligations for the scalar counter registers, phrased directly    *)
(* from the IV-halves join relation so that all widths stay concrete (avoids the  *)
(* type-variable ambiguity that arises if ivhi is substituted before WORD_BLAST). *)

let X11_SETUP = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce 2)
   ==> ivlo = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN SIMP_TAC[]);;

let X12_SETUP = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce 2)
   ==> word_zx (word_zx ivhi:int32):int64 =
       word_zx (word_zx (word_subword
         (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN SIMP_TAC[]);;

let X13_SETUP = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce 2)
   ==> word_zx (word_bytereverse (word_zx (word_ushr ivhi 32):int32):int32):int64
       = word_zx (word 2:int32):int64`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN
  REWRITE_TAC[ctr_block] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  CONV_TAC BITBLAST_RULE);;

(* Normalisation rules for the scalar counter.  The counter lives in the 32-bit W13 *)
(* view of X13; each "add w13,w13,#1" is a 32-bit add and each read of W13 is a      *)
(* truncation, so counter expressions accumulate word_zx chains.  These two rules    *)
(* (applied alongside WORD_SIMPLE_SUBWORD_CONV while stepping) keep the counter in a *)
(* single-word_zx normal form: ZX_COUNTER_UD kills up-then-down conversions,         *)
(* ZX_COUNTER_INC pushes the 32-bit increment through the extension.                 *)

let ZX_COUNTER_UD = prove
 (`word_zx (word_zx (x:int32):int64):int32 = x`,
  CONV_TAC BITBLAST_RULE);;

let ZX_COUNTER_INC = prove
 (`word_zx (word_add (word_zx (x:int64):int32) (word 1)):int32 =
   word_add (word_zx x:int32) (word 1)`,
  CONV_TAC BITBLAST_RULE);;

(* This variant assembles the counter block on the STACK: "stp x11,x14,[sp,#OFF]"    *)
(* then "ldr q0,[sp,#OFF]".  The load reads back the two stored halves as            *)
(* word_join x14 x11, which reconstructs the reversed ctr_block.                     *)

let CTR_BLOCK_BUILD_INSERT = prove
 (`word_join
     (word_or
       (word_zx ((word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64)):int32):int64)
       (word_shl (word_zx (word_bytereverse (word cval:int32)):int64) 32))
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* In the late_tag schedule each block's counter word is "add w14,w13,#N" from  *)
(* a fixed base w13, then byte-reversed; the W-register up/down-conversions leave *)
(* a word_zx nest around either the bare base (word (4*i+2), four zx layers) or   *)
(* the offset form word_add (word_zx (word_zx (word (4*i+2)))) (word N).  These   *)
(* two rules (int32) collapse both to word n / word_add (word n) (word m).        *)
let CTR_ZX_NORM = prove
 (`(word_zx (word_zx (word_zx (word_zx (word n:int32):int64):int32):int64):int32 = word n) /\
   (!m. word_zx (word_zx (word_add (word_zx (word_zx (word n:int32):int64):int32)
                                   (word m):int32):int64):int32
        = word_add (word n:int32) (word m))`,
  CONJ_TAC THENL [CONV_TAC BITBLAST_RULE; GEN_TAC THEN CONV_TAC BITBLAST_RULE]);;

(* The s2n-bignum simulator does not auto-merge two 64-bit stores into a       *)
(* 128-bit load, so after "stp x11,x14,[sp,#OFF]" the subsequent               *)
(* "ldr q0,[sp,#OFF]" would leave Q0 symbolic.  This tactic, spliced in AFTER  *)
(* the stp step and BEFORE the ldr step for state s<N>, derives the merged     *)
(* 128-bit read read(bytes128 (sp+OFF)) s<N> = word_join x14 x11 from the two  *)
(* bytes64 store facts, so the simulator can resolve the load against it.      *)
let MERGE_CTR128_TAC off sname =
  MP_TAC(ISPECL [`memory`;
                 mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                         mk_comb(`word:num->int64`,mk_small_numeral off));
                 mk_var(sname,`:armstate`)]
           (el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let AES_CTR_BLOCK_RECONSTRUCT = prove
 (`word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 2)) rk) =
   aes_ctr_block nonce rk i /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 3)) rk) =
   aes_ctr_block nonce rk (i + 1) /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 4)) rk) =
   aes_ctr_block nonce rk (i + 2) /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 5)) rk) =
   aes_ctr_block nonce rk (i + 3)`,
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CIPHER_BLOCK_NIST = prove
 (`cipher_block nonce rk inblock i =
        word_reversefields 8 (nist_cipher_block nonce rk inblock i)`,
  REWRITE_TAC[nist_cipher_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

(*** Direct implementation of AES128 using the hardware primitives ***)

let AES128_CIPHER_RECONSTRUCT = prove
 (`word_xor
   (aese
    (aesmc
    (aese
     (aesmc
     (aese
      (aesmc
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2))
         rk3))
        rk4))
       rk5))
      rk6))
     rk7))
    rk8))
   rk9)
   rk10 =
   word_reversefields 8
    (aes128_cipher (word_reversefields 8 plaintext)
        (MAP (word_reversefields 8)
             [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10]))`,
  REWRITE_TAC[aes128_cipher; LET_DEF; LET_END_DEF; MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[aesmc; aese; fips197_final_round; fips197_round] THEN
  REWRITE_TAC[AES_SUB_BYTES_SHIFT_ROWS] THEN
  REWRITE_TAC[FIPS197_EQ_SHIFT_ROWS; FIPS197_EQ_MIX_COLUMNS; fips197_sub_bytes;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GSYM WORD_XOR_REVERSEFIELDS; WORD_REVERSEFIELDS_REVERSEFIELDS;
              GSYM AES_SUB_BYTES_REVERSEFIELDS]);;

(*** This is the sequence in the code, folding an XOR in sooner ***)

let XOR_AES128_CIPHER_RECONSTRUCT = prove
 (`word_xor
    (aese
     (aesmc
     (aese
      (aesmc
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc
          (aese
           (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2))
          rk3))
         rk4))
        rk5))
       rk6))
      rk7))
     rk8))
    rk9)
   (word_xor rk10 inblock) =
   word_xor
    (word_reversefields 8
      (aes128_cipher (word_reversefields 8 plaintext)
         (MAP (word_reversefields 8)
              [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10])))
    inblock`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REWRITE_TAC[AES128_CIPHER_RECONSTRUCT]);;

(* ------------------------------------------------------------------------- *)
(* The reduction pattern that is used in the code (p1, p2, p3 are the        *)
(* Karatsuba subcomponents of an implicit 256-bit result).                   *)
(* ------------------------------------------------------------------------- *)

let polyval_reduce_g2 = new_definition
 `polyval_reduce_g2 p1 p2 p3 =
        let (HI:int128->int64) = \x. word_subword x (64,64)
        and (LO:int128->int64) = \x. word_subword x (0,64) in
        let ks = word_xor (word_xor p1 p2) p3 in
        let w1 = word_pmul (LO p1) (word 13979173243358019584 : int64) in
        let w2 = word_pmul
                 (word_xor (word_xor (LO w1) (HI p1))
                           (LO(word_xor (word_xor p1 p2) p3)))
                 (word 13979173243358019584 : int64) in
        word_xor
           (word_join
              (LO (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              (HI (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              : int128)
           (word_xor w2 p2 : int128)`;;

let RECONSTRUCT_POLYVAL_REDUCE_G2 =
  REWRITE_RULE[LET_DEF; LET_END_DEF] (GSYM polyval_reduce_g2);;

let POLYVAL_REDUCE_G2 = prove
 (`polyval_reduce_g2 p1 p2 p3 =
    polyval_reduce_prop3
      ((word_join : int128 -> int128 -> (256)word)
         (word_join (word_subword p2 (64,64):int64)
                    (word_xor (word_subword (word_xor (word_xor p1 p2) p3)
                                            (64,64):int64)
                              (word_subword p2 (0,64):int64)): int128)
         (word_join (word_xor (word_subword
          (word_xor (word_xor p1 p2) p3) (0,64):int64)
                    (word_subword p1 (64,64):int64))
                    (word_subword p1 (0,64):int64): int128))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_reduce_g2; polyval_reduce_prop3;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w1 =  (word_pmul:int64->int64->int128)
      (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
  ABBREV_TAC `ks:int128 = word_xor (word_xor p1 p2) p3` THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w2:int128 = word_pmul
     (word_xor (word_xor (word_subword (w1:int128) (0,64):int64)
                     (word_subword (p1:int128) (64,64):int64))
           (word_subword (ks:int128) (0,64):int64))
     (word 13979173243358019584:int64)` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE (LAND_CONV o LAND_CONV)
   [WORD_BITWISE_RULE
    `word_xor (word_xor w1 p1) ks = word_xor (word_xor ks p1) w1`]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Variants of the existing Karatsuba lemmas better fitting the code.        *)
(* ------------------------------------------------------------------------- *)

let PMUL_KARATSUBA_JOIN = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (0,64):int64)
                                 (word_subword a (64,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC WORD_BLAST);;

let PMUL_KARATSUBA_JOIN_ALT = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (64,64):int64)
                                 (word_subword a (0,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REWRITE_TAC[PMUL_KARATSUBA_JOIN] THEN REWRITE_TAC[WORD_XOR_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for stepping the software-pipelined loop bodies.                  *)
(* ------------------------------------------------------------------------- *)

(* Surgical address-fold: inside `word_add in_p (word (...))` ONLY, fold a nested num offset
   (64*i+c)+d -> 64*i+(c+d) (GSYM ADD_ASSOC + NUM_ADD).  Scoped to in_p reads so it can NOT mangle
   nist_cipher_block block indices / counter arith elsewhere in the tower.  The prefetch loads
   `ldp ..,[x0,#K]` (x0=in_p+64i+64 after post-inc) settle as in_p+word((64i+64)+K); NORMALIZE_RELATIVE
   gives that nested form, this folds it to in_p+word(64i+80..) to match the s0 input-split anchors. *)
let IN_P_ADDR_FOLD_CONV : conv =
  let inner = (REWR_CONV(GSYM ADD_ASSOC) THENC RAND_CONV NUM_ADD_CONV) in
  ONCE_DEPTH_CONV(fun t -> match t with
    | Comb(Comb(Const("word_add",_), v), Comb(Const("word",_), _))
        when (try fst(dest_var v) = "in_p" with _ -> false)
      -> RAND_CONV(RAND_CONV inner) t
    | _ -> failwith "IN_P_ADDR_FOLD_CONV");;

(* The (register, state index) of a fact `read R sK = ..` when R is one of the registers in    *)
(* keeplist; the steppers keep only the latest such fact for each of those registers.           *)
let gc2 keeplist c = try let l=lhs c in let rd,st=dest_comb l in let rr,cc=dest_comb rd in
   if is_const cc && mem (fst(dest_const cc)) keeplist then
     (match st with Var(nm,_) when String.length nm>=2 && nm.[0]='s' ->
        (try Some(fst(dest_const cc), int_of_string(String.sub nm 1 (String.length nm-1))) with _->None) |_->None) else None
  with _->None;;

(* Discard a fact about an OLD state when the same fact (modulo the state variable) already holds of
   the current state and no other assumption refers to that old state.  A fact refers to a state that
   occurs in it other than as the state its own left-hand read is about: the latest value of a register
   may mention an earlier state's memory read (`read Q5 s148 = .. read (memory :> ..) s99 ..`), which
   keeps s99's facts (the closers resolve that read from them) but says nothing about s148.
   The stepper re-derives the anchored memory facts, the in_p/out_p foralls and aligned_bytes_loaded
   at every step; without this they accumulate one copy per state and every ARM_STEP_TAC and
   ASM_REWRITE_TAC is linear in the assumption list. *)
let DISCARD_STALE_TAC sname : tactic = fun (asl,w) ->
  let sv = mk_var(sname,`:armstate`) in
  let is_st v = is_var v && type_of v = `:armstate` in
  let cs = map (fun (_,th) -> concl th) asl in
  let own c = try (match strip_comb (lhs c) with
                     (Const("read",_),[_;st]) when is_st st -> [st] | _ -> [])
              with Failure _ -> [] in
  let live = itlist (fun c acc ->
      let svs = filter is_st (frees c) in
      if length svs >= 2 then union (subtract svs (own c)) acc else acc) cs [] in
  let cur = filter (vfree_in sv) cs in
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let c = concl th in
    match filter is_st (frees c) with
      [s] when s <> sv && not (mem s live) -> exists (aconv (vsubst [sv,s] c)) cur
    | _ -> false) (asl,w);;

(* The state variable of the first `read` inside a fact (used for the quantified memory facts). *)
let state_of_forall c =
  try let rd = find_term (fun t -> match t with
        Comb(Comb(Const("read",_),_),Var(nm,_)) when String.length nm>=1 && nm.[0]='s' -> true | _->false) c in
      (match rd with Comb(_,Var(nm,_)) -> Some nm | _ -> None) with _ -> None;;

(* One step of a software-pipelined simulation followed by garbage collection of the assumption list.
   After the step we keep the MAYCHANGE fact of the current state, the input/output buffer foralls, the
   memory reads at the anchor pointers and at the counter stack slots (by offset), the latest read of
   each register in keeplist, and every fact that is not a read of an earlier state; DISCARD_STALE_TAC
   then drops the superseded copies of the kept facts. *)
let SWP_STEP_TAC (anchors:term list) (slots:string list) keeplist exec sname : tactic =
  ARM_STEP_TAC exec [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) ->
    let cs = map (fun (_,th) -> concl th) asl in
    let latest = map (fun r -> (r, itlist (fun c m ->
                   match gc2 keeplist c with Some(rr,k) when rr = r && k > m -> k | _ -> m) cs (-1)))
                   keeplist in
    let is_read c = try fst(dest_const(fst(strip_comb(lhs c)))) = "read" with Failure _ -> false in
    let slot_read c = can (find_term (fun t -> match t with
          Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n))
            when (try fst(dest_var sp) = "stackpointer" with Failure _ -> false) ->
              mem (string_of_term n) slots
        | _ -> false)) (lhs c) in
    let anchored c = is_read c && (exists (fun p -> free_in p (lhs c)) anchors || slot_read c) in
    let is_maychange c = can (find_term (fun t -> match t with Const("MAYCHANGE",_) -> true | _ -> false)) c in
    let old_state_read c = try (match rand(lhs c) with
          Var(nm,_) -> nm <> sname && String.length nm >= 1 && nm.[0] = 's' | _ -> false)
        with Failure _ -> false in
    DISCARD_ASSUMPTIONS_TAC (fun th ->
      let c = concl th in
      if is_maychange c then (try string_of_term(last(snd(strip_comb c))) <> sname with Failure _ -> false)
      else if is_forall c then
        (if free_in `in_p:int64` c || free_in `out_p:int64` c then false
         else match state_of_forall c with Some nm -> nm <> sname | None -> false)
      else if anchored c then false
      else match gc2 keeplist c with
             Some(r,k) -> k < List.assoc r latest
           | None -> old_state_read c) (asl,w)) THEN
  DISCARD_STALE_TAC sname;;

(* Steps k in ks of a leg: SWP_STEP_TAC, the address and subword normalization, a per-leg
   simplification of the fresh facts (extra k), and the counter-slot merge at the recorded store steps. *)
let SWP_STEPS_TAC anchors slots keeplist exec (extra:int->tactic) merges (ks:int list) : tactic =
  MAP_EVERY (fun k ->
    let sname = "s" ^ string_of_int k in
    SWP_STEP_TAC anchors slots keeplist exec sname THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
    extra k THEN
    (if List.mem_assoc k merges then MERGE_CTR128_TAC (List.assoc k merges) sname else ALL_TAC)) ks;;

(* ------------------------------------------------------------------------- *)
(* Leaf closers for the constant-time and memory-safety proofs (shared with  *)
(* the clean keep_htable safety proof).                                      *)
(* ------------------------------------------------------------------------- *)

let lc_eq = prove
 (`nblocks DIV 4 = loop_count /\ len_bits DIV 128 = nblocks
    ==> loop_count = len_bits DIV 512`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `nblocks DIV 4 = loop_count`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `len_bits DIV 128 = nblocks`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV);;

let lr_eq = prove
 (`nblocks MOD 4 = loop_remain /\ len_bits DIV 128 = nblocks
    ==> loop_remain = len_bits DIV 128 MOD 4`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `nblocks MOD 4 = loop_remain`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

let WSUB_BRANCH = prove
 (`!i k:num. i < k /\ k < 2 EXP 64
     ==> (~(val(word_sub (word (k - i):int64) (word 1)) = 0) <=> i + 1 < k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `val(word (k - i):int64) = k - i` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    TRANS_TAC LET_TRANS `k:num` THEN ASM_SIMP_TAC[LE_REFL] THEN ARITH_TAC;
    REWRITE_TAC[VAL_WORD_1] THEN
    SIMP_TAC[DIMINDEX_64; ARITH_RULE `1 < 2 EXP 64`] THEN ASM_ARITH_TAC]);;

let DEABBR : tactic =
  W(fun (asl,w) ->
    let lcth = try [MATCH_MP lc_eq (CONJ (ASSUME `nblocks DIV 4 = loop_count`)
                                          (ASSUME `len_bits DIV 128 = nblocks`))] with _ -> [] in
    let lrth = try [MATCH_MP lr_eq (CONJ (ASSUME `nblocks MOD 4 = loop_remain`)
                                          (ASSUME `len_bits DIV 128 = nblocks`))] with _ -> [] in
    let vwth = mapfilter (fun (_,th) -> let t = concl th in
        if is_eq t && (match lhs t with
                         Comb(v,Comb(wd,_)) ->
                           (try name_of v = "val" && name_of wd = "word" with _ -> false)
                       | _ -> false)
        then th else fail()) asl in
    let lclr = lcth @ lrth in
    RULE_ASSUM_TAC(fun th ->
       if is_eq(concl th) && is_var(lhs(concl th)) &&
          type_of(lhs(concl th)) = `:(uarch_event)list`
       then REWRITE_RULE (lclr @ vwth) th
       else REWRITE_RULE lclr th) THEN
    REWRITE_TAC (lclr @ vwth));;

let CTR_RECON : tactic =
  GEN_REWRITE_TAC I [GSYM VAL_EQ] THEN
  GEN_REWRITE_TAC (TRY_CONV o ONCE_DEPTH_CONV)
    [ARITH_RULE `word 3:int64 = word(2 EXP 2 - 1)`] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD_USHR] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM(ASSUME `len_bits DIV 128 = nblocks`);
              GSYM(ASSUME `nblocks DIV 4 = loop_count`);
              GSYM(ASSUME `nblocks MOD 4 = loop_remain`)] THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV;;

let ADDR_RECON : tactic =
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_CLAUSES; SUB_0;
              WORD_ADD_0; ADD_ASSOC] THEN
  (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_ARITH);;

let BRANCH_RECON : tactic =
  GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN ASM_SIMP_TAC[WSUB_BRANCH];;

let WSUB_ARITH : tactic =
  W(fun (asl,w) ->
    let l,_ = dest_eq w in
    let cnt_minus_i = (match l with Comb(Comb(_,Comb(_,a)),_) -> a | _ -> failwith "wsub") in
    let cnt,iv = dest_binary "-" cnt_minus_i in
    let lt = mk_binary "<" (iv,cnt) in
    SUBGOAL_THEN (mk_eq(cnt_minus_i, mk_binary "+" (mk_binary "-" (cnt, mk_binary "+" (iv,`1`)), `1`)))
      SUBST1_TAC THENL
     [(FIRST_ASSUM(fun th -> if concl th = lt then MP_TAC th else NO_TAC)) THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let is_branch_goal w =
  can dest_eq w &&
  (let l,r = dest_eq w in
   let strip t = match t with Comb(c,a) when (try name_of c="word" with _->false) -> a | _ -> t in
   is_cond l || is_cond r || is_cond (strip l) || is_cond (strip r));;

let LEAF1 : tactic =
  W(fun (asl,w) ->
    if is_exists w then (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC)
    else if is_branch_goal w then BRANCH_RECON
    else if can dest_eq w then (WSUB_ARITH ORELSE ADDR_RECON ORELSE CTR_RECON)
    else (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC));;
let CLOSE : tactic = REPEAT CONJ_TAC THEN LEAF1;;

let MEMACC_VIA_ASM : tactic =
  fun (asl,w) ->
    let defeqs = mapfilter (fun (_,th) -> let t = concl th in
        if is_eq t && is_var(lhs t) && type_of(lhs t) = `:(uarch_event)list`
        then (lhs t, th) else fail()) asl in
    if defeqs = [] then DISCHARGE_MEMACCESS_INBOUNDS_TAC (asl,w) else
    let _,defth = hd defeqs in
    (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM defth] THEN
     REPEAT (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
             CONJ_TAC THENL [DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC; ALL_TAC]) THEN
     FIRST_ASSUM ACCEPT_TAC) (asl,w);;

let DISCHARGE_SAFE_ROBUST : tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC] else ALL_TAC) THEN
  MEMACC_VIA_ASM;;

let LEAF2 : tactic =
  W(fun (asl,w) ->
    if is_exists w then (DEABBR THEN DISCHARGE_SAFE_ROBUST)
    else if is_branch_goal w then BRANCH_RECON
    else if can dest_eq w then (WSUB_ARITH ORELSE ADDR_RECON ORELSE CTR_RECON)
    else (DEABBR THEN DISCHARGE_SAFE_ROBUST));;
let CLOSE_R2 : tactic = REPEAT CONJ_TAC THEN LEAF2;;

(* Surgical cond reducers (constant condition), no beta-mangle of f_ev_* redexes. *)
let REDUCE_IFEQ (v:term) (k:term) : tactic =
  PURE_ONCE_REWRITE_TAC[EQT_INTRO(ASSUME(mk_eq(v,k)))] THEN PURE_REWRITE_TAC[COND_CLAUSES];;
let REDUCE_IFNE (v:term) (k:term) : tactic =
  PURE_ONCE_REWRITE_TAC[EQF_INTRO(ASSUME(mk_neg(mk_eq(v,k))))] THEN PURE_REWRITE_TAC[COND_CLAUSES];;
let REDUCE_IF0 (lv:term)  = REDUCE_IFEQ lv `0`;;
let REDUCE_IFN0 (lv:term) = REDUCE_IFNE lv `0`;;

(* Variants for the whole-subroutine safety proofs, whose memory facts close by rewriting. *)

let MEM_PRESERVE : tactic = ASM_REWRITE_TAC[] THEN NO_TAC;;

let LEAF1_SUB : tactic =
  W(fun (asl,w) ->
    if is_exists w then (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC)
    else if is_branch_goal w then BRANCH_RECON
    else if can dest_eq w then (WSUB_ARITH ORELSE ADDR_RECON ORELSE CTR_RECON ORELSE MEM_PRESERVE)
    else (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC));;
let CLOSE_SUB : tactic = REPEAT CONJ_TAC THEN LEAF1_SUB;;

let LEAF2_SUB : tactic =
  W(fun (asl,w) ->
    if is_exists w then (DEABBR THEN DISCHARGE_SAFE_ROBUST)
    else if is_branch_goal w then BRANCH_RECON
    else if can dest_eq w then (WSUB_ARITH ORELSE ADDR_RECON ORELSE CTR_RECON ORELSE MEM_PRESERVE)
    else (DEABBR THEN DISCHARGE_SAFE_ROBUST));;
let CLOSE_R2_SUB : tactic = REPEAT CONJ_TAC THEN LEAF2_SUB;;

(* mem@88 x30-save-slot preservation conjunct, appended to every invariant.    *)
let m88 = `read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress`;;
