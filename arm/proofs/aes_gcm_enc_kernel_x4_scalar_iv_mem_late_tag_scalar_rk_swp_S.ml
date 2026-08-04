(* ========================================================================= *)
(*                               HOL LIGHT                                   *)
(*                                                                           *)
(* CANONICAL functional-correctness proof of the SLOTHY software-pipelined   *)
(* AES-GCM kernel                                                            *)
(*   aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S  (swpS_mc). *)
(*                                                                           *)
(* This is a DIRECT proof: a single mid-pipeline elaborated loop invariant   *)
(* (swpS_inv8, asserted at the natural loop head pc+0x1ec) drives one        *)
(* seam-to-seam ENSURES_WHILE, with FILL / DRAIN legs and a byte-identical    *)
(* single-block tail.  There is NO program-equivalence detour: the theorem   *)
(*   AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_CORRECT     *)
(* (entry pc+0x2c -> exit pc+0x710) is proved outright, hyps-free, using only *)
(* the three standard HOL Light axioms.                                      *)
(*                                                                           *)
(* Structure:                                                                *)
(*   - lemma substrate (shared with the _swp_deint sibling): ctr_block /     *)
(*     aes_ctr_block / cipher_block / nist_cipher_block / htable_mem_4 +      *)
(*     the AES / counter / GHASH-reduce reconstruction lemmas +              *)
(*     MERGE_CTR128_TAC / SPLIT_INPUT_CONV.                                  *)
(*   - swpS_mc + SWPS_EXEC ; the partial-AES abstractions (aes7c/aes8c/       *)
(*     aes10p) and the elaborated invariant swpS_inv8.                       *)
(*   - BODYLEG (one loop body 0x1ec->0x4b0, inv i -> inv(i+1)); FILLLEG       *)
(*     (0x88->0x1ec); REDUCELAST (drain 0x4b0->0x61c); SWPS_TAIL (0x61c->     *)
(*     0x710).                                                               *)
(*   - SWPS_DRAIN, SWPS_LEG1 (FILL + WHILE + DRAIN), SWPS_LEG1_LC1,           *)
(*     SWPS_FROM88 (0x88->0x710), and the preamble-wrapped _CORRECT theorem.  *)
(*                                                                           *)
(* An alternative equivalence-route proof of the same kernel is kept in      *)
(*   aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S_via_equiv*  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/fips197.ml";;
needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;

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

let CTR_BLOCK_RECONSTRUCT_REV8 = prove
 (`word_join
    (word_join (word_reversefields 8 (word ctr):int32)
               (word_reversefields 8 (word_subword nonce (0,32):int32)):int64)
    (word_join (word_reversefields 8 (word_subword nonce (32,32):int32))
               (word_reversefields 8 (word_subword nonce (64,32):int32)):int64)
    = word_reversefields 8 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

let CTR_BLOCK_RECONSTRUCT_REV32 = prove
 (`word_join
    (word_join (word ctr:int32)
               (word_subword nonce (0,32):int32):int64)
    (word_join (word_subword nonce (32,32):int32)
               (word_subword nonce (64,32):int32):int64) =
  word_reversefields 32 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

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

let SUBWORD_WORD_LO32 = prove
 (`word_subword (word n:int64) (0,32):int32 = word n`,
  SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_64; ARITH_RULE `0 + 32 <= 64`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* Given the initial IV halves (join = reversed ctr_block for counter 2), the *)
(* loop-built block for any counter value equals the reversed ctr_block.      *)

let CTR_BLOCK_BUILD_V = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce 2)
   ==> word_join
        (word_or (word_zx ((word_zx ivhi):int32):int64)
                 (word_shl (word_zx (word_bytereverse (word cval:int32)):int64) 32))
        ivlo :int128
       = word_reversefields 8 (ctr_block nonce cval)`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN
  REWRITE_TAC[ctr_block] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  CONV_TAC WORD_BLAST);;

let JOIN_SUBWORD_ID = prove
 (`word_join (word_subword (w:int128) (64,64):int64)
             (word_subword w (0,64):int64):int128 = w`,
  CONV_TAC WORD_BLAST);;

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

(* Closed form: with X11/X12 written as (counter-free) subwords of the reversed
   ctr_block for the canonical counter 2, the loop-built block for counter cval
   equals the reversed ctr_block for cval.  This is what the loop body invokes. *)

let CTR_BLOCK_BUILD_CLOSED = prove
 (`word_join
        (word_or
          (word_zx ((word_zx (word_subword
              (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64)):int32):int64)
          (word_shl (word_zx (word_bytereverse (word cval:int32)):int64) 32))
        (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64)
        :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  MP_TAC(INST
    [`word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64`,
       `ivhi:int64`;
     `word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64`,
       `ivlo:int64`]
    CTR_BLOCK_BUILD_V) THEN
  REWRITE_TAC[JOIN_SUBWORD_ID]);;

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

(* Epilogue byte-splice: the final "str w14,[x4,#12]" overwrites only the top 4 bytes *)
(* of the ivec (the byte-reversed counter word); the low 12 bytes keep their initial  *)
(* value (the reversed nonce from ctr_block nonce 2).  Recombining gives the reversed *)
(* ctr_block for the final counter value.                                             *)

let EPI_SPLICE = prove
 (`word_join (word_bytereverse (word cval:int32):int32)
             (word_subword (word_reversefields 8 (ctr_block nonce 2):int128)
                           (0,96):96 word)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* Same splice phrased for the 64/64 then 32/32 decomposition of the 128-bit ivec    *)
(* read (which is how READ_MEMORY_BYTESIZED_SPLIT breaks it): the stored counter word *)
(* is the top 32 bits of the high 64-bit half, the rest is the unchanged nonce.       *)

let EPI_SPLICE_64 = prove
 (`word_join
      (word_join (word_bytereverse (word cval:int32):int32)
                 (word_subword (word_reversefields 8 (ctr_block nonce 2):int128)
                               (64,32):int32):int64)
      (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* After the 32-bit-cell split (and collapsing the word_zx conversion chain with     *)
(* ZX_COUNTER_UD), the counter cell (offset 12) is word_bytereverse(word c), which    *)
(* equals the top 32 bits of the reversed ctr_block.                                  *)

let COUNTER_CHUNK = prove
 (`word_zx (word_zx (word_bytereverse
     (word_zx (word_zx (word (c:num):int32):int64):int32):int32):int64):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce c):int128) (96,32):int32`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* The low three 32-bit cells of the reversed ivec (the nonce) are independent of the *)
(* counter value, so they still hold their initial (counter-2) contents.              *)

let NONCE_CHUNK = prove
 (`word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,32):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,32):int32 /\
   word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (32,32):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce c):int128) (32,32):int32 /\
   word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce c):int128) (64,32):int32`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

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

(* Split a 128-bit input-block memory read into two 64-bit halves whose addresses  *)
(* are folded back to the canonical "in_p + word(off)" form.  The scalar_rk final  *)
(* round loads each input block as scalars via "ldp x22,x23,[x0,#K]", i.e. it reads *)
(* the block's two 64-bit halves at x0+K and x0+K+8.  READ_MEMORY_SPLIT_CONV emits  *)
(* the high half at address (in_p + word off) + word 8; the simulator's memory      *)
(* lookup will not match that against x0+K+8 unless we renormalise it to            *)
(* in_p + word(off+8).  NORMALIZE_RELATIVE_ADDRESS_CONV reassociates and GSYM       *)
(* ADD_ASSOC + NUM_ADD_CONV fold the numeric offset.                                *)
let SPLIT_INPUT_CONV =
  READ_MEMORY_SPLIT_CONV 1 THENC
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
  ONCE_DEPTH_CONV(REWR_CONV(GSYM ADD_ASSOC)) THENC
  ONCE_DEPTH_CONV NUM_ADD_CONV;;

(* Tail-loop variant of the input split.  The tail block is loaded by the         *)
(* POST-INDEXED "ldp x22,x23,[x0],#16": the ARM model reads the second register    *)
(* x23 from address in_p + word((64*loop_count + 16*i) + 8) — the "+ 8" stays a    *)
(* separate num-level summand because the block offset (64*loop_count + 16*i) has   *)
(* a symbolic i, so NUM_ADD_CONV cannot fold it.  The plain SPLIT + NORMALISE (no   *)
(* ADD_ASSOC/NUM fold) reproduces exactly that address form, letting the           *)
(* post-indexed load resolve x23 (offset-mode loads in the main loop DO fold, hence *)
(* the two different conversions).                                                 *)
let SPLIT_INPUT_TAIL_CONV =
  READ_MEMORY_SPLIT_CONV 1 THENC
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV;;

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

(* In the scalar_rk variant the final AES round key (EL 10) is XORed in scalar    *)
(* registers X20/X21 into the input block halves, and the block ciphertext is     *)
(* word_xor (word_join <input_hi ^ key10_hi> <input_lo ^ key10_lo>) (9-round Q0). *)
(* This lemma rewrites that scalar-built form into the word_xor <9round>           *)
(* (word_xor rk10 inblock) shape that XOR_AES128_CIPHER_RECONSTRUCT consumes,      *)
(* with rk10 = word_reversefields 8 (EL 10 rk) and inblock = word_join of the      *)
(* input halves.  Both operand orders of the outer word_xor are covered: the       *)
(* ciphertext-output copy keeps the (word_join ... ) nineround order from the       *)
(* "eor v0,v29,v0", while the GHASH-accumulated copy has the operands commuted by   *)
(* the intervening normalisation, so we need both orientations.                     *)
let SCALAR_RK_RECONSTRUCT = prove
 (`(word_xor
     (word_join
        (word_xor (word_subword (inb:int128) (64,64):int64)
                  (word_subword (word_reversefields 8 (rk10:int128)) (64,64):int64))
        (word_xor (word_subword inb (0,64):int64)
                  (word_subword (word_reversefields 8 rk10) (0,64):int64)) :int128)
     (nineround:int128)
    = word_xor nineround (word_xor (word_reversefields 8 rk10) inb)) /\
   (word_xor
     (nineround:int128)
     (word_join
        (word_xor (word_subword (inb:int128) (64,64):int64)
                  (word_subword (word_reversefields 8 (rk10:int128)) (64,64):int64))
        (word_xor (word_subword inb (0,64):int64)
                  (word_subword (word_reversefields 8 rk10) (0,64):int64)) :int128)
    = word_xor nineround (word_xor (word_reversefields 8 rk10) inb))`,
  CONJ_TAC THEN CONV_TAC BITBLAST_RULE);;

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
(* Core correctness theorem.                                                 *)
(*                                                                           *)
(* This covers the body of the function with the save/restore boilerplate    *)
(* excised: PC starts at pc + 0x2c (first real instruction after the 11      *)
(* save instructions) and ends at pc + 0x448 (first ldp of the postamble).   *)
(* The stackpointer is the value AFTER the sub sp, #0xe0 adjustment, i.e.    *)
(* the value the SP register actually holds inside the function body.        *)
(*                                                                           *)
(* Arguments (Standard ARM ABI, values in registers at core entry):          *)
(*   X0 = in        input buffer (len_bits/8 bytes)                          *)
(*   X1 = len_bits  length in bits (whole 16-byte blocks)                    *)
(*   X2 = out       output buffer (len_bits/8 bytes)                         *)
(*   X3 = tag       16-byte GHASH accumulator (in/out)                       *)
(*   X4 = ivec      16-byte counter block (in/out)                           *)
(*   X5 = key       AES-128 round keys (176 bytes = 11 x 16)                 *)
(*   X6 = Htable    192-byte precomputed H-powers table                      *)
(*   returns X0 = byte_len (= len_bits / 8)                                  *)
(* ------------------------------------------------------------------------- *)

(*** Note that the NIST-level specs consider all byte-level encodings as
 *** big-endian, and the AES-related ARM instructions take that view too.
 *** Hence in the precondition "ctr_block" and "rk" correspond as 128-bit
 *** words to the NIST specifications. Since they are loaded from memory
 *** in the usual little-endian ARM fashion, we byte-reverse when
 *** specifying them as the values in any memory cells.
 ***)


(* ========================================================================= *)
(* SWP DE-INTERLEAVED KERNEL (B;A rotation of the clean loop).               *)
(* Proof by A/B-rotation: invariant asserted at the CLEAN seam 0x354 (after  *)
(* B, before A), where the GHASH tag is SETTLED and no partial AES is in     *)
(* flight -- so the invariant is clean-C's settled loop invariant, index-    *)
(* shifted. Loop plumbing = bignum_inv_p25519 pattern: ENSURES_WHILE with    *)
(* pc1=pc2=0x354 interior to the body; physical back-branch cbnz@0x4b0->0x1ec *)
(* buried inside the body leg. The tail (0x61c..0x710) replays clean-C's     *)
(* tail (its 0x354..0x448) shifted by +0x2c8.                                *)
(* ========================================================================= *)


(* ===================== swpS_mc + the direct correctness proof ===================== *)

let swpS_mc =
  define_from_elf "swpS_mc"
    "arm/aes_gcm/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S.o";;
let SWPS_EXEC = ARM_MK_EXEC_RULE swpS_mc;;

(* ---- partial-AES abstractions ---- *)
let aes7c = new_definition
 `aes7c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk)))`;;

let aes8c = new_definition
 `aes8c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk)))`;;

(* aes10p = the PRE-final-XOR 10-aese tower (10 aese, 9 aesmc, keys EL 0..EL 9, NO final rk10 XOR). *)
let aes10p = new_definition
 `aes10p (nonce:96 word) (rk:int128 list) (c:num) : int128 =
    aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
     (aesmc(aese (word_reversefields 8 (ctr_block nonce c))
       (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
       (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
       (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
       (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk))))
       (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))`;;

let AES10P_COMPLETE = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
    EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk
   ==> word_xor (aes10p nonce rk c) (word_reversefields 8 (EL 10 rk))
       = word_reversefields 8 (aes128_cipher (ctr_block nonce c) rk)`,
  DISCH_TAC THEN REWRITE_TAC[aes10p] THEN
  GEN_REWRITE_TAC LAND_CONV
   [INST ((`word_reversefields 8 (ctr_block nonce c):int128`,`plaintext:int128`) ::
          map (fun j -> (parse_term(Printf.sprintf "word_reversefields 8 (EL %d rk):int128" j),
                         mk_var("rk"^string_of_int j,`:int128`))) (0--10))
         AES128_CIPHER_RECONSTRUCT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; MAP] THEN ASM_REWRITE_TAC[]);;

(* ---- Q30 GHASH collapse lemmas (VALIDATED interactively: fold ALL 4 syntactic keystream forms in
   the reduce tower to nist_cipher_block, so the deint g3-body reconstruction applies).  The keystreams
   appear as: (1) word_xor(aes10p c)(word_xor inb rk10); (2) aese-rounds over aes7c c; (3) over aes8c c;
   (4) fully-expanded 10-aese over rev8(ctr_block c); (5) lane-split word_join(word_xor lanes).  Each
   folds by a one-liner below; then CT_TO_NCB turns word_xor(rev8(aes128_cipher(ctr(j+2))))(inblock j)
   into rev8(nist_cipher_block j).  Index pairing verified consistent: ctr(j+2)<->aes_ctr_block(j)<->inblock(j). *)
let AES10P_VIA_AES7C = prove
 (`aes10p nonce rk c =
   aese(aesmc(aese(aesmc(aese (aes7c nonce rk c) (word_reversefields 8 (EL 7 rk))))
     (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))`,
  REWRITE_TAC[aes10p; aes7c]);;
let AES10P_VIA_AES8C = prove
 (`aes10p nonce rk c =
   aese(aesmc(aese (aes8c nonce rk c) (word_reversefields 8 (EL 8 rk)))) (word_reversefields 8 (EL 9 rk))`,
  REWRITE_TAC[aes10p; aes8c]);;
let KEYSTREAM_FOLD = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
    EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk
   ==> word_xor (aes10p nonce rk c) (word_xor inb (word_reversefields 8 (EL 10 rk)))
       = word_xor (word_reversefields 8 (aes128_cipher (ctr_block nonce c) rk)) inb`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP AES10P_COMPLETE th)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC WORD_BITWISE_RULE);;
let JOIN_XOR_LANES = prove
 (`word_join (word_xor (word_subword (a:int128) (64,64):int64) (word_subword (b:int128) (64,64):int64))
             (word_xor (word_subword a (0,64):int64) (word_subword b (0,64):int64)) : int128
   = word_xor a b`,
  CONV_TAC WORD_BLAST);;
let CT_TO_NCB = prove
 (`word_xor (word_reversefields 8 (aes128_cipher (ctr_block nonce (j+2)) rk)) (inblock j)
   = word_reversefields 8 (nist_cipher_block nonce rk inblock j)`,
  REWRITE_TAC[nist_cipher_block; cipher_block; aes_ctr_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

(* ---- block-(4i+1) keystream closer.  swp_S carries the pipelined input^rk10 of block 4i+1 across
   the backedge in the two scalar lanes X23 (hi 64) / X28 (lo 64); `stp x28,x23,[sp,#176]`@0x210 stages
   them, Q13 reloads@0x21c.  With X23/X28 pinned to the two subword-lanes of word_xor(inblock(4i+1))(rk10),
   word_join recombines to the full 128 and the keystream folds to the settled nist_cipher_block form. *)
let JOIN_SUBWORD_RECOMBINE = prove
 (`word_join (word_subword (x:int128) (64,64):int64) (word_subword x (0,64):int64) : int128 = x`,
  CONV_TAC WORD_BLAST);;
let BLOCK1_FOLD_SUB = prove
 (`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
     EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
    (a:int64) = word_subword (word_xor (inblock (4*(i:num)+1)) (word_reversefields 8 (EL 10 rk)):int128) (64,64) /\
    (b:int64) = word_subword (word_xor (inblock (4*i+1)) (word_reversefields 8 (EL 10 rk)):int128) (0,64)
    ==> word_xor (aes10p nonce rk ((4*i+1)+2)) (word_join (a:int64) (b:int64):int128)
        = word_reversefields 8 (nist_cipher_block nonce rk inblock (4*i+1))`,
  STRIP_TAC THEN ASM_REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
  MP_TAC(INST [`(4*i+1)+2`,`c:num`; `inblock(4*i+1):int128`,`inb:int128`] KEYSTREAM_FOLD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(INST [`inblock:num->int128`,`inblock:num->int128`; `4*i+1`,`j:num`] CT_TO_NCB) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let ZXZX32 = prove
 (`word_zx (word_zx (x:int32):int64):int32 = x`, CONV_TAC WORD_BLAST);;
let ZXNEST4 = prove
 (`word_zx (word_zx (word_zx (word_zx (x:int32):int64):int32):int64):int32 = x`, CONV_TAC WORD_BLAST);;

(* mk_cbv cval : the CTR_BLOCK_BUILD_V instance folding the reassembled reversed-lane counter
   (built from the ctr-2 lanes + word cval) to word_reversefields 8 (ctr_block nonce cval). *)
let mk_cbv cval =
  let inst = INST [`word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64`,`ivhi:int64`;
                   `word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64`,`ivlo:int64`;
                   cval,`cval:num`] CTR_BLOCK_BUILD_V in
  MP inst (prove(lhand(concl inst), REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST));;

(* ---- the elaborated invariant swpS_inv8 (44+1 conjuncts, all cross-iteration regs pinned) ---- *)
let swpS_inv8 = `\(i:num) s.
    read X0 s = word_add in_p (word (64 * i)) /\
    read X2 s = word_add out_p (word (64 * i)) /\
    read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
    read (memory :> bytes128 (word_add stackpointer (word 160))) s =
        word_reversefields 8 (ctr_block nonce (4*i+2)) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
    read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword
        (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word (4 * i + 6):int32):int64 /\
    read Q7 s = word 13979173243358019584 /\
    read Q9  s = aes7c nonce rk (4*i+4) /\
    read Q12 s = aes8c nonce rk (4*i+3) /\
    read Q28 s = aes10p nonce rk (4*i+5) /\
    read Q30 s = byteswap128
        (nist_ghash (aes128_cipher (word 0) rk) tag0
           (list_of_seq (nist_cipher_block nonce rk inblock) (4 * i))) /\
    read X1 s = word (loop_count - (i+1)) /\ read X15 s = word(len_bits DIV 8) /\ read X16 s = word loop_remain /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * i ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
             word_xor (aes_ctr_block nonce rk j) (inblock j)) /\
    read Q5 s = byteswap128(h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q31 s = word_join (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 1):int64)
                           (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 0):int64) /\
    read Q17 s = byteswap128(h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q6 s = word_join (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 3):int64)
                          (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 2):int64) /\
    read (memory :> bytes128 (word_add stackpointer (word 176))) s = word_reversefields 8 (ctr_block nonce (4*i+3)) /\
    read (memory :> bytes128 (word_add stackpointer (word 192))) s = word_xor (inblock (4*i+2)) (word_reversefields 8 (EL 10 rk)) /\
    read (memory :> bytes128 (word_add stackpointer (word 208))) s = word_xor (inblock (4*i+3)) (word_reversefields 8 (EL 10 rk)) /\
    read Q10 s = word_xor (inblock (4*i+2)) (word_reversefields 8 (EL 10 rk)) /\
    read Q15 s = word_xor (inblock (4*i+3)) (word_reversefields 8 (EL 10 rk)) /\
    read X23 s = word_subword (word_xor (inblock (4*i+1)) (word_reversefields 8 (EL 10 rk)):int128) (64,64):int64 /\
    read X28 s = word_subword (word_xor (inblock (4*i+1)) (word_reversefields 8 (EL 10 rk)):int128) (0,64):int64`;;

(* Build a leg pre/post state predicate `\s. aligned_bytes_loaded s (word pc) swpS_mc /\
   read PC s = word(pc+off) /\ <BETA-reduced+ADD_CLAUSES-normalized inv idx body>` as a FLAT conjunction.
   This EXACTLY matches what ENSURES_SEQUENCE_TAC / ENSURES_WHILE_UP_TAC produce for their obligations
   (program_decodes /\ PC /\ Q s, then BETA_TAC), so a leg's conclusion unifies via MATCH_MP_TAC against
   the composed goal.  (The old form mk_conj(`aligned/\PC`, list_mk_comb(inv,[idx;s])) was UNREDUCED +
   nested-associated -> MATCH_MP_TAC No match.) *)
let leg_state inv off idx =
  let body = rhs(concl((TOP_DEPTH_CONV BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                        (list_mk_comb(inv,[idx;`s:armstate`])))) in
  mk_abs(`s:armstate`,
    list_mk_conj(`aligned_bytes_loaded s (word pc) swpS_mc` ::
                 mk_eq(`read PC s`,mk_comb(`word:num->int64`,mk_binop `+` `pc:num` off)) ::
                 conjuncts body));;

(* body-leg goal builder *)
let mk_body_goal inv =
  mk_imp(`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
      EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ i < loop_count - 1 /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,1856) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,1856) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192)`,
   list_mk_icomb "ensures" [`arm`;
     (* pre/post as FLAT, BETA-reduced conjunctions (leg_state) so this leg composes via MATCH_MP_TAC
        against ENSURES_SEQUENCE/WHILE obligations (which are flat+reduced).  POST carries aligned too. *)
     leg_state inv `0x1ec` `i:num` ;
     leg_state inv `0x4b0` `i+1` ;
     (* Frame MUST also permit the callee-saved regs the body clobbers (preamble saved/restores them):
        X19..X30 and the FULL Q8..Q15 (ABI only permits Q8..Q15 :> tophalf).  Matches deint's loop frame
        (swp_deint.ml 825-828).  Without these, Q9/Q12/Q15/X23/X28 etc. aren't subsumed -> frame fails. *)
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;

let body_goal = mk_body_goal swpS_inv8;;

(* store sites for MERGE_CTR128_TAC *)
let merges = [(10,176);(28,192);(31,176);(41,160);(50,160);(63,208);(81,192);(95,208)];;

(* keep-latest stepper over a reg-set (per-reg max-state prune): keeps only the latest read of each
   listed reg + the current step, discards other old-state reads.  With the ABBREV-to-init_ setup the
   carried values are init_-var expressions (not read-state towers), so the kept set stays BOUNDED
   (~530 asms) and the final Q30 tower is orphan-free + collapsible.  Native has no timeout. *)
let gc2 keeplist c = try let l=lhs c in let rd,st=dest_comb l in let rr,cc=dest_comb rd in
   if is_const cc && mem (fst(dest_const cc)) keeplist then
     (match st with Var(nm,_) when String.length nm>=2 && nm.[0]='s' ->
        (try Some(fst(dest_const cc), int_of_string(String.sub nm 1 (String.length nm-1))) with _->None) |_->None) else None
  with _->None;;
(* discard predicate: TRUE = drop.  Keep (a) the current step's reads, (b) the per-reg latest read of
   each keeplist reg, and (c) any read of in_p-memory (the read-only input-split anchors, needed for the
   prefetch loads to fold to inblock across stepping - they read s0 but must NOT be discarded). *)
let gkeepN keeplist th sname = ARM_STEP_TAC th [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) -> let cs=map(fun(_,t)->concl t)asl in
    let mx=map(fun r->(r,itlist(fun c m->match gc2 keeplist c with Some(rr,k)when rr=r&&k>m->k|_->m)cs(-1)))keeplist in
    DISCARD_ASSUMPTIONS_TAC(fun th->let c=concl th in
      (* MAYCHANGE assumptions: KEEP only the one whose 2nd state arg is the CURRENT step (sname) -
         discard superseded ones (older 2nd-arg) so exactly ONE `s0 s<final>` survives at the end, which
         ENSURES_FINAL_STATE_TAC / MONOTONE_MAYCHANGE_TAC then uses to discharge the frame in-context. *)
      if (try can (find_term (fun x -> match x with Const("MAYCHANGE",_) -> true | _ -> false)) c with _->false)
      then (try let _,args = strip_comb c in string_of_term(last args) <> sname with _ -> false) else
      if (try free_in `in_p:int64` (lhs c) with _->false) then false else
      match gc2 keeplist c with
      Some(r,k)->k<List.assoc r mx
      |None->(try let l=lhs c in let rd,st=dest_comb l in (match st with Var(nm,_)->nm<>sname&&String.length nm>=1&&nm.[0]='s'|_->false)with _->false))(asl,w));;

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

(* GHASH-reduce Q-regs + the counter/input X-lanes carried through the reduce lineage. *)
let REDSETX = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q8";"Q13";"Q14";"Q16";"Q17";"Q28";"Q29";"Q30";"Q31";
               "X7";"X8";"X11";"X13";"X14";"X17";"X23";"X24";"X25";"X26";"X28";"X30"];;

(* loop-head scalar lanes to GHOST_INTRO (so their s0 value is a logic var kept across the body, not a
   discarded ghost).  X23/X28 ARE here (consumed early @0x210->Q13@0x21c) so they must be KEPT; the
   invariant now ALSO pins them, so GHOST_INTRO turns the pin conjunct into ghost_X23 = subword(...),
   which is exactly the equation the block-4i+1 keystream collapse needs. *)
let ghost_lanes = ["X7";"X8";"X17";"X22";"X23";"X24";"X25";"X26";"X28";"X29";"X30";"X10";"X14";"X19";"X27"];;

(* input-split preamble (deint recipe), EXTENDED to blocks 4i+0..4i+7: the body loads the current
   group (4i+0..3, ldp [x0]/[x0,#16/32/48]) AND prefetches the next group (4i+4..7) into the carried
   lanes X23/X28/Q10/Q15/[sp+192/208] for iteration i+1.  Splitting all 8 blocks into bytes64 halves
   lets both the current ciphertext AND the inv(i+1) carried-lane pins resolve.  Bound 4i+7<nblocks
   needs i < loop_count-2 (the deint FILL/DRAIN steady range). *)
let INPUT_SPLIT_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * (4*i+0))))) s0 = inblock (4*i+0) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+1))))) s0 = inblock (4*i+1) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+2))))) s0 = inblock (4*i+2) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+3))))) s0 = inblock (4*i+3) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+4))))) s0 = inblock (4*i+4) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+5))))) s0 = inblock (4*i+5) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+6))))) s0 = inblock (4*i+6) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+7))))) s0 = inblock (4*i+7)`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 1` THEN
       UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`;
     ARITH_RULE `16 * (4*i+4) = 64*i+64`; ARITH_RULE `16 * (4*i+5) = 64*i+80`;
     ARITH_RULE `16 * (4*i+6) = 64*i+96`; ARITH_RULE `16 * (4*i+7) = 64*i+112`]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

(* ============================================================================
   DIAGNOSTIC HARNESS (stage 1): run setup + input-split + stepping + FINAL_STATE, close [0]-[6],
   then DUMP goal [7] (the Q30 GHASH tag) + its orphan count to a file so we can (a) confirm the
   stepping yields a clean tower (no read Qk sN orphans) and (b) develop the deint g3-body closer
   against the concrete term.  Uses g/e (not prove) so it never hard-fails.  Native, no timeout.
   ============================================================================ *)
(* ABBREV-based setup (John's key fix): GHOST_INTRO the loop-head scalar lanes, then ENSURES_INIT +
   input-split, then ABBREV every remaining `read C s0` to init_ logic vars.  This makes every in-body
   value a stable init_-expression that DISCARD_OLDSTATE never drops, keeping the reduce towers BOUNDED
   (init_ atoms, not read-state megabyte towers).  Then gkeepN keeps the reduce lineage -> orphan-free Q30. *)
let setup_tac =
  STRIP_TAC THEN REWRITE_TAC[fst SWPS_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  INPUT_SPLIT_TAC THEN
  (* ABBREV all non-j-parametric `read C s0` reads to init_ vars, EXCEPT in_p-memory reads: those
     are the read-only input-split anchors (read(bytes64 in_p+X) s0 = subword(inblock..)) that the
     body's prefetch loads (at s39/s55/s66) fold through - abbreviating them breaks the inblock fold
     (the anchor becomes init_k=subword(inblock..) and the reduced-to-s0 prefetch read finds no target). *)
  (fun (asl,w) ->
    let jv = `j:num` in
    let reads0 = setify(flat(map (fun (_,th) -> find_terms (fun t -> try let h,a=strip_comb t in
         fst(dest_const h)="read" && length a=2 && string_of_term(hd(tl a))="s0" with _->false) (concl th)) asl)) in
    let toab = filter (fun t -> not(free_in jv t) && not(free_in `in_p:int64` t)
                              && string_of_term t <> "read PC s0") reads0 in
    (EVERY (List.mapi (fun k t -> ABBREV_TAC (mk_eq(mk_var(Printf.sprintf "init_%d" k, type_of t), t))) toab)) (asl,w));;

(* Stepper: gkeepN keep-latest over REDSETX (keeps Q30 + reduce lineage; plain discard would drop
   Q30@176).  The init_-ABBREV setup keeps the towers bounded.  Prefetch input reads for blocks 4i+5/6/7
   (feeding the i+1 pins X23/Q10/Q15) settle as read(bytes64 (in_p+word(64i))+word K) sN with a NESTED
   address + a non-s0 state, so they don't auto-match the s0 split anchors; a post-step normalization
   (addr-fold + input-forall @ current state) resolves them (see prefetch_fold_tac). *)
let step_body_tac =
  setup_tac THEN
  (fun (asl,w) ->
     (MAP_EVERY (fun k ->
        gkeepN REDSETX SWPS_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                                 IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k merges then MERGE_CTR128_TAC (List.assoc k merges) ("s"^string_of_int k)
         else ALL_TAC))
       (1--177)) (asl,w)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                           IN_P_ADDR_FOLD_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let closers_0_6 =
  [ REWRITE_TAC[ARITH_RULE `64*(i+1)=64*i+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[ARITH_RULE `64*(i+1)=64*i+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[ZXNEST4] THEN
      SUBGOAL_THEN `word (4*i+6):int32 = word(4*(i+1)+2)` SUBST1_TAC THENL
       [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+2`);
    REWRITE_TAC[ZXZX32] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[aes7c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZXZX32] THEN
      SUBGOAL_THEN `word_add (word (4*i+6):int32) (word 2) = word(4*(i+1)+4):int32` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+4`);
    REWRITE_TAC[aes8c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZXZX32] THEN
      SUBGOAL_THEN `word_add (word (4*i+6):int32) (word 1) = word(4*(i+1)+3):int32` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+3`);
    REWRITE_TAC[aes10p] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZXZX32] THEN
      SUBGOAL_THEN `word_add (word (4*i+6):int32) (word 3) = word(4*(i+1)+5):int32` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+5`)];;

(* ---- goal [7] closer: Q30 GHASH tag.  The stepped tower (0 orphans, ghost pins for X23/X28 in asms)
   collapses all 4 keystreams to nist_cipher_block, then the deint g3-body reduce reconstruction folds
   the pmull-Karatsuba tower to the settled nist_ghash..(4(i+1)).  VALIDATED interactively end-to-end.
   ksf is built inside (MATCH_MP KEYSTREAM_FOLD the rk-list hyp, which is in the assumptions). *)
(* collapse-only part of the Q30 closer (steps 0-4): fold ghost pins + all 4 keystreams to
   nist_cipher_block, leaving the deint g3-body pmull-Karatsuba tower over the settled cipherblocks.
   Split out so the harness can dump the post-collapse form (isolating collapse from reconstruction). *)
let collapse_q30 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "collapse_q30: rk-list hyp not found" in
    let ksf = MATCH_MP KEYSTREAM_FOLD rkth in
    let ghostpins = List.filter_map (fun (_,th) ->
      let c = concl th in
      if is_eq c then (match lhs c with
        | Var(nm,_) when String.length nm>=6 && String.sub nm 0 6="ghost_"
            && can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="inblock" with _->false)) (rhs c)
          -> Some th | _ -> None) else None) asl in
    (
    (* (0) normalize the RHS tag index 4*(i+1) -> 4*i+4 so the SUC^4 unfold + GHASH_ACC_APPEND fire. *)
    REWRITE_TAC[ARITH_RULE `4*(i+1) = 4*i+4`] THEN
    (* (1) fold X23/X28 ghost pins + recombine word_join(hi)(lo) -> word_xor(inblock(4i+1))(rk10). *)
    REWRITE_TAC(JOIN_SUBWORD_RECOMBINE :: ghostpins) THEN
    (* (2) NO byteswap-split here - leave the goal byteswap128-wrapped so the reconstruction (which does
       deint's single byteswap-split + MATCH_MP verbatim) applies.  The keystream folds below reach the
       keystreams DEEP in the LHS tower regardless of the outer word_subword/byteswap wrapper. *)
    (* (3) normalize all 4 keystream syntactic forms -> aes10p, lane-join, ksf, counter-arith, CT_TO_NCB.
       NB the RHS tag is now 4*i+4; the `4*i+4=(4*i+2)+2` rewrite would hit it, but step (4)'s inverse
       restores it, so it round-trips.  The keystream counter args (4i+2..5) are what genuinely fold. *)
    REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C; GSYM aes10p] THEN
    REWRITE_TAC[JOIN_XOR_LANES] THEN
    REWRITE_TAC[ksf] THEN
    REWRITE_TAC[ARITH_RULE `4*i+5 = (4*i+3)+2`; ARITH_RULE `4*i+4 = (4*i+2)+2`;
                ARITH_RULE `4*i+3 = (4*i+1)+2`; ARITH_RULE `4*i+2 = (4*i+0)+2`] THEN
    REWRITE_TAC[CT_TO_NCB] THEN
    (* (4) canonicalize block indices to flat 4*i+K. *)
    REWRITE_TAC[ARITH_RULE `(4*i+0)+2 = 4*i+2`; ARITH_RULE `(4*i+1)+2 = 4*i+3`;
                ARITH_RULE `(4*i+2)+2 = 4*i+4`; ARITH_RULE `(4*i+3)+2 = 4*i+5`;
                ARITH_RULE `4*i+0 = 4*i`]
    ) (asl,w);;

let close_goal7 : tactic =
  fun (asl,w) ->
    (
    collapse_q30 THEN
    (* (5) deint g3-body reduce reconstruction (swp_deint.ml 2127-2209, VERBATIM, 4*i variant).  The goal
       here is byteswap128-wrapped `word_subword(word_join(tower))(64,128) = byteswap128(nist_ghash..4*i+4)`
       (collapse did NOT strip byteswap).  deint's normalize + SINGLE byteswap-split + MATCH_MP + ABBREV
       + RECONSTRUCT applies directly. *)
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
    SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
      `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
       word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (4 * i)))`;
      `cipherblock_0 = nist_cipher_block nonce rk inblock (4 * i)`;
      `cipherblock_1 = nist_cipher_block nonce rk inblock (4 * i + 1)`;
      `cipherblock_2 = nist_cipher_block nonce rk inblock (4 * i + 2)`;
      `cipherblock_3 = nist_cipher_block nonce rk inblock (4 * i + 3)`;
      `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
      `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
      REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
      ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
       `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                   `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                   `sofar:int128`; `cipherblock_0:int128`]
                  GHASH_POLYVAL_ACC_BATCHED) THEN
    REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
     `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    EXPAND_TAC "sofar" THEN
    REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
    REWRITE_TAC[ARITH_RULE `4*i+4 = SUC(SUC(SUC(SUC(4*i))))`] THEN
    REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]
    ) (asl,w);;


(* ---- goal [8]: X1 = word_sub (word (loop_count - i)) (word 1) = word(loop_count - (i+1)).  Uses the
   loop bounds (2<=loop_count, i<loop_count-2) in the assumptions.  Validated in MCP (hyps=0). ---- *)
(* X1 body goal (with inv X1 = word(loop_count-(i+1))): word_sub(word(loop_count-(i+1)))(word 1) =
   word(loop_count-((i+1)+1)) = word(loop_count-(i+2)).  Needs loop_count-(i+2)=(loop_count-(i+1))-1 and
   1<=loop_count-(i+1) (from i<loop_count-2). *)
let close_goal8 : tactic =
  fun (asl,w) ->
    let bnds = List.filter_map (fun (_,th) -> let c = concl th in
      if c = `2 <= loop_count` || c = `i < loop_count - 2` || c = `i < loop_count - 1` then Some th else None) asl in
    (MAP_EVERY (fun th -> ASSUME_TAC th) bnds THEN
     SUBGOAL_THEN `loop_count - ((i+1)+1) = (loop_count - (i+1)) - 1 /\ 1 <= loop_count - (i+1)` STRIP_ASSUME_TAC THENL
      [MAP_EVERY (fun th -> MP_TAC th) bnds THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[WORD_SUB; VAL_WORD_1] THEN
     REWRITE_TAC[GSYM VAL_WORD_1] THEN AP_TERM_TAC THEN
     MAP_EVERY (fun th -> MP_TAC th) bnds THEN ARITH_TAC) (asl,w);;

(* ---- carried-lane pin preservation closers (goals 3-9 in the dump), all pure word identities +
   the block-index shift 4*(i+1)+k = 4*i+(k+4).  Validated in MCP (hyps=0). ---- *)
(* [sp+176] counter -> rev8(ctr_block(4(i+1)+3)) : reassembled reversed-lane counter, +1 increment. *)
let close_ctr176 : tactic =
  REWRITE_TAC[ZXNEST4;ZXZX32] THEN
  SUBGOAL_THEN `word_add (word (4*i+6):int32) (word 1) = word(4*(i+1)+3):int32` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ACCEPT_TAC (mk_cbv `4*(i+1)+3`);;
(* Q10/Q15/[sp+192]/[sp+208] lane pins: word_join(word_xor lanes) = word_xor(inblock(4(i+1)+k))(rk10). *)
let close_lanejoin : tactic =
  REWRITE_TAC[ARITH_RULE `4*(i+1)+2 = 4*i+6`; ARITH_RULE `4*(i+1)+3 = 4*i+7`] THEN
  REWRITE_TAC[JOIN_XOR_LANES];;
(* X23/X28 subword pins: word_xor(subword..)(subword..) = subword(word_xor(inblock(4(i+1)+1))(rk10))(lane). *)
let close_subwordpin : tactic =
  REWRITE_TAC[ARITH_RULE `4*(i+1)+1 = 4*i+5`] THEN CONV_TAC WORD_BLAST;;

(* output-block keystream identities (the 3-way conjunction close_goal9 leaves): each
   word_xor(<aesNc-tower/aes10p>)(input^rk10) = word_xor(rev8(aes128_cipher(ctr(4i+k))))(inblock).
   Fold: JOIN_SUBWORD_RECOMBINE (block-4i+1 lanes) + normalize aesNc->aes10p + KEYSTREAM_FOLD.  The RHS
   is already in aes128_cipher form (NOT nist_cipher_block) so ksf lands directly. Validated in MCP. *)
let close_ksfold : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "close_ksfold: no rk-hyp" in
    (REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD rkth]) (asl,w);;

(* ---- goal [9]: output-forall j < 4*(i+1).  Split into the OLD stores (j<4*i, from the invariant) and
   the 4 NEW stores (blocks 4*i+0..3, this group), each reconstructing to word_xor(aes_ctr_block j)(inblock j).
   Re-indexed to swp_S's 4*i-based invariant (NOT deint's 4*(i+1)).  Candidate - refine post-dump. ---- *)
let close_goal9 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "close_goal9: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
     ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
        ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
     CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
     (* the reconstruction leaves the 4 output-block keystream identities; fold them (ksfold). *)
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD rkth]) (asl,w);;

(* ---- goal [10]: MAYCHANGE frame.  Shipped-proof idiom (cf. _swp_S_via_equiv_correct.ml): MP all the per-step
   MAYCHANGE assumptions, then a SINGLE MONOTONE_MAYCHANGE_TAC.  (REPEAT(MONOTONE.. ORELSE SUBSUMED..)
   LOOPS - MONOTONE makes trivial progress forever.) ---- *)
(* The frame goal is `<declared frame> s0 s177`.  gkeepN keeps MANY MAYCHANGE assumptions (one per step,
   various state pairs); MONOTONE_MAYCHANGE_TAC's FIRST_ASSUM may pick a WRONG one (e.g. a per-step
   fragment sk s(k+1)) -> "No match".  Fix: find the ONE full-body maychange assumption whose 2nd state
   arg is s177 (the final state), MP it, then subsumed.  Fallbacks retained. *)
let close_goal10 : tactic =
  fun (asl,w) ->
    let is_mc c = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c with _->false in
    (* gkeepN leaves several MAYCHANGE-bearing assumptions; the RIGHT one is the full-body `bigR s0 s177`.
       Try each maychange assumption with MATCH_MP pth + SUBSUMED; whichever works wins.  First establish
       the current-group output-store bound `4*i+3 < nblocks` (SUBSUMED needs it for out_p containment). *)
    let pth = prove(`R s s' ==> R subsumed R' ==> R' s s'`, REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
    (* establish the out_p-store bound SUBSUMED needs.  Body-leg: 4*i+3<nblocks (from i<loop_count-2).
       FILL (i=0, concrete blocks 0..3): 8<=nblocks (from 2<=loop_count) covers it.  Assert both via TRY. *)
    (TRY(SUBGOAL_THEN `4*i+3 < nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; `i < loop_count - 1`; `i < loop_count - 2`; `2 <= loop_count`] THEN ARITH_TAC;
       ALL_TAC]) THEN
     TRY(SUBGOAL_THEN `8 <= nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; `2 <= loop_count`] THEN ARITH_TAC;
       ALL_TAC]) THEN
     (* try each maychange assumption; the correct cumulative s0 s177 one works via pth+SUBSUMED.
        Also try the shipped idiom (MONOTONE) + folding all maychange asms as fallbacks. *)
     (* the correct cumulative `bigR s0 s177` closes via MATCH_MP pth + REWRITE[ETA;ABI] + SUBSUMED.
        REWRITE ABI is ESSENTIAL: the declared frame's MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI must be
        expanded to the register list so SUBSUMED can check per-reg containment (VERIFIED in MCP). *)
     (fun (asl2,w2) ->
        let mcths = List.filter_map (fun (_,th) -> if is_mc(concl th) then Some th else None) asl2 in
        (FIRST (map (fun th -> fun g ->
            (MATCH_MP_TAC(MATCH_MP pth th) THEN
             REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
             SUBSUMED_MAYCHANGE_TAC) g) mcths)) (asl2,w2))) (asl,w);;

(* per-conjunct dispatcher.  The expensive close_goal7 (BITBLAST + reduce reconstruction) is gated to
   run ONLY on the Q30 conjunct (is_eq & RHS mentions nist_ghash).  Every OTHER goal gets a broad FIRST
   over all the cheap closers, so routing can't mis-fire on subtle shape differences - whichever closes
   wins, and if none do the goal is left for the dump. *)
(* CHEAP closers only - close_goal7 (Q30, expensive) is EXCLUDED and applied separately ONCE.  The Q30
   conjunct (is_eq & RHS nist_ghash) is explicitly SKIPPED here (fail) so the loop leaves it for the
   dedicated pass; every other goal gets the broad FIRST. *)
(* MUST t = t but FAILS unless it fully closes the goal (no subgoals left).  Prevents no-op-success
   closers (REWRITE that doesn't apply) from being mistaken for a close in the FIRST dispatch. *)
let (MUST:tactic->tactic) = fun t (asl,w) ->
  let gs = t (asl,w) in
  let _,subs,_ = gs in
  if subs = [] then gs else failwith "MUST: goal not closed";;
let close_one : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    (* DEFER Q30-family goals (large reduce towers) to phase2 - they carry word_pmul/byteswap128 and
       are far too big for the cheap WORD_RULE/WORD_BLAST closers (which would grind for minutes). *)
    if String.length(string_of_term w) > 5000 then failwith "close_one: large Q30-family goal deferred"
    else if is_eq w && has "nist_ghash" (rhs w) then failwith "close_one: Q30 deferred"
    else
      (FIRST (map MUST
        [ close_ksfold;                                  (* output-block keystream identities (conj) *)
          close_goal9;                                   (* output-forall *)
          close_goal10;                                  (* MAYCHANGE frame *)
          el 0 closers_0_6; el 1 closers_0_6;            (* ptr X0/X2 *)
          el 2 closers_0_6; close_ctr176;                (* [sp+160]/[sp+176] counters *)
          el 3 closers_0_6;                              (* X13 *)
          el 4 closers_0_6; el 5 closers_0_6; el 6 closers_0_6;  (* aes7c/8c/10p *)
          close_lanejoin;                                (* Q10/Q15/[sp+192/208] lane pins *)
          close_subwordpin;                              (* X23/X28 subword pins *)
          close_goal8;                                   (* X1 decrement *)
          CONV_TAC WORD_RULE ])) (asl,w);;                (* misc arith *)

(* ---- FINAL single-tactic dispatcher for the assembled prove(): applied to EACH conjunct after
   REPEAT CONJ_TAC.  Shape-gated so close_goal7 (expensive) runs only on the Q30 (NG) conjunct and
   close_goal10 only on the frame.  Each branch fully closes-or-fails. ---- *)
let close_all_tac : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    if has_mc w then close_goal10 (asl,w)                                    (* MAYCHANGE frame *)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)      (* aligned (preserved asm) *)
    else if is_forall w then MUST close_goal9 (asl,w)                        (* output-forall *)
    else if is_eq w && has "nist_ghash" (rhs w) then close_goal7 (asl,w)     (* Q30 GHASH tag *)
    else
      (FIRST (map MUST
        [ close_ksfold; close_goal9;
          el 0 closers_0_6; el 1 closers_0_6; el 2 closers_0_6; close_ctr176; el 3 closers_0_6;
          el 4 closers_0_6; el 5 closers_0_6; el 6 closers_0_6;
          close_lanejoin; close_subwordpin; close_goal8; CONV_TAC WORD_RULE ])) (asl,w);;

(* The assembled body-leg tactic (single prove()): step + split + dispatch. *)
let body_leg_tac : tactic =
  step_body_tac THEN REPEAT CONJ_TAC THEN close_all_tac;;

(* ===== the assembled body-leg theorem: one loop body inv i @0x1ec -> inv(i+1) @0x4b0. ===== *)
let BODYLEG = prove(body_goal, body_leg_tac);;

(* ============================================================================
   FILL leg: 0x88 -> 0x1ec establishing swpS_inv8 0 (i=0), for the steady case 2 <= loop_count.
   swp_S's 0x88..0x1ec is byte-identical to deint's prefix; deint's FILL_LEG_LC2 stepping (swp_deint
   1430-1511) transfers (89 instrs, guard cbz x1@0x88 not taken since loop_count>=1, sub x1@0x88... the
   0x1e4 sub x1,#1 + cbz@0x1e8 is at the END - but FILL stops at 0x1ec which is AFTER that cbz falls
   through for loop_count>=2).  Endpoint invariant = swpS_inv8 0 (mid-pipeline) so closers reconstruct
   the i=0 partials.  Uses g/e diagnostic first (dump goals) like the body-leg, then assemble prove().
   ============================================================================ *)
let mk_fill_goal inv =
  mk_imp(`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
      EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,1856) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,1856) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192)`,
   list_mk_icomb "ensures" [`arm`;
     mk_abs(`s:armstate`, list_mk_conj
       [`aligned_bytes_loaded s (word pc) swpS_mc`; `read PC s = word (pc + 0x88)`;
        `read X0 s = in_p`; `read X2 s = out_p`; `read X3 s = tag_p`; `read X4 s = ivec_p`;
        `read X6 s = htable_p`; `read SP s = stackpointer`;
        `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
        `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2)`;
        `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
        `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
        `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
        `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
        `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
        `read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64`;
        `read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64`;
        `read Q7 s = word 13979173243358019584`;
        `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64`;
        `read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64`;
        `read X13 s = word_zx (word 2:int32):int64`; `read X15 s = word(len_bits DIV 8)`;
        `read X1 s = word loop_count`; `read X7 s = word nblocks`; `read X16 s = word loop_remain`;
        `read Q30 s = byteswap128 tag0`;
        `htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s`;
        `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`]) ;
     leg_state inv `0x1ec` `0` ;
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;
let fill_goal = mk_fill_goal swpS_inv8;;

(* FILL setup: like the body-leg setup but at 0x88 entry.  The guard cbz x1@0x88: x1=word loop_count,
   loop_count>=2 so val(word loop_count)=loop_count != 0 -> not taken -> falls to 0x8c.  The mid-FILL
   sub x1,#1 @0x1e4 + cbz@0x1e8: after it x1=word(loop_count-1); for loop_count>=2, loop_count-1 != 0
   -> cbz not taken -> falls to 0x1ec (the head).  Input-split blocks 0..7 (the fill reads groups 0,1). *)
let FILL_INPUT_SPLIT_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 4)))) s0 = inblock 4 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 5)))) s0 = inblock 5 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 6)))) s0 = inblock 6 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 7)))) s0 = inblock 7`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `7 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`; ARITH_RULE `16 * 2 = 32`;
     ARITH_RULE `16 * 3 = 48`; ARITH_RULE `16 * 4 = 64`; ARITH_RULE `16 * 5 = 80`;
     ARITH_RULE `16 * 6 = 96`; ARITH_RULE `16 * 7 = 112`; WORD_ADD_0]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

(* fill guard-resolution: val(word loop_count)=loop_count, ~(loop_count=0), and after sub@0x1e4:
   val(word_sub(word loop_count)(word 1))=loop_count-1, ~(loop_count-1=0). *)
let fill_valfacts_tac =
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1` ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word 1:int64) <= val(word loop_count:int64)` MP_TAC THENL
     [REWRITE_TAC[VAL_WORD_1] THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[VAL_WORD_SUB_CASES; th; VAL_WORD_1]) THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count - 1 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC];;

(* FILL merge sites (from deint's first-89-instr prefix, byte-identical): (11,192)(12,176)(19,160)
   (24,208)(31,192)(37,208).  Verify by disasm if the diagnostic shows mis-merges. *)
let fill_merges = [(11,192);(12,176);(19,160);(24,208);(31,192);(37,208)];;

let fill_step_tac =
  STRIP_TAC THEN REWRITE_TAC[fst SWPS_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  FILL_INPUT_SPLIT_TAC THEN
  fill_valfacts_tac THEN
  (* guard cbz@0x88: step 1, resolve the COND via ~(loop_count=0) *)
  ARM_STEPS_TAC SWPS_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word loop_count:int64) = loop_count`;
                             ASSUME `~(loop_count = 0)`; COND_CLAUSES]) THEN
  (* steps 2..88 with per-step subword + MERGE at fill_merges; then step 89 (the mid cbz) resolves via
     the loop_count-1 valfacts; then 90..N to reach 0x1ec.  Use gkeepN REDSETX to keep the i=0 partials. *)
  (fun (asl,w) ->
     (MAP_EVERY (fun k ->
        gkeepN REDSETX SWPS_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k fill_merges then MERGE_CTR128_TAC (List.assoc k fill_merges) ("s"^string_of_int k)
         else ALL_TAC))
       (2--88)) (asl,w)) THEN
  ARM_STEPS_TAC SWPS_EXEC [89] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1`;
                             ASSUME `~(loop_count - 1 = 0)`; COND_CLAUSES]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ---- FILL closers.  At i=0 the counters are built from CONSTANTS (word 144115188075855872 =
   shl(bytereverse 2)32, etc.) not X13-derived, so the counter/aesNc closers rewrite those constants to
   the bytereverse form then use mk_cbv.  (deint FILL_LEG_LC2 lines 1527-1530.) ---- *)
let fill_ctr_consts = [
  prove(`word 144115188075855872:int64 = word_shl (word_zx (word_bytereverse (word 2:int32)):int64) 32`, CONV_TAC WORD_BLAST);
  prove(`word 216172782113783808:int64 = word_shl (word_zx (word_bytereverse (word 3:int32)):int64) 32`, CONV_TAC WORD_BLAST);
  prove(`word 288230376151711744:int64 = word_shl (word_zx (word_bytereverse (word 4:int32)):int64) 32`, CONV_TAC WORD_BLAST);
  prove(`word 360287970189639680:int64 = word_shl (word_zx (word_bytereverse (word 5:int32)):int64) 32`, CONV_TAC WORD_BLAST)];;
(* mk_cbv_const cval: CTR_BLOCK_BUILD_V instance for the constant-lane counter (the hi lane is
   word_shl(word_zx(word_bytereverse(word cval)))32 directly, not via word(4i+6)+k). *)
let mk_cbv_const cval =
  let inst = INST [`word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64`,`ivhi:int64`;
                   `word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64`,`ivlo:int64`;
                   mk_small_numeral cval,`cval:num`] CTR_BLOCK_BUILD_V in
  MP inst (prove(lhand(concl inst), REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST));;

(* FILL per-conjunct dispatcher (i=0, no Q30 tower). *)
let fill_close_all : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    if has_mc w then close_goal10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then
      (* output-forall j<4*0: vacuous *) (REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT] THEN
        REWRITE_TAC[ARITH_RULE `j < 0 <=> F`]) (asl,w)
    else
      (FIRST (map MUST
        [ (* ptrs: in_p = word_add in_p (word(64*0)) *)
          (REWRITE_TAC[ARITH_RULE `64*0=0`; WORD_ADD_0] THEN REFL_TAC);
          CONV_TAC WORD_RULE;
          (* Q30: byteswap128 tag0 = byteswap128(nist_ghash..(4*0)) *)
          (REWRITE_TAC[ARITH_RULE `4*0=0`; list_of_seq; nist_ghash]);
          (* X13: word 6 = word_zx(word(4*0+6)) *)
          (REWRITE_TAC[ARITH_RULE `4*0+6=6`; ZXNEST4; ZXZX32] THEN CONV_TAC WORD_BLAST);
          (* [sp+160] counter ctr(4*0+2)=ctr 2 *)
          (REWRITE_TAC[ARITH_RULE `4*0+2=2`; ZXNEST4; ZXZX32] THEN REWRITE_TAC fill_ctr_consts THEN
           ACCEPT_TAC(mk_cbv_const 2));
          (* [sp+176] counter ctr(4*0+3)=ctr 3 *)
          (REWRITE_TAC[ARITH_RULE `4*0+3=3`; ZXNEST4; ZXZX32] THEN REWRITE_TAC fill_ctr_consts THEN
           ACCEPT_TAC(mk_cbv_const 3));
          (* aes7c(4*0+4)=aes7c 4 *)
          (REWRITE_TAC[ARITH_RULE `4*0+4=4`; aes7c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
           REWRITE_TAC fill_ctr_consts THEN ACCEPT_TAC(mk_cbv_const 4));
          (* aes8c(4*0+3)=aes8c 3 *)
          (REWRITE_TAC[ARITH_RULE `4*0+3=3`; aes8c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
           REWRITE_TAC fill_ctr_consts THEN ACCEPT_TAC(mk_cbv_const 3));
          (* aes10p(4*0+5)=aes10p 5 *)
          (REWRITE_TAC[ARITH_RULE `4*0+5=5`; aes10p] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
           REWRITE_TAC fill_ctr_consts THEN ACCEPT_TAC(mk_cbv_const 5));
          (* X1: word_sub(word loop_count)(word 1) = word(loop_count-(0+1)) = word(loop_count-1); needs
             1<=loop_count (from 2<=loop_count). *)
          (fun (a,w) ->
            let bnd = try snd(find (fun (_,th)->concl th = `2 <= loop_count`) a) with _ -> TRUTH in
            (REWRITE_TAC[ARITH_RULE `(0:num)+1=1`] THEN
             SUBGOAL_THEN `1 <= loop_count` ASSUME_TAC THENL [MP_TAC bnd THEN ARITH_TAC; ALL_TAC] THEN
             ASM_SIMP_TAC[WORD_SUB; VAL_WORD_1] THEN REWRITE_TAC[GSYM VAL_WORD_1] THEN
             AP_TERM_TAC THEN MP_TAC bnd THEN ARITH_TAC) (a,w));
          (* lane pins Q10/Q15/[sp+192/208]: word_join(word_xor lanes)=word_xor(inblock(4*0+2/3))(rk10) *)
          (REWRITE_TAC[ARITH_RULE `4*0+2=2`; ARITH_RULE `4*0+3=3`] THEN REWRITE_TAC[JOIN_XOR_LANES]);
          (* subword pins X23/X28: word_xor(subword..)=subword(word_xor(inblock(4*0+1))(rk10))(lane) *)
          (REWRITE_TAC[ARITH_RULE `4*0+1=1`] THEN CONV_TAC WORD_BLAST);
          CONV_TAC WORD_RULE ])) (asl,w);;

(* Prove a leg and GEN_ALL the result.  NB: prove(mk_imp(precond, ...)) does NOT auto-generalize the free
   vars (unlike prove of an explicit `!vars. ...`), so GEN_ALL is essential: otherwise MATCH_MP_TAC of the
   leg treats key_p (free) as fixed and leaves NO ?key_p, and the caller's EXISTS_TAC key_p (in SWPS_FROM88)
   fails with "Goal not existentially quantified". *)
let leaf_prove label goal tac = GEN_ALL(prove(goal, tac));;

(* ===== the FILL theorem (single prove) ===== *)
let FILLLEG = leaf_prove "FILLLEG" fill_goal (fill_step_tac THEN REPEAT CONJ_TAC THEN fill_close_all);;

(* ============================================================================
   DRAINTAIL leg: g5 of the WHILE = swpS_inv8(loop_count-1) @ 0x4b0 -> post @ 0x710.
   Decompose:
     REDUCELAST : swpS_inv8(loop_count-1) @0x4b0 -> BRIDGE @0x61c
                  (cbnz@0x4b0 NOT taken since X1=word 0; reduce_last drains the in-flight GHASH,
                   settles Q30 4*(loop_count-1)->4*loop_count, stores the last group's 4 outputs.)
     SWPS_TAIL  : BRIDGE @0x61c -> post @0x710  (byte-identical to deint's DEINT_TAIL, ported to swpS_mc).
   The BRIDGE state is deint's LEG1 0x61c post (settled seam): X0/X2 = ptr+64*loop_count, X1=word 0,
   X13=word(4*loop_count+2), Q30=byteswap128(nist_ghash..(4*loop_count)), all j<4*loop_count stored.
   Frame = the BROAD frame (adds tag_p, ivec_p) - the tail writes them; the WHILE needs ONE shared frame.
   BODYLEG/FILLLEG (narrow frame) are widened to this broad frame at glue time via ENSURES_FRAME_SUBSUMED.
   ============================================================================ *)

(* The shared BROAD frame (deint uses this uniformly across all legs, swp_deint 1755-1760). *)
let swps_broad_frame =
  `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
   MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks);
              memory :> bytes(tag_p:int64, 16); memory :> bytes(ivec_p:int64, 16);
              memory :> bytes(word_add stackpointer (word 160):int64, 64)]`;;

(* The full nonoverlapping precondition shared by all legs (deint leg1_lc2_stmt antecedent, with key_p
   dropped - swp_S has no key_p in the loop; matches mk_body_goal's set + adds the key-free ones). *)
let swps_leg_precond =
  `([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
      EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,1856) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (key_p:int64,176) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (key_p:int64,176) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (key_p:int64,176) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,1856) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (key_p:int64,176) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64)`;;

(* the BRIDGE state @0x61c (settled seam) = deint LEG1 post.  Everything indexed at 4*loop_count. *)
let swps_bridge_post =
  mk_abs(`s:armstate`, list_mk_conj
    [`aligned_bytes_loaded s (word pc) swpS_mc`; `read PC s = word (pc + 0x61c)`;
     `read X0 s = word_add in_p (word (64 * loop_count))`;
     `read X2 s = word_add out_p (word (64 * loop_count))`;
     `read X3 s = tag_p`; `read X4 s = ivec_p`; `read X6 s = htable_p`; `read SP s = stackpointer`;
     `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
     `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2)`;
     `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
     `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
     `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
     `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
     `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
     `read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64`;
     `read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64`;
     `read Q7 s = word 13979173243358019584`;
     `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64`;
     `read X12 s = word_zx (word_zx (word_subword
         (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64`;
     `read X13 s = word_zx (word (4 * loop_count + 2):int32):int64`;
     `read X15 s = word(len_bits DIV 8)`; `read X1 s = word 0`; `read X16 s = word loop_remain`;
     `read Q30 s = byteswap128
          (nist_ghash (aes128_cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count)))`;
     `htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s`;
     `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`;
     `!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
              word_xor (aes_ctr_block nonce rk j) (inblock j)`]);;

(* REDUCELAST goal: precond swpS_inv8(loop_count-1) @0x4b0 -> swps_bridge_post @0x61c, broad frame. *)
let reducelast_goal =
  mk_imp(swps_leg_precond,
   list_mk_icomb "ensures" [`arm`;
     leg_state swpS_inv8 `0x4b0` `loop_count - 1` ;
     swps_bridge_post ;
     swps_broad_frame]);;

(* REDUCELAST setup: at 0x4b0 with inv(loop_count-1).  Set m = loop_count-1 so the state is inv(m)@0x4b0
   (X1 = word(loop_count-(m+1)) = word 0).  Input blocks needed: the LAST group 4m+0..3 (= 4*loop_count-4
   ..4*loop_count-1); no prefetch group (4m+4 = 4*loop_count is out of range for loop_remain=0, and the
   drain doesn't load it - it only completes the in-flight reduce + stores the last outputs).
   Guard: cbnz@0x4b0 with X1=word 0 -> val(word 0)=0 -> NOT taken -> falls to 0x4b4. *)
let reducelast_merges = [(8,176);(28,160)];;  (* the 2 counter stp sites in reduce_last: stp[sp,#176]@0x4cc=step8, stp[sp,#160]@0x51c=step28 (rel 0x4b0=step1) *)

let REDUCELAST_INPUT_SPLIT_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * (4*m+0))))) s0 = inblock (4*m+0) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*m+1))))) s0 = inblock (4*m+1) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*m+2))))) s0 = inblock (4*m+2) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*m+3))))) s0 = inblock (4*m+3)`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `4*m+3 < nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; `loop_count = m + 1`; `2 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*m+0) = 64*m`; ARITH_RULE `16 * (4*m+1) = 64*m+16`;
     ARITH_RULE `16 * (4*m+2) = 64*m+32`; ARITH_RULE `16 * (4*m+3) = 64*m+48`]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

(* val facts for the guard cbnz@0x4b0: X1 = word 0 (inv(loop_count-1) X1 conjunct simplifies via
   loop_count-((loop_count-1)+1)=0).  We introduce m=loop_count-1, rewrite the X1 read to word 0. *)
let reducelast_step_tac =
  STRIP_TAC THEN REWRITE_TAC[fst SWPS_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  ABBREV_TAC `m = loop_count - 1` THEN
  SUBGOAL_THEN `loop_count = m + 1` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  (* simplify the X1 read to word 0.  After ABBREV_TAC m=loop_count-1, the inv X1 conjunct
     `word(loop_count - ((loop_count-1)+1))` has its `loop_count-1` folded to m, becoming
     `word(loop_count - (m+1))`; with loop_count=m+1 that is word((m+1)-(m+1)) = word 0.  Rewrite the
     X1 read in place (match on `read X1 s0 = word(loop_count - (m+1))`, robust to the ABBREV fold). *)
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read X1 s0 = word (loop_count - (m + 1))`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ASSUME `loop_count = m + 1`;
                     ARITH_RULE `(m + 1) - (m + 1) = 0`] th)
    else NO_TAC) THEN
  REDUCELAST_INPUT_SPLIT_TAC THEN
  (* guard cbnz@0x4b0: step 1, X1=word 0 -> val 0 -> not taken *)
  ARM_STEPS_TAC SWPS_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_0; COND_CLAUSES]) THEN
  (* steps 2..91 (reduce_last 0x4b4..0x618) with per-step subword + MERGE.  gkeepN keeps the reduce set. *)
  (fun (asl,w) ->
     (MAP_EVERY (fun k ->
        gkeepN REDSETX SWPS_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k reducelast_merges then MERGE_CTR128_TAC (List.assoc k reducelast_merges) ("s"^string_of_int k)
         else ALL_TAC))
       (2--91)) (asl,w)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* REDUCELAST closer: the bridge post @0x61c.  Indexing: precond is inv(m) with m=loop_count-1, so the
   bridge (indexed at loop_count = m+1) appears as "(m+1)"-forms.  Q30 settles 4m -> 4m+4 = 4*(m+1) via
   deint's DRAIN reconstruction (swp_deint 1872-1969, the 4-block settled-acc tag-settle).  output-forall
   splits into OLD (j<4m, from inv) + the last group (4m+0..3).  Most other conjuncts are settled regs. *)
let reducelast_close_ghash : tactic =
  (* Q30: word_subword(word_join(drain tower))(64,128) = byteswap128(nist_ghash..(4*(m+1))).  The 4 last
     cipherblocks fold from the pipeline pins (aes7c/8c/10p + fresh v0), then deint's reduce reconstruction
     (settled sofar@4m + 4 blocks -> 4m+4).  Reuse close_goal7's body but with m-indexing (sofar@4m). *)
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "reducelast_close_ghash: no rk-hyp" in
    let ksf = MATCH_MP KEYSTREAM_FOLD rkth in
    let ghostpins = List.filter_map (fun (_,th) ->
      let c = concl th in
      if is_eq c then (match lhs c with
        | Var(nm,_) when String.length nm>=6 && String.sub nm 0 6="ghost_"
            && can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="inblock" with _->false)) (rhs c)
          -> Some th | _ -> None) else None) asl in
    (
    (* normalize the tag index 4*(m+1) -> 4*m+4 and fold the 4 last-group keystreams. *)
    REWRITE_TAC[ARITH_RULE `4*(m+1) = 4*m+4`] THEN
    REWRITE_TAC(JOIN_SUBWORD_RECOMBINE :: ghostpins) THEN
    REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C; GSYM aes10p] THEN
    REWRITE_TAC[JOIN_XOR_LANES] THEN
    REWRITE_TAC[ksf] THEN
    REWRITE_TAC[ARITH_RULE `4*m+5 = (4*m+3)+2`; ARITH_RULE `4*m+4 = (4*m+2)+2`;
                ARITH_RULE `4*m+3 = (4*m+1)+2`; ARITH_RULE `4*m+2 = (4*m+0)+2`] THEN
    REWRITE_TAC[CT_TO_NCB] THEN
    REWRITE_TAC[ARITH_RULE `(4*m+0)+2 = 4*m+2`; ARITH_RULE `(4*m+1)+2 = 4*m+3`;
                ARITH_RULE `(4*m+2)+2 = 4*m+4`; ARITH_RULE `(4*m+3)+2 = 4*m+5`;
                ARITH_RULE `4*m+0 = 4*m`] THEN
    (* deint reduce reconstruction (4*m variant). *)
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
    SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
      `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
       word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (4 * m)))`;
      `cipherblock_0 = nist_cipher_block nonce rk inblock (4 * m)`;
      `cipherblock_1 = nist_cipher_block nonce rk inblock (4 * m + 1)`;
      `cipherblock_2 = nist_cipher_block nonce rk inblock (4 * m + 2)`;
      `cipherblock_3 = nist_cipher_block nonce rk inblock (4 * m + 3)`;
      `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
      `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
      REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
      ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
       `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                   `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                   `sofar:int128`; `cipherblock_0:int128`]
                  GHASH_POLYVAL_ACC_BATCHED) THEN
    REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
     `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    EXPAND_TAC "sofar" THEN
    REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
    REWRITE_TAC[ARITH_RULE `4*m+4 = SUC(SUC(SUC(SUC(4*m))))`] THEN
    REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]
    ) (asl,w);;

(* output-forall for the bridge: j < 4*(m+1) splits into OLD (j<4m, from inv's output-forall) + the last
   group (4m+0..3).  Mirrors close_goal9 but at m/(m+1) indexing (deint DRAIN closer 1848-1865). *)
let reducelast_close_outputs : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "reducelast_close_outputs: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `4 * (m+1) = 4*m+4`] THEN
     REWRITE_TAC[ARITH_RULE `j < 4*m+4 <=>
                          j < 4 * m \/ j = 4*m+0 \/ j = 4*m+1 \/ j = 4*m+2 \/ j = 4*m+3`] THEN
     ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     REWRITE_TAC[ARITH_RULE `16 * (4*m+0) = 64*m`; ARITH_RULE `16 * (4*m+1) = 64*m+16`;
        ARITH_RULE `16 * (4*m+2) = 64*m+32`; ARITH_RULE `16 * (4*m+3) = 64*m+48`] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
     CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD rkth]) (asl,w);;

(* REDUCELAST per-conjunct dispatcher (m = loop_count-1 in context; bridge indexed at m+1). *)
let reducelast_close_all : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    if has_mc w then close_goal10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then MUST reducelast_close_outputs (asl,w)
    else if is_eq w && has "nist_ghash" (rhs w) then reducelast_close_ghash (asl,w)
    else
      (FIRST (map MUST
        [ (* X0/X2 ptr: word_add p (word(64*m+64)) = word_add p (word(64*(m+1))) *)
          (REWRITE_TAC[ARITH_RULE `64*(m+1)=64*m+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE);
          (* X13: word_zx(word(4*m+6)) = word_zx(word(4*(m+1)+2)) *)
          (REWRITE_TAC[ARITH_RULE `4*(m+1)+2 = 4*m+6`] THEN CONV_TAC WORD_RULE);
          (* X1: word 0 (already settled) *)
          REFL_TAC;
          CONV_TAC WORD_RULE;
          CONV_TAC WORD_BLAST ])) (asl,w);;

let REDUCELAST = leaf_prove "REDUCELAST" reducelast_goal
         (reducelast_step_tac THEN REPEAT CONJ_TAC THEN reducelast_close_all);;

(* ============================================================================
   SWPS_TAIL: BRIDGE @0x61c -> final spec @0x710.  The tail region 0x4b4..0x73c is BYTE-IDENTICAL to
   deint, so this is deint's DEINT_TAIL (swp_deint 747-1042) ported verbatim with aes_gcm_deint_mc->swpS_mc
   and AES_GCM_DEINT_EXEC->SWPS_EXEC.  Precond = swps_bridge_post's body (the 0x61c seam); post = the two
   memory facts (output blocks + settled tag + ivec writeback); broad frame.
   ============================================================================ *)
(* per-step subword normalizer that leaves (forall j) region invariants untouched (deint 729). *)
let SUBWORD_NONFORALL =
  RULE_ASSUM_TAC(fun th ->
    if is_forall (concl th) then th
    else CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th);;

(* the tail needs NO `2 <= loop_count` (it runs for any loop_count incl 0/1 - deint's DEINT_TAIL precond
   omits it).  FROM88's leg-2 reaches SWPS_TAIL for ALL loop_count, so SWPS_TAIL must not require it, else
   the 2<=loop_count precond subgoal can't be discharged from FROM88's (case-split) context. *)
let swps_tail_precond =
  list_mk_conj(filter (fun c -> c <> `2 <= loop_count`) (conjuncts swps_leg_precond));;
let swps_tail_goal =
  mk_imp(swps_tail_precond,
   list_mk_icomb "ensures" [`arm`;
     swps_bridge_post ;
     mk_abs(`s:armstate`, list_mk_conj
       [`read PC s = word (pc + 0x710)`;
        `!i. i < nblocks ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                 word_xor (aes_ctr_block nonce rk i) (inblock i)`;
        `read (memory :> bytes128 tag_p) s =
           word_reversefields 8
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) nblocks))`;
        `read (memory :> bytes128 ivec_p) s =
           word_reversefields 8 (ctr_block nonce (nblocks + 2))`]) ;
     swps_broad_frame]);;

let swps_tail_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  (*** loop_remain = 0: no tail iterations, just the finalize (ivec/tag writeback) ***)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `n MOD 4 = 0 ==> 4 * n DIV 4 = n`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  (*** loop_remain >= 1: tail loop via ENSURES_WHILE (0x62c head, 0x6f8 back-edge) ***)
  ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0x62c` `pc + 0x6f8`
    `\i s.
      read X0  s = word_add in_p  (word (64 * loop_count + 16 * i)) /\
      read X2  s = word_add out_p (word (64 * loop_count + 16 * i)) /\
      read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
      read SP s = stackpointer /\
      read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
      read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
      read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
      read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
      read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
      read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
      read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
      read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
      read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
      read Q7 s = word 13979173243358019584 /\
      read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
      read X12 s = word_zx (word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
      read X13 s = word_zx (word (4 * loop_count + i + 2):int32):int64 /\
      read X15 s = word(len_bits DIV 8) /\ read X16 s = word(loop_remain - i) /\
      read Q30 s = byteswap128
          (nist_ghash (aes128_cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count + i))) /\
      htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
      read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
      read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
      (!j. j < 4 * loop_count + i
           ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
               word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
   [(*** base case: bridge 0x61c -> 0x62c, i=0 ***)
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--3) THEN
    ARM_STEPS_TAC SWPS_EXEC [4] THEN
    SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "loop_remain" THEN
      W(fun _ -> MP_TAC(SPECL [`nblocks:num`;`4`] MOD_LT_EQ)) THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),Var("s4",_))),
             Comb(Comb(Comb(Const("COND",_),_),_),_)) ->
          ASSUME_TAC(REWRITE_RULE[ASSUME `val(word loop_remain:int64) = loop_remain`;
                                  ASSUME `~(loop_remain = 0)`; COND_CLAUSES] th)
      | _ -> NO_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0];

    (*** loop body: 0x62c -> 0x6f8, one block; Inv(i) -> Inv(i+1) ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16 * i)))) s0 =
      inblock (4 * loop_count + i)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
      check (fun th -> let c = concl th in
        is_eq c && free_in `in_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))) THEN
    SUBGOAL_THEN `4 * loop_count + i < nblocks` ASSUME_TAC THENL
     [MAP_EVERY (fun t -> UNDISCH_TAC t)
        [`i < loop_remain`; `nblocks MOD 4 = loop_remain`; `nblocks DIV 4 = loop_count`] THEN
      ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN SUBWORD_NONFORALL) (1--5) THEN
    MERGE_CTR128_TAC 160 "s5" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN SUBWORD_NONFORALL) (6--28) THEN
    MERGE_CTR128_TAC 160 "s28" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN SUBWORD_NONFORALL) (29--51) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `j < a + i + 1 <=> j < a + i \/ j = a + i`] THEN
    ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
    REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0; ADD_0] THEN
    REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
    REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
    REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
    ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
    DISCARD_STATE_TAC "s51" THEN
    REWRITE_TAC[ADD_ASSOC; ARITH] THEN
    REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
    REWRITE_TAC[GSYM cipher_block] THEN
    REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
    SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    FIRST_ASSUM(fun th -> if can (term_match []
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
      then REWRITE_TAC[th] else NO_TAC) THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
    `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
     word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count + i)))`;
      `cipherblock = nist_cipher_block nonce rk inblock (4 * loop_count + i)`;
      `h = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `k = karatsuba_mid h`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
      `polyval_reduce_prop3 (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      ASM_REWRITE_TAC[] THEN LET_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
      ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM polyval_dot] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[h_power] THEN
    REWRITE_TAC[GSYM NIST_DOT_IS_POLYVAL_DOT] THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) = SUC k`] THEN
    REWRITE_TAC[list_of_seq; NIST_GHASH_APPEND; NIST_GHASH_CONS; nist_ghash] THEN
    ASM_REWRITE_TAC[];

    (*** trivial loop-back: 0x6f8 test taken ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC SWPS_EXEC [1] THEN
    SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "loop_remain" THEN
      W(fun _ -> MP_TAC(SPECL [`nblocks:num`;`4`] MOD_LT_EQ)) THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_ARITH_TAC;

    (*** finalize: 0x6f8 test not taken -> ivec/tag writeback -> 0x710 ***)
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD; CTR_ZX_NORM] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST];;

let SWPS_TAIL = leaf_prove "SWPS_TAIL" swps_tail_goal swps_tail_tac;;

(* ============================================================================
   Frame-widening: BODYLEG/FILLLEG are proven with the NARROW frame (no tag_p/ivec_p).  The WHILE + tail
   need the shared BROAD frame.  ENSURES_FRAME_SUBSUMED widens: narrow subsumed broad /\ ensures P Q narrow
   ==> ensures P Q broad.  narrow subsumed broad discharges by SUBSUMED_MAYCHANGE_TAC (broad = narrow + more).
   ============================================================================ *)
(* widen the frame of an `[hyps] |- ensures arm P Q narrow` thm to the broad frame. *)
let widen_frame_to_broad th =
  let narrow = rand(concl th) in
  let subth = prove(list_mk_icomb "subsumed" [narrow; swps_broad_frame],
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
  MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subth th);;

(* BODYLEG_BROAD / FILLLEG_BROAD : the same legs, broad frame, precond re-DISCHed, then RE-GENERALIZED
   over the leg's original universally-quantified vars (so downstream `SPEC `loop_count-2`` / MATCH_MP_TAC
   work).  Robust to BOTH a real prove() result (concl = `!vars. pre ==> ensures`) and the SKIP mk_thm
   placeholder (concl = `pre ==> ensures`, vars free): SPEC_ALL strips any leading foralls, we widen the
   bare `pre ==> ensures`, then GENL re-closes over exactly those vars. *)
let widen_leg leg =
  let vars,body = strip_forall (concl leg) in
  let leg0 = SPEC_ALL leg in                    (* leg0 : pre ==> ensures ... (vars now free) *)
  let pre = lhand(concl leg0) in
  let broad = DISCH pre (widen_frame_to_broad (UNDISCH leg0)) in
  (* re-generalize: prefer the leg's own forall vars; if none (mk_thm placeholder), close over free vars. *)
  GENL (if vars = [] then frees(concl broad) else vars) broad;;
let BODYLEG_BROAD = widen_leg BODYLEG;;
let FILLLEG_BROAD = widen_leg FILLLEG;;

(* ============================================================================
   SWPS_DRAIN: the g5/lc2 DRAIN = inv(loop_count-2) @0x1ec -> bridge @0x61c, broad frame.  Composes
   BODYLEG_BROAD@(loop_count-2) (0x1ec->0x4b0, lands inv(loop_count-1)) ;; REDUCELAST (0x4b0->0x61c) via
   ENSURES_SEQUENCE@0x4b0.  A SINGLE combined leg (deint's DRAIN_LEG_LC2_GEN analog) so both the WHILE g5
   AND the loop_count=2 degenerate case dispatch to it uniformly (index loop_count-2), with no fragile
   goal-index rewrites.  BODYLEG_BROAD's post-index (loop_count-2)+1 is rewritten to loop_count-1 IN THE
   THEOREM (from 2<=loop_count arith), never in the goal. ============================================ *)
let swps_drain_goal =
  mk_imp(swps_leg_precond,
    list_mk_icomb "ensures" [`arm`;
      leg_state swpS_inv8 `0x1ec` `loop_count - 2` ;
      swps_bridge_post ;
      swps_broad_frame]);;

let SWPS_DRAIN =
    let th = GEN_ALL(prove(swps_drain_goal,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     SUBGOAL_THEN `(loop_count - 2) + 1 = loop_count - 1` ASSUME_TAC THENL
      [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     ENSURES_SEQUENCE_TAC `pc + 0x4b0`
       (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swpS_inv8,`loop_count - 1`))))) THEN
     CONJ_TAC THENL
      [(* BODYLEG_BROAD @ i:=loop_count-2.  Rewrite the waypoint post inv(loop_count-1) -> inv((loop_count-2)+1)
          [via GSYM of the SUBGOAL] so MATCH_MP_TAC BODYLEG_BROAD unifies i:=loop_count-2 directly (same robust
          pattern as the WHILE g3 half; the earlier INST[loop_count-2/i] form no-matched because GEN_ALL may
          rename the bound var away from `i`).  Then discharge BODYLEG's precond (loop_count-2<loop_count-1). *)
       FIRST_X_ASSUM(fun th -> if concl th = `(loop_count - 2) + 1 = loop_count - 1`
         then REWRITE_TAC[SYM th] else NO_TAC) THEN
       REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC BODYLEG_BROAD THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
       (* REDUCELAST: inv(loop_count-1)@0x4b0 -> bridge@0x61c.  Its precond forall-binds key_p (only in
          nonoverlapping hyps), so MATCH_MP_TAC leaves ?key_p; supply the actual key_p. *)
       REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC REDUCELAST THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]])) in
    th;;

(* ============================================================================
   SWPS_LEG1: the main body 0x88 -> 0x61c (FILL + software-pipelined WHILE + DRAIN).  Mirrors deint's
   LEG1_LC2 (swp_deint 1972-2215), but with swp_S's DISTINCT-pc physical loop realized as a SEAM-TO-SEAM
   WHILE at 0x1ec (g3 body = 0x1ec->0x4b0 [BODYLEG_BROAD] ;; 0x4b0->0x1ec [backedge cbnz taken]; g4 trivial;
   g5 = DRAIN = BODYLEG_BROAD@(loop_count-2) ;; REDUCELAST).  Precond = swp_S 0x88 preamble-end; post = bridge.
   ============================================================================ *)
(* the 0x88 preamble-end precondition (= FILL's precond body, restated for the sequence). *)
let swps_pre88 = mk_abs(`s:armstate`, list_mk_conj
   [`aligned_bytes_loaded s (word pc) swpS_mc`; `read PC s = word (pc + 0x88)`;
    `read X0 s = in_p`; `read X2 s = out_p`; `read X3 s = tag_p`; `read X4 s = ivec_p`;
    `read X6 s = htable_p`; `read SP s = stackpointer`;
    `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
    `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2)`;
    `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
    `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
    `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
    `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
    `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
    `read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64`;
    `read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64`;
    `read Q7 s = word 13979173243358019584`;
    `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64`;
    `read X12 s = word_zx (word_zx (word_subword
        (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64`;
    `read X13 s = word_zx (word 2:int32):int64`; `read X15 s = word(len_bits DIV 8)`;
    `read X1 s = word loop_count`; `read X7 s = word nblocks`; `read X16 s = word loop_remain`;
    `read Q30 s = byteswap128 tag0`;
    `htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s`;
    `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`]);;

let swps_leg1_goal =
  mk_imp(swps_leg_precond,
    list_mk_icomb "ensures" [`arm`; swps_pre88; swps_bridge_post; swps_broad_frame]);;

(* the WHILE body-invariant (swpS_inv8 with the aligned_bytes_loaded folded in) used by ENSURES_WHILE_UP_TAC.
   The rule wants a num->armstate->bool; swpS_inv8 already is that (modulo the aligned/PC which the rule adds). *)
let swps_while_inv = swpS_inv8;;

(* helper: the inv-body at a given index, as an armstate->bool predicate (for ENSURES_SEQUENCE intermediate). *)
let inv_at k = mk_abs(`s:armstate`, mk_conj(
  mk_eq(`read PC s`, mk_comb(`word:num->int64`, mk_binop `+` `pc:num` k)),
  list_mk_comb(swpS_inv8,[k;`s:armstate`])));;

(* no-op tactic marking the WHILE-glue legs (FILL/g1..g5/DRAIN); a readable structural label. *)
let LOG (_:string) : tactic = ALL_TAC;;

let swps_leg1_tac =
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     (* expand the ABI macro into ASSIGNS so ENSURES_SEQUENCE/WHILE's C,,C=C idempotence
        (MAYCHANGE_IDEMPOT_TAC -> ASSIGNS_SEQ_ABSORB_CONV) can decompose the frame.  Each MATCH_MP_TAC
        of a leg (whose frame keeps ABI FOLDED) is preceded by GSYM to re-fold. *)
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     (* FILL: 0x88 -> 0x1ec, inv 0 *)
     ENSURES_SEQUENCE_TAC `pc + 0x1ec`
       (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swpS_inv8,`0`))))) THEN
     CONJ_TAC THENL
      [(* FILL leg discharges this; re-fold ABI so FILLLEG_BROAD's frame matches. *)
       LOG "FILL" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC FILLLEG_BROAD THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     (* now: inv 0 @0x1ec -> bridge @0x61c, broad frame. Case-split loop_count = 2. *)
     ASM_CASES_TAC `loop_count = 2` THENL
      [(* loop_count=2: WHILE runs 0 iters; DRAIN directly.  Pre = inv 0 (from FILL) but SWPS_DRAIN wants
          inv(loop_count-2); ENSURES_PRECONDITION_TAC changes the pre to inv(loop_count-2)@0x1ec, proving
          the FILL-post => it via the loop_count=2 rewrite (2-2=0, scoped to the whole predicate - safe).
          Then MATCH_MP_TAC SWPS_DRAIN.  Mirrors deint LEG1_LC2 lc=2 (swp_deint 1984-2001). *)
       LOG "lc2" THEN
       (fun (asl,w) ->
         (* dpre = aligned /\ PC=0x1ec /\ <inv(loop_count-2) body>, built with the SAME single-BETA_CONV
            +ADD_CLAUSES normalization as deint's dpre, so the impl-goal `!s. dpre s ==> FILL-post s`
            (FILL-post = inv 0, same normalization) closes via loop_count->2, 2-2->0, REWRITE[] (X==>X).
            Mirrors deint LEG1_LC2 lc=2 (swp_deint 1984-2001) EXACTLY. *)
         let sv = `s:armstate` in
         let invbody = rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                         (mk_comb(swpS_inv8,`loop_count - 2`)))) in
         let invbody_s = rhs(concl(BETA_CONV(mk_comb(invbody,sv)))) in
         let dpre = mk_abs(sv, list_mk_conj(
           [`aligned_bytes_loaded s (word pc) swpS_mc`;
            `read PC s = word (pc + 0x1ec)`] @ conjuncts invbody_s)) in
         (ENSURES_PRECONDITION_TAC dpre THEN
          CONJ_TAC THENL
           [(* impl goal: !x. A x ==> B x, where A (inv 0) and B (inv(loop_count-2)) become IDENTICAL
               under loop_count=2.  GEN_TAC, normalize the whole `A==>B` (loop_count->2 + 2-2->0 +
               NUM_REDUCE, both sides -> the same C), leaving C==>C; DISCH_THEN ACCEPT_TAC closes it. *)
            GEN_TAC THEN
            CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
            ASM_REWRITE_TAC[ARITH_RULE `2 - 2 = 0`; ADD_CLAUSES] THEN
            CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN ACCEPT_TAC;
            REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
            MATCH_MP_TAC SWPS_DRAIN THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]]) (asl,w));
       ALL_TAC] THEN
     (* loop_count >= 3: FILL(done) + seam-to-seam WHILE(loop_count-2) at 0x1ec + DRAIN. *)
     LOG "before-WHILE" THEN
     ENSURES_WHILE_UP_TAC `loop_count - 2` `pc + 0x1ec` `pc + 0x1ec` swps_while_inv THEN
     REPEAT CONJ_TAC THENL
      [(* g1 ~(loop_count-2 = 0) *)
       LOG "g1" THEN UNDISCH_TAC `~(loop_count = 2)` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
       (* g2 base: inv 0 @0x1ec -> inv 0 @0x1ec (identity).  Leftover after ASM_REWRITE:
          word(loop_count-1) = word(loop_count-(0+1)) [the X1 pin]; fold 0+1=1 (ADD_CLAUSES). *)
       LOG "g2" THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
       REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];
       (* g3 body: inv i @0x1ec -> inv(i+1) @0x1ec, via 0x4b0 (BODYLEG_BROAD ;; backedge) *)
       LOG "g3" THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
       ENSURES_SEQUENCE_TAC `pc + 0x4b0`
         (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swpS_inv8,`i+1`))))) THEN
       CONJ_TAC THENL
        [(* g3 first half: goal post is inv(i+1)@0x4b0 = BODYLEG_BROAD's post exactly; MATCH_MP_TAC
            unifies i:=i, leaves BODYLEG_BROAD's precond as subgoal (discharge from the g3 hyps). *)
         LOG "g3-BODY" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
         MATCH_MP_TAC BODYLEG_BROAD THEN ASM_REWRITE_TAC[] THEN
         MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < loop_count - 2`; `2 <= loop_count`] THEN ARITH_TAC;
         (* backedge cbnz@0x4b0 taken (X1=word(loop_count-(i+2))!=0 for i<loop_count-2) -> 0x1ec.
            Expand htable_mem_4 in BOTH the asm (s0) and goal so the 6 htable reads carry through the
            1-instr step (cbnz doesn't touch htable memory) and ASM_REWRITE closes them at s1. *)
         ENSURES_INIT_TAC "s0" THEN
         RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
         SUBGOAL_THEN `val(word (loop_count - (i + 2)):int64) = loop_count - (i + 2) /\ ~(loop_count - (i+2) = 0)`
         STRIP_ASSUME_TAC THENL
          [CONJ_TAC THENL
            [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
             MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
             MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < loop_count - 2`] THEN ARITH_TAC]; ALL_TAC] THEN
         (* the inv(i+1) X1 conjunct is word(loop_count-((i+1)+1)) = word(loop_count-(i+2)) *)
         RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(i+1)+1 = i+2`]) THEN
         ARM_STEPS_TAC SWPS_EXEC [1] THEN
         RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word (loop_count - (i + 2)):int64) = loop_count - (i + 2)`;
                                     ASSUME `~(loop_count - (i+2) = 0)`; COND_CLAUSES]) THEN
         ENSURES_FINAL_STATE_TAC THEN
         (* leftover: word(loop_count-(i+2)) = word(loop_count-((i+1)+1)) [X1 pin] + the 6 htable reads
            (goal's htable_mem_4 was pre-expanded).  Fold (i+1)+1=i+2, then ASM_REWRITE closes the X1 eq
            and the 6 htable reads (carried to s1 from the expanded s0 asms). *)
         REWRITE_TAC[ARITH_RULE `(i+1)+1 = i+2`] THEN ASM_REWRITE_TAC[]];
       (* g4 back-edge trivial (pc1=pc2=0x1ec identity) *)
       LOG "g4" THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
       REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];
       (* g5 DRAIN: inv(loop_count-2) @0x1ec -> bridge @0x61c.  This IS SWPS_DRAIN's goal (modulo the
          key_p existential MATCH_MP_TAC leaves - supply key_p). *)
       LOG "g5" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC SWPS_DRAIN THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]];;

(* GEN_ALL so FROM88's MATCH_MP_TAC SWPS_LEG1 THEN EXISTS_TAC key_p works (prove of a mk_imp does NOT
   auto-generalize; key_p would stay free and no ?key_p would be left). *)
let SWPS_LEG1 = GEN_ALL(prove(swps_leg1_goal, swps_leg1_tac));;

(* ============================================================================
   SWPS_LEG1_LC1: loop_count=1 degenerate leg (0x88 -> 0x61c): A_0 ; reduce_last (B_0 as drain).
   VERBATIM port of deint's LEG1_LC1 (swp_deint 1054-1324) with aes_gcm_deint_mc->swpS_mc,
   AES_GCM_DEINT_EXEC->SWPS_EXEC.  swp_S's 0x88..0x1e4 (A_0) and 0x4b4..0x618 (reduce_last) are
   byte-identical to deint, so the stepping recipe transfers exactly. ============================ *)
let SWPS_LEG1_LC1 = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       loop_count = 1 /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) swpS_mc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
           read Q18 s = word_reversefields 8 (EL 0 rk) /\
           read Q19 s = word_reversefields 8 (EL 1 rk) /\
           read Q20 s = word_reversefields 8 (EL 2 rk) /\
           read Q21 s = word_reversefields 8 (EL 3 rk) /\
           read Q22 s = word_reversefields 8 (EL 4 rk) /\
           read Q23 s = word_reversefields 8 (EL 5 rk) /\
           read Q24 s = word_reversefields 8 (EL 6 rk) /\
           read Q25 s = word_reversefields 8 (EL 7 rk) /\
           read Q26 s = word_reversefields 8 (EL 8 rk) /\
           read Q27 s = word_reversefields 8 (EL 9 rk) /\
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word 2:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. aligned_bytes_loaded s (word pc) swpS_mc /\
           read PC s = word (pc + 0x61c) /\
           read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[htable_mem_4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ENSURES_INIT_TAC "s0" THEN
  (*** derive the 4 group-0 input blocks from the nblocks-forall (nblocks >= 4) ***)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `4 <= nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`;
    ARITH_RULE `16 * 2 = 32`; ARITH_RULE `16 * 3 = 48`; WORD_ADD_0]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
    check (fun th -> let c = concl th in
      is_eq c && can (find_term (fun t -> t = `(memory :> bytes128 in_p)`)) (lhs c))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
    check (fun th -> let c = concl th in
      is_eq c && free_in `in_p:int64` (lhs c) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--11) THEN
  MERGE_CTR128_TAC 192 "s11" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (12--12) THEN
  MERGE_CTR128_TAC 176 "s12" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (13--19) THEN
  MERGE_CTR128_TAC 160 "s19" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (20--24) THEN
  MERGE_CTR128_TAC 208 "s24" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (25--31) THEN
  MERGE_CTR128_TAC 192 "s31" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (32--37) THEN
  MERGE_CTR128_TAC 208 "s37" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (38--96) THEN
  MERGE_CTR128_TAC 176 "s96" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (97--116) THEN
  MERGE_CTR128_TAC 160 "s116" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC SWPS_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (117--179) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `loop_count = 1` SUBST_ALL_TAC THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * i + 2) + n = 4 * i + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[(prove(`word 144115188075855872:int64 = word_shl (word_zx (word_bytereverse (word 2:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 216172782113783808:int64 = word_shl (word_zx (word_bytereverse (word 3:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 288230376151711744:int64 = word_shl (word_zx (word_bytereverse (word 4:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 360287970189639680:int64 = word_shl (word_zx (word_bytereverse (word 5:int32)):int64) 32`, CONV_TAC WORD_BLAST))] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  DISCARD_STATE_TAC "s179" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (*** loop_count=1 => the 4 blocks have LITERAL counters 2,3,4,5, so the symbolic     ***)
  (*** AES_CTR_BLOCK_RECONSTRUCT (pattern i+2) cannot fire; use its i=0 specialization. ***)
  REWRITE_TAC[CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
               (INST [`0`,`i:num`] AES_CTR_BLOCK_RECONSTRUCT)] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST; ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64)
             (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64)
                  (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64)
                  (word_subword y (64,64):int64):int128`) THEN
  (*** loop_count=1 => the GHASH accumulator is still tag0 (nist_ghash h tag0 [] = tag0), ***)
  (*** so there is no `sofar` to abbreviate: block 0 is word_xor tag0 cipherblock_0.       ***)
  MAP_EVERY ABBREV_TAC
   [`cipherblock_0 = nist_cipher_block nonce rk inblock 0`;
    `cipherblock_1 = nist_cipher_block nonce rk inblock 1`;
    `cipherblock_2 = nist_cipher_block nonce rk inblock 2`;
    `cipherblock_3 = nist_cipher_block nonce rk inblock 3`;
    `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
    `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
    `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
    `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
        (word_xor
        (word_pmul (cipherblock_3:int128) (h0:int128))
        (word_xor
        (word_pmul (cipherblock_2:int128) (h1:int128))
        (word_xor
        (word_pmul (cipherblock_1:int128) (h2:int128))
        (word_pmul (word_xor (tag0:int128) cipherblock_0)
                   (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
     `word_pmul (word_xor a b) (word_xor c d) =
      word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                 `tag0:int128`; `cipherblock_0:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]);;


(* ============================================================================
   SWPS_FROM88: main body 0x88 -> 0x710.  Port of deint DEINT_FROM88 (leg1 case-split
   loop_count 0/1/>=2 -> SWPS_LEG1_LC1/SWPS_LEG1 ; leg2 SWPS_TAIL). ============================ *)
let swps_from88_stmt =
  `!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) swpS_mc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
           read Q18 s = word_reversefields 8 (EL 0 rk) /\
           read Q19 s = word_reversefields 8 (EL 1 rk) /\
           read Q20 s = word_reversefields 8 (EL 2 rk) /\
           read Q21 s = word_reversefields 8 (EL 3 rk) /\
           read Q22 s = word_reversefields 8 (EL 4 rk) /\
           read Q23 s = word_reversefields 8 (EL 5 rk) /\
           read Q24 s = word_reversefields 8 (EL 6 rk) /\
           read Q25 s = word_reversefields 8 (EL 7 rk) /\
           read Q26 s = word_reversefields 8 (EL 8 rk) /\
           read Q27 s = word_reversefields 8 (EL 9 rk) /\
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word 2:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. read PC s = word (pc + 0x710) /\
           (!i. i < nblocks
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) nblocks)) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nblocks + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`;;
let swps_from88_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  (*** Sequence at the tail-entry pc+0x61c: leg 1 = fill+loop+drain (main body, produces the
   *** first 4*loop_count blocks + settles tag=ghash(4*loop_count)); leg 2 = the single-block
   *** tail, discharged by SWPS_TAIL.  The waypoint predicate is EXACTLY SWPS_TAIL's
   *** precondition (the bridge state). ***)
  ENSURES_SEQUENCE_TAC `pc + 0x61c`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(*** leg 1: fill + main loop + drain (pc+0x88 -> pc+0x61c).  Case-split on the group
     *** count BEFORE stepping so each case stays a clean `ensures` (dispatchable by lemma). ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [(*** loop_count = 0: cbz@0x88 taken -> 0x61c, nothing produced (tag still ghash([])=tag0).
       *** Substitute loop_count=0 BEFORE INIT (post-INIT, FIRST_X_ASSUM would grab a read-eq). ***)
      UNDISCH_THEN `loop_count = 0` SUBST_ALL_TAC THEN
      ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      ARM_STEPS_TAC SWPS_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[htable_mem_4; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                      list_of_seq; nist_ghash] THEN
      REWRITE_TAC[CONJUNCT1 LT];
      (*** loop_count >= 1: run A_0 (the group-0 producer, 0x8c..0x1e0), then the
       *** sub x1,#1 ; cbz x1,0x4b4.  If loop_count = 1 the cbz is taken -> reduce_last
       *** (B_0 as the drain), producing the bridge directly (SWPS_LEG1_LC1).  If loop_count >= 2
       *** the cbz falls through to B_0 -> the seam 0x354, then the pipelined main loop and
       *** the reduce_last drain. ***)
      ASM_CASES_TAC `loop_count = 1` THENL
       [(*** loop_count = 1: A_0 ; reduce_last -> bridge (one group, no loop): SWPS_LEG1_LC1.
         *** key_p appears only in SWPS_LEG1_LC1's hyps, so MATCH_MP_TAC leaves it existential
         *** (supply it); ASM_REWRITE then discharges every hyp incl. loop_count=1. ***)
        LOG "F88-LC1" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        MATCH_MP_TAC SWPS_LEG1_LC1 THEN
        EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[];
        (*** loop_count >= 2: A_0 ; B_0 -> seam 0x354 ; main loop ; drain -> bridge.
         *** SWPS_LEG1 is exactly this leg (0x88 -> 0x61c); its precond/post/frame match this
         *** goal, so MATCH_MP_TAC applies after re-folding the ABI frame; supply key_p, then
         *** ASM_REWRITE discharges every hyp except `2 <= loop_count`, from ~(lc=0)/\~(lc=1). ***)
        LOG "F88-LC2" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        MATCH_MP_TAC SWPS_LEG1 THEN
        EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[] THEN
        (* residual 2 <= loop_count (from ~(lc=0) /\ ~(lc=1)); ASM_ARITH_TAC uses all assms robustly. *)
        ASM_ARITH_TAC]];
    (*** leg 2: single-block tail (pc+0x61c -> pc+0x710) via SWPS_TAIL.  SWPS_TAIL's key_p
     *** appears only in its hyps (not its conclusion), so MATCH_MP_TAC leaves an existential
     *** over key_p; supply the actual key_p, then ASM_REWRITE discharges every hyp (incl. the
     *** rk-list fold and 16*nblocks<2^64, both carried as SWPS_FROM88 assumptions). ***)
    LOG "F88-TAIL" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC SWPS_TAIL THEN
    EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]];;
let SWPS_FROM88 = prove(swps_from88_stmt, swps_from88_tac);;

(* ============================================================================
   AES_GCM_..._SWP_S_CORRECT: the full-function correctness 0x2c -> 0x710 (preamble + SWPS_FROM88).
   Port of deint CORRECT wrapper. ============================ *)
let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH swpS_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) swpS_mc /\
           read PC s = word (pc + 0x2c) /\
           read SP s = stackpointer /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           wordlist_from_memory(key_p,11) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = word (pc + 0x710) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24;
                  X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  (*** setup boilerplate ***)
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst SWPS_EXEC] THEN
  ABBREV_TAC `nblocks = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  (*** round-key list length split ***)
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 11` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    EXPAND_TAC "rk" THEN REWRITE_TAC[MAP; CONS_11; GSYM CONJ_ASSOC] THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP]] THEN
  (*** sequence at the preamble-end pc+0x88; leg 1 = preamble, leg 2 = SWPS_FROM88 ***)
  ENSURES_SEQUENCE_TAC `pc + 0x88`
   `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
        read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word 2:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
        read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
        read Q30 s = byteswap128 tag0 /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i)` THEN
  CONJ_TAC THENL
   [(*** leg 1: preamble pc+0x2c -> pc+0x88 ***)
    REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce 2)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    DISCH_TAC THEN
    ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
    ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `key_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c) &&
        can (find_term (fun t -> t = `160`)) (lhs c))) THEN
    ARM_STEPS_TAC SWPS_EXEC (1--23) THEN ENSURES_FINAL_STATE_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
      then ASSUME_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X11_SETUP th) else NO_TAC);
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X12_SETUP th) else NO_TAC);
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X13_SETUP th) else NO_TAC);
      ASM_REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN EXPAND_TAC "nblocks" THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
      REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    (*** leg 2: main body pc+0x88 -> pc+0x710, via SWPS_FROM88.  htable_mem_4 stays FOLDED
         here (only leg 1 expanded it); refold the ABI frame so the sequenced goal is a
         direct instance of SWPS_FROM88.  key_p appears only in the hyps, so MATCH_MP_TAC
         leaves an existential we satisfy with the actual key_p. ***)
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC SWPS_FROM88 THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[] THEN
    (*** SWPS_FROM88's wrap-freedom hyp 16*nblocks<2^64: nblocks = len_bits DIV 128 and     ***)
    (*** W64_GEN_TAC gives len_bits < 2^64, so 16*nblocks <= len_bits/8 < 2^64.              ***)
    EXPAND_TAC "nblocks" THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC]);;
