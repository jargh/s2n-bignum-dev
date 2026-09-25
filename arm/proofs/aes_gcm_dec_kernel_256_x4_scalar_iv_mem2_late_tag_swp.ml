(* ========================================================================== *)
(* AES-256-GCM decrypt kernel, SWP (software-pipelined) speed champion:       *)
(*   aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp                     *)
(*                                                                            *)
(* Direct mid-pipeline loop-invariant proof (s2n-bignum house style): the     *)
(* software-pipelined 4-block main loop is verified via a single mid-pipeline *)
(* invariant swpS256_inv_dec, decomposed into four axiom-free leg theorems     *)
(* (each a Hoare triple over the kernel's machine code):                      *)
(*                                                                            *)
(*   SWP_DEC256_FILL     precond @0x2c   -> swpS256_inv_dec 0     @0x26c       *)
(*   SWP_DEC256_BODYLEG  swpS256_inv_dec i @0x26c -> inv(i+1)     @0x570       *)
(*   SWP_DEC256_DRAIN    inv(loop_count-1) @0x570 -> drain_bridge @0x6c0       *)
(*   SWP_DEC256_TAIL     drain_bridge @0x6c0 -> tail_post         @0x7c4       *)
(*                                                                            *)
(* GHASH is computed over the INPUT (ciphertext) blocks (nist_input_block);    *)
(* the accumulator Q30 is carried in the half-swapped SPLIT form.             *)
(*                                                                            *)
(* The whole-function composition assembles those legs into the complete      *)
(* specification.  The steady-state main loop is composed by ENSURES_WHILE     *)
(* over loop_count-1 iterations (SWPS_LEG1B, using the loosened body leg       *)
(* SWP_DEC256_BODYLEG_L1); the three degenerate cases loop_count in {0,1,>=2}  *)
(* are handled by SWPS_LC0, SWPS_LC1 and SWPS_LEG1B respectively, unified by    *)
(* SWPS_FROM88.  The result is lifted to the C-level specification:            *)
(*                                                                            *)
(*   SWP256_CORRECT                        core @pc+0x2c -> @pc+0x7c4          *)
(*   AES_GCM_DEC_KERNEL_256_X4_SCALAR_IV_MEM2_LATE_TAG_SWP_SUBROUTINE_CORRECT   *)
(*                                          full subroutine (prologue+epilogue) *)
(*                                                                            *)
(* Everything is proved axiom-free (final check_axioms = 3 base axioms only).  *)
(* ========================================================================== *)

(* ===== inlined machinery (was _scratch/dec256_{frontmatter,steppers,invariant,closers,shared_closers}.ml) ===== *)
needs "arm/proofs/base.ml";;
needs "common/fips197.ml";;
needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;

let aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc =
  define_from_elf "aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc"
    "arm/aes_gcm/aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp.o";;
let DEC256_EXEC = ARM_MK_EXEC_RULE aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc;;

let ctr_block = new_definition
  `ctr_block nonce ctr :int128 = word_join (nonce:96 word) (word ctr:int32)`;;
let aes_ctr_block = new_definition
  `aes_ctr_block nonce rk i = word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 2)) rk)`;;
let cipher_block = new_definition
  `cipher_block nonce rk inblock i = word_xor (aes_ctr_block nonce rk i) (inblock i)`;;
let nist_cipher_block = new_definition
  `nist_cipher_block nonce rk inblock i = word_reversefields 8 (cipher_block nonce rk inblock i)`;;
let nist_input_block = new_definition
  `nist_input_block (inblock:num->int128) (i:num) : int128 = word_reversefields 8 (inblock i)`;;
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

(* enc-256 substrate 84-707 *)

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
 (`word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 2)) rk) =
   aes_ctr_block nonce rk i /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 3)) rk) =
   aes_ctr_block nonce rk (i + 1) /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 4)) rk) =
   aes_ctr_block nonce rk (i + 2) /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 5)) rk) =
   aes_ctr_block nonce rk (i + 3)`,
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CIPHER_BLOCK_NIST = prove
 (`cipher_block nonce rk inblock i =
        word_reversefields 8 (nist_cipher_block nonce rk inblock i)`,
  REWRITE_TAC[nist_cipher_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

(*** Direct implementation of AES256 using the hardware primitives ***)
(*** 14 rounds: aese for rk0..rk13 (13 aesmc/aese pairs after the initial   ***)
(*** aese plaintext rk0), then the final round key rk14 XORed in.           ***)

let AES256_CIPHER_RECONSTRUCT = prove
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
       rk9))
      rk10))
     rk11))
    rk12))
   rk13)
   rk14 =
   word_reversefields 8
    (aes256_cipher (word_reversefields 8 plaintext)
        (MAP (word_reversefields 8)
             [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10;
              rk11; rk12; rk13; rk14]))`,
  REWRITE_TAC[aes256_cipher; LET_DEF; LET_END_DEF; MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[aesmc; aese; fips197_final_round; fips197_round] THEN
  REWRITE_TAC[AES_SUB_BYTES_SHIFT_ROWS] THEN
  REWRITE_TAC[FIPS197_EQ_SHIFT_ROWS; FIPS197_EQ_MIX_COLUMNS; fips197_sub_bytes;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GSYM WORD_XOR_REVERSEFIELDS; WORD_REVERSEFIELDS_REVERSEFIELDS;
              GSYM AES_SUB_BYTES_REVERSEFIELDS]);;

(*** This is the sequence in the code, folding an XOR in sooner ***)

let XOR_AES256_CIPHER_RECONSTRUCT = prove
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
        rk9))
       rk10))
      rk11))
     rk12))
    rk13)
   (word_xor rk14 inblock) =
   word_xor
    (word_reversefields 8
      (aes256_cipher (word_reversefields 8 plaintext)
         (MAP (word_reversefields 8)
              [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10;
               rk11; rk12; rk13; rk14])))
    inblock`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REWRITE_TAC[AES256_CIPHER_RECONSTRUCT]);;

(* In the scalar_rk variant the final AES round key (EL 10) is XORed in scalar    *)
(* registers X20/X21 into the input block halves, and the block ciphertext is     *)
(* word_xor (word_join <input_hi ^ key10_hi> <input_lo ^ key10_lo>) (9-round Q0). *)
(* This lemma rewrites that scalar-built form into the word_xor <9round>           *)
(* (word_xor rk10 inblock) shape that XOR_AES256_CIPHER_RECONSTRUCT consumes,      *)
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


(* ---- GHASH reduce-reconstruction lemmas (mc-agnostic, from 128 swp_S proof 600-687) ---- *)

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

Printf.printf "MARKER: reduce lemmas loaded\n%!";;

(* 256 AES abstractions + reduce 743-863 *)
let aes1c = new_definition
 `aes1c nonce (rk:int128 list) c : int128 =
    aesmc(aese (word_reversefields 8 (ctr_block nonce c)) (word_reversefields 8 (EL 0 rk)))`;;

let aes6c = new_definition
 `aes6c nonce (rk:int128 list) c : int128 = aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (word_reversefields 8 (ctr_block nonce c)) (word_reversefields 8 (EL 0 rk)))) (word_reversefields 8 (EL 1 rk)))) (word_reversefields 8 (EL 2 rk)))) (word_reversefields 8 (EL 3 rk)))) (word_reversefields 8 (EL 4 rk)))) (word_reversefields 8 (EL 5 rk)))`;;

let aes7c = new_definition
 `aes7c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk)))`;;

let aes11c = new_definition
 `aes11c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
     (aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk))))
      (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))))
      (word_reversefields 8 (EL 10 rk)))`;;

(* aes14p = pre-final-XOR 14-aese tower (14 aese, 13 aesmc, keys EL 0..13, NO EL14 XOR). *)
let aes14p = new_definition
 `aes14p (nonce:96 word) (rk:int128 list) (c:num) : int128 =
    aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
     (aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk))))
      (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))))
      (word_reversefields 8 (EL 10 rk))))(word_reversefields 8 (EL 11 rk))))
      (word_reversefields 8 (EL 12 rk))))(word_reversefields 8 (EL 13 rk))`;;

(* completion: aes14p ^ rk14 = the full 14-round AES-256 keystream (byte-reversed). *)
let AES14P_COMPLETE = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
    EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk
   ==> word_xor (aes14p nonce rk c) (word_reversefields 8 (EL 14 rk))
       = word_reversefields 8 (aes256_cipher (ctr_block nonce c) rk)`,
  DISCH_TAC THEN REWRITE_TAC[aes14p] THEN
  GEN_REWRITE_TAC LAND_CONV
   [INST ((`word_reversefields 8 (ctr_block nonce c):int128`,`plaintext:int128`) ::
          map (fun j -> (parse_term(Printf.sprintf "word_reversefields 8 (EL %d rk):int128" j),
                         mk_var("rk"^string_of_int j,`:int128`))) (0--14))
         AES256_CIPHER_RECONSTRUCT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; MAP] THEN ASM_REWRITE_TAC[]);;

Printf.printf "MARKER: AES-partial abstractions + AES14P_COMPLETE proven\n%!";;

(* ========================================================================= *)
(* Keystream-fold + counter/lane helper lemmas (256 analogs of the 128       *)
(* KEYSTREAM_FOLD / CT_TO_NCB / JOIN_* / mk_cbv, re-indexed to rk14/EL14).    *)
(* ========================================================================= *)

(* aes14p reached via the carried partials aes7c / aes11c (rewrite bridges). *)
let AES14P_VIA_AES7C = prove
 (`aes14p nonce rk c =
   aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese (aes7c nonce rk c)
     (word_reversefields 8 (EL 7 rk))))(word_reversefields 8 (EL 8 rk))))
     (word_reversefields 8 (EL 9 rk))))(word_reversefields 8 (EL 10 rk))))
     (word_reversefields 8 (EL 11 rk))))(word_reversefields 8 (EL 12 rk))))
     (word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes7c]);;

let AES14P_VIA_AES11C = prove
 (`aes14p nonce rk c =
   aese(aesmc(aese(aesmc(aese (aes11c nonce rk c) (word_reversefields 8 (EL 11 rk))))
     (word_reversefields 8 (EL 12 rk))))(word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes11c]);;

let AES14P_VIA_AES1C = prove
 (`aes14p nonce rk c = aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aes1c nonce rk c) (word_reversefields 8 (EL 1 rk)))) (word_reversefields 8 (EL 2 rk)))) (word_reversefields 8 (EL 3 rk)))) (word_reversefields 8 (EL 4 rk)))) (word_reversefields 8 (EL 5 rk)))) (word_reversefields 8 (EL 6 rk)))) (word_reversefields 8 (EL 7 rk)))) (word_reversefields 8 (EL 8 rk)))) (word_reversefields 8 (EL 9 rk)))) (word_reversefields 8 (EL 10 rk)))) (word_reversefields 8 (EL 11 rk)))) (word_reversefields 8 (EL 12 rk)))) (word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes1c]);;

let AES14P_VIA_AES6C = prove
 (`aes14p nonce rk c = aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aes6c nonce rk c) (word_reversefields 8 (EL 6 rk)))) (word_reversefields 8 (EL 7 rk)))) (word_reversefields 8 (EL 8 rk)))) (word_reversefields 8 (EL 9 rk)))) (word_reversefields 8 (EL 10 rk)))) (word_reversefields 8 (EL 11 rk)))) (word_reversefields 8 (EL 12 rk)))) (word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes6c]);;

(* --- dec-256 carry-depth AES abstractions (Q3=aes12c depth-12, Q8=aes5c depth-5) + aes14p bridges --- *)
let aes5c = new_definition
 `aes5c nonce (rk:int128 list) c : int128 =
    aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese
     (word_reversefields 8 (ctr_block nonce c))
     (word_reversefields 8 (EL 0 rk))))
     (word_reversefields 8 (EL 1 rk))))
     (word_reversefields 8 (EL 2 rk))))
     (word_reversefields 8 (EL 3 rk))))
     (word_reversefields 8 (EL 4 rk)))`;;
let aes12c = new_definition
 `aes12c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
     (aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk))))
      (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))))
      (word_reversefields 8 (EL 10 rk))))(word_reversefields 8 (EL 11 rk)))`;;
let AES14P_VIA_AES12C = prove
 (`aes14p nonce rk c =
   aese(aesmc(aese (aes12c nonce rk c) (word_reversefields 8 (EL 12 rk))))
     (word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes12c]);;
let AES14P_VIA_AES5C = prove
 (`aes14p nonce rk c =
   aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
     (aes5c nonce rk c) (word_reversefields 8 (EL 5 rk))))
     (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk))))
     (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))))
     (word_reversefields 8 (EL 10 rk))))(word_reversefields 8 (EL 11 rk))))
     (word_reversefields 8 (EL 12 rk))))(word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes5c]);;


(* keystream^input fold: word_xor(aes14p c)(word_xor inb rk14) = word_xor(rev8(cipher(ctr c)))(inb). *)
let KEYSTREAM_FOLD256 = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
    EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk
   ==> word_xor (aes14p nonce rk c) (word_xor inb (word_reversefields 8 (EL 14 rk)))
       = word_xor (word_reversefields 8 (aes256_cipher (ctr_block nonce c) rk)) inb`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP AES14P_COMPLETE th)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC WORD_BITWISE_RULE);;

(* ciphertext -> nist_cipher_block: word_xor(rev8(cipher(ctr(j+2))))(inblock j) = rev8(nist_cipher_block j). *)
let CT_TO_NCB256 = prove
 (`word_xor (word_reversefields 8 (aes256_cipher (ctr_block nonce (j+2)) rk)) (inblock j)
   = word_reversefields 8 (nist_cipher_block nonce rk inblock j)`,
  REWRITE_TAC[nist_cipher_block; cipher_block; aes_ctr_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

(* lane recombine (mc-agnostic, verbatim from 128). *)
let JOIN_SUBWORD_RECOMBINE = prove
 (`word_join (word_subword (x:int128) (64,64):int64) (word_subword x (0,64):int64) : int128 = x`,
  CONV_TAC WORD_BLAST);;
let JOIN_XOR_LANES = prove
 (`word_join (word_xor (word_subword (a:int128) (64,64):int64) (word_subword (b:int128) (64,64):int64))
             (word_xor (word_subword a (0,64):int64) (word_subword b (0,64):int64)) : int128
   = word_xor a b`,
  CONV_TAC WORD_BLAST);;
let ZXZX32 = prove
 (`word_zx (word_zx (x:int32):int64):int32 = x`, CONV_TAC WORD_BLAST);;
let ZXNEST4 = prove
 (`word_zx (word_zx (word_zx (word_zx (x:int32):int64):int32):int64):int32 = x`, CONV_TAC WORD_BLAST);;

let mk_cbv cval =
  let inst = INST [`word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64`,`ivhi:int64`;
                   `word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64`,`ivlo:int64`;
                   cval,`cval:num`] CTR_BLOCK_BUILD_V in
  MP inst (prove(lhand(concl inst), REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST));;

(* DECRYPT-specific *)
let INBLOCK_REASSEMBLE = prove
 (`(word_join
     (word_join
      (word_join (word_subword (x:int128) (64,8):byte) (word_subword x (72,8):byte):int16)
      (word_join (word_subword x (80,8):byte) (word_subword x (88,8):byte):int16):int32)
     (word_join
      (word_join (word_subword x (96,8):byte) (word_subword x (104,8):byte):int16)
      (word_join (word_subword x (112,8):byte) (word_subword x (120,8):byte):int16):int32):int64
    = word_subword (word_reversefields 8 x) (0,64)) /\
   (word_join
     (word_join
      (word_join (word_subword (x:int128) (0,8):byte) (word_subword x (8,8):byte):int16)
      (word_join (word_subword x (16,8):byte) (word_subword x (24,8):byte):int16):int32)
     (word_join
      (word_join (word_subword x (32,8):byte) (word_subword x (40,8):byte):int16)
      (word_join (word_subword x (48,8):byte) (word_subword x (56,8):byte):int16):int32):int64
    = word_subword (word_reversefields 8 x) (64,64))`,
  CONV_TAC WORD_BLAST);;

let DEC_GHASH_NORM_TAC : tactic =
  REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
  REWRITE_TAC[GSYM nist_input_block] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV);;
Printf.printf "MARKER: dec-256 front matter loaded\n%!";;(* dec-256 stepping infrastructure ported from enc-256 *)
(* 2026-09-20: CORRECTED to the 2-level split (from the enc-mem2 precedent, aes_gcm_enc_kernel_x4_scalar_iv_mem2.ml
   line 447) -- the str-w mem2 pattern (dec-256's) needs BOTH the bytes128->bytes64 split AND the bytes64@+8 ->
   bytes32 split, so the counter-word lane (bytes32 @ +12) and the nonce lanes (bytes64 @ +0, bytes32 @ +8)
   are all exposed and resolve against the surviving reads.  The old 1-level version only split bytes128->bytes64
   and left the +8/+12 lanes unresolved -- THE bug. *)
let MERGE_CTR128_TAC off sname =
  let woff n = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                       mk_comb(`word:num->int64`,mk_small_numeral n)) in
  MP_TAC(ISPECL [`memory`; woff off; mk_var(sname,`:armstate`)]
           (el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT))) THEN
  MP_TAC(ISPECL [`memory`; woff (off + 8); mk_var(sname,`:armstate`)]
           (el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC;;
let gc2 keeplist c = try let l=lhs c in let rd,st=dest_comb l in let rr,cc=dest_comb rd in
   if is_const cc && mem (fst(dest_const cc)) keeplist then
     (match st with Var(nm,_) when String.length nm>=2 && nm.[0]='s' ->
        (try Some(fst(dest_const cc), int_of_string(String.sub nm 1 (String.length nm-1))) with _->None) |_->None) else None
  with _->None;;
(* Assumption-list GC (verbatim from upstream aes_gcm_utils.ml, commit 8afc5432/071b1411): drop a fact about
   an OLD state when the same fact modulo the state var already holds of the current state and no OTHER
   assumption pins that old state.  A fact "refers to" a state that occurs in it OTHER than as the state its
   own left-hand read is about (so `read Q5 s148 = ..read(mem..)s99..` protects s99, not s148).  Appended to
   gkeepN so the stale-state forall region-invariants + multi-state derived facts do not accumulate across a
   leg (the per-register pruner keeps them); without this every ARM_STEP + ASM_REWRITE is linear in the asl,
   giving quadratic leg cost.  ~9x speedup on the 256 enc SWP proof. *)
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
(* counter stack-slot offsets (for the staged-ctr closer / a future slot-anchoring stepper variant): the 4
   staged counter blocks sp+{160,176,192,208}, their +8 high-halves sp+{168,184,200,216} (bytes64), and the
   +12 counter-word lanes sp+{172,188,204,220} (bytes32).  Mirrors upstream ctr_slots_all.  NOTE: anchoring
   these in gkeepN keeps the reads but does NOT by itself RESOLVE the raw bytes64 staged-block reads to the
   word_or(nonce)(counter<<32) form that CTR_BLOCK_BUILD_INSERT needs -- that also requires a bytes64->bytes32
   counter-lane merge (gcm-mem2-3way-merge).  Kept here as data for the staged-ctr fix; gkeepN below is the
   validated DISCARD_STALE version (do not anchor slots without also adding the lane merge, else asl re-bloats). *)
let ctr_slot_offsets = ["160";"168";"172";"176";"184";"188";"192";"200";"204";"208";"216";"220"];;
(* Q14 holds the GHASH block-0 input (inblock(4i)); its value is referenced by the Q30 accumulator tower at an
   EARLY state (read Q14 s10) but Q14 is later overwritten (AES scratch + next-group reload).  gc2's latest-only
   pruning would drop the early `read Q14 s0 = inblock(4i)` fact, leaving the tower's `read Q14 s10` unfoldable
   -> the 800-var block-0 byte-tower blowup in the seed closer.  Exempt `read Q14 sK` from BOTH prunings (like
   in_p) so the block-0 fact survives for the seed closer to fold. Cheap: Q14 has few states. *)
let is_q14_read c = try (match lhs c with
    Comb(Comb(Const("read",_),Const("Q14",_)),_) -> true | _ -> false) with _ -> false;;
(* 2026-09-19: FAITHFUL PORT of dec-128's gkeepN_mem2 (keep_htable_swp file lines 1570-1597).  The mem2
   staged counter blocks live at stack offsets 160/176/192/208; their block-base reads must be ANCHORED
   (kept across states) so read-over-write resolves the staged blocks at the body-end (the plain gkeepN's
   latest-only pruning dropped them -> SP_SLOT/AES/out closers failed).  is_spctr_read anchors ONLY the 4
   block-base reads (NOT +8/+12 lanes or bytes8 components -> no bloat).  Also anchor tag_p/ivec_p/htable_p
   reads + handle the in_p/out_p frame foralls (keep) like dec-128.  Replaces the old gkeepN + DISCARD_STALE. *)
let is_spctr_read c = try
    let l = lhs c in
    fst(dest_const(fst(strip_comb l)))="read" && free_in `stackpointer:int64` l &&
    (can (find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n))
           when (try fst(dest_var sp)="stackpointer" with _->false) ->
             (let v=string_of_term n in v="160"||v="176"||v="192"||v="208") | _ -> false)) l)
  with _ -> false;;
let state_of_forall c = try
    (match snd(strip_forall c) with
     | Comb(Comb(Const("==>",_),_),bod) ->
        (match find_terms (fun t -> match t with Comb(Comb(Const("read",_),_),Var(nm,_)) when String.length nm>=1 && nm.[0]='s' -> true | _ -> false) bod with
         | (Comb(Comb(Const("read",_),_),Var(nm,_)))::_ -> Some nm | _ -> None)
     | _ -> None) with _ -> None;;
(* state index of a `read _ sK = _` fact (K), or -1 *)
let read_state_idx c = try (match lhs c with
   Comb(Comb(Const("read",_),_),Var(nm,_)) when String.length nm>=2 && nm.[0]='s' ->
     int_of_string(String.sub nm 1 (String.length nm-1)) | _ -> -1) with _ -> -1;;
(* spctr block-base offset (160/176/192/208) of a read fact, or -1 *)
let spctr_off c = try (match find_terms (fun t -> match t with
     Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n)) when (try fst(dest_var sp)="stackpointer" with _->false)
       -> (let v=dest_small_numeral n in v=160||v=176||v=192||v=208) | _ -> false) (lhs c) with
   | (Comb(Comb(_,_),Comb(_,n)))::_ -> dest_small_numeral n | _ -> -1) with _ -> -1;;
(* 2026-09-20: the DESIGN-A staged-block closer primes constant nonce lanes at s0:
     read(bytes64 sp+{160,176,192,208})s0 = subword(rev8(ctr_block nonce 2))(0,64)   [lo]
     read(bytes32 sp+{168,184,200,216})s0 = subword(rev8(ctr_block nonce 2))(64,32)  [mid]
   These are s0-anchored CONSTANTS (never written by the body -- only the +12 counter lane is), needed at the
   per-slot MERGE (steps 16/20/32/35).  is_spctr_read/spmx anchors ONLY the bytes128 block reads at
   160/176/192/208 and its latest-per-OFFSET pruning would drop these (mid-lanes at 168.. aren't matched at all;
   lo-lanes conflate with the bytes128 baseline at the same offset).  is_ctrlane_read matches them by the exact
   lane offset set {160,176,192,208,168,184,200,216} AND requires the RHS to be a subword-of-ctr_block-2 (the
   primed constant form) so it only ever protects the priming facts, never a transient read. *)
(* APPROACH E: the primed lanes have VARIABLE RHS (ivlo | word_subword ivhi (0,32)) -- NOT the compound
   word_subword(rev8(ctr_block 2))(..) form (which crashes native ARM_STEP).  Match those. *)
let is_ctrlane_read c =
  try
    let l = lhs c in
    let r = rhs c in
    let headok = fst(dest_const(fst(strip_comb l))) = "read" in
    let spok = free_in `stackpointer:int64` l in
    let offpred t = match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n)) ->
           (try (fst(dest_var sp) = "stackpointer") &&
                (let v = dest_small_numeral n in
                 v=160||v=176||v=192||v=208||v=168||v=184||v=200||v=216)
            with _ -> false)
       | _ -> false in
    (* RHS is ivlo (a variable) or word_subword ivhi (0,32) -- the Approach-E variable-form nonce lane *)
    let rhsok = (try fst(dest_var r) = "ivlo" with _ -> false) ||
                (free_in `ivhi:int64` r &&
                 can (find_term (fun t -> match t with Const("word_subword",_) -> true | _ -> false)) r) in
    headok && spok && (can (find_term offpred) l) && rhsok
  with _ -> false;;
(* address-modulo-state KEY of a ctrlane read (the lhs component, i.e. the (:>) comb, ignoring the state var):
   distinguishes bytes64@192 from bytes32@200 etc. so per-lane latest-state pruning doesn't conflate them. *)
let ctrlane_key c = try let l = lhs c in fst(dest_comb l) with _ -> `T`;;
let gkeepN keeplist th sname = ARM_STEP_TAC th [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) -> let cs=map(fun(_,t)->concl t)asl in
    let mx=map(fun r->(r,itlist(fun c m->match gc2 keeplist c with Some(rr,k)when rr=r&&k>m->k|_->m)cs(-1)))keeplist in
    (* per-offset latest state index over the anchored spctr reads (keep only latest -> no bloat) *)
    let spmx = itlist (fun c acc -> if is_spctr_read c then
        (let off=spctr_off c and k=read_state_idx c in
         try let old=List.assoc off acc in if k>old then (off,k)::List.remove_assoc off acc else acc
         with Not_found -> (off,k)::acc) else acc) cs [] in
    (* per-lane (address-mod-state) latest state index over the primed ctrlane reads -- keep ONLY the latest
       so the lanes do NOT accumulate one-copy-per-state (which bloats the asl and -- observed -- makes native
       ARM_STEP choke a few steps in).  The nonce lanes are counter-independent constants, so the latest-state
       copy is as good as s0. *)
    let lanemx = itlist (fun c acc -> if is_ctrlane_read c then
        (let key=ctrlane_key c and k=read_state_idx c in
         try let (_,old)=List.find (fun (kk,_)->kk=key) acc in
             if k>old then (key,k)::List.filter (fun (kk,_)->not(kk=key)) acc else acc
         with Not_found -> (key,k)::acc) else acc) cs [] in
    let anchored c = try
        (fst(dest_const(fst(strip_comb(lhs c))))="read" &&
         ((free_in `tag_p:int64` (lhs c)) || (free_in `ivec_p:int64` (lhs c)) ||
          (free_in `htable_p:int64` (lhs c)) || (free_in `in_p:int64` (lhs c)))) || is_q14_read c
      with _ -> false in
    DISCARD_ASSUMPTIONS_TAC(fun th->let c=concl th in
      if (try can (find_term (fun x -> match x with Const("MAYCHANGE",_) -> true | _ -> false)) c with _->false)
      then (try let _,args = strip_comb c in string_of_term(last args) <> sname with _ -> false) else
      if is_forall c then
        (if free_in `in_p:int64` c || free_in `out_p:int64` c then false
         else (match state_of_forall c with Some nm -> nm <> sname | None -> false)) else
      if is_ctrlane_read c then
        (try read_state_idx c < snd(List.find (fun (kk,_)->kk=ctrlane_key c) lanemx) with _ -> false) else
      if is_spctr_read c then (try read_state_idx c < List.assoc (spctr_off c) spmx with _ -> false) else
      if anchored c then false else
      match gc2 keeplist c with Some(r,k)->k<List.assoc r mx
      |None->(try let l=lhs c in let rd,st=dest_comb l in (match st with Var(nm,_)->nm<>sname&&String.length nm>=1&&nm.[0]='s'|_->false)with _->false))(asl,w));;
(* Extract (ptr-name, state-index) from a `read (memory :> bytes128 tag_p/ivec_p) sK = V` assumption. *)
let get_membyteread c =
  try let l = lhs c in
      let rd, st = dest_comb l in
      let _, comp = dest_comb rd in
      let stname = (match st with Var(nm,_) when String.length nm>=2 && nm.[0]='s' ->
                       int_of_string(String.sub nm 1 (String.length nm-1)) | _ -> raise Exit) in
      if free_in `tag_p:int64` comp then Some("tag_p", stname)
      else if free_in `ivec_p:int64` comp then Some("ivec_p", stname)
      else None
  with _ -> None;;
(* FILL variant: keep the tag_p/ivec_p bytes128 reads (gkeepN drops them -> conj3,4 FAIL, the s297 read is absent),
   BUT keep ONLY THE LATEST-state read per ptr (else ~600 stale reads accumulate -> 10.6GB RSS + hours-long close).
   The latest read + the tag_p/ivec_p<->stack nonoverlaps (now in fill_goal precond) let ENSURES_FINAL_STATE_TAC
   carry it forward across the [sp,#*] stores to s297.  (in_p reads still never-discarded, as gkeepN.) *)
let gkeepF keeplist th sname = ARM_STEP_TAC th [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) -> let cs=map(fun(_,t)->concl t)asl in
    let mx=map(fun r->(r,itlist(fun c m->match gc2 keeplist c with Some(rr,k)when rr=r&&k>m->k|_->m)cs(-1)))keeplist in
    (* per-ptr max state index over the tag_p/ivec_p bytes128 reads *)
    let mmx=itlist (fun c acc -> match get_membyteread c with
       | Some(p,k) -> (try let old=List.assoc p acc in
                           if k>old then (p,k)::(List.remove_assoc p acc) else acc
                       with Not_found -> (p,k)::acc)
       | None -> acc) cs [] in
    DISCARD_ASSUMPTIONS_TAC(fun th->let c=concl th in
      if (try can (find_term (fun x -> match x with Const("MAYCHANGE",_) -> true | _ -> false)) c with _->false)
      then (try let _,args = strip_comb c in string_of_term(last args) <> sname with _ -> false) else
      if (try free_in `in_p:int64` (lhs c) with _->false) then false else
      (* tag_p/ivec_p bytes128 read: keep iff it is the latest-state one for its ptr; discard stale copies *)
      (match get_membyteread c with
       | Some(p,k) -> (try k < List.assoc p mmx with _ -> false)
       | None ->
         match gc2 keeplist c with
         Some(r,k)->k<List.assoc r mx
         |None->(try let l=lhs c in let rd,st=dest_comb l in (match st with Var(nm,_)->nm<>sname&&String.length nm>=1&&nm.[0]='s'|_->false)with _->false)))(asl,w));;
let IN_P_ADDR_FOLD_CONV : conv =
  let inner = (REWR_CONV(GSYM ADD_ASSOC) THENC RAND_CONV NUM_ADD_CONV) in
  ONCE_DEPTH_CONV(fun t -> match t with
    | Comb(Comb(Const("word_add",_), v), Comb(Const("word",_), _))
        when (try fst(dest_var v) = "in_p" with _ -> false)
      -> RAND_CONV(RAND_CONV inner) t
    | _ -> failwith "IN_P_ADDR_FOLD_CONV");;

(* 256 carried/reduce reg-set: AES partials Q3/Q4/Q8 + reduce Q1/Q2/Q11/Q13/Q14/Q29/Q30 + h-powers.
   (REDSETX_DEC / ghost_lanes_dec / merges_dec are defined in dec256_bodyleg_setup.ml, not here.) *)
let contains sub s =
  let ls = String.length s and lsub = String.length sub in
  let rec go i = if i+lsub > ls then false
    else if String.sub s i lsub = sub then true else go (i+1) in go 0;;
(* swpS256_inv_dec: dec-256 SWP mid-pipeline invariant (53 conjuncts).
   FIXED 2026-09-18: Q10/Q11 2nd term corrected from spurious nested pmul to byteswap128(h_power 0)
   -- this made the whole GHASH pipeline (incl Q30 accumulator) numerically consistent; body-leg valid.
   Fully-typed dump (reparses faithfully). *)

let swpS256_inv_dec : term =
`\(i:num) (s:armstate).
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X3:(armstate,(64)word)component)
    (s:armstate) =
    (tag_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X4:(armstate,(64)word)component)
    (s:armstate) =
    (ivec_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X6:(armstate,(64)word)component)
    (s:armstate) =
    (htable_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (SP:(armstate,(64)word)component)
    (s:armstate) =
    (stackpointer:(64)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (tag_p:(64)word))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8 (tag0:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (ivec_p:(64)word))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) 2) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q18:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 0 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q19:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 1 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q20:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 2 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q21:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 3 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q22:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 4 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q23:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 5 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q24:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 6 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q25:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 7 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q26:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 8 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q27:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 9 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q28:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 10 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q15:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 11 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q16:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 12 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q17:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 13 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q2:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 14 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q7:(armstate,(128)word)component)
    (s:armstate) =
    (word:num->(128)word) 13979173243358019584 /\
    (htable_mem_4:(128)word->(64)word->armstate->bool)
    ((ghash_twist:(128)word->(128)word)
    ((aes256_cipher:(128)word->((128)word)list->(128)word)
     ((word:num->(128)word) 0)
    (rk:((128)word)list)))
    (htable_p:(64)word)
    (s:armstate) /\
    (forall (j:num).
         (j:num) < (nblocks:num)
         ==> (read:(armstate,(128)word)component->armstate->(128)word)
             ((memory:(armstate,(64)word->(8)word)component) :>
              (bytes128:(64)word->((64)word->(8)word,(128)word)component)
              ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
              ((word:num->(64)word) (16 * (j:num)))))
             (s:armstate) =
             (inblock:num->(128)word) (j:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X0:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (64 * ((i:num) + 1))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X2:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
    ((word:num->(64)word) (64 * (i:num))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X1:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((loop_count:num) - ((i:num) + 1)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X15:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((len_bits:num) DIV 8) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X9:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (loop_remain:num) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X13:(armstate,(64)word)component)
    (s:armstate) =
    (word_zx:(32)word->(64)word) ((word:num->(32)word) (4 * (i:num) + 2)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (4 * (i:num) + 2)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (4 * (i:num) + 3)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 192)))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (4 * (i:num) + 4)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 208)))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (4 * (i:num) + 5)) /\
    (forall (j:num).
         (j:num) < 4 * (i:num)
         ==> (read:(armstate,(128)word)component->armstate->(128)word)
             ((memory:(armstate,(64)word->(8)word)component) :>
              (bytes128:(64)word->((64)word->(8)word,(128)word)component)
              ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
              ((word:num->(64)word) (16 * (j:num)))))
             (s:armstate) =
             (word_xor:(128)word->(128)word->(128)word)
             ((aes_ctr_block:(96)word->((128)word)list->num->(128)word)
              (nonce:(96)word)
              (rk:((128)word)list)
             (j:num))
             ((inblock:num->(128)word) (j:num))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) (64 * (i:num) + 32))))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((aes_ctr_block:(96)word->((128)word)list->num->(128)word)
     (nonce:(96)word)
     (rk:((128)word)list)
    (4 * (i:num) + 2))
    ((inblock:num->(128)word) (4 * (i:num) + 2)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q30:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((nist_ghash:(128)word->(128)word->((128)word)list->(128)word)
      ((aes256_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list))
      (tag0:(128)word)
     ((list_of_seq:(num->(128)word)->num->((128)word)list)
      ((nist_input_block:(num->(128)word)->num->(128)word)
      (inblock:num->(128)word))
     (4 * (i:num))))
    (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((nist_ghash:(128)word->(128)word->((128)word)list->(128)word)
      ((aes256_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list))
      (tag0:(128)word)
     ((list_of_seq:(num->(128)word)->num->((128)word)list)
      ((nist_input_block:(num->(128)word)->num->(128)word)
      (inblock:num->(128)word))
     (4 * (i:num))))
    (64,64)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q3:(armstate,(128)word)component)
    (s:armstate) =
    (aes12c:(96)word->((128)word)list->num->(128)word) (nonce:(96)word)
    (rk:((128)word)list)
    (4 * (i:num) + 3) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q8:(armstate,(128)word)component)
    (s:armstate) =
    (aes5c:(96)word->((128)word)list->num->(128)word) (nonce:(96)word)
    (rk:((128)word)list)
    (4 * (i:num) + 5) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q0:(armstate,(128)word)component)
    (s:armstate) =
    (inblock:num->(128)word) (4 * (i:num) + 3) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q1:(armstate,(128)word)component)
    (s:armstate) =
    (inblock:num->(128)word) (4 * (i:num) + 1) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q13:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes256_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    3))
    ((karatsuba_mid:(128)word->(64)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes256_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    2)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q29:(armstate,(128)word)component)
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes256_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    3) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q31:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (4 * (i:num) + 2)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q4:(armstate,(128)word)component)
    (s:armstate) =
    (word_zx:(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_xor:(128)word->(128)word->(128)word)
      ((word_join:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word)
        ((word_reversefields:num->(128)word->(128)word) 8
        ((inblock:num->(128)word) (4 * (i:num) + 1)))
       (0,64))
      ((word_subword:(128)word->num#num->(64)word)
       ((word_reversefields:num->(128)word->(128)word) 8
       ((inblock:num->(128)word) (4 * (i:num) + 1)))
      (64,64)))
     ((word_zx:(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num) + 1)))
     (0,64))))
    (0,64)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q5:(armstate,(128)word)component)
    (s:armstate) =
    (word_pmul:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_reversefields:num->(128)word->(128)word) 8
     ((inblock:num->(128)word) (4 * (i:num) + 1)))
    (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes256_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     2))
    (64,64)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q6:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_xor:(128)word->(128)word->(128)word)
       ((word_join:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word)
         ((word_reversefields:num->(128)word->(128)word) 8
         ((inblock:num->(128)word) (4 * (i:num) + 2)))
        (0,64))
       ((word_subword:(128)word->num#num->(64)word)
        ((word_reversefields:num->(128)word->(128)word) 8
        ((inblock:num->(128)word) (4 * (i:num) + 2)))
       (64,64)))
      ((word_subword:(256)word->num#num->(128)word)
       ((word_join:(128)word->(128)word->(256)word)
        ((word_join:(64)word->(64)word->(128)word)
         ((word_subword:(128)word->num#num->(64)word)
          ((word_reversefields:num->(128)word->(128)word) 8
          ((inblock:num->(128)word) (4 * (i:num) + 2)))
         (0,64))
        ((word_subword:(128)word->num#num->(64)word)
         ((word_reversefields:num->(128)word->(128)word) 8
         ((inblock:num->(128)word) (4 * (i:num) + 2)))
        (64,64)))
       ((word_join:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word)
         ((word_reversefields:num->(128)word->(128)word) 8
         ((inblock:num->(128)word) (4 * (i:num) + 2)))
        (0,64))
       ((word_subword:(128)word->num#num->(64)word)
        ((word_reversefields:num->(128)word->(128)word) 8
        ((inblock:num->(128)word) (4 * (i:num) + 2)))
       (64,64))))
      (64,128)))
     (64,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((word_join:(64)word->(64)word->(128)word)
      ((karatsuba_mid:(128)word->(64)word)
      ((h_power:(128)word->num->(128)word)
       ((ghash_twist:(128)word->(128)word)
       ((aes256_cipher:(128)word->((128)word)list->(128)word)
        ((word:num->(128)word) 0)
       (rk:((128)word)list)))
      1))
     ((karatsuba_mid:(128)word->(64)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes256_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     0)))
    (64,64)))
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_xor:(128)word->(128)word->(128)word)
       ((word_join:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word)
         ((word_reversefields:num->(128)word->(128)word) 8
         ((inblock:num->(128)word) (4 * (i:num) + 3)))
        (0,64))
       ((word_subword:(128)word->num#num->(64)word)
        ((word_reversefields:num->(128)word->(128)word) 8
        ((inblock:num->(128)word) (4 * (i:num) + 3)))
       (64,64)))
      ((word_zx:(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_reversefields:num->(128)word->(128)word) 8
       ((inblock:num->(128)word) (4 * (i:num) + 3)))
      (0,64))))
     (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((word_join:(64)word->(64)word->(128)word)
      ((karatsuba_mid:(128)word->(64)word)
      ((h_power:(128)word->num->(128)word)
       ((ghash_twist:(128)word->(128)word)
       ((aes256_cipher:(128)word->((128)word)list->(128)word)
        ((word:num->(128)word) 0)
       (rk:((128)word)list)))
      1))
     ((karatsuba_mid:(128)word->(64)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes256_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     0)))
    (0,64))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q9:(armstate,(128)word)component)
    (s:armstate) =
    (word_pmul:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_reversefields:num->(128)word->(128)word) 8
     ((inblock:num->(128)word) (4 * (i:num) + 1)))
    (64,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes256_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     2))
    (0,64)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q10:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num) + 2)))
     (64,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes256_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     1))
    (0,64)))
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num) + 3)))
     (64,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes256_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     0))
    (0,64))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q11:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num) + 2)))
     (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes256_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     1))
    (64,64)))
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num) + 3)))
     (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes256_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     0))
    (64,64))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q14:(armstate,(128)word)component)
    (s:armstate) =
    (inblock:num->(128)word) (4 * (i:num))`;;
(* ============================================================================
   dec-256 SWP BODYLEG closers: the extra lemmas (ported from dec-128, adapted
   aes128->aes256) + the dispatcher CLOSE_DEC256.
   Requires: front-matter (aes256_cipher/nist_ghash/h_power/karatsuba_mid/
   polyval_reduce_g2/RECONSTRUCT_POLYVAL_REDUCE_G2/POLYVAL_REDUCE_G2/
   PMUL_KARATSUBA_JOIN_ALT/INBLOCK_REASSEMBLE/DEC_GHASH_NORM_TAC/aesNc/
   AES14P_VIA_*/KEYSTREAM_FOLD256/CT_TO_NCB256/CTR_BLOCK_BUILD_INSERT/
   XOR_AES256_CIPHER_RECONSTRUCT/mk_cbv/ZX_COUNTER_UD/ZX_COUNTER_INC/CTR_ZX_NORM)
   + swpS256_inv_dec + body_goal_dec + steppers (gkeepN etc.) all loaded.
   ============================================================================ *)

(* --- ported GHASH/AES/arith building blocks (all test-compiled in MCP 2026-09-17) --- *)
let SWP_JOIN_IS_BSW = prove
 (`!x:int128. word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 = byteswap128 x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128]);;

let SWP_SUBWORD_JOIN_MID = WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`;;

let xor_rcancel = prove(`!a b p:int128. (word_xor a p = word_xor b p) <=> (a = b)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* the crux batched GHASH-reduce identity (aes256): the 4-block Horner accumulator step. *)
let SWP_GHASH_BRANCH2_256 = prove
 (`polyval_reduce_prop3
     (word_xor (word_pmul (nist_input_block inblock (4*i+3):int128)
                          (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0))
     (word_xor (word_pmul (nist_input_block inblock (4*i+2))
                          (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1))
     (word_xor (word_pmul (nist_input_block inblock (4*i+1))
                          (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2))
     (word_pmul (word_xor (nist_ghash (aes256_cipher (word 0) rk) tag0
                              (list_of_seq (nist_input_block inblock) (4*i)))
                          (nist_input_block inblock (4*i)))
                (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3)))))
   = nist_ghash (aes256_cipher (word 0) rk) tag0
       (list_of_seq (nist_input_block inblock) (4*i+4))`,
  MP_TAC(ISPECL [`ghash_twist (aes256_cipher (word 0) rk)`;
                 `[nist_input_block inblock (4*i+1); nist_input_block inblock (4*i+2); nist_input_block inblock (4*i+3)]:(int128)list`;
                 `nist_ghash (aes256_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4*i)):int128`;
                 `nist_input_block inblock (4*i):int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 * i + 4 = SUC(SUC(SUC(SUC(4 * i))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* dec out-store readback (14-round, aes256): word_xor inblock (word_xor rk14 (aese-tower))
   = word_xor (rev8(aes256_cipher(rev8 plaintext) rk-list)) inblock. *)
let XOR_AES256_CIPHER_RECONSTRUCT_DEC = prove
 (`word_xor inblock (word_xor rk14
     (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
      (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
      (aese (aesmc (aese plaintext rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7))
      rk8)) rk9)) rk10)) rk11)) rk12)) rk13)) =
   word_xor
   (word_reversefields 8
   (aes256_cipher (word_reversefields 8 plaintext)
   (MAP (word_reversefields 8)
   [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10; rk11; rk12; rk13; rk14])))
   inblock`,
  ONCE_REWRITE_TAC[GSYM XOR_AES256_CIPHER_RECONSTRUCT] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* X1 decrement matched to the invariant form word(loop_count-(i+1)). *)
let SWP_SUB_LEMMA_DEC = prove
 (`i < loop_count - 2 ==> word_sub (word (loop_count - (i+1)):int64) (word 1) = word (loop_count - ((i+1)+1))`,
  DISCH_TAC THEN SUBGOAL_THEN `loop_count - ((i+1)+1) = (loop_count - (i+1)) - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < loop_count - 2 ==> 1 <= loop_count - (i+1)`]);;

(* ============================================================================
   2026-09-18: SWP pipelined-accumulator machinery (ported from proven enc-256-swp).
   The dec-256 loop-head Q30 is NOT the settled nist_ghash..4(i+1) (that conjunct is
   FALSE -- HOL-certified: the machine reduce at loop head is a pipelined partial, not
   the settled group-accumulator).  swpgrp = the abstract recursive Horner accumulator;
   SWPGRP_IS_NIST_GHASH bridges it to nist_ghash at DRAIN.  See memory/gcm-dec256-swp-recon.md
   for the full diagnosis + the invariant-Q30 fix plan (read the sim's own body-end form,
   or use the swpgrp/CORE_REDUCE_GHASH reflexive close from enc lines 1371-1711). *)
let swpgrp = define
 `swpgrp (gt:int128) (acc:int128) 0 (blk:num->int128) = acc /\
  swpgrp gt acc (SUC i) blk =
    ghash_polyval_acc gt (swpgrp gt acc i blk)
      [blk (4*i); blk (4*i+1); blk (4*i+2); blk (4*i+3)]`;;
let LIST_OF_SEQ_APPEND = prove
 (`!n f m. list_of_seq f (m + n) =
           APPEND (list_of_seq f m) (list_of_seq (\i. f(m+i)) n)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND; o_THM; ETA_AX]);;
let SWPGRP_IS_NIST_GHASH = prove
 (`!h acc i blk.
       swpgrp (ghash_twist h) acc i blk =
       nist_ghash h acc (list_of_seq blk (4 * i))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[swpgrp; MULT_CLAUSES; LIST_OF_SEQ; nist_ghash];
    REWRITE_TAC[ARITH_RULE `4 * SUC i = 4 * i + 4`] THEN
    REWRITE_TAC[LIST_OF_SEQ_APPEND] THEN REWRITE_TAC[NIST_GHASH_APPEND] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[swpgrp] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIST_OF_SEQ_CLAUSES] THEN REWRITE_TAC[ARITH_RULE `4*i+0 = 4*i`] THEN
    REWRITE_TAC[NIST_GHASH_IS_POLYVAL]]);;

Printf.printf "MARKER: dec256 extra closer-lemmas proven (incl swpgrp/SWPGRP_IS_NIST_GHASH)\n%!";;

(* ============================================================================
   VALIDATED Q30-seed recon PREFIX (2026-09-17, step-by-step in MCP against the
   typed body-end goal 05).  Reduces the seed conjunct
     word_subword (word_join BIG) (64,128) = word_join (sw ACC 0)(sw ACC 64)
   to two branches: branch1 (machine word_join = polyval_reduce_prop3 packing,
   over OPAQUE p1/p2/p3/ks.. abbrevs) + branch2 (= SWP_GHASH_BRANCH2_256).
   The prefix (below) is confirmed to fire in order.  REMAINING: branch1 endgame
   -- after EXPAND[ks;ks';ks'';ks''']+WORD_SIMPLE_SUBWORD the goal is
   `word_join <p-abbrev machine> = polyval_reduce_prop3 <p-abbrev packing>`;
   dec-128's `AP_TERM_TAC THEN ...BITBLAST` does NOT apply (heads differ:
   word_join vs polyval_reduce_prop3, because dec-256 packs the reduce as a raw
   word_join not dec-128's word_xor(word_join..)).  NEXT: unfold polyval_reduce_prop3
   (LET_DEF) on RHS -> both sides word_join(64)(64); BINOP_TAC; per-half bounded
   BITBLAST/WORD_BLAST.  (A bare full-word BITBLAST times out >600s in MCP but the
   pmul-by-poly-const is the cost; splitting halves should bound it. Native has no cap.) *)
let SEED_RECON_PREFIX_256 : tactic =
  REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN DEC_GHASH_NORM_TAC THEN
  MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes256_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * i)))`;
      `cipherblock_0 = nist_input_block inblock (4 * i)`; `cipherblock_1 = nist_input_block inblock (4 * i + 1)`;
      `cipherblock_2 = nist_input_block inblock (4 * i + 2)`; `cipherblock_3 = nist_input_block inblock (4 * i + 3)`;
      `h0 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`; `h1 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 2`; `h3 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3 (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
      (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
      (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
      (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC;;
(* branch1 prep (to the p-abbrev endgame): *)
let SEED_BRANCH1_PREP_256 : tactic =
  REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
  REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM] `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[];;

(* ============================================================================
   2026-09-17 CORRECTED seed approach (DISASM-VALIDATED: invariant Q30 is right).
   DISASM: body writes Q30 by `ext v30, v5, v5, #8` (@0x4ec) = 64-bit HALF-SWAP of
   v5, where v5 = the settled GHASH reduce = nist_ghash..(4(i+1)) in register order.
   So the seed goal, after SWP_SUBWORD_JOIN_MID, is
     <machine half-swap of reduce> = word_join (sw ACC 0)(sw ACC 64)   [ACC=nist_ghash..4(i+1)]
   BOTH sides are the SAME half-swap.  The earlier "branch2 false" was a TRANS artifact
   (TRANS'd through bare prop3, not its half-swap).  CORRECT recipe (validated prefix in MCP):
     DISCH; REWRITE[SWP_SUBWORD_JOIN_MID]; DEC_GHASH_NORM_TAC; ABBREV sofar/cb0..3/h0..3;
     REWRITE[GSYM WORD_SUBWORD_XOR];
     REWRITE[ARITH_RULE `4*(i+1)=4*i+4`];
     REWRITE[SYM(SPEC_ALL SWP_GHASH_BRANCH2_256)]   (* RHS nist_ghash..(4i+4) -> prop3(packing), BOTH occ *)
       -> RHS = word_join(sw(prop3 pk)0)(sw(prop3 pk)64) = half-swap(prop3 pk);
     GEN_REWRITE(RAND_CONV o TOP_DEPTH_CONV)[polyval_reduce_prop3]; let_CONV   (* unfold prop3 on RHS *)
       -> RHS = word_join<g/f lanes>; both sides word_join;
     BINOP_TAC  -> 2 per-half goals, now CORRECTLY ALIGNED (both half-swaps of the reduce);
     each half: pure word_join/subword/xor/pmul over sofar/cb/h (9 int128 vars) -- close by
     BITBLAST (native, bounded per-half) OR abstract the ~20 nested pmuls to opaque vars then WORD_BLAST.
   branch2 issue RESOLVED: no separate branch2 -- the GSYM BRANCH2 rewrite folds nist_ghash into the
   RHS packing BEFORE the split, so both halves are the single aligned word-identity.
   REMAINING: the per-half blast is still heavy (pmul-by-poly-const). Either (i) native run per-half
   (no 600s cap), or (ii) full pmul-abstraction to opaque then instant WORD_BLAST. Try (ii) first.
   ============================================================================ *)

(* dispatcher CLOSE_DEC256 + counter/AES/out closers live in DEVEL_dec256_bodyleg.ml (assembled there). *)

(* CORE_REDUCE_GHASH (ported from enc; the CMID_LOHI/HILO canonicalization before AP_TERM is ESSENTIAL --
   without it the abstracted branch1 goal is false).  polyval_reduce_g2 of the karatsuba lo/hi/mid 3-way split
   = ghash_polyval_acc gt A [4 blocks].  ~14s bounded BITBLAST (ABBREV_PMULS keeps it small).  The efficient
   seed (Q30) closer basis -- replaces the brute WORD_BLAST that blew up (27min/7GB). *)
let ABBREV_PMULS : tactic =
  fun (asl,w) ->
    let is_full_pmul t = match strip_comb t with Const("word_pmul",_),[_;_] -> true | _ -> false in
    let pmuls = setify (find_terms is_full_pmul w) in
    let mk i t = ABBREV_TAC (mk_eq(mk_var(Printf.sprintf "pm_%d" i, type_of t), t)) in
    (EVERY (List.mapi mk pmuls)) (asl,w);;
let CMID_HILO = prove
 (`!a:int128. word_xor (word_subword a (64,64)) (word_subword a (0,64)):int64 = karatsuba_mid a`,
  REWRITE_TAC[karatsuba_mid] THEN CONV_TAC WORD_BITWISE_RULE);;
let CMID_LOHI = prove
 (`!a:int128. word_xor (word_subword a (0,64)) (word_subword a (64,64)):int64 = karatsuba_mid a`,
  REWRITE_TAC[karatsuba_mid] THEN CONV_TAC WORD_BITWISE_RULE);;
let JOIN_XOR_256 = prove
 (`!(a1:int128) (b1:int128) (a2:int128) (b2:int128).
     word_xor (word_join a1 b1 :int256) (word_join a2 b2 :int256) =
     word_join (word_xor a1 a2) (word_xor b1 b2) :int256`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;
let JOIN_XOR_128 = prove
 (`!(a1:int64) (b1:int64) (a2:int64) (b2:int64).
     word_xor (word_join a1 b1 :int128) (word_join a2 b2 :int128) =
     word_join (word_xor a1 a2) (word_xor b1 b2) :int128`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* CORE_REDUCE_GHASH (ported from proven enc-256-swp; CMID_LOHI/HILO before AP_TERM is ESSENTIAL). ~14s. *)
let CORE_REDUCE_GHASH = prove
 (`polyval_reduce_g2
     (word_xor (word_pmul (word_subword (cbb3:int128) (0,64):int64) (word_subword (h_power (gt:int128) 0) (0,64):int64))
     (word_xor (word_pmul (word_subword (cbb2:int128) (0,64):int64) (word_subword (h_power gt 1) (0,64):int64))
     (word_xor (word_pmul (word_subword (cbb1:int128) (0,64):int64) (word_subword (h_power gt 2) (0,64):int64))
     (word_pmul (word_subword (word_xor (A:int128) cbb0) (0,64):int64) (word_subword (h_power gt 3) (0,64):int64)))))
     (word_xor (word_pmul (word_subword cbb3 (64,64):int64) (word_subword (h_power gt 0) (64,64):int64))
     (word_xor (word_pmul (word_subword cbb2 (64,64):int64) (word_subword (h_power gt 1) (64,64):int64))
     (word_xor (word_pmul (word_subword cbb1 (64,64):int64) (word_subword (h_power gt 2) (64,64):int64))
     (word_pmul (word_subword (word_xor A cbb0) (64,64):int64) (word_subword (h_power gt 3) (64,64):int64)))))
     (word_xor (word_pmul (karatsuba_mid cbb3) (karatsuba_mid (h_power gt 0)))
     (word_xor (word_pmul (karatsuba_mid cbb2) (karatsuba_mid (h_power gt 1)))
     (word_xor (word_pmul (karatsuba_mid cbb1) (karatsuba_mid (h_power gt 2)))
     (word_pmul (karatsuba_mid (word_xor A cbb0)) (karatsuba_mid (h_power gt 3))))))
   = ghash_polyval_acc gt A [cbb0; cbb1; cbb2; cbb3]`,
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
      (word_xor (word_pmul (cbb3:int128) (h_power gt 0))
      (word_xor (word_pmul (cbb2:int128) (h_power gt 1))
      (word_xor (word_pmul (cbb1:int128) (h_power gt 2))
      (word_pmul (word_xor (A:int128) cbb0) (h_power gt 3)))) :int256)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_G2] THEN
    GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [PMUL_KARATSUBA_JOIN_ALT] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN
    REWRITE_TAC[CMID_LOHI; CMID_HILO] THEN AP_TERM_TAC THEN
    REWRITE_TAC[JOIN_XOR_256; JOIN_XOR_128] THEN
    ABBREV_PMULS THEN POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC BITBLAST_RULE;
    MP_TAC(ISPECL [`gt:int128`; `[cbb1;cbb2;cbb3]:(int128)list`; `A:int128`; `cbb0:int128`]
                  GHASH_POLYVAL_ACC_BATCHED) THEN
    REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE]);;
Printf.printf "MARKER: CORE_REDUCE_GHASH proven\n%!";;

(* 2026-09-19: the exploratory algebraic-toolkit lemmas (PSB/PMUL_LANE_LO/PROP3_LANES/PROP3_GEN) were
   REMOVED -- the final seed proof (SEED_AC_CLOSE_TAC + G2_IS_PROP3, below) does NOT use them, and
   PROP3_LANES' hand-written RHS was a fragile normal-form that failed REFL_TAC under the native
   let_CONV/WORD_SIMPLE_SUBWORD_CONV output ordering.  The seed is closed WITHOUT them. *)

(* ============================================================================
   2026-09-19 SEED CLOSER SOLVED (John's algebraic route: poly-const NEVER bit-blasted).
   The Q30 body-end seed reduces to:  machwj = byteswap128(polyval_reduce_prop3 simple)
   where machwj = the machine's word_join reduce over the 9 lanes vacc/vcb0..3/vh0..3, and
   simple = word_xor(pmul cb3 h0)(xor(pmul cb2 h1)(xor(pmul cb1 h2)(pmul(xor acc cb0) h3))).
   TWO axiom-free lemmas over the 9 free lanes:
     (a) MACHWJ = byteswap128(polyval_reduce_g2 <karatsuba towers>)   -- SEED_AC_CLOSE_TAC
     (b) polyval_reduce_g2 <towers> = polyval_reduce_prop3 simple      -- CORE_REDUCE branch1 (G2_IS_PROP3)
   Chain (a) o AP_TERM byteswap128 (b) = the seed.  KEY: the poly-const word_pmul _ (word 0xC2..)
   is only ever an OPAQUE shared atom -- it is unified across machine/prop3 sides by AC-xor of its
   argument (POLYARG_UNIFY), never expanded, so WORD_BLAST/BITBLAST never sees the carryless mult. *)

(* fast AC-xor prover (linear GF(2), NOT bit-blasting). Closes word_xor-tree = word_xor-tree over atoms. *)
let WORD_XOR_AC_THM = prove
 (`word_xor x y = word_xor y x /\
   word_xor (word_xor x y) z = word_xor x (word_xor y z) /\
   word_xor x (word_xor y z) = word_xor y (word_xor x z)`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* karatsuba-mid fold for a 2-term xor base (the acc-lane mid factor): folds the machine's
   word_xor(word_xor(sw a 0)(sw b 0))(word_xor(sw a 64)(sw b 64)) to karatsuba_mid(word_xor a b). *)
let CMID_XOR2 = prove
 (`word_xor (word_xor (word_subword (a:int128) (0,64)) (word_subword (b:int128) (0,64)))
            (word_xor (word_subword a (64,64)) (word_subword b (64,64))):int64
   = karatsuba_mid (word_xor a b)`,
  REWRITE_TAC[karatsuba_mid; WORD_SUBWORD_XOR] THEN CONV_TAC WORD_BITWISE_RULE);;

(* word_subword of a 64|64 word_join (collapse g2's LO/HI-of-join on the RHS). *)
let SJ_LO = WORD_BLAST `word_subword(word_join (h:int64) (l:int64):int128)(0,64):int64 = l`;;
let SJ_HI = WORD_BLAST `word_subword(word_join (h:int64) (l:int64):int128)(64,64):int64 = h`;;

(* POLYARG_UNIFY_TAC: deterministic one-pass unifier for the poly-const mults.  Finds poly-const
   word_pmul's whose argument word_xor-trees have the SAME leaf-multiset (nested poly-const subwords
   treated as atoms), proves arg-equality by the AC prover, lifts to a word_pmul equality (AP_THM/AP_TERM),
   and PURE_REWRITEs.  Apply TWICE: pass 1 unifies the inner (w1) mult so the outer (w2) args' nested
   subwords coincide; pass 2 unifies w2.  After both passes the 2 machine poly-const mults are
   syntactically identical to prop3's -> abstract as opaque + BINOP + AC closes with zero blasting. *)
let POLYARG_UNIFY_TAC : tactic = fun (asl,w) ->
  let poly = `word 13979173243358019584:int64` in
  let is_pc t = match strip_comb t with Const("word_pmul",_),[_;b]->b=poly|_->false in
  let rec flatten_xor t = match t with
    | Comb(Comb(Const("word_xor",_),a),b) -> flatten_xor a @ flatten_xor b | _ -> [t] in
  let key t = sort (<=) (map string_of_term (flatten_xor (el 0 (snd(strip_comb t))))) in
  let pcs = sort (fun a b -> String.length(string_of_term a) <= String.length(string_of_term b))
                 (setify (find_terms is_pc w)) in
  let eqs = ref [] and seen = ref [] in
  List.iter (fun t ->
     let k = key t in
     match (try Some(assoc k !seen) with _ -> None) with
     | Some rep -> if not(aconv t rep) then
         (let arga = el 0 (snd(strip_comb rep)) and argb = el 0 (snd(strip_comb t)) in
          let argeq = prove(mk_eq(argb,arga),
            (fun g -> let is_pcsub s = match s with Comb(Comb(Const("word_subword",_),bd),_)->is_pc bd|_->false in
               let subs = setify(find_terms is_pcsub (mk_eq(argb,arga))) in
               (EVERY(List.mapi (fun i s->ABBREV_TAC(mk_eq(mk_var(Printf.sprintf "Z_%d" i,type_of s),s))) subs)) g)
            THEN POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC(AC WORD_XOR_AC_THM)) in
          eqs := (AP_THM (AP_TERM `word_pmul:int64->int64->int128` argeq) poly) :: !eqs)
     | None -> seen := (k,t) :: !seen) pcs;
  (if !eqs = [] then ALL_TAC else PURE_REWRITE_TAC !eqs) (asl,w);;

(* SEED_AC_CLOSE_TAC: closes  machwj = byteswap128(polyval_reduce_g2 <towers>)  in ~1.2s, no blasting.
   Unfold g2/byteswap, fold both sides to atomic word_xor-of-64x64-lane form (leaves L_i, karatsuba_mid
   kept folded so mid-lanes are single atoms), unify the 2 poly-const mults by AC (POLYARG x2), abstract
   the shared pmuls+subwords as opaque, split the top word_join (BINOP), close each half by AC-xor. *)
let SEED_AC_CLOSE_TAC : tactic =
  REWRITE_TAC[polyval_reduce_g2; byteswap128] THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
  REWRITE_TAC[CMID_HILO; CMID_LOHI; CMID_XOR2] THEN
  (fun (asl,w) ->
     let is_leaf t = match t with
       | Comb(Comb(Const("word_subword",_),b),_) ->
           (match strip_comb b with Const("word_pmul",_),[_;bb] -> bb <> `word 13979173243358019584:int64` | _ -> false)
       | _ -> false in
     let leaves = setify (find_terms is_leaf w) in
     (EVERY (List.mapi (fun i t -> ABBREV_TAC(mk_eq(mk_var(Printf.sprintf "L_%d" i,type_of t),t))) leaves)) (asl,w)) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[CMID_HILO; CMID_LOHI; CMID_XOR2] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_LO; SJ_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[CMID_HILO; CMID_LOHI; CMID_XOR2] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  ASM_REWRITE_TAC[] THEN
  POLYARG_UNIFY_TAC THEN POLYARG_UNIFY_TAC THEN
  (fun (asl,w) ->
     let is_pmul t = match strip_comb t with Const("word_pmul",_),[_;_]->true|_->false in
     let pms = sort (fun a b -> String.length(string_of_term a) <= String.length(string_of_term b))
                    (setify(find_terms is_pmul w)) in
     (EVERY (List.mapi (fun i t -> ABBREV_TAC(mk_eq(mk_var(Printf.sprintf "QC_%d" i,type_of t),t))) pms)) (asl,w)) THEN
  (fun (asl,w) ->
     let is_sub t = match t with Comb(Comb(Const("word_subword",_),_),_)->true|_->false in
     let subs = setify(find_terms is_sub w) in
     (EVERY (List.mapi (fun i t -> ABBREV_TAC(mk_eq(mk_var(Printf.sprintf "T_%d" i,type_of t),t))) subs)) (asl,w)) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BINOP_TAC THEN CONV_TAC(AC WORD_XOR_AC_THM);;
Printf.printf "MARKER: WORD_XOR_AC_THM + CMID_XOR2 + SJ_LO/HI + POLYARG_UNIFY_TAC + SEED_AC_CLOSE_TAC defined\n%!";;

(* ---------------------------------------------------------------------------
   SEED_ABS + SWP_Q30_SEED_FINISH_TAC (the wired-in Q30 seed closer).
   machwj_abs/simple_abs/g2app_free are the abstract seed terms over 9 lanes
   vacc/vcb0..3/vh0..3 (typed dumps in _scratch/dec256_{machwj,simple,g2app}*.tm).
   SEED_ABS : machwj_abs = byteswap128(polyval_reduce_prop3 simple_abs)  -- axiom-free.
   --------------------------------------------------------------------------- *)
let machwj_abs = parse_term(("(word_join:(64)word->(64)word->(128)word)
((word_xor:(64)word->(64)word->(64)word)
 ((word_xor:(64)word->(64)word->(64)word)
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_xor:(64)word->(64)word->(64)word)
         ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word)
         (0,64))
        ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
       ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
      (0,64))
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
      (0,64))
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
      (0,64))
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
     (0,64)))))
    ((word:num->(64)word) 13979173243358019584))
   (64,64))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (0,64))
     ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
    ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
   (0,64))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
    ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
   (0,64))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
    ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
   (0,64))
  ((word_subword:(128)word->num#num->(64)word)
   ((word_pmul:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
   ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
  (0,64))))))
 ((word_xor:(64)word->(64)word->(64)word)
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_xor:(64)word->(64)word->(64)word)
       ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
     ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
    (64,64))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
     ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
    (64,64))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
     ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
    (64,64))
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
    ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
   (64,64)))))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (64,64))
     ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (64,64)))
    ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (64,64)))
   (64,64))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
    ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (64,64)))
   (64,64))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64))
    ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (64,64)))
   (64,64))
  ((word_subword:(128)word->num#num->(64)word)
   ((word_pmul:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
   ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (64,64)))
  (64,64))))))
 ((word_xor:(64)word->(64)word->(64)word)
  ((word_subword:(128)word->num#num->(64)word)
   ((word_pmul:(64)word->(64)word->(128)word)
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (0,64))
     ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (64,64))
    ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (64,64))))
   ((karatsuba_mid:(128)word->(64)word) (vh3:(128)word)))
  (64,64))
 ((word_xor:(64)word->(64)word->(64)word)
  ((word_subword:(128)word->num#num->(64)word)
   ((word_pmul:(64)word->(64)word->(128)word)
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
    ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64)))
   ((karatsuba_mid:(128)word->(64)word) (vh2:(128)word)))
  (64,64))
 ((word_xor:(64)word->(64)word->(64)word)
  ((word_subword:(128)word->num#num->(64)word)
   ((word_pmul:(64)word->(64)word->(128)word)
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
    ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64)))
   ((karatsuba_mid:(128)word->(64)word) (vh1:(128)word)))
  (64,64))
 ((word_subword:(128)word->num#num->(64)word)
  ((word_pmul:(64)word->(64)word->(128)word)
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
   ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64)))
  ((karatsuba_mid:(128)word->(64)word) (vh0:(128)word)))
 (64,64)))))))
((word_xor:(64)word->(64)word->(64)word)
 ((word_subword:(128)word->num#num->(64)word)
  ((word_pmul:(64)word->(64)word->(128)word)
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word)
         ((word_pmul:(64)word->(64)word->(128)word)
          ((word_xor:(64)word->(64)word->(64)word)
           ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word)
           (0,64))
          ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word)
          (0,64)))
         ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
        (0,64))
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word)
         ((word_pmul:(64)word->(64)word->(128)word)
          ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word)
          (0,64))
         ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
        (0,64))
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word)
         ((word_pmul:(64)word->(64)word->(128)word)
          ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word)
          (0,64))
         ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
        (0,64))
       ((word_subword:(128)word->num#num->(64)word)
        ((word_pmul:(64)word->(64)word->(128)word)
         ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word)
         (0,64))
        ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
       (0,64)))))
      ((word:num->(64)word) 13979173243358019584))
     (0,64))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
      ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
     (64,64))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
     (64,64))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
     (64,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
     ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
    (64,64))))))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_xor:(64)word->(64)word->(64)word)
         ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word)
         (0,64))
        ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
       ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
      (0,64))
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
      (0,64))
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
      (0,64))
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
     (0,64)))))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word)
        (64,64))
       ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (64,64)))
      ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (64,64)))
     (0,64))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
      ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (64,64)))
     (0,64))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64))
      ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (64,64)))
     (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
     ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (64,64)))
    (0,64))))))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_xor:(64)word->(64)word->(64)word)
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
      ((word_xor:(64)word->(64)word->(64)word)
       ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (64,64))
      ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (64,64))))
     ((karatsuba_mid:(128)word->(64)word) (vh3:(128)word)))
    (0,64))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_xor:(64)word->(64)word->(64)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
      ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64)))
     ((karatsuba_mid:(128)word->(64)word) (vh2:(128)word)))
    (0,64))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_xor:(64)word->(64)word->(64)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64)))
     ((karatsuba_mid:(128)word->(64)word) (vh1:(128)word)))
    (0,64))
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
     ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64)))
    ((karatsuba_mid:(128)word->(64)word) (vh0:(128)word)))
   (0,64)))))))
  ((word:num->(64)word) 13979173243358019584))
 (0,64))
((word_xor:(64)word->(64)word->(64)word)
 ((word_subword:(128)word->num#num->(64)word)
  ((word_pmul:(64)word->(64)word->(128)word)
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (64,64))
   ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (64,64)))
  ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (64,64)))
 (0,64))
((word_xor:(64)word->(64)word->(64)word)
 ((word_subword:(128)word->num#num->(64)word)
  ((word_pmul:(64)word->(64)word->(128)word)
   ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
  ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (64,64)))
 (0,64))
((word_xor:(64)word->(64)word->(64)word)
 ((word_subword:(128)word->num#num->(64)word)
  ((word_pmul:(64)word->(64)word->(128)word)
   ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64))
  ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (64,64)))
 (0,64))
((word_subword:(128)word->num#num->(64)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
 ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (64,64)))
(0,64)))))))
((word_xor:(64)word->(64)word->(64)word)
 ((word_xor:(64)word->(64)word->(64)word)
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_xor:(64)word->(64)word->(64)word)
         ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word)
         (0,64))
        ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
       ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
      (0,64))
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
      (0,64))
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
      (0,64))
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
     (0,64)))))
    ((word:num->(64)word) 13979173243358019584))
   (0,64))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (0,64))
     ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
    ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
   (64,64))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
    ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
   (64,64))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
    ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
   (64,64))
  ((word_subword:(128)word->num#num->(64)word)
   ((word_pmul:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
   ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
  (64,64))))))
 ((word_xor:(64)word->(64)word->(64)word)
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_xor:(64)word->(64)word->(64)word)
       ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
     ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
    (0,64))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
     ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
    (0,64))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
     ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
    (0,64))
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
    ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
   (0,64)))))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (64,64))
     ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (64,64)))
    ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (64,64)))
   (0,64))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
    ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (64,64)))
   (0,64))
  ((word_xor:(64)word->(64)word->(64)word)
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64))
    ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (64,64)))
   (0,64))
  ((word_subword:(128)word->num#num->(64)word)
   ((word_pmul:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
   ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (64,64)))
  (0,64))))))
 ((word_xor:(64)word->(64)word->(64)word)
  ((word_subword:(128)word->num#num->(64)word)
   ((word_pmul:(64)word->(64)word->(128)word)
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (0,64))
     ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (64,64))
    ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (64,64))))
   ((karatsuba_mid:(128)word->(64)word) (vh3:(128)word)))
  (0,64))
 ((word_xor:(64)word->(64)word->(64)word)
  ((word_subword:(128)word->num#num->(64)word)
   ((word_pmul:(64)word->(64)word->(128)word)
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
    ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64)))
   ((karatsuba_mid:(128)word->(64)word) (vh2:(128)word)))
  (0,64))
 ((word_xor:(64)word->(64)word->(64)word)
  ((word_subword:(128)word->num#num->(64)word)
   ((word_pmul:(64)word->(64)word->(128)word)
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
    ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64)))
   ((karatsuba_mid:(128)word->(64)word) (vh1:(128)word)))
  (0,64))
 ((word_subword:(128)word->num#num->(64)word)
  ((word_pmul:(64)word->(64)word->(128)word)
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
   ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64)))
  ((karatsuba_mid:(128)word->(64)word) (vh0:(128)word)))
 (0,64)))))))
((word_xor:(64)word->(64)word->(64)word)
 ((word_subword:(128)word->num#num->(64)word)
  ((word_pmul:(64)word->(64)word->(128)word)
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word)
         ((word_pmul:(64)word->(64)word->(128)word)
          ((word_xor:(64)word->(64)word->(64)word)
           ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word)
           (0,64))
          ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word)
          (0,64)))
         ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
        (0,64))
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word)
         ((word_pmul:(64)word->(64)word->(128)word)
          ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word)
          (0,64))
         ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
        (0,64))
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word)
         ((word_pmul:(64)word->(64)word->(128)word)
          ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word)
          (0,64))
         ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
        (0,64))
       ((word_subword:(128)word->num#num->(64)word)
        ((word_pmul:(64)word->(64)word->(128)word)
         ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word)
         (0,64))
        ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
       (0,64)))))
      ((word:num->(64)word) 13979173243358019584))
     (0,64))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
      ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
     (64,64))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
     (64,64))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
     (64,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
     ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
    (64,64))))))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_xor:(64)word->(64)word->(64)word)
         ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word)
         (0,64))
        ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
       ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64)))
      (0,64))
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
      (0,64))
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_pmul:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
      (0,64))
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
     (0,64)))))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word)
        (64,64))
       ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (64,64)))
      ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (64,64)))
     (0,64))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
      ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (64,64)))
     (0,64))
    ((word_xor:(64)word->(64)word->(64)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_pmul:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64))
      ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (64,64)))
     (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
     ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (64,64)))
    (0,64))))))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_xor:(64)word->(64)word->(64)word)
       ((word_xor:(64)word->(64)word->(64)word)
        ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (0,64))
       ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (0,64)))
      ((word_xor:(64)word->(64)word->(64)word)
       ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (64,64))
      ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (64,64))))
     ((karatsuba_mid:(128)word->(64)word) (vh3:(128)word)))
    (0,64))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_xor:(64)word->(64)word->(64)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
      ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64)))
     ((karatsuba_mid:(128)word->(64)word) (vh2:(128)word)))
    (0,64))
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_pmul:(64)word->(64)word->(128)word)
      ((word_xor:(64)word->(64)word->(64)word)
       ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
      ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64)))
     ((karatsuba_mid:(128)word->(64)word) (vh1:(128)word)))
    (0,64))
   ((word_subword:(128)word->num#num->(64)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_xor:(64)word->(64)word->(64)word)
      ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
     ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64)))
    ((karatsuba_mid:(128)word->(64)word) (vh0:(128)word)))
   (0,64)))))))
  ((word:num->(64)word) 13979173243358019584))
 (64,64))
((word_xor:(64)word->(64)word->(64)word)
 ((word_subword:(128)word->num#num->(64)word)
  ((word_pmul:(64)word->(64)word->(128)word)
   ((word_xor:(64)word->(64)word->(64)word)
    ((word_subword:(128)word->num#num->(64)word) (vacc:(128)word) (64,64))
   ((word_subword:(128)word->num#num->(64)word) (vcb0:(128)word) (64,64)))
  ((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (64,64)))
 (64,64))
((word_xor:(64)word->(64)word->(64)word)
 ((word_subword:(128)word->num#num->(64)word)
  ((word_pmul:(64)word->(64)word->(128)word)
   ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
  ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (64,64)))
 (64,64))
((word_xor:(64)word->(64)word->(64)word)
 ((word_subword:(128)word->num#num->(64)word)
  ((word_pmul:(64)word->(64)word->(128)word)
   ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64))
  ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (64,64)))
 (64,64))
((word_subword:(128)word->num#num->(64)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
 ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (64,64)))
(64,64)))))))"));;
let simple_abs = parse_term(("(word_xor:(256)word->(256)word->(256)word)
((word_pmul:(128)word->(128)word->(256)word) (vcb3:(128)word)
(vh0:(128)word))
((word_xor:(256)word->(256)word->(256)word)
 ((word_pmul:(128)word->(128)word->(256)word) (vcb2:(128)word)
 (vh1:(128)word))
((word_xor:(256)word->(256)word->(256)word)
 ((word_pmul:(128)word->(128)word->(256)word) (vcb1:(128)word)
 (vh2:(128)word))
((word_pmul:(128)word->(128)word->(256)word)
 ((word_xor:(128)word->(128)word->(128)word) (vacc:(128)word)
 (vcb0:(128)word))
(vh3:(128)word))))"));;
let g2app_free = parse_term(("(polyval_reduce_g2:(128)word->(128)word->(128)word->(128)word)
((word_xor:(128)word->(128)word->(128)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (0,64))
 ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (0,64)))
((word_xor:(128)word->(128)word->(128)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (0,64))
 ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (0,64)))
((word_xor:(128)word->(128)word->(128)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (0,64))
 ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (0,64)))
((word_pmul:(64)word->(64)word->(128)word)
 ((word_subword:(128)word->num#num->(64)word)
  ((word_xor:(128)word->(128)word->(128)word) (vacc:(128)word)
  (vcb0:(128)word))
 (0,64))
((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (0,64))))))
((word_xor:(128)word->(128)word->(128)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((word_subword:(128)word->num#num->(64)word) (vcb3:(128)word) (64,64))
 ((word_subword:(128)word->num#num->(64)word) (vh0:(128)word) (64,64)))
((word_xor:(128)word->(128)word->(128)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((word_subword:(128)word->num#num->(64)word) (vcb2:(128)word) (64,64))
 ((word_subword:(128)word->num#num->(64)word) (vh1:(128)word) (64,64)))
((word_xor:(128)word->(128)word->(128)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((word_subword:(128)word->num#num->(64)word) (vcb1:(128)word) (64,64))
 ((word_subword:(128)word->num#num->(64)word) (vh2:(128)word) (64,64)))
((word_pmul:(64)word->(64)word->(128)word)
 ((word_subword:(128)word->num#num->(64)word)
  ((word_xor:(128)word->(128)word->(128)word) (vacc:(128)word)
  (vcb0:(128)word))
 (64,64))
((word_subword:(128)word->num#num->(64)word) (vh3:(128)word) (64,64))))))
((word_xor:(128)word->(128)word->(128)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((karatsuba_mid:(128)word->(64)word) (vcb3:(128)word))
 ((karatsuba_mid:(128)word->(64)word) (vh0:(128)word)))
((word_xor:(128)word->(128)word->(128)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((karatsuba_mid:(128)word->(64)word) (vcb2:(128)word))
 ((karatsuba_mid:(128)word->(64)word) (vh1:(128)word)))
((word_xor:(128)word->(128)word->(128)word)
 ((word_pmul:(64)word->(64)word->(128)word)
  ((karatsuba_mid:(128)word->(64)word) (vcb1:(128)word))
 ((karatsuba_mid:(128)word->(64)word) (vh2:(128)word)))
((word_pmul:(64)word->(64)word->(128)word)
 ((karatsuba_mid:(128)word->(64)word)
 ((word_xor:(128)word->(128)word->(128)word) (vacc:(128)word)
 (vcb0:(128)word)))
((karatsuba_mid:(128)word->(64)word) (vh3:(128)word))))))"));;

(* (a) machwj_abs = byteswap128(polyval_reduce_g2 <towers>) -- SEED_AC_CLOSE_TAC, ~1.2s, no blasting. *)
let MACHWJ_IS_BSW_G2 = prove
 (mk_eq(machwj_abs, mk_comb(`byteswap128`, g2app_free)), SEED_AC_CLOSE_TAC);;
(* (b) polyval_reduce_g2 <towers> = polyval_reduce_prop3 simple_abs -- CORE_REDUCE branch1, ~14s. *)
let G2_IS_PROP3 = prove
 (mk_eq(g2app_free, mk_comb(`polyval_reduce_prop3`, simple_abs)),
  REWRITE_TAC[POLYVAL_REDUCE_G2] THEN
  GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [PMUL_KARATSUBA_JOIN_ALT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[CMID_LOHI; CMID_HILO] THEN AP_TERM_TAC THEN
  REWRITE_TAC[JOIN_XOR_256; JOIN_XOR_128] THEN
  ABBREV_PMULS THEN POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC BITBLAST_RULE);;
let SEED_ABS = TRANS MACHWJ_IS_BSW_G2 (AP_TERM `byteswap128` G2_IS_PROP3);;
Printf.printf "MARKER: SEED_ABS proven (machwj = byteswap128(prop3 simple), axiom-free)\n%!";;

(* SWP_Q30_SEED_FINISH_TAC: closes the body-end Q30 goal once it is in the form
     machwj[real lanes] = word_join (word_subword ACC (0,64)) (word_subword ACC (64,64))
   with ACC = nist_ghash..(4*(i+1)).  term_match recovers the 9 lane instantiations from the LHS,
   INST SEED_ABS -> machwj = byteswap128(prop3 simple[lanes]); BRANCH2 folds prop3 simple -> nist_ghash..4(i+1);
   byteswap128 def matches the RHS half-swap.  Instant (no blasting -- SEED_ABS did the work). *)
let SWP_Q30_SEED_FINISH_TAC : tactic = fun (asl,w) ->
  let (_,ilist,_) = term_match [] machwj_abs (lhs w) in
  let seed_i = INST ilist SEED_ABS in
  let br2 = REWRITE_RULE[ARITH_RULE `4*i+4 = 4*(i+1)`] SWP_GHASH_BRANCH2_256 in
  let seed_bsw = REWRITE_RULE[br2] seed_i in
  (ONCE_REWRITE_TAC[seed_bsw] THEN REWRITE_TAC[byteswap128]) (asl,w);;
Printf.printf "MARKER: SWP_Q30_SEED_FINISH_TAC defined (seed closer wired)\n%!";;

(* X13 counter-lane closer: the running counter X13 = word_zx(word(4i+2)) advances by +4 each body
   (0x274 add w13,w13,#4), so the body-end goal is
     word_zx (word_add (word_zx (word_zx (word (4*i+2)))) (word 4)) = word_zx (word (4*(i+1)+2)).
   ZXRT32 folds the inner int32->int64->int32 round-trip, then AP_TERM + WORD_RULE on the +4 arith. *)
let ZXRT32 = WORD_BLAST `word_zx(word_zx (m:int32):int64):int32 = m`;;
let CTR_LANE_dec : tactic =
  REWRITE_TAC[ZXRT32] THEN TRY(AP_TERM_TAC THEN CONV_TAC WORD_RULE) THEN
  TRY(CONV_TAC WORD_RULE);;
Printf.printf "MARKER: ZXRT32 + CTR_LANE_dec defined\n%!";;

(* mem2 staged-block fact: rev8(ctr_block nonce a) and rev8(ctr_block nonce b) share the SAME low-96 bits
   (the nonce part); only the high-32 (+12 counter word) differs.  Validates the 3-way merge: the body's
   counter-word store to sp+OFF+12 changes only the +12 lane; the nonce lanes come unchanged from the s0
   baseline read(bytes128 sp+OFF)s0 = rev8(ctr_block 4i+M).  Building block for SP_SLOT_dec. *)
let CTR_DIFFERS_ONLY_CTR = prove
 (`word_subword (word_reversefields 8 (ctr_block nonce a):int128) (0,96):(96)word =
   word_subword (word_reversefields 8 (ctr_block nonce b):int128) (0,96):(96)word`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;
Printf.printf "MARKER: CTR_DIFFERS_ONLY_CTR defined\n%!";;

(* THE mem2 3-way-merge reassembly (the SP_SLOT algebraic core).  After rev8, the counter word lives in the
   TOP 32 bits [96,128); the low 96 bits are the (counter-independent) nonce.  When the body overwrites the
   +12 counter-word lane (bytes32 at sp+OFF+12) with the new counter word word_zx(word_bytereverse(word b)),
   the resulting block = word_join <that counter word> <baseline's low-96 nonce> = rev8(ctr_block nonce b).
   So the staged-block closer, after resolving read(bytes128 sp+OFF)s193 via read-over-write to
   (counter-word ++ baseline-low-96), folds to rev8(ctr_block b) by MEM2_REASSEMBLE (a = old block index in the
   surviving s0 baseline, b = new index).  Read-over-write recipe (validated): split bytes128 -> bytes64 ->
   bytes32 (READ_MEMORY_BYTESIZED_SPLIT el 1 then el 2, NORMALIZE between) then ONCE_DEPTH COMPONENT_READ_OVER_WRITE_CONV
   resolves the +12 lane to the store value and the other lanes (disjoint) to the baseline reads. *)
let MEM2_REASSEMBLE = prove
 (`word_join (word_zx (word_bytereverse (word b:int32)):int32)
             (word_subword (word_reversefields 8 (ctr_block (nonce:(96)word) a):int128) (0,96):(96)word)
    :int128
   = word_reversefields 8 (ctr_block nonce b)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;
Printf.printf "MARKER: MEM2_REASSEMBLE defined (SP_SLOT algebraic core)\n%!";;

(* ============================================================================
   2026-09-20: enc-mem2 staged-block setup lemmas (from aes_gcm_enc_kernel_x4_scalar_iv_mem2.ml -- the EXACT
   str-w mem2 precedent).  SLOT_LO/SLOT_MID rewrite the staged-slot nonce subwords (of the reversed ctr_block 2)
   back to the resident IV halves ivlo / subword ivhi, so ASM_REWRITE closes them against the split store facts.
   CTR_BLOCK_BUILD_INSERT_PLAIN folds the AES-embedded (plain) counter-slot form to rev8(ctr_block cval).
   Cipher-independent (pure ctr_block/counter algebra) -> port verbatim from enc-mem2. *)
let SLOT_LO = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce 2)
   ==> word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 = ivlo`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;
let SLOT_MID = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce 2)
   ==> word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 =
       word_subword (ivhi:int64) (0,32):int32`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;
let CTR_BLOCK_BUILD_INSERT_PLAIN = prove
 (`word_join
     (word_join (word_bytereverse (word cval:int32):int32)
                (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;
Printf.printf "MARKER: SLOT_LO/SLOT_MID/CTR_BLOCK_BUILD_INSERT_PLAIN defined (enc-mem2 staged-block setup)\n%!";;

(* ============================================================================
   2026-09-20: DESIGN-A staged-block closer -- the WORKING mechanism (no invariant surgery, FILL stays valid).
   Reconstruct each staged counter block DURING STEPPING at its counter-store state, from nonce lanes primed at
   s0 (constant, counter-independent) + the body's +12 counter-word str.  See gcm-dec256-swp-recon 2026-09-20.
   These four lemmas are cipher-independent (pure component/ctr_block algebra). ============================== *)

(* Lane-extraction: a bytes64/bytes32 read equals the corresponding subword of the enclosing bytes128 read.
   (Pure component algebra: the byte-sized split + WORD_BLAST on the word_join reassembly.) *)
let B64_OF_B128_LO = prove
 (`read (memory :> bytes64 x) s :int64 = word_subword (read (memory :> bytes128 x) s :int128) (0,64)`,
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN CONV_TAC WORD_BLAST);;
let B32_OF_B128_MID = prove
 (`read (memory :> bytes32 (word_add x (word 8))) s :int32 =
     word_subword (read (memory :> bytes128 x) s :int128) (64,32)`,
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
              el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  CONV_TAC WORD_BLAST);;

(* Counter-independence of the nonce lanes: the low-64 and mid-32 subwords of rev8(ctr_block nonce c) do NOT
   depend on the counter c (only the top-32 counter lane does).  Lets us canonicalize any staged block's nonce
   lanes to the resident ctr_block-2 form (== the ivec) so they are CONSTANT across iterations. *)
let SUBW_LO_CI = prove
 (`word_subword (word_reversefields 8 (ctr_block nonce a):int128) (0,64):int64 =
   word_subword (word_reversefields 8 (ctr_block nonce b):int128) (0,64):int64`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;
let SUBW_MID_CI = prove
 (`word_subword (word_reversefields 8 (ctr_block nonce a):int128) (64,32):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce b):int128) (64,32):int32`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* THE dec-256 3-way-join reload fold.  DIFFERS from enc-mem2's CTR_BLOCK_BUILD_INSERT_PLAIN by an EXTRA int64
   word_zx in the counter chain (dec-256's `str w` reversal is 64-bit-wide, so after CTR_ZX_NORM the counter
   cell is word_zx(word_zx(word_bytereverse(word_zx(word_zx(word cval:int32):int64):int64):int64):int32):int32),
   NOT the int32-bytereverse of enc-mem2).  General in cval.  Proven by ctr_block + BITBLAST (~0.4s). *)
let CTR_BLOCK_BUILD_INSERT_DEC = prove
 (`word_join
     (word_join
        (word_zx (word_zx (word_bytereverse
           (word_zx (word_zx (word cval:int32):int32):int32):int32):int32):int32)
        (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;
Printf.printf "MARKER: B64_OF_B128_LO/B32_OF_B128_MID/SUBW_*_CI/CTR_BLOCK_BUILD_INSERT_DEC defined (Design-A staged-ctr closer)\n%!";;

(* ============================================================================
   2026-09-20 APPROACH E: the NATIVE-SAFE staged-block reconstruction (ivlo/ivhi VARIABLE lanes).
   The Design-A persistent lanes (RHS = word_subword(rev8(ctr_block 2))(..), a compound ctr_block memory read at
   an OLD state) crash native ARM_STEP_TAC (mk_comb).  enc-mem2 avoids this by ABBREVing the ivec halves as
   VARIABLES ivlo/ivhi and stating lanes as `= ivlo` / `= word_subword ivhi (0,32)` (variable RHS -> ARM_STEP-safe).
   CTR_BLOCK_BUILD_V_DEC: the ivlo/ivhi-variable 3-way-join fold (given the join relation).  Its counter-cell
   width profile (word_zx over int64 intermediates) is subtle and PRINTS identical to a wrong int32 form but
   term_match-FAILS -- so we rebuild it from a fully-typed .tm dump (dec256_ctr_v_dec.tm), NOT hand-typed. *)
let CTR_BLOCK_BUILD_V_DEC =
  let tm = parse_term ("(word_join:(64)word->(64)word->(128)word) (ivhi:(64)word) (ivlo:(64)word) =
(word_reversefields:num->(128)word->(128)word) 8
((ctr_block:(96)word->num->(128)word) (nonce:(96)word) 2)
==> (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_zx:(64)word->(32)word)
     ((word_zx:(32)word->(64)word)
     ((word_bytereverse:(32)word->(32)word)
     ((word_zx:(64)word->(32)word)
     ((word_zx:(32)word->(64)word) ((word:num->(32)word) (cval:num)))))))
    ((word_subword:(64)word->num#num->(32)word) (ivhi:(64)word) (0,32)))
    (ivlo:(64)word) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (cval:num))") in
  prove(tm,
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN
    REWRITE_TAC[ctr_block] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    CONV_TAC WORD_BLAST);;
Printf.printf "MARKER: CTR_BLOCK_BUILD_V_DEC defined (Approach-E ivlo/ivhi fold, from .tm dump)\n%!";;
(* ============================================================================
   dec-256 SWP body/fill SHARED closers (factored from DEVEL_dec256_bodyleg.ml lines 208-627).
   Reused verbatim by both the BODYLEG (symbolic i) and the FILL leg (i=0).
   Requires (from the loader): splitL, splitL2, swpS256_inv_dec, the dec256_closers.ml theorems
   (SWP_SUB_LEMMA_DEC, aes12c, aes5c, XOR_AES256_CIPHER_RECONSTRUCT_DEC, KEYSTREAM_FOLD256, etc.),
   and 'contains'.  Defines: rk15, INFOLD_dec, GHASH_PARTIAL_CLOSE_dec, SWP_Q30_SEED_TAC,
   OUT_BLOCK_CLOSE_dec, OUT_STORE_dec, SP_SLOT_dec, close_pc_cond, close_frame_dec, OUT_FRAME_dec,
   IVEC_RECOMB_dec, CTRREG_dec, CLOSE_DEC256.  Parse-clean, PROVEN axiom-free in the bodyleg native run.
   ============================================================================ *)

(* ==================== closers ==================== *)
let rk15 = `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
             EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk`;;

(* in_p addr normalizations (64*(i+1)+K -> 16*(4*(i+1)+M)); (i+1) form. *)
let inp_addr_norms_dec =
  (* bare K=0 case: goal address is `word (64*(i+1))` with no `+0` *)
  (WORD_RULE `word_add (in_p:int64) (word (64*(i+1))):int64 = word_add in_p (word (16*(4*(i+1))))`) ::
  List.map (fun (kk,m) ->
    WORD_RULE (subst [mk_small_numeral kk, `K:num`; mk_small_numeral m, `M:num`]
                 `word_add (in_p:int64) (word (64*(i+1)+K)):int64 = word_add in_p (word (16*(4*(i+1)+M)))`))
  [(0,0);(16,1);(32,2);(48,3);(64,4);(80,5);(96,6);(112,7)];;

(* read(in_p+...)=inblock: normalize addr then in-forall. *)
let IN_READ_CLOSE_dec : tactic =
  REWRITE_TAC inp_addr_norms_dec THEN
  (fun (asl,w) ->
     FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                  && free_in (rand(lhs w)) (concl fa) with _->false)
                          then MATCH_MP_TAC fa else NO_TAC) (asl,w)) THEN ASM_ARITH_TAC;;

(* in-read folder that dewraps+normalizes inside a partial tower. *)
let is_inp_bytes128_read t =
  try let rd,st = dest_comb t in
      let rc,comp = dest_comb rd in
      fst(dest_const rc) = "read" && is_var st &&
      free_in `in_p:int64` comp &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "bytes128")) comp
  with _ -> false;;
let sixteen_blk rd =
  let mul16 = find_term (fun t ->
      try let op,args = strip_comb t in
          fst(dest_const op) = "*" && length args = 2 &&
          is_numeral (hd args) && dest_numeral (hd args) = num 16
      with _ -> false) rd in
  rand mul16;;
(* state of an in_p bytes128 read term (the s-var name), or "" *)
let inpread_state rd = try (match dest_comb rd with (_,Var(nm,_)) -> nm | _ -> "") with _ -> "";;
(* state that an input-frame forall's read is about (its bound-body read state var), or "" *)
let inpforall_state c = try
   (match snd(strip_forall c) with
    | Comb(Comb(Const("==>",_),_),bod) ->
       (match find_terms (fun t -> match t with
          Comb(Comb(Const("read",_),cmp),Var(nm,_)) when free_in `in_p:int64` cmp -> true | _ -> false) bod with
        | (Comb(Comb(_,_),Var(nm,_)))::_ -> nm | _ -> "")
    | _ -> "") with _ -> "";;
(* fold an in_p read to inblock, picking the input-frame forall AT THE READ'S OWN STATE (the out-store's embedded
   in_p read is at an OLD state sK; gkeepN keeps in_p foralls at all states, so the sK forall is present). *)
let INFOLD_dec : tactic =
  REWRITE_TAC inp_addr_norms_dec THEN
  (fun (asl,w) ->
    let inreads = setify(find_terms is_inp_bytes128_read w) in
    if inreads = [] then ALL_TAC (asl,w)
    else (EVERY (map (fun rd ->
       let blk = sixteen_blk rd in
       let st = inpread_state rd in
       (* TRY to fold rd -> inblock blk; NEVER throw (if no usable forall, leave rd unfolded so the caller can
          decide -- avoids regressing the whole closer to a raw-goal throw). *)
       TRY(SUBGOAL_THEN (mk_eq(rd, mk_comb(`inblock:num->int128`, blk))) ASSUME_TAC THENL
        [(* prefer the input-frame forall at the SAME state as the read; else any in_p forall *)
         (FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                       && inpforall_state (concl fa) = st with _->false)
                                  then MATCH_MP_TAC fa else NO_TAC)
          ORELSE FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa) with _->false)
                                         then MATCH_MP_TAC fa else NO_TAC))
         THEN
         (* the block-index bound (blk < nblocks): ASM_ARITH alone can't cross the nblocks DIV 4 = loop_count
            relation, so first establish 4*i+7 < nblocks (covers all body-leg blocks incl one-ahead 4(i+1)+2),
            from the 3 root invariant facts, then ASM_ARITH. *)
         (SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
           [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 2` THEN
            UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]
          ORELSE ALL_TAC) THEN
         ASM_ARITH_TAC; ALL_TAC]))
      inreads)) (asl,w));;

(* GHASH partial (pmul/xor over inblock x h-power lanes, RHS is my partial form, NO nist_ghash).
   2026-09-18: after the Q10/Q11 invariant fix all 5 partials (Q5/Q6/Q9/Q10/Q11) are TRUE.  Q5/Q9/Q10/Q11 close
   by REFL after the in-fold + reassemble.  Q6 (compound: karatsuba_mid mid-lane + block-2 word_subword(word_join
   ..)(64,128) structure) needs the extra SWP_SUBWORD_JOIN_MID + WORD_SIMPLE_SUBWORD + WORD_BLAST tail to fold the
   word_subword(word_join(km h1)(km h0))(k,64) -> km h_ and close the word_xor congruence. *)
let GHASH_PARTIAL_CLOSE_dec : tactic =
  INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE; GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  (TRY REFL_TAC THEN
   TRY (REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        TRY(CONV_TAC WORD_BLAST)));;

(* GHASH seed-core (Q30 half-swap accumulator = half-swap(nist_ghash..4(i+1))). aes256. *)
let SWP_REDUCE_RECON_256 : tactic =
  MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes256_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * i)))`;
      `cipherblock_0 = nist_input_block inblock (4 * i)`; `cipherblock_1 = nist_input_block inblock (4 * i + 1)`;
      `cipherblock_2 = nist_input_block inblock (4 * i + 2)`; `cipherblock_3 = nist_input_block inblock (4 * i + 3)`;
      `h0 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`; `h1 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 2`; `h3 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3 (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
      (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
      (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
      (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
    REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM] `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC ;
    MAP_EVERY EXPAND_TAC ["sofar";"cipherblock_0";"cipherblock_1";"cipherblock_2";"cipherblock_3";"h0";"h1";"h2";"h3"] THEN
    REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    ACCEPT_TAC SWP_GHASH_BRANCH2_256];;

let SWP_SEED_CORE_256 : tactic =
  REWRITE_TAC[SWP_JOIN_IS_BSW] THEN REWRITE_TAC[xor_rcancel] THEN
  REWRITE_TAC [byteswap128; SWP_SUBWORD_JOIN_MID] THEN
  MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  SWP_REDUCE_RECON_256;;

(* Q30 seed conjunct.  2026-09-18: with the Q10/Q11 invariant fix, the Q30 goal is now TRUE (machine reduce =
   half-swap of nist_ghash..(4(i+1))).  DISASM: Q30 = ext(v5,#8) = half-swap of the settled reduce v5.  After
   SWP_JOIN_IS_BSW/xor_rcancel/byteswap128/SWP_SUBWORD_JOIN_MID the goal is
     word_join (word_subword MACHINE_lo (0,64)) (word_subword MACHINE_hi (64,64))
       = word_join (word_subword ACC (0,64)) (word_subword ACC (64,64))     [ACC = nist_ghash..(4(i+1))]
   where MACHINE_lo != MACHINE_hi (the two 64-bit lanes come from DIFFERENT machine reduce sub-trees) -- so the
   dec-128 single-x `MATCH_MP_TAC(BITBLAST_RULE join(sub x)(sub x)=join(sub y)(sub y))` is UNSOUND here.  Use
   BINOP_TAC to split into the two ALIGNED per-half identities (sub MACHINE_lo 0 = sub ACC 0) & (sub MACHINE_hi 64
   = sub ACC 64); each is a bounded GHASH-reduce word-identity closed by the recon (fold ACC via
   GSYM SWP_GHASH_BRANCH2_256 -> prop3 packing, RECONSTRUCT, then a native BITBLAST ~117s -- exceeds the 600s MCP
   cap, native-only).  branch2 (packing=nist_ghash) is subsumed by the GSYM-BRANCH2 fold. *)
(* 2026-09-19 SOLVED (John's algebraic route, no poly-const blast).  The seed goal after the prefix is
     machwj[real lanes] = word_join (word_subword ACC (0,64)) (word_subword ACC (64,64))   [ACC=nist_ghash..4(i+1)]
   PREFIX: SWP_SUBWORD_JOIN_MID collapses LHS word_subword(word_join BIG)(64,128) -> word_join(sw.. 0)(sw.. 64)
     = machwj; DEC_GHASH_NORM_TAC folds the inblock byte-lanes -> nist_input_block; ASM_REWRITE folds the block-0
     Q14 read (read Q14 sK = inblock(4i), in asl) then GSYM nist_input_block makes it nist_input_block(4i); now
     LHS is exactly machwj over the real lanes.  FINISH: SWP_Q30_SEED_FINISH_TAC (in dec256_closers.ml) term_matches
     machwj_abs -> the 9 lane insts, INSTs the proven SEED_ABS (= byteswap128(prop3 simple), axiom-free, NO
     poly-const blast), folds prop3 simple -> nist_ghash..4(i+1) via SWP_GHASH_BRANCH2_256, byteswap128 def closes.
   The whole seed is now ~instant (SEED_ABS built once at load; ~1.5s+14s).  Invariant Q30 unchanged (confirmed
   correct: half-swap of nist_ghash..4i). *)
let SWP_Q30_SEED_TAC : tactic =
  REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN DEC_GHASH_NORM_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  SWP_Q30_SEED_FINISH_TAC;;

(* AES14P_VIA_* bridges: fold a carried AES partial (aesNc) + remaining rounds -> aes14p. *)
let out_via_lemmas =
  [AES14P_VIA_AES5C; AES14P_VIA_AES12C; AES14P_VIA_AES1C; AES14P_VIA_AES6C; AES14P_VIA_AES7C; AES14P_VIA_AES11C];;
(* per-block out-store keystream fold.  After the read resolves to the machine value
     word_xor inblock_j (word_xor rk14 <tower>) = word_xor (aes_ctr_block j) inblock_j
   <tower> is either a FULL 14-round tower on a resolved rev8(ctr_block(j+2)) [block whose counter block is
   resident] OR built on a carried AES partial aesNc(j+2) [pipelined blocks].  Try both (validated in MCP). *)
(* aes_ctr_block j unfolds to rev8(aes256_cipher(ctr_block(j+2))); normalize the ctr index j+2.
   Cover BOTH the out-frame form (j = 4i+M) AND the one-ahead form (j = 4(i+1)+M). *)
let ctr_idx_norms = [ARITH_RULE `(4*i)+2 = 4*i+2`; ARITH_RULE `(4*i+1)+2 = 4*i+3`;
                     ARITH_RULE `(4*i+2)+2 = 4*i+4`; ARITH_RULE `(4*i+3)+2 = 4*i+5`;
                     ARITH_RULE `(4*(i+1)+0)+2 = 4*(i+1)+2`; ARITH_RULE `(4*(i+1)+1)+2 = 4*(i+1)+3`;
                     ARITH_RULE `(4*(i+1)+2)+2 = 4*(i+1)+4`; ARITH_RULE `(4*(i+1)+3)+2 = 4*(i+1)+5`];;
(* resident-block ctr index bridges: the FULL-tower one-ahead keystream runs on a RESIDENT rev8(ctr_block(4i+K))
   (K=6,7,8,9), while after aes_ctr_block unfold the target ctr index is 4(i+1)+M+2.  Bridge 4i+K = 4(i+1)+M'. *)
let resident_ctr_norms = [ARITH_RULE `4*i+6 = 4*(i+1)+2`; ARITH_RULE `4*i+7 = 4*(i+1)+3`;
                          ARITH_RULE `4*i+8 = 4*(i+1)+4`; ARITH_RULE `4*i+9 = 4*(i+1)+5`];;
let OUT_BLOCK_CLOSE_dec : tactic =
  (* ADD_CLAUSES normalizes 4*i+0 -> 4*i (block-0's target has an explicit +0 that the INFOLD-folded operand lacks). *)
  REWRITE_TAC[ADD_CLAUSES] THEN
  ((REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC] THEN
   REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC ctr_idx_norms THEN
   REWRITE_TAC resident_ctr_norms THEN REFL_TAC)
  ORELSE
  (REWRITE_TAC(map GSYM out_via_lemmas) THEN
   REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC ctr_idx_norms THEN
   (fun (asl,w) ->
      let c = try rand(find_term (fun t -> match t with Comb(Comb(Const("ctr_block",_),_),_) -> true | _ -> false) (rhs w))
              with _ -> `4*i+2` in
      let inb = lhand (lhs w) in
      MP_TAC(SPECL[c; inb] (GENL [`c:num`;`inb:int128`] (MATCH_MP KEYSTREAM_FOLD256 (ASSUME rk15)))) (asl,w)) THEN
   DISCH_TAC THEN POP_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
   CONV_TAC WORD_BITWISE_RULE));;

(* out-store address normalization: the goal's one-ahead address out_p+word(64*(i+1)+32) must match the store
   fact's out_p+word((64*i+64)+32) form (the body's x2 post-increment produced 64*i+64, not 64*(i+1)). *)
let out_addr_norms = [
  WORD_RULE `word_add (out_p:int64) (word (64*(i+1)+32)) = word_add out_p (word ((64*i+64)+32))`];;
(* out-store readback (one-ahead q12 store of block 4(i+1)+2 = 4i+6 at out_p+(64*i+64)+32).
   Normalize the address so ASM resolves the read to the machine value, then the unified per-block keystream fold. *)
let OUT_STORE_dec : tactic =
  REWRITE_TAC out_addr_norms THEN
  (* FIRST resolve the out_p read to the machine value (which embeds an old-state in_p read); ONLY THEN can
     INFOLD see + fold that embedded in_p read.  (Running INFOLD before ASM_REWRITE was the bug: the in_p read
     is invisible until the out read resolves.) *)
  ASM_REWRITE_TAC[] THEN
  INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;

(* staged counter block: goal is either
     word_join (read sp+X+8 sK) (read sp+X sK) = rev8(ctr_block(4(i+1)+M))   [split-form], or
     read (bytes128 sp+X) sK = rev8(ctr_block(4(i+1)+M))                     [whole-form].
   Resolve the sp reads (their values are in asl from stepping), collapse the counter-word tower to
   word_shl(word_zx(word_bytereverse(word cval)))32, then CTR_BLOCK_BUILD_INSERT + mk_cbv folds to
   rev8(ctr_block). ASM_REWRITE brings in the read facts; the ZX/CTR lemmas normalize; mk_cbv-style
   const bridges close. Robustly try REFL/WORD_BLAST after each normalization. *)
(* dec-256 RHS index norms: rev8(ctr_block (4(i+1)+M)) -> rev8(ctr_block (4i+(4+M))) so the counter-word
   base 4i+4 folds cleanly against the stored add-value; the staged blocks are +2..+6. *)
let SP_RHS_NORMS_dec = [
  ARITH_RULE `4*(i+1)+2 = 4*i+6`; ARITH_RULE `4*(i+1)+3 = 4*i+7`;
  ARITH_RULE `4*(i+1)+4 = 4*i+8`; ARITH_RULE `4*(i+1)+5 = 4*i+9`;
  ARITH_RULE `4*(i+1)+6 = 4*i+10`];;
(* counter-word add folds (int32): the body computes add w,w13,#N with w13=word(4i+6) at store time. *)
let SP_LANE_FOLDS_dec = [
  WORD_RULE `word_add (word (4*i+6):int32) (word 1) = word(4*i+7)`;
  WORD_RULE `word_add (word (4*i+6):int32) (word 2) = word(4*i+8)`;
  WORD_RULE `word_add (word (4*i+6):int32) (word 3) = word(4*i+9)`;
  WORD_RULE `word_add (word (4*i+6):int32) (word 4) = word(4*i+10)`];;
(* staged counter block closer.  Two goal shapes:
     split: word_join(read sp+X+8 sK)(read sp+X sK) = rev8(ctr_block(4(i+1)+M))
     whole: read(bytes128 sp+X) sK          = rev8(ctr_block(4(i+1)+M))
   For the split form, MERGE_CTR128_TAC folds the two bytes64 reads back to a bytes128 read (matching the
   stepping's stored value); then ASM_REWRITE brings the stored insert-form in, CTR_ZX_NORM/lane-folds
   normalize the counter word, CTR_BLOCK_BUILD_INSERT folds to rev8(ctr_block).  We try MERGE at each staged
   offset (only the matching one fires; the rest ASM_REWRITE to no-ops).  Robust closers after. *)
(* 2026-09-19 mechanism-correct SP_SLOT_dec (pieces PROVEN: read-over-write split resolution + MEM2_REASSEMBLE).
   goal (split-form): word_join(read b64 sp+OFF+8 s193)(read b64 sp+OFF s193) = rev8(ctr_block(4(i+1)+M))
   or (whole-form): read(bytes128 sp+OFF)sK = rev8(ctr_block(4(i+1)+M)).
   Recipe: (1) if split-form, GSYM-fold to read(bytes128 sp+OFF)s193 (via READ_MEMORY_BYTESIZED_SPLIT el 1);
   (2) fully split bytes128->4 bytes32 (el 1 then el 2) + resolve the +12 lane to the counter-word store and the
   other 3 lanes to the surviving baseline, via ONCE_DEPTH COMPONENT_READ_OVER_WRITE_CONV (repeated to chain
   through the state write-tower); (3) ASM_REWRITE brings the resolved counter-word + baseline lanes; normalize
   the counter word (CTR_ZX_NORM/lane-folds) and fold via CTR_BLOCK_BUILD_INSERT/MEM2_REASSEMBLE to rev8(ctr_block).
   Robust fallbacks after each step. *)
(* 2026-09-20 FAST PATH: with MERGE_CTR128_FOLD wired into the stepper, each staged block is already resident at
   body-end as read(bytes128 sp+off)s193 = rev8(ctr_block (4(i+1)+M)) (the fold produced 4i+M' = 4(i+1)+M and
   read-over-write auto-advanced it to s193).  So the whole-form goal closes by ASM_REWRITE after bridging the
   index arithmetic 4(i+1)+M = 4i+M'.  Try this first; fall back to the old read-over-write recipe otherwise. *)
let SP_SLOT_dec_fast : tactic =
  REWRITE_TAC[ARITH_RULE `4*(i+1)+2 = 4*i+6`; ARITH_RULE `4*(i+1)+3 = 4*i+7`;
              ARITH_RULE `4*(i+1)+4 = 4*i+8`; ARITH_RULE `4*(i+1)+5 = 4*i+9`] THEN
  ASM_REWRITE_TAC[];;
let SP_SLOT_dec : tactic = fun (asl,w) ->
  let splitL = el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)
  and splitL2 = el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT) in
  (* if the goal LHS is word_join(read b64)(read b64), fold it back to read(bytes128 X) *)
  (TRY(fun (a,g) ->
     (match lhs g with
      | Comb(Comb(Const("word_join",_),
          Comb(Comb(Const("read",_),_),st)),_) ->
          let base = (match find_terms (fun t->match t with
             Comb(Comb(Const("word_add",_),v),_)->(try fst(dest_var v)="stackpointer" with _->false)|_->false)
             (rand(rator(lhs g))) with
             | (Comb(Comb(_,_),Comb(_,n)))::_ -> (try dest_small_numeral n with _->160) | _ -> 160) in
          let inst = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
            (ISPECL [`memory`; mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                     mk_comb(`word:num->int64`,mk_small_numeral base)); st] splitL) in
          GEN_REWRITE_TAC LAND_CONV [GSYM inst] (a,g)
      | _ -> ALL_TAC (a,g))) THEN
   (* resolve the bytes128 read through the write chain: split ONCE to 4 bytes32 lanes, then a BOUNDED number
      of read-over-write passes (each peels one write; the chain is deep but the +12 lane resolves to the last
      relevant store and the nonce lanes are disjoint from all body stores -> ASM_REWRITE finishes).
      NB the TOP_DEPTH split is applied ONCE (not in the REPEAT loop) to avoid re-splitting the whole goal. *)
   GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [splitL; splitL2] THEN
   CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
   CONV_TAC(ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
   CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
   REWRITE_TAC SP_LANE_FOLDS_dec THEN REWRITE_TAC SP_RHS_NORMS_dec THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[MEM2_REASSEMBLE; CTR_BLOCK_BUILD_INSERT] THEN
   REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   TRY(CONV_TAC WORD_RULE) THEN TRY REFL_TAC THEN TRY(CONV_TAC WORD_BLAST) THEN
   TRY(REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST)) (asl,w);;

(* counter scalar-lane folds (word_zx/word_add towers).  The X13 running-counter lane
   (word_zx(word_add(word_zx(word_zx(word(4i+2))))(word 4)) = word_zx(word(4(i+1)+2))) closes via
   CTR_LANE_dec (ZXRT32 round-trip + AP_TERM + WORD_RULE); other lanes via the ZX/CTR normal forms. *)
let CTRREG_dec : tactic =
  CTR_LANE_dec ORELSE
  (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
   CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
   TRY REFL_TAC THEN TRY(CONV_TAC WORD_RULE) THEN TRY(AP_TERM_TAC THEN ARITH_TAC));;

(* pointers. *)
let close_ptr_dec : tactic =
  REWRITE_TAC[ARITH_RULE `64*((i+1)+1)=64*(i+1)+64`; ARITH_RULE `64*(i+1) = 64*i+64`; LEFT_ADD_DISTRIB] THEN
  CONV_TAC WORD_RULE;;

(* X1 decrement. *)
let close_x1_dec : tactic =
  ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC];;

(* back-edge PC COND: the cbnz test resolves nonzero for i+1 < loop_count (steady). *)
let close_pc_cond : tactic =
  COND_CASES_TAC THENL [REFL_TAC; ALL_TAC] THEN
  (* the else-branch is contradictory: val(word_sub..)=0 impossible for i+1<loop_count-1... but at
     i=loop_count-2 boundary this is the LAST steady iter. The WHILE composition handles the boundary;
     here (i<loop_count-2) so word_sub(loop_count-(i+1))(1) != 0. *)
  POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(val (word_sub (word (loop_count-(i+1))) (word 1):int64) = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC] THEN REWRITE_TAC[VAL_EQ_0] THEN
    MATCH_MP_TAC(MESON[] `~(x = word 0) ==> ~(x = word 0)`) THEN
    REWRITE_TAC[WORD_EQ_0] THEN MAP_EVERY UNDISCH_TAC [`i < loop_count - 2`; `2 <= loop_count`] THEN ARITH_TAC;
    REFL_TAC];;

(* MAYCHANGE frame. *)
let pth_frame_dec = prove(`R s s' ==> R subsumed R' ==> R' s s'`, REWRITE_TAC[subsumed] THEN MESON_TAC[]);;
let close_frame_dec : tactic =
  fun (asl,w) ->
    let frame_th = try snd(List.find (fun (_,th) -> let c=concl th in
        (try not(is_eq c) && can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c
            && (match c with Comb(Comb(_,a),b) -> is_var a && is_var b | _->false) with _->false)) asl)
      with _ -> failwith "close_frame_dec: no frame asm" in
    (MATCH_MP_TAC(MATCH_MP pth_frame_dec frame_th) THEN
     REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) (asl,w);;

(* out-frame forall (j<4(i+1)): orthogonality preservation. Ported from dec-128 OUT0_TAC. *)
let pth128_dec = prove
   (`!(a:int64) m n. 16 <= val(word_sub (word m) (word n):int64) /\ 16 <= val(word_sub (word n) (word m):int64)
          ==> orthogonal_components (bytes128 (word_add a (word m))) (bytes128 (word_add a (word n)))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[bytes128] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
    REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; NONOVERLAPPING_MODULO_MOD2] THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_OFFSET_SIMPLE_BOTH THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_CASES; DIMINDEX_64]) THEN
    MP_TAC(ISPEC `word m:int64` VAL_BOUND) THEN MP_TAC(ISPEC `word n:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;
let orth_lemma_dec = prove
   (`orthogonal_components c d /\ read c s' = read c s ==> read c (write d y s') = read c s`,
    MESON_TAC[orthogonal_components]);;
let OUT_ORTH_dec : tactic =
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN CONJ_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV;
    MATCH_MP_TAC pth128_dec THEN
    W(fun (asl,w) ->
      let sub1 = rand(rand(fst(dest_conj w))) in
      let mtm = rand(rator sub1) and ntm = rand sub1 in
      let m = rand mtm and n = rand ntm in
      SUBGOAL_THEN (list_mk_conj [mk_binop `(<):num->num->bool` m `2 EXP 64`;
                                  mk_binop `(<):num->num->bool` n `2 EXP 64`])
        STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `2 EXP 64 = 18446744073709551616`] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC];;
let ORTH_STEP_dec : tactic =
  FIRST [ OUT_ORTH_dec; ORTHOGONAL_COMPONENTS_TAC;
          (MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN CONJ_TAC THENL
            [CONV_TAC VALID_COMPONENT_CONV; ORTHOGONAL_COMPONENTS_TAC]) ];;
let rec OUT_ROW_dec g =
  (REFL_TAC ORELSE (MATCH_MP_TAC orth_lemma_dec THEN CONJ_TAC THENL [ORTH_STEP_dec; OUT_ROW_dec])) g;;
let OUT_FRAME_dec : tactic =
  REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
  ASM_REWRITE_TAC[] THEN
  (* split into: forall j<4i (incoming out-frame invariant, ASM) + 4 blocks j=4i+{0,1,2,3}.
     block 4i+2 = frame-carry (incoming one-ahead, ASM); blocks 4i+{0,1,3} = fresh stores (INFOLD-resolve the
     in_p read + the resident counter, then the unified per-block keystream fold).  Each branch: try ASM
     (closes the forall + carry), else the block fold. *)
  REPEAT CONJ_TAC THEN
  (* forall j<4i goal: accept the incoming out-frame invariant forall (ASM_REWRITE can't instantiate a forall).
     concrete-block goals: ASM (frame-carry blk 4i+2) else INFOLD+fold (fresh blks).  ORDER (per OUT_STORE fix):
     ASM_REWRITE to resolve the out read FIRST, THEN INFOLD the now-visible embedded in_p read, THEN OUT_BLOCK. *)
  TRY (FIRST_X_ASSUM (fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) with _->false)
                                then MATCH_ACCEPT_TAC th else NO_TAC)) THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;

(* ivec recombine: after IVEC_SPLIT the ivec baseline is in ivlo/ivhi halves; the body never writes ivec_p, so
   read(bytes128 ivec_p)s193 recombines to word_join ivhi ivlo = rev8(ctr_block 2) (enc-mem2 recipe). *)
let IVEC_RECOMB_dec : tactic =
  GEN_REWRITE_TAC LAND_CONV [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  ASM_REWRITE_TAC[];;

(* master dispatcher (shape+content routed). *)
let CLOSE_DEC256 : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
    let deep_ghash = try has "nist_ghash" w with _ -> false in
    if has_mc w then close_frame_dec (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then OUT_FRAME_dec (asl,w)
    else if not(is_eq w) then (ASM_REWRITE_TAC[] THEN TRY close_pc_cond) (asl,w)
    else if hd w = "COND" || (has "pc" w && has "COND" w) then close_pc_cond (asl,w)
    else if hd (lhs w) = "word_sub" then close_x1_dec (asl,w)
    else if hd (lhs w) = "word_add" then close_ptr_dec (asl,w)
    else if hd (lhs w) = "read" && has "aes_ctr_block" (rhs w) then OUT_STORE_dec (asl,w)
    else if hd (lhs w) = "read" && has "inblock" (rhs w) then IN_READ_CLOSE_dec (asl,w)
    else if hd (lhs w) = "read" && free_in `ivec_p:int64` (lhs w) then IVEC_RECOMB_dec (asl,w)
    else if hd (lhs w) = "read" && has "ctr_block" (rhs w) then (SP_SLOT_dec_fast ORELSE SP_SLOT_dec) (asl,w)
    else if hd (lhs w) = "word_reversefields" && has "ctr_block" (lhs w) && has "ctr_block" (rhs w) then
      (* staged slot / Q31 body-end: rev8(ctr_block(4i+M')) = rev8(ctr_block(4(i+1)+M)) with 4i+M' = 4(i+1)+M.
         The E-merge/ASM already rewrote the read to the resident block; only the index arithmetic remains. *)
      (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) (asl,w)
    else if deep_ghash then SWP_Q30_SEED_TAC (asl,w)
    else if hd (lhs w) = "aesmc" then
      (* Q3=aes12c(4(i+1)+3), Q8=aes5c(4(i+1)+5): unfold def, counter fold *)
      ((REWRITE_TAC[aes12c;aes5c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
        REWRITE_TAC[ZX_COUNTER_UD;ZX_COUNTER_INC;CTR_ZX_NORM] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REWRITE_TAC[CTR_BLOCK_BUILD_INSERT; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
        TRY(CONV_TAC WORD_RULE) THEN TRY REFL_TAC) ORELSE CTRREG_dec) (asl,w)
    else if hd (lhs w) = "word_join" && has "ctr_block" (rhs w) then (SP_SLOT_dec_fast ORELSE SP_SLOT_dec) (asl,w)
    else if free_in `in_p:int64` w then
      (* any lane embedding an in_p read = a GHASH partial (Q4/5/6/9/10/11 or word_zx Karatsuba-mid) *)
      (GHASH_PARTIAL_CLOSE_dec ORELSE SWP_Q30_SEED_TAC ORELSE CTRREG_dec) (asl,w)
    else if hd (lhs w) = "word_zx" || hd (lhs w) = "word_subword" then CTRREG_dec (asl,w)
    else (* word_xor / word_pmul GHASH partials *)
      (GHASH_PARTIAL_CLOSE_dec ORELSE SWP_Q30_SEED_TAC) (asl,w);;

(* ===== leg proofs (FILL/BODY/DRAIN/TAIL) ===== *)

(* ==================== LEG: BODY (from arm/proofs/DEVEL_dec256_bodyleg.ml) ==================== *)
(* ============================================================================
   dec-256 SWP BODYLEG (real): swpS256_inv_dec i @0x26c -> inv(i+1) @0x570.
   Steps the body 1..193 (0x26c..0x56c; 0x570 cbnz is the back-edge, handled by
   the WHILE composition -- do NOT step it here), ENSURES_FINAL_STATE, then the
   CLOSE_DEC256 dispatcher (transplant of dec-128 CLOSE_V8, adapted to aes256 +
   aes5c/aes12c + the dec-256 conjunct order/counter offsets).
   ============================================================================ *)

(* ---- keep-sets, goal, stepper ---- *)
(* 2026-09-19: X11/X12 REMOVED from the invariant (DISASM 0x288 add w12,w13,#2; 0x29c rev w11,w12 -- the body
   CLOBBERS them as counter-scratch, never restores; they are NOT resident nonce lanes.  The staged counter
   blocks live in MEMORY (bytes128 sp+OFF conjuncts, reconstructed from X13), so the X11/X12 REGISTER values are
   dead at the loop head.  Dropped from the invariant + here.  (X11 kept in REDSETX so the stepper still tracks
   it harmlessly; ghost X11 dropped -- no longer an invariant input.) *)
let REDSETX_DEC = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";"Q10";"Q11";"Q12";"Q13";"Q14";
                   "Q29";"Q30";"Q31"; "X7";"X8";"X13";"X17";"X25";"X27";"X30"];;
let ghost_lanes_dec = ["X7";"X8";"X17";"X25";"X27";"X30";"X13"];;
(* 2026-09-19: merge RIGHT AFTER each counter-word store (before the ldr q), per dec-128's timing.
   Counter-word +12 stores: sp+204@step15 (block sp+192), sp+188@19 (block sp+176), sp+220@31 (block sp+208),
   sp+172@34 (block sp+160).  So merge at store+1 = (16,192),(20,176),(32,208),(35,160) -- NOT the load steps. *)
let merges_dec = [(16,192);(20,176);(32,208);(35,160)];;

let leg_state_dec inv off idx =
  let body = rhs(concl((TOP_DEPTH_CONV BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                        (list_mk_comb(inv,[idx;`s:armstate`])))) in
  mk_abs(`s:armstate`,
    list_mk_conj(`aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc` ::
                 mk_eq(`read PC s`,mk_comb(`word:num->int64`,mk_binop `+` `pc:num` off)) ::
                 conjuncts body));;

let mk_body_goal_dec inv =
  mk_imp(`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ i < loop_count - 2 /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,2036) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,2036) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,2036) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,2036) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192)`,
   list_mk_icomb "ensures" [`arm`;
     leg_state_dec inv `0x26c` `i:num` ;
     leg_state_dec inv `0x570` `i+1` ;
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;

let body_goal_dec = mk_body_goal_dec swpS256_inv_dec;;
Printf.printf "BISECT: body_goal_dec built\n%!";;

let INPUT_SPLIT_TAC_dec =
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
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 2` THEN
       UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`;
     ARITH_RULE `16 * (4*i+4) = 64*i+64`; ARITH_RULE `16 * (4*i+5) = 64*i+80`;
     ARITH_RULE `16 * (4*i+6) = 64*i+96`; ARITH_RULE `16 * (4*i+7) = 64*i+112`]);;

let setup_tac_dec =
  STRIP_TAC THEN REWRITE_TAC[fst DEC256_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes_dec THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  INPUT_SPLIT_TAC_dec THEN
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) && (let s = string_of_term(concl th) in
      contains "h_power" s && contains "htable_p" s) then STRIP_ASSUME_TAC th else NO_TAC);;

(* ---- 2026-09-20 APPROACH E staged-block reconstruction (NATIVE-SAFE; ivlo/ivhi VARIABLE lanes) ----
   The Design-A persistent lanes (RHS = compound word_subword(rev8(ctr_block 2))(..) memory read at an OLD
   state) crash native ARM_STEP_TAC.  enc-mem2 (proven native) uses ivec-half VARIABLES ivlo/ivhi and states
   lanes as `= ivlo`/`= word_subword ivhi (0,32)` (variable RHS -> ARM_STEP-safe).  We do the same:
   IVEC_SPLIT_dec (ABBREV ivlo/ivhi + join relation), SLOT_PRIME_E (variable-form lanes), MERGE_CTR128_FOLD_E
   (reconstruct via CTR_BLOCK_BUILD_V_DEC given the join relation).  Validated all 4 slots in MCP. *)
let splitL  = el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);;
let splitL2 = el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);;
let woff_sp n = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                        mk_comb(`word:num->int64`,mk_small_numeral n));;
let baseline_of_dec asl off =
  let addr = woff_sp off in
  tryfind (fun (_,th) -> match concl th with
    | Comb(Comb(Const("=",_),
        Comb(Comb(Const("read",_),Comb(Comb(_,Const("memory",_)),Comb(Const("bytes128",_),a))),
             Var("s0",_))),_) when a = addr -> th
    | _ -> fail()) asl;;
(* split the resident ivec bytes128 baseline into ABBREV'd 64-bit halves ivlo/ivhi (+ join relation). *)
let IVEC_SPLIT_dec : tactic =
  UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce 2)` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  DISCH_TAC THEN
  ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
  ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0`;;
let find_join asl =
  tryfind (fun (_,th) -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
                         then th else fail()) asl;;
(* lo-lane: read(bytes64 sp+off)s0 = ivlo  [B64 + baseline + TRANS via subword(ctr2)(0,64) + SLOT_LO(join)] *)
let prime_lo_E off : tactic = fun (asl,w) ->
  let tm = mk_eq(mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
              mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,int64)component->(armstate,int64)component`,`memory`),
                      mk_comb(`bytes64`,woff_sp off))),`s0:armstate`),`ivlo:int64`) in
  let bl = baseline_of_dec asl off in
  let sl = MATCH_MP SLOT_LO (find_join asl) in
  (SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[B64_OF_B128_LO; bl] THEN
    TRANS_TAC EQ_TRANS `word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64` THEN
    CONJ_TAC THENL [REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST; ACCEPT_TAC sl]; ALL_TAC]) (asl,w);;
(* mid-lane: read(bytes32 sp+off+8)s0 = word_subword ivhi (0,32) [B32 + addr_rw + baseline + TRANS + SLOT_MID] *)
let prime_mid_E off : tactic = fun (asl,w) ->
  let tm = mk_eq(mk_comb(mk_comb(`read:(armstate,int32)component->armstate->int32`,
              mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,int32)component->(armstate,int32)component`,`memory`),
                      mk_comb(`bytes32`,woff_sp (off+8)))),`s0:armstate`),`word_subword (ivhi:int64) (0,32):int32`) in
  let bl = baseline_of_dec asl off in
  let sm = MATCH_MP SLOT_MID (find_join asl) in
  let addr_rw = WORD_RULE (mk_eq(woff_sp (off+8), mk_comb(mk_comb(`word_add:int64->int64->int64`, woff_sp off),`word 8:int64`))) in
  (SUBGOAL_THEN tm ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[addr_rw] THEN REWRITE_TAC[B32_OF_B128_MID; bl] THEN
    TRANS_TAC EQ_TRANS `word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32` THEN
    CONJ_TAC THENL [REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST; ACCEPT_TAC sm]; ALL_TAC]) (asl,w);;
let SLOT_PRIME_E : tactic =
  EVERY (map (fun off -> prime_lo_E off THEN prime_mid_E off) [160;176;192;208]);;
(* reconstruct read(bytes128 sp+off)sname = rev8(ctr_block cval) from the ivlo/ivhi lanes + the +12 counter store,
   folding via CTR_BLOCK_BUILD_V_DEC (needs the join relation). *)
let MERGE_CTR128_FOLD_E off cval sname : tactic = fun (asl,w) ->
  let b128 = mk_comb(mk_comb(`read:(armstate,int128)component->armstate->int128`,
              mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,int128)component->(armstate,int128)component`,`memory`),
                      mk_comb(`bytes128`,woff_sp off))),mk_var(sname,`:armstate`)) in
  let target = mk_eq(b128, mk_comb(mk_comb(`word_reversefields:num->int128->int128`,`8`),
                                   mk_comb(mk_comb(`ctr_block:(96)word->num->int128`,`nonce:(96)word`),cval))) in
  let sp128 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_sp off; mk_var(sname,`:armstate`)] splitL) in
  let sp64  = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_sp (off+8); mk_var(sname,`:armstate`)] splitL2) in
  let bv = INST [cval,`cval:num`] (MATCH_MP CTR_BLOCK_BUILD_V_DEC (find_join asl)) in
  (SUBGOAL_THEN target ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [sp128; sp64] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CTR_ZX_NORM] THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN
    (fun (a,g) ->
       let brs = find_terms (fun t -> match t with Comb(Const("word_bytereverse",_),_) -> true | _ -> false) (lhs g) in
       let idx_exprs = setify (List.concat_map (fun br ->
          find_terms (fun t -> match t with Comb(Const("word",_),e) when not(is_numeral e) -> true | _ -> false) br) brs) in
       (EVERY (map (fun we -> let e = rand we in
          if e = cval then ALL_TAC else
          GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ARITH_RULE (mk_eq(e,cval))]) idx_exprs)) (a,g)) THEN
    ACCEPT_TAC bv;
    ALL_TAC]) (asl,w);;
(* (store_step, slot_off, body-end block index cval).  store steps from disasm: 192@16,176@20,208@32,160@35. *)
let merges_dec_fold = [ (16, 192, `4*i+8`); (20, 176, `4*i+7`); (32, 208, `4*i+9`); (35, 160, `4*i+6`) ];;
Printf.printf "BISECT: APPROACH-E staged-block machinery built (IVEC_SPLIT/SLOT_PRIME_E/MERGE_CTR128_FOLD_E)\n%!";;

let step_body_all =
  setup_tac_dec THEN
  IVEC_SPLIT_dec THEN
  (fun (asl,w) -> (Printf.printf "BISECT: setup+ivec-split done, starting SLOT_PRIME_E\n%!"; ALL_TAC (asl,w))) THEN
  SLOT_PRIME_E THEN
  (fun (asl,w) -> (Printf.printf "BISECT: SLOT_PRIME_E done, starting body stepping\n%!"; ALL_TAC (asl,w))) THEN
  (fun (asl,w) ->
     (MAP_EVERY (fun k ->
        (fun (a,ww) ->
           ((if k mod 20 = 0 then Printf.printf "BISECT: step %d\n%!" k else ()); ALL_TAC (a,ww))) THEN
        gkeepN REDSETX_DEC DEC256_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                                 IN_P_ADDR_FOLD_CONV)) THEN
        (match filter (fun (kk,_,_) -> kk=k) merges_dec_fold with
         | (_,off,cval)::_ -> MERGE_CTR128_FOLD_E off cval ("s"^string_of_int k)
         | [] -> ALL_TAC))
       (1--193)) (asl,w)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                           IN_P_ADDR_FOLD_CONV));;

(* ==================== closers ==================== *)
let rk15 = `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
             EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk`;;

(* in_p addr normalizations (64*(i+1)+K -> 16*(4*(i+1)+M)); (i+1) form. *)
let inp_addr_norms_dec =
  (* bare K=0 case: goal address is `word (64*(i+1))` with no `+0` *)
  (WORD_RULE `word_add (in_p:int64) (word (64*(i+1))):int64 = word_add in_p (word (16*(4*(i+1))))`) ::
  List.map (fun (kk,m) ->
    WORD_RULE (subst [mk_small_numeral kk, `K:num`; mk_small_numeral m, `M:num`]
                 `word_add (in_p:int64) (word (64*(i+1)+K)):int64 = word_add in_p (word (16*(4*(i+1)+M)))`))
  [(0,0);(16,1);(32,2);(48,3);(64,4);(80,5);(96,6);(112,7)];;

(* read(in_p+...)=inblock: normalize addr then in-forall. *)
let IN_READ_CLOSE_dec : tactic =
  REWRITE_TAC inp_addr_norms_dec THEN
  (fun (asl,w) ->
     FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                  && free_in (rand(lhs w)) (concl fa) with _->false)
                          then MATCH_MP_TAC fa else NO_TAC) (asl,w)) THEN ASM_ARITH_TAC;;

(* in-read folder that dewraps+normalizes inside a partial tower. *)
let is_inp_bytes128_read t =
  try let rd,st = dest_comb t in
      let rc,comp = dest_comb rd in
      fst(dest_const rc) = "read" && is_var st &&
      free_in `in_p:int64` comp &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "bytes128")) comp
  with _ -> false;;
let sixteen_blk rd =
  let mul16 = find_term (fun t ->
      try let op,args = strip_comb t in
          fst(dest_const op) = "*" && length args = 2 &&
          is_numeral (hd args) && dest_numeral (hd args) = num 16
      with _ -> false) rd in
  rand mul16;;
(* state of an in_p bytes128 read term (the s-var name), or "" *)
let inpread_state rd = try (match dest_comb rd with (_,Var(nm,_)) -> nm | _ -> "") with _ -> "";;
(* state that an input-frame forall's read is about (its bound-body read state var), or "" *)
let inpforall_state c = try
   (match snd(strip_forall c) with
    | Comb(Comb(Const("==>",_),_),bod) ->
       (match find_terms (fun t -> match t with
          Comb(Comb(Const("read",_),cmp),Var(nm,_)) when free_in `in_p:int64` cmp -> true | _ -> false) bod with
        | (Comb(Comb(_,_),Var(nm,_)))::_ -> nm | _ -> "")
    | _ -> "") with _ -> "";;
(* fold an in_p read to inblock, picking the input-frame forall AT THE READ'S OWN STATE (the out-store's embedded
   in_p read is at an OLD state sK; gkeepN keeps in_p foralls at all states, so the sK forall is present). *)
let INFOLD_dec : tactic =
  REWRITE_TAC inp_addr_norms_dec THEN
  (fun (asl,w) ->
    let inreads = setify(find_terms is_inp_bytes128_read w) in
    if inreads = [] then ALL_TAC (asl,w)
    else (EVERY (map (fun rd ->
       let blk = sixteen_blk rd in
       let st = inpread_state rd in
       (* TRY to fold rd -> inblock blk; NEVER throw (if no usable forall, leave rd unfolded so the caller can
          decide -- avoids regressing the whole closer to a raw-goal throw). *)
       TRY(SUBGOAL_THEN (mk_eq(rd, mk_comb(`inblock:num->int128`, blk))) ASSUME_TAC THENL
        [(* prefer the input-frame forall at the SAME state as the read; else any in_p forall *)
         (FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                       && inpforall_state (concl fa) = st with _->false)
                                  then MATCH_MP_TAC fa else NO_TAC)
          ORELSE FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa) with _->false)
                                         then MATCH_MP_TAC fa else NO_TAC))
         THEN
         (* the block-index bound (blk < nblocks): ASM_ARITH alone can't cross the nblocks DIV 4 = loop_count
            relation, so first establish 4*i+7 < nblocks (covers all body-leg blocks incl one-ahead 4(i+1)+2),
            from the 3 root invariant facts, then ASM_ARITH. *)
         (SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
           [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 2` THEN
            UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]
          ORELSE ALL_TAC) THEN
         ASM_ARITH_TAC; ALL_TAC]))
      inreads)) (asl,w));;

(* GHASH partial (pmul/xor over inblock x h-power lanes, RHS is my partial form, NO nist_ghash).
   2026-09-18: after the Q10/Q11 invariant fix all 5 partials (Q5/Q6/Q9/Q10/Q11) are TRUE.  Q5/Q9/Q10/Q11 close
   by REFL after the in-fold + reassemble.  Q6 (compound: karatsuba_mid mid-lane + block-2 word_subword(word_join
   ..)(64,128) structure) needs the extra SWP_SUBWORD_JOIN_MID + WORD_SIMPLE_SUBWORD + WORD_BLAST tail to fold the
   word_subword(word_join(km h1)(km h0))(k,64) -> km h_ and close the word_xor congruence. *)
let GHASH_PARTIAL_CLOSE_dec : tactic =
  INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE; GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  (TRY REFL_TAC THEN
   TRY (REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        TRY(CONV_TAC WORD_BLAST)));;

(* GHASH seed-core (Q30 half-swap accumulator = half-swap(nist_ghash..4(i+1))). aes256. *)
let SWP_REDUCE_RECON_256 : tactic =
  MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes256_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * i)))`;
      `cipherblock_0 = nist_input_block inblock (4 * i)`; `cipherblock_1 = nist_input_block inblock (4 * i + 1)`;
      `cipherblock_2 = nist_input_block inblock (4 * i + 2)`; `cipherblock_3 = nist_input_block inblock (4 * i + 3)`;
      `h0 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`; `h1 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 2`; `h3 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3 (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
      (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
      (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
      (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
    REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM] `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC ;
    MAP_EVERY EXPAND_TAC ["sofar";"cipherblock_0";"cipherblock_1";"cipherblock_2";"cipherblock_3";"h0";"h1";"h2";"h3"] THEN
    REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    ACCEPT_TAC SWP_GHASH_BRANCH2_256];;

let SWP_SEED_CORE_256 : tactic =
  REWRITE_TAC[SWP_JOIN_IS_BSW] THEN REWRITE_TAC[xor_rcancel] THEN
  REWRITE_TAC [byteswap128; SWP_SUBWORD_JOIN_MID] THEN
  MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  SWP_REDUCE_RECON_256;;

(* Q30 seed conjunct.  2026-09-18: with the Q10/Q11 invariant fix, the Q30 goal is now TRUE (machine reduce =
   half-swap of nist_ghash..(4(i+1))).  DISASM: Q30 = ext(v5,#8) = half-swap of the settled reduce v5.  After
   SWP_JOIN_IS_BSW/xor_rcancel/byteswap128/SWP_SUBWORD_JOIN_MID the goal is
     word_join (word_subword MACHINE_lo (0,64)) (word_subword MACHINE_hi (64,64))
       = word_join (word_subword ACC (0,64)) (word_subword ACC (64,64))     [ACC = nist_ghash..(4(i+1))]
   where MACHINE_lo != MACHINE_hi (the two 64-bit lanes come from DIFFERENT machine reduce sub-trees) -- so the
   dec-128 single-x `MATCH_MP_TAC(BITBLAST_RULE join(sub x)(sub x)=join(sub y)(sub y))` is UNSOUND here.  Use
   BINOP_TAC to split into the two ALIGNED per-half identities (sub MACHINE_lo 0 = sub ACC 0) & (sub MACHINE_hi 64
   = sub ACC 64); each is a bounded GHASH-reduce word-identity closed by the recon (fold ACC via
   GSYM SWP_GHASH_BRANCH2_256 -> prop3 packing, RECONSTRUCT, then a native BITBLAST ~117s -- exceeds the 600s MCP
   cap, native-only).  branch2 (packing=nist_ghash) is subsumed by the GSYM-BRANCH2 fold. *)
(* 2026-09-19 SOLVED (John's algebraic route, no poly-const blast).  The seed goal after the prefix is
     machwj[real lanes] = word_join (word_subword ACC (0,64)) (word_subword ACC (64,64))   [ACC=nist_ghash..4(i+1)]
   PREFIX: SWP_SUBWORD_JOIN_MID collapses LHS word_subword(word_join BIG)(64,128) -> word_join(sw.. 0)(sw.. 64)
     = machwj; DEC_GHASH_NORM_TAC folds the inblock byte-lanes -> nist_input_block; ASM_REWRITE folds the block-0
     Q14 read (read Q14 sK = inblock(4i), in asl) then GSYM nist_input_block makes it nist_input_block(4i); now
     LHS is exactly machwj over the real lanes.  FINISH: SWP_Q30_SEED_FINISH_TAC (in dec256_closers.ml) term_matches
     machwj_abs -> the 9 lane insts, INSTs the proven SEED_ABS (= byteswap128(prop3 simple), axiom-free, NO
     poly-const blast), folds prop3 simple -> nist_ghash..4(i+1) via SWP_GHASH_BRANCH2_256, byteswap128 def closes.
   The whole seed is now ~instant (SEED_ABS built once at load; ~1.5s+14s).  Invariant Q30 unchanged (confirmed
   correct: half-swap of nist_ghash..4i). *)
let SWP_Q30_SEED_TAC : tactic =
  REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN DEC_GHASH_NORM_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  SWP_Q30_SEED_FINISH_TAC;;

(* AES14P_VIA_* bridges: fold a carried AES partial (aesNc) + remaining rounds -> aes14p. *)
let out_via_lemmas =
  [AES14P_VIA_AES5C; AES14P_VIA_AES12C; AES14P_VIA_AES1C; AES14P_VIA_AES6C; AES14P_VIA_AES7C; AES14P_VIA_AES11C];;
(* per-block out-store keystream fold.  After the read resolves to the machine value
     word_xor inblock_j (word_xor rk14 <tower>) = word_xor (aes_ctr_block j) inblock_j
   <tower> is either a FULL 14-round tower on a resolved rev8(ctr_block(j+2)) [block whose counter block is
   resident] OR built on a carried AES partial aesNc(j+2) [pipelined blocks].  Try both (validated in MCP). *)
(* aes_ctr_block j unfolds to rev8(aes256_cipher(ctr_block(j+2))); normalize the ctr index j+2.
   Cover BOTH the out-frame form (j = 4i+M) AND the one-ahead form (j = 4(i+1)+M). *)
let ctr_idx_norms = [ARITH_RULE `(4*i)+2 = 4*i+2`; ARITH_RULE `(4*i+1)+2 = 4*i+3`;
                     ARITH_RULE `(4*i+2)+2 = 4*i+4`; ARITH_RULE `(4*i+3)+2 = 4*i+5`;
                     ARITH_RULE `(4*(i+1)+0)+2 = 4*(i+1)+2`; ARITH_RULE `(4*(i+1)+1)+2 = 4*(i+1)+3`;
                     ARITH_RULE `(4*(i+1)+2)+2 = 4*(i+1)+4`; ARITH_RULE `(4*(i+1)+3)+2 = 4*(i+1)+5`];;
(* resident-block ctr index bridges: the FULL-tower one-ahead keystream runs on a RESIDENT rev8(ctr_block(4i+K))
   (K=6,7,8,9), while after aes_ctr_block unfold the target ctr index is 4(i+1)+M+2.  Bridge 4i+K = 4(i+1)+M'. *)
let resident_ctr_norms = [ARITH_RULE `4*i+6 = 4*(i+1)+2`; ARITH_RULE `4*i+7 = 4*(i+1)+3`;
                          ARITH_RULE `4*i+8 = 4*(i+1)+4`; ARITH_RULE `4*i+9 = 4*(i+1)+5`];;
let OUT_BLOCK_CLOSE_dec : tactic =
  (* ADD_CLAUSES normalizes 4*i+0 -> 4*i (block-0's target has an explicit +0 that the INFOLD-folded operand lacks). *)
  REWRITE_TAC[ADD_CLAUSES] THEN
  ((REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC] THEN
   REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC ctr_idx_norms THEN
   REWRITE_TAC resident_ctr_norms THEN REFL_TAC)
  ORELSE
  (REWRITE_TAC(map GSYM out_via_lemmas) THEN
   REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC ctr_idx_norms THEN
   (fun (asl,w) ->
      let c = try rand(find_term (fun t -> match t with Comb(Comb(Const("ctr_block",_),_),_) -> true | _ -> false) (rhs w))
              with _ -> `4*i+2` in
      let inb = lhand (lhs w) in
      MP_TAC(SPECL[c; inb] (GENL [`c:num`;`inb:int128`] (MATCH_MP KEYSTREAM_FOLD256 (ASSUME rk15)))) (asl,w)) THEN
   DISCH_TAC THEN POP_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
   CONV_TAC WORD_BITWISE_RULE));;

(* out-store address normalization: the goal's one-ahead address out_p+word(64*(i+1)+32) must match the store
   fact's out_p+word((64*i+64)+32) form (the body's x2 post-increment produced 64*i+64, not 64*(i+1)). *)
let out_addr_norms = [
  WORD_RULE `word_add (out_p:int64) (word (64*(i+1)+32)) = word_add out_p (word ((64*i+64)+32))`];;
(* out-store readback (one-ahead q12 store of block 4(i+1)+2 = 4i+6 at out_p+(64*i+64)+32).
   Normalize the address so ASM resolves the read to the machine value, then the unified per-block keystream fold. *)
let OUT_STORE_dec : tactic =
  REWRITE_TAC out_addr_norms THEN
  (* FIRST resolve the out_p read to the machine value (which embeds an old-state in_p read); ONLY THEN can
     INFOLD see + fold that embedded in_p read.  (Running INFOLD before ASM_REWRITE was the bug: the in_p read
     is invisible until the out read resolves.) *)
  ASM_REWRITE_TAC[] THEN
  INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;

(* staged counter block: goal is either
     word_join (read sp+X+8 sK) (read sp+X sK) = rev8(ctr_block(4(i+1)+M))   [split-form], or
     read (bytes128 sp+X) sK = rev8(ctr_block(4(i+1)+M))                     [whole-form].
   Resolve the sp reads (their values are in asl from stepping), collapse the counter-word tower to
   word_shl(word_zx(word_bytereverse(word cval)))32, then CTR_BLOCK_BUILD_INSERT + mk_cbv folds to
   rev8(ctr_block). ASM_REWRITE brings in the read facts; the ZX/CTR lemmas normalize; mk_cbv-style
   const bridges close. Robustly try REFL/WORD_BLAST after each normalization. *)
(* dec-256 RHS index norms: rev8(ctr_block (4(i+1)+M)) -> rev8(ctr_block (4i+(4+M))) so the counter-word
   base 4i+4 folds cleanly against the stored add-value; the staged blocks are +2..+6. *)
let SP_RHS_NORMS_dec = [
  ARITH_RULE `4*(i+1)+2 = 4*i+6`; ARITH_RULE `4*(i+1)+3 = 4*i+7`;
  ARITH_RULE `4*(i+1)+4 = 4*i+8`; ARITH_RULE `4*(i+1)+5 = 4*i+9`;
  ARITH_RULE `4*(i+1)+6 = 4*i+10`];;
(* counter-word add folds (int32): the body computes add w,w13,#N with w13=word(4i+6) at store time. *)
let SP_LANE_FOLDS_dec = [
  WORD_RULE `word_add (word (4*i+6):int32) (word 1) = word(4*i+7)`;
  WORD_RULE `word_add (word (4*i+6):int32) (word 2) = word(4*i+8)`;
  WORD_RULE `word_add (word (4*i+6):int32) (word 3) = word(4*i+9)`;
  WORD_RULE `word_add (word (4*i+6):int32) (word 4) = word(4*i+10)`];;
(* staged counter block closer.  Two goal shapes:
     split: word_join(read sp+X+8 sK)(read sp+X sK) = rev8(ctr_block(4(i+1)+M))
     whole: read(bytes128 sp+X) sK          = rev8(ctr_block(4(i+1)+M))
   For the split form, MERGE_CTR128_TAC folds the two bytes64 reads back to a bytes128 read (matching the
   stepping's stored value); then ASM_REWRITE brings the stored insert-form in, CTR_ZX_NORM/lane-folds
   normalize the counter word, CTR_BLOCK_BUILD_INSERT folds to rev8(ctr_block).  We try MERGE at each staged
   offset (only the matching one fires; the rest ASM_REWRITE to no-ops).  Robust closers after. *)
(* 2026-09-19 mechanism-correct SP_SLOT_dec (pieces PROVEN: read-over-write split resolution + MEM2_REASSEMBLE).
   goal (split-form): word_join(read b64 sp+OFF+8 s193)(read b64 sp+OFF s193) = rev8(ctr_block(4(i+1)+M))
   or (whole-form): read(bytes128 sp+OFF)sK = rev8(ctr_block(4(i+1)+M)).
   Recipe: (1) if split-form, GSYM-fold to read(bytes128 sp+OFF)s193 (via READ_MEMORY_BYTESIZED_SPLIT el 1);
   (2) fully split bytes128->4 bytes32 (el 1 then el 2) + resolve the +12 lane to the counter-word store and the
   other 3 lanes to the surviving baseline, via ONCE_DEPTH COMPONENT_READ_OVER_WRITE_CONV (repeated to chain
   through the state write-tower); (3) ASM_REWRITE brings the resolved counter-word + baseline lanes; normalize
   the counter word (CTR_ZX_NORM/lane-folds) and fold via CTR_BLOCK_BUILD_INSERT/MEM2_REASSEMBLE to rev8(ctr_block).
   Robust fallbacks after each step. *)
(* 2026-09-20 FAST PATH: with MERGE_CTR128_FOLD wired into the stepper, each staged block is already resident at
   body-end as read(bytes128 sp+off)s193 = rev8(ctr_block (4(i+1)+M)) (the fold produced 4i+M' = 4(i+1)+M and
   read-over-write auto-advanced it to s193).  So the whole-form goal closes by ASM_REWRITE after bridging the
   index arithmetic 4(i+1)+M = 4i+M'.  Try this first; fall back to the old read-over-write recipe otherwise. *)
let SP_SLOT_dec_fast : tactic =
  REWRITE_TAC[ARITH_RULE `4*(i+1)+2 = 4*i+6`; ARITH_RULE `4*(i+1)+3 = 4*i+7`;
              ARITH_RULE `4*(i+1)+4 = 4*i+8`; ARITH_RULE `4*(i+1)+5 = 4*i+9`] THEN
  ASM_REWRITE_TAC[];;
let SP_SLOT_dec : tactic = fun (asl,w) ->
  let splitL = el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)
  and splitL2 = el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT) in
  (* if the goal LHS is word_join(read b64)(read b64), fold it back to read(bytes128 X) *)
  (TRY(fun (a,g) ->
     (match lhs g with
      | Comb(Comb(Const("word_join",_),
          Comb(Comb(Const("read",_),_),st)),_) ->
          let base = (match find_terms (fun t->match t with
             Comb(Comb(Const("word_add",_),v),_)->(try fst(dest_var v)="stackpointer" with _->false)|_->false)
             (rand(rator(lhs g))) with
             | (Comb(Comb(_,_),Comb(_,n)))::_ -> (try dest_small_numeral n with _->160) | _ -> 160) in
          let inst = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
            (ISPECL [`memory`; mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                     mk_comb(`word:num->int64`,mk_small_numeral base)); st] splitL) in
          GEN_REWRITE_TAC LAND_CONV [GSYM inst] (a,g)
      | _ -> ALL_TAC (a,g))) THEN
   (* resolve the bytes128 read through the write chain: split ONCE to 4 bytes32 lanes, then a BOUNDED number
      of read-over-write passes (each peels one write; the chain is deep but the +12 lane resolves to the last
      relevant store and the nonce lanes are disjoint from all body stores -> ASM_REWRITE finishes).
      NB the TOP_DEPTH split is applied ONCE (not in the REPEAT loop) to avoid re-splitting the whole goal. *)
   GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [splitL; splitL2] THEN
   CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
   CONV_TAC(ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
   CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
   REWRITE_TAC SP_LANE_FOLDS_dec THEN REWRITE_TAC SP_RHS_NORMS_dec THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[MEM2_REASSEMBLE; CTR_BLOCK_BUILD_INSERT] THEN
   REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   TRY(CONV_TAC WORD_RULE) THEN TRY REFL_TAC THEN TRY(CONV_TAC WORD_BLAST) THEN
   TRY(REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST)) (asl,w);;

(* counter scalar-lane folds (word_zx/word_add towers).  The X13 running-counter lane
   (word_zx(word_add(word_zx(word_zx(word(4i+2))))(word 4)) = word_zx(word(4(i+1)+2))) closes via
   CTR_LANE_dec (ZXRT32 round-trip + AP_TERM + WORD_RULE); other lanes via the ZX/CTR normal forms. *)
let CTRREG_dec : tactic =
  CTR_LANE_dec ORELSE
  (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
   CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
   TRY REFL_TAC THEN TRY(CONV_TAC WORD_RULE) THEN TRY(AP_TERM_TAC THEN ARITH_TAC));;

(* pointers. *)
let close_ptr_dec : tactic =
  REWRITE_TAC[ARITH_RULE `64*((i+1)+1)=64*(i+1)+64`; ARITH_RULE `64*(i+1) = 64*i+64`; LEFT_ADD_DISTRIB] THEN
  CONV_TAC WORD_RULE;;

(* X1 decrement. *)
let close_x1_dec : tactic =
  ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC];;

(* back-edge PC COND: the cbnz test resolves nonzero for i+1 < loop_count (steady). *)
let close_pc_cond : tactic =
  COND_CASES_TAC THENL [REFL_TAC; ALL_TAC] THEN
  (* the else-branch is contradictory: val(word_sub..)=0 impossible for i+1<loop_count-1... but at
     i=loop_count-2 boundary this is the LAST steady iter. The WHILE composition handles the boundary;
     here (i<loop_count-2) so word_sub(loop_count-(i+1))(1) != 0. *)
  POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(val (word_sub (word (loop_count-(i+1))) (word 1):int64) = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC] THEN REWRITE_TAC[VAL_EQ_0] THEN
    MATCH_MP_TAC(MESON[] `~(x = word 0) ==> ~(x = word 0)`) THEN
    REWRITE_TAC[WORD_EQ_0] THEN MAP_EVERY UNDISCH_TAC [`i < loop_count - 2`; `2 <= loop_count`] THEN ARITH_TAC;
    REFL_TAC];;

(* MAYCHANGE frame. *)
let pth_frame_dec = prove(`R s s' ==> R subsumed R' ==> R' s s'`, REWRITE_TAC[subsumed] THEN MESON_TAC[]);;
let close_frame_dec : tactic =
  fun (asl,w) ->
    let frame_th = try snd(List.find (fun (_,th) -> let c=concl th in
        (try not(is_eq c) && can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c
            && (match c with Comb(Comb(_,a),b) -> is_var a && is_var b | _->false) with _->false)) asl)
      with _ -> failwith "close_frame_dec: no frame asm" in
    (MATCH_MP_TAC(MATCH_MP pth_frame_dec frame_th) THEN
     REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) (asl,w);;

(* out-frame forall (j<4(i+1)): orthogonality preservation. Ported from dec-128 OUT0_TAC. *)
let pth128_dec = prove
   (`!(a:int64) m n. 16 <= val(word_sub (word m) (word n):int64) /\ 16 <= val(word_sub (word n) (word m):int64)
          ==> orthogonal_components (bytes128 (word_add a (word m))) (bytes128 (word_add a (word n)))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[bytes128] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
    REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; NONOVERLAPPING_MODULO_MOD2] THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_OFFSET_SIMPLE_BOTH THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_CASES; DIMINDEX_64]) THEN
    MP_TAC(ISPEC `word m:int64` VAL_BOUND) THEN MP_TAC(ISPEC `word n:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;
let orth_lemma_dec = prove
   (`orthogonal_components c d /\ read c s' = read c s ==> read c (write d y s') = read c s`,
    MESON_TAC[orthogonal_components]);;
let OUT_ORTH_dec : tactic =
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN CONJ_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV;
    MATCH_MP_TAC pth128_dec THEN
    W(fun (asl,w) ->
      let sub1 = rand(rand(fst(dest_conj w))) in
      let mtm = rand(rator sub1) and ntm = rand sub1 in
      let m = rand mtm and n = rand ntm in
      SUBGOAL_THEN (list_mk_conj [mk_binop `(<):num->num->bool` m `2 EXP 64`;
                                  mk_binop `(<):num->num->bool` n `2 EXP 64`])
        STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `2 EXP 64 = 18446744073709551616`] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC];;
let ORTH_STEP_dec : tactic =
  FIRST [ OUT_ORTH_dec; ORTHOGONAL_COMPONENTS_TAC;
          (MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN CONJ_TAC THENL
            [CONV_TAC VALID_COMPONENT_CONV; ORTHOGONAL_COMPONENTS_TAC]) ];;
let rec OUT_ROW_dec g =
  (REFL_TAC ORELSE (MATCH_MP_TAC orth_lemma_dec THEN CONJ_TAC THENL [ORTH_STEP_dec; OUT_ROW_dec])) g;;
let OUT_FRAME_dec : tactic =
  REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
  ASM_REWRITE_TAC[] THEN
  (* split into: forall j<4i (incoming out-frame invariant, ASM) + 4 blocks j=4i+{0,1,2,3}.
     block 4i+2 = frame-carry (incoming one-ahead, ASM); blocks 4i+{0,1,3} = fresh stores (INFOLD-resolve the
     in_p read + the resident counter, then the unified per-block keystream fold).  Each branch: try ASM
     (closes the forall + carry), else the block fold. *)
  REPEAT CONJ_TAC THEN
  (* forall j<4i goal: accept the incoming out-frame invariant forall (ASM_REWRITE can't instantiate a forall).
     concrete-block goals: ASM (frame-carry blk 4i+2) else INFOLD+fold (fresh blks).  ORDER (per OUT_STORE fix):
     ASM_REWRITE to resolve the out read FIRST, THEN INFOLD the now-visible embedded in_p read, THEN OUT_BLOCK. *)
  TRY (FIRST_X_ASSUM (fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) with _->false)
                                then MATCH_ACCEPT_TAC th else NO_TAC)) THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;

(* ivec recombine: after IVEC_SPLIT the ivec baseline is in ivlo/ivhi halves; the body never writes ivec_p, so
   read(bytes128 ivec_p)s193 recombines to word_join ivhi ivlo = rev8(ctr_block 2) (enc-mem2 recipe). *)
let IVEC_RECOMB_dec : tactic =
  GEN_REWRITE_TAC LAND_CONV [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  ASM_REWRITE_TAC[];;

(* master dispatcher (shape+content routed). *)
let CLOSE_DEC256 : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
    let deep_ghash = try has "nist_ghash" w with _ -> false in
    if has_mc w then close_frame_dec (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then OUT_FRAME_dec (asl,w)
    else if not(is_eq w) then (ASM_REWRITE_TAC[] THEN TRY close_pc_cond) (asl,w)
    else if hd w = "COND" || (has "pc" w && has "COND" w) then close_pc_cond (asl,w)
    else if hd (lhs w) = "word_sub" then close_x1_dec (asl,w)
    else if hd (lhs w) = "word_add" then close_ptr_dec (asl,w)
    else if hd (lhs w) = "read" && has "aes_ctr_block" (rhs w) then OUT_STORE_dec (asl,w)
    else if hd (lhs w) = "read" && has "inblock" (rhs w) then IN_READ_CLOSE_dec (asl,w)
    else if hd (lhs w) = "read" && free_in `ivec_p:int64` (lhs w) then IVEC_RECOMB_dec (asl,w)
    else if hd (lhs w) = "read" && has "ctr_block" (rhs w) then (SP_SLOT_dec_fast ORELSE SP_SLOT_dec) (asl,w)
    else if hd (lhs w) = "word_reversefields" && has "ctr_block" (lhs w) && has "ctr_block" (rhs w) then
      (* staged slot / Q31 body-end: rev8(ctr_block(4i+M')) = rev8(ctr_block(4(i+1)+M)) with 4i+M' = 4(i+1)+M.
         The E-merge/ASM already rewrote the read to the resident block; only the index arithmetic remains. *)
      (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) (asl,w)
    else if deep_ghash then SWP_Q30_SEED_TAC (asl,w)
    else if hd (lhs w) = "aesmc" then
      (* Q3=aes12c(4(i+1)+3), Q8=aes5c(4(i+1)+5): unfold def, counter fold *)
      ((REWRITE_TAC[aes12c;aes5c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
        REWRITE_TAC[ZX_COUNTER_UD;ZX_COUNTER_INC;CTR_ZX_NORM] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REWRITE_TAC[CTR_BLOCK_BUILD_INSERT; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
        TRY(CONV_TAC WORD_RULE) THEN TRY REFL_TAC) ORELSE CTRREG_dec) (asl,w)
    else if hd (lhs w) = "word_join" && has "ctr_block" (rhs w) then (SP_SLOT_dec_fast ORELSE SP_SLOT_dec) (asl,w)
    else if free_in `in_p:int64` w then
      (* any lane embedding an in_p read = a GHASH partial (Q4/5/6/9/10/11 or word_zx Karatsuba-mid) *)
      (GHASH_PARTIAL_CLOSE_dec ORELSE SWP_Q30_SEED_TAC ORELSE CTRREG_dec) (asl,w)
    else if hd (lhs w) = "word_zx" || hd (lhs w) = "word_subword" then CTRREG_dec (asl,w)
    else (* word_xor / word_pmul GHASH partials *)
      (GHASH_PARTIAL_CLOSE_dec ORELSE SWP_Q30_SEED_TAC) (asl,w);;

(* diagnostic wrapper: try CLOSE_DEC256; if it fails OR leaves the goal open, log it + CHEAT
   so ONE run surfaces every remaining closer gap. Flip DIAG=false for the real axiom-free proof. *)
let diag_counter = ref 0;;
let CLOSE_DEC256_DIAG : tactic =
  fun (asl,w) ->
    let hd t = try fst(dest_const(fst(strip_comb t))) with _->"?" in
    let lh = if is_eq w then hd(lhs w) else (if is_forall w then "forall" else hd w) in
    let rh = if is_eq w then hd(rhs w) else "-" in
    (* capture the RESIDUAL: run CLOSE_DEC256 ONCE; if it leaves subgoals open, dump THOSE (the actual residual),
       not the original w.  Guard the dump in try so a print failure never aborts the run. *)
    let res_opt = try Some (CLOSE_DEC256 (asl,w)) with _ -> None in
    match res_opt with
    | Some ((_,[],_) as res) -> res   (* fully closed: return the real (axiom-free) result *)
    | _ ->
      let rgls = (match res_opt with Some (_,gls,_) -> map snd gls | None -> [w]) in
      (incr diag_counter;
       (try
          let oldf = !print_types_of_subterms in
          print_types_of_subterms := 2;
          let dump = String.concat "\n\n---RESIDUAL-SUBGOAL---\n\n" (map string_of_term rgls) in
          print_types_of_subterms := oldf;
          let oc = open_out (Printf.sprintf "/tmp/dec256_fail_%02d.txt" !diag_counter) in
          output_string oc (Printf.sprintf "[FAIL lhs=%s rhs=%s]\n\nRESIDUAL (%d subgoal(s)):\n%s\n" lh rh (length rgls) dump);
          close_out oc
        with _ -> ());
       Printf.printf "CLOSE-FAIL %02d [lhs=%s rhs=%s] (%d residual subgoal(s))\n%!" !diag_counter lh rh (length rgls);
       CHEAT_TAC (asl,w));;

(* 2026-09-18: with the Q10/Q11 invariant fix, all 26 body-end goals are TRUE and the real dispatcher
   CLOSE_DEC256 discharges 25/26 in MCP (the Q30 seed's per-half BITBLAST is native-only, ~117s/half).
   Use CLOSE_DEC256 (NOT the CHEAT-on-fail _DIAG) for the axiom-free proof; run natively (bytecode/inline_load
   is far too slow for the seed blast). *)
Printf.printf "BISECT: all closers defined; starting SWP_DEC256_BODYLEG prove\n%!";;
let SWP_DEC256_BODYLEG = prove(body_goal_dec,
  step_body_all THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC] THEN
  REPEAT CONJ_TAC THEN CLOSE_DEC256);;

Printf.printf "MARKER: SWP_DEC256_BODYLEG done (axiom-free CLOSE_DEC256)\n%!";;

(* ==================== LEG: FILL (from arm/proofs/DEVEL_dec256_fillleg.ml) ==================== *)
(* ============================================================================
   dec-256 SWP FILL leg: whole-fn precond @ pc+0x2c  ->  swpS256_inv_dec 0 @ pc+0x26c.
   Establishes the mid-pipeline invariant at the first steady head (i=0), from the
   C-argument preconditions (round keys / ivec / tag / htable / input in memory).
   Reuses the bodyleg front-matter + steppers + invariant + closers (P2, axiom-free).
   Approach-E form: ivec halves ABBREV'd ivlo/ivhi (dec256_SETUP_TAC does this).
   ============================================================================ *)

(* keep-sets from the bodyleg (dec256_bodyleg_setup carries REDSETX_DEC/ghost_lanes_dec; redefine here). *)
let REDSETX_DEC = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";"Q10";"Q11";"Q12";"Q13";"Q14";
                   "Q29";"Q30";"Q31"; "X7";"X8";"X13";"X17";"X25";"X27";"X30"];;
let ghost_lanes_dec = ["X7";"X8";"X17";"X25";"X27";"X30";"X13"];;

(* lc_bound (from dec256_setup_recipe). *)
let lc_bound = prove(`nblocks DIV 4 = loop_count /\ 16 * nblocks < 2 EXP 64 ==> loop_count < 2 EXP 64`,
  STRIP_TAC THEN
  SUBGOAL_THEN `loop_count <= nblocks` MP_TAC THENL
   [EXPAND_TAC "loop_count" THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC);;

Printf.printf "MARKER: FILL prelude loaded\n%!";;

(* leg_state builder (from bodyleg): a state predicate = abl + PC@off + the invariant-inst conjuncts. *)
let leg_state_dec inv off idx =
  let body = rhs(concl((TOP_DEPTH_CONV BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                        (list_mk_comb(inv,[idx;`s:armstate`])))) in
  mk_abs(`s:armstate`,
    list_mk_conj(`aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc` ::
                 mk_eq(`read PC s`,mk_comb(`word:num->int64`,mk_binop `+` `pc:num` off)) ::
                 conjuncts body));;

(* FILL precondition @ pc+0x2c: the whole-fn entry state (C args + ivec/tag/htable/input in memory).
   Mirrors the enc-256 SWP256_CORRECT precond, dec-256 adapted (aes256_cipher, wordlist(key_p,15), input-frame). *)
let fill_pre_body = `read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
   read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
   read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
   wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
   read X0 s = in_p /\ read X2 s = out_p /\ read X5 s = key_p /\
   read X1 s = word len_bits /\
   (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
   htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s`;;
let fill_pre = mk_abs(`s:armstate`, list_mk_conj(
   `aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc` ::
   `read PC s = word (pc + 0x2c)` :: conjuncts fill_pre_body));;
let fill_post = leg_state_dec swpS256_inv_dec `0x26c` `0`;;
(* fill hypotheses: like the bodyleg's but WITHOUT `i` (2 <= loop_count is the fill/steady case). *)
let fill_hyps = `([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ len_bits < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,2036) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,2036) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,2036) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,2036) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192) /\
     nonoverlapping (key_p:int64,240) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (key_p:int64,240) (out_p:int64,16*nblocks) /\
     nonoverlapping (key_p:int64,240) (tag_p:int64,16)`;;
let fill_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;
let fill_goal = mk_imp(fill_hyps, list_mk_icomb "ensures" [`arm`; fill_pre; fill_post; fill_frame]);;
Printf.printf "MARKER: fill_goal built (type-checks)\n%!";;

(* ---- FILL setup: STRIP hyps, ENSURES_INIT @s0 (=pc+0x2c), IVEC-split (Approach-E), input-frame pin, guard facts. ---- *)
(* input-frame pin: the fill loads blocks 0..3 (in_p+{0,16,32,48}); pin them (nblocks>=8 from 2<=loop_count). *)
let FILL_INPUT_SPLIT_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0))))  s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1))))  s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2))))  s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3))))  s0 = inblock 3 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 4))))  s0 = inblock 4 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 5))))  s0 = inblock 5 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 6))))  s0 = inblock 6 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 7))))  s0 = inblock 7`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `7 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC];;

(* KEY_EXPAND_TAC: expand wordlist_from_memory(key_p,15) s0 = MAP rev8 rk into the 15 individual round-key
   reads read(bytes128 key_p+16k) s0 = word_reversefields 8 (EL k rk) (the FILL ldr q18..q2 loads at steps 1-15
   read these at s0; needed to close the round-key Q-reg invariant conjuncts).  MCP-validated (0 goals). *)
let KEY_EXPAND_TAC : tactic = fun (asl,w) ->
  let cs = map (fun (_,th) -> concl th) asl in
  let wl = find (fun t -> try contains "wordlist_from_memory" (string_of_term t) with _ -> false) cs in
  let rkeq = find (fun t -> try is_eq t && rhs t = `rk:(int128)list` with _->false) cs in
  let wl_expanded = CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV) (ASSUME wl) in
  let expanded = REWRITE_RULE[MAP; CONS_11] (GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [SYM(ASSUME rkeq)] wl_expanded) in
  STRIP_ASSUME_TAC expanded (asl,w);;

let fill_setup_tac =
  STRIP_TAC THEN REWRITE_TAC[fst DEC256_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  (* IVEC split -> ivlo/ivhi (Approach-E; matches the invariant's staged-slot lane form) *)
  UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce 2)` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN DISCH_TAC THEN
  ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
  ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
  FILL_INPUT_SPLIT_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) && (let s = string_of_term(concl th) in
      contains "h_power" s && contains "htable_p" s) then STRIP_ASSUME_TAC th else NO_TAC) THEN
  KEY_EXPAND_TAC;;
Printf.printf "MARKER: fill_setup_tac defined (MCP-validated: lands s0@pc+0x2c; + KEY_EXPAND round-key reads)\n%!";;

(* ---- Approach-E machinery (bodyleg reuse + FILL specifics) ---- *)
let splitL  = el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);;
let splitL2 = el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);;
let woff_sp n = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                        mk_comb(`word:num->int64`,mk_small_numeral n));;
let find_join asl =
  snd(find (fun (_,th) -> try let c = concl th in is_eq c &&
    (match lhs c with Comb(Comb(Const("word_join",_),_),_) -> true | _ -> false) &&
    contains "ctr_block" (string_of_term(rhs c)) with _ -> false) asl);;

(* FILL mid-lane prime: from the stp-store `read(bytes64 sp+(off+8)) sK = ivhi`, split bytes64->bytes32 and
   derive the mid lane `read(bytes32 sp+(off+8)) sK = word_subword ivhi (0,32)` (Approach-E variable form). *)
let fill_prime_mid off sK : tactic = fun (asl,w) ->
  let sv = mk_var(sK,`:armstate`) in
  let split_hi = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
    (ISPECL [`memory`; woff_sp (off+8); sv] splitL2) in
  let rd64_hi = lhs(concl split_hi) in
  let hi_th = find (fun (_,th) -> try lhs(concl th) = rd64_hi && rhs(concl th) = `ivhi:int64` with _ -> false) asl in
  let iv_eq = TRANS (SYM (snd hi_th)) split_hi in
  let mid = mk_eq(rand(rhs(concl split_hi)), `word_subword (ivhi:int64) (0,32):int32`) in
  (SUBGOAL_THEN mid ASSUME_TAC THENL
   [MP_TAC iv_eq THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC WORD_BLAST; ALL_TAC]) (asl,w);;
let fill_prime_mids sK : tactic = MAP_EVERY (fun off -> fill_prime_mid off sK) [160;176;192;208];;

(* base-counter lemma: the ivec's counter field (rev8(ctr_block nonce 2)) reverses back to `word 2`. *)
let BASE_CTR_DEC = prove(
  `word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce 2)
   ==> word_bytereverse (word_zx (word_ushr ivhi 32):int32) = word 2:int32`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN
  REWRITE_TAC[ctr_block] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN CONV_TAC WORD_BLAST);;

(* FILL guard + cbz resolution (0x88 counter setup -> cbz@0xa8 fall-through -> 0xac).  Establishes
   val(word len_bits)=len_bits (needs len_bits<2^64), X1=word loop_count, val(word loop_count)=loop_count,
   ~(X1=word 0); steps the cbz (produces `if`) then collapses it via loop_count>=2. *)
let fill_guard_facts sK : tactic =
  let x1lc = subst [mk_var(sK,`:armstate`),`s:armstate`] `read X1 s = word loop_count` in
  let x1ne = subst [mk_var(sK,`:armstate`),`s:armstate`] `~(read X1 s = word 0)` in
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN x1lc ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[word_ushr] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
    REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN x1ne ASSUME_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ASSUME x1lc] THEN
    REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC];;
let FILL_GUARD_CBZ_TAC : tactic =
  fill_guard_facts "s31" THEN
  gkeepN REDSETX_DEC DEC256_EXEC "s32" THEN
  SUBGOAL_THEN `(val (word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) = 0) <=> F`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[] THEN
    SUBGOAL_THEN `word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64 = word loop_count`
      SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM(ASSUME `read X1 s32 = word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2`)] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;
Printf.printf "MARKER: FILL_GUARD_CBZ_TAC defined (MCP-validated: cbz@0xa8 falls through to 0xac)\n%!";;

(* FILL counter merge (at the STORE step, mirroring bodyleg merges_dec_fold): reconstruct
   read(bytes128 sp+off) sK = rev8(ctr_block nonce cval) from the lo/mid lanes + the just-stored +12 counter
   lane.  The fill counter lane is runtime `word_add base (word K)` (base = rev(ivhi>>32)); BASE_CTR_DEC folds
   base->word 2, then a live-typed WORD_BLAST eq normalizes word_add(word 2)(word K)->word cval, then
   CTR_BLOCK_BUILD_V_DEC closes.  (Bodyleg's MERGE_CTR128_FOLD_E had a clean symbolic word cval already.) *)
(* MCP-validated for all 4 counters (2/3/4/5, folds + persists).  After splitting bytes128->lo/mid/counter
   lanes + ASM_REWRITE + REWRITE[bc] (base->word 2), the goal is `<lane-expr> = rev8(ctr_block cval)` and bv is
   `<bv-lhs> = rev8(ctr_block cval)`.  The lane-expr's counter core (arg of the non-ivhi word_bytereverse) is a
   word_zx-tower over word_add(word 2)(word K) [K=1/2/3] or a longer word_zx-tower over word 2 [K=0, the +0
   collapsed by the assembler]; bv's core is word_zx(word_zx(word cval)).  Bridge the two cores via a live WORD_BLAST
   eq (WORD_BLAST can't see through word_bytereverse, so we normalize its ARGUMENT to bv's exact core form, NOT to
   word cval), then ACCEPT bv.  Bare hand-typed widths mismatch -> always build the eq from live terms. *)
let MERGE_CTR128_FILL off cval sK : tactic = fun (asl,w) ->
  let b128 = mk_comb(mk_comb(`read:(armstate,int128)component->armstate->int128`,
              mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,int128)component->(armstate,int128)component`,`memory`),
                      mk_comb(`bytes128`,woff_sp off))),mk_var(sK,`:armstate`)) in
  let target = mk_eq(b128, mk_comb(mk_comb(`word_reversefields:num->int128->int128`,`8`),
                                   mk_comb(mk_comb(`ctr_block:(96)word->num->int128`,`nonce:(96)word`),cval))) in
  let sp128 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_sp off; mk_var(sK,`:armstate`)] splitL) in
  let sp64  = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_sp (off+8); mk_var(sK,`:armstate`)] splitL2) in
  let bc = MATCH_MP BASE_CTR_DEC (find_join asl) in
  let bv = INST [cval,`cval:num`] (MATCH_MP CTR_BLOCK_BUILD_V_DEC (find_join asl)) in
  let brev_noiv t = match t with Comb(Const("word_bytereverse",_),_) -> not(free_in `ivhi:int64` t) | _ -> false in
  let bv_core = rand(find_term brev_noiv (lhs(concl bv))) in
  (SUBGOAL_THEN target ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [sp128; sp64] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[bc] THEN
    (fun (a,g) ->
       let core = rand(find_term brev_noiv (lhs g)) in
       if core = bv_core then ACCEPT_TAC bv (a,g)
       else let ceq = prove(mk_eq(core, bv_core), CONV_TAC WORD_BLAST) in
            (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ceq] THEN ACCEPT_TAC bv) (a,g));
    ALL_TAC]) (asl,w);;
(* merges at the STORE steps (str w,[sp,#off+12]; like the bodyleg's merges_dec_fold): 176@43(ctr3), 192@48(ctr4),
   208@53(ctr5), 160@56(ctr2).  Merging at the STORE (not reload) folds read(bytes128 sp+off)s(store)=rev8(ctr_block)
   EARLY, so it propagates via read-over-write to ALL later consumers: the AES input reload (Q3/Q8/Q12 = aes on the
   staged block), the reload-into-Q, and the staged-slot invariant conjunct at the final state.  (The reload-step
   merge folded too late -- at s(reload) -- so consumers reading s(reload-1) or the AES input saw the unfolded slot.) *)
let dec_fill_merges = [ (43, 176, `3`); (48, 192, `4`); (53, 208, `5`); (56, 160, `2`) ];;
Printf.printf "MARKER: MERGE_CTR128_FILL + dec_fill_merges defined (merge at STORE step)\n%!";;

(* ---- shared body/fill closers (rk15, INFOLD_dec, OUT_STORE_dec, CLOSE_DEC256, ...) ---- *)

(* ---- FILL i=0 in-read folding: INFOLD_dec expects addresses in 16*(4*(i+1)+M) form + a body `i`; at i=0 the FILL
   reads are direct word N and there is no `i`.  INFOLD_FILL = INFOLD_dec's fold but with (a) FILL address norms
   (word N = word(16*M) for N=16..112) so sixteen_blk finds the block index, (b) the block bound 7<nblocks from
   2<=loop_count (not i<loop_count-2). ---- *)
let inp_addr_norms_fill =
  List.map (fun (n,m) -> WORD_RULE (subst [mk_small_numeral n,`N:num`; mk_small_numeral m,`M:num`]
              `word_add (in_p:int64) (word N):int64 = word_add in_p (word (16 * M))`))
    [(16,1);(32,2);(48,3);(64,4);(80,5);(96,6);(112,7)];;
let INFOLD_FILL : tactic =
  REWRITE_TAC inp_addr_norms_fill THEN
  (fun (asl,w) ->
    let inreads = setify(find_terms is_inp_bytes128_read w) in
    if inreads = [] then ALL_TAC (asl,w)
    else (EVERY (map (fun rd ->
       let blk = sixteen_blk rd in
       let st = inpread_state rd in
       TRY(SUBGOAL_THEN (mk_eq(rd, mk_comb(`inblock:num->int128`, blk))) ASSUME_TAC THENL
        [(FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                       && inpforall_state (concl fa) = st with _->false)
                                  then MATCH_MP_TAC fa else NO_TAC)
          ORELSE FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa) with _->false)
                                         then MATCH_MP_TAC fa else NO_TAC))
         THEN
         (SUBGOAL_THEN `7 < nblocks` ASSUME_TAC THENL
           [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]
          ORELSE ALL_TAC) THEN
         ASM_ARITH_TAC; ALL_TAC]))
      inreads)) (asl,w));;
(* i=0 index normalizations: 4*0+K = K (the FILL folds reads to bare inblock K, but the invariant RHS uses the
   symbolic 4*0+K form).  Applied in the GHASH-partial/in-read/out-store closers so both sides match for REFL. *)
let fill_idx_norms = map (fun k -> ARITH_RULE (subst [mk_small_numeral k,`K:num`] `4*0+K = K`)) [0;1;2;3;4;5;6;7;8;9];;
(* GHASH partial closer at i=0: INFOLD_FILL then the bodyleg reassemble tail + i=0 index norms. *)
let GHASH_PARTIAL_FILL : tactic =
  INFOLD_FILL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE; GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC fill_idx_norms THEN                       (* 4*0+K -> K so LHS(inblock K)=RHS(inblock(4*0+K)) *)
  (TRY REFL_TAC THEN
   TRY (REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        TRY(CONV_TAC WORD_BLAST)));;
(* FILL Q30 seed at i=0: the accumulator is nist_ghash .. tag0 (list_of_seq .. (4*0)) = nist_ghash .. tag0 [] =
   tag0 (GHASH over the empty list), so Q30 = half-swap(tag0) -- NO Horner reduce (unlike the bodyleg's 4i seed).
   Reduce the RHS accumulator to tag0, then the machine lanes (byte-tower of rev8 tag0) = half-swap(tag0) by WORD_BLAST. *)
let SEED_TAG0_REDUCE = prove(
  `nist_ghash (aes256_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * 0)) = tag0`,
  REWRITE_TAC[MULT_CLAUSES; LIST_OF_SEQ; nist_ghash]);;
let SEED_FILL : tactic =
  REWRITE_TAC[SEED_TAG0_REDUCE] THEN CONV_TAC WORD_BLAST;;

(* FILL out-store closer (block-2 one-ahead): read(out_p+64*0+32) s144 = word_xor(aes_ctr_block(4*0+2))(inblock
   (4*0+2)).  At i=0 the address is out_p+64*0+32 directly (no 64*(i+1) form), so skip out_addr_norms; resolve the
   store via ASM, in-fold the embedded in_p read (INFOLD_FILL), then the bodyleg block-close + i=0 idx norms. *)
(* i=0 out address: the goal reads out_p+word(64*0+32); the store fact is at out_p+word 32.  Normalize. *)
let out_addr_norms_fill = [ WORD_RULE `word_add (out_p:int64) (word (64*0+32)) = word_add out_p (word 32)` ];;
(* i=0 counter index norms for aes_ctr_block unfolding: aes_ctr_block .. K = rev8(aes256_cipher(ctr_block(K+2))..);
   after fill_idx_norms reduce 4*0+K->K, the K+2 counter needs K+2 -> literal (block 2 -> ctr 4, etc.). *)
let fill_ctr_idx_norms = map (fun k ->
  ARITH_RULE (mk_eq(mk_binop `+` (mk_small_numeral k) `2`, mk_small_numeral (k+2)))) [0;1;2;3;4;5;6;7];;
let OUT_STORE_FILL : tactic =
  REWRITE_TAC out_addr_norms_fill THEN
  ASM_REWRITE_TAC[] THEN INFOLD_FILL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC fill_idx_norms THEN
  (* MCP-validated reconstruct: XOR_AES256_CIPHER_RECONSTRUCT_DEC folds the machine AES tower to
     rev8(aes256_cipher(ctr_block(K+2))rk); WORD_REVERSEFIELDS_REVERSEFIELDS undoes the rev8-of-rev8 on the ctr-block
     + round keys; MAP+rk15 rebuilds rk; aes_ctr_block def + K+2 literal makes RHS match. *)
  ((REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC] THEN
    REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC fill_ctr_idx_norms THEN REFL_TAC)
   ORELSE
   (REWRITE_TAC(map GSYM out_via_lemmas) THEN REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC fill_ctr_idx_norms THEN
    (fun (asl,w) ->
       let c = try rand(find_term (fun t -> match t with Comb(Comb(Const("ctr_block",_),_),_) -> true | _ -> false) (rhs w))
               with _ -> `4` in
       let inb = lhand (lhs w) in
       MP_TAC(SPECL[c; inb] (GENL [`c:num`;`inb:int128`] (MATCH_MP KEYSTREAM_FOLD256 (ASSUME rk15)))) (asl,w)) THEN
    DISCH_TAC THEN POP_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC WORD_BITWISE_RULE)
   ORELSE ALL_TAC);;   (* DIAG: never throw -> DIAG dumps the ACTUAL post-ASM residual (pinpoints the stuck read/fold) *)

(* FILL in-read closer (Q0/Q1/Q14 = inblock K): the read may already be folded to `inblock K` by INFOLD/ASM
   (leaving `inblock K = inblock(4*0+K)` = pure index-arith), OR be a raw read at in_p+word N (N=16..112) or bare
   in_p (block 0, offset 0).  Normalize 4*0+K->K and 4*0->0 on the RHS; normalize the addr (incl bare in_p ->
   in_p+word(16*0)); MATCH the in_p forall. *)
let IN_READ_FILL : tactic =
  REWRITE_TAC (ARITH_RULE `4*0=0` :: fill_idx_norms) THEN
  (* bare in_p (block 0, offset 0): the read address is exactly in_p (no word_add).  Rewrite in_p ->
     word_add in_p (word(16*0)) via SUBST1 ONLY in that case (guarded: goal LHS read address = bare in_p). *)
  (fun (asl,w) ->
     let is_bare = (try let rd = lhs w in
        let addr = rand(rand(rand(rator rd))) in fst(dest_var addr) = "in_p" with _ -> false) in
     (if is_bare then
        (SUBGOAL_THEN `in_p:int64 = word_add in_p (word (16 * 0))` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC])
      else TRY (REWRITE_TAC inp_addr_norms_fill)) (asl,w)) THEN
  (((fun (asl,w) ->
       FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa) with _->false)
                            then MATCH_MP_TAC fa else NO_TAC) (asl,w)) THEN
    (SUBGOAL_THEN `7 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]
     ORELSE ALL_TAC) THEN ASM_ARITH_TAC)
   ORELSE ALL_TAC);;

(* terminal cbz@0x268 (step 144): x1 = word_sub(word loop_count)(word 1) (after sub@0x264); ~=word 0 since
   loop_count>=2, so falls through to 0x26c.  Needs read X1 s143 = word loop_count (X1 anchored through the body). *)
let SWP_SUB1_NE0 = prove(
  `2 <= loop_count /\ loop_count < 2 EXP 64 ==> ~(val(word_sub (word loop_count) (word 1):int64) = 0)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1` SUBST1_TAC THENL
   [SUBGOAL_THEN `val(word 1:int64) <= val(word loop_count:int64)` MP_TAC THENL
     [REWRITE_TAC[VAL_WORD_1] THEN SUBGOAL_THEN `val(word loop_count:int64) = loop_count` SUBST1_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      DISCH_TAC THEN ASM_SIMP_TAC[VAL_WORD_SUB_CASES] THEN
      SUBGOAL_THEN `val(word loop_count:int64) = loop_count` SUBST1_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; REWRITE_TAC[VAL_WORD_1]]];
    ASM_ARITH_TAC]);;
(* terminal cbz resolution: step 144, collapse the resulting `if val(word_sub..)=0 ...` PC to pc+0x26c. *)
let FILL_CBZ144_TAC : tactic =
  SUBGOAL_THEN `loop_count < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC lc_bound THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word_sub (word loop_count) (word 1):int64) = 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SWP_SUB1_NE0 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  gkeepN ("X1"::REDSETX_DEC) DEC256_EXEC "s144" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;

(* ---- full fill stepper: setup -> steps 1-31 (+ mid-lane prime @ s23) -> guard/cbz -> body 33-143 -> cbz 144. ---- *)
let NSTEP_FILL = 143;;  (* 0x2c..0x264 straight-line; step 144 = cbz@0x268 -> fall-through to 0x26c (FILL_CBZ144_TAC). *)
let FILL_PROGRESS k : tactic = fun g -> ((if k mod 10 = 0 then Printf.printf "FILL exec step %d\n%!" k); ALL_TAC g);;
(* body keeplist: REDSETX + X1 (so read X1 = word loop_count persists from the guard to the terminal cbz). *)
let REDSETX_FILL = "X1"::REDSETX_DEC;;
let fill_step_all =
  fill_setup_tac THEN
  (* steps 1-31: round keys, tag0, ivec pair -> 4 slots; prime the mid lanes at s23 (post the 4 stp). *)
  (fun (asl,w) ->
    (MAP_EVERY (fun k ->
       gkeepN REDSETX_FILL DEC256_EXEC ("s"^string_of_int k) THEN
       RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
       (if k = 23 then fill_prime_mids "s23" else ALL_TAC) THEN FILL_PROGRESS k)
      (1--31)) (asl,w)) THEN
  (* guard + cbz @ 0xa8 -> 0xac *)
  FILL_GUARD_CBZ_TAC THEN
  (* body 33-143 (0xac..0x264) with counter merges at the RELOAD steps; keep X1 for the terminal cbz *)
  (fun (asl,w) ->
    (MAP_EVERY (fun k ->
       gkeepN REDSETX_FILL DEC256_EXEC ("s"^string_of_int k) THEN
       RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
       (match filter (fun (kk,_,_) -> kk=k) dec_fill_merges with
        | (_,off,cval)::_ -> MERGE_CTR128_FILL off cval ("s"^string_of_int k)
        | [] -> ALL_TAC) THEN FILL_PROGRESS k)
      (33--NSTEP_FILL)) (asl,w)) THEN
  FILL_CBZ144_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;
Printf.printf "MARKER: fill_step_all defined (NSTEP_FILL=%d + terminal cbz144)\n%!" NSTEP_FILL;;

(* ---- establish swpS256_inv_dec 0 @ 0x26c: reuse the bodyleg CLOSE_DEC256 dispatcher at i=0.
   The post-state conjuncts have the same shapes as the bodyleg's (with 4*0+K concrete), so CLOSE_DEC256
   handles them; the Q30 seed at i=0 = half-swap(nist_ghash..(4*0)) = half-swap(tag0) (GHASH over empty list),
   the out-frame forall j<0 is VACUOUS.  The cbz@0x268 (step 144) falls through since 2<=loop_count. ---- *)
(* FILL out-frame at i=0: the incoming FILL has NO out-frame forall (fresh start), so the split's vacuous
   `forall j. j < 4*0 ==> ...` branch can't MATCH_ACCEPT an incoming forall -> discharge it via MULT_CLAUSES+LT
   +ARITH FIRST.  The 4 concrete blocks (j=4*0+{0,1,2,3}) are all fresh keystream folds (blk 4*0+2 = one-ahead
   carry from the invariant conjunct). Otherwise identical to the bodyleg OUT_FRAME_dec. *)
let OUT_FRAME_fill : tactic =
  REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (REWRITE_TAC[MULT_CLAUSES; LT] THEN ARITH_TAC) THEN          (* vacuous j<4*0 forall *)
  TRY (FIRST_X_ASSUM (fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) with _->false)
                                then MATCH_ACCEPT_TAC th else NO_TAC)) THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;
(* FILL register-setup closers (X1/X15/X9/X13): the FILL computes these registers at runtime from len_bits/ivhi,
   while the bodyleg's invariant has them pre-set symbolically.  Each MCP-validated on the exact residual form. *)
let REG_X15_FILL : tactic =   (* word_ushr(word len_bits) 3 = word(len_bits DIV 8) *)
  REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ARITH_TAC];;
let REG_X9_FILL : tactic =   (* word_and(word_ushr(word_ushr(word len_bits)3)4)(word 3) = word loop_remain *)
  REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
  REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;;
let REG_X1_FILL : tactic =   (* word_sub(word loop_count)(word 1) = word(loop_count-1) *)
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD_1];
    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[VAL_WORD_1] THEN
    UNDISCH_TAC `2 <= loop_count` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];;
let REG_X13_FILL : tactic =   (* word_zx(word_bytereverse(word_zx(word_ushr ivhi 32))) = word_zx(word(4*0+2)) *)
  fun (asl,w) ->
    (REWRITE_TAC[MATCH_MP BASE_CTR_DEC (find_join asl)] THEN
     REWRITE_TAC[ARITH_RULE `4*0+2=2`]) (asl,w);;
(* FILL closer: route foralls -> OUT_FRAME_fill; the FILL register-setup forms -> their closers; else the bodyleg
   dispatcher.  X15/X9/X13 are new (not in CLOSE_DEC256); X1 (word_sub) overrides close_x1_dec's body form. *)
let CLOSE_FILL : tactic = fun (asl,w) ->
  let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
  let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
  (* head NAME whether const OR var (inblock is a VARIABLE in the spec, so `has`/`hd`(const) miss it). *)
  let hdname t = (try fst(dest_const(fst(strip_comb t))) with _ -> (try fst(dest_var(fst(strip_comb t))) with _ -> "")) in
  let inb = `inblock:num->int128` in
  let deep_ghash = try has "nist_ghash" w with _ -> false in
  if is_forall w then OUT_FRAME_fill (asl,w)
  else if is_eq w && hd(lhs w)="word_ushr" && free_in `len_bits:num` w && not(has "word_and" w) then REG_X15_FILL (asl,w)
  else if is_eq w && hd(lhs w)="word_and" && free_in `len_bits:num` w then REG_X9_FILL (asl,w)
  else if is_eq w && hd(lhs w)="word_sub" && free_in `loop_count:num` w && not(has "pc" w) then REG_X1_FILL (asl,w)
  else if is_eq w && hd(lhs w)="word_zx" && has "word_ushr" (lhs w) && free_in `ivhi:int64` (lhs w) then REG_X13_FILL (asl,w)
  (* Q30 seed (deep nist_ghash over the empty list at i=0 = half-swap(tag0)): reduce to tag0 + WORD_BLAST. *)
  else if deep_ghash then SEED_FILL (asl,w)
  (* pure index-arith residual inblock K = inblock(4*0+K) (in-read already folded by INFOLD/ASM). *)
  else if is_eq w && hdname(lhs w)="inblock" && hdname(rhs w)="inblock" then
    (REWRITE_TAC (ARITH_RULE `4*0=0` :: fill_idx_norms) THEN REFL_TAC) (asl,w)
  (* Q0/Q1/Q14 inblock reads (read(bytes128 in_p+..) = inblock(4*0+K) or bare in_p = inblock(4*0)): in-read closer. *)
  else if is_eq w && hd(lhs w)="read" && free_in `in_p:int64` (lhs w) && free_in inb (rhs w) then IN_READ_FILL (asl,w)
  (* out-store block (read(bytes128 out_p+..) = word_xor(aes_ctr_block..)(inblock..)): FILL i=0 out-store closer. *)
  else if is_eq w && hd(lhs w)="read" && free_in `out_p:int64` (lhs w) && has "aes_ctr_block" (rhs w) then OUT_STORE_FILL (asl,w)
  (* GHASH partials (pmul/xor/zx towers embedding in_p reads): FILL in-fold variant. *)
  else if free_in `in_p:int64` w then (GHASH_PARTIAL_FILL ORELSE CLOSE_DEC256) (asl,w)
  else CLOSE_DEC256 (asl,w);;

(* DIAG wrapper (same as bodyleg): the FIRST run surfaces every i=0 closer gap; flip FILL_DIAG=false for
   the real axiom-free proof once all conjuncts close.  2026-09-21: PROVEN diag_counter=0 (CLOSE_FILL closes all
   25 conjuncts, DIAG never cheated, check_axioms clean) -> FILL_DIAG=false for the production axiom-free proof. *)
let FILL_DIAG = false;;
let fill_diag_counter = ref 0;;
let CLOSE_FILL_DIAG : tactic =
  fun (asl,w) ->
    let hd t = try fst(dest_const(fst(strip_comb t))) with _->"?" in
    let lh = if is_eq w then hd(lhs w) else (if is_forall w then "forall" else hd w) in
    let rh = if is_eq w then hd(rhs w) else "-" in
    let res_opt = try Some (CLOSE_FILL (asl,w)) with _ -> None in
    match res_opt with
    | Some ((_,[],_) as res) -> res
    | _ ->
      let rgls = (match res_opt with Some (_,gls,_) -> map snd gls | None -> [w]) in
      (incr fill_diag_counter;
       (try
          let oldf = !print_types_of_subterms in print_types_of_subterms := 2;
          let dump = String.concat "\n\n---RESIDUAL-SUBGOAL---\n\n" (map string_of_term rgls) in
          print_types_of_subterms := oldf;
          let oc = open_out (Printf.sprintf "/tmp/dec256_fill_fail_%02d.txt" !fill_diag_counter) in
          output_string oc (Printf.sprintf "[FAIL lhs=%s rhs=%s]\n\nRESIDUAL (%d subgoal(s)):\n%s\n" lh rh (length rgls) dump);
          close_out oc
        with _ -> ());
       Printf.printf "FILL-CLOSE-FAIL %02d [lhs=%s rhs=%s] (%d residual)\n%!" !fill_diag_counter lh rh (length rgls);
       CHEAT_TAC (asl,w));;
let SWP_DEC256_FILL = prove(fill_goal,
  fill_step_all THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC] THEN
  REPEAT CONJ_TAC THEN (if FILL_DIAG then CLOSE_FILL_DIAG else CLOSE_FILL));;
Printf.printf "MARKER: SWP_DEC256_FILL done (diag_counter=%d)\n%!" !fill_diag_counter;;


(* ==================== LEG: DRAIN (from arm/proofs/DEVEL_dec256_drainleg.ml) ==================== *)
(* ============================================================================
   dec-256 SWP DRAIN leg: swpS256_inv_dec (loop_count-1) @ pc+0x570 (cbnz, x1=0 falls through)
   -> drain_bridge @ pc+0x6c0.  Finishes the LAST group (blocks 4(loop_count-1)..4*loop_count-1):
   settles Q30 = half-swap(nist_ghash .. tag0 (list_of_seq (nist_input_block inblock) (4*loop_count)))
   and stores the last group's outputs.  Mirrors the enc-256 SWP drain leg (drain_bridge @0xdd0),
   dec-256 adapted: GHASH over INPUT (ciphertext), aes256, bare `b 0x6c0` end (no body skip).
   Control flow (disasm): 0x570 cbnz x1 (x1=0 -> fall through) ; 0x574..0x6b8 straight-line drain
   (83 instrs; 3 output stores str q5/q12/q5 @ 0x6a4/0x6b4/0x6b8) ; 0x6bc b 0x6c0 (Lloop_unrolled_end).
   Reuses the bodyleg front-matter + steppers + invariant + shared closers.
   ============================================================================ *)

let REDSETX_DEC = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";"Q10";"Q11";"Q12";"Q13";"Q14";
                   "Q29";"Q30";"Q31"; "X7";"X8";"X13";"X17";"X25";"X27";"X30"];;
let ghost_lanes_dec = ["X7";"X8";"X17";"X25";"X27";"X30";"X13"];;
let lc_bound = prove(`nblocks DIV 4 = loop_count /\ 16 * nblocks < 2 EXP 64 ==> loop_count < 2 EXP 64`,
  STRIP_TAC THEN
  SUBGOAL_THEN `loop_count <= nblocks` MP_TAC THENL
   [EXPAND_TAC "loop_count" THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC);;

Printf.printf "MARKER: DRAIN prelude loaded\n%!";;

(* leg_state builder (from bodyleg). *)
let leg_state_dec inv off idx =
  let body = rhs(concl((TOP_DEPTH_CONV BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                        (list_mk_comb(inv,[idx;`s:armstate`])))) in
  mk_abs(`s:armstate`,
    list_mk_conj(`aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc` ::
                 mk_eq(`read PC s`,mk_comb(`word:num->int64`,mk_binop `+` `pc:num` off)) ::
                 conjuncts body));;

Printf.printf "MARKER: leg_state_dec defined\n%!";;

(* ---- drain_bridge @ pc+0x6c0 (settled state feeding the 1-block tail).  MCP type-checked (32 conjuncts).
   Q30 is SETTLED to half-swap(nist_ghash over 4*loop_count input blocks); the tail reloads Q12/Q13/Q14 from
   htable (0x6c0-0x6c8) so the bridge omits them.  Mirrors enc drain_bridge @0xdd0, dec-adapted (nist_input_block,
   half-swap not byteswap128, Q2=rev8(EL 14 rk) as the 15th round key). ---- *)
let drain_bridge = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc`;
  `read PC s = word (pc + 0x6c0)`;
  `read X0 s = word_add in_p (word (64 * loop_count))`;
  `read X2 s = word_add out_p (word (64 * loop_count))`;
  `read X3 s = tag_p`; `read X4 s = ivec_p`; `read X6 s = htable_p`; `read SP s = stackpointer`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
  `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2)`;
  `read X13 s = word_zx (word (4 * loop_count + 2):int32):int64`;
  `read X15 s = word(len_bits DIV 8)`;
  `read X9 s = word loop_remain`;
  `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
  `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
  `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
  `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
  `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
  `read Q28 s = word_reversefields 8 (EL 10 rk)`; `read Q15 s = word_reversefields 8 (EL 11 rk)`;
  `read Q16 s = word_reversefields 8 (EL 12 rk)`; `read Q17 s = word_reversefields 8 (EL 13 rk)`;
  `read Q2 s = word_reversefields 8 (EL 14 rk)`;
  (* Q7 = the polyval-reduce constant, loop-carried (never written); the TAIL's Q30 reduce needs it pinned.
     Carried unchanged from swpS256_inv_dec (which has it); closes by ASM in the drain (drain never writes Q7). *)
  `read Q7 s = word 13979173243358019584`;
  `read Q30 s = word_join
     ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * loop_count))) (0,64)):int64)
     ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * loop_count))) (64,64)):int64)`;
  `htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s`;
  (* staged counter slot 160: carried UNCHANGED from the invariant @i=loop_count-1 (the drain never writes sp+160);
     the TAIL needs its nonce lanes to rebuild its per-block counter (it only re-stores the +12 counter word). *)
  `read (memory :> bytes128 (word_add stackpointer (word 160))) s =
     word_reversefields 8 (ctr_block nonce (4 * (loop_count - 1) + 2))`;
  `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`;
  `!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes_ctr_block nonce rk j) (inblock j)`]);;
Printf.printf "MARKER: drain_bridge built (%d conjuncts)\n%!" (List.length(conjuncts(snd(dest_abs drain_bridge))));;

(* ---- drain_goal: swpS256_inv_dec (loop_count-1) @0x570 -> drain_bridge @0x6c0.  MCP type-checked. ---- *)
let drain_hyps = `([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ len_bits < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,2036) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,2036) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,2036) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,2036) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192)`;;
let drain_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;
let drain_goal = mk_imp(drain_hyps,
  list_mk_icomb "ensures" [`arm`; leg_state_dec swpS256_inv_dec `0x570` `loop_count - 1`; drain_bridge; drain_frame]);;
Printf.printf "MARKER: drain_goal built (type-checks)\n%!";;

(* ---- drain setup: enters the invariant @0x570 (i=loop_count-1); round keys already in Q18-Q28 (NO KEY_EXPAND,
   unlike FILL).  m=loop_count-1, X1->word 0, last-group input split (blocks 4m..4m+3).  MCP-validated: lands
   s0@0x570, 97 asls, X1=word 0.  (Reuses the bodyleg setup_tac_dec structure: GHOST_INTRO + ENSURES_INIT + BETA
   + htable unfold + input-split.  No IVEC-split needed here yet -- add if the drain reads ivec lanes.) ---- *)
let splitL  = el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);;
let INPUT_SPLIT_TAC_drain =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * (4*(loop_count-1)+0))))) s0 = inblock (4*(loop_count-1)+0) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*(loop_count-1)+1))))) s0 = inblock (4*(loop_count-1)+1) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*(loop_count-1)+2))))) s0 = inblock (4*(loop_count-1)+2) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*(loop_count-1)+3))))) s0 = inblock (4*(loop_count-1)+3)`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `4*(loop_count-1)+3 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC];;
let drain_setup_tac =
  STRIP_TAC THEN REWRITE_TAC[fst DEC256_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes_dec THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  SUBGOAL_THEN `read X1 s0 = word 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read X1 s0 = word (loop_count - ((loop_count-1)+1))`) (concl th)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `loop_count - ((loop_count-1)+1) = 0` SUBST1_TAC THENL
     [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]; ALL_TAC] THEN
  INPUT_SPLIT_TAC_drain THEN
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) && (let s = string_of_term(concl th) in
      contains "h_power" s && contains "htable_p" s) then STRIP_ASSUME_TAC th else NO_TAC);;
Printf.printf "MARKER: drain_setup_tac defined (MCP-validated: s0@0x570, 97 asls, X1=word 0)\n%!";;

(* drain cbnz@0x570 resolution: x1=word 0 -> cbnz NOT taken -> fall through to 0x574.  MCP-validated: PC->0x574.
   The cbnz produces `if ~(val(word(loop_count-(loop_count-1+1)))=0) then pc+620 else pc+1396`; reduce the counter
   to word 0 (2<=loop_count), val(word 0)=0, ~(0=0)=F, else-branch = pc+1396 = 0x574. *)
let DRAIN_CBNZ_TAC : tactic =
  gkeepN REDSETX_DEC DEC256_EXEC "s1" THEN
  SUBGOAL_THEN `loop_count - (loop_count - 1 + 1) = 0`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_0]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `~(0 = 0) <=> F`; COND_CLAUSES]);;
Printf.printf "MARKER: DRAIN_CBNZ_TAC defined (MCP-validated: 0x570 cbnz falls through to 0x574)\n%!";;

(* ---- NEXT (drain stepper + closer): ----
   (4) drain stepper: DRAIN_CBNZ_TAC (-> 0x574) then step 2..83 (0x574..0x6bc; 83 instrs incl the b 0x6c0@0x6bc).
       NO counter merges (drain is the last group; the 3 str q @0x6a4/0x6b4/0x6b8 are OUTPUT stores, steps 77/81/82).
       gkeepN REDSETX_DEC + per-step WORD_SIMPLE_SUBWORD/NORMALIZE_ADDR/IN_P_ADDR_FOLD conv.
   (5) THE CRUX: ENSURES_FINAL + close drain_bridge.  Q30 settles: the dec Q30 invariant @ i=loop_count-1 is the
       SPLIT half-swap word_join(subword(nist_ghash..4(lc-1))..0)(subword..64); the drain reduces the LAST group
       (4(lc-1)..4lc-1) so Q30_final = half-swap(nist_ghash..4*loop_count).  This is the enc/dec SHARED GHASH
       split-reduce (genuine hard core; see gcm-swp-proof-structure memory).  Adapt enc drain_close_q30
       (SWPGRP_IS_NIST_GHASH @3495 + close_goal7 reduce, m-indexed).  Plus 3 last-group output stores
       (OUT_STORE-reconstruct at block indices 4(lc-1)+{1,2,3}) + output-frame extend j<4*loop_count.
   (6) GEN_ALL for the whole-fn WHILE-glue (P4).
   Precedent: enc-256 SWP drain_close_q30 (aes_gcm_enc_kernel_256_x4_scalar_iv_mem_late_tag_scalar_rk_swp.ml
     3662-3670+) + SWPGRP_IS_NIST_GHASH @3495 + LIST_OF_SEQ_APPEND @3490.
   ============================================================================ *)

(* GHASH bridge lemmas (from enc-256 SWP): swpgrp <-> nist_ghash + list-of-seq append. Needed by the Q30 closer. *)
let LIST_OF_SEQ_APPEND = prove
 (`!n f m. list_of_seq f (m + n) = APPEND (list_of_seq f m) (list_of_seq (\i. f(m+i)) n)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND; o_THM; ETA_AX]);;
Printf.printf "MARKER: LIST_OF_SEQ_APPEND proven\n%!";;

(* ---- drain stepper: DRAIN_CBNZ_TAC (-> 0x574) then steps 2..84 (0x574..0x6bc; the b 0x6c0@0x6bc is step 84).
   NO counter merges. Reuses REDSETX_DEC + the bodyleg per-step conv. ---- *)
let NSTEP_DRAIN = 84;;   (* step1=cbnz@0x570; steps 2..84 = 0x574..0x6bc (83 instrs incl b 0x6c0@0x6bc -> 0x6c0). *)
let DRAIN_PROGRESS k : tactic = fun g -> ((if k mod 10 = 0 then Printf.printf "DRAIN exec step %d\n%!" k); ALL_TAC g);;
let drain_step_all =
  drain_setup_tac THEN
  DRAIN_CBNZ_TAC THEN
  (fun (asl,w) ->
    (MAP_EVERY (fun k ->
       gkeepN REDSETX_DEC DEC256_EXEC ("s"^string_of_int k) THEN
       RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
       DRAIN_PROGRESS k)
      (2--NSTEP_DRAIN)) (asl,w)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;
Printf.printf "MARKER: drain_step_all defined (NSTEP_DRAIN=%d)\n%!" NSTEP_DRAIN;;

(* ---- DRAIN closer (DIAG scaffold): the first native run surfaces the drain_bridge gaps.  The bridge conjuncts
   are: aligned/PC (ASM), the carried regs (round keys/X-regs = ASM from invariant + stepping), the SETTLED Q30
   (THE CRUX -- last-group Horner reduce), the 3 output stores + output-frame.  Route most to CLOSE_DEC256/ASM;
   surface the Q30 + output-frame gaps for bespoke closers.  Flip DRAIN_DIAG=false once all close. ---- *)

(* --- drain-specific closers for the 5 gaps surfaced by drain-iter1 (3 simple + Q30-settle + out-frame). --- *)
(* FAIL 01/02: pointer arithmetic X0/X2 (loop_count-1+1 = loop_count, 64*(lc-1)+64 = 64*lc). *)
let DRAIN_PTR_TAC : tactic =
  AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;;
(* FAIL 03: X13 counter word_zx(word_add(word_zx(word_zx(word(4*(lc-1)+2))))(word 4)) = word_zx(word(4*lc+2)).
   The drain does add w13,#4 @0x57c; the base counter is nested word_zx(word_zx ..) (int32->int64->int32 round-trip).
   ZX_WT collapses the nesting, GSYM WORD_ADD merges the +4, then AP_TERM + ARITH. *)
let ZX_WT = prove(`word_zx(word_zx(w:int32):int64):int32 = w`, CONV_TAC WORD_BLAST);;
let DRAIN_X13_TAC : tactic =
  REWRITE_TAC[ZX_WT] THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;;
(* FAIL 04: THE Q30 SETTLE.  Bridge the RHS 4*loop_count -> 4*((loop_count-1)+1) so SWP_Q30_SEED_TAC (bodyleg, which
   proves machine-reduce = half-swap(nist_ghash..4*(i+1)) with i:=loop_count-1) can close.  The dec Q30 is the
   split half-swap form; SWP_Q30_SEED_TAC handles it (SWP_SUBWORD_JOIN_MID + DEC_GHASH_NORM + SWP_Q30_SEED_FINISH).
   Adapt at i=loop_count-1: rewrite 4*loop_count -> 4*((loop_count-1)+1) on BOTH sides first. *)
(* NB: 4*loop_count = 4*((loop_count-1)+1) is only true for 1<=loop_count -- a bare ARITH_RULE is FALSE at
   loop_count=0 (truncated subtraction: 0-1+1=1); establish it from the 2<=loop_count hypothesis via SUBGOAL_THEN.
   THE Q30 SETTLE: the goal is machine-reduce (embedding half-swap(nist_ghash..4*(loop_count-1))) = half-swap
   (nist_ghash..4*loop_count).  SWP_Q30_SEED_TAC (bodyleg) proves this at a bare loop-index `i` (its internal
   ARITH_RULEs like 4*i+4=SUC^4(4*i) need `i` to be a VARIABLE), but here the index is the compound `loop_count-1`.
   FIX: ABBREV m = loop_count - 1 so the goal uses the bare `m` (LHS 4*(loop_count-1)->4*m, RHS via loop_count=m+1
   -> 4*(m+1)); then SWP_Q30_SEED_TAC fires with i:=m.  Mirrors enc drain_close_q30's m-indexing. *)
(* MCP-VALIDATED end-to-end (2026-09-22): after the bridge + ABBREV m, SWP_Q30_SEED_TAC (SWP_SUBWORD_JOIN_MID +
   DEC_GHASH_NORM_TAC + ASM + GSYM nist_input_block + ASM + SWP_Q30_SEED_FINISH_TAC) reduces the machine reduce to
   byteswap128(nist_ghash..4*(m+1)) = word_join(subword..)(subword..), leaving both sides the split half-swap of
   nist_ghash..4*(m+1) -> REFL_TAC closes.  (term_match machwj_abs succeeds after DEC_GHASH_NORM.)  REQUIRES the
   drain_bridge Q30 conjunct's word_subword outputs be int64-pinned (else free type-vars block the final REFL). *)
let DRAIN_Q30_TAC : tactic =
  SUBGOAL_THEN `4 * loop_count = 4 * ((loop_count - 1) + 1)`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [th]) THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = loop_count - 1` THEN
  SWP_Q30_SEED_TAC THEN REFL_TAC;;
(* FAIL 05: output-frame forall j<4*loop_count.  Split into j<4*(loop_count-1) (incoming) + the last-group blocks
   (4*(loop_count-1)+{0,1,2,3}); incoming via ASM forall, last-group blocks via OUT_STORE-reconstruct.  Delegate to
   the bodyleg OUT_FRAME_dec machinery with 4*loop_count = 4*((loop_count-1)+1). *)
let DRAIN_OUTFRAME_TAC : tactic =
  SUBGOAL_THEN `4 * loop_count = 4 * ((loop_count-1)+1)` (fun th -> GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [th]) THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  (OUT_FRAME_dec ORELSE (ASM_REWRITE_TAC[] THEN CLOSE_DEC256));;

let DRAIN_DIAG = false;;  (* PROVEN axiom-free (with slot-160 conjunct for TAIL); production. *)
let drain_diag_counter = ref 0;;
let CLOSE_DRAIN : tactic = fun (asl,w) ->
  let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
  let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
  let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
  let deep_ghash = try has "nist_ghash" w with _ -> false in
  if has_mc w then close_frame_dec (asl,w)                              (* MAYCHANGE frame subsumption *)
  else if not(is_eq w) && not(is_forall w) then ASM_REWRITE_TAC[] (asl,w)   (* aligned_bytes_loaded / PC *)
  else if is_forall w then DRAIN_OUTFRAME_TAC (asl,w)
  else if hd(lhs w)="word_add" && (free_in `in_p:int64` w || free_in `out_p:int64` w) then DRAIN_PTR_TAC (asl,w)
  else if hd(lhs w)="word_zx" && free_in `loop_count:num` (lhs w) then DRAIN_X13_TAC (asl,w)
  else if deep_ghash then DRAIN_Q30_TAC (asl,w)
  (* staged counter slot 160 = rev8(ctr_block(4*(loop_count-1)+2)): carried unchanged from the invariant (drain
     never writes sp+160). ASM resolves read-over-84-nonwriting-steps to the s0 value; SP_SLOT_dec folds it. *)
  else if is_eq w && hd(lhs w)="read" && free_in `stackpointer:int64` (lhs w) && has "ctr_block" (rhs w) then
    (ASM_REWRITE_TAC[] THEN TRY (SP_SLOT_dec_fast ORELSE SP_SLOT_dec)) (asl,w)
  else (ASM_REWRITE_TAC[] THEN TRY CLOSE_DEC256) (asl,w);;
let CLOSE_DRAIN_DIAG : tactic =
  fun (asl,w) ->
    let hd t = try fst(dest_const(fst(strip_comb t))) with _->"?" in
    let lh = if is_eq w then hd(lhs w) else (if is_forall w then "forall" else hd w) in
    let rh = if is_eq w then hd(rhs w) else "-" in
    let res_opt = try Some (CLOSE_DRAIN (asl,w)) with _ -> None in
    (match res_opt with
     | Some ((_,[],_) as res) -> res
     | _ ->
       let rgls = (match res_opt with Some (_,gls,_) -> map snd gls | None -> [w]) in
       (incr drain_diag_counter;
        (try let oldf = !print_types_of_subterms in print_types_of_subterms := 2;
           let dump = String.concat "\n\n---RESIDUAL---\n\n" (map string_of_term rgls) in
           print_types_of_subterms := oldf;
           let oc = open_out (Printf.sprintf "/tmp/dec256_drain_fail_%02d.txt" !drain_diag_counter) in
           output_string oc (Printf.sprintf "[FAIL lhs=%s rhs=%s]\n\n%s\n" lh rh dump); close_out oc
         with _ -> ());
        Printf.printf "DRAIN-CLOSE-FAIL %02d [lhs=%s rhs=%s]\n%!" !drain_diag_counter lh rh;
        CHEAT_TAC (asl,w)));;
let SWP_DEC256_DRAIN = prove(drain_goal,
  drain_step_all THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (if DRAIN_DIAG then CLOSE_DRAIN_DIAG else CLOSE_DRAIN));;
Printf.printf "MARKER: SWP_DEC256_DRAIN done (drain_diag_counter=%d)\n%!" !drain_diag_counter;;

let REDSETX_DEC = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";"Q10";"Q11";"Q12";"Q13";"Q14";
                   "Q29";"Q30";"Q31"; "X7";"X8";"X13";"X17";"X25";"X27";"X30"];;
let ghost_lanes_dec = ["X7";"X8";"X17";"X25";"X27";"X30";"X13"];;
Printf.printf "MARKER: TAIL prelude loaded\n%!";;

(* drain_bridge @ pc+0x6c0 (the tail's precondition = proven SWP_DEC256_DRAIN post; int64-pinned Q30 + slot-160
   staged block).  Copied from DEVEL_dec256_drainleg.ml so the tail leg is self-contained. *)
let drain_bridge = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc`;
  `read PC s = word (pc + 0x6c0)`;
  `read X0 s = word_add in_p (word (64 * loop_count))`;
  `read X2 s = word_add out_p (word (64 * loop_count))`;
  `read X3 s = tag_p`; `read X4 s = ivec_p`; `read X6 s = htable_p`; `read SP s = stackpointer`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
  `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2)`;
  `read X13 s = word_zx (word (4 * loop_count + 2):int32):int64`;
  `read X15 s = word(len_bits DIV 8)`; `read X9 s = word loop_remain`;
  `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
  `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
  `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
  `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
  `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
  `read Q28 s = word_reversefields 8 (EL 10 rk)`; `read Q15 s = word_reversefields 8 (EL 11 rk)`;
  `read Q16 s = word_reversefields 8 (EL 12 rk)`; `read Q17 s = word_reversefields 8 (EL 13 rk)`;
  `read Q2 s = word_reversefields 8 (EL 14 rk)`;
  `read Q7 s = word 13979173243358019584`;
  `read Q30 s = word_join
     ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * loop_count))) (0,64)):int64)
     ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * loop_count))) (64,64)):int64)`;
  `htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s`;
  `read (memory :> bytes128 (word_add stackpointer (word 160))) s =
     word_reversefields 8 (ctr_block nonce (4 * (loop_count - 1) + 2))`;
  `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`;
  `!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes_ctr_block nonce rk j) (inblock j)`]);;
Printf.printf "MARKER: drain_bridge (tail precond) built (%d conjuncts)\n%!" (List.length(conjuncts(snd(dest_abs drain_bridge))));;

(* ---- tail_inv i : the drain_bridge shape + loop index i (X0/X2 += 16*i, X13/X9/Q30 track i) + Q12/Q14 h-power
   pins (reloaded @0x6c0-0x6c8; the 1-block GHASH needs them).  MCP type-checked (32 conjuncts).  Mirrors enc
   tail_inv @0xde0. ---- *)
let tail_inv = `\(i:num) s.
    read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
    read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
    read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read Q28 s = word_reversefields 8 (EL 10 rk) /\ read Q15 s = word_reversefields 8 (EL 11 rk) /\
    read Q16 s = word_reversefields 8 (EL 12 rk) /\ read Q17 s = word_reversefields 8 (EL 13 rk) /\
    read Q2 s = word_reversefields 8 (EL 14 rk) /\
    read Q7 s = word 13979173243358019584 /\
    read X13 s = word_zx (word (4 * loop_count + i + 2):int32):int64 /\
    read X15 s = word(len_bits DIV 8) /\ read X9 s = word(loop_remain - i) /\
    read Q30 s = word_join
       ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
          (list_of_seq (nist_input_block inblock) (4 * loop_count + i))) (0,64)):int64)
       ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
          (list_of_seq (nist_input_block inblock) (4 * loop_count + i))) (64,64)):int64) /\
    htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
    read Q12 s = byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) /\
    read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0)) /\
    read (memory :> bytes64 (word_add stackpointer (word 160))) s =
       word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
    read (memory :> bytes32 (word_add stackpointer (word 168))) s =
       word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * loop_count + i ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
             word_xor (aes_ctr_block nonce rk j) (inblock j))`;;
Printf.printf "MARKER: tail_inv built (%d conjuncts)\n%!" (List.length(conjuncts(snd(dest_abs(snd(dest_abs tail_inv))))));;

(* ---- tail_post @ pc+0x7c4 (writeback done): tag = rev8(nist_ghash over all nblocks), counter word out at
   ivec_p+12, X0 = len_bits DIV 8, out-forall over ALL nblocks.  (At loop exit i=loop_remain,
   4*loop_count+loop_remain = nblocks.)  MCP type-checked. ---- *)
let tail_post = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc`;
  `read PC s = word (pc + 0x7c4)`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8
     (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) nblocks))`;
  `read (memory :> bytes128 ivec_p) s =
     word_reversefields 8 (ctr_block nonce (nblocks + 2))`;
  `read X0 s = word (len_bits DIV 8)`;
  `!j. j < nblocks ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes_ctr_block nonce rk j) (inblock j)`]);;
Printf.printf "MARKER: tail_post built (%d conjuncts)\n%!" (List.length(conjuncts(snd(dest_abs tail_post))));;

(* ---- tail_goal: drain_bridge @0x6c0 -> tail_post @0x7c4.  Takes drain_bridge AS the precond (= proven
   SWP_DEC256_DRAIN post).  MCP type-checked. ---- *)
let tail_hyps = `([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     16 * nblocks < 2 EXP 64 /\ len_bits < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,2036) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,2036) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,2036) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (htable_p:int64,192) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (in_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,2036)`;;
let tail_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(tag_p:int64,16)] ,, MAYCHANGE [memory :> bytes(ivec_p:int64,16)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;
let tail_goal = mk_imp(tail_hyps, list_mk_icomb "ensures" [`arm`; drain_bridge; tail_post; tail_frame]);;
Printf.printf "MARKER: tail_goal built\n%!";;

(* per-step conv (reused). *)
let dstep k = gkeepN REDSETX_DEC DEC256_EXEC ("s"^string_of_int k) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                              ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;

(* ---- tail_tac: ASM_CASES loop_remain=0 -> [degenerate | WHILE].  DEGENERATE + WHILE-BASE both MCP-VALIDATED
   (2026-09-22); STEP + back-edge + EXIT are the remaining focused work (see below). ----
   DEGENERATE (loop_remain=0): SUBST loop_remain=0; nblocks=4*loop_count; ENSURES_INIT; htable unfold; step 1..3
     (htable reloads 0x6c0-0x6c8); step 4 (cbz x9@0x6cc, x9=word 0 TAKEN -> 0x7b0); step 5..9 (writeback
     mov/rev64/str q30/rev/str w14 -> 0x7c4); ENSURES_FINAL; per-conjunct: tag (ABBREV gv + nblocks->4*loop_count
     + WORD_BLAST), counter (nblocks->4*loop_count + WORD_BLAST), out-frame (nblocks->4*loop_count + ASM),
     frame (close_frame_dec).  ALL VALIDATED.
   WHILE (loop_remain>0): REWRITE[ABI] THEN ENSURES_WHILE_UP_TAC `loop_remain` `pc+0x6d0` `pc+0x7ac` tail_inv THEN
     REPEAT CONJ_TAC -> 5 obligations:
     g0 ~(loop_remain=0): ASM_REWRITE.  [VALIDATED]
     g1 BASE (drain_bridge->tail_inv 0): ENSURES_INIT; htable unfold; step 1..3 (reloads); val(word loop_remain)=
        loop_remain (from lr<4); step 4 (cbz NOT taken -> 0x6d0); ENSURES_FINAL; ASM_REWRITE[ADD_CLAUSES;
        MULT_CLAUSES; SUB_0; htable_mem_4] (i=0 norms: 16*0=0, +0, -0, 4lc+0=4lc).  [VALIDATED]
     g2 STEP (tail_inv i -> tail_inv(i+1)): X_GEN_TAC i; STRIP; VAL_INT64_TAC i; ENSURES_INIT; htable unfold;
        pin the input block read(in_p+64*loop_count+16*i) = inblock(4*loop_count+i) (64a+16b=16(4a+b)); step the
        56-instr 1-block body (0x6d0..0x7a8): counter merge MERGE_CTR128 160 @ step ~6; str q30@step53 out-store;
        the 1-block GHASH Q30 update half-swap(nist_ghash..(4lc+i)) + block -> half-swap(nist_ghash..(4lc+i+1))
        via NIST_GHASH single-CONS append + the machine pmull reduce (Q12/Q14 pins).  [TODO -- the substantive leg]
     g3 back-edge: cbnz x9@0x7ac, x9=word(loop_remain-(i+1)) != 0 for i+1<loop_remain -> back to 0x6d0.  [close_pc]
     g4 EXIT (tail_inv loop_remain -> tail_post): the writeback postamble 0x7b0..0x7c4 (mov/rev64/str q30/rev/str
        w14) at i=loop_remain (4*loop_count+loop_remain=nblocks); SAME closers as the DEGENERATE case.  [~= degen]
   Model: enc tail_tac (aes_gcm_enc..swp.ml 4661-4760).  dec: aes256, half-swap Q30, INPUT GHASH (nist_input_block),
   counter str to [x4,#12].
   THE STEP Q30 update (g2 core): the 1-block GHASH.  half-swap(nist_ghash..(4lc+i)) XOR inblock(4lc+i) folded by
   one pmull-reduce (h_power 0 via Q12, karatsuba-mid via Q14) = half-swap(nist_ghash..(4lc+i+1)).  Algebraically
   NIST_GHASH_APPEND / a single ghash_polyval_acc step; adapt bodyleg GHASH-partial closers to the single-block case.
   ============================================================================ *)

(* ============================================================================
   tail_goal + tail_tac.  Degenerate (loop_remain=0) + WHILE-base VALIDATED in MCP; STEP setup/merge/stepping +
   8/9 closers validated; Q30 1-block reduce ported from enc tail_ghash_close (dec-adapted).  DIAG wrapper
   surfaces any residual for iteration (same workflow as FILL/DRAIN).
   ============================================================================ *)
let tail_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(tag_p:int64,16)] ,, MAYCHANGE [memory :> bytes(ivec_p:int64,16)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;
let tail_goal = mk_imp(tail_hyps, list_mk_icomb "ensures" [`arm`; drain_bridge; tail_post; tail_frame]);;
Printf.printf "MARKER: tail_goal built\n%!";;

let splitL  = el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);;
let splitL2 = el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);;
let woff_t n = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),mk_comb(`word:num->int64`,mk_small_numeral n));;
let ZX_WT_t = prove(`word_zx(word_zx(w:int32):int64):int32 = w`, CONV_TAC WORD_BLAST);;
let dstep_t k = gkeepN REDSETX_DEC DEC256_EXEC ("s"^string_of_int k) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                              ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;

(* BASE nonce-lane derivation: drain_bridge carries the FULL bytes128 sp+160 block (= rev8(ctr_block(4*(lc-1)+2)));
   tail_inv 0 wants the two counter-INDEPENDENT nonce sub-lanes (bytes64@+0 -> subword(rev8(ctr_block 2))(0,64),
   bytes32@+8 -> subword(..)(64,32)).  Derive them at s0 via B64_OF_B128_LO / B32_OF_B128_MID (lane = subword of
   enclosing block) + SUBW_LO_CI / SUBW_MID_CI (nonce lanes are counter-independent -> canonicalize ctr to 2), then
   STRIP_ASSUME so they survive the 4 non-storing setup steps (ldr q12/q13/q14, cbz) into s4. *)
let TAIL_BASE_LANES : tactic =
  SUBGOAL_THEN
   `read (memory :> bytes64 (word_add stackpointer (word 160))) s0 =
      word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
    read (memory :> bytes32 (word_add stackpointer (word 168))) s0 =
      word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[B64_OF_B128_LO] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBW_LO_CI] THEN CONV_TAC WORD_BLAST;
      REWRITE_TAC[WORD_RULE `word_add stackpointer (word 168):int64 =
                             word_add (word_add stackpointer (word 160)) (word 8)`] THEN
      REWRITE_TAC[B32_OF_B128_MID] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBW_MID_CI] THEN CONV_TAC WORD_BLAST];
    ALL_TAC];;

(* tail counter merge @ sK: fold read(bytes128 sp+160)sK = rev8(ctr_block(4*loop_count+i+2)) from the nonce lanes
   (bytes64@+0, bytes32@+8) carried in tail_inv + the fresh +12 counter word.  MCP-VALIDATED @s6. *)
let TAIL_CTR_MERGE sK : tactic =
  let sp128 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_t 160; mk_var(sK,`:armstate`)] splitL) in
  let sp64  = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_t 168; mk_var(sK,`:armstate`)] splitL2) in
  SUBGOAL_THEN (subst [mk_var(sK,`:armstate`),`s:armstate`]
     `read (memory :> bytes128 (word_add stackpointer (word 160))) s =
      word_reversefields 8 (ctr_block nonce (4 * loop_count + i + 2))`) ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [sp128; sp64] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST; ALL_TAC];;

(* PLAIN stepper (no gkeepN pruning) for the tail.  The 1-block loop does NOT re-read htable, and gkeepN prunes the
   GHASH karatsuba-mid intermediates Q4/Q7/Q10 -> Q30's value dangles `read Q7 s34` unclosable.  Plain ARM_STEPS
   substitutes them fully into Q30.  Also FASTER here (17s vs 155s) -- gkeepN's per-step pruning over 55 steps is
   costly and the 1-block asl is small enough to not need it. *)
let dstep_plain k =
  ARM_STEPS_TAC DEC256_EXEC [k] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;

(* STRIP the 6-way htable_mem_4 conjunction (after RULE_ASSUM REWRITE[htable_mem_4]) into 6 individual reads so
   ARM_STEP advances each to the final state (else they stay folded at s0 and the htable_mem_4 conjunct can't close).
   Mirrors DRAIN's setup.  Requires the tail_hyps `nonoverlapping (htable_p,192)(sp+160,64)` so the reads cross the
   counter store.  *)
let TAIL_HTABLE_STRIP : tactic =
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) &&
      (contains "h_power" (string_of_term(concl th)) && contains "htable_p" (string_of_term(concl th)))
    then STRIP_ASSUME_TAC th else NO_TAC);;

(* --- STEP closers --- *)
let TAIL_X9_CLOSE : tactic =    (* word_sub(word(loop_remain-i))(word 1) = word(loop_remain-(i+1)) *)
  SUBGOAL_THEN `word_sub (word (loop_remain - i)) (word 1):int64 = word ((loop_remain - i) - 1)`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
     [REFL_TAC;
      FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[VAL_WORD_1] THEN UNDISCH_TAC `i < loop_remain` THEN ARITH_TAC];
    AP_TERM_TAC THEN UNDISCH_TAC `i < loop_remain` THEN ARITH_TAC];;

(* Single-block GHASH-accumulate lemma (proven via GHASH_POLYVAL_ACC_BATCHED with the empty extra-list): the
   1-block analogue of SWP_GHASH_BRANCH2_256.  Use it to fold the settled 1-block reduce prop3(pmul(acc XOR blk)(h0))
   to nist_ghash..(m+1) once the machine tower is reconstructed. *)
let SWP_GHASH_BRANCH2_1BLK = prove
 (`polyval_reduce_prop3
     (word_pmul (word_xor (nist_ghash (aes256_cipher (word 0) rk) tag0
                              (list_of_seq (nist_input_block inblock) m))
                          (nist_input_block inblock m))
                (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0))
   = nist_ghash (aes256_cipher (word 0) rk) tag0
       (list_of_seq (nist_input_block inblock) (m+1))`,
  MP_TAC(ISPECL [`ghash_twist (aes256_cipher (word 0) rk)`; `[]:(int128)list`;
                 `nist_ghash (aes256_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) m):int128`;
                 `nist_input_block inblock m:int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `m + 1 = SUC m`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;
Printf.printf "MARKER: SWP_GHASH_BRANCH2_1BLK proven\n%!";;

(* Q30 1-block GHASH update.  half-swap(nist_ghash..(4lc+i)) XOR block(4lc+i) --one pmull reduce-->
   half-swap(nist_ghash..(4lc+i+1)).  Ported from the PROVEN enc-256 tail_ghash_close (identical machine tower;
   enc/dec differ only in the block: dec GHASHes the INPUT via nist_input_block).  PROVEN 2026-09-22.
   Structure (all algebraic, ~2.4s):
     byteswap128 + (64,128)-subword-join collapse -> MATCH_MP_TAC(join(sub x)=join(sub y) from x=y)
     -> ABBREV sofar/cipherblock/h/k -> TRANS through polyval_reduce_prop3(word_pmul(xor sofar cb) h):
       branch 1 (machine karatsuba tower = prop3(pmul..)):  PMUL_KARATSUBA_JOIN_ALT + byteswap + subword-conv
         + karatsuba_mid + INBLOCK_REASSEMBLE + GSYM nist_input_block (folds the byte tower to cipherblock)
         + POLYVAL_REDUCE_G2 + prop3-unfold + ABBREV w1 (=pmul(sub p1 0)(polyconst)) + EXPAND ks + WORD_SUBWORD_XOR
         + AC-unify the two reduce-pmul args (WORD_BITWISE_RULE on their args) + ABBREV w2 + drop asms + BITBLAST
         (only 5 free vars w1,w2,p1,p2,p3 -> 641 bool vars, tractable; blasting the raw pmul tower is NOT);
       branch 2 (prop3(pmul(xor sofar cb) h) = nist_ghash(i+1)):  EXPAND + SWP_GHASH_BRANCH2_1BLK. *)
let TAIL_Q30_CLOSE : tactic =
  REWRITE_TAC [byteswap128; WORD_BLAST
   `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
    word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  MAP_EVERY ABBREV_TAC
   [`sofar = (nist_ghash (aes256_cipher (word 0) rk) tag0
               (list_of_seq (nist_input_block inblock) (4 * loop_count + i)))`;
    `cipherblock = nist_input_block inblock (4 * loop_count + i)`;
    `h = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`;
    `k = karatsuba_mid h`] THEN
  TRANS_TAC EQ_TRANS `polyval_reduce_prop3 (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
  CONJ_TAC THENL
   [(* branch 1: machine karatsuba tower = prop3(pmul(xor sofar cb) h) *)
    REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    ASM_REWRITE_TAC[] THEN LET_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
    ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
    REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN
    ABBREV_TAC
     `w1 = (word_pmul:int64->int64->int128)
        (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
    REWRITE_TAC[polyval_reduce_prop3] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    (* ks was reintroduced by ASM_REWRITE (asm word_xor(xor p1 p2)p3 = ks); expand back + distribute *)
    (TRY(EXPAND_TAC "ks")) THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    (* AC-unify the two reduce-pmul args (they are XOR-rearrangements of the same 5 leaves) *)
    (fun (asl,w) ->
      let redp = filter (fun u->match u with
                   Comb(Comb(Const("word_pmul",_),_),Comb(Const("word",_),n)) when n=`13979173243358019584`->true|_->false)
                   (setify(find_terms (fun u->match u with Comb(Comb(Const("word_pmul",_),_),_)->true|_->false) w)) in
      match redp with
       [pm0; pm1] ->
         let getarg t = hd(snd(strip_comb t)) in
         (REWRITE_TAC[WORD_BITWISE_RULE(mk_eq(getarg pm1, getarg pm0))] ORELSE ALL_TAC) (asl,w)
      | _ -> ALL_TAC (asl,w)) THEN
    (* abstract the single remaining reduce-pmul to w2, drop the definitional asms, and bit-blast *)
    (fun (asl,w) ->
      let redp = setify(filter (fun u->match u with
                   Comb(Comb(Const("word_pmul",_),_),Comb(Const("word",_),n)) when n=`13979173243358019584`->true|_->false)
                   (find_terms (fun u->match u with Comb(Comb(Const("word_pmul",_),_),_)->true|_->false) w)) in
      match redp with
       [pm] -> ABBREV_TAC (mk_eq(mk_var("w2",type_of pm), pm)) (asl,w)
      | _ -> ALL_TAC (asl,w)) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC BITBLAST_RULE;
    (* branch 2: prop3(pmul(xor sofar cb) h) = nist_ghash(i+1) *)
    MAP_EVERY EXPAND_TAC ["sofar"; "cipherblock"; "h"] THEN
    REWRITE_TAC[ARITH_RULE `4 * loop_count + i + 1 = (4 * loop_count + i) + 1`] THEN
    MATCH_ACCEPT_TAC SWP_GHASH_BRANCH2_1BLK];;

(* Tail 1-block out-store keystream fold: FULL AES-256 tower on the resident rev8(ctr_block(4lc+i+2)) (merged @s5).
   XOR_AES256_CIPHER_RECONSTRUCT_DEC folds the machine tower -> rev8(aes256_cipher(ctr_block..)) = aes_ctr_block. *)
let TAIL_OUT_BLOCK : tactic =
  REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes_ctr_block] THEN
  REWRITE_TAC[ARITH_RULE `(4 * loop_count + i) + 2 = 4 * loop_count + i + 2`] THEN
  REFL_TAC;;

(* Tail out-frame extension (1 new block): j<4lc+i+1 <=> j<4lc+i \/ j=4lc+i.  Old sub-frame = incoming invariant
   (ASM-accept the forall); new block j=4lc+i -> the stored decrypted block (TAIL_OUT_BLOCK). *)
let TAIL_OUT_FRAME : tactic =
  REWRITE_TAC[ARITH_RULE `j < 4 * loop_count + i + 1 <=>
                          j < 4 * loop_count + i \/ j = 4 * loop_count + i`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * loop_count + i) = 64 * loop_count + 16 * i`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (FIRST_X_ASSUM (fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) with _->false)
                                then MATCH_ACCEPT_TAC th else NO_TAC)) THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN TAIL_OUT_BLOCK;;

(* Per-conjunct STEP router (post ENSURES_FINAL + ASM_REWRITE).  gkeepN resolves Q30 to the machine value, so the
   Q30 conjunct's RHS holds nist_ghash..(4lc+i+1) (target) and its LHS is the settled machine reduce -> route by
   `nist_ghash` to TAIL_Q30_CLOSE.  NB TAIL_Q30_CLOSE is NOT in the FIRST[] fallback (it partially applies + leaves
   the reduce subgoal on non-Q30 conjuncts). *)
let TAIL_STEP_CLOSE : tactic = fun (asl,w) ->
  let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
  if is_forall w && free_in `out_p:int64` w then TAIL_OUT_FRAME (asl,w)
  else if is_forall w && free_in `in_p:int64` w then ASM_REWRITE_TAC[] (asl,w)
  else if has "htable_mem_4" w then ASM_REWRITE_TAC[htable_mem_4] (asl,w)
  else if is_eq w && has "nist_ghash" w then TAIL_Q30_CLOSE (asl,w)  (* Q30 settled machine reduce *)
  else FIRST
    [ (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);                        (* X0/X2 ptr *)
      (REWRITE_TAC[ZX_WT_t] THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);  (* X13 *)
      TAIL_X9_CLOSE;                                                        (* X9 *)
      close_frame_dec;                                                      (* MAYCHANGE *)
      (ASM_REWRITE_TAC[htable_mem_4]) ] (asl,w);;

let TAIL_DIAG = false;;  (* STEP Q30 reduce now closes (TAIL_Q30_CLOSE ported from enc-256); DIAG off *)
let tail_diag_counter = ref 0;;
let CLOSE_TAIL_STEP_DIAG : tactic = fun (asl,w) ->
  let hd t = try fst(dest_const(fst(strip_comb t))) with _->"?" in
  let lh = if is_eq w then hd(lhs w) else (if is_forall w then "forall" else hd w) in
  let res = try Some(TAIL_STEP_CLOSE (asl,w)) with _ -> None in
  let rgls = (match res with Some(_,g,_) -> map snd g | None -> [w]) in
  let dump_fail () =
    (print_types_of_subterms := 2;
     let d = String.concat "\n--\n" (map string_of_term rgls) in
     print_types_of_subterms := 0;
     let oc = open_out (Printf.sprintf "/tmp/dec256_tail_fail_%02d.txt" !tail_diag_counter) in
     output_string oc (Printf.sprintf "[FAIL lh=%s]\n%s\n" lh d); close_out oc) in
  (match res with Some((_,[],_) as r) -> r
   | _ -> (incr tail_diag_counter;
           (try dump_fail () with _ -> ());
           Printf.printf "TAIL-STEP-FAIL %02d [lh=%s]\n%!" !tail_diag_counter lh;
           CHEAT_TAC (asl,w)));;

(* ---- ivec-canonical support (2026-09-24): produce the FULL bytes128 ivec post (not bytes32(ivec+12)).
   IVEC_SPLIT_TAIL: after ENSURES_INIT, split the drain_bridge ivec read `bytes128 ivec = wrf(ctr_block nonce 2)`
   into 4-byte cells (READ_MEMORY_SPLIT_CONV 2, recursive) so the 3 low nonce cells (ivec+0/+4/+8) survive the
   counter writeback (str w14,[x4,#12] touches ONLY ivec+12).  Mirrors dec-128 keep_htable_swp.ml:3916.
   IVEC_RECOMB_TAIL: at the final state, split the GOAL ivec the same way + rewrite the 3 nonce cells from the
   surviving split-precond cells + the +12 counter cell (already in asm) + ctr_block + WORD_BLAST.  ctr_block
   nonce k shares the low 96 bits for all k, so nonce cells of ..(nblocks+2) match those of ..2.  VALIDATED
   synthetically (SYNTH_IVEC, cont53e). ---- *)
let IVEC_SPLIT_TAIL : tactic =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (fun th -> let c = concl th in
      is_eq c && free_in `ivec_p:int64` (lhs c) &&
      not(free_in `out_p:int64` (lhs c)) && not(free_in `in_p:int64` (lhs c)) &&
      not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)) &&
      not(free_in `key_p:int64` (lhs c)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)));;
(* per-cell rewrites: the 3 nonce cells of ctr_block nonce (nblocks+2) equal those of ctr_block nonce 2
   (k-independence -- low 96 bits are the nonce), and the counter cell (bits 96-127) = word_bytereverse(word(nblocks+2)).
   Each proven by REWRITE[ctr_block] + WORD_BLAST (symbolic nblocks OK -- ctr_block nonce K = word_join nonce (word K),
   nonce cells drop K, counter cell keeps word K under bytereverse). *)
let ivec_cell_rw = [
  prove(`!K. word_subword (word_subword (word_reversefields 8 (ctr_block nonce K):int128) (0,64):int64) (0,32):int32 =
         word_subword (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64) (0,32):int32`,
        GEN_TAC THEN REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);
  prove(`!K. word_subword (word_subword (word_reversefields 8 (ctr_block nonce K):int128) (0,64):int64) (32,32):int32 =
         word_subword (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64) (32,32):int32`,
        GEN_TAC THEN REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);
  prove(`!K. word_subword (word_subword (word_reversefields 8 (ctr_block nonce K):int128) (64,64):int64) (0,32):int32 =
         word_subword (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64) (0,32):int32`,
        GEN_TAC THEN REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);
  prove(`!K. word_subword (word_subword (word_reversefields 8 (ctr_block nonce K):int128) (64,64):int64) (32,32):int32 =
         word_bytereverse (word K:int32)`,
        GEN_TAC THEN REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST)];;
(* word_zx on the SAME width is the identity -- collapses the machine counter zx-tower (all int32 layers). *)
let WORD_ZX_ID32 = prove(`!x:int32. word_zx x:int32 = x`, GEN_TAC THEN CONV_TAC WORD_BLAST);;
(* the machine counter cell zx-tower (4 int32 zx's around word_bytereverse) = word_bytereverse of the inner word. *)
let ZXTOWER_COLLAPSE_32 = prove
 (`word_zx (word_zx (word_bytereverse (word_zx (word_zx (c:int32):int32):int32):int32):int32):int32 =
   word_bytereverse c`, CONV_TAC WORD_BLAST);;
(* IVEC_RECON: the bytes128 ivec reconstruction (counter word ++ preserved low-96 nonce).  ONE-shot use only
   (its RHS has ctr_block nonce 2, self-matching -> a plain REWRITE loops -> stack overflow). *)
let IVEC_RECON = prove
 (`word_reversefields 8 (ctr_block nonce k):int128 =
   word_join (word_bytereverse (word (k):int32))
             (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,96):(96)word)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;
(* IVEC_RECOMB_TAIL (VALIDATED in MCP cont53h): rewrite goal RHS wrf(ctr_block(K)) via IVEC_RECON (one-shot), split
   goal + asm cells, collapse the counter zx-tower SURGICALLY (only the bytes32-ivec asms -- NOT a blanket
   RULE_ASSUM which recurses into the Q30 tower -> overflow), ASM_REWRITE, then fold the symbolic counter index
   K -> nblocks+2 (AP_TERM_TAC + ASM_ARITH, assoc-robust: 4lc+lr+2 parses right-assoc so plain SUBST misses it),
   per-cell WORD_BLAST. *)
(* kidx = the ivec counter index in the GOAL (from tail_post ivec = wrf(ctr_block nonce kidx)): nblocks+2 for g4,
   4*loop_count+2 for degen.  All symbolic counter words in the split cells get folded to `word kidx` via ASM_ARITH. *)
let IVEC_RECOMB_TAIL (kidx:term) : tactic =
  TRY(GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [IVEC_RECON]) THEN
  CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  W(fun (asl,w) ->
     let ivec_cells = filter (fun (_,th) -> let c = concl th in
        try is_eq c && free_in `ivec_p:int64` (lhs c) &&
            can (find_term (fun t -> is_const t && fst(dest_const t)="bytes32")) (lhs c)
        with _ -> false) asl in
     let normed = map (fun (_,th) -> REWRITE_RULE
        [ZXTOWER_COLLAPSE_32; WORD_ZX_ID32; ZX_WT_t; ADD_CLAUSES; MULT_CLAUSES] th) ivec_cells in
     REWRITE_TAC normed) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ctr_block] THEN
  W(fun (asl,w) ->
     let ktm = mk_comb(`word:num->int32`,kidx) in
     let idxs = setify(find_terms (fun t -> match t with
        Comb(Const("word",_),e) when (try type_of t = `:int32` with _->false) && not(is_numeral e) && not(t = ktm) -> true | _ -> false) w) in
     EVERY (map (fun t ->
        SUBGOAL_THEN (mk_eq(t, ktm)) (fun th -> REWRITE_TAC[th]) THENL
         [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC]) idxs)) THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;;

(* ---- writeback per-conjunct dispatcher (shape-routed): ivec bytes128 -> IVEC_RECOMB_TAIL; tag (nist_ghash RHS)
   -> ABBREV gv + WORD_BLAST; MAYCHANGE -> close_frame_dec; else ASM_REWRITE.  SHAPE-ROUTED so WORD_BLAST never
   hits the wrong (huge) conjunct.  `mgv` = the settled-GHASH index (4*loop_count for degen, nblocks for g4). ---- *)
let TAIL_WB_CLOSE (mgv:term) : tactic = fun (asl,w) ->
  let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
  if not(is_eq w) then
    (if has "MAYCHANGE" w then close_frame_dec (asl,w)
     else if is_forall w then ASM_REWRITE_TAC[] (asl,w)
     else ASM_REWRITE_TAC[] (asl,w))
  else if free_in `ivec_p:int64` (lhs w) && has "bytes128" (lhs w) then
    IVEC_RECOMB_TAIL (mk_binary "+" (mgv, `2`)) (asl,w)
  else if has "nist_ghash" (rhs w) then
    (* resolve the tag read to its machine byteswap tower (ASM_REWRITE) FIRST, then ABBREV the settled GHASH gv
       and WORD_BLAST the byteswap reassembly.  (WORD_BLAST can't prove an unresolved `read(...) = ...`.) *)
    (ASM_REWRITE_TAC[] THEN
     ABBREV_TAC(mk_eq(`gv:int128`,
        list_mk_comb(`nist_ghash:int128->int128->(int128)list->int128`,
          [`aes256_cipher (word 0) rk:int128`; `tag0:int128`;
           mk_comb(`list_of_seq (nist_input_block inblock):num->(int128)list`, mgv)]))) THEN
     CONV_TAC WORD_BLAST) (asl,w)
  else (ASM_REWRITE_TAC[] ORELSE CONV_TAC WORD_BLAST) (asl,w);;

(* ---- tail_tac: degenerate(loop_remain=0) | WHILE(loop_remain>0). ---- *)
let TAIL_DEGEN : tactic =
  POP_ASSUM SUBST_ALL_TAC THEN ENSURES_INIT_TAC "s0" THEN IVEC_SPLIT_TAIL THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  SUBGOAL_THEN `nblocks = 4 * loop_count` SUBST_ALL_TAC THENL
   [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `nblocks MOD 4 = 0`] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY dstep_t (1--9) THEN ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN TAIL_WB_CLOSE `4 * loop_count`;;

let tail_tac : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[fst DEC256_EXEC] THEN
  ASM_CASES_TAC `loop_remain = 0` THENL
   [TAIL_DEGEN;
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0x6d0` `pc + 0x7ac` tail_inv THEN
    REPEAT CONJ_TAC THENL
     [(* g0 *) ASM_REWRITE_TAC[];
      (* g1 BASE: drain_bridge -> tail_inv 0 *)
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      TAIL_BASE_LANES THEN
      MAP_EVERY dstep_t (1--3) THEN
      SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
      dstep_t 4 THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; htable_mem_4];
      (* g2 STEP: tail_inv i -> tail_inv(i+1).  gkeepN stepping (dstep_t) -- keeps Q30 (the loop-carried GHASH acc)
         resolved to its machine value at s55; PLAIN ARM_STEPS drops the dead ext-v30 write.  htable individual reads
         are kept by gkeepN's anchored clause + advanced across the counter store by the sp-nonoverlaps in tail_hyps.
         Counter merge @s5 (post counter-store, matching the keystream's ldr q5,[sp,#160] read). *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16 * i)))) s0 = inblock (4 * loop_count + i)`
      ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `nblocks MOD 4 = loop_remain`; `i < loop_remain`] THEN ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY dstep_t (1--5) THEN TAIL_CTR_MERGE "s5" THEN MAP_EVERY dstep_t (6--55) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN (if TAIL_DIAG then CLOSE_TAIL_STEP_DIAG else TAIL_STEP_CLOSE);
      (* g3 back-edge: cbnz x9@0x7ac (1 instr), x9=word(loop_remain-(i+1)) != 0 for i+1<loop_remain -> 0x6d0. *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
      ARM_STEPS_TAC DEC256_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
      SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < loop_remain ==> ~(loop_remain = i)`];
      (* g4 EXIT: tail_inv loop_remain @0x7ac (cbnz not taken) -> tail_post @0x7c4 (writeback: mov/rev64/str-tag/
         rev/str-ctr = 5 instrs after cbnz, step 1--6).  tag via WORD_BLAST; ivec recompose (IVEC_RECOMB_TAIL);
         out-frame = the invariant's s6 out-forall (4lc+lr=nblocks).  Split ivec at init so nonce cells survive. *)
      ENSURES_INIT_TAC "s0" THEN IVEC_SPLIT_TAIL THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN `4 * loop_count + loop_remain = nblocks` ASSUME_TAC THENL
       [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `nblocks MOD 4 = loop_remain`] THEN ARITH_TAC; ALL_TAC] THEN
      (* gkeepN stepping (prunes the Q30 tower); split ivec cells carried as memory reads. *)
      MAP_EVERY dstep_t (1--6) THEN ENSURES_FINAL_STATE_TAC THEN
      REPEAT CONJ_TAC THEN
      (* out-forall (j<nblocks): accept the invariant's s6 out-forall (4lc+lr=nblocks). *)
      TRY (FIRST_X_ASSUM(fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) &&
             contains "s6" (string_of_term(concl th)) with _->false) then MP_TAC th else NO_TAC) THEN
           ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      TAIL_WB_CLOSE `nblocks:num`]];;
Printf.printf "MARKER: tail_tac defined\n%!";;

let SWP_DEC256_TAIL = prove(tail_goal, tail_tac);;
Printf.printf "MARKER: SWP_DEC256_TAIL done (tail_diag_counter=%d)\n%!" !tail_diag_counter;;

(* ============================================================================ *)
(* P4: whole-function composition (SWPS_LEG1B + SWPS_FROM88) + SWP256_CORRECT +  *)
(* P5 SUBROUTINE wrapper.  Ported from DEVEL_dec256_P4_compose.ml (validated     *)
(* hyps=0) + DEVEL_dec256_P4_draft.ml (SWPS_LC0) + the enc-256 SWP sibling        *)
(* (aes_gcm_enc_kernel_256_x4_scalar_iv_mem_late_tag_scalar_rk_swp.ml 8244-8589). *)
(* Legs in scope: SWP_DEC256_FILL, SWP_DEC256_BODYLEG (tight), SWP_DEC256_DRAIN,  *)
(* SWP_DEC256_TAIL (= TAIL_NO2, canonical bytes128 ivec, no 2<=loop_count).       *)
(* ============================================================================ *)
Printf.printf "MARKER: starting P4 composition\n%!";;

(* ---- (a) loosened BODYLEG_L1 (i<loop_count-1) : re-prove using the in-scope tight machinery. ---- *)
let SWP_SUB_LEMMA_DEC_L1 = prove
 (`i < loop_count - 1
   ==> word_sub (word (loop_count - (i + 1))) (word 1):int64 = word (loop_count - ((i + 1) + 1))`,
  DISCH_TAC THEN SUBGOAL_THEN `loop_count - ((i+1)+1) = (loop_count - (i+1)) - 1 /\ 1 <= loop_count - (i+1)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `i < loop_count - 1` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[WORD_SUB; VAL_WORD_1] THEN
  REWRITE_TAC[GSYM VAL_WORD_1] THEN AP_TERM_TAC THEN UNDISCH_TAC `i < loop_count - 1` THEN ARITH_TAC);;

let body_goal_L1 = subst [`i < loop_count - 1`, `i < loop_count - 2`] body_goal_dec;;

let INPUT_SPLIT_TAC_dec_L1 =
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
     ARITH_RULE `16 * (4*i+6) = 64*i+96`; ARITH_RULE `16 * (4*i+7) = 64*i+112`]);;

let setup_tac_dec_L1 =
  STRIP_TAC THEN REWRITE_TAC[fst DEC256_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes_dec THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
   [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 1` THEN
    UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  INPUT_SPLIT_TAC_dec_L1 THEN
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) && (let s = string_of_term(concl th) in
      contains "h_power" s && contains "htable_p" s) then STRIP_ASSUME_TAC th else NO_TAC);;

let step_body_all_L1 =
  setup_tac_dec_L1 THEN
  IVEC_SPLIT_dec THEN
  SLOT_PRIME_E THEN
  (fun (asl,w) ->
     (MAP_EVERY (fun k ->
        gkeepN REDSETX_DEC DEC256_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                                 IN_P_ADDR_FOLD_CONV)) THEN
        (match filter (fun (kk,_,_) -> kk=k) merges_dec_fold with
         | (_,off,cval)::_ -> MERGE_CTR128_FOLD_E off cval ("s"^string_of_int k)
         | [] -> ALL_TAC))
       (1--193)) (asl,w)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                           IN_P_ADDR_FOLD_CONV));;

Printf.printf "MARKER: L1 machinery defined; proving SWP_DEC256_BODYLEG_L1\n%!";;
let SWP_DEC256_BODYLEG_L1 = prove(body_goal_L1,
  step_body_all_L1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC_L1] THEN
  REPEAT CONJ_TAC THEN CLOSE_DEC256);;
Printf.printf "MARKER: SWP_DEC256_BODYLEG_L1 done (loosened i<loop_count-1)\n%!";;

(* ---- (b) frame-widening infra (P4_compose 19-43) ---- *)
let swps_broad_frame =
  let _,ens = dest_imp drain_goal in last(snd(strip_comb ens));;
let widen_frame_to_broad th =
  let narrow = rand(concl th) in
  let subth = prove(list_mk_icomb "subsumed" [narrow; swps_broad_frame],
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
  MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subth th);;
let widen_leg leg =
  let vars,_ = strip_forall (concl leg) in
  let leg0 = SPEC_ALL leg in
  let pre = lhand(concl leg0) in
  let broad = DISCH pre (widen_frame_to_broad (UNDISCH leg0)) in
  GENL (if vars = [] then frees(concl broad) else vars) broad;;

let FILLLEG_BROAD = widen_leg SWP_DEC256_FILL;;
let DRAINLEG_BROAD = widen_leg SWP_DEC256_DRAIN;;
let BODYLEG_BROAD = widen_leg SWP_DEC256_BODYLEG_L1;;   (* loosened i<loop_count-1 *)
let fill_pre_state = el 1 (snd(strip_comb(snd(dest_imp fill_goal))));;
let while_inv = mk_gabs(`k:num`, mk_comb(swpS256_inv_dec, `k:num`));;

let gen_precond = list_mk_conj (filter (fun c -> c <> `2 <= loop_count`) (conjuncts(lhand fill_goal)));;
let mk_lcN_goal n = mk_imp(mk_conj(gen_precond, mk_eq(`loop_count:num`, mk_small_numeral n)),
    list_mk_icomb "ensures" [`arm`; fill_pre_state; drain_bridge; swps_broad_frame]);;

(* ---- (c) SWPS_LEG1B: fill_pre@0x2c -> drain_bridge@0x6c0, loop_count>=2 (folds LC2). (P4_compose 45-87) ---- *)
let swps_leg1b_goal = mk_imp(mk_conj(gen_precond, `2 <= loop_count`),
    list_mk_icomb "ensures" [`arm`; fill_pre_state; drain_bridge; swps_broad_frame]);;
let swps_leg1b_body =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x26c`
    (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swpS256_inv_dec,`0`))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC FILLLEG_BROAD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x570`
    (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swpS256_inv_dec,`loop_count - 1`))))) THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `loop_count - 1` `pc + 0x26c` `pc + 0x570` while_inv THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`2 <= loop_count`] THEN ARITH_TAC;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `4 * 0 + 2 = 2`; ARITH_RULE `64 * 0 + 32 = 32`;
                                  ARITH_RULE `4 * 0 = 0`; ARITH_RULE `64 * 0 = 0`; MULT_CLAUSES; ADD_CLAUSES]) THEN
      REWRITE_TAC[ARITH_RULE `4 * 0 + 2 = 2`; ARITH_RULE `4 * 0 + 3 = 3`; ARITH_RULE `4 * 0 + 4 = 4`;
                  ARITH_RULE `4 * 0 + 5 = 5`; ARITH_RULE `4 * 0 + 1 = 1`; ARITH_RULE `4 * 0 = 0`;
                  ARITH_RULE `64 * 1 = 64`; ARITH_RULE `64 * 0 = 0`; ARITH_RULE `64 * 0 + 32 = 32`;
                  MULT_CLAUSES; ADD_CLAUSES; LT] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      MATCH_MP_TAC BODYLEG_BROAD THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < loop_count - 1`; `2 <= loop_count`] THEN ARITH_TAC;
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
      SUBGOAL_THEN `val (word (loop_count - (k+1)):int64) = loop_count - (k+1)` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(loop_count - (k+1) = 0)` ASSUME_TAC THENL
       [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`k < loop_count - 1`; `2 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC DEC256_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN ASM_REWRITE_TAC[];
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC DRAINLEG_BROAD THEN ASM_REWRITE_TAC[]];;
let SWPS_LEG1B = prove(swps_leg1b_goal, REPEAT GEN_TAC THEN STRIP_TAC THEN swps_leg1b_body);;
Printf.printf "MARKER: SWPS_LEG1B proven\n%!";;

(* ---- (d) SWPS_LC0 (loop_count=0) : full tactic from P4_draft 326-386. ---- *)
let USHR_CHAIN_VAL = prove
 (`!lb. val(word lb:int64) = lb
        ==> val(word_ushr (word_ushr (word_ushr (word lb:int64) 3) 4) 2) = lb DIV 512`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC);;
let LC0_DIV = prove
 (`len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ loop_count = 0 ==> len_bits DIV 512 = 0`,
  STRIP_TAC THEN SUBGOAL_THEN `len_bits DIV 512 = loop_count` (fun th->ASM_REWRITE_TAC[th]) THEN
  MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN ASM_REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC);;
let X15_FOLD = prove
 (`!lb. lb < 2 EXP 64 ==> word_ushr (word lb:int64) 3 = word (lb DIV 8)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word lb:int64) = lb` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
  SUBGOAL_THEN `2 EXP 3 = 8` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `lb < 2 EXP 64` THEN ARITH_TAC);;
let USHR2_128 = prove
 (`!lb. lb < 2 EXP 64 ==> word_ushr (word_ushr (word lb:int64) 3) 4 = word (lb DIV 128)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word lb:int64) = lb` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
  SUBGOAL_THEN `2 EXP 3 = 8 /\ 2 EXP 4 = 16` (fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[DIV_DIV] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  UNDISCH_TAC `lb < 2 EXP 64` THEN ARITH_TAC);;
let X9_FOLD = prove
 (`!lb. lb < 2 EXP 64
    ==> word_and (word_ushr (word_ushr (word lb:int64) 3) 4) (word 3) = word ((lb DIV 128) MOD 4)`,
  GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[USHR2_128] THEN
  SUBGOAL_THEN `word 3:int64 = word (2 EXP 2 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val(word (lb DIV 128):int64) = lb DIV 128` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `lb < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  MATCH_MP_TAC(ARITH_RULE `x < 4 ==> x < 2 EXP 64`) THEN
  REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV);;
let NIST_GHASH_NIL = prove
 (`!h tag0 f. nist_ghash h tag0 (list_of_seq f 0) = tag0`, REWRITE_TAC[LIST_OF_SEQ; nist_ghash]);;
let SWPS_LC0_tac =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN REWRITE_TAC[fst DEC256_EXEC] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce 2)` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN DISCH_TAC THEN
  ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
  ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) && (let s = string_of_term(concl th) in
      contains "h_power" s && contains "htable_p" s) then STRIP_ASSUME_TAC th else NO_TAC) THEN
  KEY_EXPAND_TAC THEN
  MAP_EVERY (fun n -> gkeepN REDSETX_DEC DEC256_EXEC ("s"^string_of_int n)) (1--31) THEN
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `read X1 s31 = word loop_count` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `read X1 s31 = word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2`
      then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[word_ushr] THEN
    REWRITE_TAC[ASSUME `val(word len_bits:int64) = len_bits`] THEN
    MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) = 0` ASSUME_TAC THENL
   [MP_TAC(SPEC `len_bits:num` USHR_CHAIN_VAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC LC0_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  gkeepN REDSETX_DEC DEC256_EXEC "s32" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) = 0`]) THEN
  DISCARD_OLDSTATE_TAC "s32" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `64 * 0 = 0`; WORD_ADD_0; ARITH_RULE `4 * 0 + 2 = 2`; ARITH_RULE `4 * 0 = 0`;
              ARITH_RULE `4 * (0 - 1) + 2 = 2`] THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w) ->
    let ivjoin () = snd(List.find (fun (_,th)-> can (find_term (fun t->t=`word_reversefields 8 (ctr_block nonce 2)`)) (concl th)
                       && (try fst(dest_const(fst(strip_comb(lhs(concl th)))))="word_join" with _->false)) asl) in
    let is_mem_iv w = is_eq w && (try fst(dest_const(fst(strip_comb(rhs w))))="word_reversefields" with _->false)
                       && can(find_term(fun t->match t with Comb(Comb(Const("ctr_block",_),_),_)->true|_->false)) (rhs w) in
    if is_forall w then (REWRITE_TAC[LT] THEN GEN_TAC THEN REWRITE_TAC[]) (asl,w)
    else if is_mem_iv w then
      (GEN_REWRITE_TAC (LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
       CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[]) (asl,w)
    else if is_eq w && can(find_term(fun t->match t with Const("nist_ghash",_)->true|_->false)) w then
      (REWRITE_TAC[NIST_GHASH_NIL] THEN POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC WORD_BLAST) (asl,w)
    else if is_eq w && can(find_term(fun t->t=`ivhi:int64`)) (lhs w) then
      (REWRITE_TAC[MATCH_MP BASE_CTR_DEC (ivjoin())]) (asl,w)
    else if is_eq w && (try fst(dest_const(fst(strip_comb(lhs w))))="word_ushr" with _->false)
            && not(can(find_term(fun t->match t with Const("word_and",_)->true|_->false)) w) then
      ASM_SIMP_TAC[X15_FOLD] (asl,w)
    else if is_eq w && (try fst(dest_const(fst(strip_comb(lhs w))))="word_and" with _->false) then
      (ASM_SIMP_TAC[X9_FOLD] THEN AP_TERM_TAC THEN
       MAP_EVERY (fun t->TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `len_bits DIV 128 = nblocks`] THEN MESON_TAC[]) (asl,w)
    else ASM_REWRITE_TAC[] (asl,w));;
let SWPS_LC0 = prove(mk_lcN_goal 0, SWPS_LC0_tac);;
Printf.printf "MARKER: SWPS_LC0 proven (real)\n%!";;

(* ---- (e) SWPS_LC1 : the loop_count=1 degenerate leg (from DEVEL_dec256_lc1.ml, proven axiom-free 2026-09-25).
     Injected verbatim below (the swps_lc1_goal is mk_lcN_goal 1). ---- *)
let drain_bridge = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc`;
  `read PC s = word (pc + 0x6c0)`;
  `read X0 s = word_add in_p (word (64 * loop_count))`;
  `read X2 s = word_add out_p (word (64 * loop_count))`;
  `read X3 s = tag_p`; `read X4 s = ivec_p`; `read X6 s = htable_p`; `read SP s = stackpointer`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
  `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2)`;
  `read X13 s = word_zx (word (4 * loop_count + 2):int32):int64`;
  `read X15 s = word(len_bits DIV 8)`; `read X9 s = word loop_remain`;
  `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
  `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
  `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
  `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
  `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
  `read Q28 s = word_reversefields 8 (EL 10 rk)`; `read Q15 s = word_reversefields 8 (EL 11 rk)`;
  `read Q16 s = word_reversefields 8 (EL 12 rk)`; `read Q17 s = word_reversefields 8 (EL 13 rk)`;
  `read Q2 s = word_reversefields 8 (EL 14 rk)`;
  `read Q7 s = word 13979173243358019584`;
  `read Q30 s = word_join
     ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * loop_count))) (0,64)):int64)
     ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * loop_count))) (64,64)):int64)`;
  `htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s`;
  `read (memory :> bytes128 (word_add stackpointer (word 160))) s =
     word_reversefields 8 (ctr_block nonce (4 * (loop_count - 1) + 2))`;
  `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`;
  `!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes_ctr_block nonce rk j) (inblock j)`]);;

let swps_broad_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(tag_p:int64,16)] ,, MAYCHANGE [memory :> bytes(ivec_p:int64,16)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;

let gen_precond = list_mk_conj (filter (fun c -> c <> `2 <= loop_count`) (conjuncts fill_hyps));;
let swps_lc1_goal = mk_imp(mk_conj(gen_precond, `loop_count = 1`),
    list_mk_icomb "ensures" [`arm`; fill_pre; drain_bridge; swps_broad_frame]);;
Printf.printf "MARKER: swps_lc1_goal built\n%!";;

(* ---- LC1 reusable helper lemmas (from SWPS_LC0) ---- *)
let USHR_CHAIN_VAL = prove
 (`!lb. val(word lb:int64) = lb
        ==> val(word_ushr (word_ushr (word_ushr (word lb:int64) 3) 4) 2) = lb DIV 512`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC);;
let X15_FOLD = prove
 (`!lb. lb < 2 EXP 64 ==> word_ushr (word lb:int64) 3 = word (lb DIV 8)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word lb:int64) = lb` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
  SUBGOAL_THEN `2 EXP 3 = 8` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `lb < 2 EXP 64` THEN ARITH_TAC);;
let USHR2_128 = prove
 (`!lb. lb < 2 EXP 64 ==> word_ushr (word_ushr (word lb:int64) 3) 4 = word (lb DIV 128)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word lb:int64) = lb` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
  SUBGOAL_THEN `2 EXP 3 = 8 /\ 2 EXP 4 = 16` (fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[DIV_DIV] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  UNDISCH_TAC `lb < 2 EXP 64` THEN ARITH_TAC);;
let X9_FOLD = prove
 (`!lb. lb < 2 EXP 64
    ==> word_and (word_ushr (word_ushr (word lb:int64) 3) 4) (word 3) = word ((lb DIV 128) MOD 4)`,
  GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[USHR2_128] THEN
  SUBGOAL_THEN `word 3:int64 = word (2 EXP 2 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val(word (lb DIV 128):int64) = lb DIV 128` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `lb < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  MATCH_MP_TAC(ARITH_RULE `x < 4 ==> x < 2 EXP 64`) THEN
  REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ---- LC1 setup: ivec split + 4-block input pin (blocks 0..3; loop_count=1 => 3<nblocks; the fill
   prefetch-loads blocks 4..7 read arbitrary mem, never used for lc=1) + htable strip + KEY_EXPAND. ---- *)
let LC1_INPUT_SPLIT_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0))))  s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1))))  s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2))))  s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3))))  s0 = inblock 3`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `3 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC];;
let lc1_setup_tac =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN REWRITE_TAC[fst DEC256_EXEC] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce 2)` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN DISCH_TAC THEN
  ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
  ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
  LC1_INPUT_SPLIT_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) && (let s = string_of_term(concl th) in
      contains "h_power" s && contains "htable_p" s) then STRIP_ASSUME_TAC th else NO_TAC) THEN
  KEY_EXPAND_TAC;;

(* ---- LC1 guard (cbz@0xa8 step 32): val(ushr chain) = len_bits DIV 512 = loop_count = 1 != 0 -> falls through
   (loop_count=1 context; NOT the fill leg's 2<=loop_count).  Establishes the val facts, steps 32, collapses. ---- *)
let LC1_GUARD_TAC =
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `len_bits DIV 512 = loop_count` ASSUME_TAC THENL
   [UNDISCH_TAC `len_bits DIV 128 = nblocks` THEN UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) = loop_count` ASSUME_TAC THENL
   [MP_TAC(SPEC `len_bits:num` USHR_CHAIN_VAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  gkeepN REDSETX_FILL DEC256_EXEC "s32" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) = loop_count`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `loop_count = 1`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;
Printf.printf "MARKER: LC1 setup + guard tactics defined (VALIDATED in MCP through s32/cbz@0xa8)\n%!";;

(* ---- cbz@0x268 (step 144) TAKEN: for loop_count=1, after sub x1,x1,#1 @0x264 -> x1 = word_sub(word 1)(word 1)
   = word 0, so cbz count,Lloop_unrolled_start_postamble is TAKEN -> branch to 0x574.  (FILL_CBZ144 falls through
   for lc>=2 via SWP_SUB1_NE0; LC1 needs the TAKEN branch: val(word 0)=0 -> the if-cond picks the branch target.) *)
let LC1_CBZ268_TAKEN : tactic =
  (* step s144 (the cbz@0x268).  PC becomes a COND: if val(word_sub(ushr_chain)(word 1))=0 then word(pc+1396)=0x574
     else word(pc+620)=0x26c.  For loop_count=1: val(ushr_chain)=loop_count=1 (LC1_GUARD_TAC), so
     word_sub(word 1)(word 1)=word 0, val=0 -> the COND picks 0x574 (TAKEN).  Resolve it before continuing. *)
  gkeepN REDSETX_FILL DEC256_EXEC "s144" THEN
  (* establish val(word_sub(ushr_chain)(word 1)) = 0 (the cbz condition), from val(ushr_chain)=loop_count=1 *)
  SUBGOAL_THEN `val(word_sub (word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) (word 1)) = 0`
    ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
    ASM_REWRITE_TAC[ASSUME `val(word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) = loop_count`;
                    ASSUME `loop_count = 1`] THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) (word 1)) = 0`]) THEN
  REWRITE_TAC[ASSUME `val(word_sub (word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) (word 1)) = 0`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `loop_count = 1`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;

(* ---- LC1 full tactic (candidate; native-iterated).  fill-prefix (validated 1..80) + guard + rest of fill +
   cbz-TAKEN + drain-postamble stepping (steps 145..227 = 0x574..0x6c0, reuse the DRAIN schedule: no merges,
   gkeepN REDSETX_DEC) + CLOSE_DRAIN closers (the dec256 master dispatcher settles Q30 = half-swap nist_ghash..4,
   out-forall j<4, staged ctr, etc.).  drain_bridge @ loop_count=1: 4*loop_count=4, loop_count-1=0.
   NB the state at 0x574 from the fill-prefix must match the drain-postamble's entry expectations -- the native
   run's ENSURES_FINAL + CLOSE_DRAIN will surface any mismatch (DIAG). ---- *)
(* LC1 Q30 settled-reduce identity: SWP_GHASH_BRANCH2_256 @ i=0, NUM-reduced + nist_ghash..0=tag0 folded.
   Closes the settled 4-block Horner reduce = nist_ghash..4 (acc=tag0). *)
let NIST_GHASH_NIL = prove
 (`!h tag0 f. nist_ghash h tag0 (list_of_seq f 0) = tag0`, REWRITE_TAC[LIST_OF_SEQ; nist_ghash]);;
let LC1_BR0N =
  REWRITE_RULE[ARITH_RULE `4*0=0`; ARITH_RULE `4*0+1=1`; ARITH_RULE `4*0+2=2`; ARITH_RULE `4*0+3=3`;
               ARITH_RULE `4*0+4=4`; NIST_GHASH_NIL]
    (SPEC `0` (GEN `i:num` SWP_GHASH_BRANCH2_256));;
let lc1_diag_counter = ref 0;;
(* per-conjunct DIAG closer: try CLOSE_DEC256; on exception dump the goal + CHEAT so the run surfaces
   ALL failing conjuncts (find the dest_eq culprit / state-mismatch). *)
(* LC1 out-forall closer: goal `!j. j < 4*1 ==> read(out_p+16*j) s227 = word_xor(aes_ctr_block j)(inblock j)`.
   Split j<4 into j=0/1/2/3, unwind, resolve each out-store read (ASM_REWRITE), then fold via LC1_OUT_BLOCK
   (aes_ctr_block unfold + KEYSTREAM_FOLD256 @ literal counter c=j+2).  VALIDATED (block-0) in MCP. *)
let rk15_lc1 = `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
                 EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk`;;
(* per-block out closer: the goal (after read-resolve) is word_xor (read in_p sK) (word_xor rk14 (aese-tower over
   ctr_block nonce (j+2))) = word_xor (wrf(aes256_cipher(ctr_block nonce (j+2)) rk)) (inblock j).  INFOLD folds the
   in_p read -> inblock j; then OUT_BLOCK_CLOSE_dec (XOR_AES256_CIPHER_RECONSTRUCT_DEC + MAP + rk-list + REFL). *)
(* out-store block j: fold read->inblock (ASM_REWRITE), unfold RHS aes_ctr_block (-> wrf(aes256_cipher(ctr_block
   nonce (j+2)) rk)), reduce j+2, fold LHS aese-tower via XOR_AES256_CIPHER_RECONSTRUCT_DEC + double-rev + MAP +
   rk-list.  VALIDATED (blocks 0 + 1) in MCP: both sides collapse to wrf(aes256_cipher(ctr_block nonce (j+2)) rk)
   XOR inblock j -> REFL via ASM_REWRITE. *)
let LC1_OUT_BLOCK : tactic =
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes_ctr_block] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[];;
let LC1_OUT_FRAME : tactic =
  REWRITE_TAC[ARITH_RULE `4 * 1 = 4`] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN LC1_OUT_BLOCK;;
let LC1_CONJ_CLOSE : tactic = fun (asl,w) ->
  let ghd t = try fst(dest_const(fst(strip_comb t))) with _ -> "?" in
  let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
  let lh = if is_eq w then ghd(lhs w) else (if is_forall w then "forall" else ghd w) in
  if is_forall w && free_in `out_p:int64` w then
    (try LC1_OUT_FRAME (asl,w) with e ->
       (incr lc1_diag_counter;
        (try let oc = open_out (Printf.sprintf "/tmp/dec256_lc1_fail_%02d.txt" !lc1_diag_counter) in
             output_string oc (Printf.sprintf "[OUTFRAME EXN %s]\n%s\n" (Printexc.to_string e) (string_of_term w));
             close_out oc with _ -> ());
        Printf.printf "LC1 OUTFRAME EXN %02d: %s\n%!" !lc1_diag_counter (Printexc.to_string e); CHEAT_TAC (asl,w)))
  else
  (* shape-route the LC1-specific register/counter conjuncts BEFORE CLOSE_DEC256 (whose body-leg dispatch
     doesn't fire on them): X15 (word_ushr len_bits), X9 (word_and ushr), X13 (word_zx counter base). *)
  if is_eq w && lh = "word_ushr" then
    (* X15: word_ushr(word len_bits)3 = word(len_bits DIV 8) *)
    ((ASM_SIMP_TAC[X15_FOLD] ORELSE (MATCH_MP_TAC X15_FOLD THEN ASM_ARITH_TAC) ORELSE CLOSE_DEC256) (asl,w))
  else if is_eq w && lh = "word_and" then
    (* X9: word_and(ushr ushr)(word 3) = word loop_remain (=nblocks MOD 4 = (len_bits DIV 128) MOD 4).
       Substitute loop_remain <- nblocks MOD 4 <- (len_bits DIV 128) MOD 4 (via the defining eqs, NOT ARITH). *)
    ((SUBGOAL_THEN `loop_remain = (len_bits DIV 128) MOD 4` SUBST1_TAC THENL
       [FIRST_ASSUM(fun th -> if concl th = `nblocks MOD 4 = loop_remain` then REWRITE_TAC[SYM th] else NO_TAC) THEN
        FIRST_ASSUM(fun th -> if concl th = `len_bits DIV 128 = nblocks` then REWRITE_TAC[th] else NO_TAC);
        ASM_SIMP_TAC[X9_FOLD]]) (asl,w))
  else if is_eq w && lh = "word_zx" then
    (* X13 counter: word_zx(word_add(word_bytereverse(word_zx(word_ushr ivhi 32)))(word 4)) = word_zx(word(4*1+2)).
       Fold the base word_bytereverse(word_zx(word_ushr ivhi 32)) -> word 2 (BASE_CTR_DEC via the ivhi/ivlo join),
       then word_add(word 2)(word 4) = word 6 = word(4*1+2), collapse word_zx via WORD_BLAST. *)
    ((REWRITE_TAC[ARITH_RULE `4 * 1 + 2 = 6`] THEN
      (fun (a,ww) -> (REWRITE_TAC[MATCH_MP BASE_CTR_DEC (find_join a)]) (a,ww)) THEN
      CONV_TAC WORD_BLAST) (asl,w))
  else if is_eq w && has "nist_ghash" (rhs w) then
    (* Q30 settled reduce: goal = machine 4-block reduce (blocks read at old states s33/s37/s44/s126, embedding
       nist_ghash..0=tag0) = half-swap(nist_ghash..(4*(0+1))).  The blocks are RAW reads -> INFOLD_dec folds them to
       inblock first, then SWP_Q30_SEED_TAC (SWP_SUBWORD_JOIN_MID + DEC_GHASH_NORM + ASM + GSYM nist_input_block +
       SWP_Q30_SEED_FINISH) settles them at i:=0 (acc=nist_ghash..0=tag0 -> nist_ghash..4). *)
    (* Q30 settled reduce: the 4 block reads are already pinned to inblock 0..3 (global closing preamble); ASM_REWRITE
       folds them, then SWP_Q30_SEED_TAC (DEC_GHASH_NORM's INBLOCK_REASSEMBLE + GSYM nist_input_block) settles the
       reduce at i:=0 (acc=nist_ghash..0=tag0 -> nist_ghash..(4*(0+1))). *)
    (* fold blocks (ASM), settle via SWP_Q30_SEED_TAC to the word_join(subword(prop3(4-block Horner)))..= form,
       then close the settled reduce: wrf(wrf tag0)->tag0, 4*(0+1)->4, apply LC1_BR0N (BRANCH2_256@i=0). *)
    ((REWRITE_TAC[ARITH_RULE `4 * 1 = 4 * (0 + 1)`] THEN
      ASM_REWRITE_TAC[] THEN SWP_Q30_SEED_TAC THEN
      REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; ARITH_RULE `4 * (0 + 1) = 4`; LC1_BR0N] THEN
      TRY REFL_TAC) (asl,w))
  else
  try CLOSE_DEC256 (asl,w)
  with e ->
    (incr lc1_diag_counter;
     (try
        let oc = open_out (Printf.sprintf "/tmp/dec256_lc1_fail_%02d.txt" !lc1_diag_counter) in
        output_string oc (Printf.sprintf "[EXN %s lh=%s]\n%s\n" (Printexc.to_string e) lh (string_of_term w));
        close_out oc
      with _ -> ());
     Printf.printf "LC1 CLOSE EXN %02d [lh=%s]: %s\n%!" !lc1_diag_counter lh (Printexc.to_string e);
     CHEAT_TAC (asl,w));;
let swps_lc1_tac =
  lc1_setup_tac THEN
  (* fill steps 1..31 + mid-lane prime @ s23 *)
  (fun (asl,w) ->
    (MAP_EVERY (fun k ->
       gkeepN REDSETX_FILL DEC256_EXEC ("s"^string_of_int k) THEN
       RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
       (if k = 23 then fill_prime_mids "s23" else ALL_TAC))
      (1--31)) (asl,w)) THEN
  LC1_GUARD_TAC THEN
  (* fill body 33..143 (0xac..0x264) with the counter merges (same fill schedule) *)
  (fun (asl,w) ->
    (MAP_EVERY (fun k ->
       gkeepN REDSETX_FILL DEC256_EXEC ("s"^string_of_int k) THEN
       RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
       (match filter (fun (kk,_,_) -> kk=k) dec_fill_merges with
        | (_,off,cval)::_ -> MERGE_CTR128_FILL off cval ("s"^string_of_int k)
        | [] -> ALL_TAC))
      (33--143)) (asl,w)) THEN
  LC1_CBZ268_TAKEN THEN
  (fun g -> (Printf.printf "LC1: cbz@0x268 resolved, entering postamble\n%!"; ALL_TAC g)) THEN
  (* drain postamble: steps 145..227 (0x574..0x6c0), no merges, gkeepN REDSETX_DEC (DRAIN schedule). *)
  (fun (asl,w) ->
    (MAP_EVERY (fun k ->
       (fun g -> ((if k mod 20 = 0 then Printf.printf "LC1 postamble step %d\n%!" k); ALL_TAC g)) THEN
       gkeepN REDSETX_DEC DEC256_EXEC ("s"^string_of_int k) THEN
       RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)))
      (145--227)) (asl,w)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
  (fun g -> (Printf.printf "LC1: postamble stepped, ENSURES_FINAL\n%!"; ALL_TAC g)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (fun g -> (Printf.printf "LC1: FINAL done, closing conjuncts\n%!"; ALL_TAC g)) THEN
  (* pin the 4 group input-block reads (at their GHASH-input states s126/s44/s37/s33) to inblock 0..3 as
     ASSUMPTIONS, so BOTH the Q30 reduce and the out-store readbacks fold them via ASM_REWRITE.  3<nblocks from lc=1. *)
  SUBGOAL_THEN `3 < nblocks` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_RULE `~(4 = 0)`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 in_p) s126 = inblock 0 /\
     read (memory :> bytes128 (word_add in_p (word 16))) s44 = inblock 1 /\
     read (memory :> bytes128 (word_add in_p (word 32))) s37 = inblock 2 /\
     read (memory :> bytes128 (word_add in_p (word 48))) s33 = inblock 3`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `in_p:int64 = word_add in_p (word (16*0))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 16):int64 = word_add in_p (word (16*1))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 32):int64 = word_add in_p (word (16*2))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 48):int64 = word_add in_p (word (16*3))`)] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN LC1_CONJ_CLOSE;;
Printf.printf "MARKER: swps_lc1_tac defined (candidate -- native run to surface gaps)\n%!";;

(* NOTE (original TODO): the postamble 0x574..0x6c0 IS the DRAIN leg's postamble (proven in DEVEL_dec256_drainleg.ml
   drain_step_all steps 2..84 + CLOSE_DRAIN).  KEY UNKNOWN: whether the fill-prefix state at 0x574 matches the
   drain-postamble's entry (Q30 split half-swap form etc.).  If it diverges, LC1 needs a bridge lemma or the
   postamble stepping re-derived from the fill state.  Step counts: fill 1..143, cbz s144, postamble s145..s227
   (83 instrs = 0x574..0x6bc incl the b 0x6c0@0x6bc).  The single-group GHASH: Q30 seed = half-swap tag0 (nist_ghash
   ..0), the postamble reduces the group -> half-swap nist_ghash..4.  Native-iterated (Q30 reduce BITBLAST). *)

(* SUPERSEDED planning note:
   THEN postamble steps (0x574..0x6c0, ~83): the single-group drain -- GHASH reduce over blocks 0..3
   (ITER1_Q30_TAC-style: acc=tag0, 4 blocks -> nist_ghash..4), 4 output stores (RECON to [x2]) + counter
   increment (X13/staged sp+160 block).  NB CONFIRMED from .S: the postamble stores ONLY to [x2] (4 output
   blocks) -- NO [x4] (ivec) or [x3] (tag) writes (those are deferred to the TAIL writeback).  So drain_bridge's
   ivec = wrf(ctr_block nonce 2) UNCHANGED and tag = wrf 8 tag0 UNCHANGED -> NO ivec/tag recompose in LC1.
   THEN ENSURES_FINAL + drain_bridge closers (Q30 settled=half-swap nist_ghash..4, out-forall j<4=RECON,
   staged ctr @sp+160 = ctr_block nonce 2, X13 = word_zx(word 6), ivec/tag = ASM unchanged). *)
(* CONTEXT-MISMATCH NOTE (cont54): the standalone mk_lcN_goal uses defining-equation hyps (nblocks DIV 4 =
   loop_count, loop_count = 1) NOT abbreviations, so the FILL leg's fill_guard_facts / fill_setup_tac (which
   EXPAND_TAC "loop_count"/"nblocks") do NOT transfer directly.  SWPS_LC0 (P4_draft:333) handles this by using
   the USHR_CHAIN_VAL / LC0_DIV / X15_FOLD / X9_FOLD helper lemmas instead of EXPAND_TAC -- LC1 must follow the
   SWPS_LC0 register-setup pattern (X1=word loop_count via WORD_USHR_COMPOSE + val(word len_bits)=len_bits +
   nblocks DIV 4 = loop_count reasoning), with the guard resolved via loop_count=1.
   So the reusable fill STEPPING (gkeepN steps + MERGE_CTR128_FILL merges) transfers, but the guard/reg-setup
   FACTS must be rebuilt SWPS_LC0-style.  This is the bulk of LC1's remaining work + the postamble reduce.
   Plan: (1) SWPS_LC0-style setup+guard facts for the fill prefix; (2) gkeepN steps 1..143 (fill schedule);
   (3) cbz@0x268 TAKEN via loop_count=1 (x1 after sub = word_sub(word 1)(word 1)=word 0); (4) postamble
   0x574..0x6c0 stepping (~83, dec-128 ITER1 schedule adapted) + single-group Q30 reduce (ITER1_Q30_TAC port:
   PMUL_KARATSUBA_JOIN_ALT + POLYVAL_REDUCE_G2 + BITBLAST, acc=tag0 blocks 0..3) + 4 output RECON stores;
   (5) drain_bridge closers.  NATIVE-iterated (Q30 reduce BITBLAST). *)
Printf.printf "MARKER: LC1 scaffold ready\n%!";;

(* ---- DIAG prove: run swps_lc1_tac; if it leaves open subgoals, dump them to /tmp so we see the exact gap
   (esp. the 0x574 state-match / postamble closers).  Flip LC1_DIAG=false for the real axiom-free prove. ---- *)
let LC1_DIAG = false;;
Printf.printf "MARKER: starting swps_lc1 prove (DIAG=%b)\n%!" LC1_DIAG;;
let SWPS_LC1 =
  if LC1_DIAG then
    (try
       let (_,gls,_) = swps_lc1_tac ([],swps_lc1_goal) in
       Printf.printf "LC1 DIAG: %d open subgoal(s)\n%!" (List.length gls);
       let oldf = !print_types_of_subterms in print_types_of_subterms := 1;
       List.iteri (fun i (asl,g) ->
         let oc = open_out (Printf.sprintf "/tmp/dec256_lc1_open_%02d.txt" i) in
         output_string oc (Printf.sprintf "OPEN SUBGOAL %d (head=%s):\n%s\n"
           i (try fst(dest_const(fst(strip_comb(if is_eq g then lhs g else g)))) with _ -> if is_forall g then "forall" else "?")
           (string_of_term g));
         close_out oc;
         Printf.printf "  dumped subgoal %d\n%!" i) gls;
       print_types_of_subterms := oldf;
       (* return a placeholder so the file loads; NOT axiom-free -- DIAG only *)
       mk_thm([],swps_lc1_goal)
     with e -> (Printf.printf "LC1 DIAG: swps_lc1_tac raised %s\n%!" (Printexc.to_string e); mk_thm([],swps_lc1_goal)))
  else prove(swps_lc1_goal, swps_lc1_tac);;
Printf.printf "MARKER: swps_lc1 done (DIAG); HYPS=%d\n%!" (List.length(hyp SWPS_LC1));;

(* ---- (f) SWPS_FROM88: gen_precond -> tail_post@0x7c4, ALL loop_count (P4_compose 89-124). ---- *)
let from88_frame = last(snd(strip_comb(snd(dest_imp(concl(SPEC_ALL SWP_DEC256_TAIL))))));;
let widen_to_from88 th =
  let vars,_ = strip_forall (concl th) in
  let leg0 = SPEC_ALL th in
  let pre = lhand(concl leg0) in
  let ud = UNDISCH leg0 in
  let narrow = rand(concl ud) in
  let subth = prove(list_mk_icomb "subsumed" [narrow; from88_frame],
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
  let broad = DISCH pre (MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subth ud)) in
  GENL (if vars = [] then frees(concl broad) else vars) broad;;
let strip_aligned_pc abs =
  let s,body = dest_abs abs in
  let keep = filter (fun c ->
    not(can (find_term (fun t -> is_const t && fst(dest_const t)="aligned_bytes_loaded")) c)
    && not(can (find_term (fun t -> t = `read PC`)) c)) (conjuncts body) in
  mk_abs(s, list_mk_conj keep);;
let drain_bridge_body = strip_aligned_pc drain_bridge;;
let TAILLEG_FROM88 = widen_to_from88 SWP_DEC256_TAIL;;
let swps_from88_goal = mk_imp(gen_precond, list_mk_icomb "ensures" [`arm`; fill_pre_state; tail_post; from88_frame]);;
let swps_from88_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x6c0` drain_bridge_body THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `loop_count = 0` THENL
     [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC (widen_to_from88 SWPS_LC0) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `loop_count = 1` THENL
     [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC (widen_to_from88 SWPS_LC1) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL
     [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`~(loop_count=0)`;`~(loop_count=1)`] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC (widen_to_from88 SWPS_LEG1B) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC TAILLEG_FROM88 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC];;
let SWPS_FROM88 = prove(swps_from88_goal, swps_from88_tac);;
Printf.printf "MARKER: SWPS_FROM88 proven\n%!";;

(* ============================================================================ *)
(* SWP256_CORRECT: whole core function pc+0x2c -> pc+0x7c4.                      *)
(* Since fill_pre is at 0x2c and tail_post at 0x7c4, SWPS_FROM88 spans the       *)
(* entire core; the CORRECT preamble is just the round-key list split + a bridge *)
(* to fill_pre_state, then MATCH_MP_TAC SWPS_FROM88.  (Simpler than enc-256,     *)
(* which needed a 0x2c->0xb0 preamble step; dec-256's round-key loads live       *)
(* inside FILL.)                                                                 *)
(* ============================================================================ *)
Printf.printf "MARKER: proving SWP256_CORRECT...\n%!";;
(* The (stronger) from88 postcondition, extracted from SWPS_FROM88 directly (folded htable). *)
let swp_from88_post =
  el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl SWPS_FROM88)))))));;
let SWP256_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc /\
           read PC s = word (pc + 0x2c) /\
           read SP s = stackpointer /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           wordlist_from_memory(key_p,15) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = word (pc + 0x7c4) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + 2)) /\
           read X0 s = word (val len_bits DIV 8))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128)] ,,
       MAYCHANGE [memory :> bytes(tag_p, 16)] ,,
       MAYCHANGE [memory :> bytes(ivec_p, 16)] ,,
       MAYCHANGE [memory :> bytes(word_add stackpointer (word 160), 64)] ,,
       MAYCHANGE [events])`,
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst DEC256_EXEC] THEN
  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  (*** Weaken the goal postcondition to the (stronger) from88 postcondition FIRST, before the
       round-key case split, so both LENGTH branches share it.  (Validated interactively.) ***)
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC swp_from88_post THEN CONJ_TAC THENL
   [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (*** SWPS_FROM88 keeps rk abstract (wordlist_from_memory).  Case-split LENGTH rk = 15:
       - =15: derive the round-key list identity [EL 0 rk;...;EL 14 rk] = rk (from LENGTH via
         LENGTH_EQ_LIST_OF_SEQ, NO rk expansion), reconcile the C_ARGUMENTS-form precondition with
         fill_pre_state (ENSURES_PRECONDITION), then MATCH_MP_TAC SWPS_FROM88.
       - <>15: the wordlist_from_memory precondition forces LENGTH rk = 15, a contradiction, so the
         precondition is unsatisfiable -> ENSURES_PRECONDITION to (\s.F) + ENSURES_TRIVIAL. ***)
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 15` THENL
   [SUBGOAL_THEN
     `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
       EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk`
     ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
      CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
      CONV_TAC(LAND_CONV(RAND_CONV(TOP_DEPTH_CONV BETA_CONV))) THEN
      DISCH_THEN(ACCEPT_TAC o SYM); ALL_TAC] THEN
    ENSURES_PRECONDITION_TAC fill_pre_state THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC SWPS_FROM88 THEN
    REPEAT CONJ_TAC THEN
    FIRST[ ASM_REWRITE_TAC[] THEN NO_TAC;
           (MAP_EVERY UNDISCH_TAC [`len_bits < 2 EXP 64`; `len_bits DIV 128 = nblocks`] THEN ARITH_TAC);
           NONOVERLAPPING_TAC ];
    ENSURES_PRECONDITION_TAC `\s:armstate. F` THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> let c = concl th in
         if is_eq c && can (find_term (fun t -> is_const t && fst(dest_const t)="wordlist_from_memory")) c
         then MP_TAC(AP_TERM `LENGTH:int128 list->num` th) else NO_TAC) THEN
      REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ENSURES_TRIVIAL]]]);;
Printf.printf "MARKER: SWP256_CORRECT PROVEN, hyps %d\n%!" (List.length (hyp SWP256_CORRECT));;

(* ============================================================================ *)
(* P5 SUBROUTINE wrapper: lift SWP256_CORRECT through the 11-step save prologue  *)
(* and 11-step restore epilogue (D8-D15 + X19-X30, 224-byte frame).             *)
(* ============================================================================ *)
let KEY15_SPLIT = prove
 (`(wordlist_from_memory (key_p:int64,15) (s:armstate) =
    MAP (word_reversefields 8) (rk:int128 list)) <=>
   LENGTH rk = 15 /\
   read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
   read (memory :> bytes128 (word_add key_p (word 16))) s = word_reversefields 8 (EL 1 rk) /\
   read (memory :> bytes128 (word_add key_p (word 32))) s = word_reversefields 8 (EL 2 rk) /\
   read (memory :> bytes128 (word_add key_p (word 48))) s = word_reversefields 8 (EL 3 rk) /\
   read (memory :> bytes128 (word_add key_p (word 64))) s = word_reversefields 8 (EL 4 rk) /\
   read (memory :> bytes128 (word_add key_p (word 80))) s = word_reversefields 8 (EL 5 rk) /\
   read (memory :> bytes128 (word_add key_p (word 96))) s = word_reversefields 8 (EL 6 rk) /\
   read (memory :> bytes128 (word_add key_p (word 112))) s = word_reversefields 8 (EL 7 rk) /\
   read (memory :> bytes128 (word_add key_p (word 128))) s = word_reversefields 8 (EL 8 rk) /\
   read (memory :> bytes128 (word_add key_p (word 144))) s = word_reversefields 8 (EL 9 rk) /\
   read (memory :> bytes128 (word_add key_p (word 160))) s = word_reversefields 8 (EL 10 rk) /\
   read (memory :> bytes128 (word_add key_p (word 176))) s = word_reversefields 8 (EL 11 rk) /\
   read (memory :> bytes128 (word_add key_p (word 192))) s = word_reversefields 8 (EL 12 rk) /\
   read (memory :> bytes128 (word_add key_p (word 208))) s = word_reversefields 8 (EL 13 rk) /\
   read (memory :> bytes128 (word_add key_p (word 224))) s = word_reversefields 8 (EL 14 rk)`,
  CONV_TAC(LAND_CONV(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 15` THENL
   [FIRST_ASSUM(fun lenth -> MP_TAC(GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ] lenth)) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[MAP] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC] THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    REWRITE_TAC[LENGTH; LENGTH_MAP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;
Printf.printf "MARKER: KEY15_SPLIT proven\n%!";;

let AES_GCM_DEC_KERNEL_256_X4_SCALAR_IV_MEM2_LATE_TAG_SWP_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_256_x4_scalar_iv_mem2_late_tag_swp_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           wordlist_from_memory(key_p,15) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = returnaddress /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + 2)) /\
           read X0 s = word (val len_bits DIV 8))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  REWRITE_TAC[fst DEC256_EXEC; htable_mem_4; KEY15_SPLIT] THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    DEC256_EXEC
    (REWRITE_RULE[KEY15_SPLIT]
       (REWRITE_RULE[fst DEC256_EXEC; htable_mem_4] SWP256_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224);;
Printf.printf "MARKER: *** SWP256 SUBROUTINE CORRECT proven ***\n%!";;

Printf.printf "MARKER: axiom count = %d (expect 3: INFINITY/SELECT/ETA)\n%!" (List.length(axioms()));;
if List.length(axioms()) <> 3 then failwith "AXIOM LEAK: a CHEAT_TAC fired" else
Printf.printf "MARKER: *** SWP256 DEC CONSOLIDATION AXIOM-FREE ***\n%!";;
Printf.printf "MARKER: SWP256_CORRECT hyps=%d ; SUBROUTINE hyps=%d\n%!"
  (List.length(hyp SWP256_CORRECT))
  (List.length(hyp AES_GCM_DEC_KERNEL_256_X4_SCALAR_IV_MEM2_LATE_TAG_SWP_SUBROUTINE_CORRECT));;
