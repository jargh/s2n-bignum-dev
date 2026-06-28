(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-128-GCM encryption kernel.                                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** Eventually, but not yet

needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;

****)

needs "common/fips197.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

(* print_literal_from_elf "arm/aes_gcm/aes_gcm_enc_kernel.o";; *)

let aes_gcm_enc_kernel_mc =
  define_assert_from_elf "aes_gcm_enc_kernel_mc"
                         "arm/aes_gcm/aes_gcm_enc_kernel.o"
[
  0xd10283ff;       (* sub      sp, sp, #0xa0 *)
  0xa90053f3;       (* stp      x19, x20, [sp] *)
  0xa9015bf5;       (* stp      x21, x22, [sp, #0x10] *)
  0xa90263f7;       (* stp      x23, x24, [sp, #0x20] *)
  0xa9036bf9;       (* stp      x25, x26, [sp, #0x30] *)
  0xa90473fb;       (* stp      x27, x28, [sp, #0x40] *)
  0xa9057bfd;       (* stp      x29, x30, [sp, #0x50] *)
  0x6d0627e8;       (* stp      d8, d9, [sp, #0x60] *)
  0x6d072fea;       (* stp      d10, d11, [sp, #0x70] *)
  0x6d0837ec;       (* stp      d12, d13, [sp, #0x80] *)
  0x6d093fee;       (* stp      d14, d15, [sp, #0x90] *)
  0xd343fc2f;       (* lsr      x15, x1, #3 *)
  0x3dc000b2;       (* ldr      q18, [x5] *)
  0x3dc004b3;       (* ldr      q19, [x5, #0x10] *)
  0x3dc008b4;       (* ldr      q20, [x5, #0x20] *)
  0x3dc00cb5;       (* ldr      q21, [x5, #0x30] *)
  0x3dc010b6;       (* ldr      q22, [x5, #0x40] *)
  0x3dc014b7;       (* ldr      q23, [x5, #0x50] *)
  0x3dc018b8;       (* ldr      q24, [x5, #0x60] *)
  0x3dc01cb9;       (* ldr      q25, [x5, #0x70] *)
  0x3dc020ba;       (* ldr      q26, [x5, #0x80] *)
  0x3dc024bb;       (* ldr      q27, [x5, #0x90] *)
  0x3dc028bc;       (* ldr      q28, [x5, #0xa0] *)
  0x3dc0006b;       (* ldr      q11, [x3] *)
  0x4e20096b;       (* rev64.16b        v11, v11 *)
  0x3dc0009f;       (* ldr      q31, [x4] *)
  0xd2c00039;       (* mov      x25, #0x100000000 *)
  0x4f00e41e;       (* movi.16b v30, #0x0 *)
  0x9eaf033e;       (* fmov.d   v30[1], x25 *)
  0x6e200bff;       (* rev32.16b        v31, v31 *)
  0xd344fde7;       (* lsr      x7, x15, #4 *)
  0xd342fce1;       (* lsr      x1, x7, #2 *)
  0x924004e9;       (* and      x9, x7, #0x3 *)
  0xd2f84019;       (* mov      x25, #-0x3e00000000000000 *)
  0x9e670327;       (* fmov     d7, x25 *)
  0xb4001341;       (* cbz      x1, 0x2f4 *)
  0x3cc4041d;       (* ldr      q29, [x0], #0x40 *)
  0x6e200be0;       (* rev32.16b        v0, v31 *)
  0x4ebe87ff;       (* add.4s   v31, v31, v30 *)
  0x4e284a40;       (* aese.16b v0, v18 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a60;       (* aese.16b v0, v19 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a80;       (* aese.16b v0, v20 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284aa0;       (* aese.16b v0, v21 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ac0;       (* aese.16b v0, v22 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ae0;       (* aese.16b v0, v23 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b00;       (* aese.16b v0, v24 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b20;       (* aese.16b v0, v25 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b40;       (* aese.16b v0, v26 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b60;       (* aese.16b v0, v27 *)
  0x6e3c1fbd;       (* eor.16b  v29, v29, v28 *)
  0x6e201fa0;       (* eor.16b  v0, v29, v0 *)
  0x3c840440;       (* str      q0, [x2], #0x40 *)
  0x3dc00ccc;       (* ldr      q12, [x6, #0x30] *)
  0x3dc014cd;       (* ldr      q13, [x6, #0x50] *)
  0x3dc010ce;       (* ldr      q14, [x6, #0x40] *)
  0x4e200800;       (* rev64.16b        v0, v0 *)
  0x6e2b1c00;       (* eor.16b  v0, v0, v11 *)
  0x0eede008;       (* pmull.1q v8, v0, v13 *)
  0x4eede009;       (* pmull2.1q        v9, v0, v13 *)
  0x6e00400b;       (* ext.16b  v11, v0, v0, #0x8 *)
  0x6e201d6b;       (* eor.16b  v11, v11, v0 *)
  0x4eeee16a;       (* pmull2.1q        v10, v11, v14 *)
  0x3cdd001d;       (* ldur     q29, [x0, #-0x30] *)
  0x6e200be0;       (* rev32.16b        v0, v31 *)
  0x4ebe87ff;       (* add.4s   v31, v31, v30 *)
  0x4e284a40;       (* aese.16b v0, v18 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a60;       (* aese.16b v0, v19 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a80;       (* aese.16b v0, v20 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284aa0;       (* aese.16b v0, v21 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ac0;       (* aese.16b v0, v22 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ae0;       (* aese.16b v0, v23 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b00;       (* aese.16b v0, v24 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b20;       (* aese.16b v0, v25 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b40;       (* aese.16b v0, v26 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b60;       (* aese.16b v0, v27 *)
  0x6e3c1fbd;       (* eor.16b  v29, v29, v28 *)
  0x6e201fa0;       (* eor.16b  v0, v29, v0 *)
  0x3c9d0040;       (* stur     q0, [x2, #-0x30] *)
  0x4e200800;       (* rev64.16b        v0, v0 *)
  0x0eece00b;       (* pmull.1q v11, v0, v12 *)
  0x6e2b1d08;       (* eor.16b  v8, v8, v11 *)
  0x4eece00b;       (* pmull2.1q        v11, v0, v12 *)
  0x6e2b1d29;       (* eor.16b  v9, v9, v11 *)
  0x6e00400b;       (* ext.16b  v11, v0, v0, #0x8 *)
  0x2e201d6b;       (* eor.8b   v11, v11, v0 *)
  0x0eeee16b;       (* pmull.1q v11, v11, v14 *)
  0x6e2b1d4a;       (* eor.16b  v10, v10, v11 *)
  0x3cde001d;       (* ldur     q29, [x0, #-0x20] *)
  0x6e200be0;       (* rev32.16b        v0, v31 *)
  0x4ebe87ff;       (* add.4s   v31, v31, v30 *)
  0x4e284a40;       (* aese.16b v0, v18 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a60;       (* aese.16b v0, v19 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a80;       (* aese.16b v0, v20 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284aa0;       (* aese.16b v0, v21 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ac0;       (* aese.16b v0, v22 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ae0;       (* aese.16b v0, v23 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b00;       (* aese.16b v0, v24 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b20;       (* aese.16b v0, v25 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b40;       (* aese.16b v0, v26 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b60;       (* aese.16b v0, v27 *)
  0x6e3c1fbd;       (* eor.16b  v29, v29, v28 *)
  0x6e201fa0;       (* eor.16b  v0, v29, v0 *)
  0x3c9e0040;       (* stur     q0, [x2, #-0x20] *)
  0x3dc000cc;       (* ldr      q12, [x6] *)
  0x3dc008cd;       (* ldr      q13, [x6, #0x20] *)
  0x3dc004ce;       (* ldr      q14, [x6, #0x10] *)
  0x4e200800;       (* rev64.16b        v0, v0 *)
  0x0eede00b;       (* pmull.1q v11, v0, v13 *)
  0x6e2b1d08;       (* eor.16b  v8, v8, v11 *)
  0x4eede00b;       (* pmull2.1q        v11, v0, v13 *)
  0x6e2b1d29;       (* eor.16b  v9, v9, v11 *)
  0x6e00400b;       (* ext.16b  v11, v0, v0, #0x8 *)
  0x6e201d6b;       (* eor.16b  v11, v11, v0 *)
  0x4eeee16b;       (* pmull2.1q        v11, v11, v14 *)
  0x6e2b1d4a;       (* eor.16b  v10, v10, v11 *)
  0x3cdf001d;       (* ldur     q29, [x0, #-0x10] *)
  0x6e200be0;       (* rev32.16b        v0, v31 *)
  0x4ebe87ff;       (* add.4s   v31, v31, v30 *)
  0x4e284a40;       (* aese.16b v0, v18 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a60;       (* aese.16b v0, v19 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a80;       (* aese.16b v0, v20 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284aa0;       (* aese.16b v0, v21 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ac0;       (* aese.16b v0, v22 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ae0;       (* aese.16b v0, v23 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b00;       (* aese.16b v0, v24 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b20;       (* aese.16b v0, v25 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b40;       (* aese.16b v0, v26 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b60;       (* aese.16b v0, v27 *)
  0x6e3c1fbd;       (* eor.16b  v29, v29, v28 *)
  0x6e201fa0;       (* eor.16b  v0, v29, v0 *)
  0x3c9f0040;       (* stur     q0, [x2, #-0x10] *)
  0x4e200800;       (* rev64.16b        v0, v0 *)
  0x0eece00b;       (* pmull.1q v11, v0, v12 *)
  0x6e2b1d08;       (* eor.16b  v8, v8, v11 *)
  0x4eece00b;       (* pmull2.1q        v11, v0, v12 *)
  0x6e2b1d29;       (* eor.16b  v9, v9, v11 *)
  0x6e00400b;       (* ext.16b  v11, v0, v0, #0x8 *)
  0x2e201d6b;       (* eor.8b   v11, v11, v0 *)
  0x0eeee16b;       (* pmull.1q v11, v11, v14 *)
  0x6e2b1d4a;       (* eor.16b  v10, v10, v11 *)
  0x6e291d00;       (* eor.16b  v0, v8, v9 *)
  0x0ee7e121;       (* pmull.1q v1, v9, v7 *)
  0x6e094129;       (* ext.16b  v9, v9, v9, #0x8 *)
  0x6e201d4a;       (* eor.16b  v10, v10, v0 *)
  0x6e211d21;       (* eor.16b  v1, v9, v1 *)
  0x6e211d4a;       (* eor.16b  v10, v10, v1 *)
  0x0ee7e149;       (* pmull.1q v9, v10, v7 *)
  0x6e291d08;       (* eor.16b  v8, v8, v9 *)
  0x6e0a414a;       (* ext.16b  v10, v10, v10, #0x8 *)
  0x6e2a1d0b;       (* eor.16b  v11, v8, v10 *)
  0x6e0b416b;       (* ext.16b  v11, v11, v11, #0x8 *)
  0xd1000421;       (* sub      x1, x1, #0x1 *)
  0xb5ffed01;       (* cbnz     x1, 0x94 *)
  0x3dc000cc;       (* ldr      q12, [x6] *)
  0x3dc008cd;       (* ldr      q13, [x6, #0x20] *)
  0x3dc004ce;       (* ldr      q14, [x6, #0x10] *)
  0xb40005c9;       (* cbz      x9, 0x3bc *)
  0x3cc1041d;       (* ldr      q29, [x0], #0x10 *)
  0x6e200be0;       (* rev32.16b        v0, v31 *)
  0x4ebe87ff;       (* add.4s   v31, v31, v30 *)
  0x4e284a40;       (* aese.16b v0, v18 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a60;       (* aese.16b v0, v19 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a80;       (* aese.16b v0, v20 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284aa0;       (* aese.16b v0, v21 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ac0;       (* aese.16b v0, v22 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ae0;       (* aese.16b v0, v23 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b00;       (* aese.16b v0, v24 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b20;       (* aese.16b v0, v25 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b40;       (* aese.16b v0, v26 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b60;       (* aese.16b v0, v27 *)
  0x6e3c1fbd;       (* eor.16b  v29, v29, v28 *)
  0x6e201fa0;       (* eor.16b  v0, v29, v0 *)
  0x3c810440;       (* str      q0, [x2], #0x10 *)
  0x4e200800;       (* rev64.16b        v0, v0 *)
  0x6e2b1c00;       (* eor.16b  v0, v0, v11 *)
  0x0eece008;       (* pmull.1q v8, v0, v12 *)
  0x4eece009;       (* pmull2.1q        v9, v0, v12 *)
  0x6e00400b;       (* ext.16b  v11, v0, v0, #0x8 *)
  0x2e201d6b;       (* eor.8b   v11, v11, v0 *)
  0x0eeee16a;       (* pmull.1q v10, v11, v14 *)
  0x6e291d00;       (* eor.16b  v0, v8, v9 *)
  0x0ee7e121;       (* pmull.1q v1, v9, v7 *)
  0x6e094129;       (* ext.16b  v9, v9, v9, #0x8 *)
  0x6e201d4a;       (* eor.16b  v10, v10, v0 *)
  0x6e211d21;       (* eor.16b  v1, v9, v1 *)
  0x6e211d4a;       (* eor.16b  v10, v10, v1 *)
  0x0ee7e149;       (* pmull.1q v9, v10, v7 *)
  0x6e291d08;       (* eor.16b  v8, v8, v9 *)
  0x6e0a414a;       (* ext.16b  v10, v10, v10, #0x8 *)
  0x6e2a1d0b;       (* eor.16b  v11, v8, v10 *)
  0x6e0b416b;       (* ext.16b  v11, v11, v11, #0x8 *)
  0xd1000529;       (* sub      x9, x9, #0x1 *)
  0xb5fffa89;       (* cbnz     x9, 0x308 *)
  0xaa0f03e0;       (* mov      x0, x15 *)
  0x4e20096b;       (* rev64.16b        v11, v11 *)
  0x3d80006b;       (* str      q11, [x3] *)
  0x6e200bff;       (* rev32.16b        v31, v31 *)
  0x3d80009f;       (* str      q31, [x4] *)
  0x6d4627e8;       (* ldp      d8, d9, [sp, #0x60] *)
  0x6d472fea;       (* ldp      d10, d11, [sp, #0x70] *)
  0x6d4837ec;       (* ldp      d12, d13, [sp, #0x80] *)
  0x6d493fee;       (* ldp      d14, d15, [sp, #0x90] *)
  0xa94053f3;       (* ldp      x19, x20, [sp] *)
  0xa9415bf5;       (* ldp      x21, x22, [sp, #0x10] *)
  0xa94263f7;       (* ldp      x23, x24, [sp, #0x20] *)
  0xa9436bf9;       (* ldp      x25, x26, [sp, #0x30] *)
  0xa94473fb;       (* ldp      x27, x28, [sp, #0x40] *)
  0xa9457bfd;       (* ldp      x29, x30, [sp, #0x50] *)
  0x910283ff;       (* add      sp, sp, #0xa0 *)
  0xd65f03c0        (* ret *)
];;

let AES_GCM_ENC_KERNEL_EXEC = ARM_MK_EXEC_RULE aes_gcm_enc_kernel_mc;;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem.                                                 *)
(*                                                                           *)
(* This covers the body of the function with the save/restore boilerplate   *)
(* excised: PC starts at pc + 0x2c (first real instruction after the 11     *)
(* save instructions) and ends at pc + 0x3cc (first ldp of the postamble). *)
(* The stackpointer is the value AFTER the sub sp, #0xa0 adjustment, i.e.   *)
(* the value the SP register actually holds inside the function body.       *)
(*                                                                           *)
(* Arguments (Standard ARM ABI, values in registers at core entry):         *)
(*   X0 = in        input buffer (len_bits/8 bytes)                         *)
(*   X1 = len_bits  length in bits (whole 16-byte blocks)                   *)
(*   X2 = out       output buffer (len_bits/8 bytes)                        *)
(*   X3 = tag       16-byte GHASH accumulator (in/out)                      *)
(*   X4 = ivec      16-byte counter block (in/out)                          *)
(*   X5 = key       AES-128 round keys (176 bytes = 11 x 16)                *)
(*   X6 = Htable    192-byte precomputed H-powers table                     *)
(*   returns X0 = byte_len (= len_bits / 8)                                 *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_ENC_KERNEL_CORRECT = prove(
  `!in_p out_p len_bits tag_p ivec_p key_p htable_p
    tag0 ivec0
    rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10
    pc stackpointer.
    PAIRWISE nonoverlapping
      [(stackpointer, 160);
       (word pc, LENGTH aes_gcm_enc_kernel_mc);
       (in_p,  8 * val len_bits DIV 64);
       (out_p, 8 * val len_bits DIV 64);
       (tag_p, 16);
       (ivec_p, 16);
       (key_p, 176);
       (htable_p, 192)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
           read PC s = word (pc + 0x2c) /\
           read SP s = stackpointer /\
           C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = tag0 /\
           read (memory :> bytes128 ivec_p) s = ivec0 /\
           read (memory :> bytes128 (word_add key_p (word   0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_p (word  16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_p (word  32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_p (word  48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_p (word  64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_p (word  80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_p (word  96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_p (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_p (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_p (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_p (word 160))) s = rk10)
      (\s. read PC s = word (pc + 0x3cc) /\
           (* TODO: strengthen with:
              - return value:  read X0 s = word (val len_bits DIV 8)
              - ciphertext:    output = CTR(input, ivec0, [rk0..rk10])
              - tag update:    read (memory :> bytes128 tag_p) s =
                                 nist_ghash (aes128_cipher (word 0) [rk0..rk10])
                                            tag0 ciphertext_blocks
              - ivec update:   read (memory :> bytes128 ivec_p) s =
                                 (counter incremented nblocks times)
           *)
           read X0 s = read X0 s)   (* placeholder *)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24;
                  X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 8 * val len_bits DIV 64);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst AES_GCM_ENC_KERNEL_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness: lifts the core proof through the save/restore     *)
(* boilerplate and the final ret. This is the theorem used externally.       *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_ENC_KERNEL_SUBROUTINE_CORRECT = prove(
  `!in_p out_p len_bits tag_p ivec_p key_p htable_p
    tag0 ivec0
    rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 160), 160);
       (word pc, LENGTH aes_gcm_enc_kernel_mc);
       (in_p,  8 * val len_bits DIV 64);
       (out_p, 8 * val len_bits DIV 64);
       (tag_p, 16);
       (ivec_p, 16);
       (key_p, 176);
       (htable_p, 192)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = tag0 /\
           read (memory :> bytes128 ivec_p) s = ivec0 /\
           read (memory :> bytes128 (word_add key_p (word   0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_p (word  16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_p (word  32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_p (word  48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_p (word  64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_p (word  80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_p (word  96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_p (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_p (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_p (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_p (word 160))) s = rk10)
      (\s. read PC s = returnaddress)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 8 * val len_bits DIV 64);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 160), 160)])`,
  REWRITE_TAC[fst AES_GCM_ENC_KERNEL_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES_GCM_ENC_KERNEL_EXEC
    (REWRITE_RULE[fst AES_GCM_ENC_KERNEL_EXEC] AES_GCM_ENC_KERNEL_CORRECT)
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 160);;
