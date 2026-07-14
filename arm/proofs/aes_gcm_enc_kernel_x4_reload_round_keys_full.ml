(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-128-GCM encryption kernel.                                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "common/fips197.ml";;

needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

(* print_literal_from_elf "arm/aes_gcm/aes_gcm_enc_kernel_x4_reload_round_keys_full.o";; *)

let aes_gcm_enc_kernel_x4_reload_round_keys_full_mc =
  define_assert_from_elf "aes_gcm_enc_kernel_x4_reload_round_keys_full_mc"
                         "arm/aes_gcm/aes_gcm_enc_kernel_x4_reload_round_keys_full.o"
[
  0xd10283ff;       (* arm_SUB SP SP (rvalue (word 160)) *)
  0xa90053f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  0xa9015bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  0xa90263f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  0xa9036bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&48))) *)
  0xa90473fb;       (* arm_STP X27 X28 SP (Immediate_Offset (iword (&64))) *)
  0xa9057bfd;       (* arm_STP X29 X30 SP (Immediate_Offset (iword (&80))) *)
  0x6d0627e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&96))) *)
  0x6d072fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&112))) *)
  0x6d0837ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&128))) *)
  0x6d093fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&144))) *)
  0xd343fc2f;       (* arm_LSR X15 X1 3 *)
  0x3dc0006b;       (* arm_LDR Q11 X3 (Immediate_Offset (word 0)) *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x3dc0009f;       (* arm_LDR Q31 X4 (Immediate_Offset (word 0)) *)
  0xd2c00039;       (* arm_MOVZ X25 (word 1) 32 *)
  0x4f00e41e;       (* arm_MOVI Q30 (word 0) *)
  0x9eaf033e;       (* arm_FMOV_ItoF Q30 X25 1 *)
  0x6e200bff;       (* arm_REV32_VEC Q31 Q31 8 *)
  0xd344fde7;       (* arm_LSR X7 X15 4 *)
  0xd342fce1;       (* arm_LSR X1 X7 2 *)
  0x924004e9;       (* arm_AND X9 X7 (rvalue (word 3)) *)
  0x0f06e447;       (* arm_MOVI D7 (word 14033993530586874562) *)
  0x5f7854e7;       (* arm_SHL_VEC Q7 Q7 56 64 64 *)
  0xb40014a1;       (* arm_CBZ X1 (word 660) *)
  0x3dc000b9;       (* arm_LDR Q25 X5 (Immediate_Offset (word 0)) *)
  0x4ebe87ef;       (* arm_ADD_VEC Q15 Q31 Q30 32 128 *)
  0x3dc010c8;       (* arm_LDR Q8 X6 (Immediate_Offset (word 64)) *)
  0x6e200bff;       (* arm_REV32_VEC Q31 Q31 8 *)
  0x4ebe85ed;       (* arm_ADD_VEC Q13 Q15 Q30 32 128 *)
  0x3dc024bd;       (* arm_LDR Q29 X5 (Immediate_Offset (word 144)) *)
  0x6e2009e2;       (* arm_REV32_VEC Q2 Q15 8 *)
  0x3dc004b8;       (* arm_LDR Q24 X5 (Immediate_Offset (word 16)) *)
  0x6e2009b5;       (* arm_REV32_VEC Q21 Q13 8 *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b22;       (* arm_AESE Q2 Q25 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3dc008a3;       (* arm_LDR Q3 X5 (Immediate_Offset (word 32)) *)
  0x3dc01ca1;       (* arm_LDR Q1 X5 (Immediate_Offset (word 112)) *)
  0x4e284b35;       (* arm_AESE Q21 Q25 *)
  0x4e286ab5;       (* arm_AESMC Q21 Q21 *)
  0x3dc00caf;       (* arm_LDR Q15 X5 (Immediate_Offset (word 48)) *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b02;       (* arm_AESE Q2 Q24 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3dc010b6;       (* arm_LDR Q22 X5 (Immediate_Offset (word 64)) *)
  0x4e28487f;       (* arm_AESE Q31 Q3 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284862;       (* arm_AESE Q2 Q3 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3dc014b7;       (* arm_LDR Q23 X5 (Immediate_Offset (word 80)) *)
  0x3dc018bc;       (* arm_LDR Q28 X5 (Immediate_Offset (word 96)) *)
  0x4e2849ff;       (* arm_AESE Q31 Q15 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e2849e2;       (* arm_AESE Q2 Q15 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ebe85a0;       (* arm_ADD_VEC Q0 Q13 Q30 32 128 *)
  0x3dc020aa;       (* arm_LDR Q10 X5 (Immediate_Offset (word 128)) *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284ac2;       (* arm_AESE Q2 Q22 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e200804;       (* arm_REV32_VEC Q4 Q0 8 *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284ae2;       (* arm_AESE Q2 Q23 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3cc40412;       (* arm_LDR Q18 X0 (Postimmediate_Offset (word 64)) *)
  0x4e284b9f;       (* arm_AESE Q31 Q28 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc014da;       (* arm_LDR Q26 X6 (Immediate_Offset (word 80)) *)
  0x4e284b24;       (* arm_AESE Q4 Q25 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3cdd0006;       (* arm_LDR Q6 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e28483f;       (* arm_AESE Q31 Q1 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc028b9;       (* arm_LDR Q25 X5 (Immediate_Offset (word 160)) *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e28495f;       (* arm_AESE Q31 Q10 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc00cd3;       (* arm_LDR Q19 X6 (Immediate_Offset (word 48)) *)
  0x4e284822;       (* arm_AESE Q2 Q1 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e391e45;       (* arm_EOR_VEC Q5 Q18 Q25 128 *)
  0x4e284bbf;       (* arm_AESE Q31 Q29 *)
  0x4e284942;       (* arm_AESE Q2 Q10 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e391cd0;       (* arm_EOR_VEC Q16 Q6 Q25 128 *)
  0x4e284b04;       (* arm_AESE Q4 Q24 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3f1ca5;       (* arm_EOR_VEC Q5 Q5 Q31 128 *)
  0x4e284b15;       (* arm_AESE Q21 Q24 *)
  0x4e286ab5;       (* arm_AESMC Q21 Q21 *)
  0x4e284864;       (* arm_AESE Q4 Q3 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e2008bf;       (* arm_REV64_VEC Q31 Q5 8 *)
  0x4e284875;       (* arm_AESE Q21 Q3 *)
  0x4e286ab5;       (* arm_AESMC Q21 Q21 *)
  0x4e2849e4;       (* arm_AESE Q4 Q15 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284ba2;       (* arm_AESE Q2 Q29 *)
  0x6e2b1feb;       (* arm_EOR_VEC Q11 Q31 Q11 128 *)
  0x3cde0009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e284ac4;       (* arm_AESE Q4 Q22 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e2849f5;       (* arm_AESE Q21 Q15 *)
  0x4e286ab5;       (* arm_AESMC Q21 Q21 *)
  0x6e221e0f;       (* arm_EOR_VEC Q15 Q16 Q2 128 *)
  0x6e0b4171;       (* arm_EXT Q17 Q11 Q11 64 *)
  0x4e284ae4;       (* arm_AESE Q4 Q23 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e2009ed;       (* arm_REV64_VEC Q13 Q15 8 *)
  0x4e284ad5;       (* arm_AESE Q21 Q22 *)
  0x4e286ab5;       (* arm_AESMC Q21 Q21 *)
  0x6e2b1e36;       (* arm_EOR_VEC Q22 Q17 Q11 128 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x5e1805b0;       (* arm_DUP_ELEM Q16 Q13 1 64 *)
  0x4e284af5;       (* arm_AESE Q21 Q23 *)
  0x4e286ab5;       (* arm_AESMC Q21 Q21 *)
  0x3cdf0017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e284824;       (* arm_AESE Q4 Q1 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x2e2d1e10;       (* arm_EOR_VEC Q16 Q16 Q13 64 *)
  0x4e284b95;       (* arm_AESE Q21 Q28 *)
  0x4e286ab5;       (* arm_AESMC Q21 Q21 *)
  0x6e391d2e;       (* arm_EOR_VEC Q14 Q9 Q25 128 *)
  0x4e284944;       (* arm_AESE Q4 Q10 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284835;       (* arm_AESE Q21 Q1 *)
  0x4e286ab5;       (* arm_AESMC Q21 Q21 *)
  0x3dc000c3;       (* arm_LDR Q3 X6 (Immediate_Offset (word 0)) *)
  0x4e284ba4;       (* arm_AESE Q4 Q29 *)
  0x6e391ef9;       (* arm_EOR_VEC Q25 Q23 Q25 128 *)
  0x3dc004db;       (* arm_LDR Q27 X6 (Immediate_Offset (word 16)) *)
  0x4e284955;       (* arm_AESE Q21 Q10 *)
  0x4e286ab5;       (* arm_AESMC Q21 Q21 *)
  0x6e241f2c;       (* arm_EOR_VEC Q12 Q25 Q4 128 *)
  0x4ee8e2c4;       (* arm_PMULL2_VEC Q4 Q22 Q8 64 *)
  0x4e284bb5;       (* arm_AESE Q21 Q29 *)
  0x3dc008d2;       (* arm_LDR Q18 X6 (Immediate_Offset (word 32)) *)
  0x0ef3e1a1;       (* arm_PMULL_VEC Q1 Q13 Q19 64 *)
  0x4e20099f;       (* arm_REV64_VEC Q31 Q12 8 *)
  0x0ee8e216;       (* arm_PMULL_VEC Q22 Q16 Q8 64 *)
  0x6e351dd5;       (* arm_EOR_VEC Q21 Q14 Q21 128 *)
  0x5e1807f9;       (* arm_DUP_ELEM Q25 Q31 1 64 *)
  0x4ef3e1bd;       (* arm_PMULL2_VEC Q29 Q13 Q19 64 *)
  0x4efae168;       (* arm_PMULL2_VEC Q8 Q11 Q26 64 *)
  0x6e361c8d;       (* arm_EOR_VEC Q13 Q4 Q22 128 *)
  0x0efae16e;       (* arm_PMULL_VEC Q14 Q11 Q26 64 *)
  0x4e200ab4;       (* arm_REV64_VEC Q20 Q21 8 *)
  0x6e3d1d13;       (* arm_EOR_VEC Q19 Q8 Q29 128 *)
  0x4ee3e3ea;       (* arm_PMULL2_VEC Q10 Q31 Q3 64 *)
  0x6e144290;       (* arm_EXT Q16 Q20 Q20 64 *)
  0x4ef2e29a;       (* arm_PMULL2_VEC Q26 Q20 Q18 64 *)
  0x0ef2e29c;       (* arm_PMULL_VEC Q28 Q20 Q18 64 *)
  0x2e3f1f39;       (* arm_EOR_VEC Q25 Q25 Q31 64 *)
  0x6e341e10;       (* arm_EOR_VEC Q16 Q16 Q20 128 *)
  0x6e211dd2;       (* arm_EOR_VEC Q18 Q14 Q1 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0ee3e3f4;       (* arm_PMULL_VEC Q20 Q31 Q3 64 *)
  0x6e3c1e4e;       (* arm_EOR_VEC Q14 Q18 Q28 128 *)
  0x4efbe203;       (* arm_PMULL2_VEC Q3 Q16 Q27 64 *)
  0x0efbe33f;       (* arm_PMULL_VEC Q31 Q25 Q27 64 *)
  0x6e2a1e7a;       (* arm_EOR_VEC Q26 Q19 Q10 128 *)
  0x6e231dad;       (* arm_EOR_VEC Q13 Q13 Q3 128 *)
  0x6e341dd3;       (* arm_EOR_VEC Q19 Q14 Q20 128 *)
  0x6e1a4352;       (* arm_EXT Q18 Q26 Q26 64 *)
  0x0ee7e35c;       (* arm_PMULL_VEC Q28 Q26 Q7 64 *)
  0x6e3a1e7b;       (* arm_EOR_VEC Q27 Q19 Q26 128 *)
  0x6e3f1dad;       (* arm_EOR_VEC Q13 Q13 Q31 128 *)
  0x6e3c1e50;       (* arm_EOR_VEC Q16 Q18 Q28 128 *)
  0x6e3b1dad;       (* arm_EOR_VEC Q13 Q13 Q27 128 *)
  0x6e301db2;       (* arm_EOR_VEC Q18 Q13 Q16 128 *)
  0x3d800c4c;       (* arm_STR Q12 X2 (Immediate_Offset (word 48)) *)
  0x0ee7e25f;       (* arm_PMULL_VEC Q31 Q18 Q7 64 *)
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0x6e3f1e6c;       (* arm_EOR_VEC Q12 Q19 Q31 128 *)
  0x3c840445;       (* arm_STR Q5 X2 (Postimmediate_Offset (word 64)) *)
  0x6e321d92;       (* arm_EOR_VEC Q18 Q12 Q18 128 *)
  0x4ebe841f;       (* arm_ADD_VEC Q31 Q0 Q30 32 128 *)
  0x3c9d004f;       (* arm_STR Q15 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e0055;       (* arm_STR Q21 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x6e12424b;       (* arm_EXT Q11 Q18 Q18 64 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb5ffeba1;       (* arm_CBNZ X1 (word 2096500) *)
  0x3dc000b2;       (* arm_LDR Q18 X5 (Immediate_Offset (word 0)) *)
  0x3dc004b3;       (* arm_LDR Q19 X5 (Immediate_Offset (word 16)) *)
  0x3dc008b4;       (* arm_LDR Q20 X5 (Immediate_Offset (word 32)) *)
  0x3dc00cb5;       (* arm_LDR Q21 X5 (Immediate_Offset (word 48)) *)
  0x3dc010b6;       (* arm_LDR Q22 X5 (Immediate_Offset (word 64)) *)
  0x3dc014b7;       (* arm_LDR Q23 X5 (Immediate_Offset (word 80)) *)
  0x3dc018b8;       (* arm_LDR Q24 X5 (Immediate_Offset (word 96)) *)
  0x3dc01cb9;       (* arm_LDR Q25 X5 (Immediate_Offset (word 112)) *)
  0x3dc020ba;       (* arm_LDR Q26 X5 (Immediate_Offset (word 128)) *)
  0x3dc024bb;       (* arm_LDR Q27 X5 (Immediate_Offset (word 144)) *)
  0x3dc028bc;       (* arm_LDR Q28 X5 (Immediate_Offset (word 160)) *)
  0x3dc000cc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 0)) *)
  0x3dc008cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 32)) *)
  0x3dc004ce;       (* arm_LDR Q14 X6 (Immediate_Offset (word 16)) *)
  0xb40005c9;       (* arm_CBZ X9 (word 184) *)
  0x6e200bf0;       (* arm_REV32_VEC Q16 Q31 8 *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x4ebe87ff;       (* arm_ADD_VEC Q31 Q31 Q30 32 128 *)
  0x4e284a50;       (* arm_AESE Q16 Q18 *)
  0x4e286a10;       (* arm_AESMC Q16 Q16 *)
  0x6e3c1d02;       (* arm_EOR_VEC Q2 Q8 Q28 128 *)
  0x4e284a70;       (* arm_AESE Q16 Q19 *)
  0x4e286a10;       (* arm_AESMC Q16 Q16 *)
  0x4e284a90;       (* arm_AESE Q16 Q20 *)
  0x4e286a10;       (* arm_AESMC Q16 Q16 *)
  0x4e284ab0;       (* arm_AESE Q16 Q21 *)
  0x4e286a10;       (* arm_AESMC Q16 Q16 *)
  0x4e284ad0;       (* arm_AESE Q16 Q22 *)
  0x4e286a10;       (* arm_AESMC Q16 Q16 *)
  0x4e284af0;       (* arm_AESE Q16 Q23 *)
  0x4e286a10;       (* arm_AESMC Q16 Q16 *)
  0x4e284b10;       (* arm_AESE Q16 Q24 *)
  0x4e286a10;       (* arm_AESMC Q16 Q16 *)
  0x4e284b30;       (* arm_AESE Q16 Q25 *)
  0x4e286a10;       (* arm_AESMC Q16 Q16 *)
  0x4e284b50;       (* arm_AESE Q16 Q26 *)
  0x4e286a10;       (* arm_AESMC Q16 Q16 *)
  0x4e284b70;       (* arm_AESE Q16 Q27 *)
  0x6e301c43;       (* arm_EOR_VEC Q3 Q2 Q16 128 *)
  0x3c810443;       (* arm_STR Q3 X2 (Postimmediate_Offset (word 16)) *)
  0x4e20086f;       (* arm_REV64_VEC Q15 Q3 8 *)
  0x6e2b1ded;       (* arm_EOR_VEC Q13 Q15 Q11 128 *)
  0x4eece1a4;       (* arm_PMULL2_VEC Q4 Q13 Q12 64 *)
  0x5e1805ab;       (* arm_DUP_ELEM Q11 Q13 1 64 *)
  0x0eece1a5;       (* arm_PMULL_VEC Q5 Q13 Q12 64 *)
  0x2e2d1d6a;       (* arm_EOR_VEC Q10 Q11 Q13 64 *)
  0x6e044091;       (* arm_EXT Q17 Q4 Q4 64 *)
  0x6e241cab;       (* arm_EOR_VEC Q11 Q5 Q4 128 *)
  0x0ee7e084;       (* arm_PMULL_VEC Q4 Q4 Q7 64 *)
  0x0eeee143;       (* arm_PMULL_VEC Q3 Q10 Q14 64 *)
  0x6e241e20;       (* arm_EOR_VEC Q0 Q17 Q4 128 *)
  0x6e2b1c69;       (* arm_EOR_VEC Q9 Q3 Q11 128 *)
  0x6e201d31;       (* arm_EOR_VEC Q17 Q9 Q0 128 *)
  0x0ee7e224;       (* arm_PMULL_VEC Q4 Q17 Q7 64 *)
  0x6e241ca6;       (* arm_EOR_VEC Q6 Q5 Q4 128 *)
  0x6e114224;       (* arm_EXT Q4 Q17 Q17 64 *)
  0x6e241cc4;       (* arm_EOR_VEC Q4 Q6 Q4 128 *)
  0x6e04408b;       (* arm_EXT Q11 Q4 Q4 64 *)
  0xd1000529;       (* arm_SUB X9 X9 (rvalue (word 1)) *)
  0xb5fffa89;       (* arm_CBNZ X9 (word 2096976) *)
  0xaa0f03e0;       (* arm_MOV X0 X15 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x3d80006b;       (* arm_STR Q11 X3 (Immediate_Offset (word 0)) *)
  0x6e200bff;       (* arm_REV32_VEC Q31 Q31 8 *)
  0x3d80009f;       (* arm_STR Q31 X4 (Immediate_Offset (word 0)) *)
  0x6d4627e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&96))) *)
  0x6d472fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&112))) *)
  0x6d4837ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&128))) *)
  0x6d493fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&144))) *)
  0xa94053f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  0xa9415bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  0xa94263f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  0xa9436bf9;       (* arm_LDP X25 X26 SP (Immediate_Offset (iword (&48))) *)
  0xa94473fb;       (* arm_LDP X27 X28 SP (Immediate_Offset (iword (&64))) *)
  0xa9457bfd;       (* arm_LDP X29 X30 SP (Immediate_Offset (iword (&80))) *)
  0x910283ff;       (* arm_ADD SP SP (rvalue (word 160)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC = ARM_MK_EXEC_RULE aes_gcm_enc_kernel_x4_reload_round_keys_full_mc;;

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
(* Core correctness theorem.                                                 *)
(*                                                                           *)
(* This covers the body of the function with the save/restore boilerplate    *)
(* excised: PC starts at pc + 0x2c (first real instruction after the 11      *)
(* save instructions) and ends at pc + 0x3cc (first ldp of the postamble).   *)
(* The stackpointer is the value AFTER the sub sp, #0xa0 adjustment, i.e.    *)
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

let AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc.
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16)]
        [(word pc, LENGTH aes_gcm_enc_kernel_x4_reload_round_keys_full_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_x4_reload_round_keys_full_mc /\
           read PC s = word (pc + 0x2c) /\
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
      (\s. read PC s = word (pc + 0x3f8) /\
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
                  memory :> bytes(ivec_p, 16)])`,
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC] THEN

  (*** Abbreviate the loop counts to keep goal terms manageable ***)

  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN

  (*** Break up the round key list - a bit clumsy ****)

  ASM_CASES_TAC `LENGTH(rk:int128 list) = 11` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    EXPAND_TAC "rk" THEN REWRITE_TAC[MAP; CONS_11; GSYM CONJ_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP]] THEN

  (***** Initial state setup ****)

  ENSURES_SEQUENCE_TAC `pc + 0x60`
   `\s. read X0 s = in_p /\
        read X2 s = out_p /\
        read X3 s = tag_p /\
        read X4 s = ivec_p /\
        read X6 s = htable_p /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read X5 s = key_p /\
        read (memory :> bytes128 key_p) s =
          word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read Q7 s = word 13979173243358019584 /\
        read Q30 s = word 79228162514264337593543950336 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word loop_count /\
        read X7 s = word nblocks /\
        read X9 s = word loop_remain /\
        read Q31 s = word_reversefields 32 (ctr_block nonce 2) /\
        read Q11 s =
          byteswap128 tag0 /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!i. i < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                 inblock i)` THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_USHR_COMPOSE] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[word_ushr] THEN
      MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[word_ushr] THEN EXPAND_TAC "nblocks" THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[word_ushr; ARITH_RULE `2 EXP 7 = 128`] THEN
      REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
      REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN] THEN AP_TERM_TAC THEN
      EXPAND_TAC "loop_remain" THEN ARITH_TAC;
      REWRITE_TAC[usimd4; usimd2; ctr_block; DIMINDEX_32] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      CONV_TAC WORD_BLAST;
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    MAP_EVERY VAL_INT64_TAC
     [`nblocks:num`; `loop_count:num`; `loop_remain:num`]] THEN

  (*** Break code between main unrolled loop and tail loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2f4`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\
        read X4 s = ivec_p /\
        read X6 s = htable_p /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read X5 s = key_p /\
        read (memory :> bytes128 key_p) s =
          word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read Q7 s = word 13979173243358019584 /\
        read Q30 s = word 79228162514264337593543950336 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word 0 /\
        read X7 s = word nblocks /\
        read X9 s = word loop_remain /\
        read Q31 s = word_reversefields 32
                       (ctr_block nonce (4 * loop_count + 2)) /\
        read Q11 s =
          byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock)
                            (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_CASES_TAC `loop_count = 0` THENL
     [POP_ASSUM SUBST_ALL_TAC THEN
      ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC [1] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; CONJUNCT1 LT] THEN
      REWRITE_TAC[list_of_seq; nist_ghash] THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN

    (**** Loop setup for the main unrolled loop ***)

    ENSURES_WHILE_UP_TAC `loop_count:num` `pc + 0x064` `pc + 0x2f0`
      `\i s.
        read X0  s = word_add in_p  (word (64 * i)) /\
        read X2  s = word_add out_p (word (64 * i)) /\
        read X3 s = tag_p /\
        read X4 s = ivec_p /\
        read X6 s = htable_p /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read X5 s = key_p /\
        read (memory :> bytes128 key_p) s =
          word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read Q7 s = word 13979173243358019584 /\
        read Q30 s = word 79228162514264337593543950336 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word(loop_count - i) /\
        read X7 s = word nblocks /\
        read X9 s = word loop_remain /\
        read Q31 s = word_reversefields 32 (ctr_block nonce (4 * i + 2)) /\
        read Q11 s =
          byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * i))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
        (!j. j < 4 * i
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
    ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC [1] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0; LT;
                  list_of_seq; nist_ghash];

      (**** Main loop invariant (main unrolled loop) ****)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read (memory :> bytes128 (word_add in_p (word (64 * i)))) s0 =
        inblock (4 * i) /\
        read (memory :> bytes128 (word_add in_p (word (64 * i + 16)))) s0 =
        inblock (4 * i + 1) /\
        read (memory :> bytes128 (word_add in_p (word (64 * i + 32)))) s0 =
        inblock (4 * i + 2) /\
        read (memory :> bytes128 (word_add in_p (word (64 * i + 48)))) s0 =
        inblock (4 * i + 3)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE
         `64 * i + 16 = 16 * (4 * i + 1) /\
          64 * i + 32 = 16 * (4 * i + 2) /\
          64 * i + 48 = 16 * (4 * i + 3)`] THEN
        REWRITE_TAC[ARITH_RULE `64 * a = 16 * 4 * a`] THEN
        REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC [n] THEN
            RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
          (1--163) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `j < 4 * (i + 1) <=>
                              j < 4 * i \/ j = 4 * i \/ j = 4 * i + 1 \/
                              j = 4 * i + 2 \/ j = 4 * i + 3`] THEN
      ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
      REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
      REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
      REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
      REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
      REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
      ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
      DISCARD_STATE_TAC "s163" THEN
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
      REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
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
            (word_xor
            (word_pmul (cipherblock_3:int128) (h0:int128))
            (word_xor
            (word_pmul (cipherblock_2:int128) (h1:int128))
            (word_xor
            (word_pmul (cipherblock_1:int128) (h2:int128))
            (word_pmul (word_xor (sofar:int128) cipherblock_0)
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
                     `sofar:int128`; `cipherblock_0:int128`]
                    GHASH_POLYVAL_ACC_BATCHED) THEN
      REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
      CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
      REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
      REWRITE_TAC[ARITH_RULE `4 * i + 4 = SUC(SUC(SUC(SUC(4 * i))))`] THEN
      REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      REWRITE_TAC[APPEND] THEN
      REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL];

      (**** Trivial loop-back goal (main unrolled loop) ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC [1] THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[GSYM VAL_EQ];

      (*** Trivial bridge between the two loops ***)

      ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC [1] THEN
      REWRITE_TAC[SUB_REFL]];

    ALL_TAC] THEN

  (*** Trivial case of the tail loop ***)

  ASM_CASES_TAC `loop_remain = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--20) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `n MOD 4 = 0 ==> 4 * n DIV 4 = n`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC BITBLAST_RULE;

    ALL_TAC] THEN

  (*** Loop setup for the tail loop ***)

  ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0x330` `pc + 0x3e0`
    `\i s.
      read X0  s = word_add in_p  (word (64 * loop_count + 16 * i)) /\
      read X2  s = word_add out_p (word (64 * loop_count + 16 * i)) /\
      read X3 s = tag_p /\
      read X4 s = ivec_p /\
      read X6 s = htable_p /\
      read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
      read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
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
      read Q28 s = word_reversefields 8 (EL 10 rk) /\
      read Q7 s = word 13979173243358019584 /\
      read Q30 s = word 79228162514264337593543950336 /\
      read X15 s = word(len_bits DIV 8) /\
      read X9 s = word(loop_remain - i) /\
      read Q31 s = word_reversefields 32
                    (ctr_block nonce (4 * loop_count + i + 2)) /\
      read Q11 s =
        byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock)
                          (4 * loop_count + i))) /\
      htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
      read Q12 s = byteswap128
        (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
      read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
      (!j. j < 4 * loop_count + i
           ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
               word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--15) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0];

    (*** Main loop invariant (tail loop) ****)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128
        (word_add in_p (word (64 * loop_count + 16 * i)))) s0 =
      inblock (4 * loop_count + i)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC [n] THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
     (1--44) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `j < a + i + 1 <=> j < a + i \/ j = a + i`] THEN
    ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
    REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
    ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
    DISCARD_STATE_TAC "s44" THEN
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
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
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
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock)
                              (4 * loop_count + i)))`;
      `cipherblock =
        nist_cipher_block nonce rk inblock (4 * loop_count + i)`;
      `h = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `k = karatsuba_mid h`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
      `polyval_reduce_prop3
          (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      LET_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
      ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM polyval_dot] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[h_power] THEN
    REWRITE_TAC[GSYM NIST_DOT_IS_POLYVAL_DOT] THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) = SUC k`] THEN
    REWRITE_TAC[list_of_seq; NIST_GHASH_APPEND;
                NIST_GHASH_CONS; nist_ghash] THEN
    ASM_REWRITE_TAC[];

    (*** Trivial loop-back goal (tail loop) ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC [1] THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ];

    (**** Final writeback, reversal etc. ***)

    ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC (1--6) THEN
    REWRITE_TAC[ADD_ASSOC] THEN
    SUBGOAL_THEN `4 * loop_count + loop_remain = nblocks` SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[byteswap128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC BITBLAST_RULE]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness: lifts the core proof through the save/restore     *)
(* boilerplate and the final ret. This is the theorem used externally.       *)
(* ------------------------------------------------------------------------- *)

(*** The externally-used spec. Its pre/postconditions match the core theorem
 *** (CTR ciphertext output, GHASH tag, updated counter), lifted through the
 *** save/restore prologue/epilogue and the final ret. The stack frame region
 *** (160 bytes below the incoming SP) is added to the nonoverlapping lists and
 *** to the MAYCHANGE. ARM_ADD_RETURN_STACK_TAC does the lifting; we expand the
 *** compound memory predicates htable_mem_4 and wordlist_from_memory (in both
 *** the goal and the fed core theorem) so the interior big-step's precondition
 *** obligation is discharged with no residual subgoal.
 ***)

let AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 160), 160)]
      [(word pc, LENGTH aes_gcm_enc_kernel_x4_reload_round_keys_full_mc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 160), 160)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_x4_reload_round_keys_full_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
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
      (\s. read PC s = returnaddress /\
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
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 160), 160)])`,
  REWRITE_TAC[fst AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC; htable_mem_4] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC
    (CONV_RULE(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)
       (REWRITE_RULE[fst AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_EXEC; htable_mem_4]
          AES_GCM_ENC_KERNEL_X4_RELOAD_ROUND_KEYS_FULL_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 160);;
