
(*****************************************************************************)

(* ------------------------------------------------------------------------- *)
(* Starting proofs about the machine code.                                   *)
(* ------------------------------------------------------------------------- *)

(*****************************************************************************)

(*
print_literal_relocs_from_elf "arm/ed25519/code/ed25519_tmp.o";;

save_literal_relocs_from_elf
  "arm/ed25519/literal_relocs_tmp.txt"
  "arm/ed25519/code/ed25519_tmp.o";;
*)

let ed25519_mc,constants_data = define_assert_relocs_from_elf "ed25519_mc"
    "arm/ed25519/code/ed25519_tmp.o"
  (fun w BL ADR ADRP ADD_rri64 -> [
  w 0xa9a953f3;         (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &368))) *)
  w 0xf9000bfe;         (* arm_STR X30 SP (Immediate_Offset (word 16)) *)
  w 0xaa0003f3;         (* arm_MOV X19 X0 *)
  w 0xaa0103f4;         (* arm_MOV X20 X1 *)
  w 0x910063e0;         (* arm_ADD X0 SP (rvalue (word 24)) *)
  BL (mk_var("sha512_init",`:num`),0,20);
  w 0x910063e0;         (* arm_ADD X0 SP (rvalue (word 24)) *)
  w 0xaa1403e1;         (* arm_MOV X1 X20 *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  BL (mk_var("sha512_update",`:num`),0,36);
  w 0x9103c3e0;         (* arm_ADD X0 SP (rvalue (word 240)) *)
  w 0x910063e1;         (* arm_ADD X1 SP (rvalue (word 24)) *)
  BL (mk_var("sha512_final",`:num`),0,48);
  w 0x3943c3e0;         (* arm_LDRB W0 SP (Immediate_Offset (word 240)) *)
  w 0x121d1000;         (* arm_AND W0 W0 (rvalue (word 248)) *)
  w 0x3903c3e0;         (* arm_STRB W0 SP (Immediate_Offset (word 240)) *)
  w 0x39443fe0;         (* arm_LDRB W0 SP (Immediate_Offset (word 271)) *)
  w 0x12001800;         (* arm_AND W0 W0 (rvalue (word 127)) *)
  w 0x321a0000;         (* arm_ORR W0 W0 (rvalue (word 64)) *)
  w 0x39043fe0;         (* arm_STRB W0 SP (Immediate_Offset (word 271)) *)
  w 0x9104c3e0;         (* arm_ADD X0 SP (rvalue (word 304)) *)
  w 0x9103c3e1;         (* arm_ADD X1 SP (rvalue (word 240)) *)
  BL (mk_var("edwards25519_scalarmulbase_alt",`:num`),0,88);
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0x9104c3e1;         (* arm_ADD X1 SP (rvalue (word 304)) *)
  BL (mk_var("edwards25519_encode",`:num`),0,100);
  w 0xf9400bfe;         (* arm_LDR X30 SP (Immediate_Offset (word 16)) *)
  w 0xa8d753f3;         (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&368))) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd10843ff;         (* arm_SUB SP SP (rvalue (word 528)) *)
  w 0xa90053f3;         (* arm_STP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  w 0xa9015bf5;         (* arm_STP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xa90263f7;         (* arm_STP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  w 0xf9001bfe;         (* arm_STR X30 SP (Immediate_Offset (word 48)) *)
  w 0xaa0003f3;         (* arm_MOV X19 X0 *)
  w 0xaa0103f4;         (* arm_MOV X20 X1 *)
  w 0xaa0203f5;         (* arm_MOV X21 X2 *)
  w 0xaa0303f6;         (* arm_MOV X22 X3 *)
  w 0xaa0403f7;         (* arm_MOV X23 X4 *)
  w 0xaa0503f8;         (* arm_MOV X24 X5 *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  BL (mk_var("sha512_init",`:num`),0,164);
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1603e1;         (* arm_MOV X1 X22 *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  BL (mk_var("sha512_update",`:num`),0,180);
  w 0x910443e0;         (* arm_ADD X0 SP (rvalue (word 272)) *)
  w 0x9100e3e1;         (* arm_ADD X1 SP (rvalue (word 56)) *)
  BL (mk_var("sha512_final",`:num`),0,192);
  w 0x394443e0;         (* arm_LDRB W0 SP (Immediate_Offset (word 272)) *)
  w 0x121d1000;         (* arm_AND W0 W0 (rvalue (word 248)) *)
  w 0x390443e0;         (* arm_STRB W0 SP (Immediate_Offset (word 272)) *)
  w 0x3944bfe0;         (* arm_LDRB W0 SP (Immediate_Offset (word 303)) *)
  w 0x12001800;         (* arm_AND W0 W0 (rvalue (word 127)) *)
  w 0x321a0000;         (* arm_ORR W0 W0 (rvalue (word 64)) *)
  w 0x3904bfe0;         (* arm_STRB W0 SP (Immediate_Offset (word 303)) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  BL (mk_var("sha512_init",`:num`),0,228);
  w 0xb40000b8;         (* arm_CBZ X24 (word 20) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1703e1;         (* arm_MOV X1 X23 *)
  w 0xaa1803e2;         (* arm_MOV X2 X24 *)
  BL (mk_var("sha512_update",`:num`),0,248);
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0x9104c3e1;         (* arm_ADD X1 SP (rvalue (word 304)) *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  BL (mk_var("sha512_update",`:num`),0,264);
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1403e1;         (* arm_MOV X1 X20 *)
  w 0xaa1503e2;         (* arm_MOV X2 X21 *)
  BL (mk_var("sha512_update",`:num`),0,280);
  w 0x910543e0;         (* arm_ADD X0 SP (rvalue (word 336)) *)
  w 0x9100e3e1;         (* arm_ADD X1 SP (rvalue (word 56)) *)
  BL (mk_var("sha512_final",`:num`),0,292);
  w 0x910543e0;         (* arm_ADD X0 SP (rvalue (word 336)) *)
  w 0xd2800101;         (* arm_MOV X1 (rvalue (word 8)) *)
  w 0xaa0003e2;         (* arm_MOV X2 X0 *)
  BL (mk_var("bignum_mod_n25519",`:num`),0,308);
  w 0x910643e0;         (* arm_ADD X0 SP (rvalue (word 400)) *)
  w 0x910543e1;         (* arm_ADD X1 SP (rvalue (word 336)) *)
  BL (mk_var("edwards25519_scalarmulbase_alt",`:num`),0,320);
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0x910643e1;         (* arm_ADD X1 SP (rvalue (word 400)) *)
  BL (mk_var("edwards25519_encode",`:num`),0,332);
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  BL (mk_var("sha512_init",`:num`),0,340);
  w 0xb40000b8;         (* arm_CBZ X24 (word 20) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1703e1;         (* arm_MOV X1 X23 *)
  w 0xaa1803e2;         (* arm_MOV X2 X24 *)
  BL (mk_var("sha512_update",`:num`),0,360);
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1303e1;         (* arm_MOV X1 X19 *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  BL (mk_var("sha512_update",`:num`),0,376);
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0x910082c1;         (* arm_ADD X1 X22 (rvalue (word 32)) *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  BL (mk_var("sha512_update",`:num`),0,392);
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1403e1;         (* arm_MOV X1 X20 *)
  w 0xaa1503e2;         (* arm_MOV X2 X21 *)
  BL (mk_var("sha512_update",`:num`),0,408);
  w 0x910743e0;         (* arm_ADD X0 SP (rvalue (word 464)) *)
  w 0x9100e3e1;         (* arm_ADD X1 SP (rvalue (word 56)) *)
  BL (mk_var("sha512_final",`:num`),0,420);
  w 0x910743e0;         (* arm_ADD X0 SP (rvalue (word 464)) *)
  w 0xd2800101;         (* arm_MOV X1 (rvalue (word 8)) *)
  w 0xaa0003e2;         (* arm_MOV X2 X0 *)
  BL (mk_var("bignum_mod_n25519",`:num`),0,436);
  w 0x91008260;         (* arm_ADD X0 X19 (rvalue (word 32)) *)
  w 0x910743e1;         (* arm_ADD X1 SP (rvalue (word 464)) *)
  w 0x910443e2;         (* arm_ADD X2 SP (rvalue (word 272)) *)
  w 0x910543e3;         (* arm_ADD X3 SP (rvalue (word 336)) *)
  BL (mk_var("bignum_madd_n25519_alt",`:num`),0,456);
  w 0xa94053f3;         (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  w 0xa9415bf5;         (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xa94263f7;         (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  w 0xf9401bfe;         (* arm_LDR X30 SP (Immediate_Offset (word 48)) *)
  w 0x910843ff;         (* arm_ADD SP SP (rvalue (word 528)) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd10843ff;         (* arm_SUB SP SP (rvalue (word 528)) *)
  w 0xa90053f3;         (* arm_STP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  w 0xa9015bf5;         (* arm_STP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xa90263f7;         (* arm_STP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  w 0xf9001bfe;         (* arm_STR X30 SP (Immediate_Offset (word 48)) *)
  w 0xaa0003f3;         (* arm_MOV X19 X0 *)
  w 0xaa0103f4;         (* arm_MOV X20 X1 *)
  w 0xaa0203f5;         (* arm_MOV X21 X2 *)
  w 0xaa0303f6;         (* arm_MOV X22 X3 *)
  w 0xaa0403f7;         (* arm_MOV X23 X4 *)
  w 0xaa0503f8;         (* arm_MOV X24 X5 *)
  w 0xd29a7da0;         (* arm_MOV X0 (rvalue (word 54253)) *)
  w 0xf2ab9ea0;         (* arm_MOVK X0 (word 23797) 16 *)
  w 0xf2cc6340;         (* arm_MOVK X0 (word 25370) 32 *)
  w 0xf2eb0240;         (* arm_MOVK X0 (word 22546) 48 *)
  w 0xd2939ac1;         (* arm_MOV X1 (rvalue (word 40150)) *)
  w 0xf2b45ee1;         (* arm_MOVK X1 (word 41719) 16 *)
  w 0xf2df3bc1;         (* arm_MOVK X1 (word 63966) 32 *)
  w 0xf2e29bc1;         (* arm_MOVK X1 (word 5342) 48 *)
  w 0xa90387e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&56))) *)
  w 0xaa1f03e0;         (* arm_MOV X0 XZR *)
  w 0xd2800021;         (* arm_MOV X1 (rvalue (word 1)) *)
  w 0xd3410021;         (* arm_LSL X1 X1 63 *)
  w 0xa90487e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&72))) *)
  w 0xd2800080;         (* arm_MOV X0 (rvalue (word 4)) *)
  w 0x9100e3e1;         (* arm_ADD X1 SP (rvalue (word 56)) *)
  w 0xd2800082;         (* arm_MOV X2 (rvalue (word 4)) *)
  w 0x910082a3;         (* arm_ADD X3 X21 (rvalue (word 32)) *)
  BL (mk_var("bignum_le",`:num`),0,596);
  w 0xb5000720;         (* arm_CBNZ X0 (word 228) *)
  w 0x910163e0;         (* arm_ADD X0 SP (rvalue (word 88)) *)
  w 0xaa1603e1;         (* arm_MOV X1 X22 *)
  BL (mk_var("edwards25519_decode_alt",`:num`),0,612);
  w 0xb50006a0;         (* arm_CBNZ X0 (word 212) *)
  w 0x910263e0;         (* arm_ADD X0 SP (rvalue (word 152)) *)
  BL (mk_var("sha512_init",`:num`),0,624);
  w 0xb40000b8;         (* arm_CBZ X24 (word 20) *)
  w 0x910263e0;         (* arm_ADD X0 SP (rvalue (word 152)) *)
  w 0xaa1703e1;         (* arm_MOV X1 X23 *)
  w 0xaa1803e2;         (* arm_MOV X2 X24 *)
  BL (mk_var("sha512_update",`:num`),0,644);
  w 0x910263e0;         (* arm_ADD X0 SP (rvalue (word 152)) *)
  w 0xaa1503e1;         (* arm_MOV X1 X21 *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  BL (mk_var("sha512_update",`:num`),0,660);
  w 0x910263e0;         (* arm_ADD X0 SP (rvalue (word 152)) *)
  w 0xaa1603e1;         (* arm_MOV X1 X22 *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  BL (mk_var("sha512_update",`:num`),0,676);
  w 0x910263e0;         (* arm_ADD X0 SP (rvalue (word 152)) *)
  w 0xaa1303e1;         (* arm_MOV X1 X19 *)
  w 0xaa1403e2;         (* arm_MOV X2 X20 *)
  BL (mk_var("sha512_update",`:num`),0,692);
  w 0x9105c3e0;         (* arm_ADD X0 SP (rvalue (word 368)) *)
  w 0x910263e1;         (* arm_ADD X1 SP (rvalue (word 152)) *)
  BL (mk_var("sha512_final",`:num`),0,704);
  w 0x910163e0;         (* arm_ADD X0 SP (rvalue (word 88)) *)
  w 0xaa0003e1;         (* arm_MOV X1 X0 *)
  BL (mk_var("bignum_neg_p25519",`:num`),0,716);
  w 0x9105c3e0;         (* arm_ADD X0 SP (rvalue (word 368)) *)
  w 0xd2800101;         (* arm_MOV X1 (rvalue (word 8)) *)
  w 0xaa0003e2;         (* arm_MOV X2 X0 *)
  BL (mk_var("bignum_mod_n25519",`:num`),0,732);
  w 0x9106c3e0;         (* arm_ADD X0 SP (rvalue (word 432)) *)
  w 0x9105c3e1;         (* arm_ADD X1 SP (rvalue (word 368)) *)
  w 0x910163e2;         (* arm_ADD X2 SP (rvalue (word 88)) *)
  w 0x910082a3;         (* arm_ADD X3 X21 (rvalue (word 32)) *)
  BL (mk_var("edwards25519_scalarmuldouble_alt",`:num`),0,752);
  w 0x9107c3e0;         (* arm_ADD X0 SP (rvalue (word 496)) *)
  w 0x9106c3e1;         (* arm_ADD X1 SP (rvalue (word 432)) *)
  BL (mk_var("edwards25519_encode",`:num`),0,764);
  w 0xa95f07e0;         (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&496))) *)
  w 0xa9400ea2;         (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&0))) *)
  w 0xeb02001f;         (* arm_CMP X0 X2 *)
  w 0x54000181;         (* arm_BNE (word 48) *)
  w 0xeb03003f;         (* arm_CMP X1 X3 *)
  w 0x54000141;         (* arm_BNE (word 40) *)
  w 0x910803e4;         (* arm_ADD X4 SP (rvalue (word 512)) *)
  w 0xa9400480;         (* arm_LDP X0 X1 X4 (Immediate_Offset (iword (&0))) *)
  w 0xa9410ea2;         (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&16))) *)
  w 0xeb02001f;         (* arm_CMP X0 X2 *)
  w 0x540000a1;         (* arm_BNE (word 20) *)
  w 0xeb03003f;         (* arm_CMP X1 X3 *)
  w 0x54000061;         (* arm_BNE (word 12) *)
  w 0xd2800020;         (* arm_MOV X0 (rvalue (word 1)) *)
  w 0x14000002;         (* arm_B (word 8) *)
  w 0xaa1f03e0;         (* arm_MOV X0 XZR *)
  w 0xa94053f3;         (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  w 0xa9415bf5;         (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xa94263f7;         (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  w 0xf9401bfe;         (* arm_LDR X30 SP (Immediate_Offset (word 48)) *)
  w 0x910843ff;         (* arm_ADD SP SP (rvalue (word 528)) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xa9bf7bfd;         (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  w 0xaa1f03e4;         (* arm_MOV X4 XZR *)
  w 0xaa1f03e5;         (* arm_MOV X5 XZR *)
  w 0x97ffff44;         (* arm_BL (word 268434704) *)
  w 0xd2800020;         (* arm_MOV X0 (rvalue (word 1)) *)
  w 0xa8c17bfd;         (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&16))) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xa9bf7bfd;         (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  w 0xaa1f03e4;         (* arm_MOV X4 XZR *)
  w 0xaa1f03e5;         (* arm_MOV X5 XZR *)
  w 0x97ffff99;         (* arm_BL (word 268435044) *)
  w 0xa8c17bfd;         (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&16))) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd28d2a64;         (* arm_MOV X4 (rvalue (word 26963)) *)
  w 0xf2a8ace4;         (* arm_MOVK X4 (word 17767) 16 *)
  w 0xf2c64c84;         (* arm_MOVK X4 (word 12900) 32 *)
  w 0xf2e6a6a4;         (* arm_MOVK X4 (word 13621) 48 *)
  w 0xd2872625;         (* arm_MOV X5 (rvalue (word 14641)) *)
  w 0xf2adc405;         (* arm_MOVK X5 (word 28192) 16 *)
  w 0xf2c40de5;         (* arm_MOVK X5 (word 8303) 32 *)
  w 0xf2ec88a5;         (* arm_MOVK X5 (word 25669) 48 *)
  w 0xa9001404;         (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&0))) *)
  w 0xd286a644;         (* arm_MOV X4 (rvalue (word 13618)) *)
  w 0xf2a626a4;         (* arm_MOVK X4 (word 12597) 16 *)
  w 0xf2c40724;         (* arm_MOVK X4 (word 8249) 32 *)
  w 0xf2edec64;         (* arm_MOVK X4 (word 28515) 48 *)
  w 0xd28d8d85;         (* arm_MOV X5 (rvalue (word 27756)) *)
  w 0xf2ae6d25;         (* arm_MOVK X5 (word 29545) 16 *)
  w 0xf2cded25;         (* arm_MOVK X5 (word 28521) 32 *)
  w 0xf2ee6dc5;         (* arm_MOVK X5 (word 29550) 48 *)
  w 0xa9011404;         (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  w 0x39008001;         (* arm_STRB W1 X0 (Immediate_Offset (word 32)) *)
  w 0x39008403;         (* arm_STRB W3 X0 (Immediate_Offset (word 33)) *)
  w 0x91008804;         (* arm_ADD X4 X0 (rvalue (word 34)) *)
  w 0xaa1f03e5;         (* arm_MOV X5 XZR *)
  w 0x14000004;         (* arm_B (word 16) *)
  w 0x38656846;         (* arm_LDRB W6 X2 (Register_Offset X5) *)
  w 0x38256886;         (* arm_STRB W6 X4 (Register_Offset X5) *)
  w 0x910004a5;         (* arm_ADD X5 X5 (rvalue (word 1)) *)
  w 0xeb05007f;         (* arm_CMP X3 X5 *)
  w 0x54ffff81;         (* arm_BNE (word 2097136) *)
  w 0x91008860;         (* arm_ADD X0 X3 (rvalue (word 34)) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xa9ab53f3;         (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &336))) *)
  w 0xa9015bf5;         (* arm_STP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xf90013fe;         (* arm_STR X30 SP (Immediate_Offset (word 32)) *)
  w 0xaa0003f3;         (* arm_MOV X19 X0 *)
  w 0xaa0103f4;         (* arm_MOV X20 X1 *)
  w 0xaa0203f5;         (* arm_MOV X21 X2 *)
  w 0xaa0303f6;         (* arm_MOV X22 X3 *)
  w 0xb4000225;         (* arm_CBZ X5 (word 68) *)
  w 0xf103fcbf;         (* arm_CMP X5 (rvalue (word 255)) *)
  w 0x540001e8;         (* arm_BHI (word 60) *)
  w 0x9100a3e0;         (* arm_ADD X0 SP (rvalue (word 40)) *)
  w 0xaa1f03e1;         (* arm_MOV X1 XZR *)
  w 0xaa0403e2;         (* arm_MOV X2 X4 *)
  w 0xaa0503e3;         (* arm_MOV X3 X5 *)
  w 0x97ffffd4;         (* arm_BL (word 268435280) *)
  w 0xaa0003e5;         (* arm_MOV X5 X0 *)
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0xaa1403e1;         (* arm_MOV X1 X20 *)
  w 0xaa1503e2;         (* arm_MOV X2 X21 *)
  w 0xaa1603e3;         (* arm_MOV X3 X22 *)
  w 0x9100a3e4;         (* arm_ADD X4 SP (rvalue (word 40)) *)
  w 0x97ffff07;         (* arm_BL (word 268434460) *)
  w 0xd2800020;         (* arm_MOV X0 (rvalue (word 1)) *)
  w 0x14000002;         (* arm_B (word 8) *)
  w 0xaa1f03e0;         (* arm_MOV X0 XZR *)
  w 0xa9415bf5;         (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94013fe;         (* arm_LDR X30 SP (Immediate_Offset (word 32)) *)
  w 0xa8d553f3;         (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&336))) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xa9ab53f3;         (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &336))) *)
  w 0xa9015bf5;         (* arm_STP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xf90013fe;         (* arm_STR X30 SP (Immediate_Offset (word 32)) *)
  w 0xaa0003f3;         (* arm_MOV X19 X0 *)
  w 0xaa0103f4;         (* arm_MOV X20 X1 *)
  w 0xaa0203f5;         (* arm_MOV X21 X2 *)
  w 0xaa0303f6;         (* arm_MOV X22 X3 *)
  w 0xb4000205;         (* arm_CBZ X5 (word 64) *)
  w 0xf103fcbf;         (* arm_CMP X5 (rvalue (word 255)) *)
  w 0x540001c8;         (* arm_BHI (word 56) *)
  w 0x9100a3e0;         (* arm_ADD X0 SP (rvalue (word 40)) *)
  w 0xaa1f03e1;         (* arm_MOV X1 XZR *)
  w 0xaa0403e2;         (* arm_MOV X2 X4 *)
  w 0xaa0503e3;         (* arm_MOV X3 X5 *)
  w 0x97ffffb7;         (* arm_BL (word 268435164) *)
  w 0xaa0003e5;         (* arm_MOV X5 X0 *)
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0xaa1403e1;         (* arm_MOV X1 X20 *)
  w 0xaa1503e2;         (* arm_MOV X2 X21 *)
  w 0xaa1603e3;         (* arm_MOV X3 X22 *)
  w 0x9100a3e4;         (* arm_ADD X4 SP (rvalue (word 40)) *)
  w 0x97ffff46;         (* arm_BL (word 268434712) *)
  w 0x14000002;         (* arm_B (word 8) *)
  w 0xaa1f03e0;         (* arm_MOV X0 XZR *)
  w 0xa9415bf5;         (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94013fe;         (* arm_LDR X30 SP (Immediate_Offset (word 32)) *)
  w 0xa8d553f3;         (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&336))) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd109c3ff;         (* arm_SUB SP SP (rvalue (word 624)) *)
  w 0xa90053f3;         (* arm_STP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  w 0xa9015bf5;         (* arm_STP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xf90013fe;         (* arm_STR X30 SP (Immediate_Offset (word 32)) *)
  w 0xaa0003f3;         (* arm_MOV X19 X0 *)
  w 0xaa0103f4;         (* arm_MOV X20 X1 *)
  w 0xaa0203f5;         (* arm_MOV X21 X2 *)
  w 0xaa0303f6;         (* arm_MOV X22 X3 *)
  w 0xf103fcbf;         (* arm_CMP X5 (rvalue (word 255)) *)
  w 0x54000328;         (* arm_BHI (word 100) *)
  w 0x9100a3e0;         (* arm_ADD X0 SP (rvalue (word 40)) *)
  w 0xd2800021;         (* arm_MOV X1 (rvalue (word 1)) *)
  w 0xaa0403e2;         (* arm_MOV X2 X4 *)
  w 0xaa0503e3;         (* arm_MOV X3 X5 *)
  w 0x97ffff9b;         (* arm_BL (word 268435052) *)
  w 0xf900abe0;         (* arm_STR X0 SP (Immediate_Offset (word 336)) *)
  w 0x910563e0;         (* arm_ADD X0 SP (rvalue (word 344)) *)
  BL (mk_var("sha512_init",`:num`),0,1324);
  w 0x910563e0;         (* arm_ADD X0 SP (rvalue (word 344)) *)
  w 0xaa1403e1;         (* arm_MOV X1 X20 *)
  w 0xaa1503e2;         (* arm_MOV X2 X21 *)
  BL (mk_var("sha512_update",`:num`),0,1340);
  w 0x9108c3e0;         (* arm_ADD X0 SP (rvalue (word 560)) *)
  w 0x910563e1;         (* arm_ADD X1 SP (rvalue (word 344)) *)
  BL (mk_var("sha512_final",`:num`),0,1352);
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0x9108c3e1;         (* arm_ADD X1 SP (rvalue (word 560)) *)
  w 0xd2800802;         (* arm_MOV X2 (rvalue (word 64)) *)
  w 0xaa1603e3;         (* arm_MOV X3 X22 *)
  w 0x9100a3e4;         (* arm_ADD X4 SP (rvalue (word 40)) *)
  w 0xf940abe5;         (* arm_LDR X5 SP (Immediate_Offset (word 336)) *)
  w 0x97fffec4;         (* arm_BL (word 268434192) *)
  w 0xd2800020;         (* arm_MOV X0 (rvalue (word 1)) *)
  w 0x14000002;         (* arm_B (word 8) *)
  w 0xaa1f03e0;         (* arm_MOV X0 XZR *)
  w 0xa94053f3;         (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  w 0xa9415bf5;         (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94013fe;         (* arm_LDR X30 SP (Immediate_Offset (word 32)) *)
  w 0x9109c3ff;         (* arm_ADD SP SP (rvalue (word 624)) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd109c3ff;         (* arm_SUB SP SP (rvalue (word 624)) *)
  w 0xa90053f3;         (* arm_STP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  w 0xa9015bf5;         (* arm_STP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xf90013fe;         (* arm_STR X30 SP (Immediate_Offset (word 32)) *)
  w 0xaa0003f3;         (* arm_MOV X19 X0 *)
  w 0xaa0103f4;         (* arm_MOV X20 X1 *)
  w 0xaa0203f5;         (* arm_MOV X21 X2 *)
  w 0xaa0303f6;         (* arm_MOV X22 X3 *)
  w 0xf103fcbf;         (* arm_CMP X5 (rvalue (word 255)) *)
  w 0x54000308;         (* arm_BHI (word 96) *)
  w 0x9100a3e0;         (* arm_ADD X0 SP (rvalue (word 40)) *)
  w 0xd2800021;         (* arm_MOV X1 (rvalue (word 1)) *)
  w 0xaa0403e2;         (* arm_MOV X2 X4 *)
  w 0xaa0503e3;         (* arm_MOV X3 X5 *)
  w 0x97ffff73;         (* arm_BL (word 268434892) *)
  w 0xf900abe0;         (* arm_STR X0 SP (Immediate_Offset (word 336)) *)
  w 0x910563e0;         (* arm_ADD X0 SP (rvalue (word 344)) *)
  BL (mk_var("sha512_init",`:num`),0,1484);
  w 0x910563e0;         (* arm_ADD X0 SP (rvalue (word 344)) *)
  w 0xaa1303e1;         (* arm_MOV X1 X19 *)
  w 0xaa1403e2;         (* arm_MOV X2 X20 *)
  BL (mk_var("sha512_update",`:num`),0,1500);
  w 0x9108c3e0;         (* arm_ADD X0 SP (rvalue (word 560)) *)
  w 0x910563e1;         (* arm_ADD X1 SP (rvalue (word 344)) *)
  BL (mk_var("sha512_final",`:num`),0,1512);
  w 0x9108c3e0;         (* arm_ADD X0 SP (rvalue (word 560)) *)
  w 0xd2800801;         (* arm_MOV X1 (rvalue (word 64)) *)
  w 0xaa1503e2;         (* arm_MOV X2 X21 *)
  w 0xaa1603e3;         (* arm_MOV X3 X22 *)
  w 0x9100a3e4;         (* arm_ADD X4 SP (rvalue (word 40)) *)
  w 0xf940abe5;         (* arm_LDR X5 SP (Immediate_Offset (word 336)) *)
  w 0x97fffef8;         (* arm_BL (word 268434400) *)
  w 0x14000002;         (* arm_B (word 8) *)
  w 0xaa1f03e0;         (* arm_MOV X0 XZR *)
  w 0xa94053f3;         (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  w 0xa9415bf5;         (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94013fe;         (* arm_LDR X30 SP (Immediate_Offset (word 32)) *)
  w 0x9109c3ff;         (* arm_ADD SP SP (rvalue (word 624)) *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;


let EXEC = ARM_MK_EXEC_RULE ed25519_mc;;

(* void ed25519_keypair_from_seed_s2n_bignum(
    uint8_t A[ED25519_PUBLIC_KEY_LEN], const uint8_t seed[ED25519_SEED_LEN]) *)
let ED25519_KEYPAIR_FROM_S2N_BIGNUM_CORRECT = prove
  (`!sp A_p seed_p seed pc retpc.
    PAIRWISE nonoverlapping [(word pc, ???); (A_p, 32); (seed_p, 32); (word_sub sp (word ???), ???)] /\
    LENGTH seed = 32 ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
           read PC s = word (pc + ???) /\
           read SP s = sp /\
           read X30 s = word retpc /\
           C_ARGUMENTS [A_p; seed_p] s /\
           byte_list_at seed seed_p s)
      (\s. read PC s = word retpc /\
           byte_list_at (public_key_of_seed seed) A_p s)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(A_p, 32)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)])`,
  );;

(* size_t dom2_common(
    uint8_t dom2_buffer[MAX_DOM2_SIZE], const uint64_t phflag,
    const uint8_t *context, size_t context_len) *)
let DOM2_COMMON_CORRECT = prove
  (`!dom2_buf_p phflag ctx_p ctx pc retpc.
    PAIRWISE nonoverlapping [(word pc, ???); (dom2_buf_p, max_dom2_size); (ctx_p, LENGTH ctx)] /\
    LENGTH ctx <= 255 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
         read PC s = word (pc + ???) /\
         read X30 s = word retpc /\
         C_ARGUMENTS [dom2_buf_p, phflag, ctx_p, word (LENGTH ctx)] s /\
         byte_list_at ctx ctx_p s)
    (\s. read PC s = word retpc /\
         byte_list_at (dom2_prefix ++ [word phflag] ++ [word ctx_len] ++ ctx) /\
         C_RETURN s = LENGTH (dom2_prefix ++ [word phflag] ++ [word ctx_len] ++ ctx))
    (MAYCHANGE [X0; X4; X5] ;;
     MAYCHANGE [memory :> bytes(dom2_buf_p, max_dom2_size)])`,
  );;

(* void ed25519_sign_common(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    uint8_t *dom2_buffer, size_t dom2_buffer_len) *)
let ED25519_SIGN_COMMON_CORRECT = prove
  (`!sp sig_p msg_p msg priv_key_p seed A dom2_buf_p alg ctx pc retpc.
    PAIRWISE nonoverlapping [(word pc, ???); (sig_p, 64); (msg_p; LENGTH (ph alg msg)); (priv_key_p, 64); (dom2_buf_p, max_dom2_size); (word_sub sp (word ???), ???)] /\
    LENGTH (ph alg msg) < 2 EXP 64 /\
    LENGTH seed = 32 /\
    A = public_key_of_seed seed /\
    dom2_valid alg ctx ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
         read PC s = word (pc + ???) /\
         read SP s = sp /\
         read X30 s = word retpc /\
         C_ARGUMENTS [sig_p; msg_p; word (LENGTH (ph alg msg)); priv_key_p; dom2_buf_p, word (LENGTH (dom2_of alg ctx))] s /\
         byte_list_at (ph alg msg) msg_p s /\
         byte_list_at (seed ++ A) priv_key_p s /\
         byte_list_at (dom2_of alg ctx) dom2_buf_p s)
    (\s. read PC s = word retpc /\
         byte_list_at (sign alg seed msg) sig_p s)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ;;
     MAYCHANGE [memory :> bytes(sig_p, 64)] ;;
     MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)])`,
  );;

(* int ed25519_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN]) *)
let ED25519_SIGN_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  (`!sp sig_p msg_p msg priv_key_p seed A pc retpc.
    PAIRWISE nonoverlapping [(word pc, ???); (sig_p, 64); (msg_p; LENGTH msg); (priv_key_p, 64); (word_sub sp (word ???), ???)] /\
    LENGTH msg < 2 EXP 64 /\
    LENGTH seed = 32 /\
    A = public_key_of_seed seed ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
         read PC s = word (pc + ???) /\
         read SP s = sp /\
         read X30 s = word retpc /\
         C_ARGUMENTS [sig_p; msg_p; word (LENGTH msg); priv_key_p] s /\
         byte_list_at msg msg_p s /\
         byte_list_at (seed ++ A) priv_key_p s)
    (\s. read PC s = word retpc /\
         byte_list_at (sign 0 [] seed msg) sig_p s /\
         C_RETURN s = word 1)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ;;
     MAYCHANGE [memory :> bytes(sig_p, 64)] ;;
     MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)])`,
     );;

(* int ed25519ctx_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len) *)
let ED25519CTX_SIGN_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  (`!sp sig_p msg_p msg priv_key_p seed A ctx_p ctx pc retpc.
    PAIRWISE nonoverlapping [(word pc, ???); (sig_p, 64); (msg_p; LENGTH msg); (priv_key_p, 64); (ctx_p, LENGTH ctx); (word_sub sp (word ???), ???)] /\
    LENGTH msg < 2 EXP 64 /\
    LENGTH seed = 32 /\
    A = public_key_of_seed seed /\
    LENGTH ctx < 2 EXP 64 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
         read PC s = word (pc + ???) /\
         read SP s = sp /\
         read X30 s = word retpc /\
         C_ARGUMENTS [sig_p; msg_p; word (LENGTH msg); priv_key_p; ctx_p, word (LENGTH ctx)] s /\
         byte_list_at msg msg_p s /\
         byte_list_at (seed ++ A) priv_key_p s /\
         byte_list_at ctx ctx_p s)
    (\s. read PC s = word retpc /\
      if dom_valid 1 ctx
        then C_RETURN s = word 1 /\ byte_list_at (sign 1 ctx seed m) sig_p s
        else C_RETURN s = 0)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ;;
     MAYCHANGE [memory :> bytes(sig_p, 64)] ;;
     MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)])`,
  );;

(* int ed25519ph_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len) *)
let ED25519PH_SIGN_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  (`!sp sig_p msg_p msg priv_key_p seed A ctx_p ctx pc retpc.
    PAIRWISE nonoverlapping [(word pc, ???); (sig_p, 64); (msg_p; LENGTH msg); (priv_key_p, 64); (ctx_p, LENGTH ctx); (word_sub sp (word ???), ???)] /\
    LENGTH msg < 2 EXP 64 /\
    LENGTH seed = 32 /\
    A = public_key_of_seed seed /\
    LENGTH ctx < 2 EXP 64 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
         read PC s = word (pc + ???) /\
         read SP s = sp /\
         read X30 s = word retpc /\
         C_ARGUMENTS [sig_p; msg_p; word (LENGTH msg); priv_key_p; ctx_p, word (LENGTH ctx)] s /\
         byte_list_at msg msg_p s /\
         byte_list_at (seed ++ A) priv_key_p s /\
         byte_list_at ctx ctx_p s)
    (\s. read PC s = word retpc /\
      if dom_valid 2 ctx
        then C_RETURN s = word 1 /\ byte_list_at (sign 2 ctx seed m) sig_p s
        else C_RETURN s = 0)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ;;
     MAYCHANGE [memory :> bytes(sig_p, 64)] ;;
     MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)])`,
  );;

(* int ed25519_verify_common(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
    uint8_t *dom2_buffer, size_t dom2_buffer_len) *)
let ED25519_VERIFY_COMMON_CORRECT = prove
  (`!sp msg_p msg sig_p sig A_p A dom2_buf_p alg ctx pc retpc.
    PAIRWISE nonoverlapping [(word pc, ???); (msg_p; LENGTH (ph alg msg)); (sig_p, 64); (A_p, 32); (dom2_buf_p, max_dom2_size); (word_sub sp (word ???), ???)] /\
    LENGTH (ph alg msg) < 2 EXP 64 /\
    LENGTH sig = 64 /\
    LENGTH A = 32 /\
    dom2_valid alg ctx ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
         read PC s = word (pc + ???) /\
         read SP s = sp /\
         read X30 s = word retpc /\
         C_ARGUMENTS [msg_p; word (LENGTH (ph alg msg)); sig_p; A_p; dom2_buf_p, word (LENGTH (dom2_of alg ctx))] s /\
         byte_list_at (ph alg msg) msg_p s /\
         byte_list_at A A_p s /\
         byte_list_at (dom2_of alg ctx) dom2_buf_p s)
    (\s. read PC s = word retpc /\
         if verify_args_valid A sig /\ verify alg ctx A sig msg
            then C_RETURN s = word 1
            else C_RETURN s = word 0)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ;;
     MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)])`,
  );;

(* int ed25519_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN]) *)
let ED25519_VERIFY_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  (`!sp msg_p msg sig_p sig A_p A pc retpc.
    PAIRWISE nonoverlapping [(word pc, ???); (msg_p; LENGTH msg); (sig_p, 64);
      (A_p, 32); (word_sub sp (word ???), ???)] /\
    LENGTH msg < 2 EXP 64 /\
    LENGTH sig = 64 /\
    LENGTH A = 32 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
         read PC s = word (pc + ???) /\
         read SP s = sp /\
         read X30 s = word retpc /\
         C_ARGUMENTS [msg_p; word (LENGTH msg); sig_p; A_p] s /\
         byte_list_at msg msg_p s /\
         byte_list_at A A_p s)
    (\s. read PC s = word retpc /\
         if verify_args_valid A sig /\ verify 0 [] A sig msg
            then C_RETURN s = word 1
            else C_RETURN s = word 0)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ;;
     MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)])`,
  );;

(* int ed25519ctx_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len) *)
let ED25519CTX_VERIFY_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  (`!sp msg_p msg sig_p sig A_p A ctx_p ctx pc retpc.
    PAIRWISE nonoverlapping [(word pc, ???); (msg_p; LENGTH msg); (sig_p, 64);
      (A_p, 32); (ctx_p, LENGTH ctx); (word_sub sp (word ???), ???)] /\
    LENGTH msg < 2 EXP 64 /\
    LENGTH sig = 64 /\
    LENGTH A = 32 /\
    LENGTH ctx < 2 EXP 64 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
         read PC s = word (pc + ???) /\
         read SP s = sp /\
         read X30 s = word retpc /\
         C_ARGUMENTS [msg_p; word (LENGTH msg); sig_p; A_p; ctx_p, word (LENGTH ctx)] s /\
         byte_list_at msg msg_p s /\
         byte_list_at A A_p s /\
         byte_list_at ctx ctx_p s)
    (\s. read PC s = word retpc /\
         if dom2_valid 1 ctx /\ verify_args_valid A sig /\ verify 1 ctx A sig msg
            then C_RETURN s = word 1
            else C_RETURN s = word 0)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ;;
     MAYCHANGE [memory :> bytes(sig_p, 64)] ;;
     MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)])`,
  );;

(* int ed25519ph_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len) *)
let ED25519PH_VERIFY_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  (`!sp msg_p msg sig_p sig A_p A ctx_p ctx pc retpc.
    PAIRWISE nonoverlapping [(word pc, ???); (msg_p; LENGTH msg); (sig_p, 64);
      (A_p, 32); (ctx_p, LENGTH ctx); (word_sub sp (word ???), ???)] /\
    LENGTH msg < 2 EXP 64 /\
    LENGTH sig = 64 /\
    LENGTH A = 32 /\
    LENGTH ctx < 2 EXP 64 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
         read PC s = word (pc + ???) /\
         read SP s = sp /\
         read X30 s = word retpc /\
         C_ARGUMENTS [msg_p; word (LENGTH msg); sig_p; A_p; ctx_p, word (LENGTH ctx)] s /\
         byte_list_at msg msg_p s /\
         byte_list_at A A_p s /\
         byte_list_at ctx ctx_p s)
    (\s. read PC s = word retpc /\
         if dom2_valid 2 ctx /\ verify_args_valid A sig /\ verify 2 ctx A sig msg
            then C_RETURN s = word 1
            else C_RETURN s = word 0)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ;;
     MAYCHANGE [memory :> bytes(sig_p, 64)] ;;
     MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)])`,
  );;
