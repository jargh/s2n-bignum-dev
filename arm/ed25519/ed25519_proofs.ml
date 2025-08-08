needs "arm/sha512/sha512_proofs.ml";;
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
  w 0x94000231;         (* arm_BL (word 2244) *)
  w 0x910063e0;         (* arm_ADD X0 SP (rvalue (word 24)) *)
  w 0xaa1403e1;         (* arm_MOV X1 X20 *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  w 0x94000255;         (* arm_BL (word 2388) *)
  w 0x9103c3e0;         (* arm_ADD X0 SP (rvalue (word 240)) *)
  w 0x910063e1;         (* arm_ADD X1 SP (rvalue (word 24)) *)
  w 0x9400028c;         (* arm_BL (word 2608) *)
  w 0x3943c3e0;         (* arm_LDRB W0 SP (Immediate_Offset (word 240)) *)
  w 0x121d1000;         (* arm_AND W0 W0 (rvalue (word 248)) *)
  w 0x3903c3e0;         (* arm_STRB W0 SP (Immediate_Offset (word 240)) *)
  w 0x39443fe0;         (* arm_LDRB W0 SP (Immediate_Offset (word 271)) *)
  w 0x12001800;         (* arm_AND W0 W0 (rvalue (word 127)) *)
  w 0x321a0000;         (* arm_ORR W0 W0 (rvalue (word 64)) *)
  w 0x39043fe0;         (* arm_STRB W0 SP (Immediate_Offset (word 271)) *)
  w 0x9104c3e0;         (* arm_ADD X0 SP (rvalue (word 304)) *)
  w 0x9103c3e1;         (* arm_ADD X1 SP (rvalue (word 240)) *)
  w 0x94000175;         (* arm_BL (word 1492) *)
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0x9104c3e1;         (* arm_ADD X1 SP (rvalue (word 304)) *)
  w 0x94000170;         (* arm_BL (word 1472) *)
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
  w 0x9400020d;         (* arm_BL (word 2100) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1603e1;         (* arm_MOV X1 X22 *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  w 0x94000231;         (* arm_BL (word 2244) *)
  w 0x910443e0;         (* arm_ADD X0 SP (rvalue (word 272)) *)
  w 0x9100e3e1;         (* arm_ADD X1 SP (rvalue (word 56)) *)
  w 0x94000268;         (* arm_BL (word 2464) *)
  w 0x394443e0;         (* arm_LDRB W0 SP (Immediate_Offset (word 272)) *)
  w 0x121d1000;         (* arm_AND W0 W0 (rvalue (word 248)) *)
  w 0x390443e0;         (* arm_STRB W0 SP (Immediate_Offset (word 272)) *)
  w 0x3944bfe0;         (* arm_LDRB W0 SP (Immediate_Offset (word 303)) *)
  w 0x12001800;         (* arm_AND W0 W0 (rvalue (word 127)) *)
  w 0x321a0000;         (* arm_ORR W0 W0 (rvalue (word 64)) *)
  w 0x3904bfe0;         (* arm_STRB W0 SP (Immediate_Offset (word 303)) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0x940001fd;         (* arm_BL (word 2036) *)
  w 0xb40000b8;         (* arm_CBZ X24 (word 20) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1703e1;         (* arm_MOV X1 X23 *)
  w 0xaa1803e2;         (* arm_MOV X2 X24 *)
  w 0x94000220;         (* arm_BL (word 2176) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0x9104c3e1;         (* arm_ADD X1 SP (rvalue (word 304)) *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  w 0x9400021c;         (* arm_BL (word 2160) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1403e1;         (* arm_MOV X1 X20 *)
  w 0xaa1503e2;         (* arm_MOV X2 X21 *)
  w 0x94000218;         (* arm_BL (word 2144) *)
  w 0x910543e0;         (* arm_ADD X0 SP (rvalue (word 336)) *)
  w 0x9100e3e1;         (* arm_ADD X1 SP (rvalue (word 56)) *)
  w 0x9400024f;         (* arm_BL (word 2364) *)
  w 0x910543e0;         (* arm_ADD X0 SP (rvalue (word 336)) *)
  w 0xd2800101;         (* arm_MOV X1 (rvalue (word 8)) *)
  w 0xaa0003e2;         (* arm_MOV X2 X0 *)
  w 0x94000140;         (* arm_BL (word 1280) *)
  w 0x910643e0;         (* arm_ADD X0 SP (rvalue (word 400)) *)
  w 0x910543e1;         (* arm_ADD X1 SP (rvalue (word 336)) *)
  w 0x9400013b;         (* arm_BL (word 1260) *)
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0x910643e1;         (* arm_ADD X1 SP (rvalue (word 400)) *)
  w 0x94000136;         (* arm_BL (word 1240) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0x940001e1;         (* arm_BL (word 1924) *)
  w 0xb40000b8;         (* arm_CBZ X24 (word 20) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1703e1;         (* arm_MOV X1 X23 *)
  w 0xaa1803e2;         (* arm_MOV X2 X24 *)
  w 0x94000204;         (* arm_BL (word 2064) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1303e1;         (* arm_MOV X1 X19 *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  w 0x94000200;         (* arm_BL (word 2048) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0x910082c1;         (* arm_ADD X1 X22 (rvalue (word 32)) *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  w 0x940001fc;         (* arm_BL (word 2032) *)
  w 0x9100e3e0;         (* arm_ADD X0 SP (rvalue (word 56)) *)
  w 0xaa1403e1;         (* arm_MOV X1 X20 *)
  w 0xaa1503e2;         (* arm_MOV X2 X21 *)
  w 0x940001f8;         (* arm_BL (word 2016) *)
  w 0x910743e0;         (* arm_ADD X0 SP (rvalue (word 464)) *)
  w 0x9100e3e1;         (* arm_ADD X1 SP (rvalue (word 56)) *)
  w 0x9400022f;         (* arm_BL (word 2236) *)
  w 0x910743e0;         (* arm_ADD X0 SP (rvalue (word 464)) *)
  w 0xd2800101;         (* arm_MOV X1 (rvalue (word 8)) *)
  w 0xaa0003e2;         (* arm_MOV X2 X0 *)
  w 0x94000120;         (* arm_BL (word 1152) *)
  w 0x91008260;         (* arm_ADD X0 X19 (rvalue (word 32)) *)
  w 0x910743e1;         (* arm_ADD X1 SP (rvalue (word 464)) *)
  w 0x910443e2;         (* arm_ADD X2 SP (rvalue (word 272)) *)
  w 0x910543e3;         (* arm_ADD X3 SP (rvalue (word 336)) *)
  w 0x9400011d;         (* arm_BL (word 1140) *)
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
  w 0x940000fb;         (* arm_BL (word 1004) *)
  w 0xb5000720;         (* arm_CBNZ X0 (word 228) *)
  w 0x910163e0;         (* arm_ADD X0 SP (rvalue (word 88)) *)
  w 0xaa1603e1;         (* arm_MOV X1 X22 *)
  w 0x940000f1;         (* arm_BL (word 964) *)
  w 0xb50006a0;         (* arm_CBNZ X0 (word 212) *)
  w 0x910263e0;         (* arm_ADD X0 SP (rvalue (word 152)) *)
  w 0x9400019a;         (* arm_BL (word 1640) *)
  w 0xb40000b8;         (* arm_CBZ X24 (word 20) *)
  w 0x910263e0;         (* arm_ADD X0 SP (rvalue (word 152)) *)
  w 0xaa1703e1;         (* arm_MOV X1 X23 *)
  w 0xaa1803e2;         (* arm_MOV X2 X24 *)
  w 0x940001bd;         (* arm_BL (word 1780) *)
  w 0x910263e0;         (* arm_ADD X0 SP (rvalue (word 152)) *)
  w 0xaa1503e1;         (* arm_MOV X1 X21 *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  w 0x940001b9;         (* arm_BL (word 1764) *)
  w 0x910263e0;         (* arm_ADD X0 SP (rvalue (word 152)) *)
  w 0xaa1603e1;         (* arm_MOV X1 X22 *)
  w 0xd2800402;         (* arm_MOV X2 (rvalue (word 32)) *)
  w 0x940001b5;         (* arm_BL (word 1748) *)
  w 0x910263e0;         (* arm_ADD X0 SP (rvalue (word 152)) *)
  w 0xaa1303e1;         (* arm_MOV X1 X19 *)
  w 0xaa1403e2;         (* arm_MOV X2 X20 *)
  w 0x940001b1;         (* arm_BL (word 1732) *)
  w 0x9105c3e0;         (* arm_ADD X0 SP (rvalue (word 368)) *)
  w 0x910263e1;         (* arm_ADD X1 SP (rvalue (word 152)) *)
  w 0x940001e8;         (* arm_BL (word 1952) *)
  w 0x910163e0;         (* arm_ADD X0 SP (rvalue (word 88)) *)
  w 0xaa0003e1;         (* arm_MOV X1 X0 *)
  w 0x940000db;         (* arm_BL (word 876) *)
  w 0x9105c3e0;         (* arm_ADD X0 SP (rvalue (word 368)) *)
  w 0xd2800101;         (* arm_MOV X1 (rvalue (word 8)) *)
  w 0xaa0003e2;         (* arm_MOV X2 X0 *)
  w 0x940000d6;         (* arm_BL (word 856) *)
  w 0x9106c3e0;         (* arm_ADD X0 SP (rvalue (word 432)) *)
  w 0x9105c3e1;         (* arm_ADD X1 SP (rvalue (word 368)) *)
  w 0x910163e2;         (* arm_ADD X2 SP (rvalue (word 88)) *)
  w 0x910082a3;         (* arm_ADD X3 X21 (rvalue (word 32)) *)
  w 0x940000d0;         (* arm_BL (word 832) *)
  w 0x9107c3e0;         (* arm_ADD X0 SP (rvalue (word 496)) *)
  w 0x9106c3e1;         (* arm_ADD X1 SP (rvalue (word 432)) *)
  w 0x940000ca;         (* arm_BL (word 808) *)
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
  w 0x940000eb;         (* arm_BL (word 940) *)
  w 0x910563e0;         (* arm_ADD X0 SP (rvalue (word 344)) *)
  w 0xaa1403e1;         (* arm_MOV X1 X20 *)
  w 0xaa1503e2;         (* arm_MOV X2 X21 *)
  w 0x9400010f;         (* arm_BL (word 1084) *)
  w 0x9108c3e0;         (* arm_ADD X0 SP (rvalue (word 560)) *)
  w 0x910563e1;         (* arm_ADD X1 SP (rvalue (word 344)) *)
  w 0x94000146;         (* arm_BL (word 1304) *)
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
  w 0x940000c3;         (* arm_BL (word 780) *)
  w 0x910563e0;         (* arm_ADD X0 SP (rvalue (word 344)) *)
  w 0xaa1303e1;         (* arm_MOV X1 X19 *)
  w 0xaa1403e2;         (* arm_MOV X2 X20 *)
  w 0x940000e7;         (* arm_BL (word 924) *)
  w 0x9108c3e0;         (* arm_ADD X0 SP (rvalue (word 560)) *)
  w 0x910563e1;         (* arm_ADD X1 SP (rvalue (word 344)) *)
  w 0x9400011e;         (* arm_BL (word 1144) *)
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
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd2800003;         (* arm_MOV X3 (rvalue (word 0)) *)
  w 0x39400025;         (* arm_LDRB W5 X1 (Immediate_Offset (word 0)) *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0x91002021;         (* arm_ADD X1 X1 (rvalue (word 8)) *)
  w 0x385f9024;         (* arm_LDRB W4 X1 (Immediate_Offset (word 18446744073709551609)) *)
  w 0x385fa026;         (* arm_LDRB W6 X1 (Immediate_Offset (word 18446744073709551610)) *)
  w 0xb3401ca2;         (* arm_BFM X2 X5 0 7 *)
  w 0x385fb025;         (* arm_LDRB W5 X1 (Immediate_Offset (word 18446744073709551611)) *)
  w 0xb3781c82;         (* arm_BFM X2 X4 56 7 *)
  w 0x385fc024;         (* arm_LDRB W4 X1 (Immediate_Offset (word 18446744073709551612)) *)
  w 0xb3701cc2;         (* arm_BFM X2 X6 48 7 *)
  w 0x385fd026;         (* arm_LDRB W6 X1 (Immediate_Offset (word 18446744073709551613)) *)
  w 0xb3681ca2;         (* arm_BFM X2 X5 40 7 *)
  w 0x385fe025;         (* arm_LDRB W5 X1 (Immediate_Offset (word 18446744073709551614)) *)
  w 0xb3601c82;         (* arm_BFM X2 X4 32 7 *)
  w 0x385ff024;         (* arm_LDRB W4 X1 (Immediate_Offset (word 18446744073709551615)) *)
  w 0xb3581cc2;         (* arm_BFM X2 X6 24 7 *)
  w 0xb3501ca2;         (* arm_BFM X2 X5 16 7 *)
  w 0xb3481c82;         (* arm_BFM X2 X4 8 7 *)
  w 0xdac00c42;         (* arm_REV X2 X2 *)
  w 0xf8237802;         (* arm_STR X2 X0 (Shiftreg_Offset X3 3) *)
  w 0x91000463;         (* arm_ADD X3 X3 (rvalue (word 1)) *)
  w 0xf100407f;         (* arm_CMP X3 (rvalue (word 16)) *)
  w 0x54fffd41;         (* arm_BNE (word 2097064) *)
  w 0xaa0003e2;         (* arm_MOV X2 X0 *)
  w 0x9108200b;         (* arm_ADD X11 X0 (rvalue (word 520)) *)
  w 0xa9452009;         (* arm_LDP X9 X8 X0 (Immediate_Offset (iword (&80))) *)
  w 0xa9461807;         (* arm_LDP X7 X6 X0 (Immediate_Offset (iword (&96))) *)
  w 0xa9470003;         (* arm_LDP X3 X0 X0 (Immediate_Offset (iword (&112))) *)
  w 0xf940244a;         (* arm_LDR X10 X2 (Immediate_Offset (word 72)) *)
  w 0xf8408444;         (* arm_LDR X4 X2 (Postimmediate_Offset (word 8)) *)
  w 0x8b0a0085;         (* arm_ADD X5 X4 X10 *)
  w 0x93c3f461;         (* arm_ROR X1 X3 61 *)
  w 0xf9400044;         (* arm_LDR X4 X2 (Immediate_Offset (word 0)) *)
  w 0xcac34c21;         (* arm_EOR X1 X1 (Shiftedreg X3 ROR 19) *)
  w 0xaa0903ea;         (* arm_MOV X10 X9 *)
  w 0xaa0803e9;         (* arm_MOV X9 X8 *)
  w 0xaa0703e8;         (* arm_MOV X8 X7 *)
  w 0xca431821;         (* arm_EOR X1 X1 (Shiftedreg X3 LSR 6) *)
  w 0xaa0603e7;         (* arm_MOV X7 X6 *)
  w 0xaa0303e6;         (* arm_MOV X6 X3 *)
  w 0xaa0003e3;         (* arm_MOV X3 X0 *)
  w 0x91002042;         (* arm_ADD X2 X2 (rvalue (word 8)) *)
  w 0x93c42080;         (* arm_ROR X0 X4 8 *)
  w 0xcac40400;         (* arm_EOR X0 X0 (Shiftedreg X4 ROR 1) *)
  w 0xca441c00;         (* arm_EOR X0 X0 (Shiftedreg X4 LSR 7) *)
  w 0x8b010000;         (* arm_ADD X0 X0 X1 *)
  w 0x8b050000;         (* arm_ADD X0 X0 X5 *)
  w 0xf9003840;         (* arm_STR X0 X2 (Immediate_Offset (word 112)) *)
  w 0xeb02017f;         (* arm_CMP X11 X2 *)
  w 0x54fffda1;         (* arm_BNE (word 2097076) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd10b43ff;         (* arm_SUB SP SP (rvalue (word 720)) *)
  w 0xaa0003ec;         (* arm_MOV X12 X0 *)
  w 0x910143e0;         (* arm_ADD X0 SP (rvalue (word 80)) *)
  w 0xa9007bfd;         (* arm_STP X29 X30 SP (Immediate_Offset (iword (&0))) *)
  w 0x910003fd;         (* arm_ADD X29 SP (rvalue (word 0)) *)
  w 0x97ffffc7;         (* arm_BL (word 268435228) *)
  w 0xf2400d9f;         (* arm_TST X12 (rvalue (word 15)) *)
  w 0x54000961;         (* arm_BNE (word 300) *)
  w 0xa9401d86;         (* arm_LDP X6 X7 X12 (Immediate_Offset (iword (&0))) *)
  w 0xa9411584;         (* arm_LDP X4 X5 X12 (Immediate_Offset (iword (&16))) *)
  w 0xa9420d82;         (* arm_LDP X2 X3 X12 (Immediate_Offset (iword (&32))) *)
  w 0xa9430580;         (* arm_LDP X0 X1 X12 (Immediate_Offset (iword (&48))) *)
  w 0xa9011fe6;         (* arm_STP X6 X7 SP (Immediate_Offset (iword (&16))) *)
  w 0xa90217e4;         (* arm_STP X4 X5 SP (Immediate_Offset (iword (&32))) *)
  w 0xa9030fe2;         (* arm_STP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  w 0xa90407e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  ADRP (mk_var("K",`:num`),0,1876,14);
  w 0xd2800026;         (* arm_MOV X6 (rvalue (word 1)) *)
  ADD_rri64 (mk_var("K",`:num`),0,14,14);
  w 0xa94123e5;         (* arm_LDP X5 X8 SP (Immediate_Offset (iword (&16))) *)
  w 0xa94237e7;         (* arm_LDP X7 X13 SP (Immediate_Offset (iword (&32))) *)
  w 0xa9432be3;         (* arm_LDP X3 X10 SP (Immediate_Offset (iword (&48))) *)
  w 0xa9442fe9;         (* arm_LDP X9 X11 SP (Immediate_Offset (iword (&64))) *)
  w 0x14000007;         (* arm_B (word 28) *)
  w 0xaa0803e7;         (* arm_MOV X7 X8 *)
  w 0xaa0a03e9;         (* arm_MOV X9 X10 *)
  w 0xaa0503e8;         (* arm_MOV X8 X5 *)
  w 0xaa0303ea;         (* arm_MOV X10 X3 *)
  w 0xaa0003e5;         (* arm_MOV X5 X0 *)
  w 0xaa0203e3;         (* arm_MOV X3 X2 *)
  w 0xd37df0c1;         (* arm_LSL X1 X6 3 *)
  w 0x910143e4;         (* arm_ADD X4 SP (rvalue (word 80)) *)
  w 0x93c34860;         (* arm_ROR X0 X3 18 *)
  w 0x8b0101c2;         (* arm_ADD X2 X14 X1 *)
  w 0x8b01008f;         (* arm_ADD X15 X4 X1 *)
  w 0xcac33800;         (* arm_EOR X0 X0 (Shiftedreg X3 ROR 14) *)
  w 0x93c588a1;         (* arm_ROR X1 X5 34 *)
  w 0xf85f8050;         (* arm_LDR X16 X2 (Immediate_Offset (word 18446744073709551608)) *)
  w 0xcac57021;         (* arm_EOR X1 X1 (Shiftedreg X5 ROR 28) *)
  w 0x8a230124;         (* arm_BIC X4 X9 X3 *)
  w 0xcac3a400;         (* arm_EOR X0 X0 (Shiftedreg X3 ROR 41) *)
  w 0x8a0a0072;         (* arm_AND X18 X3 X10 *)
  w 0xca0800e2;         (* arm_EOR X2 X7 X8 *)
  w 0xf85f81f1;         (* arm_LDR X17 X15 (Immediate_Offset (word 18446744073709551608)) *)
  w 0xca120084;         (* arm_EOR X4 X4 X18 *)
  w 0xcac59c21;         (* arm_EOR X1 X1 (Shiftedreg X5 ROR 39) *)
  w 0x8b040000;         (* arm_ADD X0 X0 X4 *)
  w 0x8a050042;         (* arm_AND X2 X2 X5 *)
  w 0x8a0800e4;         (* arm_AND X4 X7 X8 *)
  w 0x910004c6;         (* arm_ADD X6 X6 (rvalue (word 1)) *)
  w 0xca040042;         (* arm_EOR X2 X2 X4 *)
  w 0x8b020021;         (* arm_ADD X1 X1 X2 *)
  w 0x8b110202;         (* arm_ADD X2 X16 X17 *)
  w 0x8b020000;         (* arm_ADD X0 X0 X2 *)
  w 0x8b0b0000;         (* arm_ADD X0 X0 X11 *)
  w 0xaa0903eb;         (* arm_MOV X11 X9 *)
  w 0x8b0001a2;         (* arm_ADD X2 X13 X0 *)
  w 0x8b010000;         (* arm_ADD X0 X0 X1 *)
  w 0xaa0703ed;         (* arm_MOV X13 X7 *)
  w 0xf10144df;         (* arm_CMP X6 (rvalue (word 81)) *)
  w 0x54fffb81;         (* arm_BNE (word 2097008) *)
  w 0xa9401186;         (* arm_LDP X6 X4 X12 (Immediate_Offset (iword (&0))) *)
  w 0xa9407bfd;         (* arm_LDP X29 X30 SP (Immediate_Offset (iword (&0))) *)
  w 0x8b0000c6;         (* arm_ADD X6 X6 X0 *)
  w 0x8b050084;         (* arm_ADD X4 X4 X5 *)
  w 0xa9419580;         (* arm_LDP X0 X5 X12 (Immediate_Offset (iword (&24))) *)
  w 0xa9001186;         (* arm_STP X6 X4 X12 (Immediate_Offset (iword (&0))) *)
  w 0x8b070000;         (* arm_ADD X0 X0 X7 *)
  w 0x8b0200a5;         (* arm_ADD X5 X5 X2 *)
  w 0xf9400981;         (* arm_LDR X1 X12 (Immediate_Offset (word 16)) *)
  w 0xf9001185;         (* arm_STR X5 X12 (Immediate_Offset (word 32)) *)
  w 0x8b080021;         (* arm_ADD X1 X1 X8 *)
  w 0xa9010181;         (* arm_STP X1 X0 X12 (Immediate_Offset (iword (&16))) *)
  w 0xa9428584;         (* arm_LDP X4 X1 X12 (Immediate_Offset (iword (&40))) *)
  w 0xf9401d80;         (* arm_LDR X0 X12 (Immediate_Offset (word 56)) *)
  w 0x8b030082;         (* arm_ADD X2 X4 X3 *)
  w 0x8b0a0021;         (* arm_ADD X1 X1 X10 *)
  w 0xa9028582;         (* arm_STP X2 X1 X12 (Immediate_Offset (iword (&40))) *)
  w 0x8b090000;         (* arm_ADD X0 X0 X9 *)
  w 0xf9001d80;         (* arm_STR X0 X12 (Immediate_Offset (word 56)) *)
  w 0x910b43ff;         (* arm_ADD SP SP (rvalue (word 720)) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xa9400181;         (* arm_LDP X1 X0 X12 (Immediate_Offset (iword (&0))) *)
  w 0xf9400982;         (* arm_LDR X2 X12 (Immediate_Offset (word 16)) *)
  w 0xa90103e1;         (* arm_STP X1 X0 SP (Immediate_Offset (iword (&16))) *)
  w 0xa9418181;         (* arm_LDP X1 X0 X12 (Immediate_Offset (iword (&24))) *)
  w 0xf90013e2;         (* arm_STR X2 SP (Immediate_Offset (word 32)) *)
  w 0xf9401582;         (* arm_LDR X2 X12 (Immediate_Offset (word 40)) *)
  w 0xa90283e1;         (* arm_STP X1 X0 SP (Immediate_Offset (iword (&40))) *)
  w 0xa9430181;         (* arm_LDP X1 X0 X12 (Immediate_Offset (iword (&48))) *)
  w 0xf9001fe2;         (* arm_STR X2 SP (Immediate_Offset (word 56)) *)
  w 0xa90403e1;         (* arm_STP X1 X0 SP (Immediate_Offset (iword (&64))) *)
  w 0x17ffffb4;         (* arm_B (word 268435152) *)
  w 0xb4000262;         (* arm_CBZ X2 (word 76) *)
  w 0xa9bd7bfd;         (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &48))) *)
  w 0x910003fd;         (* arm_ADD X29 SP (rvalue (word 0)) *)
  w 0xa90153f3;         (* arm_STP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xaa0103f3;         (* arm_MOV X19 X1 *)
  w 0xd1000454;         (* arm_SUB X20 X2 (rvalue (word 1)) *)
  w 0xf90013f5;         (* arm_STR X21 SP (Immediate_Offset (word 32)) *)
  w 0xaa0003f5;         (* arm_MOV X21 X0 *)
  w 0xaa1303e1;         (* arm_MOV X1 X19 *)
  w 0xaa1503e0;         (* arm_MOV X0 X21 *)
  w 0xd1000694;         (* arm_SUB X20 X20 (rvalue (word 1)) *)
  w 0x91020273;         (* arm_ADD X19 X19 (rvalue (word 128)) *)
  w 0x97ffff97;         (* arm_BL (word 268435036) *)
  w 0xb100069f;         (* arm_CMN X20 (rvalue (word 1)) *)
  w 0x54ffff41;         (* arm_BNE (word 2097128) *)
  w 0xa94153f3;         (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94013f5;         (* arm_LDR X21 SP (Immediate_Offset (word 32)) *)
  w 0xa8c37bfd;         (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&48))) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd2992101;         (* arm_MOV X1 (rvalue (word 51464)) *)
  w 0xd294e767;         (* arm_MOV X7 (rvalue (word 42811)) *)
  w 0xa9047c1f;         (* arm_STP XZR XZR X0 (Immediate_Offset (iword (&64))) *)
  w 0xf2be7781;         (* arm_MOVK X1 (word 62396) 16 *)
  w 0xf2b09947;         (* arm_MOVK X7 (word 33994) 16 *)
  w 0xf2dccce1;         (* arm_MOVK X1 (word 58983) 32 *)
  w 0xf2d5d0a7;         (* arm_MOVK X7 (word 44677) 32 *)
  w 0xf2ed4121;         (* arm_MOVK X1 (word 27145) 48 *)
  w 0xf2f76ce7;         (* arm_MOVK X7 (word 47975) 48 *)
  w 0x3903401f;         (* arm_STRB WZR X0 (Immediate_Offset (word 208)) *)
  w 0xd29f0566;         (* arm_MOV X6 (rvalue (word 63531)) *)
  w 0xd286de25;         (* arm_MOV X5 (rvalue (word 14065)) *)
  w 0xd2905a24;         (* arm_MOV X4 (rvalue (word 33489)) *)
  w 0xd28d83e3;         (* arm_MOV X3 (rvalue (word 27679)) *)
  w 0xa9001c01;         (* arm_STP X1 X7 X0 (Immediate_Offset (iword (&0))) *)
  w 0xd297ad62;         (* arm_MOV X2 (rvalue (word 48491)) *)
  w 0xd2842f21;         (* arm_MOV X1 (rvalue (word 8569)) *)
  w 0xf2bfd286;         (* arm_MOVK X6 (word 65172) 16 *)
  w 0xf2abe3a5;         (* arm_MOVK X5 (word 24349) 16 *)
  w 0xf2b5bcc4;         (* arm_MOVK X4 (word 44518) 16 *)
  w 0xf2a567c3;         (* arm_MOVK X3 (word 11070) 16 *)
  w 0xf2bf6822;         (* arm_MOVK X2 (word 64321) 16 *)
  w 0xf2a26fc1;         (* arm_MOVK X1 (word 4990) 16 *)
  w 0xf2de6e46;         (* arm_MOVK X6 (word 62322) 32 *)
  w 0xf2dea745;         (* arm_MOVK X5 (word 62778) 32 *)
  w 0xf2ca4fe4;         (* arm_MOVK X4 (word 21119) 32 *)
  w 0xf2cd1183;         (* arm_MOVK X3 (word 26764) 32 *)
  w 0xf2db3562;         (* arm_MOVK X2 (word 55723) 32 *)
  w 0xf2d9a321;         (* arm_MOVK X1 (word 52505) 32 *)
  w 0xf2e78dc6;         (* arm_MOVK X6 (word 15470) 48 *)
  w 0xf2f4a9e5;         (* arm_MOVK X5 (word 42319) 48 *)
  w 0xf2ea21c4;         (* arm_MOVK X4 (word 20750) 48 *)
  w 0xf2f360a3;         (* arm_MOVK X3 (word 39685) 48 *)
  w 0xf2e3f062;         (* arm_MOVK X2 (word 8067) 48 *)
  w 0xf2eb7c01;         (* arm_MOVK X1 (word 23520) 48 *)
  w 0xa9011406;         (* arm_STP X6 X5 X0 (Immediate_Offset (iword (&16))) *)
  w 0xa9020c04;         (* arm_STP X4 X3 X0 (Immediate_Offset (iword (&32))) *)
  w 0xf9001802;         (* arm_STR X2 X0 (Immediate_Offset (word 48)) *)
  w 0xf9001c01;         (* arm_STR X1 X0 (Immediate_Offset (word 56)) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xa9bd7bfd;         (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &48))) *)
  w 0x910003fd;         (* arm_ADD X29 SP (rvalue (word 0)) *)
  w 0xa90153f3;         (* arm_STP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xf90013f5;         (* arm_STR X21 SP (Immediate_Offset (word 32)) *)
  w 0xaa0003f5;         (* arm_MOV X21 X0 *)
  w 0xaa0103f3;         (* arm_MOV X19 X1 *)
  w 0xaa0203f4;         (* arm_MOV X20 X2 *)
  w 0xd37df283;         (* arm_LSL X3 X20 3 *)
  w 0xd37dfe85;         (* arm_LSR X5 X20 61 *)
  w 0xf94022a0;         (* arm_LDR X0 X21 (Immediate_Offset (word 64)) *)
  w 0xf94026a2;         (* arm_LDR X2 X21 (Immediate_Offset (word 72)) *)
  w 0xab030000;         (* arm_ADDS X0 X0 X3 *)
  w 0x9a050042;         (* arm_ADC X2 X2 X5 *)
  w 0xa9040aa0;         (* arm_STP X0 X2 X21 (Immediate_Offset (iword (&64))) *)
  w 0x394342a4;         (* arm_LDRB W4 X21 (Immediate_Offset (word 208)) *)
  w 0xb40002a4;         (* arm_CBZ X4 (word 84) *)
  w 0xd2801000;         (* arm_MOV X0 (rvalue (word 128)) *)
  w 0xcb040000;         (* arm_SUB X0 X0 X4 *)
  w 0xeb14001f;         (* arm_CMP X0 X20 *)
  w 0x54000049;         (* arm_BLS (word 8) *)
  w 0xaa1403e0;         (* arm_MOV X0 X20 *)
  w 0x910142a1;         (* arm_ADD X1 X21 (rvalue (word 80)) *)
  w 0xaa1f03e2;         (* arm_MOV X2 XZR *)
  w 0x14000005;         (* arm_B (word 20) *)
  w 0x38626a63;         (* arm_LDRB W3 X19 (Register_Offset X2) *)
  w 0x38246823;         (* arm_STRB W3 X1 (Register_Offset X4) *)
  w 0x91000442;         (* arm_ADD X2 X2 (rvalue (word 1)) *)
  w 0x91000484;         (* arm_ADD X4 X4 (rvalue (word 1)) *)
  w 0xeb00005f;         (* arm_CMP X2 X0 *)
  w 0x54ffff61;         (* arm_BNE (word 2097132) *)
  w 0x8b000273;         (* arm_ADD X19 X19 X0 *)
  w 0xcb000294;         (* arm_SUB X20 X20 X0 *)
  w 0xf102009f;         (* arm_CMP X4 (rvalue (word 128)) *)
  w 0x54000281;         (* arm_BNE (word 80) *)
  w 0xaa1503e0;         (* arm_MOV X0 X21 *)
  w 0x97ffff44;         (* arm_BL (word 268434704) *)
  w 0xf102029f;         (* arm_CMP X20 (rvalue (word 128)) *)
  w 0x54000103;         (* arm_BCC (word 32) *)
  w 0xaa1503e0;         (* arm_MOV X0 X21 *)
  w 0xaa1303e1;         (* arm_MOV X1 X19 *)
  w 0xd347fe82;         (* arm_LSR X2 X20 7 *)
  w 0xd379e043;         (* arm_LSL X3 X2 7 *)
  w 0x8b030273;         (* arm_ADD X19 X19 X3 *)
  w 0x92401a94;         (* arm_AND X20 X20 (rvalue (word 127)) *)
  w 0x97ffff98;         (* arm_BL (word 268435040) *)
  w 0xaa1f03e4;         (* arm_MOV X4 XZR *)
  w 0x910142a1;         (* arm_ADD X1 X21 (rvalue (word 80)) *)
  w 0x14000004;         (* arm_B (word 16) *)
  w 0x38646a62;         (* arm_LDRB W2 X19 (Register_Offset X4) *)
  w 0x38246822;         (* arm_STRB W2 X1 (Register_Offset X4) *)
  w 0x91000484;         (* arm_ADD X4 X4 (rvalue (word 1)) *)
  w 0xeb14009f;         (* arm_CMP X4 X20 *)
  w 0x54ffff81;         (* arm_BNE (word 2097136) *)
  w 0x390342a4;         (* arm_STRB W4 X21 (Immediate_Offset (word 208)) *)
  w 0xa94153f3;         (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94013f5;         (* arm_LDR X21 SP (Immediate_Offset (word 32)) *)
  w 0xa8c37bfd;         (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&48))) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xa9bd7bfd;         (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &48))) *)
  w 0x910003fd;         (* arm_ADD X29 SP (rvalue (word 0)) *)
  w 0xa90153f3;         (* arm_STP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xaa0003f4;         (* arm_MOV X20 X0 *)
  w 0xaa0103f3;         (* arm_MOV X19 X1 *)
  w 0xf90013f5;         (* arm_STR X21 SP (Immediate_Offset (word 32)) *)
  w 0x91014275;         (* arm_ADD X21 X19 (rvalue (word 80)) *)
  w 0x39434262;         (* arm_LDRB W2 X19 (Immediate_Offset (word 208)) *)
  w 0x52801003;         (* arm_MOV W3 (rvalue (word 128)) *)
  w 0x38226aa3;         (* arm_STRB W3 X21 (Register_Offset X2) *)
  w 0x91000442;         (* arm_ADD X2 X2 (rvalue (word 1)) *)
  w 0xf101c05f;         (* arm_CMP X2 (rvalue (word 112)) *)
  w 0x54000149;         (* arm_BLS (word 40) *)
  w 0x14000003;         (* arm_B (word 12) *)
  w 0x38226abf;         (* arm_STRB WZR X21 (Register_Offset X2) *)
  w 0x91000442;         (* arm_ADD X2 X2 (rvalue (word 1)) *)
  w 0xf102005f;         (* arm_CMP X2 (rvalue (word 128)) *)
  w 0x54ffffa1;         (* arm_BNE (word 2097140) *)
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0xaa1503e1;         (* arm_MOV X1 X21 *)
  w 0x97ffff19;         (* arm_BL (word 268434532) *)
  w 0xaa1f03e2;         (* arm_MOV X2 XZR *)
  w 0x14000003;         (* arm_B (word 12) *)
  w 0x38226abf;         (* arm_STRB WZR X21 (Register_Offset X2) *)
  w 0x91000442;         (* arm_ADD X2 X2 (rvalue (word 1)) *)
  w 0xf101c05f;         (* arm_CMP X2 (rvalue (word 112)) *)
  w 0x54ffffa1;         (* arm_BNE (word 2097140) *)
  w 0xf9402660;         (* arm_LDR X0 X19 (Immediate_Offset (word 72)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9006260;         (* arm_STR X0 X19 (Immediate_Offset (word 192)) *)
  w 0xf9402260;         (* arm_LDR X0 X19 (Immediate_Offset (word 64)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9006660;         (* arm_STR X0 X19 (Immediate_Offset (word 200)) *)
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0xaa1503e1;         (* arm_MOV X1 X21 *)
  w 0x97ffff0a;         (* arm_BL (word 268434472) *)
  w 0xf9400260;         (* arm_LDR X0 X19 (Immediate_Offset (word 0)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9000280;         (* arm_STR X0 X20 (Immediate_Offset (word 0)) *)
  w 0xf9400660;         (* arm_LDR X0 X19 (Immediate_Offset (word 8)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9000680;         (* arm_STR X0 X20 (Immediate_Offset (word 8)) *)
  w 0xf9400a60;         (* arm_LDR X0 X19 (Immediate_Offset (word 16)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9000a80;         (* arm_STR X0 X20 (Immediate_Offset (word 16)) *)
  w 0xf9400e60;         (* arm_LDR X0 X19 (Immediate_Offset (word 24)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9000e80;         (* arm_STR X0 X20 (Immediate_Offset (word 24)) *)
  w 0xf9401260;         (* arm_LDR X0 X19 (Immediate_Offset (word 32)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9001280;         (* arm_STR X0 X20 (Immediate_Offset (word 32)) *)
  w 0xf9401660;         (* arm_LDR X0 X19 (Immediate_Offset (word 40)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9001680;         (* arm_STR X0 X20 (Immediate_Offset (word 40)) *)
  w 0xf9401a60;         (* arm_LDR X0 X19 (Immediate_Offset (word 48)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9001a80;         (* arm_STR X0 X20 (Immediate_Offset (word 48)) *)
  w 0xf9401e60;         (* arm_LDR X0 X19 (Immediate_Offset (word 56)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9001e80;         (* arm_STR X0 X20 (Immediate_Offset (word 56)) *)
  w 0xa94153f3;         (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94013f5;         (* arm_LDR X21 SP (Immediate_Offset (word 32)) *)
  w 0xa8c37bfd;         (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&48))) *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;


let ED25519_EXEC = ARM_MK_EXEC_RULE ed25519_mc;;

(*****************************************************************************)

(* ------------------------------------------------------------------------- *)
(* ??? Stubs. To be removed.                                                 *)
(* ------------------------------------------------------------------------- *)

(*****************************************************************************)
let edwards25519_encode_mc = define_assert_from_elf "edwards25519_encode_mc" "arm/ed25519/code/stub.o"
[
  0xd65f03c0        (* arm_RET X30 *)
];;
let EDWARDS25519_ENCODE_EXEC = ARM_MK_EXEC_RULE edwards25519_encode_mc;;

let edwards25519_decode_alt_mc = define_assert_from_elf "edwards25519_decode_alt_mc" "arm/ed25519/code/stub.o"
[
  0xd65f03c0        (* arm_RET X30 *)
];;
let EDWARDS25519_DECODE_ALT_EXEC = ARM_MK_EXEC_RULE edwards25519_decode_alt_mc;;

let edwards25519_scalarmulbase_alt_mc = define_assert_from_elf "edwards25519_scalarmulbase_alt_mc" "arm/ed25519/code/stub.o"
[
  0xd65f03c0        (* arm_RET X30 *)
];;
let EDWARDS25519_SCALARMULBASE_ALT_EXEC =
  ARM_MK_EXEC_RULE edwards25519_scalarmulbase_alt_mc;;

let edwards25519_scalarmuldouble_alt_mc = define_assert_from_elf "edwards25519_scalarmuldouble_alt_mc" "arm/ed25519/code/stub.o"
[
  0xd65f03c0        (* arm_RET X30 *)
];;
let EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC =
  ARM_MK_EXEC_RULE edwards25519_scalarmuldouble_alt_mc;;

let bignum_mod_n25519_mc = define_assert_from_elf "bignum_mod_n25519_mc" "arm/ed25519/code/stub.o"
[
  0xd65f03c0        (* arm_RET X30 *)
];;
let BIGNUM_MOD_N25519_EXEC = ARM_MK_EXEC_RULE bignum_mod_n25519_mc;;

let bignum_neg_p25519_mc = define_assert_from_elf "bignum_neg_p25519_mc" "arm/ed25519/code/stub.o"
[
  0xd65f03c0        (* arm_RET X30 *)
];;
let BIGNUM_NEG_P25519_EXEC = ARM_MK_EXEC_RULE bignum_neg_p25519_mc;;

let bignum_madd_n25519_alt_mc = define_assert_from_elf "bignum_madd_n25519_alt_mc" "arm/ed25519/code/stub.o"
[
  0xd65f03c0        (* arm_RET X30 *)
];;
let BIGNUM_MADD_N25519_ALT_EXEC = ARM_MK_EXEC_RULE bignum_madd_n25519_alt_mc;;

let bignum_le_mc = define_assert_from_elf "bignum_le_mc" "arm/ed25519/code/stub.o"
[
  0xd65f03c0        (* arm_RET X30 *)
];;
let BIGNUM_LE_EXEC = ARM_MK_EXEC_RULE bignum_le_mc;;

let EDWARDS25519_ENCODE_SUBROUTINE_CORRECT = time prove
 (`!z p x y pc returnaddress.
      nonoverlapping (word pc,4) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) edwards25519_encode_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; p] s /\
                bignum_pair_from_memory(p,4) s = (x,y))
           (\s. read PC s = returnaddress /\
                (x < p_25519 /\ y < p_25519
                ==> read (memory :> bytelist(z,32)) s =
                    bytelist_of_num 32 (ed25519_encode (&x,&y))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,32)])`,
      CHEAT_TAC);;

let EDWARDS25519_DECODE_ALT_SUBROUTINE_CORRECT = time prove
 (`!z c n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 224),224))
            [word pc,4; z,8 * 8; c,8 * 4] /\
        nonoverlapping (word pc,0x7b0) (z,8 * 8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) edwards25519_decode_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; c] s /\
                  read (memory :> bytes(c,32)) s = n)
             (\s. read PC s = returnaddress /\
                  C_RETURN s = word(bitval(~ed25519_validencode n)) /\
                  (ed25519_validencode n
                   ==> bignum_pair_from_memory(z,4) s =
                       paired (modular_encode (256,p_25519))
                              (ed25519_decode n)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 8);
                    memory :> bytes(word_sub stackpointer (word 224),224)])`,
  CHEAT_TAC);;

let EDWARDS25519_SCALARMULBASE_ALT_SUBROUTINE_CORRECT = time prove
 (`!res scalar n pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 496),496))
        [(word pc,4); (res,64); (scalar,32)] /\
    nonoverlapping (res,64) (word pc,0xe1e0)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) edwards25519_scalarmulbase_alt_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [res; scalar] s /\
              bignum_from_memory (scalar,4) s = n)
         (\s. read PC s = returnaddress /\
              bignum_pair_from_memory(res,4) s =
              paired (modular_encode (256,p_25519))
                     (group_pow edwards25519_group E_25519 n))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(word_sub stackpointer (word 496),496)])`,
  CHEAT_TAC);;

let EDWARDS25519_SCALARMULDOUBLE_ALT_SUBROUTINE_CORRECT = time prove
 (`!res scalar point bscalar n xy m pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 1696),1696))
        [(word pc,4); (res,64); (scalar,32); (point,64); (bscalar,32)] /\
    nonoverlapping (res,64) (word pc,0x59a0)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [res; scalar; point; bscalar] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_pair_from_memory (point,4) s = xy /\
              bignum_from_memory (bscalar,4) s = m)
         (\s. read PC s = returnaddress /\
              !P. P IN group_carrier edwards25519_group /\
                  paired (modular_decode (256,p_25519)) xy = P
                  ==> bignum_pair_from_memory(res,4) s =
                      paired (modular_encode (256,p_25519))
                             (group_mul edwards25519_group
                                 (group_pow edwards25519_group P n)
                                 (group_pow edwards25519_group E_25519 m)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,64);
                    memory :> bytes(word_sub stackpointer (word 1696),1696)])`,
  CHEAT_TAC);;

let BIGNUM_MOD_N25519_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc returnaddress.
      nonoverlapping (word pc,4) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n25519_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s = n MOD n_25519)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  CHEAT_TAC);;

let BIGNUM_NEG_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,4) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_neg_p25519_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = returnaddress /\
                  (n <= p_25519
                   ==> bignum_from_memory (z,4) s = (p_25519 - n) MOD p_25519))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
 CHEAT_TAC);;

let BIGNUM_MADD_N25519_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x m y n c r pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,4); (x,8 * 4); (y,8 * 4); (c,8 * 4); (z,8 * 4)] /\
      nonoverlapping (word pc,4) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_madd_n25519_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x; y; c] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n /\
                bignum_from_memory (c,4) s = r)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s = (m * n + r) MOD n_25519)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,4);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  CHEAT_TAC);;

let BIGNUM_LE_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_le_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. (read PC s' = returnaddress \/
                 read PC s' = returnaddress) /\
                C_RETURN s' = if x <= y then word 1 else word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  CHEAT_TAC);;

(*****************************************************************************)

(* ------------------------------------------------------------------------- *)
(* ??? End of stubs.                                                 *)
(* ------------------------------------------------------------------------- *)

(*****************************************************************************)

(* void ed25519_public_key_from_seed_s2n_bignum(
    uint8_t A[ED25519_PUBLIC_KEY_LEN], const uint8_t seed[ED25519_SEED_LEN]) *)
let ED25519_PUBLIC_KEY_FROM_SEED_S2N_BIGNUM_CORRECT = prove
  (`!sp A_p seed_p seed pc retpc K_base.
    aligned 16 sp /\
    adrp_within_bounds (word K_base) (word (pc + 0x754)) /\
    PAIRWISE nonoverlapping [(word pc, 0xb60); (A_p, 32); (seed_p, 32);
      (word_sub sp (word 1184), 1184); (word K_base, 640)] /\
    LENGTH seed = 32 ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc K_base) /\
           read PC s = word pc /\
           read SP s = sp /\
           read X30 s = word retpc /\
           C_ARGUMENTS [A_p; seed_p] s /\
           byte_list_at seed seed_p s /\
           constants_at (word K_base) s)
      (\s. read PC s = word retpc /\
           byte_list_at (public_key_of_seed seed) A_p s)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(A_p, 32)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 1184), 1184)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
      constants_at; C_ARGUMENTS; C_RETURN] THEN
    WORD_FORALL_OFFSET_TAC 1184 THEN
    REPEAT STRIP_TAC THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
    ENSURES_PRESERVED_TAC "x20_init" `X20` THEN

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC ED25519_EXEC (1--6) THEN
    (* SUBGOAL_THEN `word (pc + 2264) = word ((pc + 1604) + 660):int64` ASSUME_TAC THENL
    [ CHEAT_TAC; ALL_TAC ] THEN
    SUBGOAL_THEN `aligned_bytes_loaded s6 (word (pc + 1604)) (sha512_mc (pc + 1604) K_base)` ASSUME_TAC THENL
    [ CHEAT_TAC; ALL_TAC ] THEN *)
    ARM_SUBROUTINE_SIM_TAC
      (SPEC_ALL ed25519_mc, ED25519_EXEC, 0x644,
        TRIM_LIST_CONV
        (mk_comb (`TRIM_LIST (0x644,0):byte list -> byte list`, rand (concl (SPEC_ALL ed25519_mc)))), SHA512_INIT)
      [`sp + word 840 : int64`; `pc + 0x644`; `pc + 0x18`; `K_base : num`] 7 THEN
    RENAME_TAC `s7:armstate` `s6_ret:armstate` THEN
  );;

let LENGTH_DOM2_PREFIX = prove
  (`LENGTH dom2_prefix = 32`,
  REWRITE_TAC [dom2_prefix; LENGTH; MAP; byte_of_char; ascii_of_char] THEN
    CONV_TAC NUM_REDUCE_CONV);;

(* size_t dom2_common(
    uint8_t dom2_buffer[max_dom2_size], const uint64_t phflag,
    const uint8_t *context, size_t context_len) *)
let DOM2_COMMON_CORRECT = prove
  (`!dom2_buf_p flag ctx_p ctx pc retpc K_base.
    PAIRWISE nonoverlapping [(word pc, 2944); (dom2_buf_p, max_dom2_size); (ctx_p, LENGTH ctx)] /\
    LENGTH ctx <= 255 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc K_base) /\
         read PC s = word (pc + 0x38c) /\
         read X30 s = word retpc /\
         C_ARGUMENTS [dom2_buf_p; flag; ctx_p; word (LENGTH ctx)] s /\
         byte_list_at ctx ctx_p s)
    (\s. read PC s = word retpc /\
         byte_list_at (dom2_prefix ++ [word (val flag)] ++ [word (LENGTH ctx)] ++ ctx) dom2_buf_p s /\
         C_RETURN s = word (LENGTH (dom2_prefix ++ [word (val flag)] ++ [word (LENGTH ctx)] ++ ctx)))
    (MAYCHANGE [PC; X0; X4; X5; X6] ,,
     MAYCHANGE [memory :> bytes(dom2_buf_p, max_dom2_size)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; max_dom2_size; C_ARGUMENTS; C_RETURN] THEN
    REPEAT STRIP_TAC THEN
    ENSURES_WHILE_UP_OR_0_TAC
      `LENGTH (ctx:byte list)` `pc + 0x3f4` `pc + 0x3f4`
      `\i s. // loop invariant
        read X2 s = ctx_p /\ read X3 s = word (LENGTH ctx) /\
        read X4 s = dom2_buf_p + word 34 /\ read X5 s = word i /\ read X30 s = word retpc /\
        byte_list_at (dom2_prefix ++ [word (val (flag:int64))] ++ [word (LENGTH ctx)] ++ take i ctx) dom2_buf_p s /\
        byte_list_at ctx ctx_p s` THEN
    REPEAT CONJ_TAC THENL
    [ (* Subgoal 1: initialization *)
      ENSURES_INIT_TAC "s227" THEN
        RULE_ASSUM_TAC (REWRITE_RULE [byte_list_at]) THEN
        ARM_STEPS_TAC ED25519_EXEC (228--250) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC [byte_list_at] THEN
        REWRITE_TAC [take; SUB_LIST_CLAUSES; APPEND_NIL] THEN
        REWRITE_TAC [LENGTH; LENGTH_APPEND; LENGTH_DOM2_PREFIX] THEN
        REWRITE_TAC [dom2_prefix; MAP; byte_of_char; ascii_of_char] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC [APPEND] THEN
        CONV_TAC (TOP_DEPTH_CONV EL_CONV) THEN
        RULE_ASSUM_TAC (REWRITE_RULE[READ_MEMORY_SPLIT_CONV 3 `read (memory :> bytes64 a) s = m`]) THEN
        RULE_ASSUM_TAC (CONV_RULE WORD_REDUCE_CONV) THEN
        REPEAT (POP_ASSUM MP_TAC) THEN
        REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_ADD_0] THEN
        CONV_TAC (ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [GSYM VAL_EQ] THEN
        REWRITE_TAC [VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8] THEN
        REWRITE_TAC [MOD_MOD_EXP_MIN] THEN ARITH_TAC;
      (* Subgoal 2: loop body *)
      REPEAT STRIP_TAC THEN
        REWRITE_TAC [byte_list_at; LENGTH_APPEND; LENGTH; LENGTH_DOM2_PREFIX] THEN
        REWRITE_TAC [ADD_ASSOC; ARITH] THEN REWRITE_TAC [GSYM ADD_ASSOC] THEN
        SUBGOAL_THEN `LENGTH (take i (ctx:byte list)) = i` (fun th -> REWRITE_TAC [th]) THENL
        [ REWRITE_TAC [take; LENGTH_SUB_LIST] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `LENGTH (take (i+1) (ctx:byte list)) = i + 1` (fun th -> REWRITE_TAC [th]) THENL
        [ REWRITE_TAC [take; LENGTH_SUB_LIST] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ENSURES_INIT_TAC "s253_0" THEN
        ARM_STEPS_TAC ED25519_EXEC (254--255) THEN
        POP_ASSUM MP_TAC THEN
        SUBGOAL_THEN `!x y. x <= 255 /\ y < x ==> ~(val (word_sub (word x) (word y):int64) = 0)`
          (fun th -> ASM_SIMP_TAC [th]) THENL
        [ REPEAT GEN_TAC THEN STRIP_TAC THEN
            REWRITE_TAC [VAL_EQ_0] THEN
            FIRST_ASSUM (fun th ->
              ASSUME_TAC (REWRITE_RULE [MATCH_MP LT_IMP_LE th] (ISPECL [`x:num`; `y:num`] WORD_SUB))) THEN
            POP_ASSUM (fun th -> REWRITE_TAC [GSYM th]) THEN
            REWRITE_TAC [GSYM VAL_EQ_0] THEN
            IMP_REWRITE_TAC [VAL_WORD_EQ] THEN REWRITE_TAC [DIMINDEX_64] THEN
            SIMPLE_ARITH_TAC;
          ALL_TAC ] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `read (memory :> bytes8 (ctx_p + word i)) s255 = EL i ctx` ASSUME_TAC THENL
        [ ASM_SIMP_TAC []; ALL_TAC ] THEN
        ARM_STEPS_TAC ED25519_EXEC (251--253) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC [WORD_ADD] THEN
        REPEAT STRIP_TAC THEN
        ASM_CASES_TAC `i' < 34 + i` THENL
        [ ASM_SIMP_TAC [] THEN
            REWRITE_TAC [take; SUB_LIST_SPLIT] THEN
            REWRITE_TAC [APPEND_ASSOC] THEN
            GEN_REWRITE_TAC RAND_CONV [EL_APPEND] THEN
            REWRITE_TAC [LENGTH_APPEND; LENGTH_DOM2_PREFIX; LENGTH_SUB_LIST; LENGTH] THEN
            COND_CASES_TAC THENL [ REWRITE_TAC []; SIMPLE_ARITH_TAC ];
          SUBGOAL_THEN `i' = 34 + i` (fun th -> REWRITE_TAC [th]) THENL
            [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
            REWRITE_TAC [take; SUB_LIST_SPLIT] THEN
            REWRITE_TAC [APPEND_ASSOC] THEN
            GEN_REWRITE_TAC RAND_CONV [EL_APPEND] THEN
            REWRITE_TAC [LENGTH_APPEND; LENGTH_DOM2_PREFIX; LENGTH_SUB_LIST; LENGTH] THEN
            COND_CASES_TAC THENL [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
            ASM_REWRITE_TAC [] THEN
            SIMP_TAC [WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8; ARITH] THEN
            IMP_REWRITE_TAC [EL_SUB_LIST] THEN
            REWRITE_TAC [MIN; SUB_0; GSYM ADD1; LE_SUC_LT; ADD] THEN
            SUBGOAL_THEN `i <= LENGTH (ctx:byte list)` (fun th -> REWRITE_TAC [th]) THENL
            [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
            ASM_REWRITE_TAC [SUB_REFL; ADD_0; ARITH] ];
      (* Subgoal 3: back edge *)
      REPEAT STRIP_TAC THEN
        ARM_SIM_TAC ED25519_EXEC [];
      (* After the loop *)
      REWRITE_TAC [take; SUB_LIST_LENGTH] THEN
        REWRITE_TAC [byte_list_at; LENGTH_APPEND; LENGTH; LENGTH_DOM2_PREFIX] THEN
        ENSURES_INIT_TAC "s253" THEN
        ARM_STEPS_TAC ED25519_EXEC (254--257) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC [] THEN
        CONV_TAC WORD_RULE ]);;

(* void ed25519_sign_common(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    uint8_t *dom2_buffer, size_t dom2_buffer_len) *)
let ED25519_SIGN_COMMON_CORRECT = prove
  (`!sp sig_p msg_p msg priv_key_p seed A dom2_buf_p alg ctx pc retpc.
    aligned 16 sp /\
    adrp_within_bounds (word K_base) (word (pc + 0x754)) /\
    PAIRWISE nonoverlapping [(word pc, 0xb60); (sig_p, 64); (msg_p; LENGTH (ph alg msg)); (priv_key_p, 64);
      (dom2_buf_p, max_dom2_size); (word_sub sp (word ???), ???)] /\
    LENGTH (ph alg msg) < 2 EXP 64 /\
    LENGTH seed = 32 /\
    A = public_key_of_seed seed /\
    dom2_valid alg ctx ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc K_base) /\
         read PC s = word (pc + 0x74) /\
         read SP s = sp /\
         read X30 s = word retpc /\
         C_ARGUMENTS [sig_p; msg_p; word (LENGTH (ph alg msg)); priv_key_p; dom2_buf_p, word (LENGTH (dom2_of alg ctx))] s /\
         byte_list_at (ph alg msg) msg_p s /\
         byte_list_at (seed ++ A) priv_key_p s /\
         byte_list_at (dom2_of alg ctx) dom2_buf_p s)
    (\s. read PC s = word retpc /\
         byte_list_at (sign alg seed msg) sig_p s)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(sig_p, 64)] ,,
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
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(sig_p, 64)] ,,
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
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(sig_p, 64)] ,,
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
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(sig_p, 64)] ,,
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
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
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
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
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
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(sig_p, 64)] ,,
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
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(sig_p, 64)] ,,
     MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)])`,
  );;
