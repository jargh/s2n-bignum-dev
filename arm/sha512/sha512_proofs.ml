needs "arm/sha512/sha512_spec_proofs.ml";;

(*****************************************************************************)

(* ------------------------------------------------------------------------- *)
(* Starting proofs about the machine code.                                   *)
(* ------------------------------------------------------------------------- *)

(*****************************************************************************)

(*
print_literal_relocs_from_elf "arm/sha512/code/sha512_asm.o";;

save_literal_relocs_from_elf
  "arm/sha512/literal_relocs.txt"
  "arm/sha512/code/sha512_asm.o";;
*)

let sha512_mc,sha512_constants_data = define_assert_relocs_from_elf "sha512_mc"
    "arm/sha512/code/sha512_asm.o"
  (fun w BL ADR ADRP ADD_rri64 -> [
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
  ADRP (mk_var("K",`:num`),0,272,14);
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

let SHA512_EXEC = ARM_MK_EXEC_RULE sha512_mc;;

(* void sha512_init(sha512_ctx *sha) *)
let SHA512_INIT = prove
  (`!ctx_p pc retpc K_base.
    nonoverlapping (word pc : int64, 1308) (ctx_p, 216) ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) (sha512_mc pc K_base) /\
          read PC s = word (pc + 0x294) /\
          read X30 s = word retpc /\
          read X0 s = ctx_p)
      (\s. read PC s = word retpc /\
          sha512_ctx_at [] ctx_p s)
      (MAYCHANGE [X1; X2; X3; X4; X5; X6; X7; PC] ,,
      MAYCHANGE [memory :> bytes(ctx_p, 216)] ,, MAYCHANGE [events])`,
  REWRITE_TAC [NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
    ARM_SIM_TAC SHA512_EXEC (166--205) THEN
    ASM_REWRITE_TAC [sha512_ctx_at; sha512_ctx_from; hash_buffer_at; h_init; h_a; h_b; h_c; h_d; h_e; h_f; h_g; h_h;
                     sha512; sha512'; bytes_to_blocks; num_bytes_per_block; bytes_mod_blocks; drop; byte_list_at;
                     LENGTH; VAL_WORD_0; MULT; DIV_0; SUB_LIST_CLAUSES; ARITH] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[LENGTH; MOD_0] THEN
    CONV_TAC EXPAND_CASES_CONV);;

(* void msg_schedule(uint64_t schedule[80], const uint8_t *in_data) *)
let MSG_SCHEDULE = prove
  (`!sch_p m_p m pc retpc K_base.
    PAIRWISE nonoverlapping
      [(word pc : int64, 1308); (sch_p, 640); (m_p, num_bytes_per_block)] ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) (sha512_mc pc K_base) /\
          read PC s = word pc /\
          read X30 s = word retpc /\
          read X0 s = sch_p /\ 
          read X1 s = m_p /\
          msg_block_at m m_p s)
      (\s. read PC s = word retpc /\
          msg_schedule_at m sch_p s)
      (MAYCHANGE [X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; PC] ,,
      MAYCHANGE [memory :> bytes(sch_p, 640)] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              num_bytes_per_block; msg_schedule_at] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC
    `16` `pc + 0x4` `pc + 0x58`
      `\i s. // loop invariant
        (read X30 s = word retpc /\ read X0 s = sch_p /\
          read X1 s = word_add m_p (word (8 * i)) /\ read X3 s = word i /\ msg_block_at m m_p s) /\
        (!j. j < i ==> read (memory :> bytes64(word_add sch_p (word (8 * j)))) s = msg_schedule m j)` THEN
  REPEAT CONJ_TAC THENL
  [ (* Subgoal 1: upper bound of counter is non-zero *)
    ARITH_TAC;
    (* Subgoal 2: initialization *)
    REWRITE_TAC [msg_block_at] THEN
      CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      ARM_SIM_TAC SHA512_EXEC [1] THEN ASM_REWRITE_TAC [LT];
    (* Subgoal 3: loop body *)
    REPEAT STRIP_TAC THEN REWRITE_TAC [msg_block_at] THEN
      CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      ENSURES_INIT_TAC "s1" THEN ASM_REWRITE_TAC [FORALL_LT_SUC] THEN
      SUBGOAL_THEN
        `!i. i < 16
          ==> !j. j < 8
            ==> read (memory :> bytes8(word_add m_p (word(8 * i + j)))) s1 =
              word_subword (m i:int64) (8 * j,8)`
        (MP_TAC o SPEC `i:num`) THENL
        [ RULE_ASSUM_TAC (REWRITE_RULE[READ_MEMORY_SPLIT_CONV 3 `read (memory :> bytes64 a) s = m`]) THEN
          RULE_ASSUM_TAC (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
          CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
          CONV_TAC EXPAND_CASES_CONV THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      CONV_TAC (LAND_CONV EXPAND_CASES_CONV) THEN
      REWRITE_TAC [ADD_CLAUSES] THEN STRIP_TAC THEN
      REWRITE_TAC [GSYM CONJ_ASSOC] THEN
      VAL_INT64_TAC `i:num` THEN
      ARM_STEPS_TAC SHA512_EXEC (2--22) THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
      ONCE_ASM_REWRITE_TAC[msg_schedule] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST;
    (* Subgoal 4: backedge *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[msg_block_at] THEN
      CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN
      VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC SHA512_EXEC (1--2) THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      ASM_SIMP_TAC[LT_IMP_NE];
    ALL_TAC] THEN
  (* After the first loop *)
  ENSURES_WHILE_AUP_TAC
    `16` `80` `pc + 0x7c` `pc + 0xc4`
    `\k s. // loop invariant
        (read X30 s = word retpc /\ read X2 s = word_add sch_p (word (8 * (k - 15))) /\
        read X11 s = word_add sch_p (word (8 * 65)) /\
        read X0 s = msg_schedule m (k - 1) /\ read X3 s = msg_schedule m (k - 2) /\ read X4 s = msg_schedule m (k - 16) /\
        read X6 s = msg_schedule m (k - 3)/\ read X7 s = msg_schedule m (k - 4) /\ read X8 s = msg_schedule m (k - 5)/\
        read X9 s = msg_schedule m (k - 6) /\ read X10 s = msg_schedule m (k - 7) /\
        (!j. j < k ==> read (memory :> bytes64(word_add sch_p (word (8 * j)))) s = msg_schedule m j))` THEN
  REPEAT CONJ_TAC THENL
  [ (* Subgoal 1: upper bound of counter is non-zero *)
    ARITH_TAC;
    (* Subgoal 2: initialization *)
    ENSURES_INIT_TAC "s22" THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE [WORD_ADD_0]) THEN
      ARM_STEPS_TAC SHA512_EXEC (23--31) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC [] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC [WORD_ADD_0];
    (* Subgoal 3: loop body *)
    REPEAT STRIP_TAC THEN
      ENSURES_INIT_TAC "s31" THEN
      FIRST_ASSUM(fun th -> 
        MAP_EVERY (MP_TAC o C SPEC th) [`i - 2`; `i - 7`; `i - 15`; `i - 16`]) THEN
      REPEAT(ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC]) THEN
      ARM_STEPS_TAC SHA512_EXEC (32--49) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL
      [ ASM_SIMP_TAC[ARITH_RULE `16 <= i ==> (i + 1) - 15 = (i - 15) + 1`] THEN
          CONV_TAC WORD_RULE;
        ALL_TAC ] THEN
      CONJ_TAC THENL
      [ REWRITE_TAC [ADD_SUB] THEN
          GEN_REWRITE_TAC RAND_CONV [msg_schedule] THEN
          ASM_REWRITE_TAC[GSYM NOT_LE] THEN
          REWRITE_TAC [msg_schedule_word; sigma0_DEF; sigma1_DEF] THEN
          CONV_TAC WORD_BLAST;
        ALL_TAC ] THEN
      REPEAT (CONJ_TAC THENL [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC]) THEN
      ASM_REWRITE_TAC [FORALL_LT_SUC] THEN
      SUBGOAL_THEN `8 * i = 8 * (i - 15) + 120` SUBST1_TAC THENL [SIMPLE_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      GEN_REWRITE_TAC RAND_CONV [msg_schedule] THEN
      ASM_REWRITE_TAC[GSYM NOT_LE] THEN
      REWRITE_TAC [msg_schedule_word; sigma0_DEF; sigma1_DEF] THEN
      CONV_TAC WORD_BLAST;
    (* Subgoal 4: backedge *)
    REPEAT STRIP_TAC THEN
      ARM_SIM_TAC SHA512_EXEC (1--2) THEN
      REWRITE_TAC [VAL_EQ] THEN
      REWRITE_TAC[WORD_RULE `word_add x y = word_add x z <=> y = z`] THEN
      REWRITE_TAC [GSYM VAL_EQ] THEN
      VAL_INT64_TAC `8 * (i - 15)` THEN
      ASM_REWRITE_TAC [] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 80 ==> ~(520 = 8 * (i - 15))`];
    ALL_TAC ] THEN
  (* After the second loop *)
  ARM_SIM_TAC SHA512_EXEC (50--52));;

let WORD_ADD1_SHL3_SUB8 = prove
  (`(b + word_shl (word (i + 1)) 3) + word 18446744073709551608:int64 =
    b + word (8 * i)`,
  REWRITE_TAC[WORD_RULE
   `(b + word_shl (word (i + 1)) 3) + x =  b + word(8 * i) + (x + word 8)`] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC WORD_RULE);;

(* void sha512_process_block(uint64_t h[8], const uint8_t *in_data) *)
let SHA512_PROCESS_BLOCK = prove
  (`!sp h_p h m_p m pc retpc K_base.
  aligned 16 sp /\
  adrp_within_bounds (word K_base) (word (pc + 0x110)) /\
  PAIRWISE nonoverlapping
    [(word pc : int64, 1308); (h_p, 64);
     (m_p, num_bytes_per_block); (word_sub sp (word 720), 720);
     (word K_base, 640)] ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (sha512_mc pc K_base) /\
         read PC s = word (pc + 0xd0) /\
         read X30 s = word retpc /\
         read SP s = sp /\
         read X0 s = h_p /\
         read X1 s = m_p /\
         hash_buffer_at h h_p s /\
         msg_block_at m m_p s /\
         constants_at (word K_base) s)
    (\s. read PC s = word retpc /\
         hash_buffer_at (sha512_block m h) h_p s)
    (MAYCHANGE [X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                X12; X13; X14; X15; X16; X17; X18; PC] ,,
     MAYCHANGE [memory :> bytes(h_p, 64)] ,,
     MAYCHANGE [memory :> bytes(word_sub sp (word 720), 720)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; num_bytes_per_block] THEN
  WORD_FORALL_OFFSET_TAC 720 THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_WHILE_UP_TAC
    `79` `pc + 0x148` `pc + 0x148`
    `\i s. // loop invariant
      (read (memory :> bytes64(sp)) s = x29_init /\
      read (memory :> bytes64(sp + word 8)) s = word retpc /\
      read SP s = sp /\ read X12 s = h_p /\
      read X14 s = word K_base /\ read X6 s = word (i + 1) /\
      (read X5 s, read X8 s, read X7 s, read X13 s,
        read X3 s, read X10 s, read X9 s, read X11 s) =
        compression_until i 0 h m /\
      msg_schedule_at m (sp + word 0x50) s /\
      hash_buffer_at h h_p s /\
      constants_at (word K_base) s)` THEN
  REPEAT CONJ_TAC THENL
  [ (* Subgoal 1: upper bound of counter is non-zero *)
    ARITH_TAC;
    (* Subgoal 2: initialization *)
    REWRITE_TAC [msg_block_at; hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
      ENSURES_INIT_TAC "s52" THEN
      RULE_ASSUM_TAC (REWRITE_RULE [constants_at]) THEN
      ARM_STEPS_TAC SHA512_EXEC (53--58) THEN
      ARM_SUBROUTINE_SIM_TAC
        (SPEC_ALL sha512_mc, SHA512_EXEC, 0, SPEC_ALL sha512_mc, REWRITE_RULE [num_bytes_per_block; msg_block_at] MSG_SCHEDULE)
        [`sp + word 80 : int64 `;`m_p : int64`;`m : num -> int64`;
          `pc : num`; `pc + 0xe8 : num`; `K_base : num`] 59 THEN
      RENAME_TAC `s59:armstate` `s58_ret:armstate` THEN
      RULE_ASSUM_TAC (REWRITE_RULE [msg_schedule_at]) THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ARM_STEPS_TAC SHA512_EXEC (59--60) THEN
      FIRST_X_ASSUM MP_TAC THEN COND_CASES_TAC THENL
      [ (* Case: jump *)
        STRIP_TAC THEN
          ARM_STEPS_TAC SHA512_EXEC (135--145) THEN
          ARM_STEPS_TAC SHA512_EXEC (69--71) THEN (* break here for ADRP-ADD *)
          FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[ADRP_ADD_FOLD] THEN DISCH_TAC) THEN
          ARM_STEPS_TAC SHA512_EXEC (72--76) THEN
          ENSURES_FINAL_STATE_TAC THEN
          ONCE_ASM_REWRITE_TAC [compression_until] THEN
          ASM_REWRITE_TAC[LT; msg_schedule_at; constants_at; ARITH];
        (* Case: no jump *)
        STRIP_TAC THEN
          ARM_STEPS_TAC SHA512_EXEC (61--71) THEN
          FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[ADRP_ADD_FOLD] THEN DISCH_TAC) THEN
          ARM_STEPS_TAC SHA512_EXEC (72--75) THEN
          ARM_STEPS_TAC SHA512_EXEC [82] THEN
          ENSURES_FINAL_STATE_TAC THEN
          ONCE_ASM_REWRITE_TAC [compression_until] THEN
          ASM_REWRITE_TAC[LT; msg_schedule_at; constants_at; ARITH] ];
    (* Subgoal 3: loop body *)
    REPEAT STRIP_TAC THEN
      REWRITE_TAC [hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
      ENSURES_INIT_TAC "s82" THEN
      RULE_ASSUM_TAC (REWRITE_RULE [msg_schedule_at; constants_at]) THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ASSUME_TAC(GEN_ALL WORD_ADD1_SHL3_SUB8) THEN
      RULE_ASSUM_TAC (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
      SUBGOAL_THEN
        `read (memory :> bytes64 (word K_base + word (8 * i))) s82 = K_tbl i /\
          read (memory :> bytes64 (sp + word (80 + 8 * i))) s82 = msg_schedule m i`
        STRIP_ASSUME_TAC THENL
      [ RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
          RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
          RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
          CONJ_TAC THEN UNDISCH_TAC `i < 79` THEN SPEC_TAC(`i:num`,`i:num`) THEN
          CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
          CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASSUME_TAC(WORD_RULE `(sp + word 80) + word(8 * i):int64 = sp + word(80 + 8 * i)`) THEN
      ARM_STEPS_TAC SHA512_EXEC (83--113) THEN
      SUBGOAL_THEN `~(val ((word (i + 1) : int64) + word 18446744073709551536) = 0)`
        MP_TAC THENL
      [ REWRITE_TAC[VAL_EQ_0] THEN
          REWRITE_TAC[WORD_RULE `word_add x y = word 0 <=> x = word_neg y`] THEN
          CONV_TAC WORD_REDUCE_CONV THEN
          REWRITE_TAC[GSYM VAL_EQ] THEN
          VAL_INT64_TAC `i + 1` THEN
          ASM_REWRITE_TAC[] THEN
          CONV_TAC WORD_REDUCE_CONV THEN
          ASM_SIMP_TAC[ARITH_RULE `i < 79 ==> ~(i + 1 = 80)`];
        DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) ] THEN
      ARM_STEPS_TAC SHA512_EXEC (77--81) THEN
      ARM_STEPS_TAC SHA512_EXEC [83] THEN
      RENAME_TAC `s83:armstate` `s82':armstate` THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC [LT; msg_schedule_at; constants_at; ARITH; WORD_ADD] THEN
      CONV_TAC (ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC [] THEN
      MP_TAC (SPECL [`0`; `i:num`; `h:hash_t`; `m:num->int64`] COMPRESSION_STEP) THEN
      REWRITE_TAC [LE_0] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
      REWRITE_TAC [compression_update; compression_t1; compression_t2; Sigma0_DEF; Sigma1_DEF; Ch_DEF; Maj_DEF] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC [SHA512_A; SHA512_B; SHA512_C;
        SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H] THEN
      CONV_TAC WORD_BLAST;
    (* Subgoal 4: backedge *)
    REPEAT STRIP_TAC THEN ARM_SIM_TAC SHA512_EXEC [];
    ALL_TAC;
  ] THEN
  (* After the loop *)
  REWRITE_TAC [hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
  ENSURES_INIT_TAC "s82" THEN
  RULE_ASSUM_TAC (REWRITE_RULE [msg_schedule_at; constants_at]) THEN
  RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  SUBGOAL_THEN `read (memory :> bytes64 (word K_base + word 632)) s82 = K_tbl 79 /\
    read (memory :> bytes64 (sp + word 712)) s82 = msg_schedule m 79` STRIP_ASSUME_TAC THENL
  [ REPEAT (FIRST_X_ASSUM (ASSUME_TAC o SPEC `79`)) THEN
      RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
      ASM_SIMP_TAC [ARITH];
    ALL_TAC ] THEN
  ARM_STEPS_TAC SHA512_EXEC (83--113) THEN (* Do not branch *)
  ARM_STEPS_TAC SHA512_EXEC (114--134) THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC [sha512_block; compression] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC [ARITH_RULE `80 = 79 + 1`] THEN
  MP_TAC (SPECL [`0`; `79`; `h:hash_t`; `m:num->int64`] COMPRESSION_STEP) THEN
  REWRITE_TAC [LE_0] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  REWRITE_TAC [add8; compression_update; compression_t1; compression_t2; Sigma0_DEF; Sigma1_DEF; Ch_DEF; Maj_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC [SHA512_A; SHA512_B; SHA512_C;
    SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H; WORD_ADD_SYM] THEN
  CONV_TAC WORD_BLAST);;

(* void sha512_process_blocks(uint64_t h[8], const uint8_t *in_data, size_t num_blocks) *)
let SHA512_PROCESS_BLOCKS = prove
  (`!sp h_p h m_p m l pc retpc K_base.
    aligned 16 sp /\
    adrp_within_bounds (word K_base) (word (pc + 0x110)) /\
    PAIRWISE nonoverlapping
      [(word pc : int64, 1308); (h_p, 64); (m_p, num_bytes_per_block * val l);
      (word_sub sp (word 768), 768); (word K_base, 640)] ==>
      ensures arm
      (\s. aligned_bytes_loaded s (word pc) (sha512_mc pc K_base) /\
          read PC s = word (pc + 0x244) /\
          read X30 s = word retpc /\
          read SP s = sp /\
          aligned 16 sp /\
          read X0 s = h_p /\
          read X1 s = m_p /\
          read X2 s = l /\
          hash_buffer_at h h_p s /\
          msg_blocks_at m (val l) m_p s /\
          constants_at (word K_base) s)
      (\s. read PC s = word retpc /\
          hash_buffer_at (sha512' h m (val l)) h_p s)
      (MAYCHANGE [X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                  X11; X12; X13; X14; X15; X16; X17; X18; PC] ,,
      MAYCHANGE [memory :> bytes(h_p, 64)] ,,
      MAYCHANGE [memory :> bytes(word_sub sp (word 768), 768)] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; num_bytes_per_block] THEN
    WORD_FORALL_OFFSET_TAC 768 THEN
    REPEAT STRIP_TAC THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
    ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
    ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
    REWRITE_TAC [hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
    (* The input data is empty *)
    ASM_CASES_TAC `l : int64 = word 0` THENL
    [ ENSURES_INIT_TAC "s145" THEN
        ARM_STEPS_TAC SHA512_EXEC [146] THEN
        ARM_STEPS_TAC SHA512_EXEC [164] THEN
        ENSURES_FINAL_STATE_TAC THEN
        ONCE_REWRITE_TAC [sha512'] THEN
        ASM_REWRITE_TAC [VAL_WORD_0];
      ALL_TAC ] THEN
    (* The input data is non-empty *)
    ENSURES_WHILE_UP_TAC
      `val (l : int64)` `pc + 0x264` `pc + 0x278`
      `\i s. // loop invariant
        (read (memory :> bytes64(sp + word 720)) s = x29_init /\
        read (memory :> bytes64(sp + word 728)) s = word retpc /\
        read (memory :> bytes64(sp + word 736)) s = x19_init /\
        read (memory :> bytes64(sp + word 744)) s = x20_init /\
        read (memory :> bytes64(sp + word 752)) s = x21_init /\
        read SP s = sp + word 720 /\ read X21 s = h_p /\
        read X19 s = m_p + word (0x80 * i) /\ read X20 s = word_sub l (word (i + 1)) /\
        hash_buffer_at (sha512' h m i) h_p s /\
          msg_blocks_at m (val l) m_p s /\
        constants_at (word K_base) s)` THEN
  REPEAT CONJ_TAC THENL
  [ (* Subgoal 1: upper bound of counter is non-zero *)
    ASM_REWRITE_TAC [VAL_EQ_0];
    (* Subgoal 2: initialization *)
    REWRITE_TAC [msg_blocks_at; constants_at; num_bytes_per_block] THEN
      ENSURES_INIT_TAC "s145" THEN
      RULE_ASSUM_TAC (REWRITE_RULE [msg_block_at]) THEN
      RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ARM_STEPS_TAC SHA512_EXEC [146] THEN
      SUBGOAL_THEN `~(val (l:int64) = 0)` (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THENL
      [ ASM_REWRITE_TAC [VAL_EQ_0]; ALL_TAC ] THEN
      ARM_STEPS_TAC SHA512_EXEC (147--153) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ONCE_REWRITE_TAC [sha512'] THEN
      ASM_REWRITE_TAC [msg_block_at; hash_buffer_at; EXPAND_HASH_THM; WORD_ADD_0; ARITH];
    (* Subgoal 3: loop body *)
    REPEAT STRIP_TAC THEN
      ENSURES_INIT_TAC "s153" THEN
      RULE_ASSUM_TAC (REWRITE_RULE [msg_blocks_at; msg_block_at; num_bytes_per_block;
        hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC]) THEN
      FIRST_X_ASSUM (fun th -> MP_TAC th THEN MP_TAC (SPEC `i:num` th)) THEN
      ASM_REWRITE_TAC [msg_block_at; num_bytes_per_block; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [constants_at]) THEN
      REPEAT DISCH_TAC THEN
      ARM_STEPS_TAC SHA512_EXEC (154--158) THEN
      ARM_SUBROUTINE_SIM_TAC
        (SPEC_ALL sha512_mc, SHA512_EXEC, 0, SPEC_ALL sha512_mc,
          (REWRITE_RULE [num_bytes_per_block; hash_buffer_at; EXPAND_HASH_THM;
                        msg_block_at; constants_at; GSYM CONJ_ASSOC] SHA512_PROCESS_BLOCK))
        [ `sp + word 720 : int64`; `h_p:int64`; `sha512' h m i`;
          `m_p + word (128 * i) : int64`; `m (i : num) : num -> int64`;
          `pc : num`; `pc + 0x278`; `K_base : num`] 159 THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC [msg_blocks_at; msg_block_at; num_bytes_per_block;
        GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
        constants_at; hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [ CONV_TAC WORD_RULE; ALL_TAC ]) THEN
      REPEAT CONJ_TAC THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [sha512'] THEN
      REWRITE_TAC [ARITH_RULE `~(i + 1 = 0) /\ (i + 1) - 1 = i`];
    (* Subgoal 4: backedge *)
    REPEAT STRIP_TAC THEN
      REWRITE_TAC [msg_blocks_at; msg_block_at; constants_at; hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
      ENSURES_INIT_TAC "s165" THEN
      ARM_STEPS_TAC SHA512_EXEC (159--160) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [VAL_EQ_0] THEN
      REWRITE_TAC [WORD_RULE `(word_sub l (word(i + 1))) + word 1 = word 0 <=> word i = l`] THEN
      ASM_SIMP_TAC [MESON[VAL_BOUND; VAL_WORD_GALOIS; LT_TRANS; LT_REFL] `i < val(l:int64) ==> ~(word i = l)`];
    ALL_TAC ] THEN
  (* After the loop *)
  REWRITE_TAC [msg_blocks_at; constants_at; hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s158" THEN
    ARM_STEPS_TAC SHA512_EXEC (159--160) THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [WORD_RULE `word_sub l (word (val l + 1)) + word 1 : int64 = word 0`] THEN
    REWRITE_TAC [VAL_EQ_0] THEN DISCH_TAC THEN
    ARM_STEPS_TAC SHA512_EXEC (161--164) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC []);;

let MSG_LEN_LO_EQ = prove
  (`!m0 m:byte list.
    word ((LENGTH m0 * 8) MOD 2 EXP 64) + word_shl (word (LENGTH m)) 3 =
      word ((LENGTH (m0 ++ m) * 8) MOD 2 EXP 64):int64`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [LENGTH_APPEND; word_shl; GSYM DIMINDEX_64; WORD_ADD; WORD_MOD_SIZE] THEN
    REWRITE_TAC [VAL_WORD] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [GSYM WORD_MOD_SIZE] THEN
    REWRITE_TAC [MOD_MULT_LMOD] THEN
    REWRITE_TAC [WORD_MOD_SIZE] THEN
    CONV_TAC WORD_RULE);;

let MSG_LEN_HI_EQ = prove
  (`!m0 m:byte list.
    LENGTH m < 2 EXP 64 ==>
    (word ((LENGTH m0 * 8) DIV 2 EXP 64) + word_ushr (word (LENGTH m)) 61) +
      word (bitval (2 EXP 64 <=
        val (word ((LENGTH m0 * 8) MOD 2 EXP 64):int64) +
          val (word_shl (word (LENGTH m):int64) 3))) =
        word ((LENGTH (m0 ++ m) * 8) DIV 2 EXP 64):int64`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [LENGTH_APPEND; word_ushr; word_shl; DIMINDEX_64;
      GSYM WORD_ADD_ASSOC; WORD_MOD_SIZE; VAL_WORD; MOD_MOD_REFL;
      MOD_MULT_LMOD; RIGHT_ADD_DISTRIB] THEN
    POP_ASSUM (fun th -> REWRITE_TAC [MATCH_MP MOD_LT th]) THEN
    MP_TAC (SPECL [`LENGTH (m0:byte list) * 8`; `2 EXP 64`] DIVISION) THEN
    ANTS_TAC THENL [ ARITH_TAC; ALL_TAC ] THEN
    DISCH_THEN (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    MP_TAC (SPECL [`LENGTH (m:byte list) * 8`; `2 EXP 64`] DIVISION) THEN
    ANTS_TAC THENL [ ARITH_TAC; ALL_TAC ] THEN
    DISCH_THEN (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    ONCE_REWRITE_TAC [ARITH_RULE `!a b c d:num. (a+b)+(c+d) = (a+c)+(b+d)`] THEN
    REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB] THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [MULT_SYM] THEN
    SUBGOAL_THEN `~(2 EXP 64 = 0) /\
      (2 EXP 64 * ((LENGTH (m0:byte list) * 8) DIV 2 EXP 64 + (LENGTH (m:byte list) * 8) DIV 2 EXP 64))
        MOD 2 EXP 64 = 0`
      (fun th -> REWRITE_TAC [MATCH_MP MOD_0_ADD_DIV th]) THENL
    [ REWRITE_TAC [MOD_MULT] THEN ARITH_TAC;
      ALL_TAC ] THEN
    REWRITE_TAC [MATCH_MP DIV_MULT (ARITH_RULE `~(2 EXP 64 = 0)`)] THEN
    REWRITE_TAC [ARITH_RULE `2 EXP 3 = 8`;
      ARITH_RULE `!x. x DIV 2 EXP 61 = (x * 8) DIV 2 EXP 64`;
      MULT_SYM] THEN
    ASSUME_TAC (ARITH_RULE `(LENGTH (m0:byte list) * 8) MOD 2 EXP 64 +
      (LENGTH (m:byte list) * 8) MOD 2 EXP 64 < 2 * 2 EXP 64`) THEN
    ASM_SIMP_TAC [BITVAL_LE_DIV; WORD_ADD; WORD_ADD_ASSOC] );;

let SHL_7_MULT_128 = prove
  (`!x. word_shl (word x) 7 =
    word (x * 128) : N word`,
  CONV_TAC WORD_RULE);;

let AND_127_MOD_128 = prove
  (`!x. word_and (word x) (word 127) = word (x MOD 128) : int64`,
  STRIP_TAC THEN
    REWRITE_TAC [ARITH_RULE `127 = 2 EXP 7 - 1`; WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[VAL_WORD; MOD_MOD_EXP_MIN; DIMINDEX_64] THEN
    ARITH_TAC);;

let NEW_INPUT_FILLS_CUR_BLOCK_ONCE_ARITH = prove
  (`!x y. 128 - x MOD 128 <= y ==>
    y - (128 - x MOD 128) < 128 ==>
    128 - x MOD 128 = (x + y) DIV 128 * 128 - x /\
    y - (128 - x MOD 128) = (x + y) MOD 128`,
  REPEAT STRIP_TAC THENL
  [ SUBGOAL_THEN `128 <= y + x MOD 128 /\ y + x MOD 128 < 256` STRIP_ASSUME_TAC THENL
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      SUBGOAL_THEN `x = x DIV 128 * 128 + x MOD 128` ASSUME_TAC THENL
      [ SIMP_TAC [DIVISION; ARITH]; ALL_TAC ] THEN
      SUBGOAL_THEN `(x + y) DIV 128 = x DIV 128 + 1` ASSUME_TAC THENL
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      SIMPLE_ARITH_TAC;
    SUBGOAL_THEN `(y + x MOD 128) MOD 128 + 128 = y + x MOD 128` MP_TAC THENL
      [ REWRITE_TAC[ARITH_RULE `y MOD 128 + 128 = y <=> y DIV 128 = 1`] THEN
          ASM_ARITH_TAC;
        CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_SYM] THEN
          ASM_ARITH_TAC ] ]);;

let INT64_USHR_7 = prove
  (`!x. x < 2 EXP 64 ==>
    word_ushr (word x) 7 =
    word (x DIV 128) : int64`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [word_ushr; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC [MOD_LT] THEN
    ARITH_TAC);;

let NEW_INPUT_FILLS_CUR_BLOCK_ARITH1 = prove
  (`!x y. y < 2 EXP 64 /\ 128 - x MOD 128 <= y ==>
    word (128 - x MOD 128) +
    word_shl (word ((y - (128 - x MOD 128)) DIV 128)) 7 =
    word ((x + y) DIV 128 * 128 - x) : int64`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_RULE `word_shl (word n) 7 = word(128 * n)`] THEN
    REWRITE_TAC [GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN
    ASSUME_TAC (SPEC `x:num` ADD_128_SUB_MOD_0) THEN
    SUBGOAL_THEN `y = 128 - x MOD 128 + (y - (128 - x MOD 128))`
      (fun th -> ONCE_REWRITE_TAC [th]) THENL
    [ ASM_ARITH_TAC; ALL_TAC ] THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_0_ADD_DIV o
      lhand o lhand o rand o snd) THEN
    ANTS_TAC THENL
    [ ASM_REWRITE_TAC [ARITH]; ALL_TAC ] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE [GSYM DIVIDES_MOD; DIVIDES_DIV_MULT]) THEN
    ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [ARITH_RULE `!x y. x <= y ==> x + y - x = y`] THEN
    ARITH_TAC);;

let NEW_INPUT_FILLS_CUR_BLOCK_ARITH2 = prove
  (`!x y. y < 2 EXP 64 /\ 128 - x MOD 128 <= y ==>
    word_and (word (y - (128 - x MOD 128))) (word 127) =
    word ((x + y) MOD 128) : int64`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [AND_127_MOD_128] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `y = 128 - x MOD 128 + (y - (128 - x MOD 128))`
      (fun th -> ONCE_REWRITE_TAC [th]) THENL
    [ ASM_ARITH_TAC; ALL_TAC ] THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM MOD_ADD_MOD] THEN
    REWRITE_TAC [ADD_128_SUB_MOD_0; ADD] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    SUBGOAL_THEN `y = 128 - x MOD 128 + (y - (128 - x MOD 128))`
      (fun th -> ONCE_REWRITE_TAC [th]) THEN
    ASM_SIMP_TAC [ARITH_RULE `!x y. x <= y ==> x + y - x = y`] THEN
    ARITH_TAC);;

  let NEW_INPUT_FILLS_CUR_BLOCK_AUX = prove
    (`!x y. 128 - x MOD 128 <= y
            ==> x <= (x + y) DIV 128 * 128`,
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[ARITH_RULE `x <= y DIV 128 * 128 <=> x + y MOD 128 <= y`] THEN
      SUBST1_TAC(MESON[MOD_ADD_MOD; MOD_MOD_REFL]
      `(x + y) MOD 128 = (x MOD 128 + y) MOD 128`) THEN
      ASM_CASES_TAC `(x MOD 128 + y) DIV 128 = 0` THEN ASM_ARITH_TAC);;

(* void sha512_update(sha512_ctx *sha, const void *in_data, size_t in_len) *)
let SHA512_UPDATE = prove
  (`!sp ctx_p m0 m_p m pc retpc K_base.
    aligned 16 sp /\
    adrp_within_bounds (word K_base) (word (pc + 0x110)) /\
    PAIRWISE nonoverlapping
      [(word pc : int64, 1308); (ctx_p, 216); (m_p, LENGTH m);
       (word_sub sp (word 816), 816); (word K_base, 640)] /\
    LENGTH m < 2 EXP 64 /\
    LENGTH m0 + LENGTH m < 2 EXP 125 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (sha512_mc pc K_base) /\
         read PC s = word (pc + 0x334) /\
         read X30 s = word retpc /\
         read SP s = sp /\
         read X0 s = ctx_p /\
         read X1 s = m_p /\
         read X2 s = word (LENGTH m) /\
         sha512_ctx_at m0 ctx_p s /\
         byte_list_at m m_p s /\
         constants_at (word K_base) s)
    (\s. read PC s = word retpc /\
         sha512_ctx_at (m0 ++ m) ctx_p s)
    (MAYCHANGE [X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                  X11; X12; X13; X14; X15; X16; X17; X18; PC] ,,
                  MAYCHANGE [memory :> bytes(ctx_p, 216)] ,,
     MAYCHANGE [memory :> bytes(word_sub sp (word 816), 816)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL] THEN
    WORD_FORALL_OFFSET_TAC 816 THEN
    REPEAT STRIP_TAC THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
    ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
    ENSURES_PRESERVED_TAC "x21_init" `X21` THEN

    VAL_INT64_TAC `LENGTH (m:byte list)` THEN
    ASM_CASES_TAC `LENGTH (bytes_mod_blocks m0) = 0` THENL
    [ (* cur_pos is zero *)
      SUBGOAL_THEN `LENGTH (m0:byte list) MOD 128 = 0` ASSUME_TAC THENL
        [ RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD]) THEN
            ASM_REWRITE_TAC [];
          ALL_TAC] THEN
        ENSURES_WHILE_UP_OR_0_TAC
        `LENGTH (bytes_mod_blocks m)` `pc + 0x400` `pc + 0x400`
        `\i s. // loop invariant
          read SP s = sp + word 768 /\ read X1 s = ctx_p + word 80 /\
          read X4 s = word i /\ read X19 s = m_p + word (LENGTH m DIV 128 * 128) /\
          read X20 s = word (LENGTH (bytes_mod_blocks m)) /\ read X21 s = ctx_p /\
          read (memory :> bytes64 (sp + word 784)) s = x19_init /\
          read (memory :> bytes64 (sp + word 792)) s = x20_init /\
          read (memory :> bytes64 (sp + word 800)) s = x21_init /\
          read (memory :> bytes64 (sp + word 768)) s = x29_init /\
          read (memory :> bytes64 (sp + word 776)) s = word retpc /\
          byte_list_at (take i (bytes_mod_blocks m)) (word_add ctx_p (word 80)) s /\
          byte_list_at m m_p s /\
          hash_buffer_at (sha512 (bytes_to_blocks (m0 ++ m)) (LENGTH (m0 ++ m) DIV 128)) ctx_p s /\
          read (memory :> bytes64 (ctx_p + word 64)) s = word ((LENGTH (m0 ++ m) * 8) MOD 2 EXP 64) /\
          read (memory :> bytes64 (ctx_p + word 72)) s = word ((LENGTH (m0 ++ m) * 8) DIV 2 EXP 64)` THEN
        REPEAT CONJ_TAC THENL
        [ (* Subgoal 1: initialization *)
          ENSURES_INIT_TAC "s205" THEN
            ASSUM_EXPAND_SHA512_SPECS_TAC THEN
            ARM_STEPS_TAC SHA512_EXEC (206--221) THEN
            ARM_STEPS_TAC SHA512_EXEC (242--243) THEN
            POP_ASSUM MP_TAC THEN
            COND_CASES_TAC THENL
            [ (* No new block to be processed *)
              SUBGOAL_THEN `LENGTH (m:byte list) DIV 128 = 0` ASSUME_TAC THENL
                [ ASM_SIMP_TAC [DIV_LT]; ALL_TAC ] THEN
                SUBGOAL_THEN `LENGTH (m0 ++ m:byte list) DIV 128 = LENGTH m0 DIV 128` ASSUME_TAC THENL
                [ REWRITE_TAC [LENGTH_APPEND] THEN
                    IMP_REWRITE_TAC [MOD_0_ADD_DIV] THEN
                    SIMPLE_ARITH_TAC;
                  ALL_TAC ] THEN
                STRIP_TAC THEN
                ARM_STEPS_TAC SHA512_EXEC (251--253) THEN
                ENSURES_FINAL_STATE_TAC THEN
                ASM_REWRITE_TAC [take; SUB_LIST_CLAUSES; byte_list_at; LENGTH;
                  bytes_mod_blocks; num_bytes_per_block; MULT; WORD_ADD_0; DROP_0] THEN
                CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
                ASM_SIMP_TAC [MSG_LEN_LO_EQ; MSG_LEN_HI_EQ] THEN
                SIMP_TAC [SPECL [`bytes_to_blocks (m0 ++ m)`;
                 `bytes_to_blocks m0`] BLOCKS_EQ_SHA512_EQ; BLOCKS_APPEND_EQ_LAND] THEN
                EXPAND_SHA512_SPECS_TAC THEN
                ASM_REWRITE_TAC [];
              (* Some new block to be processed *)
              STRIP_TAC THEN
                ARM_STEPS_TAC SHA512_EXEC (244--250) THEN
                RULE_ASSUM_TAC (REWRITE_RULE [WORD_BLAST `!l:int64. word_ushr l 7 = word (val l DIV 128)`]) THEN
                VAL_INT64_TAC `LENGTH (m:byte list)` THEN
                POP_ASSUM (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
                SUBGOAL_THEN `hash_buffer_at (sha512 (bytes_to_blocks m0) (LENGTH m0 DIV 128)) ctx_p s250 /\
                    msg_blocks_at (bytes_to_blocks m) (LENGTH (m:byte list) DIV 128) m_p s250 /\
                    constants_at (word K_base) s250` ASSUME_TAC THENL
                  [ EXPAND_SHA512_SPECS_TAC THEN
                      ASM_REWRITE_TAC [] THEN
                      MATCH_MP_TAC BYTE_LIST_AT_MSG_BLOCKS_AT THEN
                      ASM_REWRITE_TAC [byte_list_at];
                    ALL_TAC] THEN
                VAL_INT64_TAC `LENGTH (m:byte list) DIV 128` THEN
                VAL_INT64_TAC `LENGTH (m:byte list) DIV 128` THEN
                SUBGOAL_THEN `aligned 16 ((sp:int64) + word 768)` ASSUME_TAC THENL
                [ ALIGNED_16_TAC; ALL_TAC ] THEN
                ARM_SUBROUTINE_SIM_TAC
                  (SPEC_ALL sha512_mc, SHA512_EXEC, 0, SPEC_ALL sha512_mc,
                    REWRITE_RULE [num_bytes_per_block] SHA512_PROCESS_BLOCKS)
                  [ `sp + word 768 : int64`; `ctx_p:int64`; `sha512 (bytes_to_blocks m0) (LENGTH m0 DIV 128)`;
                    `m_p : int64`; `bytes_to_blocks m`; `word (LENGTH (m:byte list) DIV 128) : int64`;
                    `pc : num`; `pc + 0x3e8`; `K_base : num`] 251 THEN
                RENAME_TAC `s251:armstate` `s250_ret:armstate` THEN
                MP_TAC (REWRITE_RULE [GSYM sha512] (SPECL [`h_init:hash_t`; `m0:byte list`; `m:byte list`] SHA512'_BLOCKS_STEP)) THEN
                ASM_REWRITE_TAC [] THEN
                DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
                ASSUM_EXPAND_SHA512_SPECS_TAC THEN
                ARM_STEPS_TAC SHA512_EXEC (251--253) THEN
                ENSURES_FINAL_STATE_TAC THEN
                ASM_REWRITE_TAC [take; SUB_LIST_CLAUSES; byte_list_at; LENGTH;
                  SHL_7_MULT_128; AND_127_MOD_128; LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD] THEN
                ASM_SIMP_TAC [MSG_LEN_LO_EQ; MSG_LEN_HI_EQ] THEN
                CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
                EXPAND_SHA512_SPECS_TAC THEN
                ASM_REWRITE_TAC [] ];
          (* Subgoal 2: loop body *)
          REPEAT STRIP_TAC THEN
            ENSURES_INIT_TAC "s256_0" THEN
            ASSUM_EXPAND_SHA512_SPECS_TAC THEN
            SUBGOAL_THEN
              `read (memory :> bytes8 (m_p + word (LENGTH m DIV 128 * 128 + i))) s256_0 = EL i (bytes_mod_blocks m)`
              ASSUME_TAC THENL
            [ REWRITE_TAC [bytes_mod_blocks; num_bytes_per_block; drop] THEN
                IMP_REWRITE_TAC [EL_SUB_LIST] THEN
                SIMP_TAC [ARITH_RULE `!x y. x <= y ==> x + y - x <= y`; DIV_MULT_LE; ARITH] THEN
                REWRITE_TAC [ARITH_RULE `LENGTH m - LENGTH m DIV 128 * 128 = LENGTH (m:byte list) MOD 128`;
                  ARITH_RULE `LENGTH m DIV 128 * 128 + i < LENGTH m <=> i < LENGTH (m:byte list) MOD 128`] THEN
                ASM_REWRITE_TAC [GSYM LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD];
              ALL_TAC ] THEN
            ARM_STEPS_TAC SHA512_EXEC (257--258) THEN
            POP_ASSUM MP_TAC THEN
            ASSUME_TAC (REWRITE_RULE [num_bytes_per_block]
              (SPEC `m : byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
            VAL_INT64_TAC `i:num` THEN
            VAL_INT64_TAC `LENGTH (bytes_mod_blocks m)` THEN
            ASM_REWRITE_TAC [VAL_WORD_SUB_EQ_0] THEN STRIP_TAC THEN
            SUBGOAL_THEN `LENGTH (take i (bytes_mod_blocks m)) = i` ASSUME_TAC THENL
            [ REWRITE_TAC [take; LENGTH_SUB_LIST] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
            POP_ASSUM (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
            ARM_STEPS_TAC SHA512_EXEC (254--256) THEN
            ENSURES_FINAL_STATE_TAC THEN
            EXPAND_SHA512_SPECS_TAC THEN
            ASM_REWRITE_TAC [WORD_ADD; take; LENGTH_SUB_LIST;
              MIN; SUB_0; GSYM ADD1; LE_SUC_LT] THEN
            GEN_TAC THEN DISCH_TAC THEN
            ASM_CASES_TAC `i' < i` THENL
            [ IMP_REWRITE_TAC [take; EL_SUB_LIST; ADD; LT] THEN
                SIMPLE_ARITH_TAC;
              SUBGOAL_THEN `i' = i : num`
                (fun th -> ASM_REWRITE_TAC [th; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THENL
              [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
              IMP_REWRITE_TAC [word_zx; VAL_WORD_EQ; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
              REWRITE_TAC [WORD_VAL] THEN
              IMP_REWRITE_TAC [take; EL_SUB_LIST; ADD; LT] THEN
              REWRITE_TAC [GSYM CONJ_ASSOC] THEN
              CONJ_TAC THENL
              [ SIMPLE_ARITH_TAC; CONV_TAC WORD_BLAST ] ];
          (* Subgoal 3: back edge *)
          REPEAT STRIP_TAC THEN
            ARM_SIM_TAC SHA512_EXEC [];
          ALL_TAC ] THEN
        (* After the only loop *)
        ASSUME_TAC (REWRITE_RULE [num_bytes_per_block]
          (SPEC `m : byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
        EXPAND_SHA512_SPECS_TAC THEN
        REWRITE_TAC [take; SUB_LIST_LENGTH] THEN
        ENSURES_INIT_TAC "s256" THEN
        ARM_STEPS_TAC SHA512_EXEC (257--263) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC [] THEN
        IMP_REWRITE_TAC [word_zx; VAL_WORD_EQ; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
        REWRITE_TAC [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD; LENGTH_APPEND] THEN
        ONCE_REWRITE_TAC [GSYM MOD_ADD_MOD] THEN
        ASM_REWRITE_TAC [ADD; MOD_MOD_REFL] THEN
        CONJ_TAC THENL
        [ ASM_SIMP_TAC [MOD_0_BYTES_MOD_BLOCKS_APPEND];
          ARITH_TAC ];
      (* cur_pos is non-zero *)
      ASSUME_TAC (REWRITE_RULE [num_bytes_per_block]
        (SPEC `m0 : byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
        VAL_INT64_TAC `LENGTH (bytes_mod_blocks m0)` THEN
        SUBGOAL_THEN `word_sub (word 128) (word (LENGTH (bytes_mod_blocks m0))) =
            word (128 - LENGTH (bytes_mod_blocks m0)):int64` ASSUME_TAC THENL
          [ REWRITE_TAC [WORD_SUB] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
        ENSURES_WHILE_UP_OR_0_TAC
          `MIN (128 - LENGTH (bytes_mod_blocks m0)) (LENGTH (m:byte list))` `pc + 0x3a4` `pc + 0x3a4`
          `\i s. // loop invariant
            read SP s = sp + word 768 /\
            read X0 s = word (MIN (128 - LENGTH (bytes_mod_blocks m0)) (LENGTH m)) /\ 
            read X1 s = ctx_p + word 80 /\ read X2 s = word i /\
            read X4 s = word (LENGTH (bytes_mod_blocks m0) + i) /\ read X19 s = m_p /\
            read X20 s = word (LENGTH m) /\ read X21 s = ctx_p /\
            read (memory :> bytes64 (sp + word 784)) s = x19_init /\
            read (memory :> bytes64 (sp + word 792)) s = x20_init /\
            read (memory :> bytes64 (sp + word 800)) s = x21_init /\
            read (memory :> bytes64 (sp + word 768)) s = x29_init /\
            read (memory :> bytes64 (sp + word 776)) s = word retpc /\
            byte_list_at (bytes_mod_blocks m0 ++ take i m) (word_add ctx_p (word 80)) s /\
            byte_list_at m m_p s /\
            hash_buffer_at (sha512 (bytes_to_blocks m0) (LENGTH m0 DIV 128)) ctx_p s /\
            read (memory :> bytes64 (ctx_p + word 64)) s = word ((LENGTH (m0 ++ m) * 8) MOD 2 EXP 64) /\
            read (memory :> bytes64 (ctx_p + word 72)) s = word ((LENGTH (m0 ++ m) * 8) DIV 2 EXP 64) /\
            constants_at (word K_base) s` THEN
        REPEAT CONJ_TAC THENL
        [ (* Subgoal 1: initialization *)
          ENSURES_INIT_TAC "s205" THEN
            ASSUM_EXPAND_SHA512_SPECS_TAC THEN
            ARM_STEPS_TAC SHA512_EXEC (206--220) THEN
            REPLICATE_TAC 2 (POP_ASSUM MP_TAC) THEN
            IMP_REWRITE_TAC [word_zx; VAL_WORD_EQ; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
            REPEAT (ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]) THEN
            REPEAT STRIP_TAC THEN
            ARM_STEPS_TAC SHA512_EXEC (221--225) THEN
            POP_ASSUM MP_TAC THEN
            SUBGOAL_THEN `!x. LENGTH (m:byte list) <= x <=>
              val (word (LENGTH m):int64) <= x` (fun th -> REWRITE_TAC [th; BLS_LS]) THENL
            [ ASM_REWRITE_TAC []; ALL_TAC ] THEN
            VAL_INT64_TAC `128 - LENGTH (bytes_mod_blocks m0)` THEN
            ASM_REWRITE_TAC [] THEN
            COND_CASES_TAC THEN STRIP_TAC THENL
            [ ARM_STEPS_TAC SHA512_EXEC (227--229) ; ARM_STEPS_TAC SHA512_EXEC (226--229) ] THEN
            ENSURES_FINAL_STATE_TAC THEN
            EXPAND_SHA512_SPECS_TAC THEN
            ASM_REWRITE_TAC [MIN; ADD_0; take; SUB_LIST_CLAUSES; APPEND_NIL] THEN
            ASM_SIMP_TAC [MSG_LEN_LO_EQ; MSG_LEN_HI_EQ];
          (* Subgoal 2: loop body *)
          REPEAT STRIP_TAC THEN
            ENSURES_INIT_TAC "s233_0" THEN
            ASSUM_EXPAND_SHA512_SPECS_TAC THEN
            SUBGOAL_THEN `LENGTH (bytes_mod_blocks m0 ++ take i m) = LENGTH (bytes_mod_blocks m0) + i` ASSUME_TAC THENL
            [ REWRITE_TAC [LENGTH_APPEND; take; LENGTH_SUB_LIST] THEN
                SIMPLE_ARITH_TAC;
              ALL_TAC ] THEN
            SUBGOAL_THEN `read (memory :> bytes8 (m_p + word i)) s233_0 = EL i m` ASSUME_TAC THENL
            [ FIRST_X_ASSUM (K ALL_TAC o SPEC `i:num`) THEN
                FIRST_X_ASSUM (MP_TAC o SPEC `i:num`) THEN
                DISCH_THEN (fun th -> IMP_REWRITE_TAC [th]) THEN
                SIMPLE_ARITH_TAC;
              ALL_TAC ] THEN
            ARM_STEPS_TAC SHA512_EXEC (234--235) THEN
            POP_ASSUM MP_TAC THEN
            VAL_INT64_TAC `i:num` THEN
            VAL_INT64_TAC `MIN (128 - LENGTH (bytes_mod_blocks m0)) (LENGTH (m:byte list))` THEN
            ASM_REWRITE_TAC [VAL_WORD_SUB_EQ_0] THEN
            STRIP_TAC THEN
            ARM_STEPS_TAC SHA512_EXEC (230--233) THEN
            ENSURES_FINAL_STATE_TAC THEN
            EXPAND_SHA512_SPECS_TAC THEN
            ASM_REWRITE_TAC [WORD_ADD_ASSOC; WORD_ADD] THEN
            SUBGOAL_THEN `LENGTH (bytes_mod_blocks m0 ++ take (i + 1) m) =
              SUC (LENGTH (bytes_mod_blocks m0 ++ take i m))` (fun th -> REWRITE_TAC [th]) THENL
            [ REWRITE_TAC [take; SUB_LIST_SPLIT; LENGTH_APPEND; LENGTH_SUB_LIST] THEN
                SIMPLE_ARITH_TAC;
              ALL_TAC] THEN
            REPEAT STRIP_TAC THEN
            ASM_CASES_TAC `i' < LENGTH (bytes_mod_blocks m0 ++ take i m)` THENL
            [ ASM_SIMP_TAC [] THEN
                REWRITE_TAC [take; SUB_LIST_SPLIT; APPEND_ASSOC] THEN
                GEN_REWRITE_TAC RAND_CONV [EL_APPEND] THEN
                REWRITE_TAC [GSYM take] THEN
                ASM_REWRITE_TAC [];
              SUBGOAL_THEN `i' = LENGTH (bytes_mod_blocks m0 ++ take i m)` MP_TAC THENL
                [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                ASM_REWRITE_TAC [] THEN
                DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
                ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
                IMP_REWRITE_TAC [word_zx; VAL_WORD_EQ; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
                REWRITE_TAC [WORD_VAL; EL_APPEND] THEN
                REWRITE_TAC [ARITH_RULE `!x y. ~(x+y < x) /\ (x + y) - x = y`] THEN
                IMP_REWRITE_TAC [take; EL_SUB_LIST] THEN
                REWRITE_TAC [ADD] THEN
                REPLICATE_TAC 2 (CONJ_TAC THENL [ ALL_TAC; CONV_TAC WORD_BLAST ]) THEN
                SIMPLE_ARITH_TAC ];
          (* Subgoal 3: backedge *)
          REPEAT STRIP_TAC THEN
            ARM_SIM_TAC SHA512_EXEC [];
          ALL_TAC ] THEN
        (* After the first loop *)
        ASM_CASES_TAC `128 - LENGTH (bytes_mod_blocks m0) <= LENGTH (m:byte list)` THEN
        ASM_REWRITE_TAC [MIN] THENL
        [ (* Need to process the filled block buffer *)
          ENSURES_WHILE_UP_OR_0_TAC
            `LENGTH (bytes_mod_blocks (m0 ++ m))` `pc + 0x400` `pc + 0x400`
            `\i s. // loop invariant
              read SP s = sp + word 768 /\ read X1 s = ctx_p + word 80 /\
              read X4 s = word i /\ read X19 s = m_p + word (LENGTH (m0 ++ m) DIV 128 * 128 - LENGTH m0) /\
              read X20 s = word (LENGTH (bytes_mod_blocks (m0 ++ m))) /\ read X21 s = ctx_p /\
              read (memory :> bytes64 (sp + word 784)) s = x19_init /\
              read (memory :> bytes64 (sp + word 792)) s = x20_init /\
              read (memory :> bytes64 (sp + word 800)) s = x21_init /\
              read (memory :> bytes64 (sp + word 768)) s = x29_init /\
              read (memory :> bytes64 (sp + word 776)) s = word retpc /\
              byte_list_at (take i (bytes_mod_blocks (m0 ++ m))) (word_add ctx_p (word 80)) s /\
              byte_list_at m m_p s /\
              hash_buffer_at (sha512 (bytes_to_blocks (m0 ++ m)) (LENGTH (m0 ++ m) DIV 128)) ctx_p s /\
              read (memory :> bytes64 (ctx_p + word 64)) s = word ((LENGTH (m0 ++ m) * 8) MOD 2 EXP 64) /\
              read (memory :> bytes64 (ctx_p + word 72)) s = word ((LENGTH (m0 ++ m) * 8) DIV 2 EXP 64) /\
              constants_at (word K_base) s` THEN
            REPEAT CONJ_TAC THENL
            [ (* Subgoal 1: initialization *)
              ENSURES_INIT_TAC "s233" THEN
                ASSUM_EXPAND_SHA512_SPECS_TAC THEN
                ARM_STEPS_TAC SHA512_EXEC (234--239) THEN
                POP_ASSUM MP_TAC THEN
                ASM_REWRITE_TAC [MIN; VAL_WORD_SUB_EQ_0] THEN
                IMP_REWRITE_TAC [ADD_SUB_SWAP2; SUB_REFL; SUB_0] THEN
                ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
                STRIP_TAC THEN
                ARM_STEPS_TAC SHA512_EXEC (240--241) THEN
                (* Prepare to process the cur_block buffer *)
                SUBGOAL_THEN `hash_buffer_at (sha512 (bytes_to_blocks m0) (LENGTH m0 DIV 128)) ctx_p s241 /\
                  constants_at (word K_base) s241` STRIP_ASSUME_TAC THENL
                [ REWRITE_TAC [constants_at; hash_buffer_at; EXPAND_HASH_THM] THEN
                    CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
                    ASM_REWRITE_TAC [];
                  ALL_TAC] THEN
                SUBGOAL_THEN
                  `msg_block_at
                    (bytes_to_one_block (bytes_mod_blocks m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m))
                    (ctx_p + word 80) s241` ASSUME_TAC THENL
                [ MATCH_MP_TAC BYTE_LIST_AT_MSG_BLOCK_AT THEN
                    ASM_REWRITE_TAC [byte_list_at] THEN
                    REWRITE_TAC [take; LENGTH_APPEND; LENGTH_SUB_LIST] THEN
                    SIMPLE_ARITH_TAC;
                  ALL_TAC] THEN
                ARM_SUBROUTINE_SIM_TAC
                  (SPEC_ALL sha512_mc, SHA512_EXEC, 0, SPEC_ALL sha512_mc,
                    REWRITE_RULE [num_bytes_per_block] SHA512_PROCESS_BLOCK)
                  [ `sp + word 768 : int64`; `ctx_p:int64`; `sha512 (bytes_to_blocks m0) (LENGTH m0 DIV 128)`;
                    `ctx_p + word 80 : int64`;
                    `bytes_to_one_block (bytes_mod_blocks m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m)`;
                    `pc : num`; `pc + 0x3c4`; `K_base : num`] 242 THEN
                RENAME_TAC `s242:armstate` `s241_ret:armstate` THEN
                MP_TAC (REWRITE_RULE [GSYM sha512]
                  (SPECL [`h_init:hash_t`; `m0:byte list`; `take (128 - LENGTH (bytes_mod_blocks m0)) (m:byte list)`]
                    SHA512'_BLOCK_BYTES_MOD_BLOCKS_STEP)) THEN
                ANTS_TAC THENL
                [ REWRITE_TAC [take; LENGTH_SUB_LIST; MIN] THEN
                  ASSUME_TAC (REWRITE_RULE [num_bytes_per_block]
                    (SPEC `m0 : byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
                    SIMPLE_ARITH_TAC;
                  ALL_TAC ] THEN
                DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
                ASSUM_EXPAND_SHA512_SPECS_TAC THEN
                ARM_STEPS_TAC SHA512_EXEC (242--243) THEN
                POP_ASSUM MP_TAC THEN
                ASM_REWRITE_TAC [MIN] THEN
                SUBGOAL_THEN `word_sub (word (LENGTH (m:byte list))) (word (128 - LENGTH (bytes_mod_blocks m0))) =
                  word (LENGTH m - (128 - LENGTH (bytes_mod_blocks m0))):int64` ASSUME_TAC THENL
                [ REWRITE_TAC [WORD_SUB] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                VAL_INT64_TAC `LENGTH (m:byte list) - (128 - LENGTH (bytes_mod_blocks m0))` THEN
                ASM_REWRITE_TAC [] THEN
                COND_CASES_TAC THEN STRIP_TAC THENL
                [ MP_TAC (SPECL [`bytes_to_blocks (m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m)`;
                    `bytes_to_blocks (m0 ++ m)`;
                    `LENGTH (m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m) DIV 128`] BLOCKS_EQ_SHA512_EQ) THEN
                    ANTS_TAC THENL
                    [ REPEAT STRIP_TAC THEN
                        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
                          [GSYM (ISPECL [`m:byte list`; `128 - LENGTH (bytes_mod_blocks m0)`] SUB_LIST_TOPSPLIT)] THEN
                        REWRITE_TAC [APPEND_ASSOC] THEN
                        ASM_SIMP_TAC [GSYM take; BLOCKS_APPEND_EQ_LAND];
                      ALL_TAC ] THEN
                    SUBGOAL_THEN `LENGTH (m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m) DIV 128 = LENGTH (m0 ++ m) DIV 128`
                    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
                    [ GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
                        [GSYM (ISPECL [`m:byte list`; `128 - LENGTH (bytes_mod_blocks m0)`] SUB_LIST_TOPSPLIT)] THEN
                        REWRITE_TAC [take; LENGTH_APPEND; LENGTH; LENGTH_SUB_LIST; MIN] THEN
                        ASM_REWRITE_TAC [SUB_0; LE_REFL] THEN
                        REWRITE_TAC [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD] THEN
                        RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD]) THEN
                        REWRITE_TAC [ARITH_RULE `x + y - z + a - (b - c) = (x + y - z) + a - (b - c)`] THEN
                        REWRITE_TAC [ARITH_RULE `x + 128 - x MOD 128 = x - x MOD 128 + 128`] THEN
                        SUBGOAL_THEN `~(128 = 0) /\ (LENGTH (m0:byte list) - LENGTH m0 MOD 128 + 128) MOD 128 = 0`
                          (MP_TAC o MATCH_MP MOD_0_ADD_DIV) THENL
                        [ SIMP_TAC [ADD_MODULUS_MOD; SUB_MOD_MOD; ARITH]; ALL_TAC ] THEN
                        DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
                        SIMPLE_ARITH_TAC;
                      ALL_TAC ] THEN
                    DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
                    ARM_STEPS_TAC SHA512_EXEC (251--253) THEN
                    ENSURES_FINAL_STATE_TAC THEN
                    EXPAND_SHA512_SPECS_TAC THEN
                    ASM_REWRITE_TAC [take; SUB_LIST_CLAUSES; LENGTH] THEN
                    CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
                    REWRITE_TAC [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD; LENGTH_APPEND] THEN
                    RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD]) THEN
                    MP_TAC NEW_INPUT_FILLS_CUR_BLOCK_ONCE_ARITH THEN
                    DISCH_THEN (fun th -> ASM_SIMP_TAC
                      [SPECL [`LENGTH (m0:byte list)`; `LENGTH (m:byte list)`] th]);
                  ARM_STEPS_TAC SHA512_EXEC (244--250) THEN
                    SUBGOAL_THEN `hash_buffer_at (sha512 (bytes_to_blocks (m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m)) (LENGTH (m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m) DIV 128)) ctx_p s250 /\
                      msg_blocks_at (bytes_to_blocks (drop (128 - LENGTH (bytes_mod_blocks m0)) m)) ((LENGTH (m:byte list) - (128 - LENGTH (bytes_mod_blocks m0))) DIV 128) (m_p + word (128 - LENGTH (bytes_mod_blocks m0))) s250 /\
                      constants_at (word K_base) s250` ASSUME_TAC THENL
                    [ EXPAND_SHA512_SPECS_TAC THEN ASM_REWRITE_TAC [] THEN
                        SUBGOAL_THEN `LENGTH (m:byte list) - (128 - LENGTH (bytes_mod_blocks m0)) =
                          LENGTH (drop (128 - LENGTH (bytes_mod_blocks m0)) m)` (fun th -> REWRITE_TAC [th]) THENL
                        [ REWRITE_TAC [drop; LENGTH_APPEND; LENGTH_SUB_LIST] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                        MATCH_MP_TAC BYTE_LIST_AT_MSG_BLOCKS_AT THEN
                        MATCH_MP_TAC SHIFT_BYTE_LIST_AT THEN
                        ASM_REWRITE_TAC [byte_list_at];
                      ALL_TAC] THEN
                    VAL_INT64_TAC `(LENGTH (m:byte list) - (128 - LENGTH (bytes_mod_blocks m0))) DIV 128` THEN
                    MP_TAC (SPEC `LENGTH (m:byte list) - (128 - LENGTH (bytes_mod_blocks m0))` INT64_USHR_7) THEN
                    ANTS_TAC THENL [ SIMPLE_ARITH_TAC ; ALL_TAC ] THEN
                    DISCH_TAC THEN
                    SUBGOAL_THEN `aligned 16 ((sp:int64) + word 768)` ASSUME_TAC THENL
                    [ ALIGNED_16_TAC; ALL_TAC ] THEN
                    ARM_SUBROUTINE_SIM_TAC
                      (SPEC_ALL sha512_mc, SHA512_EXEC, 0, SPEC_ALL sha512_mc,
                        REWRITE_RULE [num_bytes_per_block] SHA512_PROCESS_BLOCKS)
                      [ `sp + word 768 : int64`; `ctx_p:int64`; `sha512 (bytes_to_blocks (m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m)) (LENGTH (m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m) DIV 128)`;
                        `m_p + word (128 - LENGTH (bytes_mod_blocks m0)) : int64`; `bytes_to_blocks (drop (128 - LENGTH (bytes_mod_blocks m0)) m)`;
                        `word ((LENGTH (m:byte list) - (128 - LENGTH (bytes_mod_blocks m0))) DIV 128) : int64`;
                        `pc : num`; `pc + 0x3e8`; `K_base : num`] 251 THEN
                    RENAME_TAC `s251:armstate` `s250_ret:armstate` THEN
                    MP_TAC (REWRITE_RULE [GSYM sha512]
                      (SPECL [`h_init:hash_t`; `m0:byte list`; `m:byte list`] SHA512'_BLOCKS_TAKE_DROP_STEP)) THEN
                    ASM_REWRITE_TAC [] THEN
                    DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
                    ASSUM_EXPAND_SHA512_SPECS_TAC THEN
                    ARM_STEPS_TAC SHA512_EXEC (251--253) THEN
                    ENSURES_FINAL_STATE_TAC THEN
                    EXPAND_SHA512_SPECS_TAC THEN
                    ASM_REWRITE_TAC [take; SUB_LIST_CLAUSES; byte_list_at; LENGTH] THEN
                    CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
                    RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD]) THEN
                    REWRITE_TAC [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD; LENGTH_APPEND; GSYM WORD_ADD_ASSOC] THEN
                    ASM_SIMP_TAC [NEW_INPUT_FILLS_CUR_BLOCK_ARITH1; NEW_INPUT_FILLS_CUR_BLOCK_ARITH2] ];
              (* Subgoal 2: loop body *)
              REPEAT STRIP_TAC THEN
                ENSURES_INIT_TAC "s256_0" THEN
                ASSUM_EXPAND_SHA512_SPECS_TAC THEN
                ARM_STEPS_TAC SHA512_EXEC (257--258) THEN
                POP_ASSUM MP_TAC THEN
                ASSUME_TAC (REWRITE_RULE [num_bytes_per_block]
                  (SPEC `m0 ++ m : byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
                VAL_INT64_TAC `i:num` THEN
                VAL_INT64_TAC `LENGTH (bytes_mod_blocks (m0 ++ m))` THEN
                ASM_REWRITE_TAC [VAL_WORD_SUB_EQ_0] THEN STRIP_TAC THEN
                SUBGOAL_THEN `LENGTH (take i (bytes_mod_blocks (m0 ++ m))) = i` ASSUME_TAC THENL
                [ REWRITE_TAC [take; LENGTH_SUB_LIST] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                SUBGOAL_THEN `read (memory :> bytes8 (m_p + word (LENGTH (m0 ++ m) DIV 128 * 128 - LENGTH m0 + i))) s258 =
                  EL (LENGTH (m0 ++ m) DIV 128 * 128 - LENGTH m0 + i) (m:byte list)` ASSUME_TAC THENL
                [ RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_APPEND; LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD]) THEN
                    SUBGOAL_THEN `!x y. 128 - x MOD 128 <= y ==> (x + y) DIV 128 * 128 - x + (x + y) MOD 128 <= y` MP_TAC THENL
                    [ REPEAT GEN_TAC THEN
                        DISCH_THEN (ASSUME_TAC o MATCH_MP NEW_INPUT_FILLS_CUR_BLOCK_AUX) THEN
                        SIMPLE_ARITH_TAC;
                      ALL_TAC ] THEN
                    DISCH_THEN (MP_TAC o SPECL [`LENGTH (m0:byte list)`; `LENGTH (m:byte list)`]) THEN
                    ASM_REWRITE_TAC [] THEN
                    DISCH_TAC THEN
                    SUBGOAL_THEN `LENGTH (m0 ++ m) DIV 128 * 128 - LENGTH m0 + i < LENGTH (m:byte list)` ASSUME_TAC THENL
                    [ REWRITE_TAC [LENGTH_APPEND] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                    ASM_SIMP_TAC [];
                  ALL_TAC ] THEN
                ARM_STEPS_TAC SHA512_EXEC (254--256) THEN
                ENSURES_FINAL_STATE_TAC THEN
                EXPAND_SHA512_SPECS_TAC THEN
                ASM_REWRITE_TAC [WORD_ADD] THEN
                SUBGOAL_THEN `LENGTH (take (i + 1) (bytes_mod_blocks (m0 ++ m))) =
                  SUC (LENGTH (take i (bytes_mod_blocks (m0 ++ m))))` (fun th -> REWRITE_TAC [th]) THENL
                [ REWRITE_TAC [take; LENGTH_SUB_LIST] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                REPEAT STRIP_TAC THEN
                ASM_CASES_TAC `i' < LENGTH (take i (bytes_mod_blocks (m0 ++ m)))` THENL
                [ ASM_SIMP_TAC [] THEN
                    IMP_REWRITE_TAC [take; EL_SUB_LIST] THEN
                    SIMPLE_ARITH_TAC;
                  SUBGOAL_THEN `i' = LENGTH (take i (bytes_mod_blocks (m0 ++ m)))` (fun th -> REWRITE_TAC [th]) THENL
                    [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                    ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
                    IMP_REWRITE_TAC [word_zx; VAL_WORD_EQ; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
                    REPLICATE_TAC 2 (CONJ_TAC THENL [ ALL_TAC; CONV_TAC WORD_BLAST ]) THEN
                    REWRITE_TAC [WORD_VAL; take; BYTES_MOD_BLOCKS_SUB_LIST; num_bytes_per_block] THEN
                    IMP_REWRITE_TAC [SUB_LIST_SUB_LIST] THEN
                    CONJ_TAC THENL
                    [ ALL_TAC; REWRITE_TAC [GSYM LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD] THEN SIMPLE_ARITH_TAC ] THEN
                    IMP_REWRITE_TAC [EL_SUB_LIST] THEN
                    SUBGOAL_THEN `LENGTH (m0:byte list) <= LENGTH (m0 ++ m) DIV 128 * 128` ASSUME_TAC THENL
                    [ REWRITE_TAC [LENGTH_APPEND] THEN
                        IMP_REWRITE_TAC [NEW_INPUT_FILLS_CUR_BLOCK_AUX] THEN
                        ASM_REWRITE_TAC [GSYM LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD];
                      ALL_TAC ] THEN
                    REWRITE_TAC [EL_APPEND; ADD_0] THEN
                    COND_CASES_TAC THENL [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                    ASM_SIMP_TAC [ARITH_RULE `!x y i. x <= y ==> y - x + i = (y + i) - x`] THEN
                    ONCE_REWRITE_TAC [ARITH_RULE `!x y. x <= y <=> x <= y DIV 128 * 128 + y MOD 128`] THEN
                    REWRITE_TAC [GSYM LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD] THEN
                    SIMPLE_ARITH_TAC ];
              (* Subgoal 3: back edge *)
              REPEAT STRIP_TAC THEN
                ARM_SIM_TAC SHA512_EXEC [];
                ALL_TAC ] THEN
            (* After the second loop *)
            ASSUME_TAC (REWRITE_RULE [num_bytes_per_block]
              (SPEC `m0 ++ m : byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
            REWRITE_TAC [take; SUB_LIST_LENGTH] THEN
            EXPAND_SHA512_SPECS_TAC THEN
            ENSURES_INIT_TAC "s256" THEN
            ARM_STEPS_TAC SHA512_EXEC (257--263) THEN
            ENSURES_FINAL_STATE_TAC THEN
            ASM_REWRITE_TAC [] THEN
            IMP_REWRITE_TAC [word_zx; VAL_WORD_EQ; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
            SIMPLE_ARITH_TAC;
          (* All input transferred, no processing required *)
          REWRITE_TAC [take; SUB_LIST_LENGTH] THEN
          SIMP_TAC [SPECL [`bytes_to_blocks m0`; `bytes_to_blocks (m0 ++ m)`;
            `LENGTH (m0:byte list) DIV 128`] BLOCKS_EQ_SHA512_EQ; BLOCKS_APPEND_EQ_LAND] THEN
            SUBGOAL_THEN `LENGTH (m0:byte list) DIV 128 = LENGTH (m0 ++ m) DIV 128`
              (fun th -> REWRITE_TAC [th]) THENL
            [ RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD]) THEN
                REWRITE_TAC [LENGTH_APPEND] THEN
                IMP_REWRITE_TAC [ADD_MOD_LT_ADD_DIV] THEN
                SIMPLE_ARITH_TAC;
              ALL_TAC ] THEN
            ENSURES_INIT_TAC "s233" THEN
            ASSUM_EXPAND_SHA512_SPECS_TAC THEN
            SUBGOAL_THEN `LENGTH (bytes_mod_blocks m0 ++ m) < 128` ASSUME_TAC THENL
            [ REWRITE_TAC [LENGTH_APPEND] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
            ARM_STEPS_TAC SHA512_EXEC (234--239) THEN
            POP_ASSUM MP_TAC THEN
            VAL_INT64_TAC `LENGTH (bytes_mod_blocks m0) + LENGTH (m:byte list)` THEN
            ASM_REWRITE_TAC [MIN; VAL_WORD_SUB_EQ_0] THEN
            CONV_TAC WORD_REDUCE_CONV THEN
            SUBGOAL_THEN `~(LENGTH (bytes_mod_blocks m0) + LENGTH (m:byte list) = 128)`
              (fun th -> REWRITE_TAC [th]) THENL
            [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
            STRIP_TAC THEN
            ARM_STEPS_TAC SHA512_EXEC (259--263) THEN
            ENSURES_FINAL_STATE_TAC THEN
            EXPAND_SHA512_SPECS_TAC THEN
            ASM_REWRITE_TAC [MIN] THEN
            IMP_REWRITE_TAC [word_zx; VAL_WORD_EQ; DIMINDEX_32] THEN
            CONJ_TAC THENL
            [ SUBGOAL_THEN `m0 ++ m = (take (LENGTH m0 DIV 128 * 128) m0 ++ (bytes_mod_blocks m0 ++ m))`
                  (fun th -> ONCE_REWRITE_TAC [th]) THENL
                [ REWRITE_TAC [APPEND_ASSOC; TAKE_APPEND_MOD_BLOCKS_REFL];
                  ALL_TAC ] THEN
                MP_TAC (SPECL [`take (LENGTH m0 DIV 128 * 128) m0:byte list`; `bytes_mod_blocks m0 ++ m`] MOD_0_BYTES_MOD_BLOCKS_APPEND) THEN
                ANTS_TAC THENL
                [ REWRITE_TAC [take; LENGTH_SUB_LIST] THEN
                    MP_TAC (SPECL [`LENGTH (m0:byte list)`; `128`] DIV_MULT_LE) THEN
                    REWRITE_TAC [ARITH; SUB_0; MIN] THEN
                    DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
                    ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [MOD_MULT];
                  ALL_TAC] THEN
                DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
                MP_TAC (SPEC `bytes_mod_blocks m0 ++ m` BYTES_MOD_BLOCKS_REFL) THEN
                ANTS_TAC THENL
                [ REWRITE_TAC [LENGTH_APPEND] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                DISCH_THEN (fun th -> REWRITE_TAC [th]); 
              RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD]) THEN
                REWRITE_TAC [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD; LENGTH_APPEND] THEN
                SUBGOAL_THEN `LENGTH (m0:byte list) MOD 128 + LENGTH (m:byte list) < 128`
                  ASSUME_TAC THENL
                [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                ONCE_REWRITE_TAC [GSYM (CONJUNCT2 (SPEC_ALL ADD_MOD_MOD_REFL))] THEN
                ASM_SIMP_TAC [MOD_LT] THEN
                SIMPLE_ARITH_TAC ] ] ]);;

let PAD_ONE_BLOCK_ARITH = prove
  (`!x. x MOD 128 + 1 <= 112 ==>
    ceil_div (x + 1 + 16) 128 * 128 - (x + 1 + 16) = 112 - (x MOD 128 + 1)`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [ceil_div] THEN
    SUBGOAL_THEN `x = x DIV 128 * 128 + x MOD 128`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
    [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    REWRITE_TAC [ARITH_RULE `x DIV 128 * 128 + x MOD 128 + 1 + 16 + 128 - 1 =
      (x DIV 128 + 1) * 128 + x MOD 128 + 16`] THEN
    SIMP_TAC [DIV_MULT_ADD; ARITH] THEN
    POP_ASSUM (ASSUME_TAC o MATCH_MP (ARITH_RULE `!x. x + 1 <= 112 ==> x + 16 < 128`)) THEN
    ASM_SIMP_TAC [DIV_LT] THEN
    ARITH_TAC);;

let PAD_TWO_BLOCKS_ARITH = prove
(`!x. ~(x MOD 128 + 1 <= 112) ==>
  ceil_div (x + 1 + 16) 128 * 128 - (x + 1 + 16) =
  128 - (x MOD 128 + 1) + 112`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [ceil_div] THEN
    SUBGOAL_THEN `x = x DIV 128 * 128 + x MOD 128`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
    [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    REWRITE_TAC [ARITH_RULE `x DIV 128 * 128 + x MOD 128 + 1 + 16 + 128 - 1 =
      (x DIV 128 + 1) * 128 + x MOD 128 + 16`] THEN
    SIMP_TAC [DIV_MULT_ADD; ARITH] THEN
    SUBGOAL_THEN `(x MOD 128 + 16) DIV 128 = 1` (fun th -> REWRITE_TAC [th]) THENL
    [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
    ARITH_TAC);;

(* void sha512_final(uint8_t out[SHA512_DIGEST_LENGTH], sha512_ctx *sha) *)
let SHA512_FINAL = prove
  (`!sp out_p ctx_p m pc retpc K_base.
    aligned 16 sp /\
    adrp_within_bounds (word K_base) (word (pc + 0x110)) /\
    PAIRWISE nonoverlapping
      [(word pc : int64, 1308); (out_p, 64); (ctx_p, 216);
       (word_sub sp (word 768), 768); (word K_base, 640)] /\
    LENGTH m < 2 EXP 125 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (sha512_mc pc K_base) /\
         read PC s = word (pc + 0x41c) /\
         read X30 s = word retpc /\
         read SP s = sp /\
         read X0 s = out_p /\
         read X1 s = ctx_p /\
         sha512_ctx_at m ctx_p s /\
         constants_at (word K_base) s)
    (\s. read PC s = word retpc /\
        byte_list_at (sha512_pad m) out_p s)
    (MAYCHANGE [X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                X12; X13; X14; X15; X16; X17; X18; PC] ,,
     MAYCHANGE [memory :> bytes(ctx_p, 216)] ,,
     MAYCHANGE [memory :> bytes(out_p, 64)] ,,
     MAYCHANGE [memory :> bytes(word_sub sp (word 768), 768)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; sha512_pad; num_bytes_per_block] THEN
    WORD_FORALL_OFFSET_TAC 768 THEN
    REPEAT STRIP_TAC THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
    ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
    ENSURES_PRESERVED_TAC "x21_init" `X21` THEN

    ASM_CASES_TAC `LENGTH (bytes_mod_blocks m) + 1 <= 112` THENL
    [ (* The padding can fit into one final block *)
      ENSURES_WHILE_AUP_OR_0_TAC
        `LENGTH (bytes_mod_blocks m) + 1` `112` `pc + 0x480` `pc + 0x480`
        `\i s. // loop invariant
          read SP s = sp + word 720 /\ read X2 s = word i /\ read X19 s = ctx_p /\
          read X20 s = out_p /\ read X21 s = ctx_p + word 80 /\
          read (memory :> bytes64 (sp + word 736)) s = x19_init /\
          read (memory :> bytes64 (sp + word 744)) s = x20_init /\
          read (memory :> bytes64 (sp + word 752)) s = x21_init /\
          read (memory :> bytes64 (sp + word 720)) s = x29_init /\
          read (memory :> bytes64 (sp + word 728)) s = word retpc /\
          hash_buffer_at (sha512 (bytes_to_blocks m) (LENGTH m DIV 128)) ctx_p s /\
          byte_list_at (bytes_mod_blocks m ++ [word 0x80] ++ REPLICATE (i - (LENGTH (bytes_mod_blocks m) + 1)) (word 0 : byte))
            (word_add ctx_p (word (8 * 10))) s /\
          read (memory :> bytes64 (ctx_p + word 64)) s = word ((LENGTH m * 8) MOD 2 EXP 64) /\
          read (memory :> bytes64 (ctx_p + word 72)) s = word ((LENGTH m * 8) DIV 2 EXP 64) /\
          constants_at (word K_base) s` THEN
        REPEAT CONJ_TAC THENL
        [ (* Subgoal 1: well-defined bounds *)
          ASM_REWRITE_TAC [];
          (* Subgoal 2: initialization *)
          ENSURES_INIT_TAC "s263" THEN
            ASSUM_EXPAND_SHA512_SPECS_TAC THEN
            ARM_STEPS_TAC SHA512_EXEC (264--271) THEN
            REPLICATE_TAC 2 (POP_ASSUM MP_TAC) THEN
            IMP_REWRITE_TAC [word_zx; VAL_WORD_EQ; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
            ASSUME_TAC (REWRITE_RULE [num_bytes_per_block]
              (SPEC `m : byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
            REPEAT (ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]) THEN
            REPEAT STRIP_TAC THEN
            ARM_STEPS_TAC SHA512_EXEC (272--276) THEN
            POP_ASSUM MP_TAC THEN
            SIMP_TAC [BITBLAST_RULE `!x:int64. x + word 18446744073709551505 = word_sub (x + word 1) (word 112)`] THEN
            SIMP_TAC [CONV_RULE WORD_REDUCE_CONV
              (ISPECL [`word (LENGTH (bytes_mod_blocks m)) + word 1 : int64`; `word 112 : int64`]
                BLS_LS)] THEN
            IMP_REWRITE_TAC [GSYM WORD_ADD; VAL_WORD_EQ; DIMINDEX_64] THEN
            ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
            STRIP_TAC THEN
            ARM_STEPS_TAC SHA512_EXEC [285] THEN
            ENSURES_FINAL_STATE_TAC THEN
            EXPAND_SHA512_SPECS_TAC THEN
            ASM_REWRITE_TAC [WORD_ADD; REPLICATE; APPEND_NIL] THEN
            SUBGOAL_THEN `LENGTH (bytes_mod_blocks m ++ [word 128]) =
              SUC (LENGTH (bytes_mod_blocks m))` (fun th -> REWRITE_TAC [th]) THENL
            [ REWRITE_TAC [LENGTH_APPEND; LENGTH; ADD; ADD1]; ALL_TAC ] THEN
            REPEAT STRIP_TAC THEN
            ASM_CASES_TAC `i < LENGTH (bytes_mod_blocks m)` THENL
            [ ASM_SIMP_TAC [EL_APPEND];
              SUBGOAL_THEN `i = LENGTH (bytes_mod_blocks m)` (fun th -> REWRITE_TAC [th]) THENL
              [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
              ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                EL_APPEND; LT_REFL; SUB_REFL; EL; HD] ];
          (* Subgoal 3 : loop body *)
          REPEAT STRIP_TAC THEN
            ENSURES_INIT_TAC "s288_0" THEN
            ASSUM_EXPAND_SHA512_SPECS_TAC THEN
            SUBGOAL_THEN `LENGTH (bytes_mod_blocks m ++ [word 128] ++
              REPLICATE (i - (LENGTH (bytes_mod_blocks m) + 1)) (word 0)) = i`
              ASSUME_TAC THENL
            [ REWRITE_TAC [LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN
                SIMPLE_ARITH_TAC;
              ALL_TAC ] THEN
            POP_ASSUM (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
            ARM_STEPS_TAC SHA512_EXEC (289--290) THEN
            POP_ASSUM MP_TAC THEN
            SIMP_TAC [BITBLAST_RULE `!x:int64. x + word 18446744073709551505 = word_sub (x + word 1) (word 112)`] THEN
            VAL_INT64_TAC `i:num` THEN
            ASM_REWRITE_TAC [VAL_WORD_SUB_EQ_0] THEN
            CONV_TAC WORD_REDUCE_CONV THEN
            ASM_REWRITE_TAC [GSYM WORD_ADD] THEN STRIP_TAC THEN
            ARM_STEPS_TAC SHA512_EXEC (294--295) THEN
            ENSURES_FINAL_STATE_TAC THEN
            EXPAND_SHA512_SPECS_TAC THEN
            ASM_REWRITE_TAC [WORD_ADD] THEN
            ASM_SIMP_TAC [ARITH_RULE `!x i. x <= i ==> (i+1) - x = SUC (i - x)`] THEN
            REWRITE_TAC [REPLICATE; CONS_REPLICATE_REPLICATE_APPEND] THEN
            REWRITE_TAC [LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN
            ASM_SIMP_TAC [ARITH_RULE `!x i. x+1 <= i ==> x + SUC 0 + i - (x + 1) + SUC 0 = SUC i`] THEN
            REPEAT STRIP_TAC THEN
            ASM_CASES_TAC `i' < i` THENL
            [ ASM_SIMP_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
                REWRITE_TAC [APPEND_ASSOC] THEN
                GEN_REWRITE_TAC RAND_CONV [EL_APPEND] THEN
                COND_CASES_TAC THENL
                [ REWRITE_TAC [];
                  POP_ASSUM MP_TAC THEN
                    REWRITE_TAC [LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN
                    SIMPLE_ARITH_TAC ];
              SUBGOAL_THEN `i' = i:num` (fun th -> REWRITE_TAC [th]) THENL
                [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
                ASM_SIMP_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
                REWRITE_TAC [APPEND_ASSOC] THEN
                ONCE_REWRITE_TAC [EL_APPEND] THEN
                REWRITE_TAC [LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN
                COND_CASES_TAC THENL
                [ SIMPLE_ARITH_TAC;
                  ASM_SIMP_TAC [ARITH_RULE `!x i. x+1 <= i ==> i - ((x + SUC 0) + i - (x + 1)) = 0`] THEN
                    REWRITE_TAC [EL; HD] ] ];
          (* Subgoal 4: backedge *)
          REPEAT STRIP_TAC THEN
            ARM_SIM_TAC SHA512_EXEC [];
          ALL_TAC ] THEN
        (* After the final loop *)
        ENSURES_INIT_TAC "s288" THEN
          ASSUM_EXPAND_SHA512_SPECS_TAC THEN
          SUBGOAL_THEN `LENGTH (bytes_mod_blocks m ++ [word 128] ++
            REPLICATE (112 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0)) = 112` ASSUME_TAC THENL
          [ REWRITE_TAC [LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
          POP_ASSUM (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN ASSUME_TAC th) THEN
          ARM_STEPS_TAC SHA512_EXEC (289--299) THEN
          SUBGOAL_THEN `hash_buffer_at (sha512 (bytes_to_blocks m) (LENGTH m DIV 128)) ctx_p s299 /\
            constants_at (word K_base) s299` ASSUME_TAC THENL
          [ REWRITE_TAC [hash_buffer_at; constants_at; EXPAND_HASH_THM] THEN
              CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
              ASM_REWRITE_TAC [];
            ALL_TAC] THEN
          SUBGOAL_THEN
            `msg_block_at
              (bytes_to_one_block (bytes_mod_blocks m ++ [word 0x80] ++
                REPLICATE ((ceil_div (LENGTH m + 1 + 16) num_bytes_per_block) * num_bytes_per_block - (LENGTH m + 1 + 16)) (word 0) ++
                int128_to_bytes (word_bytereverse (word (LENGTH m * 8)))))
              (ctx_p + word 80) s299` ASSUME_TAC THENL
            [ RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD]) THEN
                REWRITE_TAC [num_bytes_per_block; LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD] THEN
                ASM_SIMP_TAC [PAD_ONE_BLOCK_ARITH] THEN
                MATCH_MP_TAC BYTE_LIST_AT_MSG_BLOCK_AT THEN
                CONJ_TAC THENL
                [ REWRITE_TAC [LENGTH; LENGTH_APPEND; int128_to_bytes; LENGTH_REPLICATE;
                      LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD] THEN
                    ARITH_TAC;
                  REWRITE_TAC [APPEND_ASSOC] THEN
                    ONCE_REWRITE_TAC [BYTE_LIST_AT_APPEND] THEN
                    CONJ_TAC THENL
                    [ ASM_REWRITE_TAC [byte_list_at; GSYM APPEND_ASSOC];
                      REWRITE_TAC [LENGTH; LENGTH_APPEND; LENGTH_REPLICATE;
                          LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD; GSYM ONE] THEN
                        ASM_SIMP_TAC [ARITH_RULE `!x. x <= 112 ==> x + 112 - x = 112`] THEN
                        MATCH_MP_TAC INT64_HI_LO_INT128 THEN
                        REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
                        CONV_TAC (TOP_DEPTH_CONV NUM_ADD_CONV) THEN
                        ASM_REWRITE_TAC [] THEN
                        SIMPLE_ARITH_TAC ] ];
              ALL_TAC ] THEN
          ARM_SUBROUTINE_SIM_TAC
            (SPEC_ALL sha512_mc, SHA512_EXEC, 0, SPEC_ALL sha512_mc,
              REWRITE_RULE [num_bytes_per_block] SHA512_PROCESS_BLOCK)
            [ `sp + word 720 : int64`; `ctx_p:int64`; `sha512 (bytes_to_blocks m) (LENGTH m DIV 128)`;
              `ctx_p + word 80 : int64`;
              `bytes_to_one_block (bytes_mod_blocks m ++ [word 0x80] ++
                REPLICATE ((ceil_div (LENGTH m + 1 + 16) num_bytes_per_block) * num_bytes_per_block - (LENGTH m + 1 + 16)) (word 0) ++
                int128_to_bytes (word_bytereverse (word (LENGTH m * 8))))`;
              `pc : num`; `pc + 0x4ac`; `K_base : num`] 300 THEN
          RENAME_TAC `s300:armstate` `s299_ret:armstate` THEN
          MP_TAC (REWRITE_RULE [GSYM sha512] (SPECL [`h_init:hash_t`; `m:byte list`;
            `[word 128] ++
            REPLICATE
              (ceil_div (LENGTH m + 1 + 16) num_bytes_per_block *
              num_bytes_per_block -
              (LENGTH (m:byte list) + 1 + 16))
              (word 0) ++
            int128_to_bytes (word_bytereverse (word (LENGTH m * 8)))`]
            SHA512'_BLOCK_BYTES_MOD_BLOCKS_STEP)) THEN
          ANTS_TAC THENL
          [ REWRITE_TAC [LENGTH; LENGTH_APPEND; LENGTH_REPLICATE; int128_to_bytes;
                          LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD; num_bytes_per_block] THEN
              RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD]) THEN
              ASM_SIMP_TAC [PAD_ONE_BLOCK_ARITH] THEN
              SIMPLE_ARITH_TAC;
            ALL_TAC ] THEN
          REWRITE_TAC [GSYM pad] THEN
          DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
          ASSUM_EXPAND_SHA512_SPECS_TAC THEN
          ARM_STEPS_TAC SHA512_EXEC (309--336) THEN
          ENSURES_FINAL_STATE_TAC THEN
          ASM_REWRITE_TAC [hash_buffer_to_byte_list] THEN
          REWRITE_TAC [BYTE_LIST_AT_APPEND] THEN
          SUBGOAL_THEN `!w. LENGTH (int64_to_bytes w) = 8` (fun th -> REWRITE_TAC [th]) THENL
          [ REWRITE_TAC [LENGTH; int64_to_bytes] THEN ARITH_TAC; ALL_TAC ] THEN
          ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ARITH] THEN
          ASM_REWRITE_TAC [GSYM INT64_BYTE_LIST];
      (* The padding cannot fit into one final block *)
      ENSURES_WHILE_AUP_OR_0_TAC
        `LENGTH (bytes_mod_blocks m) + 1` `128` `pc + 0x45c` `pc + 0x45c`
        `\i s. // loop invariant
            read SP s = sp + word 720 /\ read X2 s = word i /\ read X19 s = ctx_p /\
            read X20 s = out_p /\ read X21 s = ctx_p + word 80 /\
            read (memory :> bytes64 (sp + word 736)) s = x19_init /\
            read (memory :> bytes64 (sp + word 744)) s = x20_init /\
            read (memory :> bytes64 (sp + word 752)) s = x21_init /\
            read (memory :> bytes64 (sp + word 720)) s = x29_init /\
            read (memory :> bytes64 (sp + word 728)) s = word retpc /\
            hash_buffer_at (sha512 (bytes_to_blocks m) (LENGTH m DIV 128)) ctx_p s /\
            byte_list_at (bytes_mod_blocks m ++ [word 0x80] ++ REPLICATE (i - (LENGTH (bytes_mod_blocks m) + 1)) (word 0))
              (word_add ctx_p (word (8 * 10))) s /\
            read (memory :> bytes64 (ctx_p + word 64)) s = word ((LENGTH m * 8) MOD 2 EXP 64) /\
            read (memory :> bytes64 (ctx_p + word 72)) s = word ((LENGTH m * 8) DIV 2 EXP 64) /\
            constants_at (word K_base) s` THEN
      REPEAT CONJ_TAC THENL
      [ (* Subgoal 1: well-defined bounds *)
        ASSUME_TAC (REWRITE_RULE [num_bytes_per_block]
          (SPEC `m : byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
          SIMPLE_ARITH_TAC;
        (* Subgoal 2: initialization *)
        ENSURES_INIT_TAC "s263" THEN
          ASSUM_EXPAND_SHA512_SPECS_TAC THEN
          ASSUME_TAC (REWRITE_RULE [num_bytes_per_block]
            (SPEC `m:byte list`LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
          ARM_STEPS_TAC SHA512_EXEC (264--271) THEN
          REPLICATE_TAC 2 (POP_ASSUM MP_TAC) THEN
          IMP_REWRITE_TAC [word_zx; VAL_WORD_EQ; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
          ASSUME_TAC (REWRITE_RULE [num_bytes_per_block]
            (SPEC `m : byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
          REPEAT (ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]) THEN
          REPEAT STRIP_TAC THEN
          ARM_STEPS_TAC SHA512_EXEC (272--276) THEN
          POP_ASSUM MP_TAC THEN
          SIMP_TAC [BITBLAST_RULE `!x:int64. x + word 18446744073709551505 = word_sub (x + word 1) (word 112)`] THEN
          SIMP_TAC [CONV_RULE WORD_REDUCE_CONV
            (ISPECL [`word (LENGTH (bytes_mod_blocks m)) + word 1 : int64`; `word 112 : int64`]
              BLS_LS)] THEN
          IMP_REWRITE_TAC [GSYM WORD_ADD; VAL_WORD_EQ; DIMINDEX_64] THEN
          ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          STRIP_TAC THEN
          ARM_STEPS_TAC SHA512_EXEC [279] THEN
          ENSURES_FINAL_STATE_TAC THEN
          EXPAND_SHA512_SPECS_TAC THEN
          ASM_REWRITE_TAC [WORD_ADD; REPLICATE; APPEND_NIL] THEN
          REPEAT STRIP_TAC THEN
          ASM_CASES_TAC `i < LENGTH (bytes_mod_blocks m)` THENL
          [ ASM_SIMP_TAC [] THEN ASM_REWRITE_TAC [EL_APPEND];
            SUBGOAL_THEN `i = LENGTH (bytes_mod_blocks m)` ASSUME_TAC THENL
              [ RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_APPEND; LENGTH]) THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
              ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
              REWRITE_TAC [EL_APPEND; LT_REFL; SUB_REFL; EL; HD] ];
        (* Subgoal 3: loop body *)
        REPEAT STRIP_TAC THEN
          ENSURES_INIT_TAC "s279_0" THEN
          ASSUM_EXPAND_SHA512_SPECS_TAC THEN
          SUBGOAL_THEN `LENGTH (bytes_mod_blocks m ++ [word 128] ++
            REPLICATE (i - (LENGTH (bytes_mod_blocks m) + 1)) (word 0)) = i`
            ASSUME_TAC THENL
          [ REWRITE_TAC [LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
          POP_ASSUM (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN ASSUME_TAC th) THEN
          ARM_STEPS_TAC SHA512_EXEC (280--281) THEN
          POP_ASSUM MP_TAC THEN
          SIMP_TAC [BITBLAST_RULE `!x:int64. x + word 18446744073709551489 = word_sub (x + word 1) (word 128)`] THEN
          VAL_INT64_TAC `i : num` THEN
          ASM_REWRITE_TAC [VAL_WORD_SUB_EQ_0] THEN
          CONV_TAC WORD_REDUCE_CONV THEN
          ASM_REWRITE_TAC [GSYM WORD_ADD] THEN STRIP_TAC THEN
          ARM_STEPS_TAC SHA512_EXEC (278--279) THEN
          ENSURES_FINAL_STATE_TAC THEN
          EXPAND_SHA512_SPECS_TAC THEN
          ASM_REWRITE_TAC [WORD_ADD] THEN
          ASM_SIMP_TAC [ARITH_RULE `!x i. x <= i ==> (i+1) - x = SUC (i - x)`] THEN
          REWRITE_TAC [REPLICATE; CONS_REPLICATE_REPLICATE_APPEND] THEN
          REWRITE_TAC [APPEND_ASSOC] THEN ONCE_REWRITE_TAC [LENGTH_APPEND] THEN
          ASM_REWRITE_TAC [GSYM APPEND_ASSOC; LENGTH] THEN
          REPEAT STRIP_TAC THEN
          ASM_CASES_TAC `i' < i` THENL
          [ ASM_SIMP_TAC [] THEN
              REWRITE_TAC [APPEND_ASSOC] THEN
              GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [LENGTH_APPEND] THEN
              GEN_REWRITE_TAC RAND_CONV [EL_APPEND] THEN
              COND_CASES_TAC THENL
              [ REWRITE_TAC [];
                POP_ASSUM MP_TAC THEN
                  ASM_REWRITE_TAC [GSYM APPEND_ASSOC] THEN
                  SIMPLE_ARITH_TAC ];
            SUBGOAL_THEN `i' = i : num` (fun th -> REWRITE_TAC [th]) THENL
              [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
              ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
              REWRITE_TAC [APPEND_ASSOC] THEN
              GEN_REWRITE_TAC RAND_CONV [EL_APPEND] THEN
              ASM_REWRITE_TAC [GSYM APPEND_ASSOC; LT_REFL; SUB_REFL; EL; HD] ];
        (* Subgoal 4: backedge *)
        REPEAT STRIP_TAC THEN
          ARM_SIM_TAC SHA512_EXEC [];
        ALL_TAC ] THEN
      (* After the first loop *)
      ENSURES_WHILE_UP_TAC
        `112` `pc + 0x480` `pc + 0x480`
        `\i s. // loop invariant
            read SP s = sp + word 720 /\ read X2 s = word i /\ read X19 s = ctx_p /\
            read X20 s = out_p /\ read X21 s = ctx_p + word 80 /\
            read (memory :> bytes64 (sp + word 736)) s = x19_init /\
            read (memory :> bytes64 (sp + word 744)) s = x20_init /\
            read (memory :> bytes64 (sp + word 752)) s = x21_init /\
            read (memory :> bytes64 (sp + word 720)) s = x29_init /\
            read (memory :> bytes64 (sp + word 728)) s = word retpc /\
            hash_buffer_at (sha512 (bytes_to_blocks (m ++ [word 0x80] ++ REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0))) (LENGTH (m ++ [word 0x80] ++ REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0)) DIV 128)) ctx_p s /\
            byte_list_at (REPLICATE i (word 0)) (word_add ctx_p (word (8 * 10))) s /\
            read (memory :> bytes64 (ctx_p + word 64)) s = word ((LENGTH m * 8) MOD 2 EXP 64) /\
            read (memory :> bytes64 (ctx_p + word 72)) s = word ((LENGTH m * 8) DIV 2 EXP 64) /\
            constants_at (word K_base) s` THEN
      REPEAT CONJ_TAC THENL
      [ (* Subgoal 1: non-zero iterations *)
        ARITH_TAC;
        (* Subgoal 2: initialization *)
        ENSURES_INIT_TAC "s279" THEN
          ASSUM_EXPAND_SHA512_SPECS_TAC THEN
          ASSUME_TAC (REWRITE_RULE [num_bytes_per_block] (SPEC `m:byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
          SUBGOAL_THEN `LENGTH (bytes_mod_blocks m ++ [word 128] ++
            REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0)) = 128` ASSUME_TAC THENL
          [ REWRITE_TAC [LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN SIMPLE_ARITH_TAC ; ALL_TAC ] THEN
          POP_ASSUM (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN ASSUME_TAC th) THEN
          ARM_STEPS_TAC SHA512_EXEC (280--284) THEN
          SUBGOAL_THEN `hash_buffer_at (sha512 (bytes_to_blocks m) (LENGTH m DIV 128)) ctx_p s284 /\
            constants_at (word K_base) s284` ASSUME_TAC THENL
          [ REWRITE_TAC [hash_buffer_at; constants_at; EXPAND_HASH_THM] THEN
              CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
              ASM_REWRITE_TAC [];
            ALL_TAC] THEN
          SUBGOAL_THEN
            `msg_block_at
              (bytes_to_one_block (bytes_mod_blocks m ++ [word 0x80] ++
                REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0)))
              (ctx_p + word 80) s284` ASSUME_TAC THENL
          [ MATCH_MP_TAC BYTE_LIST_AT_MSG_BLOCK_AT THEN
              REWRITE_TAC [LENGTH; LENGTH_APPEND; LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD;
                LENGTH_REPLICATE] THEN
              CONJ_TAC THENL [ ARITH_TAC; ALL_TAC ] THEN
              REWRITE_TAC [byte_list_at] THEN
              ASM_REWRITE_TAC [GSYM LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD];
            ALL_TAC ] THEN
          ARM_SUBROUTINE_SIM_TAC
            (SPEC_ALL sha512_mc, SHA512_EXEC, 0, SPEC_ALL sha512_mc,
              REWRITE_RULE [num_bytes_per_block] SHA512_PROCESS_BLOCK)
            [ `sp + word 720 : int64`; `ctx_p:int64`; `sha512 (bytes_to_blocks m) (LENGTH m DIV 128)`;
              `ctx_p + word 80 : int64`;
              `bytes_to_one_block (bytes_mod_blocks m ++ [word 0x80] ++
                REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0))`;
              `pc : num`; `pc + 0x470`; `K_base : num`] 285 THEN
          RENAME_TAC `s285:armstate` `s284_ret:armstate` THEN
          MP_TAC (REWRITE_RULE [GSYM sha512]
            (SPECL [`h_init:hash_t`; `m:byte list`;
              `[word 128] ++
                REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0):byte list`]
              SHA512'_BLOCK_BYTES_MOD_BLOCKS_STEP)) THEN
          ANTS_TAC THENL
          [ REWRITE_TAC [LENGTH; LENGTH_APPEND; LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD;
              LENGTH_REPLICATE] THEN ARITH_TAC;
            ALL_TAC ] THEN
          DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
          ASSUM_EXPAND_SHA512_SPECS_TAC THEN
          ARM_STEPS_TAC SHA512_EXEC (285--286) THEN
          ENSURES_FINAL_STATE_TAC THEN
          ASM_REWRITE_TAC [WORD_ADD; REPLICATE; LENGTH; byte_list_at] THEN
          CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
          EXPAND_SHA512_SPECS_TAC THEN
          ASM_REWRITE_TAC [];
        (* Subgoal 3: loop body *)
        REPEAT STRIP_TAC THEN
          ENSURES_INIT_TAC "s288_0" THEN
          ASSUM_EXPAND_SHA512_SPECS_TAC THEN
          RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_REPLICATE]) THEN
          ARM_STEPS_TAC SHA512_EXEC (289--290) THEN
          POP_ASSUM MP_TAC THEN
          SIMP_TAC [BITBLAST_RULE `!x:int64. x + word 18446744073709551505 = word_sub (x + word 1) (word 112)`] THEN
          VAL_INT64_TAC `i:num` THEN
          ASM_REWRITE_TAC [VAL_WORD_SUB_EQ_0] THEN
          CONV_TAC WORD_REDUCE_CONV THEN
          ASM_REWRITE_TAC [GSYM WORD_ADD] THEN STRIP_TAC THEN
          ARM_STEPS_TAC SHA512_EXEC (287--288) THEN
          ENSURES_FINAL_STATE_TAC THEN
          EXPAND_SHA512_SPECS_TAC THEN
          ASM_REWRITE_TAC [WORD_ADD] THEN
          REWRITE_TAC [REPLICATE; GSYM ADD1; CONS_REPLICATE_REPLICATE_APPEND] THEN
          REWRITE_TAC [LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN
          REPEAT STRIP_TAC THEN
          ASM_CASES_TAC `i' < i` THENL
          [ ASM_SIMP_TAC [] THEN
              ASM_REWRITE_TAC [EL_APPEND; LENGTH_REPLICATE];
            SUBGOAL_THEN `i' = i : num` (fun th -> REWRITE_TAC [th]) THENL
              [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
              ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
              ASM_REWRITE_TAC [EL_APPEND; LENGTH_REPLICATE; LT_REFL; SUB_REFL; EL; HD] ];
        (* Subgoal 4: backedge *)
        REPEAT STRIP_TAC THEN
          ARM_SIM_TAC SHA512_EXEC [];
        ALL_TAC ] THEN
      (* After the final loop *)
      ENSURES_INIT_TAC "s288" THEN
        ASSUM_EXPAND_SHA512_SPECS_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_REPLICATE]) THEN
        ARM_STEPS_TAC SHA512_EXEC (289--299) THEN
        SUBGOAL_THEN
        `hash_buffer_at
          (sha512
            (bytes_to_blocks
              (m ++ [word 128] ++
                REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0)))
            (LENGTH (m ++ [word 128] ++
                REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0)) DIV 128)) ctx_p s299 /\
          constants_at (word K_base) s299` ASSUME_TAC THENL
        [ REWRITE_TAC [hash_buffer_at; constants_at; EXPAND_HASH_THM] THEN
            CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
            ASM_REWRITE_TAC [];
          ALL_TAC] THEN
        SUBGOAL_THEN
          `msg_block_at
            (bytes_to_one_block (REPLICATE 112 (word 0) ++
              int128_to_bytes (word_bytereverse (word (LENGTH (m : byte list) * 8)))))
            (ctx_p + word 80) s299` ASSUME_TAC THENL
        [ MATCH_MP_TAC BYTE_LIST_AT_MSG_BLOCK_AT THEN
            CONJ_TAC THENL
            [ REWRITE_TAC [LENGTH; LENGTH_APPEND; int128_to_bytes; LENGTH_REPLICATE] THEN
                ARITH_TAC;
              REWRITE_TAC [APPEND_ASSOC] THEN
                ONCE_REWRITE_TAC [BYTE_LIST_AT_APPEND] THEN
                CONJ_TAC THENL
                [ ASM_REWRITE_TAC [byte_list_at; LENGTH_REPLICATE];
                  MATCH_MP_TAC INT64_HI_LO_INT128 THEN
                    REWRITE_TAC [LENGTH_REPLICATE; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
                    CONV_TAC (TOP_DEPTH_CONV NUM_ADD_CONV) THEN
                    ASM_REWRITE_TAC [] THEN
                    SIMPLE_ARITH_TAC ] ];
          ALL_TAC ] THEN
        ARM_SUBROUTINE_SIM_TAC
          (SPEC_ALL sha512_mc, SHA512_EXEC, 0, SPEC_ALL sha512_mc,
            REWRITE_RULE [num_bytes_per_block] SHA512_PROCESS_BLOCK)
          [ `sp + word 720 : int64`; `ctx_p:int64`; `sha512 (bytes_to_blocks
              (m ++ [word 128] ++
                REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0)))
            (LENGTH (m ++ [word 128] ++
                REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0)) DIV 128)`;
            `ctx_p + word 80 : int64`;
            `bytes_to_one_block (REPLICATE 112 (word 0) ++
              int128_to_bytes (word_bytereverse (word (LENGTH (m : byte list) * 8))))`;
            `pc : num`; `pc + 0x4ac`; `K_base : num`] 300 THEN
        RENAME_TAC `s300:armstate` `s299_ret:armstate` THEN
        MP_TAC (REWRITE_RULE [GSYM sha512]
          (SPECL [`h_init:hash_t`;
            `m ++ [word 128] ++ REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1)) (word 0):byte list`;
            `REPLICATE 112 (word 0) ++ int128_to_bytes (word_bytereverse (word (LENGTH (m:byte list) * 8)))`]
            SHA512'_BLOCK_STEP)) THEN
        ANTS_TAC THENL
        [ REWRITE_TAC [LENGTH; LENGTH_APPEND; LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD; LENGTH_REPLICATE;
              int128_to_bytes; ARITH] THEN
            REWRITE_TAC [ARITH_RULE `!x. x + 1 + 128 - (x MOD 128 + 1) = x + 128 - x MOD 128`;
              ADD_128_SUB_MOD_0];
          ALL_TAC ] THEN
        SUBGOAL_THEN `!a b c d e:byte list. (a ++ b ++ c) ++ d ++ e = a ++ b ++ (c ++ d) ++ e`
          (fun th -> ONCE_REWRITE_TAC [th]) THENL
        [ REWRITE_TAC [APPEND_ASSOC]; ALL_TAC ] THEN
        REWRITE_TAC [REPLICATE_APPEND] THEN
        SUBGOAL_THEN `m ++ [word 128] ++
          REPLICATE (128 - (LENGTH (bytes_mod_blocks m) + 1) + 112) (word 0) ++
          int128_to_bytes (word_bytereverse (word (LENGTH m * 8))) = pad m`
          (fun th -> REWRITE_TAC [th]) THENL
        [ REWRITE_TAC [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD; pad; num_bytes_per_block] THEN
            RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD]) THEN
            ASM_SIMP_TAC [GSYM PAD_TWO_BLOCKS_ARITH];
          ALL_TAC ] THEN
        DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
        ASSUM_EXPAND_SHA512_SPECS_TAC THEN
        ARM_STEPS_TAC SHA512_EXEC (300--327) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC [hash_buffer_to_byte_list] THEN
        REWRITE_TAC [BYTE_LIST_AT_APPEND] THEN
        SUBGOAL_THEN `!w. LENGTH (int64_to_bytes w) = 8` (fun th -> REWRITE_TAC [th]) THENL
        [ REWRITE_TAC [LENGTH; int64_to_bytes] THEN ARITH_TAC; ALL_TAC ] THEN
        ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ARITH] THEN
        ASM_REWRITE_TAC [GSYM INT64_BYTE_LIST] ]);;
