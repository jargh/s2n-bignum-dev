needs "arm/sha512/sha512_specs.ml";;

(*****************************************************************************)

(* ------------------------------------------------------------------------- *)
(* Starting proofs about the machine code.                                   *)
(* ------------------------------------------------------------------------- *)

(*****************************************************************************)

(*
print_literal_relocs_from_elf "arm/sha512/sha512.o";;

save_literal_relocs_from_elf
  "arm/sha512/literal_relocs.txt"
  "arm/sha512/sha512.o";;
*)

let a_mc,a_constants_data = define_assert_relocs_from_elf "a_mc"
    "arm/sha512/sha512.o"
(fun w BL ADR ADRP ADD_rri64 -> [
  (*** msg_schedule ***)
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
  w 0xd503201f;         (* arm_NOP *)
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
  w 0xd503201f;         (* arm_NOP *)
  w 0xd503201f;         (* arm_NOP *)
  w 0xd503201f;         (* arm_NOP *)

  (*** sha512_process_block ***)
  w 0xd10b43ff;         (* arm_SUB SP SP (rvalue (word 720)) *)
  w 0xaa0003ec;         (* arm_MOV X12 X0 *)
  w 0x910143e0;         (* arm_ADD X0 SP (rvalue (word 80)) *)
  w 0xa9007bfd;         (* arm_STP X29 X30 SP (Immediate_Offset (iword (&0))) *)
  w 0x910003fd;         (* arm_ADD X29 SP (rvalue (word 0)) *)
  w 0x97ffffc3;         (* arm_BL (word 268435212) *)
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
  ADRP (mk_var("K",`:num`),0,288,14);
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
  w 0xd503201f;         (* arm_NOP *)
  w 0xd503201f;         (* arm_NOP *)
  w 0xd503201f;         (* arm_NOP *)

  (*** sha512_process_blocks ***)
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
  w 0x97ffff94;         (* arm_BL (word 268435024) *)
  w 0xb100069f;         (* arm_CMN X20 (rvalue (word 1)) *)
  w 0x54ffff41;         (* arm_BNE (word 2097128) *)
  w 0xa94153f3;         (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94013f5;         (* arm_LDR X21 SP (Immediate_Offset (word 32)) *)
  w 0xa8c37bfd;         (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&48))) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd65f03c0;         (* arm_RET X30 *)

  (*** sha512_init ***)
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

  (*** sha512_update ***)
  w 0xa9bd7bfd;         (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &48))) *)
  w 0x910003fd;         (* arm_ADD X29 SP (rvalue (word 0)) *)
  w 0xd37df043;         (* arm_LSL X3 X2 3 *)
  w 0xd37dfc45;         (* arm_LSR X5 X2 61 *)
  w 0xa90153f3;         (* arm_STP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xaa0203f4;         (* arm_MOV X20 X2 *)
  w 0xaa0103f3;         (* arm_MOV X19 X1 *)
  w 0xf90013f5;         (* arm_STR X21 SP (Immediate_Offset (word 32)) *)
  w 0xaa0003f5;         (* arm_MOV X21 X0 *)
  w 0x39434004;         (* arm_LDRB W4 X0 (Immediate_Offset (word 208)) *)
  w 0xf9402000;         (* arm_LDR X0 X0 (Immediate_Offset (word 64)) *)
  w 0xf94026a2;         (* arm_LDR X2 X21 (Immediate_Offset (word 72)) *)
  w 0xab030000;         (* arm_ADDS X0 X0 X3 *)
  w 0x9a050042;         (* arm_ADC X2 X2 X5 *)
  w 0xa9040aa0;         (* arm_STP X0 X2 X21 (Immediate_Offset (iword (&64))) *)
  w 0x340008a4;         (* arm_CBZ W4 (word 276) *)
  w 0x52801003;         (* arm_MOV W3 (rvalue (word 128)) *)
  w 0x910142a1;         (* arm_ADD X1 X21 (rvalue (word 80)) *)
  w 0x4b040063;         (* arm_SUB W3 W3 W4 *)
  w 0x92401c85;         (* arm_AND X5 X4 (rvalue (word 255)) *)
  w 0x93407c63;         (* arm_SBFM X3 X3 0 31 *)
  w 0xeb03029f;         (* arm_CMP X20 X3 *)
  w 0x540016e3;         (* arm_BCC (word 732) *)
  w 0xb40006e3;         (* arm_CBZ X3 (word 220) *)
  w 0x910140a2;         (* arm_ADD X2 X5 (rvalue (word 80)) *)
  w 0x91000660;         (* arm_ADD X0 X19 (rvalue (word 1)) *)
  w 0x8b0202a2;         (* arm_ADD X2 X21 X2 *)
  w 0xd1000466;         (* arm_SUB X6 X3 (rvalue (word 1)) *)
  w 0xcb000040;         (* arm_SUB X0 X2 X0 *)
  w 0xaa020264;         (* arm_ORR X4 X19 X2 *)
  w 0xf100181f;         (* arm_CMP X0 (rvalue (word 6)) *)
  w 0x92400880;         (* arm_AND X0 X4 (rvalue (word 7)) *)
  w 0xfa4688c0;         (* arm_CCMP X6 (rvalue (word 6)) (word 0) Condition_HI *)
  w 0xfa408800;         (* arm_CCMP X0 (rvalue (word 0)) (word 0) Condition_HI *)
  w 0x54001ea1;         (* arm_BNE (word 980) *)
  w 0x927df066;         (* arm_AND X6 X3 (rvalue (word 18446744073709551608)) *)
  w 0xd2800000;         (* arm_MOV X0 (rvalue (word 0)) *)
  w 0xf8606a64;         (* arm_LDR X4 X19 (Register_Offset X0) *)
  w 0xf8206844;         (* arm_STR X4 X2 (Register_Offset X0) *)
  w 0x91002000;         (* arm_ADD X0 X0 (rvalue (word 8)) *)
  w 0xeb0000df;         (* arm_CMP X6 X0 *)
  w 0x54ffff81;         (* arm_BNE (word 2097136) *)
  w 0x927df062;         (* arm_AND X2 X3 (rvalue (word 18446744073709551608)) *)
  w 0xf240087f;         (* arm_TST X3 (rvalue (word 7)) *)
  w 0x54000440;         (* arm_BEQ (word 136) *)
  w 0x38626a66;         (* arm_LDRB W6 X19 (Register_Offset X2) *)
  w 0x8b050020;         (* arm_ADD X0 X1 X5 *)
  w 0x91000444;         (* arm_ADD X4 X2 (rvalue (word 1)) *)
  w 0x38226806;         (* arm_STRB W6 X0 (Register_Offset X2) *)
  w 0xeb04007f;         (* arm_CMP X3 X4 *)
  w 0x54000389;         (* arm_BLS (word 112) *)
  w 0x38646a66;         (* arm_LDRB W6 X19 (Register_Offset X4) *)
  w 0x91000845;         (* arm_ADD X5 X2 (rvalue (word 2)) *)
  w 0x38246806;         (* arm_STRB W6 X0 (Register_Offset X4) *)
  w 0xeb05007f;         (* arm_CMP X3 X5 *)
  w 0x540002e9;         (* arm_BLS (word 92) *)
  w 0x38656a66;         (* arm_LDRB W6 X19 (Register_Offset X5) *)
  w 0x91000c44;         (* arm_ADD X4 X2 (rvalue (word 3)) *)
  w 0x38256806;         (* arm_STRB W6 X0 (Register_Offset X5) *)
  w 0xeb04007f;         (* arm_CMP X3 X4 *)
  w 0x54000249;         (* arm_BLS (word 72) *)
  w 0x38646a66;         (* arm_LDRB W6 X19 (Register_Offset X4) *)
  w 0x91001045;         (* arm_ADD X5 X2 (rvalue (word 4)) *)
  w 0x38246806;         (* arm_STRB W6 X0 (Register_Offset X4) *)
  w 0xeb05007f;         (* arm_CMP X3 X5 *)
  w 0x540001a9;         (* arm_BLS (word 52) *)
  w 0x38656a66;         (* arm_LDRB W6 X19 (Register_Offset X5) *)
  w 0x91001444;         (* arm_ADD X4 X2 (rvalue (word 5)) *)
  w 0x38256806;         (* arm_STRB W6 X0 (Register_Offset X5) *)
  w 0xeb04007f;         (* arm_CMP X3 X4 *)
  w 0x54000109;         (* arm_BLS (word 32) *)
  w 0x38646a65;         (* arm_LDRB W5 X19 (Register_Offset X4) *)
  w 0x91001842;         (* arm_ADD X2 X2 (rvalue (word 6)) *)
  w 0x38246805;         (* arm_STRB W5 X0 (Register_Offset X4) *)
  w 0xeb02007f;         (* arm_CMP X3 X2 *)
  w 0x54000069;         (* arm_BLS (word 12) *)
  w 0x38626a64;         (* arm_LDRB W4 X19 (Register_Offset X2) *)
  w 0x38226804;         (* arm_STRB W4 X0 (Register_Offset X2) *)
  w 0xd2800022;         (* arm_MOV X2 (rvalue (word 1)) *)
  w 0xaa1503e0;         (* arm_MOV X0 X21 *)
  w 0xcb030294;         (* arm_SUB X20 X20 X3 *)
  w 0x8b030273;         (* arm_ADD X19 X19 X3 *)
  w 0x97ffff72;         (* arm_BL (word 268434888) *)
  w 0x390342bf;         (* arm_STRB WZR X21 (Immediate_Offset (word 208)) *)
  w 0xf101fe9f;         (* arm_CMP X20 (rvalue (word 127)) *)
  w 0x54000de8;         (* arm_BHI (word 444) *)
  w 0xb4000d54;         (* arm_CBZ X20 (word 424) *)
  w 0x910142a1;         (* arm_ADD X1 X21 (rvalue (word 80)) *)
  w 0x91000660;         (* arm_ADD X0 X19 (rvalue (word 1)) *)
  w 0xaa010262;         (* arm_ORR X2 X19 X1 *)
  w 0xcb000020;         (* arm_SUB X0 X1 X0 *)
  w 0xf240085f;         (* arm_TST X2 (rvalue (word 7)) *)
  w 0xd1000682;         (* arm_SUB X2 X20 (rvalue (word 1)) *)
  w 0xfa460800;         (* arm_CCMP X0 (rvalue (word 6)) (word 0) Condition_EQ *)
  w 0xfa468840;         (* arm_CCMP X2 (rvalue (word 6)) (word 0) Condition_HI *)
  w 0x54001609;         (* arm_BLS (word 704) *)
  w 0xf9400262;         (* arm_LDR X2 X19 (Immediate_Offset (word 0)) *)
  w 0xd343fe80;         (* arm_LSR X0 X20 3 *)
  w 0xf9002aa2;         (* arm_STR X2 X21 (Immediate_Offset (word 80)) *)
  w 0xf100041f;         (* arm_CMP X0 (rvalue (word 1)) *)
  w 0x54000700;         (* arm_BEQ (word 224) *)
  w 0xf9400662;         (* arm_LDR X2 X19 (Immediate_Offset (word 8)) *)
  w 0xf9002ea2;         (* arm_STR X2 X21 (Immediate_Offset (word 88)) *)
  w 0xf100081f;         (* arm_CMP X0 (rvalue (word 2)) *)
  w 0x54000680;         (* arm_BEQ (word 208) *)
  w 0xf9400a62;         (* arm_LDR X2 X19 (Immediate_Offset (word 16)) *)
  w 0xf90032a2;         (* arm_STR X2 X21 (Immediate_Offset (word 96)) *)
  w 0xf1000c1f;         (* arm_CMP X0 (rvalue (word 3)) *)
  w 0x54000600;         (* arm_BEQ (word 192) *)
  w 0xf9400e62;         (* arm_LDR X2 X19 (Immediate_Offset (word 24)) *)
  w 0xf90036a2;         (* arm_STR X2 X21 (Immediate_Offset (word 104)) *)
  w 0xf100101f;         (* arm_CMP X0 (rvalue (word 4)) *)
  w 0x54000580;         (* arm_BEQ (word 176) *)
  w 0xf9401262;         (* arm_LDR X2 X19 (Immediate_Offset (word 32)) *)
  w 0xf9003aa2;         (* arm_STR X2 X21 (Immediate_Offset (word 112)) *)
  w 0xf100141f;         (* arm_CMP X0 (rvalue (word 5)) *)
  w 0x54000500;         (* arm_BEQ (word 160) *)
  w 0xf9401662;         (* arm_LDR X2 X19 (Immediate_Offset (word 40)) *)
  w 0xf9003ea2;         (* arm_STR X2 X21 (Immediate_Offset (word 120)) *)
  w 0xf100181f;         (* arm_CMP X0 (rvalue (word 6)) *)
  w 0x54000480;         (* arm_BEQ (word 144) *)
  w 0xf9401a62;         (* arm_LDR X2 X19 (Immediate_Offset (word 48)) *)
  w 0xf90042a2;         (* arm_STR X2 X21 (Immediate_Offset (word 128)) *)
  w 0xf1001c1f;         (* arm_CMP X0 (rvalue (word 7)) *)
  w 0x54000400;         (* arm_BEQ (word 128) *)
  w 0xf9401e62;         (* arm_LDR X2 X19 (Immediate_Offset (word 56)) *)
  w 0xf90046a2;         (* arm_STR X2 X21 (Immediate_Offset (word 136)) *)
  w 0xf100201f;         (* arm_CMP X0 (rvalue (word 8)) *)
  w 0x54000380;         (* arm_BEQ (word 112) *)
  w 0xf9402262;         (* arm_LDR X2 X19 (Immediate_Offset (word 64)) *)
  w 0xf9004aa2;         (* arm_STR X2 X21 (Immediate_Offset (word 144)) *)
  w 0xf100241f;         (* arm_CMP X0 (rvalue (word 9)) *)
  w 0x54000300;         (* arm_BEQ (word 96) *)
  w 0xf9402662;         (* arm_LDR X2 X19 (Immediate_Offset (word 72)) *)
  w 0xf9004ea2;         (* arm_STR X2 X21 (Immediate_Offset (word 152)) *)
  w 0xf100281f;         (* arm_CMP X0 (rvalue (word 10)) *)
  w 0x54000280;         (* arm_BEQ (word 80) *)
  w 0xf9402a62;         (* arm_LDR X2 X19 (Immediate_Offset (word 80)) *)
  w 0xf90052a2;         (* arm_STR X2 X21 (Immediate_Offset (word 160)) *)
  w 0xf1002c1f;         (* arm_CMP X0 (rvalue (word 11)) *)
  w 0x54000200;         (* arm_BEQ (word 64) *)
  w 0xf9402e62;         (* arm_LDR X2 X19 (Immediate_Offset (word 88)) *)
  w 0xf90056a2;         (* arm_STR X2 X21 (Immediate_Offset (word 168)) *)
  w 0xf100301f;         (* arm_CMP X0 (rvalue (word 12)) *)
  w 0x54000180;         (* arm_BEQ (word 48) *)
  w 0xf9403262;         (* arm_LDR X2 X19 (Immediate_Offset (word 96)) *)
  w 0xf9005aa2;         (* arm_STR X2 X21 (Immediate_Offset (word 176)) *)
  w 0xf100341f;         (* arm_CMP X0 (rvalue (word 13)) *)
  w 0x54000100;         (* arm_BEQ (word 32) *)
  w 0xf9403662;         (* arm_LDR X2 X19 (Immediate_Offset (word 104)) *)
  w 0xf9005ea2;         (* arm_STR X2 X21 (Immediate_Offset (word 184)) *)
  w 0xf1003c1f;         (* arm_CMP X0 (rvalue (word 15)) *)
  w 0x54000081;         (* arm_BNE (word 16) *)
  w 0xf9403a60;         (* arm_LDR X0 X19 (Immediate_Offset (word 112)) *)
  w 0xf90062a0;         (* arm_STR X0 X21 (Immediate_Offset (word 192)) *)
  w 0xd503201f;         (* arm_NOP *)
  w 0x927df280;         (* arm_AND X0 X20 (rvalue (word 18446744073709551608)) *)
  w 0xf2400a9f;         (* arm_TST X20 (rvalue (word 7)) *)
  w 0x54000420;         (* arm_BEQ (word 132) *)
  w 0x38606a63;         (* arm_LDRB W3 X19 (Register_Offset X0) *)
  w 0x91000402;         (* arm_ADD X2 X0 (rvalue (word 1)) *)
  w 0x38206823;         (* arm_STRB W3 X1 (Register_Offset X0) *)
  w 0xeb02029f;         (* arm_CMP X20 X2 *)
  w 0x54000389;         (* arm_BLS (word 112) *)
  w 0x38626a64;         (* arm_LDRB W4 X19 (Register_Offset X2) *)
  w 0x91000803;         (* arm_ADD X3 X0 (rvalue (word 2)) *)
  w 0x38226824;         (* arm_STRB W4 X1 (Register_Offset X2) *)
  w 0xeb03029f;         (* arm_CMP X20 X3 *)
  w 0x540002e9;         (* arm_BLS (word 92) *)
  w 0x38636a64;         (* arm_LDRB W4 X19 (Register_Offset X3) *)
  w 0x91000c02;         (* arm_ADD X2 X0 (rvalue (word 3)) *)
  w 0x38236824;         (* arm_STRB W4 X1 (Register_Offset X3) *)
  w 0xeb02029f;         (* arm_CMP X20 X2 *)
  w 0x54000249;         (* arm_BLS (word 72) *)
  w 0x38626a64;         (* arm_LDRB W4 X19 (Register_Offset X2) *)
  w 0x91001003;         (* arm_ADD X3 X0 (rvalue (word 4)) *)
  w 0x38226824;         (* arm_STRB W4 X1 (Register_Offset X2) *)
  w 0xeb03029f;         (* arm_CMP X20 X3 *)
  w 0x540001a9;         (* arm_BLS (word 52) *)
  w 0x38636a64;         (* arm_LDRB W4 X19 (Register_Offset X3) *)
  w 0x91001402;         (* arm_ADD X2 X0 (rvalue (word 5)) *)
  w 0x38236824;         (* arm_STRB W4 X1 (Register_Offset X3) *)
  w 0xeb02029f;         (* arm_CMP X20 X2 *)
  w 0x54000109;         (* arm_BLS (word 32) *)
  w 0x38626a63;         (* arm_LDRB W3 X19 (Register_Offset X2) *)
  w 0x91001800;         (* arm_ADD X0 X0 (rvalue (word 6)) *)
  w 0x38226823;         (* arm_STRB W3 X1 (Register_Offset X2) *)
  w 0xeb00029f;         (* arm_CMP X20 X0 *)
  w 0x54000069;         (* arm_BLS (word 12) *)
  w 0x38606a62;         (* arm_LDRB W2 X19 (Register_Offset X0) *)
  w 0x38206822;         (* arm_STRB W2 X1 (Register_Offset X0) *)
  w 0x390342b4;         (* arm_STRB W20 X21 (Immediate_Offset (word 208)) *)
  w 0xa94153f3;         (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94013f5;         (* arm_LDR X21 SP (Immediate_Offset (word 32)) *)
  w 0xa8c37bfd;         (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&48))) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd347fe82;         (* arm_LSR X2 X20 7 *)
  w 0xaa1303e1;         (* arm_MOV X1 X19 *)
  w 0xaa1503e0;         (* arm_MOV X0 X21 *)
  w 0x97fffefd;         (* arm_BL (word 268434420) *)
  w 0x9279e280;         (* arm_AND X0 X20 (rvalue (word 18446744073709551488)) *)
  w 0x92401a94;         (* arm_AND X20 X20 (rvalue (word 127)) *)
  w 0x8b000273;         (* arm_ADD X19 X19 X0 *)
  w 0xb4fffeb4;         (* arm_CBZ X20 (word 2097108) *)
  w 0x17ffff8b;         (* arm_B (word 268434988) *)
  w 0xb4000794;         (* arm_CBZ X20 (word 240) *)
  w 0x910140a2;         (* arm_ADD X2 X5 (rvalue (word 80)) *)
  w 0x91000660;         (* arm_ADD X0 X19 (rvalue (word 1)) *)
  w 0x8b0202a2;         (* arm_ADD X2 X21 X2 *)
  w 0xd1000684;         (* arm_SUB X4 X20 (rvalue (word 1)) *)
  w 0xcb000040;         (* arm_SUB X0 X2 X0 *)
  w 0xaa020263;         (* arm_ORR X3 X19 X2 *)
  w 0xf100181f;         (* arm_CMP X0 (rvalue (word 6)) *)
  w 0x92400860;         (* arm_AND X0 X3 (rvalue (word 7)) *)
  w 0xfa468880;         (* arm_CCMP X4 (rvalue (word 6)) (word 0) Condition_HI *)
  w 0xfa408800;         (* arm_CCMP X0 (rvalue (word 0)) (word 0) Condition_HI *)
  w 0x540008c1;         (* arm_BNE (word 280) *)
  w 0x927df284;         (* arm_AND X4 X20 (rvalue (word 18446744073709551608)) *)
  w 0xd2800000;         (* arm_MOV X0 (rvalue (word 0)) *)
  w 0xd503201f;         (* arm_NOP *)
  w 0xf8606a63;         (* arm_LDR X3 X19 (Register_Offset X0) *)
  w 0xf8206843;         (* arm_STR X3 X2 (Register_Offset X0) *)
  w 0x91002000;         (* arm_ADD X0 X0 (rvalue (word 8)) *)
  w 0xeb00009f;         (* arm_CMP X4 X0 *)
  w 0x54ffff81;         (* arm_BNE (word 2097136) *)
  w 0x927df280;         (* arm_AND X0 X20 (rvalue (word 18446744073709551608)) *)
  w 0xf2400a9f;         (* arm_TST X20 (rvalue (word 7)) *)
  w 0x540004a0;         (* arm_BEQ (word 148) *)
  w 0x38606a63;         (* arm_LDRB W3 X19 (Register_Offset X0) *)
  w 0x8b050024;         (* arm_ADD X4 X1 X5 *)
  w 0x91000402;         (* arm_ADD X2 X0 (rvalue (word 1)) *)
  w 0x38206883;         (* arm_STRB W3 X4 (Register_Offset X0) *)
  w 0xeb02029f;         (* arm_CMP X20 X2 *)
  w 0x540003e9;         (* arm_BLS (word 124) *)
  w 0x38626a66;         (* arm_LDRB W6 X19 (Register_Offset X2) *)
  w 0x8b020022;         (* arm_ADD X2 X1 X2 *)
  w 0x91000803;         (* arm_ADD X3 X0 (rvalue (word 2)) *)
  w 0x38256846;         (* arm_STRB W6 X2 (Register_Offset X5) *)
  w 0xeb03029f;         (* arm_CMP X20 X3 *)
  w 0x54000329;         (* arm_BLS (word 100) *)
  w 0x38636a66;         (* arm_LDRB W6 X19 (Register_Offset X3) *)
  w 0x8b030023;         (* arm_ADD X3 X1 X3 *)
  w 0x91000c02;         (* arm_ADD X2 X0 (rvalue (word 3)) *)
  w 0x38256866;         (* arm_STRB W6 X3 (Register_Offset X5) *)
  w 0xeb02029f;         (* arm_CMP X20 X2 *)
  w 0x54000269;         (* arm_BLS (word 76) *)
  w 0x38626a63;         (* arm_LDRB W3 X19 (Register_Offset X2) *)
  w 0x8b020022;         (* arm_ADD X2 X1 X2 *)
  w 0x91001001;         (* arm_ADD X1 X0 (rvalue (word 4)) *)
  w 0x38256843;         (* arm_STRB W3 X2 (Register_Offset X5) *)
  w 0xeb01029f;         (* arm_CMP X20 X1 *)
  w 0x540001a9;         (* arm_BLS (word 52) *)
  w 0x38616a63;         (* arm_LDRB W3 X19 (Register_Offset X1) *)
  w 0x91001402;         (* arm_ADD X2 X0 (rvalue (word 5)) *)
  w 0x38216883;         (* arm_STRB W3 X4 (Register_Offset X1) *)
  w 0xeb02029f;         (* arm_CMP X20 X2 *)
  w 0x54000109;         (* arm_BLS (word 32) *)
  w 0x38626a61;         (* arm_LDRB W1 X19 (Register_Offset X2) *)
  w 0x91001800;         (* arm_ADD X0 X0 (rvalue (word 6)) *)
  w 0x38226881;         (* arm_STRB W1 X4 (Register_Offset X2) *)
  w 0xeb00029f;         (* arm_CMP X20 X0 *)
  w 0x54000069;         (* arm_BLS (word 12) *)
  w 0x38606a61;         (* arm_LDRB W1 X19 (Register_Offset X0) *)
  w 0x38206881;         (* arm_STRB W1 X4 (Register_Offset X0) *)
  w 0x394342a4;         (* arm_LDRB W4 X21 (Immediate_Offset (word 208)) *)
  w 0x0b140084;         (* arm_ADD W4 W4 W20 *)
  w 0x390342a4;         (* arm_STRB W4 X21 (Immediate_Offset (word 208)) *)
  w 0xa94153f3;         (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94013f5;         (* arm_LDR X21 SP (Immediate_Offset (word 32)) *)
  w 0xa8c37bfd;         (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&48))) *)
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0xd2800000;         (* arm_MOV X0 (rvalue (word 0)) *)
  w 0x38606a62;         (* arm_LDRB W2 X19 (Register_Offset X0) *)
  w 0x38206822;         (* arm_STRB W2 X1 (Register_Offset X0) *)
  w 0x91000400;         (* arm_ADD X0 X0 (rvalue (word 1)) *)
  w 0xeb00029f;         (* arm_CMP X20 X0 *)
  w 0x54ffff81;         (* arm_BNE (word 2097136) *)
  w 0x390342b4;         (* arm_STRB W20 X21 (Immediate_Offset (word 208)) *)
  w 0x17ffffaa;         (* arm_B (word 268435112) *)
  w 0xd2800000;         (* arm_MOV X0 (rvalue (word 0)) *)
  w 0x38606a64;         (* arm_LDRB W4 X19 (Register_Offset X0) *)
  w 0x38206844;         (* arm_STRB W4 X2 (Register_Offset X0) *)
  w 0x91000400;         (* arm_ADD X0 X0 (rvalue (word 1)) *)
  w 0xeb00007f;         (* arm_CMP X3 X0 *)
  w 0x54ffff81;         (* arm_BNE (word 2097136) *)
  w 0x17ffff31;         (* arm_B (word 268434628) *)
  w 0xd2800000;         (* arm_MOV X0 (rvalue (word 0)) *)
  w 0x38606a61;         (* arm_LDRB W1 X19 (Register_Offset X0) *)
  w 0x38206841;         (* arm_STRB W1 X2 (Register_Offset X0) *)
  w 0x91000400;         (* arm_ADD X0 X0 (rvalue (word 1)) *)
  w 0xeb00029f;         (* arm_CMP X20 X0 *)
  w 0x54ffff81;         (* arm_BNE (word 2097136) *)
  w 0x17ffffe4;         (* arm_B (word 268435344) *)

  (*** sha512_final ***)
  w 0xa9bd7bfd;         (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &48))) *)
  w 0x910003fd;         (* arm_ADD X29 SP (rvalue (word 0)) *)
  w 0x12800fe3;         (* arm_MOVN W3 (word 127) 0 *)
  w 0xa90153f3;         (* arm_STP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  w 0xaa0003f4;         (* arm_MOV X20 X0 *)
  w 0xaa0103f3;         (* arm_MOV X19 X1 *)
  w 0xf90013f5;         (* arm_STR X21 SP (Immediate_Offset (word 32)) *)
  w 0x91014275;         (* arm_ADD X21 X19 (rvalue (word 80)) *)
  w 0x39434022;         (* arm_LDRB W2 X1 (Immediate_Offset (word 208)) *)
  w 0x8b22c021;         (* arm_ADD X1 X1 (Extendedreg W2 SXTW) *)
  w 0x39014023;         (* arm_STRB W3 X1 (Immediate_Offset (word 80)) *)
  w 0x11000440;         (* arm_ADD W0 W2 (rvalue (word 1)) *)
  w 0x12001c00;         (* arm_AND W0 W0 (rvalue (word 255)) *)
  w 0x92401c02;         (* arm_AND X2 X0 (rvalue (word 255)) *)
  w 0x39034260;         (* arm_STRB W0 X19 (Immediate_Offset (word 208)) *)
  w 0x7101c01f;         (* arm_CMP W0 (rvalue (word 112)) *)
  w 0x54001129;         (* arm_BLS (word 548) *)
  w 0x52801001;         (* arm_MOV W1 (rvalue (word 128)) *)
  w 0x4b000020;         (* arm_SUB W0 W1 W0 *)
  w 0x93407c04;         (* arm_SBFM X4 X0 0 31 *)
  w 0x340005e0;         (* arm_CBZ W0 (word 188) *)
  w 0x91014040;         (* arm_ADD X0 X2 (rvalue (word 80)) *)
  w 0xd1000483;         (* arm_SUB X3 X4 (rvalue (word 1)) *)
  w 0x8b000265;         (* arm_ADD X5 X19 X0 *)
  w 0xcb0503e1;         (* arm_NEG X1 X5 *)
  w 0x92400821;         (* arm_AND X1 X1 (rvalue (word 7)) *)
  w 0xf100447f;         (* arm_CMP X3 (rvalue (word 17)) *)
  w 0x54001269;         (* arm_BLS (word 588) *)
  w 0xb4001201;         (* arm_CBZ X1 (word 576) *)
  w 0x38226abf;         (* arm_STRB WZR X21 (Register_Offset X2) *)
  w 0xf100043f;         (* arm_CMP X1 (rvalue (word 1)) *)
  w 0x54001120;         (* arm_BEQ (word 548) *)
  w 0x8b0202a3;         (* arm_ADD X3 X21 X2 *)
  w 0x3900047f;         (* arm_STRB WZR X3 (Immediate_Offset (word 1)) *)
  w 0xf100083f;         (* arm_CMP X1 (rvalue (word 2)) *)
  w 0x540010a0;         (* arm_BEQ (word 532) *)
  w 0x3900087f;         (* arm_STRB WZR X3 (Immediate_Offset (word 2)) *)
  w 0xf1000c3f;         (* arm_CMP X1 (rvalue (word 3)) *)
  w 0x54001040;         (* arm_BEQ (word 520) *)
  w 0x39000c7f;         (* arm_STRB WZR X3 (Immediate_Offset (word 3)) *)
  w 0xf100103f;         (* arm_CMP X1 (rvalue (word 4)) *)
  w 0x54000fe0;         (* arm_BEQ (word 508) *)
  w 0x3900107f;         (* arm_STRB WZR X3 (Immediate_Offset (word 4)) *)
  w 0xf100143f;         (* arm_CMP X1 (rvalue (word 5)) *)
  w 0x54000f80;         (* arm_BEQ (word 496) *)
  w 0x3900147f;         (* arm_STRB WZR X3 (Immediate_Offset (word 5)) *)
  w 0xf1001c3f;         (* arm_CMP X1 (rvalue (word 7)) *)
  w 0x54001061;         (* arm_BNE (word 524) *)
  w 0xd28000e2;         (* arm_MOV X2 (rvalue (word 7)) *)
  w 0x3900187f;         (* arm_STRB WZR X3 (Immediate_Offset (word 6)) *)
  w 0x8b010000;         (* arm_ADD X0 X0 X1 *)
  w 0xcb010081;         (* arm_SUB X1 X4 X1 *)
  w 0x8b000260;         (* arm_ADD X0 X19 X0 *)
  w 0x927df023;         (* arm_AND X3 X1 (rvalue (word 18446744073709551608)) *)
  w 0x8b000063;         (* arm_ADD X3 X3 X0 *)
  w 0xf800841f;         (* arm_STR XZR X0 (Postimmediate_Offset (word 8)) *)
  w 0xeb00007f;         (* arm_CMP X3 X0 *)
  w 0x54ffffc1;         (* arm_BNE (word 2097144) *)
  w 0x927df020;         (* arm_AND X0 X1 (rvalue (word 18446744073709551608)) *)
  w 0x8b000042;         (* arm_ADD X2 X2 X0 *)
  w 0xeb00003f;         (* arm_CMP X1 X0 *)
  w 0x540000c0;         (* arm_BEQ (word 24) *)
  w 0xd503201f;         (* arm_NOP *)
  w 0x382268bf;         (* arm_STRB WZR X5 (Register_Offset X2) *)
  w 0x91000442;         (* arm_ADD X2 X2 (rvalue (word 1)) *)
  w 0xeb02009f;         (* arm_CMP X4 X2 *)
  w 0x54ffffa8;         (* arm_BHI (word 2097140) *)
  w 0xaa1503e1;         (* arm_MOV X1 X21 *)
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0x97fffdfa;         (* arm_BL (word 268433384) *)
  w 0xcb1503e0;         (* arm_NEG X0 X21 *)
  w 0xd2800e01;         (* arm_MOV X1 (rvalue (word 112)) *)
  w 0x3903427f;         (* arm_STRB WZR X19 (Immediate_Offset (word 208)) *)
  w 0x92400800;         (* arm_AND X0 X0 (rvalue (word 7)) *)
  w 0xaa0103e4;         (* arm_MOV X4 X1 *)
  w 0xaa1503e6;         (* arm_MOV X6 X21 *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0xd2800a03;         (* arm_MOV X3 (rvalue (word 80)) *)
  w 0xb4000b80;         (* arm_CBZ X0 (word 368) *)
  w 0x38226abf;         (* arm_STRB WZR X21 (Register_Offset X2) *)
  w 0xf100041f;         (* arm_CMP X0 (rvalue (word 1)) *)
  w 0x54000aa0;         (* arm_BEQ (word 340) *)
  w 0x8b0202a5;         (* arm_ADD X5 X21 X2 *)
  w 0x390004bf;         (* arm_STRB WZR X5 (Immediate_Offset (word 1)) *)
  w 0xf100081f;         (* arm_CMP X0 (rvalue (word 2)) *)
  w 0x54000a20;         (* arm_BEQ (word 324) *)
  w 0x390008bf;         (* arm_STRB WZR X5 (Immediate_Offset (word 2)) *)
  w 0xf1000c1f;         (* arm_CMP X0 (rvalue (word 3)) *)
  w 0x540009c0;         (* arm_BEQ (word 312) *)
  w 0x39000cbf;         (* arm_STRB WZR X5 (Immediate_Offset (word 3)) *)
  w 0xf100101f;         (* arm_CMP X0 (rvalue (word 4)) *)
  w 0x54000960;         (* arm_BEQ (word 300) *)
  w 0x390010bf;         (* arm_STRB WZR X5 (Immediate_Offset (word 4)) *)
  w 0xf100141f;         (* arm_CMP X0 (rvalue (word 5)) *)
  w 0x54000900;         (* arm_BEQ (word 288) *)
  w 0x390014bf;         (* arm_STRB WZR X5 (Immediate_Offset (word 5)) *)
  w 0xf1001c1f;         (* arm_CMP X0 (rvalue (word 7)) *)
  w 0x540009e1;         (* arm_BNE (word 316) *)
  w 0xaa0003e2;         (* arm_MOV X2 X0 *)
  w 0x390018bf;         (* arm_STRB WZR X5 (Immediate_Offset (word 6)) *)
  w 0x8b000063;         (* arm_ADD X3 X3 X0 *)
  w 0xcb000021;         (* arm_SUB X1 X1 X0 *)
  w 0x8b030263;         (* arm_ADD X3 X19 X3 *)
  w 0x927df020;         (* arm_AND X0 X1 (rvalue (word 18446744073709551608)) *)
  w 0x8b030000;         (* arm_ADD X0 X0 X3 *)
  w 0xf800847f;         (* arm_STR XZR X3 (Postimmediate_Offset (word 8)) *)
  w 0xeb00007f;         (* arm_CMP X3 X0 *)
  w 0x54ffffc1;         (* arm_BNE (word 2097144) *)
  w 0x927df020;         (* arm_AND X0 X1 (rvalue (word 18446744073709551608)) *)
  w 0x8b000042;         (* arm_ADD X2 X2 X0 *)
  w 0xeb00003f;         (* arm_CMP X1 X0 *)
  w 0x540000a0;         (* arm_BEQ (word 20) *)
  w 0x382268df;         (* arm_STRB WZR X6 (Register_Offset X2) *)
  w 0x91000442;         (* arm_ADD X2 X2 (rvalue (word 1)) *)
  w 0xeb04005f;         (* arm_CMP X2 X4 *)
  w 0x54ffffa3;         (* arm_BCC (word 2097140) *)
  w 0xf9402660;         (* arm_LDR X0 X19 (Immediate_Offset (word 72)) *)
  w 0xaa1503e1;         (* arm_MOV X1 X21 *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9006260;         (* arm_STR X0 X19 (Immediate_Offset (word 192)) *)
  w 0xf9402260;         (* arm_LDR X0 X19 (Immediate_Offset (word 64)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9006660;         (* arm_STR X0 X19 (Immediate_Offset (word 200)) *)
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0x97fffdc3;         (* arm_BL (word 268433164) *)
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
  w 0xd65f03c0;         (* arm_RET X30 *)
  w 0x52800e01;         (* arm_MOV W1 (rvalue (word 112)) *)
  w 0x4b000020;         (* arm_SUB W0 W1 W0 *)
  w 0x93407c04;         (* arm_SBFM X4 X0 0 31 *)
  w 0x34fffb00;         (* arm_CBZ W0 (word 2096992) *)
  w 0x91014043;         (* arm_ADD X3 X2 (rvalue (word 80)) *)
  w 0xaa0403e1;         (* arm_MOV X1 X4 *)
  w 0x8b030266;         (* arm_ADD X6 X19 X3 *)
  w 0xcb0603e0;         (* arm_NEG X0 X6 *)
  w 0x92400800;         (* arm_AND X0 X0 (rvalue (word 7)) *)
  w 0xf100489f;         (* arm_CMP X4 (rvalue (word 18)) *)
  w 0x54fff568;         (* arm_BHI (word 2096812) *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0x17ffffcb;         (* arm_B (word 268435244) *)
  w 0xaa0003e2;         (* arm_MOV X2 X0 *)
  w 0x17ffffbd;         (* arm_B (word 268435188) *)
  w 0xaa0103e2;         (* arm_MOV X2 X1 *)
  w 0x17ffff89;         (* arm_B (word 268434980) *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0x17ffffb9;         (* arm_B (word 268435172) *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0x17ffff85;         (* arm_B (word 268434964) *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0x17ffff90;         (* arm_B (word 268435008) *)
  w 0xd28000c2;         (* arm_MOV X2 (rvalue (word 6)) *)
  w 0x17ffffb3;         (* arm_B (word 268435148) *)
  w 0xd28000c2;         (* arm_MOV X2 (rvalue (word 6)) *)
  w 0x17ffff7f          (* arm_B (word 268434940) *)
]);;

let EXEC = ARM_MK_EXEC_RULE a_mc;;

(* void sha512_init(sha512_ctx *sha) *)
let SHA512_INIT = prove(`! ctx_p pc retpc K_base.
  nonoverlapping (word pc : int64, 2748) (ctx_p, 216) ==>
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K_base) /\
         read PC s = word (pc + 0x2b0) /\
         read X30 s = word retpc /\
         read X0 s = ctx_p)
    (\s. read PC s = word retpc /\
         sha512_ctx_at [] ctx_p s)
    (MAYCHANGE [X1; X2; X3; X4; X5; X6; X7; PC] ,,
     MAYCHANGE [memory :> bytes(ctx_p, 216)] ,, MAYCHANGE [events])`,
  REWRITE_TAC [NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
    ARM_SIM_TAC EXEC (173--212) THEN
    ASM_REWRITE_TAC [sha512_ctx_at; sha512_ctx_from; hash_buffer_at; h_init; h_a; h_b; h_c; h_d; h_e; h_f; h_g; h_h;
                     sha512; sha512'; bytes_to_blocks; num_bytes_per_block; bytes_mod_blocks; take; drop;
                     LENGTH; VAL_WORD_0; MULT; DIV_0; SUB_LIST_CLAUSES; ARITH] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[LENGTH; SUB_LIST_CLAUSES; MOD_0]);;

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let FORALL_LT_SUC = prove
 (`!P n. (!i. i < n + 1 ==> P i) <=> (!i. i < n ==> P i) /\ P n`,
  REWRITE_TAC[GSYM ADD1] THEN MESON_TAC[LT]);;

(* void msg_schedule(uint64_t schedule[80], const uint8_t *in_data) *)
let MSG_SCHEDULE = prove(`! sch_p m_p m pc retpc K_base.
  PAIRWISE nonoverlapping
    [(word pc : int64, 2748); (sch_p, 640); (m_p, num_bytes_per_block)] ==>
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K_base) /\
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
        (! j. j < i ==> read (memory :> bytes64(word_add sch_p (word (8 * j)))) s = msg_schedule m j)` THEN
  REPEAT CONJ_TAC THENL
  [ (* Subgoal 1: upper bound of counter is non-zero *)
    ARITH_TAC;
    (* Subgoal 2: initialization *)
    REWRITE_TAC [msg_block_at] THEN
      CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      ARM_SIM_TAC EXEC [1] THEN ASM_REWRITE_TAC [LT];
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
      ARM_STEPS_TAC EXEC (2--22) THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
      CONJ_TAC THENL [CHEAT_TAC; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC[msg_schedule] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST;
    (* Subgoal 4: backedge *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[msg_block_at] THEN
      CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN
      VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC EXEC (1--2) THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      ASM_SIMP_TAC[LT_IMP_NE] THEN
      CHEAT_TAC; ALL_TAC] THEN
  (* After the first loop *)
  ENSURES_WHILE_AUP_TAC
    `16` `80` `pc + 0x80` `pc + 0xc8`
    `\k s. // loop invariant
        (read X30 s = word retpc /\ read X2 s = word_add sch_p (word (8 * (k - 15))) /\
        read X11 s = word_add sch_p (word (8 * 65)) /\
        read X0 s = msg_schedule m (k - 1) /\ read X3 s = msg_schedule m (k - 2) /\ read X4 s = msg_schedule m (k - 16) /\
        read X6 s = msg_schedule m (k - 3)/\ read X7 s = msg_schedule m (k - 4) /\ read X8 s = msg_schedule m (k - 5)/\
        read X9 s = msg_schedule m (k - 6) /\ read X10 s = msg_schedule m (k - 7) /\
        (! j. j < k ==> read (memory :> bytes64(word_add sch_p (word (8 * j)))) s = msg_schedule m j))` THEN
  REPEAT CONJ_TAC THENL
  [ (* Subgoal 1: upper bound of counter is non-zero *)
    ARITH_TAC;
    (* Subgoal 2: initialization *)
    ENSURES_INIT_TAC "s22" THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE [WORD_ADD_0]) THEN
      ARM_STEPS_TAC EXEC (23--32) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC [] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC [WORD_ADD_0];
    (* Subgoal 3: loop body *)
    REPEAT STRIP_TAC THEN
      ENSURES_INIT_TAC "s32" THEN
      FIRST_ASSUM(fun th -> 
        MAP_EVERY (MP_TAC o C SPEC th) [`i - 2`; `i - 7`; `i - 15`; `i - 16`]) THEN
      REPEAT(ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC]) THEN
      ARM_STEPS_TAC EXEC (33--50) THEN
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
      ASM_REWRITE_TAC [FORALL_LT_SUC] THEN CONJ_TAC THENL [CHEAT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `8 * i = 8 * (i - 15) + 120` SUBST1_TAC THENL [SIMPLE_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      GEN_REWRITE_TAC RAND_CONV [msg_schedule] THEN
      ASM_REWRITE_TAC[GSYM NOT_LE] THEN
      REWRITE_TAC [msg_schedule_word; sigma0_DEF; sigma1_DEF] THEN
      CONV_TAC WORD_BLAST;
    (* Subgoal 4: backedge *)
    REPEAT STRIP_TAC THEN
      ARM_SIM_TAC EXEC (1--2) THEN
      CONJ_TAC THENL [ALL_TAC; CHEAT_TAC] THEN
      REWRITE_TAC [VAL_EQ] THEN
      REWRITE_TAC[WORD_RULE `word_add x y = word_add x z <=> y = z`] THEN
      REWRITE_TAC [GSYM VAL_EQ] THEN
      VAL_INT64_TAC `8 * (i - 15)` THEN
      ASM_REWRITE_TAC [] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 80 ==> ~(520 = 8 * (i - 15))`];
    ALL_TAC ] THEN
  (* After the second loop *)
  ARM_SIM_TAC EXEC (51--53) THEN
  CHEAT_TAC);;

let EXPAND_HASH_THM = prove(
  `! h0 h1 h2 h3 h4 h5 h6 h7 h.
    (h0, h1, h2, h3, h4, h5, h6, h7) = h <=>
      h0 = SHA512_A h /\ h1 = SHA512_B h /\
      h2 = SHA512_C h /\ h3 = SHA512_D h /\
      h4 = SHA512_E h /\ h5 = SHA512_F h /\
      h6 = SHA512_G h /\ h7 = SHA512_H h`,
  REWRITE_TAC [FORALL_PAIR_THM; PAIR_EQ; SHA512_A; SHA512_B; SHA512_C;
    SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H]);;

let RENAME_TAC old_name new_name =
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(old_name, new_name) THEN 
  STRIP_TAC THEN STRIP_TAC;;

let COMPRESSION_STEP_AUX = prove(`! r i j h m.
  i + r = j /\ i <= j ==>
    compression_until (j + 1) i h m
      = compression_update
          (compression_until j i h m)
          (K j)
          (msg_schedule m j)`,
  INDUCT_TAC THENL
  [ (* Base case *)
    REWRITE_TAC[ADD_CLAUSES] THEN
      REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [compression_until] THEN
      ASM_REWRITE_TAC[ARITH_RULE `j < j + 1`] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ONCE_REWRITE_TAC [compression_until] THEN
      REWRITE_TAC[LT_REFL];
    (* Inductive case *)
    REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [compression_until] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ARITH_RULE `i + SUC r = (i + 1) + r`]) THEN
      MP_TAC (ARITH_RULE `(i + 1) + r = j ==> i < j + 1 /\ i < j`) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`i + 1`; `j : num`; `compression_update h (K i) (msg_schedule m i)`; `m : num -> int64`]) THEN
      SUBGOAL_THEN `i + 1 <= j` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] ]);;

let COMPRESSION_STEP = prove(`! i j h m.
  i <= j ==>
    compression_until (j + 1) i h m
      = compression_update
        (compression_until j i h m)
        (K j)
        (msg_schedule m j)`,
  REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`j - i`; `i:num`; `j:num`;
             `h:hash_t`; `m:num->int64`] COMPRESSION_STEP_AUX) THEN
    IMP_REWRITE_TAC [ARITH_RULE `i <= j ==> i+j-i=j`]);;

let WORD_ADD1_SHL3_SUB8 = prove
 (`(b + word_shl (word (i + 1)) 3) + word 18446744073709551608:int64 =
   b + word (8 * i)`,
  REWRITE_TAC[WORD_RULE
   `(b + word_shl (word (i + 1)) 3) + x =  b + word(8 * i) + (x + word 8)`] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC WORD_RULE);;

(* void sha512_process_block(uint64_t h[8], const uint8_t *in_data) *)
let SHA512_PROCESS_BLOCK = prove(`! sp h_p h m_p m pc retpc K_base.
  aligned 16 sp /\
  adrp_within_bounds (word K_base) (word (pc + 0x120)) /\
  PAIRWISE nonoverlapping
    [(word pc : int64, 2748); (h_p, 64);
     (m_p, num_bytes_per_block); (word_sub sp (word 720), 720);
     (word K_base, 640)] ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K_base) /\
         read PC s = word (pc + 0xe0) /\
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
    `79` `pc + 0x158` `pc + 0x158`
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
      ENSURES_INIT_TAC "s56" THEN
      (* ??? Once the bounding machinary is ready, should be able to avoid the expansion and make stepping faster *)
      RULE_ASSUM_TAC (REWRITE_RULE [constants_at]) THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
      ARM_STEPS_TAC EXEC (57--62) THEN
      ARM_SUBROUTINE_SIM_TAC
        (SPEC_ALL a_mc, EXEC, 0, SPEC_ALL a_mc, REWRITE_RULE [num_bytes_per_block; msg_block_at] MSG_SCHEDULE)
        [`sp + word 80 : int64 `;`m_p : int64`;`m : num -> int64`;
          `pc : num`; `pc + 0xf8 : num`; `K_base : num`] 63 THEN
      RENAME_TAC `s63:armstate` `s62:armstate` THEN
      (* ??? Once the bounding machinary is ready, should be able to avoid the expansion and make stepping faster *)
      RULE_ASSUM_TAC (REWRITE_RULE [msg_schedule_at]) THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ARM_STEPS_TAC EXEC (63--64) THEN
      FIRST_X_ASSUM MP_TAC THEN COND_CASES_TAC THENL
      [ (* Case: jump *)
        STRIP_TAC THEN
          ARM_STEPS_TAC EXEC (139--149) THEN
          ARM_STEPS_TAC EXEC (73--75) THEN (* break here for ADRP-ADD *)
          FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[ADRP_ADD_FOLD] THEN DISCH_TAC) THEN
          ARM_STEPS_TAC EXEC (76--80) THEN
          ENSURES_FINAL_STATE_TAC THEN
          ONCE_ASM_REWRITE_TAC [compression_until] THEN
          ASM_REWRITE_TAC[LT; msg_schedule_at; constants_at; ARITH] THEN
          (* ??? Once the bounding machinary is ready, should be able to avoid the expansion and make stepping faster *)
          CONJ_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
          CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
          ASM_REWRITE_TAC [];
        (* Case: no jump *)
        STRIP_TAC THEN
          ARM_STEPS_TAC EXEC (65--75) THEN
          FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[ADRP_ADD_FOLD] THEN DISCH_TAC) THEN
          ARM_STEPS_TAC EXEC (76--79) THEN
          ARM_STEPS_TAC EXEC [86] THEN
          ENSURES_FINAL_STATE_TAC THEN
          ONCE_ASM_REWRITE_TAC [compression_until] THEN
          ASM_REWRITE_TAC[LT; msg_schedule_at; constants_at; ARITH] THEN
          (* ??? Once the bounding machinary is ready, should be able to avoid the expansion and make stepping faster *)
          CONJ_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
          CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
          ASM_REWRITE_TAC [] ];
    (* Subgoal 3: loop body *)
    REPEAT STRIP_TAC THEN
      REWRITE_TAC [hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
      ENSURES_INIT_TAC "s86" THEN
      RULE_ASSUM_TAC (REWRITE_RULE [msg_schedule_at; constants_at]) THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
      RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ASSUME_TAC(GEN_ALL WORD_ADD1_SHL3_SUB8) THEN
      RULE_ASSUM_TAC (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
      SUBGOAL_THEN
      `read (memory :> bytes64 (word K_base + word (8 * i))) s86 = K i /\
        read (memory :> bytes64 (sp + word (80 + 8 * i))) s86 = msg_schedule m i`
      STRIP_ASSUME_TAC THENL
      [CONJ_TAC THEN UNDISCH_TAC `i < 79` THEN SPEC_TAC(`i:num`,`i:num`) THEN
        CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
        ASSUME_TAC(WORD_RULE `(sp + word 80) + word(8 * i):int64 = sp + word(80 + 8 * i)`) THEN
      ARM_STEPS_TAC EXEC (87--117) THEN
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
      ARM_STEPS_TAC EXEC (81--85) THEN
      ARM_STEPS_TAC EXEC [87] THEN
      RENAME_TAC `s87:armstate` `s86':armstate` THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[LT; msg_schedule_at; constants_at; ARITH; WORD_ADD] THEN
      MP_TAC (SPECL [`0`; `i:num`; `h:hash_t`; `m:num->int64`] COMPRESSION_STEP) THEN
      REWRITE_TAC [LE_0] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
      REWRITE_TAC [compression_update; compression_t1; compression_t2; Sigma0_DEF; Sigma1_DEF; Ch_DEF; Maj_DEF] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC [SHA512_A; SHA512_B; SHA512_C;
        SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H] THEN
      CONJ_TAC THENL [ CONV_TAC WORD_BLAST; ALL_TAC ] THEN
      CONJ_TAC THENL [ CONV_TAC WORD_BLAST; ALL_TAC ] THEN
      CONJ_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC [];
    (* Subgoal 4: backedge *)
    REPEAT STRIP_TAC THEN ARM_SIM_TAC EXEC [];
    ALL_TAC;
  ] THEN
  (* After the loop *)
  REWRITE_TAC [hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
  ENSURES_INIT_TAC "s86" THEN
  RULE_ASSUM_TAC (REWRITE_RULE [msg_schedule_at; constants_at]) THEN
  RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  RULE_ASSUM_TAC (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  ARM_STEPS_TAC EXEC (87--117) THEN (* Do not branch *)
  CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ARM_STEPS_TAC EXEC (118--138) THEN
  ENSURES_FINAL_STATE_TAC THEN
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
let SHA512_PROCESS_BLOCKS = prove(
  `! sp h_p h m_p m l pc retpc K_base.
    aligned 16 sp /\
    adrp_within_bounds (word K_base) (word (pc + 0x120)) /\
    PAIRWISE nonoverlapping
      [(word pc : int64, 2748); (h_p, 640); (m_p, num_bytes_per_block * val l);
      (word_sub sp (word 768), 768); (word K_base, 640)] ==>
      ensures arm
      (\s. aligned_bytes_loaded s (word pc) (a_mc pc K_base) /\
          read PC s = word (pc + 0x260) /\
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
    [ ENSURES_INIT_TAC "s152" THEN
        ARM_STEPS_TAC EXEC [153] THEN
        ARM_STEPS_TAC EXEC [171] THEN
        ENSURES_FINAL_STATE_TAC THEN
        ONCE_REWRITE_TAC [sha512'] THEN
        ASM_REWRITE_TAC [VAL_WORD_0];
      ALL_TAC ] THEN
    (* The input data is non-empty *)
    ENSURES_WHILE_UP_TAC
      `val (l : int64)` `pc + 0x280` `pc + 0x294`
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
    REWRITE_TAC [msg_blocks_at; constants_at] THEN
      ENSURES_INIT_TAC "s152" THEN
      ARM_STEPS_TAC EXEC [153] THEN
      SUBGOAL_THEN `~(val (l:int64) = 0)` (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th])) THENL
      [ ASM_REWRITE_TAC [VAL_EQ_0]; ALL_TAC ] THEN
      ARM_STEPS_TAC EXEC (154--160) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ONCE_REWRITE_TAC [sha512'] THEN
      ASM_REWRITE_TAC [hash_buffer_at; EXPAND_HASH_THM; WORD_ADD_0; ARITH] THEN
      CHEAT_TAC (* ??? waiting for the machinery *);
    (* Subgoal 3: loop body *)
    REPEAT STRIP_TAC THEN
      ENSURES_INIT_TAC "s160" THEN
      RULE_ASSUM_TAC (REWRITE_RULE [msg_blocks_at; constants_at; hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC]) THEN
      RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `i:num`) THEN
      ASM_REWRITE_TAC [msg_block_at; num_bytes_per_block; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      DISCH_TAC THEN
      ARM_STEPS_TAC EXEC (161--165) THEN
      ARM_SUBROUTINE_SIM_TAC
        (SPEC_ALL a_mc, EXEC, 0, SPEC_ALL a_mc,
          CONV_RULE (ONCE_DEPTH_CONV EXPAND_CASES_CONV)
          (REWRITE_RULE [num_bytes_per_block; hash_buffer_at; EXPAND_HASH_THM;
                        msg_block_at; constants_at; GSYM CONJ_ASSOC] SHA512_PROCESS_BLOCK))
        [ `sp + word 720 : int64`; `h_p:int64`; `sha512' h m i`;
          `m_p + word (128 * i) : int64`; `m (i : num) : num -> int64`;
          `pc : num`; `pc + 0x294`; `K_base : num`] 166 THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC [msg_blocks_at; constants_at; hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [ CONV_TAC WORD_RULE; ALL_TAC ]) THEN
      REPLICATE_TAC 8 (CONJ_TAC THENL
      [ GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [sha512'] THEN
          REWRITE_TAC [ARITH_RULE `~(i + 1 = 0) /\ (i + 1) - 1 = i`];
        ALL_TAC ]) THEN
      CHEAT_TAC;
    (* Subgoal 4: backedge *)
    REPEAT STRIP_TAC THEN
      REWRITE_TAC [msg_blocks_at; constants_at; hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
      ENSURES_INIT_TAC "s165" THEN
      ARM_STEPS_TAC EXEC (166--167) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [VAL_EQ_0] THEN
      REWRITE_TAC [WORD_RULE `(word_sub l (word(i + 1))) + word 1 = word 0 <=> word i = l`] THEN
      ASM_SIMP_TAC [MESON[VAL_BOUND; VAL_WORD_GALOIS; LT_TRANS; LT_REFL] `i < val(l:int64) ==> ~(word i = l)`] THEN
      CHEAT_TAC (*??? waiting for machinery *);
    ALL_TAC ] THEN
  (* After the loop *)
  REWRITE_TAC [msg_blocks_at; constants_at; hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s165" THEN
    ARM_STEPS_TAC EXEC (166--167) THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [WORD_RULE `word_sub l (word (val l + 1)) + word 1 : int64 = word 0`] THEN
    REWRITE_TAC [VAL_EQ_0] THEN DISCH_TAC THEN
    ARM_STEPS_TAC EXEC (168--171) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC []);;









(*********** ??? work in progress ***********)
let rec back_up n = if n > 1 then (b(); back_up (n-1)) else b();;


let BYTES_MOD_BLOCKS_SUB_LIST = prove(
  `! m. bytes_mod_blocks m =
    SUB_LIST
      (LENGTH m DIV num_bytes_per_block * num_bytes_per_block,
       LENGTH m MOD num_bytes_per_block)
      m`,
  STRIP_TAC THEN
  REWRITE_TAC [bytes_mod_blocks; drop; num_bytes_per_block] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    [MATCH_MP DIVISION (ARITH_RULE `~(128 = 0)`)] THEN
  REWRITE_TAC [ADD_SUB2]);;

let LENGTH_BYTES_MOD_BLOCKS_LT = prove(
  `! m. LENGTH (bytes_mod_blocks m) < num_bytes_per_block`,
  STRIP_TAC THEN
  REWRITE_TAC [num_bytes_per_block; BYTES_MOD_BLOCKS_SUB_LIST; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

(* void sha512_update(sha512_ctx *sha, const void *in_data, size_t in_len) *)
g `! sp ctx_p m0 m_p m l pc retpc K_base.
    aligned 16 sp /\
    adrp_within_bounds (word K_base) (word (pc + 0x120)) /\
    PAIRWISE nonoverlapping
      [(word pc : int64, 2748); (ctx_p, 216); (m_p, val l);
       (word_sub sp (word 816), 816); (word K_base, 640)] /\
    LENGTH m0 + LENGTH m < 2 EXP 125 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K_base) /\
         read PC s = word (pc + 0x350) /\
         read X30 s = word retpc /\
         read SP s = sp /\
         read X0 s = ctx_p /\
         read X1 s = m_p /\
         read X2 s = l /\
         sha512_ctx_at m0 ctx_p s /\
         byte_list_at m (val l) m_p s /\
         constants_at (word K_base) s)
    (\s. read PC s = word retpc /\
         sha512_ctx_at (m0 ++ m) ctx_p s)
    (MAYCHANGE [X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                  X11; X12; X13; X14; X15; X16; X17; X18; PC] ,,
                  MAYCHANGE [memory :> bytes(ctx_p, 216)] ,,
     MAYCHANGE [memory :> bytes(word_sub sp (word 816), 816)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;

  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL] THEN
    WORD_FORALL_OFFSET_TAC 816 THEN
    REPEAT STRIP_TAC THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
    ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
    ENSURES_PRESERVED_TAC "x21_init" `X21` THEN

    ENSURES_INIT_TAC "s212" THEN
    RULE_ASSUM_TAC (REWRITE_RULE[sha512_ctx_at; byte_list_at; constants_at;
                    sha512_ctx_from; num_bytes_per_block;
                    hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC]) THEN
    RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV let_CONV)) THEN
    RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV))
    POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o rev) THEN
    STRIP_TAC THEN
    ARM_STEPS_TAC EXEC (213--228) THEN
    POP_ASSUM MP_TAC THEN
    IMP_REWRITE_TAC [word_zx; VAL_WORD_EQ; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
    ASSUME_TAC (REWRITE_RULE [num_bytes_per_block] (SPEC `m0 : byte list` LENGTH_BYTES_MOD_BLOCKS_LT)) THEN
    REPEAT (ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]) THEN
    COND_CASES_TAC THENL
    [ (* `bytes_mod_blocks m0` is empty *)
      STRIP_TAC THEN
      ARM_STEPS_TAC EXEC (297--298) THEN
      POP_ASSUM MP_TAC THEN COND_CASES_TAC THENL
      [ STRIP_TAC THEN
        ARM_STEPS_TAC EXEC (409--412) THEN
        ;
      ]
      ;
    ]





(* void sha512_final(uint8_t out[SHA512_DIGEST_LENGTH], sha512_ctx *sha) *)
g `! sp out_p ctx_p m pc retpc K_base.
    aligned 16 sp /\
    adrp_within_bounds (word K_base) (word (pc + 0x120)) /\
    PAIRWISE nonoverlapping
      [(word pc : int64, 2748); (ctx_p, 216);
       (word_sub sp (word 768), 768); (word K_base, 640)] /\
    LENGTH m < 2 EXP 125 ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K_base) /\
         read PC s = word (pc + 0x7e4) /\
         read X30 s = word retpc /\
         read SP s = sp /\
         read X0 s = out_p /\
         read X1 s = ctx_p /\
         sha512_ctx_at m ctx_p s /\
         constants_at (word K_base) s)
    (\s. read PC s = word retpc /\
        hash_buffer_at (sha512 (bytes_to_blocks (pad m)) (LENGTH (pad m) DIV num_bytes_per_block)) out_p s)
    (MAYCHANGE [X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                X12; X13; X14; X15; X16; X17; X18; PC] ,,
     MAYCHANGE [memory :> bytes(ctx_p, 216)] ,,
     MAYCHANGE [memory :> bytes(out_p, 64)] ,,
     MAYCHANGE [memory :> bytes(word_sub sp (word 768), 768)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;