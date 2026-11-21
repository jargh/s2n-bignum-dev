(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The code and read-only data of the WireGuard handshake image compiled by  *)
(* gcc 13 with -O2 from Linux 6.18.64 (see wireguard/README.md), as one      *)
(* image. All the theorems about it assume that it is loaded at an address   *)
(* pc that is a multiple of 4096, as the dynamic loader does, and that it    *)
(* does not wrap around the end of the address space, i.e.                   *)
(* pc + wireguard_size <= 2 EXP 64. A function f in it is then at pc + f,    *)
(* with the names for the addresses and sizes in the binary that are listed  *)
(* in layout.ml.                                                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/wireguard/gcc13_O2/layout.ml";;
needs "arm/proofs/utils/wireguard.ml";;

let wireguard_gcc13_O2_mc = define_from_elf
  "wireguard_gcc13_O2_mc" "arm/wireguard/gcc13_O2/wireguard.o";;

let LENGTH_WIREGUARD_GCC13_O2_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` wireguard_gcc13_O2_mc);;

(* The image has the size given in the layout file.                          *)

let () =
  if dest_small_numeral(rhs(concl LENGTH_WIREGUARD_GCC13_O2_MC)) <>
     layout "wireguard_size"
  then failwith "The size of the image is not wireguard_size";;
