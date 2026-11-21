(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The BLAKE2s hash function of RFC 7693, for byte-string keys and inputs.   *)
(*                                                                           *)
(* This follows the pseudocode of RFC 7693 Section 3 for BLAKE2s (32-bit     *)
(* words, 10 rounds, rotations 16, 12, 8 and 7, blocks of 64 bytes). The     *)
(* working vector v[0..15] and the chained state h[0..7] are functions from  *)
(* indices to words, the message block m[0..15] likewise, and byte strings   *)
(* are read and written as little-endian numbers (Section 2.4). The hash     *)
(* blake2s key nn msg is BLAKE2s with key `key` (0 to 32 bytes), output      *)
(* length nn (1 to 32 bytes) and input `msg`; the definitions are total but  *)
(* only meaningful in those ranges.                                          *)
(* ========================================================================= *)

needs "Library/words.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Little-endian correspondence between byte lists and numbers. These are    *)
(* the same definitions as in common/words2.ml and common/fips202.ml, so     *)
(* they can be loaded together, but this file only needs the HOL Light       *)
(* library.                                                                  *)
(* ------------------------------------------------------------------------- *)

let num_of_bytelist = define
 `(num_of_bytelist [] = 0) /\
  (!h t. num_of_bytelist (CONS h t) = val(h:byte) + 256 * num_of_bytelist t)`;;

let bytelist_of_num = define
 `(bytelist_of_num 0 n = []) /\
  (bytelist_of_num (SUC k) n =
     CONS (word(n MOD 256):byte) (bytelist_of_num k (n DIV 256)))`;;

(* ------------------------------------------------------------------------- *)
(* The initialization vector (Section 2.6) and the message schedule SIGMA    *)
(* (Section 2.7).                                                            *)
(* ------------------------------------------------------------------------- *)

let blake2s_iv = new_definition
 `blake2s_iv:int32 list =
   [word 0x6A09E667; word 0xBB67AE85; word 0x3C6EF372; word 0xA54FF53A;
    word 0x510E527F; word 0x9B05688C; word 0x1F83D9AB; word 0x5BE0CD19]`;;

let blake2s_sigma = new_definition
 `blake2s_sigma =
   [[ 0;  1;  2;  3;  4;  5;  6;  7;  8;  9; 10; 11; 12; 13; 14; 15];
    [14; 10;  4;  8;  9; 15; 13;  6;  1; 12;  0;  2; 11;  7;  5;  3];
    [11;  8; 12;  0;  5;  2; 15; 13; 10; 14;  3;  6;  7;  1;  9;  4];
    [ 7;  9;  3;  1; 13; 12; 11; 14;  2;  6;  5; 10;  4;  0; 15;  8];
    [ 9;  0;  5;  7;  2;  4; 10; 15; 14;  1; 11; 12;  6;  8;  3; 13];
    [ 2; 12;  6; 10;  0; 11;  8;  3;  4; 13;  7;  5; 15; 14;  1;  9];
    [12;  5;  1; 15; 14; 13;  4; 10;  0;  7;  6;  3;  9;  2;  8; 11];
    [13; 11;  7; 14; 12;  1;  3;  9;  5;  0; 15;  4;  8;  6;  2; 10];
    [ 6; 15; 14;  9; 11;  3;  0;  8; 12;  2; 13;  7;  1;  4; 10;  5];
    [10;  2;  8;  4;  7;  6;  1;  5; 15; 11;  9; 14;  3; 12; 13;  0]]`;;

(* ------------------------------------------------------------------------- *)
(* The mixing function G (Section 3.1) on v[a], v[b], v[c] and v[d], with    *)
(* the message words x and y.                                                *)
(* ------------------------------------------------------------------------- *)

let blake2s_g = new_definition
 `blake2s_g a b c d (x:int32) (y:int32) (v:num->int32) =
    let va = word_add (word_add (v a) (v b)) x in
    let vd = word_ror (word_xor (v d) va) 16 in
    let vc = word_add (v c) vd in
    let vb = word_ror (word_xor (v b) vc) 12 in
    let va' = word_add (word_add va vb) y in
    let vd' = word_ror (word_xor vd va') 8 in
    let vc' = word_add vc vd' in
    let vb' = word_ror (word_xor vb vc') 7 in
    \i. if i = a then va' else if i = b then vb'
        else if i = c then vc' else if i = d then vd' else v i`;;

(* ------------------------------------------------------------------------- *)
(* One round of the compression function F (Section 3.2), the first eight    *)
(* applications of G down the columns and then along the diagonals, and the  *)
(* first n rounds.                                                           *)
(* ------------------------------------------------------------------------- *)

let blake2s_round = new_definition
 `blake2s_round r (m:num->int32) (v:num->int32) =
    let s = \j. m (EL j (EL (r MOD 10) blake2s_sigma)) in
    blake2s_g 3 4  9 14 (s 14) (s 15)
     (blake2s_g 2 7  8 13 (s 12) (s 13)
       (blake2s_g 1 6 11 12 (s 10) (s 11)
         (blake2s_g 0 5 10 15 (s 8) (s 9)
           (blake2s_g 3 7 11 15 (s 6) (s 7)
             (blake2s_g 2 6 10 14 (s 4) (s 5)
               (blake2s_g 1 5  9 13 (s 2) (s 3)
                 (blake2s_g 0 4  8 12 (s 0) (s 1) v)))))))`;;

let blake2s_rounds = define
 `blake2s_rounds 0 m v = v /\
  blake2s_rounds (SUC n) m v = blake2s_round n m (blake2s_rounds n m v)`;;

(* ------------------------------------------------------------------------- *)
(* The compression function F (Section 3.2) of the state h with the message  *)
(* block m, the offset counter t (a 64-bit number, the number of bytes       *)
(* hashed so far) and the final-block flag f, and its initial work vector.   *)
(* ------------------------------------------------------------------------- *)

let blake2s_workvec = new_definition
 `blake2s_workvec (h:num->int32) t f =
    \i. if i < 8 then h i
        else if i = 12 then word_xor (EL 4 blake2s_iv) (word t)
        else if i = 13 then word_xor (EL 5 blake2s_iv) (word(t DIV 2 EXP 32))
        else if i = 14 /\ f then word_not (EL 6 blake2s_iv)
        else EL (i - 8) blake2s_iv`;;

let blake2s_compress = new_definition
 `blake2s_compress (h:num->int32) (m:num->int32) t f =
    let v = blake2s_rounds 10 m (blake2s_workvec h t f) in
    \i. word_xor (h i) (word_xor (v i) (v(i + 8)))`;;

(* ------------------------------------------------------------------------- *)
(* The hash (Section 3.3). The data blocks d[0..dd-1] are the key padded     *)
(* with zeros to a whole block (if there is a key) followed by the input     *)
(* padded with zeros to a whole number of blocks, with one block of zeros if *)
(* both are empty. The words of block i are little-endian 4-byte groups.     *)
(* ------------------------------------------------------------------------- *)

let blake2s_block = new_definition
 `blake2s_block (p:byte list) i =
    \j. word(num_of_bytelist(SUB_LIST(64 * i + 4 * j,4) p)):int32`;;

let blake2s_blocks = define
 `blake2s_blocks (d:num->num->int32) h 0 = h /\
  blake2s_blocks d h (SUC i) =
    blake2s_compress (blake2s_blocks d h i) (d i) (64 * (i + 1)) F`;;

let blake2s_data = new_definition
 `blake2s_data (key:byte list) (msg:byte list) =
    let d = APPEND (if LENGTH key = 0 then []
                    else APPEND key (REPLICATE (64 - LENGTH key) (word 0)))
                   msg in
    let dd = MAX 1 ((LENGTH d + 63) DIV 64) in
    (dd,APPEND d (REPLICATE (64 * dd - LENGTH d) (word 0)))`;;

let blake2s_bytes = new_definition
 `blake2s_bytes (h:num->int32) =
    bytelist_of_num 32 (nsum (0..7) (\i. val(h i) * 2 EXP (32 * i)))`;;

let blake2s = new_definition
 `blake2s (key:byte list) nn (msg:byte list) =
    let kk = LENGTH key and ll = LENGTH msg in
    let dd,p = blake2s_data key msg in
    let h0 = \i. if i = 0
                 then word_xor (EL 0 blake2s_iv)
                       (word_xor (word 0x01010000)
                         (word_xor (word_shl (word kk) 8) (word nn)))
                 else EL i blake2s_iv in
    let h = blake2s_blocks (blake2s_block p) h0 (dd - 1) in
    let h' = blake2s_compress h (blake2s_block p (dd - 1))
                              (if kk = 0 then ll else ll + 64) T in
    SUB_LIST(0,nn) (blake2s_bytes h')`;;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
