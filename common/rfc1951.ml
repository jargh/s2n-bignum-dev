(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The DEFLATE compressed data format, per RFC 1951.                         *)
(*                                                                           *)
(* Decoding is specified by relations that follow the structure of the RFC.  *)
(* The input is a list of bytes, read as a stream of bits starting from the  *)
(* least significant bit of each byte (section 3.1.1), and the relations     *)
(* connect positions in that stream with the output produced. Where the RFC  *)
(* leaves room for interpretation, acceptance and rejection follow puff.c,   *)
(* Mark Adler's decoder in zlib written as an unambiguous statement of the   *)
(* format: the NLEN of a stored block must be the one's complement of LEN,   *)
(* a distance may not reach back before the start of the output, the code    *)
(* length code must be complete, and a literal/length or distance code may   *)
(* be incomplete only if it consists of one code of length 1 (or, for        *)
(* distances, of no codes at all).                                           *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* The bit stream. Numbers other than Huffman codes are packed starting      *)
(* with their least significant bit, and Huffman codes starting with their   *)
(* most significant bit.                                                     *)
(* ------------------------------------------------------------------------- *)

let deflate_bit = new_definition
 `deflate_bit (l:byte list) i = bit (i MOD 8) (EL (i DIV 8) l)`;;

let deflate_bits = define
 `(deflate_bits (l:byte list) p 0 = 0) /\
  (deflate_bits l p (SUC n) =
   bitval(deflate_bit l p) + 2 * deflate_bits l (p + 1) n)`;;

let deflate_codebits = define
 `(deflate_codebits (l:byte list) p 0 = 0) /\
  (deflate_codebits l p (SUC n) =
   2 EXP n * bitval(deflate_bit l p) + deflate_codebits l (p + 1) n)`;;

(* ------------------------------------------------------------------------- *)
(* Canonical Huffman codes (section 3.2.2), given by the list of code        *)
(* lengths for the symbols 0, 1, 2, ..., in which 0 means that the symbol    *)
(* has no code. Codes are assigned in order of length and then of symbol,    *)
(* so the code of s is the number below, written with EL s lens bits. The    *)
(* code lengths are at most 15, so the Kraft sum is scaled by 2^15: the      *)
(* code is complete if the sum is 2^15, and is prefix-free if it is at most  *)
(* 2^15. The symbol s is decoded from the bits at positions p to q - 1 if    *)
(* those bits are its code.                                                  *)
(* ------------------------------------------------------------------------- *)

let huffman_code = new_definition
 `huffman_code (lens:num list) s =
    nsum {t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens < EL s lens}
         (\t. 2 EXP (EL s lens - EL t lens)) +
    CARD {t | t < s /\ EL t lens = EL s lens}`;;

let huffman_kraft = new_definition
 `huffman_kraft (lens:num list) =
    nsum {s | s < LENGTH lens /\ ~(EL s lens = 0)}
         (\s. 2 EXP (15 - EL s lens))`;;

let huffman_decode = new_definition
 `huffman_decode (l:byte list) lens p s q <=>
    s < LENGTH lens /\ ~(EL s lens = 0) /\ q = p + EL s lens /\
    q <= 8 * LENGTH l /\
    deflate_codebits l p (EL s lens) = huffman_code lens s`;;

(* The literal/length and distance codes of a dynamic block must be          *)
(* prefix-free, and complete unless all their code lengths are 0 or 1.       *)

let huffman_ok = new_definition
 `huffman_ok (lens:num list) <=>
    huffman_kraft lens <= 2 EXP 15 /\
    (huffman_kraft lens = 2 EXP 15 \/ ALL (\n. n <= 1) lens)`;;

(* ------------------------------------------------------------------------- *)
(* Lengths and distances (section 3.2.5): the symbol 257 + i stands for a    *)
(* length EL i deflate_length_base plus the number in the next               *)
(* EL i deflate_length_extra bits, and the distance symbol d for a distance  *)
(* EL d deflate_dist_base plus the next EL d deflate_dist_extra bits.        *)
(* ------------------------------------------------------------------------- *)

let deflate_length_base = new_definition
 `deflate_length_base =
    [3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 15; 17; 19; 23; 27; 31;
     35; 43; 51; 59; 67; 83; 99; 115; 131; 163; 195; 227; 258]`;;

let deflate_length_extra = new_definition
 `deflate_length_extra =
    [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 2; 2; 2; 2;
     3; 3; 3; 3; 4; 4; 4; 4; 5; 5; 5; 5; 0]`;;

let deflate_dist_base = new_definition
 `deflate_dist_base =
    [1; 2; 3; 4; 5; 7; 9; 13; 17; 25; 33; 49; 65; 97; 129; 193;
     257; 385; 513; 769; 1025; 1537; 2049; 3073; 4097; 6145;
     8193; 12289; 16385; 24577]`;;

let deflate_dist_extra = new_definition
 `deflate_dist_extra =
    [0; 0; 0; 0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6;
     7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 12; 13; 13]`;;

(* A length/distance pair at positions p to q - 1, using the literal/length  *)
(* code ll and the distance code dl.                                         *)

let deflate_lendist = new_definition
 `deflate_lendist (l:byte list) ll dl p len distance q <=>
    ?s p1 d p2.
        huffman_decode l ll p s p1 /\ 257 <= s /\ s <= 285 /\
        huffman_decode l dl (p1 + EL (s - 257) deflate_length_extra) d p2 /\
        d < 30 /\ q = p2 + EL d deflate_dist_extra /\ q <= 8 * LENGTH l /\
        len = EL (s - 257) deflate_length_base +
              deflate_bits l p1 (EL (s - 257) deflate_length_extra) /\
        distance = EL d deflate_dist_base +
               deflate_bits l p2 (EL d deflate_dist_extra)`;;

(* Copying len bytes from distance bytes back, one at a time, so the copy    *)
(* may overlap the bytes it produces.                                        *)

let lz77_copy = define
 `(lz77_copy (out:byte list) distance 0 = out) /\
  (lz77_copy out distance (SUC n) =
   lz77_copy (APPEND out [EL (LENGTH out - distance) out]) distance n)`;;

(* ------------------------------------------------------------------------- *)
(* The compressed data of a block (section 3.2.5), up to and including the   *)
(* end-of-block symbol 256: deflate_codes l ll dl (out,p) (out',q) when the  *)
(* bits from p to q - 1 extend the output from out to out'.                  *)
(* ------------------------------------------------------------------------- *)

let DEFLATE_CODES_RULES,DEFLATE_CODES_INDUCT,DEFLATE_CODES_CASES =
  new_inductive_definition
 `(!out p q.
        huffman_decode l ll p 256 q
        ==> deflate_codes (l:byte list) ll dl (out:byte list,p) (out,q)) /\
  (!out p q s r.
        huffman_decode l ll p s q /\ s < 256 /\
        deflate_codes l ll dl (APPEND out [word s],q) r
        ==> deflate_codes l ll dl (out,p) r) /\
  (!out p q len distance r.
        deflate_lendist l ll dl p len distance q /\ distance <= LENGTH out /\
        deflate_codes l ll dl (lz77_copy out distance len,q) r
        ==> deflate_codes l ll dl (out,p) r)`;;

(* ------------------------------------------------------------------------- *)
(* Stored blocks (section 3.2.4): after skipping to a byte boundary, LEN,    *)
(* its one's complement NLEN, and LEN bytes copied to the output.            *)
(* ------------------------------------------------------------------------- *)

let deflate_stored = new_definition
 `deflate_stored (l:byte list) (out:byte list,p) r <=>
    ?a n. a = 8 * ((p + 7) DIV 8) /\ n = deflate_bits l a 16 /\
          deflate_bits l (a + 16) 16 = 65535 - n /\
          a + 32 + 8 * n <= 8 * LENGTH l /\
          r = (APPEND out (list_of_seq (\i. EL (a DIV 8 + 4 + i) l) n),
               a + 32 + 8 * n)`;;

(* ------------------------------------------------------------------------- *)
(* Blocks compressed with fixed Huffman codes (section 3.2.6). The fixed     *)
(* literal/length code includes the invalid symbols 286 and 287, and the     *)
(* fixed distance code the invalid symbols 30 and 31.                        *)
(* ------------------------------------------------------------------------- *)

let deflate_fixed_ll = new_definition
 `deflate_fixed_ll =
    list_of_seq (\s. if s < 144 then 8 else if s < 256 then 9
                     else if s < 280 then 7 else 8) 288`;;

let deflate_fixed_dl = new_definition
 `deflate_fixed_dl = REPLICATE 32 5`;;

(* ------------------------------------------------------------------------- *)
(* Blocks compressed with dynamic Huffman codes (section 3.2.7). The code    *)
(* lengths of the literal/length and distance codes are themselves coded:    *)
(* deflate_lengths l cl n (lens,p) (lens',q) when the bits from p to q - 1   *)
(* code lengths, run-length coded with the code length code cl, that extend  *)
(* lens to lens' of length n.                                                *)
(* ------------------------------------------------------------------------- *)

let DEFLATE_LENGTHS_RULES,DEFLATE_LENGTHS_INDUCT,DEFLATE_LENGTHS_CASES =
  new_inductive_definition
 `(!lens p.
        LENGTH lens = n
        ==> deflate_lengths (l:byte list) cl n (lens,p) (lens,p)) /\
  (!lens p q s r.
        LENGTH lens < n /\ huffman_decode l cl p s q /\ s < 16 /\
        deflate_lengths l cl n (APPEND lens [s],q) r
        ==> deflate_lengths l cl n (lens,p) r) /\
  (!lens p q k r.
        huffman_decode l cl p 16 q /\ ~(lens = []) /\
        q + 2 <= 8 * LENGTH l /\ k = 3 + deflate_bits l q 2 /\
        LENGTH lens + k <= n /\
        deflate_lengths l cl n (APPEND lens (REPLICATE k (LAST lens)),q + 2) r
        ==> deflate_lengths l cl n (lens,p) r) /\
  (!lens p q k r.
        huffman_decode l cl p 17 q /\
        q + 3 <= 8 * LENGTH l /\ k = 3 + deflate_bits l q 3 /\
        LENGTH lens + k <= n /\
        deflate_lengths l cl n (APPEND lens (REPLICATE k 0),q + 3) r
        ==> deflate_lengths l cl n (lens,p) r) /\
  (!lens p q k r.
        huffman_decode l cl p 18 q /\
        q + 7 <= 8 * LENGTH l /\ k = 11 + deflate_bits l q 7 /\
        LENGTH lens + k <= n /\
        deflate_lengths l cl n (APPEND lens (REPLICATE k 0),q + 7) r
        ==> deflate_lengths l cl n (lens,p) r)`;;

(* The code length code lengths come in this order.                          *)

let deflate_clen_order = new_definition
 `deflate_clen_order =
    [16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14; 1; 15]`;;

let deflate_dynamic = new_definition
 `deflate_dynamic (l:byte list) (out:byte list,p) r <=>
    ?nlen ndist ncode cl lens q.
        nlen = 257 + deflate_bits l p 5 /\ nlen <= 286 /\
        ndist = 1 + deflate_bits l (p + 5) 5 /\ ndist <= 30 /\
        ncode = 4 + deflate_bits l (p + 10) 4 /\
        p + 14 + 3 * ncode <= 8 * LENGTH l /\
        LENGTH cl = 19 /\
        (!i. i < 19
             ==> EL (EL i deflate_clen_order) cl =
                 if i < ncode then deflate_bits l (p + 14 + 3 * i) 3 else 0) /\
        huffman_kraft cl = 2 EXP 15 /\
        deflate_lengths l cl (nlen + ndist)
                        ([],p + 14 + 3 * ncode) (lens,q) /\
        ~(EL 256 lens = 0) /\
        huffman_ok (list_of_seq (\i. EL i lens) nlen) /\
        huffman_ok (list_of_seq (\i. EL (nlen + i) lens) ndist) /\
        deflate_codes l (list_of_seq (\i. EL i lens) nlen)
                        (list_of_seq (\i. EL (nlen + i) lens) ndist)
                        (out,q) r`;;

(* ------------------------------------------------------------------------- *)
(* Blocks (section 3.2.3): after the bit BFINAL and the two bits BTYPE, the  *)
(* block data, whose form depends on BTYPE (3 is an error). The blocks are   *)
(* decoded up to one with BFINAL set.                                        *)
(* ------------------------------------------------------------------------- *)

let deflate_block = new_definition
 `deflate_block (l:byte list) btype (out:byte list,p) r <=>
    btype = 0 /\ deflate_stored l (out,p) r \/
    btype = 1 /\ deflate_codes l deflate_fixed_ll deflate_fixed_dl (out,p) r \/
    btype = 2 /\ deflate_dynamic l (out,p) r`;;

let DEFLATE_BLOCKS_RULES,DEFLATE_BLOCKS_INDUCT,DEFLATE_BLOCKS_CASES =
  new_inductive_definition
 `(!out p r.
        p + 3 <= 8 * LENGTH l /\ deflate_bit l p /\
        deflate_block l (deflate_bits l (p + 1) 2) (out,p + 3) r
        ==> deflate_blocks (l:byte list) (out:byte list,p) r) /\
  (!out p r s.
        p + 3 <= 8 * LENGTH l /\ ~deflate_bit l p /\
        deflate_block l (deflate_bits l (p + 1) 2) (out,p + 3) s /\
        deflate_blocks l s r
        ==> deflate_blocks l (out,p) r)`;;

(* ------------------------------------------------------------------------- *)
(* A compressed data set at the start of the input l decodes to the output   *)
(* out using the first n bytes of l. Any bits after the end of the final     *)
(* block in its last byte are ignored, as are any later bytes.               *)
(* ------------------------------------------------------------------------- *)

let deflate_decode = new_definition
 `deflate_decode (l:byte list) out n <=>
    ?q. deflate_blocks l ([],0) (out,q) /\ n = (q + 7) DIV 8`;;
