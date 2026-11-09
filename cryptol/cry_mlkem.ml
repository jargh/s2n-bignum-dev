(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A naive shallow translation of the Cryptol specification of ML-KEM        *)
(* (GaloisInc/cryptol-specs, Primitive/Asymmetric/KEM/ML_KEM/                *)
(* Specification.cry at commit 3558c703cfa7d86c2a3387cedfab6f83e8bcd558)     *)
(* into HOL Light. The proofs that the translated functions agree with       *)
(* common/fips203.ml are in cryptol/cry_mlkem_proofs.ml.                     *)
(*                                                                           *)
(* The Cryptol text quoted in the comments is Copyright (c) 2013-2025        *)
(* Galois Inc., under the BSD 3-Clause license in                            *)
(* cryptol/LICENSE.cryptol-specs (its fast NTT section is marked Copyright   *)
(* Amazon.com, Inc. or its affiliates).                                      *)
(*                                                                           *)
(* Translation rules (by hand, one HOL definition per Cryptol definition,    *)
(* keeping the structure of the Cryptol text, which is quoted above each):   *)
(*                                                                           *)
(*  - Bit is bool. A bit vector used as a number ([8], [12], [d]) is an      *)
(*    N word with dimindex(:N) the width; a bit array used only as a         *)
(*    sequence ([8 * ell]Bit) is a bool list in Cryptol's sequence order.    *)
(*  - [n]a for other a is a list of length n; [inf]a is a function num->a.   *)
(*    # is APPEND, or cry_sappend when its right operand is infinite.        *)
(*  - Z q is integer_mod_ring 3329 (canonical integers in [0,q)), with its   *)
(*    ring operations; Integer is int; Rational is real.                     *)
(*  - Comprehensions are MAP (nested ones cry_join o MAP, parallel ones      *)
(*    over ZIP); [a .. b] is cry_range; sum is cry_zsum or cry_wsum;         *)
(*    join is cry_join; split/groupBy are cry_split/cry_groupBy.             *)
(*  - Numeric type parameters used as values become num arguments, and       *)
(*    Cryptol names that are HOL constants get a suffix v (F, vector).       *)
(*  - The module parameters k, eta_1, eta_2 are num arguments of the         *)
(*    functions that use them. d_u and d_v are also bit-vector widths, so    *)
(*    they are type variables DU and DV (d_u = dimindex(:DU)), carried by    *)
(*    arguments (:DU) and (:DV), as for dimindex.                            *)
(*  - xs @@ is is cry_atat; transpose is cry_transpose, with the number of   *)
(*    columns as an argument. Option is option; error is ARB.                *)
(*  - The SHA-3 functions of the Cryptol spec are taken to be those of       *)
(*    common/fips202.ml (relating the two SHA-3 specs is a separate step).   *)
(* ========================================================================= *)

needs "common/fips203_theory.ml";;
needs "Library/floor.ml";;

(* Library/floor.ml leaves real arithmetic prioritized; restore the          *)
(* default, so that unannotated arithmetic below is on num.                  *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The few Cryptol prelude functions used, on lists.                         *)
(* ------------------------------------------------------------------------- *)

(* [a .. b] for numbers (empty if b < a).                                    *)

let cry_range = new_definition
 `cry_range a b = list_of_seq (\i. a + i) ((b + 1) - a)`;;

(* groupBy`{each}: consecutive groups of `each` elements; split`{parts}:     *)
(* `parts` equal groups.                                                     *)

let cry_groupBy = new_definition
 `cry_groupBy each (l:A list) =
    list_of_seq (\i. list_of_seq (\j. EL (each * i + j) l) each)
                (LENGTH l DIV each)`;;

let cry_split = new_definition
 `cry_split parts (l:A list) = cry_groupBy (LENGTH l DIV parts) l`;;

(* join: concatenation of a sequence of sequences.                           *)

let cry_join = new_definition
 `cry_join (l:(A list) list) = ITLIST APPEND l []`;;

(* xs @@ is: the elements of xs at the indices is; transpose`{cols}: the     *)
(* transpose of a matrix with cols columns.                                  *)

let cry_atat = new_definition
 `cry_atat (xs:A list) (is:num list) = MAP (\i. EL i xs) is`;;

let cry_transpose = new_definition
 `cry_transpose cols (m:(A list) list) =
    list_of_seq (\j. MAP (\row. EL j row) m) cols`;;

(* # with an infinite right operand: a sequence followed by a stream.        *)

let cry_sappend = new_definition
 `cry_sappend (l:A list) (t:num->A) =
    \n. if n < LENGTH l then EL n l else t(n - LENGTH l)`;;

(* sum, in Z q and for words (Cryptol's foldl (+) zero; both are             *)
(* commutative and associative, so the order of the fold is immaterial).     *)

let cry_zsum = new_definition
 `cry_zsum (l:int list) =
    ITLIST (ring_add (integer_mod_ring 3329)) l
           (ring_0(integer_mod_ring 3329))`;;

let cry_wsum = new_definition
 `cry_wsum (l:(N word) list) = ITLIST word_add l (word 0)`;;

(* ------------------------------------------------------------------------- *)
(* roundNearest : Rational -> Integer                                        *)
(* roundNearest x = floor (x + 0.5)                                          *)
(* ------------------------------------------------------------------------- *)

let cry_roundNearest = new_definition
 `cry_roundNearest (x:real) = int_of_real(floor(x + &1 / &2))`;;

(* ------------------------------------------------------------------------- *)
(* Compress : {d} (d < width q) => Z q -> [d]                                *)
(* Compress x = y where                                                      *)
(*     x' = fromInteger (fromZ x) : Rational                                 *)
(*     y' = roundNearest (((2^^`d) /. `q) * x')                              *)
(*     y = (fromInteger y') : [d]                                            *)
(* ------------------------------------------------------------------------- *)

let cry_Compress = new_definition
 `cry_Compress (x:int) : N word =
    let x' = real_of_int x in
    let y' = cry_roundNearest((&2 pow dimindex(:N) / &3329) * x') in
    iword y'`;;

(* ------------------------------------------------------------------------- *)
(* Decompress : {d} (d < width q) => [d] -> Z q                              *)
(* Decompress y = x where                                                    *)
(*     y' = fromInteger (toInteger y) : Rational                             *)
(*     x' = roundNearest ((`q /. (2^^`d)) * y')                              *)
(*     x = (fromInteger x') : Z q                                            *)
(* ------------------------------------------------------------------------- *)

let cry_Decompress = new_definition
 `cry_Decompress (y:N word) : int =
    let y' = real_of_int(&(val y)) in
    let x' = cry_roundNearest((&3329 / &2 pow dimindex(:N)) * y') in
    x' rem &3329`;;

(* ------------------------------------------------------------------------- *)
(* Compress_Vec : {d} (d < lg2 q) => [n](Z q) -> [n][d]                      *)
(* Compress_Vec x = map Compress`{d} x                                       *)
(* Decompress_Vec : {d} (d < lg2 q) => [n][d] -> [n](Z q)                    *)
(* Decompress_Vec x = map Decompress`{d} x                                   *)
(* Compress_Mat : {d, k1} (d < lg2 q, fin k1) => [k1][n](Z q) -> [k1][n][d]  *)
(* Compress_Mat x = map Compress_Vec`{d} x                                   *)
(* Decompress_Mat : {d, k1} (d < lg2 q, fin k1) =>                           *)
(*     [k1][n][d] -> [k1][n](Z q)                                            *)
(* Decompress_Mat x = map Decompress_Vec`{d} x                               *)
(* ------------------------------------------------------------------------- *)

let cry_Compress_Vec = new_definition
 `cry_Compress_Vec (x:int list) : (N word) list = MAP cry_Compress x`;;

let cry_Decompress_Vec = new_definition
 `cry_Decompress_Vec (x:(N word) list) : int list = MAP cry_Decompress x`;;

let cry_Compress_Mat = new_definition
 `cry_Compress_Mat (x:(int list) list) : ((N word) list) list =
    MAP cry_Compress_Vec x`;;

let cry_Decompress_Mat = new_definition
 `cry_Decompress_Mat (x:((N word) list) list) : (int list) list =
    MAP cry_Decompress_Vec x`;;

(* ------------------------------------------------------------------------- *)
(* BitsToBytes : {ell} (fin ell) => [8 * ell]Bit -> [ell]Byte                *)
(* BitsToBytes b                                                             *)
(*     | ell == 0 => zero                                                    *)
(*     | ell > 0 => B where                                                  *)
(*         b' = groupBy`{8} [(zext [bi], i)                                  *)
(*             | bi <- b                                                     *)
(*             | i <- [0..8 * ell - 1]]                                      *)
(*         B = [sum [bi * (2 ^^ (i % 8))                                     *)
(*                 | (bi, i) <- bi8]                                         *)
(*             | bi8 <- b']                                                  *)
(* ------------------------------------------------------------------------- *)

let cry_BitsToBytes = new_definition
 `cry_BitsToBytes (b:bool list) : byte list =
    if LENGTH b = 0 then [] else
    let b' = cry_groupBy 8 (ZIP (MAP (\bi. word(bitval bi)) b)
                                (cry_range 0 (LENGTH b - 1))) in
    MAP (\bi8. cry_wsum (MAP (\(bi,i). word_mul bi (word(2 EXP (i MOD 8))))
                             bi8))
        b'`;;

(* ------------------------------------------------------------------------- *)
(* BytesToBits : {ell} (fin ell) => [ell]Byte -> [ell*8]Bit                  *)
(* BytesToBits C                                                             *)
(*     | ell == 0 => []                                                      *)
(*     | ell > 0 => join [[ b8ij where                                       *)
(*             b8ij = Ci' ! 0                                                *)
(*             Ci' = Ci >> j                                                 *)
(*         | j <- [0..7]]                                                    *)
(*         | Ci <- C ]                                                       *)
(* ------------------------------------------------------------------------- *)

let cry_BytesToBits = new_definition
 `cry_BytesToBits (C:byte list) : bool list =
    cry_join (MAP (\Ci. MAP (\j. bit 0 (word_ushr Ci j)) (cry_range 0 7)) C)`;;

(* ------------------------------------------------------------------------- *)
(* ByteEncode : {d} (1 <= d, d < 12) => [256][d] -> [32 * d]Byte             *)
(* ByteEncode F = B where                                                    *)
(*     as = [[ a >> j | j <- [0..d-1]] | a <- F]                             *)
(*     b = join [ [ a ! 0 | a <- ajs] | ajs <- as]                           *)
(*     B = BitsToBytes b                                                     *)
(* ------------------------------------------------------------------------- *)

let cry_ByteEncode = new_definition
 `cry_ByteEncode (Fv:(N word) list) : byte list =
    let as = MAP (\a. MAP (\j. word_ushr a j)
                          (cry_range 0 (dimindex(:N) - 1))) Fv in
    let b = cry_join (MAP (\ajs. MAP (\a. bit 0 a) ajs) as) in
    cry_BitsToBytes b`;;

(* ------------------------------------------------------------------------- *)
(* ByteEncode_Vec : {d} (fin d, 1 <= d, d < 12) =>                           *)
(*     [k][256][d] -> [k * 32 * d]Byte                                       *)
(* ByteEncode_Vec F_vec = join (map ByteEncode F_vec)                        *)
(* ------------------------------------------------------------------------- *)

let cry_ByteEncode_Vec = new_definition
 `cry_ByteEncode_Vec (F_vec:((N word) list) list) =
    cry_join (MAP cry_ByteEncode F_vec)`;;

(* ------------------------------------------------------------------------- *)
(* ByteDecode : {d} (1 <= d, d < 12) => [32 * d]Byte -> [256][d]             *)
(* ByteDecode B = F where                                                    *)
(*     b = BytesToBits B                                                     *)
(*     F = [ sum [ (zext [bidj]) << j                                        *)
(*             | bidj <- bid                                                 *)
(*             | j <- [0..d-1]]                                              *)
(*         | bid <- split`{256} b]                                           *)
(* ------------------------------------------------------------------------- *)

let cry_ByteDecode = new_definition
 `cry_ByteDecode (B:byte list) : (N word) list =
    let b = cry_BytesToBits B in
    MAP (\bid. cry_wsum (MAP (\(bidj,j). word_shl (word(bitval bidj)) j)
                             (ZIP bid (cry_range 0 (dimindex(:N) - 1)))))
        (cry_split 256 b)`;;

(* ------------------------------------------------------------------------- *)
(* ByteDecode_Vec : {d} (1 <= d, d < 12) => [k * 32 * d]Byte -> [k][256][d]  *)
(* ByteDecode_Vec B_vec = map ByteDecode (split B_vec)                       *)
(* ------------------------------------------------------------------------- *)

let cry_ByteDecode_Vec = new_definition
 `cry_ByteDecode_Vec k (B_vec:byte list) : ((N word) list) list =
    MAP cry_ByteDecode (cry_split k B_vec)`;;

(* ------------------------------------------------------------------------- *)
(* ByteEncode12 : [256](Z q) -> [32 * 12]Byte                                *)
(* ByteEncode12 F = B where                                                  *)
(*     type d = 12                                                           *)
(*     toBitVec : Z q -> [d]                                                 *)
(*     toBitVec f = fromInteger (fromZ f)                                    *)
(*     F' = map toBitVec F                                                   *)
(*     as = [[ a >> j | j <- [0..d-1]] | a <- F' ]                           *)
(*     b = join [ [ a ! 0 | a <- ajs] | ajs <- as]                           *)
(*     B = BitsToBytes b                                                     *)
(* ------------------------------------------------------------------------- *)

let cry_ByteEncode12 = new_definition
 `cry_ByteEncode12 (Fv:int list) : byte list =
    let toBitVec = \f. (iword f:12 word) in
    let Fv' = MAP toBitVec Fv in
    let as = MAP (\a. MAP (\j. word_ushr a j) (cry_range 0 (12 - 1))) Fv' in
    let b = cry_join (MAP (\ajs. MAP (\a. bit 0 a) ajs) as) in
    cry_BitsToBytes b`;;

(* ------------------------------------------------------------------------- *)
(* ByteEncode12_Vec : [k][256](Z q) -> [k * 32 * 12]Byte                     *)
(* ByteEncode12_Vec F_vec = join (map ByteEncode12 F_vec)                    *)
(* ------------------------------------------------------------------------- *)

let cry_ByteEncode12_Vec = new_definition
 `cry_ByteEncode12_Vec (F_vec:(int list) list) =
    cry_join (MAP cry_ByteEncode12 F_vec)`;;

(* ------------------------------------------------------------------------- *)
(* ByteDecode12 : [32 * 12]Byte -> [256](Z q)                                *)
(* ByteDecode12 B = F' where                                                 *)
(*     type d = 12                                                           *)
(*     b = BytesToBits B                                                     *)
(*     F = [ sum [ (zext`{d} [bidj]) << j                                    *)
(*             | bidj <- bid                                                 *)
(*             | j <- [0..d-1]]                                              *)
(*         | bid <- split`{256} b]                                           *)
(*     toZq f = fromInteger (toInteger f)                                    *)
(*     F' = map toZq F                                                       *)
(* ------------------------------------------------------------------------- *)

let cry_ByteDecode12 = new_definition
 `cry_ByteDecode12 (B:byte list) : int list =
    let b = cry_BytesToBits B in
    let Fv = MAP (\bid. cry_wsum (MAP (\(bidj,j). word_shl
                                         (word(bitval bidj):12 word) j)
                                     (ZIP bid (cry_range 0 (12 - 1)))))
                (cry_split 256 b) in
    let toZq = \f. &(val f) rem &3329 in
    MAP toZq Fv`;;

(* ------------------------------------------------------------------------- *)
(* ByteDecode12_Vec : [k * 32 * 12]Byte -> [k][256](Z q)                     *)
(* ByteDecode12_Vec B = map ByteDecode12 (split B)                           *)
(* ------------------------------------------------------------------------- *)

let cry_ByteDecode12_Vec = new_definition
 `cry_ByteDecode12_Vec k (B:byte list) =
    MAP cry_ByteDecode12 (cry_split k B)`;;

(* ------------------------------------------------------------------------- *)
(* SamplePolyCBD: {eta} (2 <= eta, eta <= 3) => [64 * eta]Byte -> Rq         *)
(* SamplePolyCBD B = f where                                                 *)
(*     b = BytesToBits B                                                     *)
(*     BitToZ : Bit -> Z q                                                   *)
(*     BitToZ bit = if bit then 1 else 0                                     *)
(*     b' = map BitToZ b                                                     *)
(*     x i = sum [b'@(2 * i * `eta + j) | j <- [0 .. (eta-1)]]               *)
(*     y i = sum [b'@(2 * i * `eta + `eta + j) | j <- [0 .. (eta-1)]]        *)
(*     f = [(x i) - (y i) | i <- [0 .. 255]]                                 *)
(*                                                                           *)
(* The enumerations are not constrained by anything else, so their element   *)
(* type defaults to Integer and the index arithmetic is exact (with [8] it   *)
(* would wrap around, which the equivalence proof would expose).             *)
(* ------------------------------------------------------------------------- *)

let cry_SamplePolyCBD = new_definition
 `cry_SamplePolyCBD eta (B:byte list) : int list =
    let b = cry_BytesToBits B in
    let BitToZ = \bit. if bit then &1 else &0 in
    let b' = MAP BitToZ b in
    let x = \i. cry_zsum (MAP (\j. EL (2 * i * eta + j) b')
                              (cry_range 0 (eta - 1))) in
    let y = \i. cry_zsum (MAP (\j. EL (2 * i * eta + eta + j) b')
                              (cry_range 0 (eta - 1))) in
    MAP (\i. ring_sub (integer_mod_ring 3329) (x i) (y i)) (cry_range 0 255)`;;

(* ------------------------------------------------------------------------- *)
(* BitRev7 : [8] -> [8]                                                      *)
(* BitRev7 i = if i > 255 then error "BitRev7 called with invalid input"     *)
(*     else (reverse i) >> 1                                                 *)
(*                                                                           *)
(* (The error branch is unreachable for an 8-bit i; it becomes ARB.)         *)
(* ------------------------------------------------------------------------- *)

let cry_BitRev7 = new_definition
 `cry_BitRev7 (i:byte) =
    if val i > 255 then ARB else word_ushr (word_reversefields 1 i) 1`;;

(* ------------------------------------------------------------------------- *)
(* XOF : ([34]Byte) -> [inf]Byte                                             *)
(* XOF = SHAKE128::xofBytes                                                  *)
(* ------------------------------------------------------------------------- *)

let cry_XOF = new_definition
 `cry_XOF (B:byte list) = shake128 B`;;

(* ------------------------------------------------------------------------- *)
(* SampleNTT : [34]Byte -> Tq                                                *)
(* SampleNTT B = a_hat' where                                                *)
(*     ctx0 = XOF B                                                          *)
(*     a_hat = take`{256} (filter ctx0)                                      *)
(*     filter: [inf]Byte -> [inf][12]                                        *)
(*     filter XOFSqueeze = a_hat_j where                                     *)
(*         (C # ctx) = XOFSqueeze                                            *)
(*         [C0, C1, C2] = map zext`{12} C                                    *)
(*         d1 = C0 + 256 * (C1 % 16)                                         *)
(*         d2 = (C1 / 16) + 16 * C2                                          *)
(*         a_hat_j = if (d1 < `q) && (d2 < `q) then                          *)
(*                 [d1, d2] # filter ctx                                     *)
(*             else if d1 < `q then                                          *)
(*                 [d1] # filter ctx                                         *)
(*             else if d2 < `q then                                          *)
(*                 [d2] # filter ctx                                         *)
(*             else filter ctx                                               *)
(*     toZq : [12] -> Z q                                                    *)
(*     toZq x = fromInteger (toInteger x)                                    *)
(*     a_hat' = map toZq a_hat                                               *)
(*                                                                           *)
(* The recursive stream function filter is not translated as a recursion:    *)
(* the call on the stream s offers d1 and d2 computed from s 0, s 1, s 2,    *)
(* and recurses on the rest, so filter returns the subsequence of values     *)
(* < q of the candidate sequence d1, d2, d1, d2, ... of the 3-byte groups.   *)
(* That subsequence is defined directly (cry_stream_filter, by the minimal-  *)
(* index construction also used in fips203.ml). CRY_FILTER_EQN in            *)
(* cry_mlkem_proofs.ml proves that it satisfies the recursion equation of    *)
(* filter on every stream with infinitely many candidates < q (on the other  *)
(* streams filter is undefined after the last one), and CRY_FILTER_UNIQUE    *)
(* that it is the only function that does.                                   *)
(* ------------------------------------------------------------------------- *)

let cry_filter_d1 = new_definition
 `cry_filter_d1 (s:num->byte) : 12 word =
    let C0 = (word_zx (s 0):12 word) and C1 = (word_zx (s 1):12 word) in
    word_add C0 (word_mul (word 256) (word_umod C1 (word 16)))`;;

let cry_filter_d2 = new_definition
 `cry_filter_d2 (s:num->byte) : 12 word =
    let C1 = (word_zx (s 1):12 word) and C2 = (word_zx (s 2):12 word) in
    word_add (word_udiv C1 (word 16)) (word_mul (word 16) C2)`;;

let cry_filter_cand = new_definition
 `cry_filter_cand (s:num->byte) n =
    let s' = \i. s(3 * (n DIV 2) + i) in
    if EVEN n then cry_filter_d1 s' else cry_filter_d2 s'`;;

let cry_stream_filter = new_definition
 `cry_stream_filter (p:A->bool) (c:num->A) n =
    c(@j. p(c j) /\ CARD {j' | j' < j /\ p(c j')} = n)`;;

let cry_filter = new_definition
 `cry_filter (s:num->byte) =
    cry_stream_filter (\x:12 word. val x < 3329) (cry_filter_cand s)`;;

let cry_SampleNTT = new_definition
 `cry_SampleNTT (B:byte list) : int list =
    let ctx0 = cry_XOF B in
    let a_hat = list_of_seq (cry_filter ctx0) 256 in
    let toZq = \x:12 word. &(val x) rem &3329 in
    MAP toZq a_hat`;;

(* ------------------------------------------------------------------------- *)
(* NaiveNTT : Rq -> Tq                                                       *)
(* NaiveNTT f = join [[f2i i, f2iPlus1 i] | i <- [0 .. 127]] where           *)
(*     f2i i = sum [f @(2*j) * zeta_term i j | j <- [0 .. 127]]              *)
(*     f2iPlus1 i = sum [f @(2*j+1) * zeta_term i j | j <- [0 .. 127]]       *)
(*     zeta_term i j = zeta ^^ ((2 * BitRev7 i + 1) * j)                     *)
(*                                                                           *)
(* With zeta = 17 : Z q. Since BitRev7 : [8] -> [8], i is a byte, and j is   *)
(* one too because it is multiplied by 2 * BitRev7 i + 1. So the exponent    *)
(* (2 * BitRev7 i + 1) * j is computed modulo 256. That is harmless only     *)
(* because zeta has order 256 in Z q, which the proof has to use.            *)
(* ------------------------------------------------------------------------- *)

let cry_NaiveNTT = new_definition
 `cry_NaiveNTT (f:int list) : int list =
    let zq = integer_mod_ring 3329 in
    let zeta_term = \i:byte j:byte.
      ring_pow zq (&17)
        (val(word_mul (word_add (word_mul (word 2) (cry_BitRev7 i)) (word 1))
                      j)) in
    let f2i = \i:byte.
      cry_zsum (MAP (\j:byte. ring_mul zq (EL (val(word_mul (word 2) j)) f)
                                          (zeta_term i j))
                    (MAP word (cry_range 0 127))) in
    let f2iPlus1 = \i:byte.
      cry_zsum (MAP (\j:byte. ring_mul zq
                       (EL (val(word_add (word_mul (word 2) j) (word 1))) f)
                       (zeta_term i j))
                    (MAP word (cry_range 0 127))) in
    cry_join (MAP (\i. [f2i i; f2iPlus1 i]) (MAP word (cry_range 0 127)))`;;

(* ------------------------------------------------------------------------- *)
(* NaiveNTTInv : Tq -> Rq                                                    *)
(* NaiveNTTInv f_hat = [f_i * 3303 | f_i <- f] where                         *)
(*     f = join [[f2i i, f2iPlus1 i] | i <- [0 .. 127]]                      *)
(*     f2i i = sum [f_hat @(2*j) * zeta_term i j | j <- [0 .. 127]]          *)
(*     f2iPlus1 i = sum [f_hat @(2*j+1) * zeta_term i j | j <- [0 .. 127]]   *)
(*     zeta_term i j = (recip zeta) ^^ ((2 * BitRev7 j + 1) * i)             *)
(*                                                                           *)
(* As in NaiveNTT, i and j are bytes, so the exponent is computed modulo     *)
(* 256; recip zeta has order 256 too.                                        *)
(* ------------------------------------------------------------------------- *)

let cry_NaiveNTTInv = new_definition
 `cry_NaiveNTTInv (f_hat:int list) : int list =
    let zq = integer_mod_ring 3329 in
    let zeta_term = \i:byte j:byte.
      ring_pow zq (ring_inv zq (&17))
        (val(word_mul (word_add (word_mul (word 2) (cry_BitRev7 j)) (word 1))
                      i)) in
    let f2i = \i:byte.
      cry_zsum (MAP (\j:byte. ring_mul zq (EL (val(word_mul (word 2) j)) f_hat)
                                          (zeta_term i j))
                    (MAP word (cry_range 0 127))) in
    let f2iPlus1 = \i:byte.
      cry_zsum (MAP (\j:byte. ring_mul zq
                       (EL (val(word_add (word_mul (word 2) j) (word 1)))
                           f_hat)
                       (zeta_term i j))
                    (MAP word (cry_range 0 127))) in
    let f = cry_join (MAP (\i. [f2i i; f2iPlus1 i])
                          (MAP word (cry_range 0 127))) in
    MAP (\f_i. ring_mul zq f_i (&3303)) f`;;

(* ------------------------------------------------------------------------- *)
(* The fast NTT of the spec (NTT = fast_ntt), with the size of the type-     *)
(* level recursion (length 2^^lv) as a number argument and the constraint    *)
(* guards as a conditional:                                                  *)
(*                                                                           *)
(* fast_ntt v = fast_nttl v 1                                                *)
(* fast_nttl : {lv} (lv >= 2, lv <= 8) => [2^^lv](Z q) -> [8] -> [2^^lv](Z q)*)
(* fast_nttl v k                                                             *)
(*     | lv == 2 => ct_butterfly`{lv,lv-1} v (zeta_expc@k)                   *)
(*     | lv  > 2 => (fast_nttl`{lv-1} s0 (k * 2)) #                          *)
(*                  (fast_nttl`{lv-1} s1 (k * 2 + 1))                        *)
(*                 where                                                     *)
(*                 t = ct_butterfly`{lv,lv-1} v (zeta_expc@k)                *)
(*                 [s0, s1] = split t                                        *)
(* ct_butterfly : {m, hm} (...) => [2^^m](Z q) -> (Z q) -> [2^^m](Z q)       *)
(* ct_butterfly v z = new_v where                                            *)
(*     halflen = 2^^`hm                                                      *)
(*     lower, upper : [2^^hm](Z q)                                           *)
(*     lower@x = v@x + z * v@(x + halflen)                                   *)
(*     upper@x = v@x - z * v@(x + halflen)                                   *)
(*     new_v = lower # upper                                                 *)
(* ------------------------------------------------------------------------- *)

let cry_zeta_expc = new_definition
 `cry_zeta_expc:int list =
     [&1; &1729; &2580; &3289; &2642; &630; &1897; &848; &1062; &1919; &193;
      &797; &2786; &3260; &569; &1746; &296; &2447; &1339; &1476; &3046;
      &56; &2240; &1333; &1426; &2094; &535; &2882; &2393; &2879; &1974;
      &821; &289; &331; &3253; &1756; &1197; &2304; &2277; &2055; &650;
      &1977; &2513; &632; &2865; &33; &1320; &1915; &2319; &1435; &807;
      &452; &1438; &2868; &1534; &2402; &2647; &2617; &1481; &648; &2474;
      &3110; &1227; &910; &17; &2761; &583; &2649; &1637; &723; &2288;
      &1100; &1409; &2662; &3281; &233; &756; &2156; &3015; &3050; &1703;
      &1651; &2789; &1789; &1847; &952; &1461; &2687; &939; &2308; &2437;
      &2388; &733; &2337; &268; &641; &1584; &2298; &2037; &3220; &375;
      &2549; &2090; &1645; &1063; &319; &2773; &757; &2099; &561; &2466;
      &2594; &2804; &1092; &403; &1026; &1143; &2150; &2775; &886; &1722;
      &1212; &1874; &1029; &2110; &2935; &885; &2154]`;;

let cry_ct_butterfly = new_definition
 `cry_ct_butterfly hm (v:int list) (z:int) =
    let zq = integer_mod_ring 3329 in
    let halflen = 2 EXP hm in
    let lower = list_of_seq (\x. ring_add zq (EL x v)
                                   (ring_mul zq z (EL (x + halflen) v)))
                            halflen
    and upper = list_of_seq (\x. ring_sub zq (EL x v)
                                   (ring_mul zq z (EL (x + halflen) v)))
                            halflen in
    APPEND lower upper`;;

let cry_fast_nttl = define
 `cry_fast_nttl lv (v:int list) (k:byte) =
    if lv <= 2 then cry_ct_butterfly (lv - 1) v (EL (val k) cry_zeta_expc)
    else
      let t = cry_ct_butterfly (lv - 1) v (EL (val k) cry_zeta_expc) in
      let s0 = EL 0 (cry_split 2 t) and s1 = EL 1 (cry_split 2 t) in
      APPEND (cry_fast_nttl (lv - 1) s0 (word_mul k (word 2)))
             (cry_fast_nttl (lv - 1) s1
                (word_add (word_mul k (word 2)) (word 1)))`;;

let cry_fast_ntt = new_definition
 `cry_fast_ntt (v:int list) = cry_fast_nttl 8 v (word 1)`;;

let cry_NTT = new_definition
 `cry_NTT = cry_fast_ntt`;;

(* ------------------------------------------------------------------------- *)
(* The fast inverse NTT of the spec (NTTInv = fast_invntt), translated like  *)
(* fast_ntt, and the NTTs of vectors:                                        *)
(*                                                                           *)
(* fast_invnttl : {lv} (lv >= 2, lv <= 8) =>                                 *)
(*     [2^^lv](Z q) -> [8] -> [2^^lv](Z q)                                   *)
(* fast_invnttl v k                                                          *)
(*     | lv == 2 => gs_butterfly`{lv,lv-1} v (zeta_expc@k)                   *)
(*     | lv  > 2 => gs_butterfly`{lv,lv-1} t (zeta_expc@k) where             *)
(*         [s0, s1] = split v                                                *)
(*         t = (fast_invnttl`{lv-1} s0 (k * 2 + 1)) #                        *)
(*             (fast_invnttl`{lv-1} s1 (k * 2))                              *)
(* gs_butterfly : {m, hm} (...) => [2^^m](Z q) -> (Z q) -> [2^^m](Z q)       *)
(* gs_butterfly v z = new_v where                                            *)
(*     halflen = 2^^`hm                                                      *)
(*     lower, upper : [2^^hm](Z q)                                           *)
(*     lower@x = v@x  + v@(x + halflen)                                      *)
(*     upper@x = z * (v@(x + halflen) - v@x)                                 *)
(*     new_v = lower # upper                                                 *)
(* fast_invntt : Tq -> Rq                                                    *)
(* fast_invntt v = mul_recip128 (fast_invnttl v 1) where                     *)
(*     recip_128_modq = (recip 128) : (Z q)                                  *)
(*     mul_recip128 : Tq -> Tq                                               *)
(*     mul_recip128 v' = [ v'@x * recip_128_modq | x <- [0 .. <n] ]          *)
(*                                                                           *)
(* NTT_Vec v = map NTT v                                                     *)
(* NTTInv_Vec v = map NTTInv v                                               *)
(* ------------------------------------------------------------------------- *)

let cry_gs_butterfly = new_definition
 `cry_gs_butterfly hm (v:int list) (z:int) =
    let zq = integer_mod_ring 3329 in
    let halflen = 2 EXP hm in
    let lower = list_of_seq (\x. ring_add zq (EL x v) (EL (x + halflen) v))
                            halflen
    and upper = list_of_seq (\x. ring_mul zq z
                                   (ring_sub zq (EL (x + halflen) v) (EL x v)))
                            halflen in
    APPEND lower upper`;;

let cry_fast_invnttl = define
 `cry_fast_invnttl lv (v:int list) (k:byte) =
    if lv <= 2 then cry_gs_butterfly (lv - 1) v (EL (val k) cry_zeta_expc)
    else
      let s0 = EL 0 (cry_split 2 v) and s1 = EL 1 (cry_split 2 v) in
      let t = APPEND (cry_fast_invnttl (lv - 1) s0
                        (word_add (word_mul k (word 2)) (word 1)))
                     (cry_fast_invnttl (lv - 1) s1 (word_mul k (word 2))) in
      cry_gs_butterfly (lv - 1) t (EL (val k) cry_zeta_expc)`;;

let cry_fast_invntt = new_definition
 `cry_fast_invntt (v:int list) =
    let zq = integer_mod_ring 3329 in
    let recip_128_modq = ring_inv zq (&128) in
    let mul_recip128 =
      \v'. MAP (\x. ring_mul zq (EL x v') recip_128_modq)
               (cry_range 0 (256 - 1)) in
    mul_recip128 (cry_fast_invnttl 8 v (word 1))`;;

let cry_NTTInv = new_definition
 `cry_NTTInv = cry_fast_invntt`;;

let cry_NTT_Vec = new_definition
 `cry_NTT_Vec (v:(int list) list) = MAP cry_NTT v`;;

let cry_NTTInv_Vec = new_definition
 `cry_NTTInv_Vec (v:(int list) list) = MAP cry_NTTInv v`;;

(* ------------------------------------------------------------------------- *)
(* BaseCaseMultiply : (Z q) -> (Z q) -> (Z q) -> (Z q) -> (Z q) -> [2](Z q)  *)
(* BaseCaseMultiply a0 a1 b0 b1 gamma = [c0, c1]                             *)
(*   where                                                                   *)
(*     c0 = a0 * b0 + a1 * b1 * gamma                                        *)
(*     c1 = a0 * b1 + a1 * b0                                                *)
(* MultiplyNTTs : Tq -> Tq -> Tq                                             *)
(* MultiplyNTTs f_hat g_hat = join h_hat where                               *)
(*     h_hat = [ BaseCaseMultiply                                            *)
(*         (f_hat @(2*i)) (f_hat @(2*i+1)) (g_hat @(2*i)) (g_hat @(2*i+1))   *)
(*         (zeta ^^(2 * BitRev7 i + 1))                                      *)
(*     | i <- [0 .. 127] ]                                                   *)
(* ------------------------------------------------------------------------- *)

let cry_BaseCaseMultiply = new_definition
 `cry_BaseCaseMultiply a0 a1 b0 b1 (gamma:int) =
    let zq = integer_mod_ring 3329 in
    let c0 = ring_add zq (ring_mul zq a0 b0)
                         (ring_mul zq (ring_mul zq a1 b1) gamma)
    and c1 = ring_add zq (ring_mul zq a0 b1) (ring_mul zq a1 b0) in
    [c0; c1]`;;

let cry_MultiplyNTTs = new_definition
 `cry_MultiplyNTTs (f_hat:int list) (g_hat:int list) : int list =
    let h_hat =
      MAP (\i:byte.
             cry_BaseCaseMultiply
               (EL (val(word_mul (word 2) i)) f_hat)
               (EL (val(word_add (word_mul (word 2) i) (word 1))) f_hat)
               (EL (val(word_mul (word 2) i)) g_hat)
               (EL (val(word_add (word_mul (word 2) i) (word 1))) g_hat)
               (ring_pow (integer_mod_ring 3329) (&17)
                  (val(word_add (word_mul (word 2) (cry_BitRev7 i))
                                (word 1)))))
          (MAP word (cry_range 0 127)) in
    cry_join h_hat`;;

(* ------------------------------------------------------------------------- *)
(* Sums and differences of polynomials and vectors (Cryptol's + and - on     *)
(* sequences are elementwise; Rq and Tq are both [n](Z q)), and the dot      *)
(* products:                                                                 *)
(*                                                                           *)
(* dotVecVec v1 v2 = sum (zipWith (x) v1 v2)        where (x) = MultiplyNTTs *)
(* dotMatVec matrix vector = [dotVecVec v1 vector | v1 <- matrix]            *)
(* ------------------------------------------------------------------------- *)

let cry_tq_add = new_definition
 `cry_tq_add (a:int list) (b:int list) =
    MAP2 (ring_add (integer_mod_ring 3329)) a b`;;

let cry_tq_sub = new_definition
 `cry_tq_sub (a:int list) (b:int list) =
    MAP2 (ring_sub (integer_mod_ring 3329)) a b`;;

let cry_vec_add = new_definition
 `cry_vec_add (u:(int list) list) (v:(int list) list) = MAP2 cry_tq_add u v`;;

let cry_tq_zero = new_definition
 `cry_tq_zero:int list = list_of_seq (\i. &0) 256`;;

let cry_dotVecVec = new_definition
 `cry_dotVecVec (v1:(int list) list) (v2:(int list) list) =
    ITLIST cry_tq_add (MAP2 cry_MultiplyNTTs v1 v2) cry_tq_zero`;;

let cry_dotMatVec = new_definition
 `cry_dotMatVec (matrixv:((int list) list) list) (vectorv:(int list) list) =
    MAP (\v1. cry_dotVecVec v1 vectorv) matrixv`;;

(* ------------------------------------------------------------------------- *)
(* PRF : {eta} (2 <= eta, eta <= 3) => [32]Byte -> Byte -> [64 * eta]Byte    *)
(* PRF s b = SHAKE256::xofBytes`{8 * 64 * eta} (s # [b])                     *)
(* G : {ginl} (fin ginl) => [ginl]Byte -> ([32]Byte, [32]Byte)               *)
(* G c = (a, b) where                                                        *)
(*     [a, b] = split (SHA3_512::hashBytes c)                                *)
(* ------------------------------------------------------------------------- *)

let cry_PRF = new_definition
 `cry_PRF eta (s:byte list) (b:byte) =
    list_of_seq (shake256 (APPEND s [b])) (64 * eta)`;;

let cry_G = new_definition
 `cry_G (c:byte list) =
    let ab = cry_split 2 (sha3_512 c) in EL 0 ab,EL 1 ab`;;

(* ------------------------------------------------------------------------- *)
(* H : {hinl} (fin hinl) => [hinl]Byte -> [32]Byte                           *)
(* H s = SHA3_256::hashBytes s                                               *)
(* J : {hinl} (fin hinl) => [hinl]Byte -> [32]Byte                           *)
(* J s = SHAKE256::xofBytes`{8 * 32} s                                       *)
(* ------------------------------------------------------------------------- *)

let cry_H = new_definition
 `cry_H (s:byte list) = sha3_256 s`;;

let cry_J = new_definition
 `cry_J (s:byte list) = list_of_seq (shake256 s) 32`;;

(* ------------------------------------------------------------------------- *)
(* K-PKE KeyGen (K_PKE::KeyGen; parameters k and eta_1 as numbers):          *)
(*                                                                           *)
(* KeyGen d = (ekPKE, dkPKE) where                                           *)
(*     (rho, sigma) = G (d # [`(k)])                                         *)
(*     A_hat = [[ SampleNTT (rho # [j] # [i])                                *)
(*         | j <- [0 .. k-1]]                                                *)
(*         | i <- [0 .. k-1]]                                                *)
(*     s = [SamplePolyCBD`{eta_1} (PRF sigma N) | N <- [0 .. k-1]]           *)
(*     e = [SamplePolyCBD`{eta_1} (PRF sigma N) | N <- [k .. 2 * k - 1]]     *)
(*     s_hat = NTT_Vec s                                                     *)
(*     e_hat = NTT_Vec e                                                     *)
(*     t_hat = (dotMatVec A_hat s_hat) + e_hat                               *)
(*     ekPKE = (ByteEncode12_Vec t_hat) # rho                                *)
(*     dkPKE = ByteEncode12_Vec s_hat                                        *)
(*                                                                           *)
(* (In the Cryptol text rho and sigma are the Greek letters U+03C1 and       *)
(* U+03C3, and the dot product uses the infix (x) = U+00D7 for MultiplyNTTs.)*)
(* ------------------------------------------------------------------------- *)

let cry_K_PKE_KeyGen = new_definition
 `cry_K_PKE_KeyGen k eta_1 (d:byte list) =
    let rho,sigma = cry_G (APPEND d [word k]) in
    let A_hat =
      MAP (\i. MAP (\j. cry_SampleNTT (APPEND rho (APPEND [j] [i])))
                   (MAP word (cry_range 0 (k - 1))))
          (MAP word (cry_range 0 (k - 1))) in
    let s = MAP (\N. cry_SamplePolyCBD eta_1 (cry_PRF eta_1 sigma N))
                (MAP word (cry_range 0 (k - 1)))
    and e = MAP (\N. cry_SamplePolyCBD eta_1 (cry_PRF eta_1 sigma N))
                (MAP word (cry_range k (2 * k - 1))) in
    let s_hat = cry_NTT_Vec s
    and e_hat = cry_NTT_Vec e in
    let t_hat = cry_vec_add (cry_dotMatVec A_hat s_hat) e_hat in
    let ekPKE = APPEND (cry_ByteEncode12_Vec t_hat) rho
    and dkPKE = cry_ByteEncode12_Vec s_hat in
    ekPKE,dkPKE`;;

(* ------------------------------------------------------------------------- *)
(* K-PKE Encrypt (K_PKE::Encrypt):                                           *)
(*                                                                           *)
(* Encrypt ekPKE m r = c where                                               *)
(*     t_hat = ByteDecode12_Vec (ekPKE @@[0 .. 384*k - 1])                   *)
(*     rho = ekPKE @@[384*k .. 384*k + 32 - 1]                               *)
(*     A_hat = [[ SampleNTT (rho # [j] # [i])                                *)
(*         | j <- [0 .. k-1]]                                                *)
(*         | i <- [0 .. k-1]]                                                *)
(*     y = [SamplePolyCBD`{eta_1} (PRF r N)                                  *)
(*         | N <- [0 .. k-1]]                                                *)
(*     e1 = [SamplePolyCBD`{eta_2} (PRF r N)                                 *)
(*         | N <- [k .. 2 * k - 1]]                                          *)
(*     e2 = SamplePolyCBD`{eta_2} (PRF r (2 * `k))                           *)
(*     y_hat = NTT_Vec y                                                     *)
(*     u = NTTInv_Vec (dotMatVec (transpose A_hat) y_hat) + e1               *)
(*     mu = Decompress_Vec`{1} (ByteDecode`{1} m)                            *)
(*     v = (NTTInv (dotVecVec t_hat y_hat)) + e2 + mu                        *)
(*     c1 = ByteEncode_Vec`{d_u} (Compress_Mat`{d_u} u)                      *)
(*     c2 = ByteEncode`{d_v} (Compress_Vec`{d_v} v)                          *)
(*     c = c1 # c2                                                           *)
(* ------------------------------------------------------------------------- *)

let cry_K_PKE_Encrypt = new_definition
 `cry_K_PKE_Encrypt (du_t:DU->bool) (dv_t:DV->bool) k eta_1 eta_2
                    (ekPKE:byte list) (m:byte list) (r:byte list) =
    let t_hat = cry_ByteDecode12_Vec k
                  (cry_atat ekPKE (cry_range 0 (384 * k - 1))) in
    let rho = cry_atat ekPKE (cry_range (384 * k) (384 * k + 32 - 1)) in
    let A_hat =
      MAP (\i. MAP (\j. cry_SampleNTT (APPEND rho (APPEND [j] [i])))
                   (MAP word (cry_range 0 (k - 1))))
          (MAP word (cry_range 0 (k - 1))) in
    let y = MAP (\N. cry_SamplePolyCBD eta_1 (cry_PRF eta_1 r N))
                (MAP word (cry_range 0 (k - 1))) in
    let e1 = MAP (\N. cry_SamplePolyCBD eta_2 (cry_PRF eta_2 r N))
                 (MAP word (cry_range k (2 * k - 1))) in
    let e2 = cry_SamplePolyCBD eta_2 (cry_PRF eta_2 r (word(2 * k))) in
    let y_hat = cry_NTT_Vec y in
    let u = cry_vec_add
              (cry_NTTInv_Vec (cry_dotMatVec (cry_transpose k A_hat) y_hat))
              e1 in
    let mu = cry_Decompress_Vec (cry_ByteDecode m:(1 word) list) in
    let v = cry_tq_add (cry_tq_add (cry_NTTInv (cry_dotVecVec t_hat y_hat))
                                   e2) mu in
    let c1 = cry_ByteEncode_Vec (cry_Compress_Mat u:((DU word) list) list) in
    let c2 = cry_ByteEncode (cry_Compress_Vec v:(DV word) list) in
    let c = APPEND c1 c2 in
    c`;;

(* ------------------------------------------------------------------------- *)
(* K-PKE Decrypt (K_PKE::Decrypt):                                           *)
(*                                                                           *)
(* Decrypt dkPKE c = m where                                                 *)
(*     c1 = c @@[0 .. 32 * d_u * k - 1]                                      *)
(*     c2 = c @@[32 * d_u * k .. 32 * (d_u * k + d_v) - 1]                   *)
(*     u' = Decompress_Mat`{d_u} (ByteDecode_Vec`{d_u} c1)                   *)
(*     v' = Decompress_Vec`{d_v} (ByteDecode`{d_v} c2)                       *)
(*     s_hat = ByteDecode12_Vec dkPKE                                        *)
(*     w = v' - NTTInv (dotVecVec s_hat (NTT_Vec u'))                        *)
(*     m = ByteEncode`{1} (Compress_Vec`{1} w)                               *)
(* ------------------------------------------------------------------------- *)

let cry_K_PKE_Decrypt = new_definition
 `cry_K_PKE_Decrypt (du_t:DU->bool) (dv_t:DV->bool) k
                    (dkPKE:byte list) (c:byte list) =
    let c1 = cry_atat c (cry_range 0 (32 * dimindex(:DU) * k - 1)) in
    let c2 = cry_atat c (cry_range (32 * dimindex(:DU) * k)
                         (32 * (dimindex(:DU) * k + dimindex(:DV)) - 1)) in
    let u' = cry_Decompress_Mat
               (cry_ByteDecode_Vec k c1:((DU word) list) list) in
    let v' = cry_Decompress_Vec (cry_ByteDecode c2:(DV word) list) in
    let s_hat = cry_ByteDecode12_Vec k dkPKE in
    let w = cry_tq_sub v'
              (cry_NTTInv (cry_dotVecVec s_hat (cry_NTT_Vec u'))) in
    let m = cry_ByteEncode (cry_Compress_Vec w:(1 word) list) in
    m`;;

(* ------------------------------------------------------------------------- *)
(* The internal ML-KEM functions:                                            *)
(*                                                                           *)
(* KeyGen_internal d z = (ek, dk) where                                      *)
(*   (ekPKE, dkPKE) = K_PKE::KeyGen d                                        *)
(*   ek = ekPKE                                                              *)
(*   dk = dkPKE # ek # (H ek) # z                                            *)
(* Encaps_internal ek m = (K, c) where                                       *)
(*   (K, r) = G (m # (H ek))                                                 *)
(*   c = K_PKE::Encrypt ek m r                                               *)
(* Decaps_internal dk c = K where                                            *)
(*     dkPKE = dk @@ [0 .. 384*k - 1]                                        *)
(*     ekPKE = dk @@ [384*k .. 768*k + 32 - 1]                               *)
(*     h = dk @@ [768*k + 32 .. 768*k + 64 - 1]                              *)
(*     z = dk @@ [768*k + 64 .. 768*k + 96 - 1]                              *)
(*     m' = K_PKE::Decrypt dkPKE c                                           *)
(*     (K', r') = G (m' # h)                                                 *)
(*     Kbar = J (z # c)                                                      *)
(*     c' = K_PKE::Encrypt ekPKE m' r'                                       *)
(*     K = if (c != c') then                                                 *)
(*             Kbar                                                          *)
(*         else                                                              *)
(*             K'                                                            *)
(* ------------------------------------------------------------------------- *)

let cry_KeyGen_internal = new_definition
 `cry_KeyGen_internal k eta_1 (d:byte list) (z:byte list) =
    let ekPKE,dkPKE = cry_K_PKE_KeyGen k eta_1 d in
    let ek = ekPKE in
    let dk = APPEND dkPKE (APPEND ek (APPEND (cry_H ek) z)) in
    ek,dk`;;

let cry_Encaps_internal = new_definition
 `cry_Encaps_internal (du_t:DU->bool) (dv_t:DV->bool) k eta_1 eta_2
                      (ek:byte list) (m:byte list) =
    let K,r = cry_G (APPEND m (cry_H ek)) in
    let c = cry_K_PKE_Encrypt du_t dv_t k eta_1 eta_2 ek m r in
    K,c`;;

let cry_Decaps_internal = new_definition
 `cry_Decaps_internal (du_t:DU->bool) (dv_t:DV->bool) k eta_1 eta_2
                      (dk:byte list) (c:byte list) =
    let dkPKE = cry_atat dk (cry_range 0 (384 * k - 1)) in
    let ekPKE = cry_atat dk (cry_range (384 * k) (768 * k + 32 - 1)) in
    let h = cry_atat dk (cry_range (768 * k + 32) (768 * k + 64 - 1)) in
    let z = cry_atat dk (cry_range (768 * k + 64) (768 * k + 96 - 1)) in
    let m' = cry_K_PKE_Decrypt du_t dv_t k dkPKE c in
    let K',r' = cry_G (APPEND m' h) in
    let Kbar = cry_J (APPEND z c) in
    let c' = cry_K_PKE_Encrypt du_t dv_t k eta_1 eta_2 ekPKE m' r' in
    let K = if ~(c = c') then Kbar else K' in
    K`;;

(* ------------------------------------------------------------------------- *)
(* The ML-KEM API, which takes the randomness as Option arguments:           *)
(*                                                                           *)
(* KeyGen : Option ([32]Byte) -> Option ([32]Byte)                           *)
(*     -> (EncapsulationKey, DecapsulationKey)                               *)
(* KeyGen d z = (ek, dk) where                                               *)
(*     d' = case d of                                                        *)
(*         None -> error "Random bit generation failed; ..."                 *)
(*         Some _d -> _d                                                     *)
(*     z' = case z of                                                        *)
(*         None -> error "Random bit generation failed; ..."                 *)
(*         Some _z -> _z                                                     *)
(*     (ek, dk) = KeyGen_internal d' z'                                      *)
(* encapsulationKeyCheck : EncapsulationKey -> Bool                          *)
(* encapsulationKeyCheck ek = modulusCheck where                             *)
(*     test = ByteEncode12_Vec (ByteDecode12_Vec (ek @@ [0..384 * k - 1]))   *)
(*     modulusCheck = test == (ek @@ [0..384 * k - 1])                       *)
(* Encaps : EncapsulationKey -> Option ([32]Byte)                            *)
(*     -> (SharedSecretKey, Ciphertext)                                      *)
(* Encaps ek m = (K, c) where                                                *)
(*     m' = case m of                                                        *)
(*         None -> error "Random bit generation failed; ..."                 *)
(*         Some _m -> _m                                                     *)
(*     (K, c) = Encaps_internal ek m'                                        *)
(* decapsulationInputCheck : DecapsulationKey -> Ciphertext -> Bool          *)
(* decapsulationInputCheck dk c = decapsulationKeyCheck dk                   *)
(* decapsulationKeyCheck : DecapsulationKey -> Bool                          *)
(* decapsulationKeyCheck dk = hash_check where                               *)
(*     test = H (dk @@ [384*k .. 768*k + 32 - 1])                            *)
(*     hash_check = test == (dk @@ [768*k + 32 .. 768*k + 64 - 1])           *)
(* Decaps : DecapsulationKey -> Ciphertext -> SharedSecretKey                *)
(* Decaps = Decaps_internal                                                  *)
(*                                                                           *)
(* (decapsulationKeyCheck is defined first, since HOL Light needs that. The  *)
(* key-pair check keyPairCheck, which tests a key pair with these checks     *)
(* and an encapsulation and decapsulation, is not translated.)               *)
(* ------------------------------------------------------------------------- *)

let cry_KeyGen = new_definition
 `cry_KeyGen k eta_1 (d:(byte list)option) (z:(byte list)option) =
    let d' = (match d with NONE -> ARB | SOME _d -> _d) in
    let z' = (match z with NONE -> ARB | SOME _z -> _z) in
    let ek,dk = cry_KeyGen_internal k eta_1 d' z' in
    ek,dk`;;

let cry_encapsulationKeyCheck = new_definition
 `cry_encapsulationKeyCheck k (ek:byte list) <=>
    let test = cry_ByteEncode12_Vec
                (cry_ByteDecode12_Vec k
                  (cry_atat ek (cry_range 0 (384 * k - 1)))) in
    let modulusCheck = (test = cry_atat ek (cry_range 0 (384 * k - 1))) in
    modulusCheck`;;

let cry_Encaps = new_definition
 `cry_Encaps (du_t:DU->bool) (dv_t:DV->bool) k eta_1 eta_2
             (ek:byte list) (m:(byte list)option) =
    let m' = (match m with NONE -> ARB | SOME _m -> _m) in
    let K,c = cry_Encaps_internal du_t dv_t k eta_1 eta_2 ek m' in
    K,c`;;

let cry_decapsulationKeyCheck = new_definition
 `cry_decapsulationKeyCheck k (dk:byte list) <=>
    let test = cry_H (cry_atat dk (cry_range (384 * k) (768 * k + 32 - 1))) in
    let hash_check =
      (test = cry_atat dk (cry_range (768 * k + 32) (768 * k + 64 - 1))) in
    hash_check`;;

let cry_decapsulationInputCheck = new_definition
 `cry_decapsulationInputCheck k (dk:byte list) (c:byte list) <=>
    cry_decapsulationKeyCheck k dk`;;

let cry_Decaps = new_definition
 `cry_Decaps = cry_Decaps_internal`;;
