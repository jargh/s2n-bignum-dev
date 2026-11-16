(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Huffman-coded literals in the Zstandard format, per RFC 8878: FSE table   *)
(* descriptions and FSE decoding tables (section 4.1), Huffman tree          *)
(* descriptions and Huffman-coded streams (section 4.2), and literals in one *)
(* stream or in four (section 3.1.1.3.1).                                    *)
(*                                                                           *)
(* The definitions take a flag zstd. With zstd false they follow the RFC,    *)
(* and with zstd true they describe what zstd 1.5.7 accepts, which differs   *)
(* from the RFC as follows.                                                  *)
(*                                                                           *)
(* - Codes may have up to 12 bits (HUF_TABLELOG_MAX), not 11 (4.2.1).        *)
(*                                                                           *)
(* - zstd's reading of an FSE table description (FSE_readNCount) reads 0     *)
(*   bits past the end of its input, and when it refills its 32-bit window   *)
(*   a position past the end wraps around, modulo 32, into the last 4 bytes; *)
(*   only the final position is checked against the end. So zstd accepts     *)
(*   some descriptions that run past the end of their input, by reading      *)
(*   some bits twice.                                                        *)
(*                                                                           *)
(* - The FSE table description of the Huffman weights may describe up to     *)
(*   256 symbols, provided that the decoding tables fit in zstd's workspace: *)
(*   the last symbol is at most 11 if Accuracy_Log is 6 and at most 91 if it *)
(*   is 5. The RFC leaves the number of symbols to the context (4.1.1); here *)
(*   it is at most 12, for the weights 0 to 11.                              *)
(*                                                                           *)
(* - zstd rejects four Huffman-coded streams (3.1.1.3.1.6) for fewer than 6  *)
(*   bytes. Its fast decoding of four streams, which it uses by default for  *)
(*   tables of 11 bits and streams of at least 8 bytes, does not check that  *)
(*   the streams are consumed exactly, and so accepts many inputs that both  *)
(*   readings reject; the definitions here follow its other decoding, with   *)
(*   the flag HUF_flags_disableFast.                                         *)
(*                                                                           *)
(* Where the RFC is silent, both follow zstd: the FSE-compressed weights     *)
(* must have bits for both initial states, and some symbol must have weight  *)
(* 1, taking "This power of 2 gives Max_Number_of_Bits the depth of the      *)
(* current tree" (4.2.1) as a requirement.                                   *)
(* ========================================================================= *)

needs "Library/words.ml";;
needs "Library/bitsize.ml";;

(* ------------------------------------------------------------------------- *)
(* Bits. A forward bitstream (an FSE table description) is read from the     *)
(* least significant bit of its first byte, and numbers in it start with     *)
(* their least significant bit. Bits past the end of the list read as 0.     *)
(* zstd_sublist l a n is the n bytes of l from offset a.                     *)
(* ------------------------------------------------------------------------- *)

let zstd_bit = new_definition
 `zstd_bit (l:byte list) i <=>
    i < 8 * LENGTH l /\ bit (i MOD 8) (EL (i DIV 8) l)`;;

let zstd_bits = define
 `(zstd_bits (l:byte list) p 0 = 0) /\
  (zstd_bits l p (SUC n) = bitval(zstd_bit l p) + 2 * zstd_bits l (p + 1) n)`;;

let zstd_sublist = new_definition
 `zstd_sublist (l:byte list) a n = list_of_seq (\i. EL (a + i) l) n`;;

(* ------------------------------------------------------------------------- *)
(* Backward bitstreams (sections 4.1 and 4.2): the last byte holds a 1 bit   *)
(* above the useful bits, which are read from the most significant down.     *)
(* zstd_end st r says that the stream st has r useful bits, and              *)
(* zstd_back st q k is the number in the k bits below position q, with 0     *)
(* bits below position 0.                                                    *)
(* ------------------------------------------------------------------------- *)

let zstd_end = new_definition
 `zstd_end (st:byte list) r <=>
    ~(st = []) /\ 8 * (LENGTH st - 1) <= r /\ zstd_bit st r /\
    (!i. r < i ==> ~zstd_bit st i)`;;

let zstd_back = new_definition
 `zstd_back (st:byte list) q k = (2 EXP k * zstd_bits st 0 q) DIV 2 EXP q`;;

(* ------------------------------------------------------------------------- *)
(* FSE table descriptions (section 4.1.1). With pts probability points left, *)
(* a probability is coded by a value from 0 to pts + 1 in bitsize(pts + 1)   *)
(* bits, or one bit fewer for the small values (Table 20); fse_field gives   *)
(* the value and the position after it. The value v stands for the           *)
(* probability v - 1, where -1 means "less than 1" and uses one point.       *)
(* ------------------------------------------------------------------------- *)

let fse_field = new_definition
 `fse_field (l:byte list) pts p =
    let nb = bitsize(pts + 1) in
    let small = 2 EXP nb - (pts + 2) in
    let v = zstd_bits l p nb in
    if v MOD 2 EXP (nb - 1) < small then (v MOD 2 EXP (nb - 1),p + nb - 1)
    else if v < 2 EXP (nb - 1) then (v,p + nb)
    else (v - small,p + nb)`;;

let fse_points = new_definition
 `fse_points v = if v = 0 then 1 else v - 1`;;

(* The RFC reading requires the description to lie within its input l.       *)
(* zstd reads 0 bits past the end of l, and when it refills its window,      *)
(* after a probability, after a run of repeat flags and after every 12       *)
(* repeat flags of 3, a position past the end of l (or of the first 8 bytes  *)
(* of l padded with 0 bytes, if l is shorter) wraps around into the last 32  *)
(* bits.                                                                     *)

let fse_inside = new_definition
 `fse_inside zstd (l:byte list) q <=> zstd \/ q <= 8 * LENGTH l`;;

let fse_reload = new_definition
 `fse_reload zstd (l:byte list) p =
    let w = 8 * MAX (LENGTH l) 8 in
    if zstd /\ w <= p then w - 32 + (p - w) MOD 32 else p`;;

(* A probability 0 is followed by 2-bit repeat flags, each adding that many  *)
(* probabilities 0, up to and including the first that is not 3:             *)
(* fse_zeros zstd l (k,z,p) (z',q) when the flags from p to q - 1 add        *)
(* z' - z probabilities 0, k counting the flags 3 so far modulo 12.          *)

let FSE_ZEROS_RULES,FSE_ZEROS_INDUCT,FSE_ZEROS_CASES = new_inductive_definition
 `(!k z p.
        zstd_bits l p 2 < 3 /\ fse_inside zstd l (p + 2)
        ==> fse_zeros zstd (l:byte list) (k,z,p)
                      (z + zstd_bits l p 2,fse_reload zstd l (p + 2))) /\
  (!k z p r.
        zstd_bits l p 2 = 3 /\ fse_inside zstd l (p + 2) /\ k < 11 /\
        fse_zeros zstd l (k + 1,z + 3,p + 2) r
        ==> fse_zeros zstd l (k,z,p) r) /\
  (!z p r.
        zstd_bits l p 2 = 3 /\ fse_inside zstd l (p + 2) /\
        fse_zeros zstd l (0,z + 3,fse_reload zstd l (p + 2)) r
        ==> fse_zeros zstd l (11,z,p) r)`;;

(* fse_counts zstd l n (pts,cs,p) (cs',q) when the bits from p to q - 1      *)
(* extend the probabilities cs to cs', using up the pts points left, with at *)
(* most n probabilities in all.                                              *)

let FSE_COUNTS_RULES,FSE_COUNTS_INDUCT,FSE_COUNTS_CASES =
  new_inductive_definition
 `(!pts cs p v q.
        LENGTH cs < n /\ fse_field l pts p = (v,q) /\ fse_inside zstd l q /\
        fse_points v = pts
        ==> fse_counts zstd (l:byte list) n (pts,cs,p)
                       (APPEND cs [&v - &1:int],q)) /\
  (!pts cs p v q r.
        LENGTH cs < n /\ fse_field l pts p = (v,q) /\ fse_inside zstd l q /\
        ~(v = 1) /\ fse_points v < pts /\
        fse_counts zstd l n
          (pts - fse_points v,APPEND cs [&v - &1],fse_reload zstd l q) r
        ==> fse_counts zstd l n (pts,cs,p) r) /\
  (!pts cs p q z q' r.
        LENGTH cs < n /\ fse_field l pts p = (1,q) /\ fse_inside zstd l q /\
        fse_zeros zstd l (0,0,fse_reload zstd l q) (z,q') /\
        fse_counts zstd l n (pts,APPEND cs (REPLICATE (z + 1) (&0)),q') r
        ==> fse_counts zstd l n (pts,cs,p) r)`;;

(* The description at the start of l: Accuracy_Log alog, at most maxalog,    *)
(* and the probabilities cs of the symbols 0, 1, ..., using m bytes.         *)

let fse_ncount = new_definition
 `fse_ncount zstd maxalog n (l:byte list) (cs:int list,alog,m) <=>
    alog = zstd_bits l 0 4 + 5 /\ alog <= maxalog /\
    ?q. fse_counts zstd l n (2 EXP alog,[],4) (cs,q) /\
        q <= 8 * LENGTH l /\ m = (q + 7) DIV 8`;;

(* ------------------------------------------------------------------------- *)
(* FSE decoding tables (section 4.1.1), with 2^alog states. The symbols      *)
(* with probability -1 take one state each, from the last state down; the    *)
(* others take as many states as their probability, in order of symbol, the  *)
(* states being visited from 0 in steps of fse_step alog modulo 2^alog,      *)
(* skipping those already taken. The k-th state of a symbol of probability c *)
(* (1 for -1), counting from 0 in increasing order, has the next-state       *)
(* number c + k, which gives its Number_of_Bits and Baseline (Table 21).     *)
(* ------------------------------------------------------------------------- *)

let fse_step = new_definition
 `fse_step alog = 2 EXP alog DIV 2 + 2 EXP alog DIV 8 + 3`;;

let fse_lowprob = new_definition
 `fse_lowprob (cs:int list) =
    FILTER (\s. EL s cs = -- &1) (list_of_seq (\s. s) (LENGTH cs))`;;

let fse_spread = new_definition
 `fse_spread (cs:int list) alog =
    let low = fse_lowprob cs in
    let cells = FILTER (\u. u < 2 EXP alog - LENGTH low)
                  (list_of_seq (\j. (j * fse_step alog) MOD 2 EXP alog)
                               (2 EXP alog)) in
    let syms = ITLIST APPEND
                 (list_of_seq
                    (\s. REPLICATE (num_of_int(max (EL s cs) (&0))) s)
                    (LENGTH cs)) [] in
    APPEND (ZIP cells syms)
           (ZIP (list_of_seq (\j. 2 EXP alog - 1 - j) (LENGTH low)) low)`;;

let fse_symbol = new_definition
 `fse_symbol cs alog u = ASSOC u (fse_spread cs alog)`;;

let fse_next = new_definition
 `fse_next (cs:int list) alog u =
    let s = fse_symbol cs alog u in
    (if EL s cs = -- &1 then 1 else num_of_int(EL s cs)) +
    CARD {v | v < u /\ fse_symbol cs alog v = s}`;;

let fse_nbits = new_definition
 `fse_nbits cs alog u = (alog + 1) - bitsize(fse_next cs alog u)`;;

let fse_base = new_definition
 `fse_base cs alog u =
    2 EXP fse_nbits cs alog u * fse_next cs alog u - 2 EXP alog`;;

(* ------------------------------------------------------------------------- *)
(* FSE-compressed Huffman weights (section 4.2.1.2): after the FSE table     *)
(* description, a backward bitstream with two interleaved states. The first  *)
(* state, read first, decodes the even-numbered weights and the second the   *)
(* odd-numbered ones. fse_weights cs alog st (s,s',q,ws) w when, with the    *)
(* state s to decode next, the other state s' and q useful bits left, the    *)
(* stream st extends the weights ws to w. When updating a state would need   *)
(* more bits than are left, the symbol of the other state is the last        *)
(* weight. There are at most 255 weights.                                    *)
(* ------------------------------------------------------------------------- *)

let FSE_WEIGHTS_RULES,FSE_WEIGHTS_INDUCT,FSE_WEIGHTS_CASES =
  new_inductive_definition
 `(!s s' q ws.
        LENGTH ws + 2 <= 255 /\ q < fse_nbits cs alog s
        ==> fse_weights (cs:int list) alog (st:byte list) (s,s',q,ws)
              (APPEND ws [fse_symbol cs alog s; fse_symbol cs alog s'])) /\
  (!s s' q ws w.
        LENGTH ws + 2 <= 255 /\ fse_nbits cs alog s <= q /\
        fse_weights cs alog st
          (s',fse_base cs alog s + zstd_back st q (fse_nbits cs alog s),
           q - fse_nbits cs alog s,APPEND ws [fse_symbol cs alog s]) w
        ==> fse_weights cs alog st (s,s',q,ws) w)`;;

(* The weights w given by the block blk, Accuracy_Log being at most 6.       *)

let fse_weight_block = new_definition
 `fse_weight_block zstd (blk:byte list) (w:num list) <=>
    ?cs alog m r.
        fse_ncount zstd 6 (if zstd then 256 else 12) blk (cs,alog,m) /\
        (zstd ==> LENGTH cs <= (if alog = 6 then 12 else 92)) /\
        let st = zstd_sublist blk m (LENGTH blk - m) in
        zstd_end st r /\ 2 * alog <= r /\
        fse_weights cs alog st
          (zstd_back st r alog,zstd_back st (r - alog) alog,r - 2 * alog,[])
          w`;;

(* ------------------------------------------------------------------------- *)
(* Huffman tree descriptions (section 4.2.1): a header byte, then the        *)
(* weights of all the symbols but the last, either as 4-bit numbers (header  *)
(* at least 128) or FSE-compressed (header below 128, the number of bytes).  *)
(* huf_header zstd l w h: the description at the start of l gives the        *)
(* weights w and has h bytes.                                                *)
(* ------------------------------------------------------------------------- *)

let huf_header = new_definition
 `huf_header zstd (l:byte list) (w:num list) h <=>
    ~(l = []) /\
    (128 <= val(EL 0 l) /\
     h = 1 + (val(EL 0 l) - 126) DIV 2 /\ h <= LENGTH l /\
     w = list_of_seq (\i. if EVEN i then val(EL (1 + i DIV 2) l) DIV 16
                          else val(EL (1 + i DIV 2) l) MOD 16)
                     (val(EL 0 l) - 127) \/
     val(EL 0 l) < 128 /\ h = 1 + val(EL 0 l) /\ h <= LENGTH l /\
     fse_weight_block zstd (zstd_sublist l 1 (h - 1)) w)`;;

(* The last weight completes the sum of 2^(Weight - 1) over the symbols to   *)
(* the next power of 2, 2^ml, where ml is Max_Number_of_Bits, which must be  *)
(* the length of the longest code.                                           *)

let huf_weights = new_definition
 `huf_weights zstd (l:byte list) ws ml h <=>
    ?w k. huf_header zstd l w h /\
          let total = nsum {i | i < LENGTH w /\ ~(EL i w = 0)}
                           (\i. 2 EXP (EL i w - 1)) in
          ~(total = 0) /\ ml = bitsize total /\
          ml <= (if zstd then 12 else 11) /\
          2 EXP ml - total = 2 EXP k /\ ws = APPEND w [k + 1] /\
          MEM 1 ws`;;

(* ------------------------------------------------------------------------- *)
(* Prefix codes (section 4.2.1.3). The symbol s of weight EL s ws > 0 has a  *)
(* code of ml + 1 - EL s ws bits: the symbols are sorted by weight and then  *)
(* by symbol, and the 2^ml states are given out in that order, 2^(w - 1) to  *)
(* a symbol of weight w. The code of s is the first of its states divided    *)
(* by 2^(EL s ws - 1).                                                       *)
(* ------------------------------------------------------------------------- *)

let huf_code = new_definition
 `huf_code (ws:num list) s =
    nsum {t | t < LENGTH ws /\ ~(EL t ws = 0) /\
              (EL t ws < EL s ws \/ EL t ws = EL s ws /\ t < s)}
         (\t. 2 EXP (EL t ws - 1)) DIV 2 EXP (EL s ws - 1)`;;

(* The codes of the bytes out, the first most significant, as a number and   *)
(* its number of bits.                                                       *)

let huf_bits = define
 `(huf_bits (ws:num list) ml [] = (0,0)) /\
  (huf_bits ws ml (CONS (c:byte) out) =
     (2 EXP SND(huf_bits ws ml out) * huf_code ws (val c) +
      FST(huf_bits ws ml out),
      ((ml + 1) - EL (val c) ws) + SND(huf_bits ws ml out)))`;;

(* ------------------------------------------------------------------------- *)
(* Huffman-coded streams (section 4.2.2): the useful bits of the stream st   *)
(* are exactly the codes of the symbols out, read from the most significant  *)
(* down.                                                                     *)
(* ------------------------------------------------------------------------- *)

let huf_stream = new_definition
 `huf_stream ws ml (st:byte list) (out:byte list) <=>
    ALL (\c. val c < LENGTH ws /\ ~(EL (val c) ws = 0)) out /\
    zstd_end st (SND(huf_bits ws ml out)) /\
    zstd_bits st 0 (SND(huf_bits ws ml out)) = FST(huf_bits ws ml out)`;;

(* ------------------------------------------------------------------------- *)
(* Huffman-coded literals in a single stream (Size_Format 00 of a            *)
(* Compressed_Literals_Block, section 3.1.1.3.1.1): a Huffman tree           *)
(* description followed by one Huffman-coded stream, taking all of l.        *)
(* ------------------------------------------------------------------------- *)

let huf_decompress1x1 = new_definition
 `huf_decompress1x1 zstd (l:byte list) (out:byte list) <=>
    ?ws ml h. huf_weights zstd l ws ml h /\ h < LENGTH l /\
              huf_stream ws ml (zstd_sublist l h (LENGTH l - h)) out`;;

(* ------------------------------------------------------------------------- *)
(* Huffman-coded literals in four streams (Size_Format 01, 10 or 11 of a     *)
(* Compressed_Literals_Block, section 3.1.1.3.1.6). After the tree           *)
(* description, the block blk has a jump table of 6 bytes, the sizes of the  *)
(* first three streams as 2-byte little-endian numbers (huf_jump blk k), and *)
(* then the four streams, the last taking the rest of blk. Of the n bytes    *)
(* out, the first three streams decode (n + 3) DIV 4 each and the fourth the *)
(* rest; zstd rejects fewer than 6 bytes.                                    *)
(* ------------------------------------------------------------------------- *)

let huf_jump = new_definition
 `huf_jump (blk:byte list) k =
    val(EL (2 * k) blk) + 256 * val(EL (2 * k + 1) blk)`;;

let huf_streams4 = new_definition
 `huf_streams4 zstd ws ml (blk:byte list) (out:byte list) <=>
    6 <= LENGTH blk /\
    let s1 = huf_jump blk 0 and s2 = huf_jump blk 1 and s3 = huf_jump blk 2
    and q = (LENGTH out + 3) DIV 4 in
    let a4 = 6 + s1 + s2 + s3 in
    a4 <= LENGTH blk /\ 3 * q <= LENGTH out /\ (zstd ==> 6 <= LENGTH out) /\
    huf_stream ws ml (zstd_sublist blk 6 s1) (zstd_sublist out 0 q) /\
    huf_stream ws ml (zstd_sublist blk (6 + s1) s2) (zstd_sublist out q q) /\
    huf_stream ws ml (zstd_sublist blk (6 + s1 + s2) s3)
               (zstd_sublist out (2 * q) q) /\
    huf_stream ws ml (zstd_sublist blk a4 (LENGTH blk - a4))
               (zstd_sublist out (3 * q) (LENGTH out - 3 * q))`;;

let huf_decompress4x1 = new_definition
 `huf_decompress4x1 zstd (l:byte list) (out:byte list) <=>
    ?ws ml h. huf_weights zstd l ws ml h /\ h < LENGTH l /\
              huf_streams4 zstd ws ml (zstd_sublist l h (LENGTH l - h)) out`;;
