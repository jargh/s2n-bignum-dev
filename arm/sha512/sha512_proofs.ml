needs "arm/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* Mathematical specifications of SHA-512.                                   *)
(* ------------------------------------------------------------------------- *)

(*****************************************************************************)

parse_as_prefix "~~";;
override_interface("~~",`word_not:N word->N word`);;
parse_as_infix("&&",(13,"right"));;
override_interface("&&",`word_and:N word->N word->N word`);;
parse_as_infix("||",(13,"right"));;
override_interface("||",`word_or:N word->N word->N word`);;
parse_as_infix("^^",(13,"right"));;
override_interface("^^",`word_xor:N word->N word->N word`);;

overload_interface("+",`word_add:N word->N word->N word`);;

let Ch_DEF = new_definition
 `Ch(x,y,z):int64 = (x && y) ^^ (~~x && z)`;;

let Maj_DEF = new_definition
 `Maj(x,y,z):int64 = (x && y) ^^ (x && z) ^^ (y && z)`;;

let Sigma0_DEF = new_definition
 `Sigma0(x):int64 = word_ror x 28 ^^ word_ror x 34 ^^ word_ror x 39`;;

let Sigma1_DEF = new_definition
 `Sigma1(x):int64 = word_ror x 14 ^^ word_ror x 18 ^^ word_ror x 41`;;

let sigma0_DEF = new_definition
 `sigma0(x):int64 = word_ror x 1 ^^ word_ror x 8 ^^ word_ushr x 7`;;

let sigma1_DEF = new_definition
 `sigma1(x):int64 = word_ror x 19 ^^ word_ror x 61 ^^ word_ushr x 6`;;

unparse_as_prefix "~~";;
remove_interface("~~");;
unparse_as_infix("&&");;
remove_interface("&&");;
unparse_as_infix("||");;
remove_interface("||");;
unparse_as_infix("^^");;
remove_interface("^^");;
remove_interface("++");;

(* ------------------------------------------------------------------------- *)
(* Section 4.2.3                                                             *)
(*                                                                           *)
(* In principle these have a more concise mathematical definition            *)
(* (first 64 fractional bit of cube roots of the first 80 primes)            *)
(* but it's easier just to use them as magic numbers. This is copied         *)
(* from TweetNaCl                                                            *)
(* ------------------------------------------------------------------------- *)

let  K_0  = new_definition  `K_0 : (64)word = word 0x428a2f98d728ae22`;;
let  K_1  = new_definition  `K_1 : (64)word = word 0x7137449123ef65cd`;;
let  K_2  = new_definition  `K_2 : (64)word = word 0xb5c0fbcfec4d3b2f`;;
let  K_3  = new_definition  `K_3 : (64)word = word 0xe9b5dba58189dbbc`;;
let  K_4  = new_definition  `K_4 : (64)word = word 0x3956c25bf348b538`;;
let  K_5  = new_definition  `K_5 : (64)word = word 0x59f111f1b605d019`;;
let  K_6  = new_definition  `K_6 : (64)word = word 0x923f82a4af194f9b`;;
let  K_7  = new_definition  `K_7 : (64)word = word 0xab1c5ed5da6d8118`;;
let  K_8  = new_definition  `K_8 : (64)word = word 0xd807aa98a3030242`;;
let  K_9  = new_definition  `K_9 : (64)word = word 0x12835b0145706fbe`;;
let K_10  = new_definition `K_10 : (64)word = word 0x243185be4ee4b28c`;;
let K_11  = new_definition `K_11 : (64)word = word 0x550c7dc3d5ffb4e2`;;
let K_12  = new_definition `K_12 : (64)word = word 0x72be5d74f27b896f`;;
let K_13  = new_definition `K_13 : (64)word = word 0x80deb1fe3b1696b1`;;
let K_14  = new_definition `K_14 : (64)word = word 0x9bdc06a725c71235`;;
let K_15  = new_definition `K_15 : (64)word = word 0xc19bf174cf692694`;;
let K_16  = new_definition `K_16 : (64)word = word 0xe49b69c19ef14ad2`;;
let K_17  = new_definition `K_17 : (64)word = word 0xefbe4786384f25e3`;;
let K_18  = new_definition `K_18 : (64)word = word 0x0fc19dc68b8cd5b5`;;
let K_19  = new_definition `K_19 : (64)word = word 0x240ca1cc77ac9c65`;;
let K_20  = new_definition `K_20 : (64)word = word 0x2de92c6f592b0275`;;
let K_21  = new_definition `K_21 : (64)word = word 0x4a7484aa6ea6e483`;;
let K_22  = new_definition `K_22 : (64)word = word 0x5cb0a9dcbd41fbd4`;;
let K_23  = new_definition `K_23 : (64)word = word 0x76f988da831153b5`;;
let K_24  = new_definition `K_24 : (64)word = word 0x983e5152ee66dfab`;;
let K_25  = new_definition `K_25 : (64)word = word 0xa831c66d2db43210`;;
let K_26  = new_definition `K_26 : (64)word = word 0xb00327c898fb213f`;;
let K_27  = new_definition `K_27 : (64)word = word 0xbf597fc7beef0ee4`;;
let K_28  = new_definition `K_28 : (64)word = word 0xc6e00bf33da88fc2`;;
let K_29  = new_definition `K_29 : (64)word = word 0xd5a79147930aa725`;;
let K_30  = new_definition `K_30 : (64)word = word 0x06ca6351e003826f`;;
let K_31  = new_definition `K_31 : (64)word = word 0x142929670a0e6e70`;;
let K_32  = new_definition `K_32 : (64)word = word 0x27b70a8546d22ffc`;;
let K_33  = new_definition `K_33 : (64)word = word 0x2e1b21385c26c926`;;
let K_34  = new_definition `K_34 : (64)word = word 0x4d2c6dfc5ac42aed`;;
let K_35  = new_definition `K_35 : (64)word = word 0x53380d139d95b3df`;;
let K_36  = new_definition `K_36 : (64)word = word 0x650a73548baf63de`;;
let K_37  = new_definition `K_37 : (64)word = word 0x766a0abb3c77b2a8`;;
let K_38  = new_definition `K_38 : (64)word = word 0x81c2c92e47edaee6`;;
let K_39  = new_definition `K_39 : (64)word = word 0x92722c851482353b`;;
let K_40  = new_definition `K_40 : (64)word = word 0xa2bfe8a14cf10364`;;
let K_41  = new_definition `K_41 : (64)word = word 0xa81a664bbc423001`;;
let K_42  = new_definition `K_42 : (64)word = word 0xc24b8b70d0f89791`;;
let K_43  = new_definition `K_43 : (64)word = word 0xc76c51a30654be30`;;
let K_44  = new_definition `K_44 : (64)word = word 0xd192e819d6ef5218`;;
let K_45  = new_definition `K_45 : (64)word = word 0xd69906245565a910`;;
let K_46  = new_definition `K_46 : (64)word = word 0xf40e35855771202a`;;
let K_47  = new_definition `K_47 : (64)word = word 0x106aa07032bbd1b8`;;
let K_48  = new_definition `K_48 : (64)word = word 0x19a4c116b8d2d0c8`;;
let K_49  = new_definition `K_49 : (64)word = word 0x1e376c085141ab53`;;
let K_50  = new_definition `K_50 : (64)word = word 0x2748774cdf8eeb99`;;
let K_51  = new_definition `K_51 : (64)word = word 0x34b0bcb5e19b48a8`;;
let K_52  = new_definition `K_52 : (64)word = word 0x391c0cb3c5c95a63`;;
let K_53  = new_definition `K_53 : (64)word = word 0x4ed8aa4ae3418acb`;;
let K_54  = new_definition `K_54 : (64)word = word 0x5b9cca4f7763e373`;;
let K_55  = new_definition `K_55 : (64)word = word 0x682e6ff3d6b2b8a3`;;
let K_56  = new_definition `K_56 : (64)word = word 0x748f82ee5defb2fc`;;
let K_57  = new_definition `K_57 : (64)word = word 0x78a5636f43172f60`;;
let K_58  = new_definition `K_58 : (64)word = word 0x84c87814a1f0ab72`;;
let K_59  = new_definition `K_59 : (64)word = word 0x8cc702081a6439ec`;;
let K_60  = new_definition `K_60 : (64)word = word 0x90befffa23631e28`;;
let K_61  = new_definition `K_61 : (64)word = word 0xa4506cebde82bde9`;;
let K_62  = new_definition `K_62 : (64)word = word 0xbef9a3f7b2c67915`;;
let K_63  = new_definition `K_63 : (64)word = word 0xc67178f2e372532b`;;
let K_64  = new_definition `K_64 : (64)word = word 0xca273eceea26619c`;;
let K_65  = new_definition `K_65 : (64)word = word 0xd186b8c721c0c207`;;
let K_66  = new_definition `K_66 : (64)word = word 0xeada7dd6cde0eb1e`;;
let K_67  = new_definition `K_67 : (64)word = word 0xf57d4f7fee6ed178`;;
let K_68  = new_definition `K_68 : (64)word = word 0x06f067aa72176fba`;;
let K_69  = new_definition `K_69 : (64)word = word 0x0a637dc5a2c898a6`;;
let K_70  = new_definition `K_70 : (64)word = word 0x113f9804bef90dae`;;
let K_71  = new_definition `K_71 : (64)word = word 0x1b710b35131c471b`;;
let K_72  = new_definition `K_72 : (64)word = word 0x28db77f523047d84`;;
let K_73  = new_definition `K_73 : (64)word = word 0x32caab7b40c72493`;;
let K_74  = new_definition `K_74 : (64)word = word 0x3c9ebe0a15c9bebc`;;
let K_75  = new_definition `K_75 : (64)word = word 0x431d67c49c100d4c`;;
let K_76  = new_definition `K_76 : (64)word = word 0x4cc5d4becb3e42b6`;;
let K_77  = new_definition `K_77 : (64)word = word 0x597f299cfc657e2a`;;
let K_78  = new_definition `K_78 : (64)word = word 0x5fcb6fab3ad6faec`;;
let K_79  = new_definition `K_79 : (64)word = word 0x6c44198c4a475817`;;

let ktbl_list = new_definition `ktbl_list : ((64)word)list =
              [  K_0;  K_1;  K_2;  K_3;  K_4;  K_5;  K_6;  K_7;  K_8;  K_9;
                 K_10; K_11; K_12; K_13; K_14; K_15; K_16; K_17; K_18; K_19;
                 K_20; K_21; K_22; K_23; K_24; K_25; K_26; K_27; K_28; K_29;
                 K_30; K_31; K_32; K_33; K_34; K_35; K_36; K_37; K_38; K_39;
                 K_40; K_41; K_42; K_43; K_44; K_45; K_46; K_47; K_48; K_49;
                 K_50; K_51; K_52; K_53; K_54; K_55; K_56; K_57; K_58; K_59;
                 K_60; K_61; K_62; K_63; K_64; K_65; K_66; K_67; K_68; K_69;
                 K_70; K_71; K_72; K_73; K_74; K_75; K_76; K_77; K_78; K_79 ]`;;

let K_DEF = new_definition `K i:int64 = EL i ktbl_list`;;

(* ------------------------------------------------------------------------- *)
(* Section 5.3.5: the initial value of the 8 hash variables.                 *)
(* ------------------------------------------------------------------------- *)

let h_a = new_definition `h_a : (64)word = word 0x6a09e667f3bcc908`;;
let h_b = new_definition `h_b : (64)word = word 0xbb67ae8584caa73b`;;
let h_c = new_definition `h_c : (64)word = word 0x3c6ef372fe94f82b`;;
let h_d = new_definition `h_d : (64)word = word 0xa54ff53a5f1d36f1`;; 
let h_e = new_definition `h_e : (64)word = word 0x510e527fade682d1`;;
let h_f = new_definition `h_f : (64)word = word 0x9b05688c2b3e6c1f`;;
let h_g = new_definition `h_g : (64)word = word 0x1f83d9abfb41bd6b`;; 
let h_h = new_definition `h_h : (64)word = word 0x5be0cd19137e2179`;;

new_type_abbrev("hash_t",`:int64#int64#int64#int64#int64#int64#int64#int64`);;

let h_init = new_definition
  `h_init : hash_t = h_a, h_b, h_c, h_d, h_e, h_f, h_g, h_h`;;

(* ------------------------------------------------------------------------- *)
(* Main inner loop iteration.                                                *)
(* ------------------------------------------------------------------------- *)

let msg_schedule_word = define
  `msg_schedule_word w1 w2 w3 w4 =
    sigma1 w1 + w2 + sigma0 w3 + w4`;;

let msg_schedule = define
 `msg_schedule (m:num->int64) (i:num) : int64 =
      if i < 16 then word_bytereverse (m i)
      else msg_schedule_word (msg_schedule m (i - 2))
                                 (msg_schedule m (i - 7))
                                 (msg_schedule m (i - 15))
                                 (msg_schedule m (i - 16))`;;

let compression_t1 = define
  `compression_t1 e f g h = h + Sigma1(e) + Ch(e,f,g)`;;

let compression_t2 = define
  `compression_t2 a b c = Sigma0(a) + Maj(a,b,c)`;;

let SHA512_A = define 
  `SHA512_A(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = a`;;
let SHA512_B = define 
  `SHA512_B(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = b`;;
let SHA512_C = define 
  `SHA512_C(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = c`;;
let SHA512_D = define 
  `SHA512_D(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = d`;;
let SHA512_E = define 
  `SHA512_E(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = e`;;
let SHA512_F = define 
  `SHA512_F(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = f`;;
let SHA512_G = define 
  `SHA512_G(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = g`;;
let SHA512_H = define 
  `SHA512_H(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = h`;;

let compression_update = define
 `compression_update hash ki wi =
    let a = SHA512_A hash in
    let b = SHA512_B hash in
    let c = SHA512_C hash in
    let d = SHA512_D hash in
    let e = SHA512_E hash in
    let f = SHA512_F hash in
    let g = SHA512_G hash in
    let h = SHA512_H hash in
    let t1 = (compression_t1 e f g h) + ki + wi in
    let t2 = compression_t2 a b c in
    (t1 + t2, a, b, c, d + t1, e, f, g)`;;
      
let compression = define
  `compression (i:num) hash (m:num->int64) =
      if i < 80 then
        let ki = K i in
        let wi = msg_schedule m i in
        let update = compression_update hash (K i) wi in
        compression (i + 1) update m
      else 
        hash`;;

let add8 = define 
 `add8 hash hash' = 
  let a = SHA512_A hash in
  let b = SHA512_B hash in
  let c = SHA512_C hash in
  let d = SHA512_D hash in
  let e = SHA512_E hash in
  let f = SHA512_F hash in
  let g = SHA512_G hash in
  let h = SHA512_H hash in
  let a' = SHA512_A hash' in
  let b' = SHA512_B hash' in
  let c' = SHA512_C hash' in
  let d' = SHA512_D hash' in
  let e' = SHA512_E hash' in
  let f' = SHA512_F hash' in
  let g' = SHA512_G hash' in
  let h' = SHA512_H hash' in
  (a+a',b+b',c+c',d+d',e+e',f+f',g+g',h+h')`;;

let sha512_block = define
 `sha512_block (m:num->int64) hash =
    let hash' = compression 0 hash m in
    add8 hash' hash`;;

let sha512' = define
  `sha512' hash (m:num->num->int64) (i:num) =
    if i = 0 then hash
    else sha512_block (m (i - 1)) (sha512' hash m (i - 1))`;;

let sha512 = define 
  `sha512 = sha512' h_init`;;

let num_bytes_per_block = define
  `num_bytes_per_block = 128`;;

let ceil_div = define
  `ceil_div (m : num) (n : num) = (m + n - 1) DIV n`;;

parse_as_infix ("++", (13, "right"));;
override_interface("++", `APPEND`);;

let int128_to_bytes = define
  `int128_to_bytes (w : int128) : byte list =
    [word_subword w (0, 8); word_subword w (8, 8);
     word_subword w (16, 8); word_subword w (24, 8);
     word_subword w (32, 8); word_subword w (40, 8);
     word_subword w (48, 8); word_subword w (56, 8);
     word_subword w (64, 8); word_subword w (72, 8);
     word_subword w (80, 8); word_subword w (88, 8);
     word_subword w (96, 8); word_subword w (104, 8);
     word_subword w (112, 8); word_subword w (120, 8)]`;;

(* Pad a message with 100...0<l> until it is a multiple of blocks,
 * where l is a 128-bit big-endian word equal to the number of bits in the message *)
let pad = define
  `pad (m : byte list) : byte list = m ++ [word 0x80] ++
    REPLICATE ((ceil_div (LENGTH m + 1 + 16) num_bytes_per_block) * num_bytes_per_block - (LENGTH m + 1 + 16)) (word 0) ++
    int128_to_bytes (word_bytereverse (word (LENGTH m * 8)))`;;

let take = define
  `take (n : num) (l : A list) : A list =
    SUB_LIST (0, n) l`;;

let drop = define
  `drop (n : num) (l : A list) : A list =
    SUB_LIST (n, LENGTH l - n) l`;;

let join_bytes_to_int64 = define
  `join_bytes_to_int64  (bs : byte list) : int64 =
    word_join
      (word_join (word_join (EL 7 bs) (EL 6 bs) : int16) (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
      (word_join (word_join (EL 3 bs) (EL 2 bs) : int16) (word_join (EL 1 bs) (EL 0 bs) : int16) : int32)`;;

(* Conversion from byte list to a block of 8-byte words *)
let bytes_to_one_block = define
  `bytes_to_one_block (m : byte list) : num -> int64 =
    \i. join_bytes_to_int64 (SUB_LIST (i * 8, 8) m)`;;

(* Conversion from byte list to blocks of 8-byte words *)
let bytes_to_blocks = define
  `bytes_to_blocks (m : byte list) : num -> num -> int64 =
    \i. bytes_to_one_block (SUB_LIST (i * num_bytes_per_block, num_bytes_per_block) m)`;;

let bytes_mod_blocks = define
  `bytes_mod_blocks (m : byte list) : byte list =
    drop ((LENGTH m DIV num_bytes_per_block) * num_bytes_per_block) m`;;

let sha512_ctx_from = define
  `sha512_ctx_from (m : byte list) =
    (sha512 (bytes_to_blocks m) (LENGTH m DIV num_bytes_per_block),
     word ((LENGTH m * 8) MOD (2 EXP 64)) : int64, word ((LENGTH m * 8) DIV (2 EXP 64)) : int64,
     bytes_mod_blocks m)`;;

(*****************************************************************************)

(* ------------------------------------------------------------------------- *)
(* Auxiliary definitions to associate memory contents with HOL Light terms.  *)
(* ------------------------------------------------------------------------- *)

(*****************************************************************************)

let hash_buffer_at = define
  `hash_buffer_at (h : hash_t) (h_p : int64) s =
    (read (memory :> bytes64(h_p)) s,                          read (memory :> bytes64 (word_add h_p (word 8))) s,
     read (memory :> bytes64 (word_add h_p (word (8 * 2)))) s, read (memory :> bytes64 (word_add h_p (word (8 * 3)))) s,
     read (memory :> bytes64 (word_add h_p (word (8 * 4)))) s, read (memory :> bytes64 (word_add h_p (word (8 * 5)))) s,
     read (memory :> bytes64 (word_add h_p (word (8 * 6)))) s, read (memory :> bytes64 (word_add h_p (word (8 * 7)))) s) = h`;;

let byte_list_at = define
  `byte_list_at (m : byte list) (l : num) (m_p : int64) s =
    (LENGTH m = l /\
     ! i. i < l ==> read (memory :> bytes8(word_add m_p (word i))) s = EL i m)`;;

let msg_block_at = define
  `msg_block_at (m : num -> int64) (m_p : int64) s =
    (read (memory :> bytes64(m_p)) s = m 0                            /\ read (memory :> bytes64(word_add m_p (word 8))) s = m 1 /\
     read (memory :> bytes64(word_add m_p (word (8 * 2)))) s = m 2    /\ read (memory :> bytes64(word_add m_p (word (8 * 3)))) s = m 3 /\
     read (memory :> bytes64(word_add m_p (word (8 * 4)))) s = m 4    /\ read (memory :> bytes64(word_add m_p (word (8 * 5)))) s = m 5 /\
     read (memory :> bytes64(word_add m_p (word (8 * 6)))) s = m 6    /\ read (memory :> bytes64(word_add m_p (word (8 * 7)))) s = m 7 /\
     read (memory :> bytes64(word_add m_p (word (8 * 8)))) s = m 8    /\ read (memory :> bytes64(word_add m_p (word (8 * 9)))) s = m 9 /\
     read (memory :> bytes64(word_add m_p (word (8 * 10)))) s = m 10  /\ read (memory :> bytes64(word_add m_p (word (8 * 11)))) s = m 11 /\
     read (memory :> bytes64(word_add m_p (word (8 * 12)))) s = m 12  /\ read (memory :> bytes64(word_add m_p (word (8 * 13)))) s = m 13 /\
     read (memory :> bytes64(word_add m_p (word (8 * 14)))) s = m 14  /\ read (memory :> bytes64(word_add m_p (word (8 * 15)))) s = m 15)`;;

let msg_blocks_at = define
  `msg_blocks_at (m : num -> num -> int64) (l : num) (m_p : int64) s =
    ! i. i < l ==> msg_block_at (m i) (word_add m_p (word (num_bytes_per_block * i))) s`;;

let sha512_ctx_at = define
  `sha512_ctx_at (m : byte list) (ctx_p : int64) s =
    let h, msg_len_lo, msg_len_hi, cur_block = sha512_ctx_from m in
    (hash_buffer_at h ctx_p s /\
     read (memory :> bytes64 (word_add ctx_p (word (8 * 8)))) s = msg_len_lo /\
     read (memory :> bytes64 (word_add ctx_p (word (8 * 9)))) s = msg_len_hi /\
     take (LENGTH cur_block) (read (memory :> bytelist (word_add ctx_p (word (8 * 10)), num_bytes_per_block)) s) = cur_block /\
     read (memory :> bytes8 (word_add ctx_p (word 208))) s = word (LENGTH cur_block))`;;

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
  w 0x54001169;         (* arm_BLS (word 556) *)
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
  w 0x540012a9;         (* arm_BLS (word 596) *)
  w 0xb4001241;         (* arm_CBZ X1 (word 584) *)
  w 0x38226abf;         (* arm_STRB WZR X21 (Register_Offset X2) *)
  w 0xf100043f;         (* arm_CMP X1 (rvalue (word 1)) *)
  w 0x54001160;         (* arm_BEQ (word 556) *)
  w 0x8b0202a3;         (* arm_ADD X3 X21 X2 *)
  w 0x3900047f;         (* arm_STRB WZR X3 (Immediate_Offset (word 1)) *)
  w 0xf100083f;         (* arm_CMP X1 (rvalue (word 2)) *)
  w 0x540010e0;         (* arm_BEQ (word 540) *)
  w 0x3900087f;         (* arm_STRB WZR X3 (Immediate_Offset (word 2)) *)
  w 0xf1000c3f;         (* arm_CMP X1 (rvalue (word 3)) *)
  w 0x54001080;         (* arm_BEQ (word 528) *)
  w 0x39000c7f;         (* arm_STRB WZR X3 (Immediate_Offset (word 3)) *)
  w 0xf100103f;         (* arm_CMP X1 (rvalue (word 4)) *)
  w 0x54001020;         (* arm_BEQ (word 516) *)
  w 0x3900107f;         (* arm_STRB WZR X3 (Immediate_Offset (word 4)) *)
  w 0xf100143f;         (* arm_CMP X1 (rvalue (word 5)) *)
  w 0x54000fc0;         (* arm_BEQ (word 504) *)
  w 0x3900147f;         (* arm_STRB WZR X3 (Immediate_Offset (word 5)) *)
  w 0xf1001c3f;         (* arm_CMP X1 (rvalue (word 7)) *)
  w 0x540010a1;         (* arm_BNE (word 532) *)
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
  w 0xd2800022;         (* arm_MOV X2 (rvalue (word 1)) *)
  w 0xaa1503e1;         (* arm_MOV X1 X21 *)
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0x97fffe59;         (* arm_BL (word 268433764) *)
  w 0xcb1503e0;         (* arm_NEG X0 X21 *)
  w 0xd2800e01;         (* arm_MOV X1 (rvalue (word 112)) *)
  w 0x3903427f;         (* arm_STRB WZR X19 (Immediate_Offset (word 208)) *)
  w 0x92400800;         (* arm_AND X0 X0 (rvalue (word 7)) *)
  w 0xaa0103e4;         (* arm_MOV X4 X1 *)
  w 0xaa1503e6;         (* arm_MOV X6 X21 *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0xd2800a03;         (* arm_MOV X3 (rvalue (word 80)) *)
  w 0xb4000ba0;         (* arm_CBZ X0 (word 372) *)
  w 0x38226abf;         (* arm_STRB WZR X21 (Register_Offset X2) *)
  w 0xf100041f;         (* arm_CMP X0 (rvalue (word 1)) *)
  w 0x54000ac0;         (* arm_BEQ (word 344) *)
  w 0x8b0202a5;         (* arm_ADD X5 X21 X2 *)
  w 0x390004bf;         (* arm_STRB WZR X5 (Immediate_Offset (word 1)) *)
  w 0xf100081f;         (* arm_CMP X0 (rvalue (word 2)) *)
  w 0x54000a40;         (* arm_BEQ (word 328) *)
  w 0x390008bf;         (* arm_STRB WZR X5 (Immediate_Offset (word 2)) *)
  w 0xf1000c1f;         (* arm_CMP X0 (rvalue (word 3)) *)
  w 0x540009e0;         (* arm_BEQ (word 316) *)
  w 0x39000cbf;         (* arm_STRB WZR X5 (Immediate_Offset (word 3)) *)
  w 0xf100101f;         (* arm_CMP X0 (rvalue (word 4)) *)
  w 0x54000980;         (* arm_BEQ (word 304) *)
  w 0x390010bf;         (* arm_STRB WZR X5 (Immediate_Offset (word 4)) *)
  w 0xf100141f;         (* arm_CMP X0 (rvalue (word 5)) *)
  w 0x54000920;         (* arm_BEQ (word 292) *)
  w 0x390014bf;         (* arm_STRB WZR X5 (Immediate_Offset (word 5)) *)
  w 0xf1001c1f;         (* arm_CMP X0 (rvalue (word 7)) *)
  w 0x54000a01;         (* arm_BNE (word 320) *)
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
  w 0xd2800022;         (* arm_MOV X2 (rvalue (word 1)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9006260;         (* arm_STR X0 X19 (Immediate_Offset (word 192)) *)
  w 0xf9402260;         (* arm_LDR X0 X19 (Immediate_Offset (word 64)) *)
  w 0xdac00c00;         (* arm_REV X0 X0 *)
  w 0xf9006660;         (* arm_STR X0 X19 (Immediate_Offset (word 200)) *)
  w 0xaa1303e0;         (* arm_MOV X0 X19 *)
  w 0x97fffe21;         (* arm_BL (word 268433540) *)
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
  w 0x34fffae0;         (* arm_CBZ W0 (word 2096988) *)
  w 0x91014043;         (* arm_ADD X3 X2 (rvalue (word 80)) *)
  w 0xaa0403e1;         (* arm_MOV X1 X4 *)
  w 0x8b030266;         (* arm_ADD X6 X19 X3 *)
  w 0xcb0603e0;         (* arm_NEG X0 X6 *)
  w 0x92400800;         (* arm_AND X0 X0 (rvalue (word 7)) *)
  w 0xf100489f;         (* arm_CMP X4 (rvalue (word 18)) *)
  w 0x54fff548;         (* arm_BHI (word 2096808) *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0x17ffffca;         (* arm_B (word 268435240) *)
  w 0xaa0003e2;         (* arm_MOV X2 X0 *)
  w 0x17ffffbc;         (* arm_B (word 268435184) *)
  w 0xaa0103e2;         (* arm_MOV X2 X1 *)
  w 0x17ffff87;         (* arm_B (word 268434972) *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0x17ffffb8;         (* arm_B (word 268435168) *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0x17ffff83;         (* arm_B (word 268434956) *)
  w 0xd2800002;         (* arm_MOV X2 (rvalue (word 0)) *)
  w 0x17ffff8e;         (* arm_B (word 268435000) *)
  w 0xd28000c2;         (* arm_MOV X2 (rvalue (word 6)) *)
  w 0x17ffffb2;         (* arm_B (word 268435144) *)
  w 0xd28000c2;         (* arm_MOV X2 (rvalue (word 6)) *)
  w 0x17ffff7d          (* arm_B (word 268434932) *)
]);;

let EXEC = ARM_MK_EXEC_RULE a_mc;;

(* sha512_init *)
let SHA512_INIT = prove(`! ctx_p pc retpc K.
  nonoverlapping (word pc : int64, 2748) (ctx_p, 216) ==>
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K) /\
         read PC s = word (pc + 0x2b0) /\
         read X30 s = retpc /\
         read X0 s = ctx_p)
    (\s. read PC s = retpc /\
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

(* msg_schedule *)
let MSG_SCHEDULE = prove(`! sch_p m_p m pc retpc K.
  PAIRWISE nonoverlapping
    [(word pc : int64, 2748); (sch_p, 640); (m_p, num_bytes_per_block)] ==>
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K) /\
         read PC s = word pc /\
         read X30 s = word retpc /\
         read X0 s = sch_p /\ 
         read X1 s = m_p /\
         msg_block_at m m_p s)
    (\s. read PC s = word retpc /\
         ! i. i < 80 ==> read (memory :> bytes64(word_add sch_p (word (8 * i)))) s = msg_schedule m i)
    (MAYCHANGE [X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; PC] ,,
     MAYCHANGE [memory :> bytes(sch_p, 640)] ,, MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; num_bytes_per_block] THEN
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









     





(*********** ??? work in progress ***********)
let rec back_up n = if n > 1 then (b(); back_up (n-1)) else b();;

(* void sha512_process_block(uint64_t h[8], const uint8_t *in_data) *)
g `! sp h_p h m_p m pc retpc K.
  PAIRWISE nonoverlapping
    [(word pc : int64, 2748); (h_p, 64);
     (m_p, num_bytes_per_block); (word_sub sp (word 720), 720)] ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K) /\
         read PC s = word (pc + 0xe0) /\
         read X30 s = retpc /\
         read SP s = sp /\
         aligned 16 sp /\
         read X0 s = h_p /\
         read X1 s = m_p /\
         hash_buffer_at h h_p s /\
         msg_block_at m m_p s)
    (\s. read PC s = retpc /\
         hash_buffer_at (sha512_block m h) h_p s)
    (MAYCHANGE [X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                X12; X13; X14; X15; X16; X17; X18; PC] ,,
     MAYCHANGE [memory :> bytes(h_p, 64)] ,,
     MAYCHANGE [memory :> bytes(word_sub sp (word 720), 720)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;

e (REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; num_bytes_per_block]);;
e (WORD_FORALL_OFFSET_TAC 720);;
e (REPEAT STRIP_TAC);;
e (ENSURES_EXISTING_PRESERVED_TAC `SP`);;
e (ENSURES_PRESERVED_TAC "x29_init" `X29`);;
e (ENSURES_EXISTING_PRESERVED_TAC `X30`);;

e (ENSURES_INIT_TAC "s56");;
e (ARM_STEPS_TAC EXEC (57--61));;








(*
(* void sha512_process_blocks(uint64_t h[8], const uint8_t *in_data, size_t num_blocks) *)
g `! h_p h m_p m l pc retpc K sp.
  PAIRWISE nonoverlapping
    [(word pc : int64, 2748); (h_p, 640); (m_p, num_bytes_per_block * l);
    (word sp : int64, 768)] ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K) /\
         read PC s = word pc + ???/\
         read X30 s = retpc /\
         aligned 16 (word sp : int64) /\
         read X0 s = h_p /\
         read X1 s = m_p /\
         read X2 s = l /\
         hash_buffer_at h h_p s /\
         msg_blocks_at m l m_p s)
    (\s. read PC s = retpc /\
        hash_buffer_at (sha512' h m i) h_p s)
    (MAYCHANGE [X0; X1; X2; PC] ,, MAYCHANGE [memory :> bytes(h_p, 64)] ,,
     MAYCHANGE [memory :> bytes(word sp, 768)] ,, MAYCHANGE [events])`

(* void sha512_update(sha512_ctx *sha, const void *in_data, size_t in_len) *)
g `! ctx_p (h : hash_t) (msg_len_lo : int64) (msg_len_hi : int64) (cur_block : byte list) (cur_pos : byte) (ctx_p : int64)
     m0 m_p m l pc retpc K sp.
    nonoverlapping pc, h_p, m_p, stack??? ==>
    LENGTH m = l ==>
    sha512_ctx_inv m0 msg_len_lo msg_len_hi cur_block ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K) /\
         read PC s = word pc + ??? /\
         read X30 s = retpc /\
         aligned 16 (word sp : int64) /\
         read X0 s = ctx_p /\
         read X1 s = m_p /\
         read X2 s = l /\
         sha512_ctx_at h msg_len_lo msg_len_hi cur_block cur_pos ctx_p s /\
         byte_list_at m l m_p s)
    (\s. read PC s = retpc /\
        ! (h' : hash_t) (msg_len_lo' : int64) (msg_len_hi' : int64) (cur_block' : byte list),
        sha512_ctx_inv (m0 ++ m) h' msg_len_lo' msg_len_hi' cur_block' ==>
        sha512_ctx_at h' msg_len_lo' msg_len_hi' cur_block' (LENGTH cur_block') ctx_p s)
    (MAYCHANGE [X0; X1; X2; ???; PC] ,, MAYCHANGE [memory :> bytes(h_p, 64)] ,,
     MAYCHANGE [memory :> bytes(word sp, 768)] ,, MAYCHANGE [events])`

(* void sha512_final(uint8_t out[SHA512_DIGEST_LENGTH], sha512_ctx *sha) *)
g `! ctx_p (h : hash_t) (msg_len_lo : int64) (msg_len_hi : int64) (cur_block : byte list) (cur_pos : byte) (ctx_p : int64)
     m out_p pc retpc K sp.
    nonoverlapping pc, out_p, stack??? ==>
    sha512_ctx_inv m msg_len_lo msg_len_hi cur_block ==>
    ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc K) /\
         read PC s = word pc + ??? /\
         read X30 s = retpc /\
         aligned 16 (word sp : int64) /\
         read X0 s = out_p /\
         read X1 s = ctx_p /\
         sha512_ctx_at h msg_len_lo msg_len_hi cur_block cur_pos ctx_p s /\)
    (\s. read PC s = retpc /\
        hash_buffer_at (sha512 (bytes_to_blocks (pad m)) (LENGTH (pad m) DIV num_bytes_per_block)) out_p s)
    (MAYCHANGE [X0; X1; X2; ???; PC] ,, MAYCHANGE [memory :> bytes(h_p, 64)] ,,
     MAYCHANGE [memory :> bytes(word sp, ???)] ,, MAYCHANGE [events])`
     *)