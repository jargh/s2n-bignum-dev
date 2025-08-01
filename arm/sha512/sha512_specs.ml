needs "arm/sha512/utils.ml";;

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

let compression_until = define
  `compression_until (j:num) (i:num) hash (m:num->int64) =
      if i < j then
        let ki = K i in
        let wi = msg_schedule m i in
        let update = compression_update hash ki wi in
        compression_until j (i + 1) update m
      else 
        hash`;;
      
let compression = define
  `compression = compression_until 80`;;

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

let join_bytes_to_int64 = define
  `join_bytes_to_int64 (bs : byte list) : int64 =
    word_join
      (word_join (word_join (EL 7 bs) (EL 6 bs) : int16) (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
      (word_join (word_join (EL 3 bs) (EL 2 bs) : int16) (word_join (EL 1 bs) (EL 0 bs) : int16) : int32)`;;

let int64_to_bytes = define
  `int64_to_bytes (w : int64) : byte list =
    [word_subword w (0, 8); word_subword w (8, 8);
     word_subword w (16, 8); word_subword w (24, 8);
     word_subword w (32, 8); word_subword w (40, 8);
     word_subword w (48, 8); word_subword w (56, 8)]`;;

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

let hash_buffer_to_byte_list = define
  `hash_buffer_to_byte_list (h : hash_t) : byte list =
    int64_to_bytes (word_bytereverse (SHA512_A h)) ++
    int64_to_bytes (word_bytereverse (SHA512_B h)) ++
    int64_to_bytes (word_bytereverse (SHA512_C h)) ++
    int64_to_bytes (word_bytereverse (SHA512_D h)) ++
    int64_to_bytes (word_bytereverse (SHA512_E h)) ++
    int64_to_bytes (word_bytereverse (SHA512_F h)) ++
    int64_to_bytes (word_bytereverse (SHA512_G h)) ++
    int64_to_bytes (word_bytereverse (SHA512_H h))`;;

let sha512_pad = define
  `sha512_pad (m : byte list) : byte list =
    hash_buffer_to_byte_list
      (sha512 (bytes_to_blocks (pad m)) (LENGTH (pad m) DIV num_bytes_per_block))`;;

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
  `byte_list_at (m : byte list) (m_p : int64) s =
    ! i. i < LENGTH m ==> read (memory :> bytes8(word_add m_p (word i))) s = EL i m`;;

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
     byte_list_at cur_block (word_add ctx_p (word (8 * 10))) s /\
     read (memory :> bytes8 (word_add ctx_p (word 208))) s = word (LENGTH cur_block))`;;

let msg_schedule_at = define
  `msg_schedule_at (m : num -> int64) (sch_p : int64) s =
    ! i. i < 80 ==> read (memory :> bytes64(word_add sch_p (word (8 * i)))) s = msg_schedule m i`;;

let constants_at = define
  `constants_at (K_base : int64) s =
    ! i. i < 80 ==> read (memory :> bytes64(word_add K_base (word (8 * i)))) s = K i`;;
