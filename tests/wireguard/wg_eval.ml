(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Evaluation by proof of the BLAKE2s, ChaCha20 and Poly1305 functions of    *)
(* common/rfc7693.ml and common/rfc8439.ml on concrete inputs, used to check *)
(* the definitions against test vectors (tests/wireguard/wg_checks.ml).      *)
(*                                                                           *)
(* The 16-word states are functions num->int32 of which only the values      *)
(* below 16 matter (below 8 for the BLAKE2s chained state). Evaluation keeps *)
(* them as explicit tables \i. EL i [c0; ...; c15] of constants, related to  *)
(* the actual states by wg_agree n v w (v and w agree below n), as           *)
(* tests/mlkem/fips202_eval.ml does for the Keccak lanes.                    *)
(* ========================================================================= *)

needs "common/wireguard_tables.ml";;

(* |- wg_agree 16 (blake2s_round r mtab vtab) tab' for explicit tables.      *)

let BLAKE2S_ROUND_TABLE_RULE r mtab vtab =
  let tm = list_mk_comb(`blake2s_round`,[r;mtab;vtab]) in
  let th1 = (REWR_CONV blake2s_round THENC TOP_DEPTH_CONV let_CONV THENC
             TOP_DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV THENC
             PURE_REWRITE_CONV[blake2s_sigma] THENC
             TOP_DEPTH_CONV EL_CONV THENC TOP_DEPTH_CONV BETA_CONV THENC
             TOP_DEPTH_CONV EL_CONV) tm in
  let th2 = WG_NEST_EVAL BLAKE2S_G_STEP "blake2s_g" (rand(concl th1)) in
  CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM th1)))) th2;;

(* |- wg_agree 16 (blake2s_rounds n m v) tab from |- wg_agree 16 m mtab and  *)
(* |- wg_agree 16 v vtab.                                                     *)

let BLAKE2S_ROUNDS_RULE n mth vth =
  let mtab = rand(concl mth) in
  let m = rand(rator(concl mth)) and v = rand(rator(concl vth)) in
  let r0,rs = CONJ_PAIR blake2s_rounds in
  let th0 = CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM(REWR_CONV r0
              (list_mk_comb(`blake2s_rounds`,[`0`;m;v]))))))) vth in
  let rec iter k th =
    if k = n then th else
    let kk = mk_small_numeral k in
    let th1 = WG_SPEC [kk,`r:num`] (MATCH_MP BLAKE2S_ROUND_AGREE (CONJ mth th)) in
    let th2 = BLAKE2S_ROUND_TABLE_RULE kk mtab (rand(concl th)) in
    let th3 = MATCH_MP WG_AGREE_TRANS (CONJ th1 th2) in
    let eq = CONV_RULE(LAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV
               NUM_SUC_CONV))))
              (REWR_CONV rs (list_mk_comb(`blake2s_rounds`,
                 [mk_comb(`SUC`,kk);m;v]))) in
    iter (k + 1) (CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM eq)))) th3) in
  iter 0 th0;;

(* |- wg_agree 8 (blake2s_compress h m t f) tab' from |- wg_agree 8 h htab,   *)
(* |- wg_agree 16 m mtab and numerals t, booleans f.                         *)

let BLAKE2S_COMPRESS_RULE hth mth t f =
  let htab = rand(concl hth) and mtab = rand(concl mth) in
  let th1 = WG_SPEC [t,`t:num`; f,`f:bool`]
              (MATCH_MP BLAKE2S_COMPRESS_AGREE (CONJ hth mth)) in
  let wv = list_mk_comb(`blake2s_workvec`,[htab;t;f]) in
  let wvth = WG_EVAL_TABLE
    (RATOR_CONV(REWR_CONV blake2s_workvec) THENC BETA_CONV THENC
     NUM_REDUCE_CONV THENC REWRITE_CONV[] THENC
     PURE_REWRITE_CONV[blake2s_iv] THENC WG_REDUCE_CONV) 16 wv in
  let rth = BLAKE2S_ROUNDS_RULE 10 (ISPECL [`16`; mtab] WG_AGREE_REFL) wvth in
  let ats = map (WG_AGREE_AT rth) (0--15) in
  let ctm = list_mk_comb(`blake2s_compress`,[htab;mtab;t;f]) in
  let th2 = WG_EVAL_TABLE
    (RATOR_CONV(REWR_CONV blake2s_compress THENC let_CONV) THENC
     BETA_CONV THENC NUM_REDUCE_CONV THENC PURE_REWRITE_CONV ats THENC
     WG_REDUCE_CONV) 8 ctm in
  MATCH_MP WG_AGREE_TRANS (CONJ th1 th2);;

(* Evaluation of lists and numbers of bytes.                                 *)

let rec WG_REPLICATE_CONV tm =
  match tm with
    Comb(Comb(Const("REPLICATE",_),n),x) ->
      if dest_numeral n =/ num_0 then REWR_CONV (CONJUNCT1 REPLICATE) tm else
      (RATOR_CONV(RAND_CONV num_CONV) THENC REWR_CONV (CONJUNCT2 REPLICATE) THENC
       RAND_CONV WG_REPLICATE_CONV) tm
  | _ -> failwith "WG_REPLICATE_CONV";;

let rec WG_BYTELIST_OF_NUM_CONV tm =
  match tm with
    Comb(Comb(Const("bytelist_of_num",_),k),n) ->
      if dest_numeral k =/ num_0 then REWR_CONV (CONJUNCT1 bytelist_of_num) tm
      else (RATOR_CONV(RAND_CONV num_CONV) THENC
            REWR_CONV (CONJUNCT2 bytelist_of_num) THENC
            NUM_REDUCE_CONV THENC RAND_CONV WG_BYTELIST_OF_NUM_CONV) tm
  | _ -> failwith "WG_BYTELIST_OF_NUM_CONV";;

let WG_LIST_CONV =
  TOP_DEPTH_CONV(WG_REPLICATE_CONV ORELSEC LENGTH_CONV ORELSEC
                 CHANGED_CONV(PURE_REWRITE_CONV[APPEND]) ORELSEC
                 SUB_LIST_CONV ORELSEC NUM_RED_CONV);;

let WG_NUM_OF_BYTELIST_CONV =
  PURE_REWRITE_CONV[num_of_bytelist] THENC
  DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV;;

(* The table of the message block i of the padded data p.                    *)

let BLAKE2S_BLOCK_RULE p i =
  WG_EVAL_TABLE
   (RATOR_CONV(REWR_CONV blake2s_block) THENC BETA_CONV THENC
    NUM_REDUCE_CONV THENC WG_LIST_CONV THENC WG_NUM_OF_BYTELIST_CONV)
   16 (list_mk_comb(`blake2s_block`,[p;mk_small_numeral i]));;

(* blake2s key nn msg = bytes, for explicit key, nn and msg.                  *)

let BLAKE2S_CONV tm =
  match tm with
    Comb(Comb(Comb(Const("blake2s",_),key),nn),msg) ->
      let th1 = (REWR_CONV blake2s THENC
                 ONCE_DEPTH_CONV(LENGTH_CONV) THENC
                 ONCE_DEPTH_CONV(REWR_CONV blake2s_data THENC
                   TOP_DEPTH_CONV let_CONV THENC WG_LIST_CONV THENC
                   NUM_REDUCE_CONV THENC WG_LIST_CONV) THENC
                 TOP_DEPTH_CONV let_CONV THENC NUM_REDUCE_CONV) tm in
      (* the result: SUB_LIST(0,nn) (blake2s_bytes (blake2s_compress
         (blake2s_blocks (blake2s_block p) h0 n) (blake2s_block p n) t T)) *)
      let bytes_tm = rand(rand(concl th1)) in
      let comp_tm = rand bytes_tm in
      let [blocks_tm; lastblk_tm; t; f] = snd(strip_comb comp_tm) in
      let [d; h0; n] = snd(strip_comb blocks_tm) in
      let p = rand d in
      let nblocks = Num.int_of_num(dest_numeral n) in
      let h0th = WG_EVAL_TABLE (BETA_CONV THENC NUM_REDUCE_CONV THENC
                   REWRITE_CONV[] THENC PURE_REWRITE_CONV[blake2s_iv] THENC
                   WG_REDUCE_CONV) 8 h0 in
      let b0,bs = CONJ_PAIR blake2s_blocks in
      let th0 = CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM(REWR_CONV b0
                  (list_mk_comb(`blake2s_blocks`,[d;h0;`0`]))))))) h0th in
      let rec iter i th =
        if i = nblocks then th else
        let ii = mk_small_numeral i in
        let mth = BLAKE2S_BLOCK_RULE p i in
        let tt = mk_small_numeral (64 * (i + 1)) in
        let cth = BLAKE2S_COMPRESS_RULE th mth tt `F` in
        let eq = CONV_RULE(LAND_CONV(RAND_CONV NUM_SUC_CONV) THENC
                           RAND_CONV(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV)))
                   (REWR_CONV bs (list_mk_comb(`blake2s_blocks`,
                      [d;h0;mk_comb(`SUC`,ii)]))) in
        iter (i + 1) (CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM eq)))) cth) in
      let hth = iter 0 th0 in
      let mth = BLAKE2S_BLOCK_RULE p nblocks in
      let cth = BLAKE2S_COMPRESS_RULE hth mth t f in
      let bth = MATCH_MP BLAKE2S_BYTES_AGREE cth in
      let bth2 = CONV_RULE(RAND_CONV(REWR_CONV blake2s_bytes THENC
                   ONCE_DEPTH_CONV EXPAND_NSUM_CONV THENC
                   TOP_DEPTH_CONV BETA_CONV THENC TOP_DEPTH_CONV EL_CONV THENC
                   DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV THENC
                   WG_BYTELIST_OF_NUM_CONV)) bth in
      let th2 = AP_TERM (rator(rand(concl th1))) bth2 in
      CONV_RULE(RAND_CONV SUB_LIST_CONV) (TRANS th1 th2)
  | _ -> failwith "BLAKE2S_CONV";;

(* ------------------------------------------------------------------------- *)
(* ChaCha20: the rounds, the block function and encryption.                  *)
(* ------------------------------------------------------------------------- *)

(* |- wg_agree 16 (chacha20_double_round tab) tab' for an explicit table.    *)

let CHACHA20_DOUBLE_ROUND_TABLE_RULE vtab =
  let tm = mk_comb(`chacha20_double_round`,vtab) in
  let th1 = REWR_CONV chacha20_double_round tm in
  let th2 = WG_NEST_EVAL CHACHA20_QROUND_STEP "chacha20_qround"
              (rand(concl th1)) in
  CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM th1)))) th2;;

let CHACHA20_ROUNDS_RULE n vth =
  let v = rand(rator(concl vth)) in
  let r0,rs = CONJ_PAIR chacha20_rounds in
  let th0 = CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM(REWR_CONV r0
              (list_mk_comb(`chacha20_rounds`,[`0`;v]))))))) vth in
  let rec iter k th =
    if k = n then th else
    let kk = mk_small_numeral k in
    let th1 = MATCH_MP CHACHA20_DOUBLE_ROUND_AGREE th in
    let th2 = CHACHA20_DOUBLE_ROUND_TABLE_RULE (rand(concl th)) in
    let th3 = MATCH_MP WG_AGREE_TRANS (CONJ th1 th2) in
    let eq = CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV NUM_SUC_CONV)))
              (REWR_CONV rs (list_mk_comb(`chacha20_rounds`,
                 [mk_comb(`SUC`,kk);v]))) in
    iter (k + 1) (CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM eq)))) th3) in
  iter 0 th0;;

let CHACHA20_LE32_CONV =
  REWR_CONV chacha20_le32 THENC NUM_REDUCE_CONV THENC WG_LIST_CONV THENC
  WG_NUM_OF_BYTELIST_CONV;;

(* |- wg_agree 16 (chacha20_state key counter nonce) tab                       *)

let CHACHA20_STATE_RULE key counter nonce =
  WG_EVAL_TABLE
   (RATOR_CONV(REWR_CONV chacha20_state) THENC BETA_CONV THENC
    NUM_REDUCE_CONV THENC REWRITE_CONV[] THENC
    TRY_CONV CHACHA20_LE32_CONV)
   16 (list_mk_comb(`chacha20_state`,[key;counter;nonce]));;

(* chacha20_block key counter nonce = bytes, and the table of the rounds     *)
(* (for HChaCha20).                                                          *)

let CHACHA20_ROUNDS_OF_STATE key counter nonce =
  let xth = CHACHA20_STATE_RULE key counter nonce in
  let rth = CHACHA20_ROUNDS_RULE 10 (ISPECL [`16`; rand(concl xth)]
                                            WG_AGREE_REFL) in
  let x = rand(rator(concl xth)) in
  let rth' = MATCH_MP WG_AGREE_TRANS
               (CONJ (ISPEC `10` (MATCH_MP CHACHA20_ROUNDS_AGREE xth)) rth) in
  xth,rth';;

let CHACHA20_BLOCK_CONV tm =
  match tm with
    Comb(Comb(Comb(Const("chacha20_block",_),key),counter),nonce) ->
      let xth,rth = CHACHA20_ROUNDS_OF_STATE key counter nonce in
      let th1 = (REWR_CONV chacha20_block THENC TOP_DEPTH_CONV let_CONV) tm in
      let ath = MATCH_MP CHACHA20_ADD_AGREE (CONJ xth rth) in
      let atab = rand(concl ath) in
      let ath2 = WG_EVAL_TABLE (BETA_CONV THENC TOP_DEPTH_CONV BETA_CONV THENC
                                TOP_DEPTH_CONV EL_CONV) 16 atab in
      let wth = MATCH_MP CHACHA20_WORDS_AGREE
                  (MATCH_MP WG_AGREE_TRANS (CONJ ath ath2)) in
      let wth2 = CONV_RULE(RAND_CONV(REWR_CONV chacha20_words THENC
                   NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EXPAND_NSUM_CONV THENC
                   TOP_DEPTH_CONV BETA_CONV THENC TOP_DEPTH_CONV EL_CONV THENC
                   DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV THENC
                   WG_BYTELIST_OF_NUM_CONV)) wth in
      TRANS th1 wth2
  | _ -> failwith "CHACHA20_BLOCK_CONV";;

(* chacha20_encrypt key counter nonce m = bytes, evaluating each block once. *)

let CHACHA20_ENCRYPT_CONV tm =
  match tm with
    Comb(Comb(Comb(Comb(Const("chacha20_encrypt",_),key),counter),nonce),m) ->
      let th1 = (REWR_CONV chacha20_encrypt THENC
                 RAND_CONV LENGTH_CONV THENC LIST_OF_SEQ_CONV THENC
                 TOP_DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV) tm in
      let blocks = setify(find_terms
        (fun t -> try let f,args = strip_comb t in
                      fst(dest_const f) = "chacha20_block" && length args = 3
                  with Failure _ -> false) (rand(concl th1))) in
      let bths = map CHACHA20_BLOCK_CONV blocks in
      CONV_RULE(RAND_CONV(PURE_REWRITE_CONV bths THENC
                          TOP_DEPTH_CONV EL_CONV THENC WORD_REDUCE_CONV)) th1
  | _ -> failwith "CHACHA20_ENCRYPT_CONV";;

(* ------------------------------------------------------------------------- *)
(* Poly1305 and the AEAD.                                                    *)
(* ------------------------------------------------------------------------- *)

let rec POLY1305_ACC_CONV tm =
  match tm with
    Comb(Comb(Comb(Const("poly1305_acc",_),r),msg),n) ->
      if dest_numeral n =/ num_0 then REWR_CONV (CONJUNCT1 poly1305_acc) tm
      else (RAND_CONV num_CONV THENC REWR_CONV (CONJUNCT2 poly1305_acc) THENC
            let_CONV ORELSEC (fun t -> REFL t)) tm |>
           (fun th -> CONV_RULE(RAND_CONV(
              TRY_CONV let_CONV THENC
              ONCE_DEPTH_CONV POLY1305_ACC_CONV THENC
              NUM_REDUCE_CONV THENC WG_LIST_CONV THENC
              WG_NUM_OF_BYTELIST_CONV THENC NUM_REDUCE_CONV)) th)
  | _ -> failwith "POLY1305_ACC_CONV";;

let POLY1305_CONV =
  REWR_CONV poly1305 THENC
  ONCE_DEPTH_CONV(REWR_CONV poly1305_r) THENC
  NUM_REDUCE_CONV THENC WG_LIST_CONV THENC
  DEPTH_CONV(CHANGED_CONV WG_NUM_OF_BYTELIST_CONV) THENC
  WORD_REDUCE_CONV THENC NUM_REDUCE_CONV THENC
  ONCE_DEPTH_CONV POLY1305_ACC_CONV THENC NUM_REDUCE_CONV THENC
  WG_BYTELIST_OF_NUM_CONV;;

(* An explicit byte list from appends of lists, padding, lengths and         *)
(* little-endian numbers.                                                    *)

let WG_BYTES_CONV =
  PURE_REWRITE_CONV[poly1305_pad16] THENC DEPTH_CONV LENGTH_CONV THENC
  NUM_REDUCE_CONV THENC DEPTH_CONV WG_REPLICATE_CONV THENC
  DEPTH_CONV WG_BYTELIST_OF_NUM_CONV THENC PURE_REWRITE_CONV[APPEND];;

let AEAD_TAG_CONV =
  REWR_CONV aead_chacha20_poly1305_tag THENC
  ONCE_DEPTH_CONV CHACHA20_BLOCK_CONV THENC
  ONCE_DEPTH_CONV SUB_LIST_CONV THENC let_CONV THENC
  RAND_CONV WG_BYTES_CONV THENC POLY1305_CONV;;

let AEAD_ENCRYPT_CONV =
  REWR_CONV aead_chacha20_poly1305_encrypt THENC
  ONCE_DEPTH_CONV CHACHA20_ENCRYPT_CONV THENC let_CONV THENC
  RAND_CONV AEAD_TAG_CONV THENC PURE_REWRITE_CONV[APPEND];;
