(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof-producing evaluation for the RFC 8878 spec (common/rfc8878.ml):     *)
(* conversions for the functions of the spec on explicit arguments, and      *)
(* HUF_DECOMPRESS1X1_RULE zstd bs n, which proves                            *)
(* |- huf_decompress1x1 zstd l out for the byte list l with the values bs    *)
(* and the n bytes out it decodes to, following the inductive relations step *)
(* by step: the decoding decisions are made in OCaml, and every one of them  *)
(* is checked in HOL. HUF_DECOMPRESS4X1_RULE does the same for four streams, *)
(* proving |- huf_decompress4x1 zstd l out. Intended for small inputs.       *)
(* ========================================================================= *)

needs "common/rfc8878.ml";;

(* ------------------------------------------------------------------------- *)
(* Explicit lists: EL, LENGTH, list_of_seq, FILTER, ASSOC and REPLICATE.     *)
(* ------------------------------------------------------------------------- *)

let EL_CONV =
  let pth0 = prove(`!h:A t. EL 0 (CONS h t) = h`, REWRITE_TAC[EL; HD])
  and pthS = prove(`!h:A t n. EL (SUC n) (CONS h t) = EL n t`,
                   REWRITE_TAC[EL; TL]) in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("EL",_),k),l) when is_numeral k && is_list l ->
        if dest_small_numeral k = 0 then PART_MATCH lhs pth0 tm else
        let th1 = RATOR_CONV(RAND_CONV num_CONV) tm in
        let th2 = PART_MATCH lhs pthS (rand(concl th1)) in
        TRANS th1 (TRANS th2 (conv(rand(concl th2))))
    | _ -> failwith "EL_CONV" in
  conv;;

let LENGTH_CONV = REWRITE_CONV[LENGTH] THENC NUM_REDUCE_CONV;;

(* A memo table for EL i l, for a fixed explicit list l.                     *)

let el_table ltm =
  let n = length(dest_list ltm) in
  Array.init n
   (fun i -> EL_CONV(list_mk_icomb "EL" [mk_small_numeral i; ltm]));;

let EL_TABLE_CONV ltm tab tm =
  match tm with
    Comb(Comb(Const("EL",_),k),l)
      when l = ltm && is_numeral k &&
           dest_small_numeral k < Array.length tab ->
        tab.(dest_small_numeral k)
  | _ -> failwith "EL_TABLE_CONV";;

let LIST_OF_SEQ_CONV =
  let p0,pS = CONJ_PAIR list_of_seq in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("list_of_seq",_),f),n) when is_numeral n ->
        if dest_small_numeral n = 0 then REWR_CONV p0 tm else
        (RAND_CONV num_CONV THENC REWR_CONV pS THENC
         LAND_CONV(RAND_CONV NUM_REDUCE_CONV THENC conv) THENC
         RAND_CONV(RATOR_CONV(RAND_CONV(TRY_CONV BETA_CONV))) THENC
         REWRITE_CONV[APPEND]) tm
    | _ -> failwith "LIST_OF_SEQ_CONV" in
  conv;;

let FILTER_CONV pconv =
  let f0,fS = CONJ_PAIR FILTER in
  let ct,cf = CONJ_PAIR(SPEC_ALL COND_CLAUSES) in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("FILTER",_),p),l) ->
        if is_const l then REWR_CONV f0 tm else
        (REWR_CONV fS THENC
         RATOR_CONV(RATOR_CONV(RAND_CONV(BETA_CONV THENC pconv))) THENC
         ((REWR_CONV ct THENC RAND_CONV conv) ORELSEC
          (REWR_CONV cf THENC conv))) tm
    | _ -> failwith "FILTER_CONV" in
  conv;;

let ASSOC_CONV =
  let ct,cf = CONJ_PAIR(SPEC_ALL COND_CLAUSES) in
  let rec conv tm =
    (REWR_CONV ASSOC THENC
     RATOR_CONV(RATOR_CONV(RAND_CONV
       (LAND_CONV(REWR_CONV FST) THENC NUM_EQ_CONV))) THENC
     ((REWR_CONV ct THENC REWR_CONV SND) ORELSEC
      (REWR_CONV cf THENC conv))) tm in
  conv;;

let REPLICATE_CONV =
  let r0,rS = CONJ_PAIR REPLICATE in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("REPLICATE",_),k),x) when is_numeral k ->
        if dest_small_numeral k = 0 then REWR_CONV r0 tm else
        (RATOR_CONV(RAND_CONV num_CONV) THENC REWR_CONV rS THENC
         RAND_CONV conv) tm
    | _ -> failwith "REPLICATE_CONV" in
  conv;;

(* bitsize n for a numeral n.                                                *)

let BITSIZE_CONV tm =
  match tm with
    Comb(Const("bitsize",_),n) when is_numeral n ->
      let k = dest_small_numeral n in
      let rec f k b = if k = 0 then b else f (k / 2) (b + 1) in
      let th = SPECL [n; mk_small_numeral (f k 0)] BITSIZE_UNIQUE_EQ in
      EQ_MP (SYM th)
        (EQT_ELIM((NUM_REDUCE_CONV THENC REWRITE_CONV[]) (rand(concl th))))
  | _ -> failwith "BITSIZE_CONV";;

(* nsum and CARD over {i | i < n /\ P i}, for a numeral n.                   *)

let NSUM_RESTRICT_LT = prove
 (`!n P (g:num->num).
        nsum {t | t < n /\ P t} g =
        nsum {t | t < n} (\t. if P t then g t else 0)`,
  REWRITE_TAC[GSYM NSUM_RESTRICT_SET; IN_ELIM_THM]);;

let CARD_RESTRICT_LT = prove
 (`!n P. CARD {v | v < n /\ P v} =
         nsum {v | v < n} (\v. if P v then 1 else 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NSUM_RESTRICT_SET; IN_ELIM_THM] THEN
  MATCH_MP_TAC CARD_EQ_NSUM THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{v:num | v < n}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Inputs: explicit byte lists, their bits and numbers from bits.            *)
(* ------------------------------------------------------------------------- *)

let ZSTD_BITS_ADD1 = prove
 (`!l p n. zstd_bits l p (n + 1) =
           zstd_bits l p n + 2 EXP n * bitval(zstd_bit l (p + n))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[ONE; zstd_bits; ADD_CLAUSES; EXP; MULT_CLAUSES];
    REWRITE_TAC[ARITH_RULE `SUC n + 1 = SUC(n + 1)`; zstd_bits] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP; ARITH_RULE `p + SUC n = (p + 1) + n`] THEN ARITH_TAC]);;

type input = {ltm : term; bytes : int array; bitf : int -> thm;
              lenth : thm; elconv : conv; prefix : int -> thm};;

let mk_bytes (bs:int list) =
  mk_list(map (fun b -> mk_comb(`word:num->byte`,mk_small_numeral b)) bs,
          `:byte`);;

let make_input (bs:int list) =
  let ltm = mk_bytes bs in
  let tab = el_table ltm in
  let elconv = EL_TABLE_CONV ltm tab in
  let lenth = LENGTH_CONV(list_mk_icomb "LENGTH" [ltm]) in
  let bconv = REWR_CONV zstd_bit THENC
              LAND_CONV(RAND_CONV(RAND_CONV(K lenth)) THENC NUM_REDUCE_CONV)
              THENC REWRITE_CONV[] THENC
              TRY_CONV(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV) THENC
                       RAND_CONV(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV) THENC
                                 elconv) THENC
                       WORD_REDUCE_CONV) in
  let memo = Hashtbl.create 1000 in
  let bitf i =
    try Hashtbl.find memo i with Not_found ->
    let th = bconv(list_mk_icomb "zstd_bit" [ltm; mk_small_numeral i]) in
    Hashtbl.add memo i th; th in
  let pmemo = Hashtbl.create 1000 in
  let rec prefix q =
    try Hashtbl.find pmemo q with Not_found ->
    let th =
      if q = 0 then REWR_CONV (CONJUNCT1 zstd_bits)
                      (list_mk_icomb "zstd_bits" [ltm; `0`; `0`]) else
      let th0 = prefix (q - 1) in
      let th1 = SPECL [ltm; `0`; mk_small_numeral(q - 1)] ZSTD_BITS_ADD1 in
      let th2 = CONV_RULE(LAND_CONV(RAND_CONV NUM_REDUCE_CONV) THENC
                          RAND_CONV(LAND_CONV(K th0) THENC
                                    RAND_CONV(RAND_CONV(RAND_CONV
                                      (RAND_CONV NUM_REDUCE_CONV THENC
                                       (fun t -> bitf(dest_small_numeral
                                                        (rand t)))) THENC
                                      REWRITE_CONV[BITVAL_CLAUSES])) THENC
                                    NUM_REDUCE_CONV)) th1 in
      th2 in
    Hashtbl.add pmemo q th; th in
  {ltm = ltm; bytes = Array.of_list bs; bitf = bitf; lenth = lenth;
   elconv = elconv; prefix = prefix};;

(* zstd_bits l p n for the input l and numerals p, n.                        *)

let ZSTD_BITS_CONV inp =
  let b0,bS = CONJ_PAIR zstd_bits in
  let rec conv tm =
    let n = dest_small_numeral(rand tm) in
    if n = 0 then REWR_CONV b0 tm else
    let p = dest_small_numeral(rand(rator tm)) in
    if p = 0 then inp.prefix n else
    (RAND_CONV num_CONV THENC REWR_CONV bS THENC
     LAND_CONV(RAND_CONV(fun _ -> inp.bitf p) THENC
               REWRITE_CONV[BITVAL_CLAUSES]) THENC
     RAND_CONV(RAND_CONV(RATOR_CONV(RAND_CONV NUM_ADD_CONV) THENC conv)) THENC
     NUM_REDUCE_CONV) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* A general evaluator for closed terms of the spec with explicit arguments: *)
(* TOP_DEPTH_CONV of single steps, which unfold the definitions of the spec  *)
(* and reduce the results, memoizing the bits of the lists met, EL, LENGTH   *)
(* and the values of the tables and codes.                                   *)
(* ------------------------------------------------------------------------- *)

(* The end of a backward bit stream, with only finitely many bits to check.  *)

let ZSTD_END_ALT = prove
 (`!st r. zstd_end st r <=>
          ~(st = []) /\ 8 * (LENGTH st - 1) <= r /\ zstd_bit st r /\
          (!i. i < 8 * LENGTH st - (r + 1) ==> ~zstd_bit st (r + 1 + i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zstd_end] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ASM_CASES_TAC `i < 8 * LENGTH(st:byte list)` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i - (r + 1)`) THEN
      ASM_SIMP_TAC[ARITH_RULE `r < i ==> r + 1 + i - (r + 1) = i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[zstd_bit]]]);;

let ZSTD_END_CONV tm =
  match tm with
    Comb(Comb(Const("zstd_end",_),st),r) when is_list st && is_numeral r ->
      REWR_CONV ZSTD_END_ALT tm
  | _ -> failwith "ZSTD_END_CONV";;

(* !i. i < n ==> P i, for a numeral n.                                       *)

let BOUNDED_FORALL_CONV tm =
  match tm with
    Comb(Const("!",_),Abs(i,Comb(Comb(Const("==>",_),
         Comb(Comb(Const("<",_),i'),n)),_))) when i = i' && is_numeral n ->
      EXPAND_CASES_CONV tm
  | _ -> failwith "BOUNDED_FORALL_CONV";;

(* Inputs are made on demand for the explicit lists met, and kept.           *)

let inputs = ref ([]:(term * input) list);;

let input_of ltm =
  try assoc ltm !inputs with Failure _ ->
  let inp = make_input (map (fun t -> dest_small_numeral(rand t))
                            (dest_list ltm)) in
  inputs := (ltm,inp) :: !inputs; inp;;

let INPUT_BITS_CONV tm =
  match tm with
    Comb(Comb(Comb(Const("zstd_bits",_),l),p),n)
      when is_list l && is_numeral p && is_numeral n ->
        ZSTD_BITS_CONV (input_of l) tm
  | Comb(Comb(Const("zstd_bit",_),l),i) when is_list l && is_numeral i ->
        (input_of l).bitf (dest_small_numeral i)
  | _ -> failwith "INPUT_BITS_CONV";;

let rec is_value tm =
  is_numeral tm || tm = `T` || tm = `F` ||
  (match tm with
     Comb(Const("word",_),n) -> is_numeral n
   | Comb(Const("int_of_num",_),n) -> is_numeral n
   | Comb(Const("int_neg",_),Comb(Const("int_of_num",_),n)) -> is_numeral n
   | Comb(Comb(Const(",",_),a),b) -> is_value a && is_value b
   | _ -> is_list tm && forall is_value (dest_list tm));;

let VALUE_LET_CONV tm =
  match tm with
    Comb(Comb(Const("LET",_),f),x) when is_value x -> let_CONV tm
  | _ -> failwith "VALUE_LET_CONV";;

(* EL and LENGTH of explicit lists, memoized for each list.                  *)

let el_tables = Hashtbl.create 100;;

let EXPLICIT_EL_CONV tm =
  match tm with
    Comb(Comb(Const("EL",_),k),l) when is_numeral k && is_list l ->
      let tab = try Hashtbl.find el_tables l with Not_found ->
                let t = el_table l in Hashtbl.add el_tables l t; t in
      EL_TABLE_CONV l tab tm
  | _ -> failwith "EXPLICIT_EL_CONV";;

let length_memo = Hashtbl.create 100;;

let EXPLICIT_LENGTH_CONV tm =
  match tm with
    Comb(Const("LENGTH",_),l) when is_list l ->
      (try Hashtbl.find length_memo tm with Not_found ->
       let th = LENGTH_CONV tm in Hashtbl.add length_memo tm th; th)
  | _ -> failwith "EXPLICIT_LENGTH_CONV";;

let EXPLICIT_APPEND_CONV tm =
  match tm with
    Comb(Comb(Const("APPEND",_),l1),l2) when is_list l1 && is_list l2 ->
      REWRITE_CONV[APPEND] tm
  | _ -> failwith "EXPLICIT_APPEND_CONV";;

let EVAL_STEP_CONV =
  let rews = [COND_CLAUSES; AND_CLAUSES; OR_CLAUSES; NOT_CLAUSES;
              IMP_CLAUSES; EQ_CLAUSES; FST; SND; PAIR_EQ; BITVAL_CLAUSES;
              NUM_OF_INT_OF_NUM; MAX; INT_MAX; NOT_CONS_NIL;
              MEM; ALL; ZIP; ITLIST; CONS_11; NSUM_CLAUSES] in
  let rewc = GEN_REWRITE_CONV I rews in
  let nsumc = GEN_REWRITE_CONV I [NSUM_RESTRICT_LT; CARD_RESTRICT_LT] in
  let defc = GEN_REWRITE_CONV I
    [fse_step; fse_points; fse_inside; fse_reload; fse_field; zstd_back;
     huf_code; fse_lowprob; fse_symbol; fse_next; fse_nbits; fse_base;
     fse_spread; zstd_sublist; huf_bits; huf_stream; huf_jump] in
  let memo = Hashtbl.create 1000 in
  let memo_names = ["fse_spread"; "fse_symbol"; "fse_next"; "fse_nbits";
                    "fse_base"; "huf_code"; "fse_lowprob"; "huf_bits"] in
  let rec memoc tm =
    let h,args = strip_comb tm in
    match h with
      Const(c,_) when mem c memo_names && forall is_value args ->
        (try Hashtbl.find memo tm with Not_found ->
         let th = (defc THENC TOP_DEPTH_CONV step) tm in
         if not(is_value(rand(concl th))) then failwith "memoc" else
         (Hashtbl.add memo tm th; th))
    | _ -> failwith "memoc"
  and step tm =
    (INPUT_BITS_CONV ORELSEC memoc ORELSEC
     ZSTD_END_CONV ORELSEC BOUNDED_FORALL_CONV ORELSEC
     BETA_CONV ORELSEC VALUE_LET_CONV ORELSEC
     EXPLICIT_EL_CONV ORELSEC EXPLICIT_LENGTH_CONV ORELSEC
     EXPLICIT_APPEND_CONV ORELSEC
     BITSIZE_CONV ORELSEC REPLICATE_CONV ORELSEC LIST_OF_SEQ_CONV ORELSEC
     NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
     ASSOC_CONV ORELSEC FILTER_CONV (TOP_DEPTH_CONV step) ORELSEC
     rewc ORELSEC nsumc ORELSEC defc ORELSEC
     (fun tm -> match tm with
        Comb(Comb(Const("nsum",_),s),f) ->
          (LAND_CONV(REWR_CONV NUMSEG_LT THENC NUM_REDUCE_CONV THENC
                     REWRITE_CONV[]) THENC
           (REWR_CONV(CONJUNCT1 NSUM_CLAUSES) ORELSEC EXPAND_NSUM_CONV)) tm
      | _ -> failwith "nsum")) tm in
  step;;

let EVAL_CONV = TOP_DEPTH_CONV EVAL_STEP_CONV;;

let EVAL_RULE tm =
  let th = EVAL_CONV tm in
  if rand(concl th) = `T` then EQT_ELIM th
  else (print_string "\nEVAL_RULE: "; print_term (rand(concl th));
        print_newline(); failwith "EVAL_RULE");;

(* ------------------------------------------------------------------------- *)
(* Proving instances of rules: the rule's conclusion for the given values of *)
(* its variables, its antecedent proved conjunct by conjunct, by evaluation  *)
(* or, for a conjunct of one of the relations, from the next of the given    *)
(* theorems once its arguments are evaluated. The conclusion is returned     *)
(* with its arguments evaluated.                                             *)
(* ------------------------------------------------------------------------- *)

let relation_names =
  ["fse_zeros"; "fse_counts"; "fse_weights"; "fse_ncount"; "fse_weight_block";
   "huf_header"; "huf_weights"; "huf_streams4"];;

let is_relation tm =
  match fst(strip_comb tm) with
    Const(c,_) -> mem c relation_names
  | _ -> false;;

let rec VALUE_EVAL_CONV tm =
  if is_value tm then REFL tm else
  match tm with
    Comb(Comb(Const(",",_),a),b) -> MK_COMB(AP_TERM (rator(rator tm))
                                              (VALUE_EVAL_CONV a),
                                            VALUE_EVAL_CONV b)
  | _ -> EVAL_CONV tm;;

let ARGS_EVAL_CONV tm =
  let h,args = strip_comb tm in
  let ths = map VALUE_EVAL_CONV args in
  rev_itlist (fun th acc -> MK_COMB(acc,th)) ths (REFL h);;

(* PROVE (wits,subs) tm proves tm, a conjunction of existentials, lets, side *)
(* conditions and relations, with the witnesses wits for the existentials    *)
(* and the theorems subs for the relations, in order.                        *)

let rec PROVE (wits,subs) tm =
  if is_conj tm then
    let l,r = dest_conj tm in
    let thl,st = PROVE (wits,subs) l in
    let thr,st' = PROVE st r in
    CONJ thl thr,st'
  else if is_exists tm then
    match wits with
      w::ws -> let x,b = dest_exists tm in
               let th,st = PROVE (ws,subs) (vsubst [w,x] b) in
               EXISTS (tm,w) th,st
    | [] -> failwith "PROVE: no witness"
  else if is_let tm then
    let eq = (RAND_CONV EVAL_CONV THENC let_CONV) tm in
    let th,st = PROVE (wits,subs) (rand(concl eq)) in
    EQ_MP (SYM eq) th,st
  else if is_relation tm then
    match subs with
      th::rest ->
        let eq = ARGS_EVAL_CONV tm in
        if aconv (rand(concl eq)) (concl th) then EQ_MP (SYM eq) th,(wits,rest)
        else (print_string "\nPROVE: wanted "; print_term(rand(concl eq));
              print_string "\n but have "; print_term(concl th);
              print_newline(); failwith "PROVE")
    | [] -> failwith "PROVE: no theorem"
  else EVAL_RULE tm,(wits,subs);;

let PROVE_ALL wits subs tm =
  let th,(wits',subs') = PROVE (wits,subs) tm in
  if wits' <> [] || subs' <> [] then failwith "PROVE_ALL: left over" else th;;

(* The instance of the k-th clause of the rules for the values vals.         *)

let RULE_INST rules k vals subs =
  let th = SPECL vals (el k (CONJUNCTS rules)) in
  CONV_RULE ARGS_EVAL_CONV (MP th (PROVE_ALL [] subs (lhand(concl th))));;

(* A defined predicate, from its definition, witnesses and theorems.         *)

let DEF_RULE def wits subs tm =
  let eq = REWR_CONV def tm in
  EQ_MP (SYM eq) (PROVE_ALL wits subs (rand(concl eq)));;

(* ------------------------------------------------------------------------- *)
(* Terms for OCaml values.                                                   *)
(* ------------------------------------------------------------------------- *)

let mk_n = mk_small_numeral;;

let mk_int c =
  let n = mk_comb(`int_of_num`,mk_n(abs c)) in
  if c < 0 then mk_comb(`int_neg`,n) else n;;

let mk_ints cs = mk_list(map mk_int cs,`:int`);;

let mk_nums ns = mk_list(map mk_n ns,`:num`);;

let mk_bool b = if b then `T` else `F`;;

(* ------------------------------------------------------------------------- *)
(* The spec's functions in OCaml, for the decoding decisions.                *)
(* ------------------------------------------------------------------------- *)

exception Reject of string;;

let obit (l:int array) j =
  if 0 <= j && j < 8 * Array.length l then (l.(j / 8) lsr (j mod 8)) land 1
  else 0;;

let obits l p n =
  let v = ref 0 in
  for i = n - 1 downto 0 do v := 2 * !v + obit l (p + i) done; !v;;

let oback l q k =
  let v = ref 0 in
  for i = k - 1 downto 0 do v := 2 * !v + obit l (q - k + i) done; !v;;

let obitsize n =
  let rec f k b = if k = 0 then b else f (k / 2) (b + 1) in f n 0;;

let ofield l pts p =
  let nb = obitsize (pts + 1) in
  let small = (1 lsl nb) - (pts + 2) in
  let v = obits l p nb in
  let lo = v mod (1 lsl (nb - 1)) in
  if lo < small then lo,p + nb - 1
  else if v < 1 lsl (nb - 1) then v,p + nb
  else v - small,p + nb;;

let opoints v = if v = 0 then 1 else v - 1;;

let oinside zstd l q = zstd || q <= 8 * Array.length l;;

let oreload zstd l p =
  let w = 8 * max (Array.length l) 8 in
  if zstd && w <= p then w - 32 + (p - w) mod 32 else p;;

let check b s = if not b then raise (Reject s);;

(* The FSE decoding table as an array of (symbol, nbits, base).              *)

let otable (cs:int list) alog =
  let size = 1 lsl alog in
  let step = size / 2 + size / 8 + 3 in
  let csa = Array.of_list cs in
  let n = Array.length csa in
  let sym = Array.make size (-1) in
  let high = ref size in
  for s = 0 to n - 1 do
    if csa.(s) = -1 then (decr high; sym.(!high) <- s) done;
  let pos = ref 0 in
  for s = 0 to n - 1 do
    for i = 1 to max csa.(s) 0 do ignore i;
      sym.(!pos) <- s;
      pos := (!pos + step) land (size - 1);
      while !pos >= !high do pos := (!pos + step) land (size - 1) done
    done
  done;
  let seen = Array.make n 0 in
  Array.init size (fun u ->
    let s = sym.(u) in
    let nxt = (if csa.(s) = -1 then 1 else csa.(s)) + seen.(s) in
    seen.(s) <- seen.(s) + 1;
    let nb = alog + 1 - obitsize nxt in
    s,nb,(1 lsl nb) * nxt - size);;

(* ------------------------------------------------------------------------- *)
(* Derivations of the relations.                                             *)
(* ------------------------------------------------------------------------- *)

(* |- fse_zeros zstd l (k,z,p) (z',q), with z' and q.                        *)

let FSE_ZEROS_DERIV zstd inp k z p =
  let l = inp.bytes in
  let rules = SPECL [mk_bool zstd; inp.ltm] FSE_ZEROS_RULES in
  let rec go k z p =
    let f = obits l p 2 in
    check (oinside zstd l (p + 2)) "NCount beyond the input";
    if f < 3 then
      RULE_INST rules 0 [mk_n k; mk_n z; mk_n p] [],
      (z + f,oreload zstd l (p + 2))
    else if k < 11 then
      let th,res = go (k + 1) (z + 3) (p + 2) in
      RULE_INST rules 1 [mk_n k; mk_n z; mk_n p; rand(concl th)] [th],res
    else
      let th,res = go 0 (z + 3) (oreload zstd l (p + 2)) in
      RULE_INST rules 2 [mk_n z; mk_n p; rand(concl th)] [th],res in
  go k z p;;

(* |- fse_counts zstd l n (pts,cs,p) (cs',q), with cs' and q.                *)

let FSE_COUNTS_DERIV zstd inp n pts cs p =
  let l = inp.bytes in
  let rules = SPECL [mk_bool zstd; inp.ltm; mk_n n] FSE_COUNTS_RULES in
  let rec go pts cs p =
    check (length cs < n) "too many symbols in NCount";
    let v,q = ofield l pts p in
    check (oinside zstd l q) "NCount beyond the input";
    let vals = [mk_n pts; mk_ints cs; mk_n p] in
    if opoints v = pts then
      RULE_INST rules 0 (vals @ [mk_n v; mk_n q]) [],(cs @ [v - 1],q)
    else if v <> 1 && opoints v < pts then
      let th,res = go (pts - opoints v) (cs @ [v - 1]) (oreload zstd l q) in
      RULE_INST rules 1 (vals @ [mk_n v; mk_n q; rand(concl th)]) [th],res
    else if v = 1 then
      let zth,(z,q') = FSE_ZEROS_DERIV zstd inp 0 0 (oreload zstd l q) in
      let th,res = go pts (cs @ replicate 0 (z + 1)) q' in
      RULE_INST rules 2 (vals @ [mk_n q; mk_n z; mk_n q'; rand(concl th)])
        [zth; th],res
    else raise (Reject "NCount overshoots the total") in
  go pts cs p;;

(* |- fse_ncount zstd maxalog n l (cs,alog,m), with cs, alog and m.          *)

let FSE_NCOUNT_DERIV zstd maxalog n inp =
  let alog = obits inp.bytes 0 4 + 5 in
  check (alog <= maxalog) "accuracy log too large";
  let th,(cs,q) = FSE_COUNTS_DERIV zstd inp n (1 lsl alog) [] 4 in
  check (q <= 8 * Array.length inp.bytes) "NCount beyond the input";
  let m = (q + 7) / 8 in
  let tm = list_mk_icomb "fse_ncount"
    [mk_bool zstd; mk_n maxalog; mk_n n; inp.ltm;
     mk_pair(mk_ints cs,mk_pair(mk_n alog,mk_n m))] in
  DEF_RULE fse_ncount [mk_n q] [th] tm,(cs,alog,m);;

(* |- fse_weights cs alog st (s,s',q,ws) w, with w.                          *)

let FSE_WEIGHTS_DERIV cs alog st s s2 q ws =
  let table = otable cs alog in
  let rules = SPECL [mk_ints cs; mk_n alog; st.ltm] FSE_WEIGHTS_RULES in
  let rec go s s2 q ws =
    check (length ws + 2 <= 255) "too many weights";
    let sym,nb,base = table.(s) in
    let vals = [mk_n s; mk_n s2; mk_n q; mk_nums ws] in
    if q < nb then
      let sym2,_,_ = table.(s2) in
      RULE_INST rules 0 vals [],ws @ [sym; sym2]
    else
      let th,res = go s2 (base + oback st.bytes q nb) (q - nb) (ws @ [sym]) in
      RULE_INST rules 1 (vals @ [rand(concl th)]) [th],res in
  go s s2 q ws;;

(* |- zstd_end st r, with r.                                                 *)

let oend (st:int array) =
  let n = Array.length st in
  check (n > 0) "empty stream";
  check (st.(n - 1) <> 0) "last byte of stream is 0";
  8 * (n - 1) + obitsize st.(n - 1) - 1;;

(* |- fse_weight_block zstd blk w, with w.                                   *)

let FSE_WEIGHT_BLOCK_DERIV zstd blk =
  let nth,(cs,alog,m) =
    FSE_NCOUNT_DERIV zstd 6 (if zstd then 256 else 12) blk in
  check (not zstd || length cs <= (if alog = 6 then 12 else 92))
    "too many symbols for the workspace";
  let st = input_of(mk_bytes(Array.to_list(Array.sub blk.bytes m
                               (Array.length blk.bytes - m)))) in
  let r = oend st.bytes in
  check (2 * alog <= r) "initial states beyond the stream";
  let wth,w = FSE_WEIGHTS_DERIV cs alog st (oback st.bytes r alog)
                (oback st.bytes (r - alog) alog) (r - 2 * alog) [] in
  let tm = list_mk_icomb "fse_weight_block"
             [mk_bool zstd; blk.ltm; mk_nums w] in
  DEF_RULE fse_weight_block [mk_ints cs; mk_n alog; mk_n m; mk_n r]
    [nth; wth] tm,w;;

(* |- huf_header zstd l w h, with w and h.                                   *)

let HUF_HEADER_DERIV zstd inp =
  let l = inp.bytes in
  check (Array.length l > 0) "no tree description";
  let b = l.(0) in
  let eq = REWR_CONV huf_header in
  if b >= 128 then
    let h = 1 + (b - 126) / 2 in
    check (h <= Array.length l) "raw weights beyond the input";
    let w = map (fun i -> if i mod 2 = 0 then l.(1 + i / 2) / 16
                          else l.(1 + i / 2) mod 16) (0--(b - 128)) in
    let tm = list_mk_icomb "huf_header"
               [mk_bool zstd; inp.ltm; mk_nums w; mk_n h] in
    let th = eq tm in
    let a,d = dest_conj(rand(concl th)) in
    let l1,_ = dest_disj d in
    EQ_MP (SYM th) (CONJ (EVAL_RULE a) (DISJ1 (PROVE_ALL [] [] l1) (rand d))),
    (w,h)
  else
    let h = 1 + b in
    check (h <= Array.length l) "FSE weights beyond the input";
    let blk = input_of(mk_bytes(Array.to_list(Array.sub l 1 (h - 1)))) in
    let bth,w = FSE_WEIGHT_BLOCK_DERIV zstd blk in
    let tm = list_mk_icomb "huf_header"
               [mk_bool zstd; inp.ltm; mk_nums w; mk_n h] in
    let th = eq tm in
    let a,d = dest_conj(rand(concl th)) in
    let l1,r1 = dest_disj d in
    EQ_MP (SYM th) (CONJ (EVAL_RULE a) (DISJ2 l1 (PROVE_ALL [] [bth] r1))),
    (w,h);;

(* |- huf_weights zstd l ws ml h, with ws, ml and h.                         *)

let HUF_WEIGHTS_DERIV zstd inp =
  let hth,(w,h) = HUF_HEADER_DERIV zstd inp in
  check (forall (fun x -> x <= 13) w) "tree too deep";
  let total =
    itlist (fun x a -> if x = 0 then a else a + (1 lsl (x - 1))) w 0 in
  check (total <> 0) "all weights zero";
  let ml = obitsize total in
  check (ml <= (if zstd then 12 else 11)) "tree too deep";
  let rest = (1 lsl ml) - total in
  let k = obitsize rest - 1 in
  check (rest = 1 lsl k) "last weight not a power of 2";
  let ws = w @ [k + 1] in
  check (mem 1 ws) "no code of the maximum length";
  let tm = list_mk_icomb "huf_weights"
             [mk_bool zstd; inp.ltm; mk_nums ws; mk_n ml; mk_n h] in
  DEF_RULE huf_weights [mk_nums w; mk_n k] [hth] tm,(ws,ml,h);;

(* The symbols of a Huffman-coded stream, read with the code of ws, ml.      *)

let ostream ws ml (st:int array) n =
  let r = oend st in
  let wsa = Array.of_list ws in
  let codes = Hashtbl.create 256 in
  let order = sort (<) (filter (fun (x,_) -> x <> 0)
                 (map (fun s -> wsa.(s),s) (0--(Array.length wsa - 1)))) in
  ignore(itlist (fun (x,s) start ->
           Hashtbl.add codes (ml + 1 - x,start / (1 lsl (x - 1))) s;
           start + (1 lsl (x - 1))) (rev order) 0);
  let q = ref r and out = ref [] in
  for i = 1 to n do ignore i;
    let rec find nb =
      check (nb <= ml) "no code matches the stream";
      if nb <= !q &&
         Hashtbl.mem codes (nb,oback st !q nb) then
        (out := Hashtbl.find codes (nb,oback st !q nb) :: !out;
         q := !q - nb)
      else find (nb + 1) in
    find 1
  done;
  check (!q = 0) "stream not consumed exactly";
  rev !out;;

(* |- huf_decompress1x1 zstd l out, for the input bs and n output bytes.     *)

let HUF_DECOMPRESS1X1_RULE zstd (bs:int list) n =
  let inp = input_of(mk_bytes bs) in
  let wth,(ws,ml,h) = HUF_WEIGHTS_DERIV zstd inp in
  check (h < Array.length inp.bytes) "no stream after the tree description";
  let st = Array.sub inp.bytes h (Array.length inp.bytes - h) in
  let out = ostream ws ml st n in
  let tm = list_mk_icomb "huf_decompress1x1"
             [mk_bool zstd; inp.ltm; mk_bytes out] in
  DEF_RULE huf_decompress1x1 [mk_nums ws; mk_n ml; mk_n h] [wth] tm;;

(* |- huf_decompress4x1 zstd l out, for the input bs and n output bytes.     *)

let HUF_DECOMPRESS4X1_RULE zstd (bs:int list) n =
  let inp = input_of(mk_bytes bs) in
  let wth,(ws,ml,h) = HUF_WEIGHTS_DERIV zstd inp in
  check (h < Array.length inp.bytes) "no stream after the tree description";
  let blk = Array.sub inp.bytes h (Array.length inp.bytes - h) in
  check (Array.length blk >= 6) "no jump table";
  let jump k = blk.(2 * k) + 256 * blk.(2 * k + 1) in
  let s1 = jump 0 and s2 = jump 1 and s3 = jump 2 and q = (n + 3) / 4 in
  let a4 = 6 + s1 + s2 + s3 in
  check (a4 <= Array.length blk) "streams past the end of the block";
  check (3 * q <= n) "no fourth segment";
  check (not zstd || 6 <= n) "fewer than 6 bytes in four streams";
  let out = ostream ws ml (Array.sub blk 6 s1) q @
            ostream ws ml (Array.sub blk (6 + s1) s2) q @
            ostream ws ml (Array.sub blk (6 + s1 + s2) s3) q @
            ostream ws ml (Array.sub blk a4 (Array.length blk - a4))
              (n - 3 * q) in
  let stm = list_mk_icomb "huf_streams4"
              [mk_bool zstd; mk_nums ws; mk_n ml;
               mk_bytes(Array.to_list blk); mk_bytes out] in
  let sth = EQT_ELIM((REWR_CONV huf_streams4 THENC
                      TOP_DEPTH_CONV let_CONV THENC EVAL_CONV) stm) in
  let tm = list_mk_icomb "huf_decompress4x1"
             [mk_bool zstd; inp.ltm; mk_bytes out] in
  DEF_RULE huf_decompress4x1 [mk_nums ws; mk_n ml; mk_n h] [wth; sth] tm;;
