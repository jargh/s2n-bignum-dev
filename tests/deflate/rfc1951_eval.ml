(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof-producing decoding for the RFC 1951 spec. DEFLATE_DECODE_RULE bs    *)
(* proves |- deflate_decode l out n for the byte list l with the values bs,  *)
(* following the inductive relations step by step: the decoding decisions    *)
(* are made in OCaml, and every one of them is checked in HOL. Intended for  *)
(* small inputs (it computes with explicit lists).                           *)
(* ========================================================================= *)

needs "tests/deflate/rfc1951_checks.ml";;

(* ------------------------------------------------------------------------- *)
(* Explicit lists of numerals or words: EL, LENGTH and APPEND.               *)
(* ------------------------------------------------------------------------- *)

let EL_CONV =
  let pth0 = prove(`!h:A t. EL 0 (CONS h t) = h`, REWRITE_TAC[EL; HD])
  and pthS = prove(`!h:A t n. EL (SUC n) (CONS h t) = EL n t`,
                   REWRITE_TAC[EL; TL]) in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("EL",_),k),l) ->
        if dest_small_numeral k = 0 then PART_MATCH lhs pth0 tm else
        let th1 = RATOR_CONV(RAND_CONV num_CONV) tm in
        let th2 = PART_MATCH lhs pthS (rand(concl th1)) in
        TRANS th1 (TRANS th2 (conv(rand(concl th2))))
    | _ -> failwith "EL_CONV" in
  conv;;

let LENGTH_CONV = REWRITE_CONV[LENGTH] THENC NUM_REDUCE_CONV;;

let APPEND_CONV = REWRITE_CONV[APPEND];;

(* A memo table for EL i l, for a fixed explicit list l.                     *)

let el_table ltm =
  let n = length(dest_list ltm) in
  Array.init n
   (fun i -> EL_CONV(list_mk_icomb "EL" [mk_small_numeral i; ltm]));;

let EL_TABLE_CONV ltm tab tm =
  match tm with
    Comb(Comb(Const("EL",_),k),l) when l = ltm -> tab.(dest_small_numeral k)
  | _ -> failwith "EL_TABLE_CONV";;

(* ------------------------------------------------------------------------- *)
(* The input: bits, and numbers from bits in both orders.                    *)
(* ------------------------------------------------------------------------- *)

type input = {ltm : term; bytes : int array; bitf : int -> thm;
              lenth : thm};;

let make_input (bs:int list) =
  let ltm = mk_list(map (fun b -> mk_comb(`word:num->byte`,mk_small_numeral b))
                        bs,`:byte`) in
  let tab = el_table ltm in
  let byte_conv = EL_TABLE_CONV ltm tab in
  let bconv = REWR_CONV deflate_bit THENC
              RATOR_CONV(RAND_CONV NUM_REDUCE_CONV) THENC
              RAND_CONV(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV) THENC
                        byte_conv) THENC
              WORD_REDUCE_CONV in
  let memo = Hashtbl.create 1000 in
  let bitf i =
    try Hashtbl.find memo i with Not_found ->
    let th = bconv(list_mk_icomb "deflate_bit" [ltm; mk_small_numeral i]) in
    Hashtbl.add memo i th; th in
  {ltm = ltm; bytes = Array.of_list bs; bitf = bitf;
   lenth = LENGTH_CONV(list_mk_icomb "LENGTH" [ltm])};;

let BITVAL_CONV = GEN_REWRITE_CONV I [BITVAL_CLAUSES];;

let DEFLATE_BITS_CONV inp =
  let b0,bS = CONJ_PAIR deflate_bits in
  let rec conv tm =
    let n = dest_small_numeral(rand tm) in
    if n = 0 then REWR_CONV b0 tm else
    let p = dest_small_numeral(rand(rator tm)) in
    (RAND_CONV num_CONV THENC REWR_CONV bS THENC
     LAND_CONV(RAND_CONV(fun _ -> inp.bitf p) THENC BITVAL_CONV) THENC
     RAND_CONV(RAND_CONV(RATOR_CONV(RAND_CONV NUM_ADD_CONV) THENC conv)) THENC
     NUM_REDUCE_CONV) tm in
  conv;;

let DEFLATE_CODEBITS_CONV inp =
  let b0,bS = CONJ_PAIR deflate_codebits in
  let rec conv tm =
    let n = dest_small_numeral(rand tm) in
    if n = 0 then REWR_CONV b0 tm else
    let p = dest_small_numeral(rand(rator tm)) in
    (RAND_CONV num_CONV THENC REWR_CONV bS THENC
     LAND_CONV(RAND_CONV(RAND_CONV(fun _ -> inp.bitf p) THENC
                         BITVAL_CONV)) THENC
     RAND_CONV(RATOR_CONV(RAND_CONV NUM_ADD_CONV) THENC conv) THENC
     NUM_REDUCE_CONV) tm in
  conv;;

(* Any subterm deflate_bits l p n or deflate_codebits l p n with numerals.   *)

let BITS_CONV inp tm =
  match tm with
    Comb(Comb(Comb(Const("deflate_bits",_),l),p),n)
      when l = inp.ltm && is_numeral p && is_numeral n ->
        DEFLATE_BITS_CONV inp tm
  | Comb(Comb(Comb(Const("deflate_codebits",_),l),p),n)
      when l = inp.ltm && is_numeral p && is_numeral n ->
        DEFLATE_CODEBITS_CONV inp tm
  | _ -> failwith "BITS_CONV";;

(* ------------------------------------------------------------------------- *)
(* Code tables: an explicit (or fixed) list of code lengths, with EL and     *)
(* LENGTH theorems and memoized huffman_code values.                         *)
(* ------------------------------------------------------------------------- *)

type table = {lens : int array; lterm : term; elconv : conv; lenth : thm;
              codes : (int,thm) Hashtbl.t; ocaml_code : int array;
              decode : (int * int,int) Hashtbl.t};;

let ocaml_codes lens =
  let n = Array.length lens in
  Array.init n (fun s ->
    let ls = lens.(s) in
    if ls = 0 then 0 else
    let a = ref 0 and b = ref 0 in
    for t = 0 to n - 1 do
      if lens.(t) <> 0 && lens.(t) < ls then a := !a + (1 lsl (ls - lens.(t)));
      if t < s && lens.(t) = ls then incr b
    done;
    !a + !b);;

let make_table lterm lens elconv lenth =
  let codes = ocaml_codes lens in
  let dec = Hashtbl.create 300 in
  Array.iteri (fun s l -> if l <> 0 then Hashtbl.replace dec (l,codes.(s)) s)
    lens;
  {lens = lens; lterm = lterm; elconv = elconv; lenth = lenth;
   codes = Hashtbl.create 300; ocaml_code = codes; decode = dec};;

let explicit_table (lens:int list) =
  let lterm = mk_list(map mk_small_numeral lens,`:num`) in
  let tab = el_table lterm in
  make_table lterm (Array.of_list lens) (EL_TABLE_CONV lterm tab)
    (LENGTH_CONV(list_mk_icomb "LENGTH" [lterm]));;

let fixed_ll_table =
  let ll = Array.init 288 (fun s -> if s < 144 then 8 else if s < 256 then 9
                                    else if s < 280 then 7 else 8) in
  make_table `deflate_fixed_ll` ll EL_FIXED_CONV
    (CONJUNCT1 LENGTH_DEFLATE_FIXED);;

let fixed_dl_table =
  make_table `deflate_fixed_dl` (Array.make 32 5) EL_FIXED_CONV
    (CONJUNCT2 LENGTH_DEFLATE_FIXED);;

let SUM_CONV tab =
  REWRITE_CONV[tab.lenth; CONJUNCT1 LT; EMPTY_GSPEC; CARD_CLAUSES] THENC
  SIMP_CONV[NSUM_RESTRICT_LT; CARD_RESTRICT_LT; ARITH_EQ] THENC
  NUM_REDUCE_CONV THENC
  DEPTH_CONV EXPAND_NSUM_CONV THENC
  DEPTH_CONV tab.elconv THENC
  NUM_REDUCE_CONV;;

let HUFFMAN_CODE_CONV tab tm =
  let s = match tm with
      Comb(Comb(Const("huffman_code",_),l),s) when l = tab.lterm ->
        dest_small_numeral s
    | _ -> failwith "HUFFMAN_CODE_CONV" in
  try Hashtbl.find tab.codes s with Not_found ->
  let th = (REWR_CONV huffman_code THENC SUM_CONV tab) tm in
  Hashtbl.add tab.codes s th; th;;

let HUFFMAN_KRAFT_CONV tab = REWR_CONV huffman_kraft THENC SUM_CONV tab;;

(* |- huffman_decode l lens p s q, for numerals p, s, q                      *)

let HUFFMAN_DECODE_RULE inp tab p s q =
  let tm = list_mk_icomb "huffman_decode"
    [inp.ltm; tab.lterm; mk_small_numeral p; mk_small_numeral s;
     mk_small_numeral q] in
  EQT_ELIM
   ((REWR_CONV huffman_decode THENC
     REWRITE_CONV[tab.lenth; inp.lenth] THENC
     DEPTH_CONV tab.elconv THENC NUM_REDUCE_CONV THENC
     ONCE_DEPTH_CONV(HUFFMAN_CODE_CONV tab) THENC
     DEPTH_CONV(BITS_CONV inp) THENC NUM_REDUCE_CONV) tm);;

(* ------------------------------------------------------------------------- *)
(* Decoding in OCaml, mirroring the relations.                               *)
(* ------------------------------------------------------------------------- *)

exception Bad of string;;

let bitv inp i =
  if i >= 8 * Array.length inp.bytes then raise (Bad "out of input") else
  (inp.bytes.(i / 8) lsr (i mod 8)) land 1;;

let bitsv inp p n =
  let v = ref 0 in
  for i = n - 1 downto 0 do v := 2 * !v + bitv inp (p + i) done;
  !v;;

let codebitsv inp p n =
  let v = ref 0 in for i = 0 to n - 1 do v := 2 * !v + bitv inp (p + i) done;
  !v;;

let decodev inp tab p =
  let rec loop l =
    if l > 15 then raise (Bad "no symbol") else
    try let s = Hashtbl.find tab.decode (l,codebitsv inp p l) in (s,p + l)
    with Not_found -> loop (l + 1) in
  loop 1;;

let length_base = [|3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 15; 17; 19; 23; 27; 31;
                    35; 43; 51; 59; 67; 83; 99; 115; 131; 163; 195; 227; 258|]
and length_extra = [|0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 2; 2; 2; 2;
                     3; 3; 3; 3; 4; 4; 4; 4; 5; 5; 5; 5; 0|]
and dist_base = [|1; 2; 3; 4; 5; 7; 9; 13; 17; 25; 33; 49; 65; 97; 129; 193;
                  257; 385; 513; 769; 1025; 1537; 2049; 3073; 4097; 6145;
                  8193; 12289; 16385; 24577|]
and dist_extra = [|0; 0; 0; 0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6;
                   7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 12; 13; 13|];;

(* ------------------------------------------------------------------------- *)
(* Outputs are explicit lists of words, kept also as OCaml int lists.        *)
(* ------------------------------------------------------------------------- *)

let mk_out (bs:int list) =
  mk_list(map (fun b -> mk_comb(`word:num->byte`,mk_small_numeral b)) bs,
          `:byte`);;

(* lz77_copy out d n, for an explicit out and numerals d, n.                 *)

let LZ77_COPY_CONV =
  let c0,cS = CONJ_PAIR lz77_copy in
  let rec conv tm =
    let n = dest_small_numeral(rand tm) in
    if n = 0 then REWR_CONV c0 tm else
    (RAND_CONV num_CONV THENC REWR_CONV cS THENC
     RATOR_CONV(RATOR_CONV(RAND_CONV
      (RAND_CONV(RATOR_CONV(RAND_CONV
        (RATOR_CONV(RAND_CONV(LAND_CONV LENGTH_CONV THENC NUM_SUB_CONV)) THENC
         EL_CONV))) THENC APPEND_CONV))) THENC
     conv) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Evaluating side conditions, and proving existentials with witnesses.      *)
(* ------------------------------------------------------------------------- *)

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

(* Normalize list expressions in the outputs and code length lists.          *)

let LISTS_CONV =
  NUM_REDUCE_CONV THENC
  DEPTH_CONV(LZ77_COPY_CONV ORELSEC REPLICATE_CONV) THENC
  REWRITE_CONV[APPEND; LAST; NOT_CONS_NIL] THENC
  DEPTH_CONV EL_CONV;;

let TRANSPORT target th =
  let eq = LISTS_CONV target in
  if rand(concl eq) = concl th then EQ_MP (SYM eq) th
  else (print_term (rand(concl eq)); print_newline();
        print_term (concl th); failwith "TRANSPORT");;

let SIDE_CONV inp tabs =
  let hd_conv tm =
    match strip_comb tm with
      Const("huffman_decode",_),[l;lt;p;s;q]
        when l = inp.ltm && is_numeral p && is_numeral s && is_numeral q ->
          let tab = find (fun t -> t.lterm = lt) tabs in
          EQT_INTRO(HUFFMAN_DECODE_RULE inp tab (dest_small_numeral p)
                      (dest_small_numeral s) (dest_small_numeral q))
    | _ -> failwith "hd_conv" in
  REWRITE_CONV[deflate_length_base; deflate_length_extra; deflate_dist_base;
               deflate_dist_extra; deflate_clen_order; inp.lenth] THENC
  NUM_REDUCE_CONV THENC DEPTH_CONV EL_CONV THENC NUM_REDUCE_CONV THENC
  DEPTH_CONV(BITS_CONV inp) THENC NUM_REDUCE_CONV THENC
  DEPTH_CONV hd_conv THENC
  LENGTH_CONV THENC REWRITE_CONV[] THENC NUM_REDUCE_CONV;;

let SIDE_RULE inp tabs tm =
  let th = SIDE_CONV inp tabs tm in
  if rand(concl th) = `T` then EQT_ELIM th
  else (print_term (rand(concl th)); failwith "SIDE_RULE");;

(* Prove ?x1 ... xn. P given witnesses and a prover for the instance of P.   *)

let rec EXISTS_RULE tm wits prove_body =
  match wits with
    [] -> prove_body tm
  | w::ws -> let x,b = dest_exists tm in
             EXISTS (tm,w) (EXISTS_RULE (vsubst [w,x] b) ws prove_body);;

(* Prove a conjunction whose conjuncts are each handled by one of provers.   *)

let rec CONJ_RULE provers tm =
  let attempt p t =
    try p t with Failure s ->
      (print_string "\nCONJ_RULE failed on: "; print_term t;
       print_newline(); failwith s) in
  match provers with
    [p] -> attempt p tm
  | p::ps -> let l,r = dest_conj tm in
             CONJ (attempt p l) (CONJ_RULE ps r)
  | [] -> failwith "CONJ_RULE";;

let mk_n = mk_small_numeral;;

(* ------------------------------------------------------------------------- *)
(* The compressed data of a block.                                           *)
(* ------------------------------------------------------------------------- *)

type cstep = Clit of int * int * int
           | Cpair of int * int * int * int * int * int * int * int
           | Ceob of int * int;;

let decode_codes inp ll dl out p =
  let rec loop out p acc =
    let s,q = decodev inp ll p in
    if s = 256 then (List.rev ((Ceob(p,q),out)::acc), out, q)
    else if s < 256 then loop (out @ [s]) q ((Clit(p,s,q),out)::acc)
    else begin
      if s > 285 then raise (Bad "bad length symbol");
      let i = s - 257 in
      let p1 = q in
      let d,p2 = decodev inp dl (p1 + length_extra.(i)) in
      if d >= 30 then raise (Bad "bad distance symbol");
      let q' = p2 + dist_extra.(d) in
      if q' > 8 * Array.length inp.bytes then raise (Bad "out of input");
      let len = length_base.(i) + bitsv inp p1 length_extra.(i)
      and dist = dist_base.(d) + bitsv inp p2 dist_extra.(d) in
      if dist > List.length out then raise (Bad "distance too far back");
      let ob = ref out in
      for jj = 1 to len do
        ob := !ob @ [List.nth !ob (List.length !ob - dist)]
      done;
      loop !ob q' ((Cpair(p,s,p1,d,p2,q',len,dist),out)::acc)
    end in
  loop out p [];;

let codes_chain inp ll dl steps =
  let [r1;r2;r3] = CONJUNCTS(SPECL [inp.ltm; ll.lterm; dl.lterm]
                               DEFLATE_CODES_RULES) in
  let side = SIDE_RULE inp [ll; dl] in
  let rec chain steps =
    match steps with
      [Ceob(p,q),out] ->
        MP (SPECL [mk_out out; mk_n p; mk_n q] r1)
           (HUFFMAN_DECODE_RULE inp ll p 256 q)
    | (Clit(p,s,q),out)::rest ->
        let nth = chain rest in
        let th = SPECL [mk_out out; mk_n p; mk_n q; mk_n s; rand(concl nth)]
                   r2 in
        MP th (CONJ_RULE [side; side; (fun t -> TRANSPORT t nth)]
                 (lhand(concl th)))
    | (Cpair(p,s,p1,d,p2,q,len,dist),out)::rest ->
        let nth = chain rest in
        let th = SPECL [mk_out out; mk_n p; mk_n q; mk_n len; mk_n dist;
                        rand(concl nth)] r3 in
        let lendist tm =
          let th1 = REWR_CONV deflate_lendist tm in
          EQ_MP (SYM th1) (EXISTS_RULE (rand(concl th1))
                             (map mk_n [s; p1; d; p2]) side) in
        MP th (CONJ_RULE [lendist;
                          (fun t -> EQT_ELIM(LENGTH_CONV t));
                          (fun t -> TRANSPORT t nth)]
                 (lhand(concl th)))
    | _ -> failwith "codes_chain" in
  chain steps;;

(* ------------------------------------------------------------------------- *)
(* Run-length coded code lengths.                                            *)
(* ------------------------------------------------------------------------- *)

type lstep = Llit of int * int * int        (* p, s, q *)
           | Lrep of int * int * int * int  (* p, symbol 16/17/18, q, k *)
           | Ldone of int;;                 (* p *)

let decode_lengths inp cl n p =
  let rec loop lens p acc =
    if List.length lens = n then (List.rev ((Ldone p,lens)::acc), lens, p)
    else
      let s,q = decodev inp cl p in
      if s < 16 then loop (lens @ [s]) q ((Llit(p,s,q),lens)::acc)
      else
        let x,e,k =
          if s = 16 then
            (if lens = [] then raise (Bad "repeat with no previous length")
             else (List.nth lens (List.length lens - 1),2,3 + bitsv inp q 2))
          else if s = 17 then (0,3,3 + bitsv inp q 3)
          else (0,7,11 + bitsv inp q 7) in
        if q + e > 8 * Array.length inp.bytes then raise (Bad "out of input");
        if List.length lens + k > n then raise (Bad "too many lengths");
        loop (lens @ Array.to_list(Array.make k x)) (q + e)
             ((Lrep(p,s,q,k),lens)::acc) in
  loop [] p [];;

let mk_nums l = mk_list(map mk_small_numeral l,`:num`);;

let lengths_chain inp cl n steps =
  let [r1;r2;r3;r4;r5] =
    CONJUNCTS(SPECL [inp.ltm; cl.lterm; mk_n n] DEFLATE_LENGTHS_RULES) in
  let side = SIDE_RULE inp [cl] in
  let rec chain steps =
    match steps with
      [Ldone p,lens] ->
        MP (SPECL [mk_nums lens; mk_n p] r1)
           (EQT_ELIM(LENGTH_CONV(lhand(concl(SPECL [mk_nums lens; mk_n p]
                                                  r1)))))
    | (Llit(p,s,q),lens)::rest ->
        let nth = chain rest in
        let th = SPECL [mk_nums lens; mk_n p; mk_n q; mk_n s; rand(concl nth)]
                   r2 in
        MP th (CONJ_RULE [(fun t -> EQT_ELIM(LENGTH_CONV t)); side; side;
                          (fun t -> TRANSPORT t nth)] (lhand(concl th)))
    | (Lrep(p,s,q,k),lens)::rest ->
        let nth = chain rest in
        let r = if s = 16 then r3 else if s = 17 then r4 else r5 in
        let th = SPECL [mk_nums lens; mk_n p; mk_n q; mk_n k; rand(concl nth)]
                   r in
        let rules = if s = 16 then
          [side; (fun t -> EQT_ELIM(REWRITE_CONV[NOT_CONS_NIL] t)); side;
           side; (fun t -> EQT_ELIM(LENGTH_CONV t));
           (fun t -> TRANSPORT t nth)]
        else [side; side; side; (fun t -> EQT_ELIM(LENGTH_CONV t));
              (fun t -> TRANSPORT t nth)] in
        MP th (CONJ_RULE rules (lhand(concl th)))
    | _ -> failwith "lengths_chain" in
  chain steps;;

(* ------------------------------------------------------------------------- *)
(* Blocks.                                                                   *)
(* ------------------------------------------------------------------------- *)

let STORED_RULE inp out p =
  (* |- deflate_stored l (out,p) (out',q) and the new out', q *)
  let a = 8 * ((p + 7) / 8) in
  if a + 32 > 8 * Array.length inp.bytes then raise (Bad "out of input");
  let n = bitsv inp a 16 in
  if bitsv inp (a + 16) 16 <> 65535 - n then raise (Bad "NLEN mismatch");
  if a + 32 + 8 * n > 8 * Array.length inp.bytes then
    raise (Bad "out of input");
  let out' = out @ Array.to_list(Array.sub inp.bytes (a / 8 + 4) n) in
  let q = a + 32 + 8 * n in
  let r = mk_pair(mk_out out',mk_n q) in
  let tm = list_mk_icomb "deflate_stored"
             [inp.ltm; mk_pair(mk_out out,mk_n p); r] in
  let th1 = REWR_CONV deflate_stored tm in
  let byte_tab = el_table inp.ltm in
  let last tm =
    EQT_ELIM((RAND_CONV(LAND_CONV(RAND_CONV
               (LIST_OF_SEQ_CONV THENC NUM_REDUCE_CONV THENC
                DEPTH_CONV(EL_TABLE_CONV inp.ltm byte_tab)) THENC
               APPEND_CONV) THENC NUM_REDUCE_CONV) THENC
              REWRITE_CONV[PAIR_EQ]) tm) in
  let side = SIDE_RULE inp [] in
  (EQ_MP (SYM th1)
     (EXISTS_RULE (rand(concl th1)) [mk_n a; mk_n n]
        (CONJ_RULE [side; side; side; side; last])),
   out',q);;

let ok_rule tm =
  (* huffman_ok L for an explicit list L *)
  let lens = map dest_small_numeral (dest_list(rand tm)) in
  let tab = explicit_table lens in
  EQT_ELIM((REWR_CONV huffman_ok THENC
            ONCE_DEPTH_CONV(HUFFMAN_KRAFT_CONV tab) THENC
            NUM_REDUCE_CONV THENC REWRITE_CONV[ALL] THENC
            NUM_REDUCE_CONV) tm);;

let DYNAMIC_RULE inp out p =
  if p + 14 > 8 * Array.length inp.bytes then raise (Bad "out of input");
  let nlen = 257 + bitsv inp p 5 and ndist = 1 + bitsv inp (p + 5) 5
  and ncode = 4 + bitsv inp (p + 10) 4 in
  if nlen > 286 || ndist > 30 then raise (Bad "bad counts");
  if p + 14 + 3 * ncode > 8 * Array.length inp.bytes then
    raise (Bad "out of input");
  let order = [|16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14;
                1; 15|] in
  let cla = Array.make 19 0 in
  for i = 0 to ncode - 1 do cla.(order.(i)) <- bitsv inp (p + 14 + 3 * i) 3
  done;
  let cl = explicit_table (Array.to_list cla) in
  let steps,lens,q =
    decode_lengths inp cl (nlen + ndist) (p + 14 + 3 * ncode) in
  let lensa = Array.of_list lens in
  let ll = explicit_table (Array.to_list(Array.sub lensa 0 nlen))
  and dl = explicit_table (Array.to_list(Array.sub lensa nlen ndist)) in
  let csteps,out',q' = decode_codes inp ll dl out q in
  let lth = lengths_chain inp cl (nlen + ndist) steps in
  let cth = codes_chain inp ll dl csteps in
  let r = rand(concl cth) in
  let tm = list_mk_icomb "deflate_dynamic"
             [inp.ltm; mk_pair(mk_out out,mk_n p); r] in
  let th1 = REWR_CONV deflate_dynamic tm in
  let side = SIDE_RULE inp [] in
  let clens tm =
    EQT_ELIM((EXPAND_CASES_CONV THENC SIDE_CONV inp []) tm) in
  let kraft tm =
    EQT_ELIM((LAND_CONV(HUFFMAN_KRAFT_CONV cl) THENC NUM_REDUCE_CONV) tm) in
  let subs = LIST_OF_SEQ_CONV THENC DEPTH_CONV EL_CONV THENC NUM_REDUCE_CONV
                              THENC DEPTH_CONV EL_CONV in
  let viasubs th tm =
    let eq = (DEPTH_CONV(fun t -> if fst(strip_comb t) =
                                     `list_of_seq:(num->num)->num->num list`
                                  then subs t else failwith "") THENC
              NUM_REDUCE_CONV) tm in
    if rand(concl eq) = concl th then EQ_MP (SYM eq) th
    else (print_term(rand(concl eq)); print_newline(); print_term(concl th);
          failwith "viasubs") in
  let okc tm = ok_rule (rand(concl(RAND_CONV subs tm))) |>
               EQ_MP (SYM(RAND_CONV subs tm)) in
  let body = CONJ_RULE
    [side; side; side; side; side; side;
     (fun t -> EQT_ELIM(LENGTH_CONV t)); clens; kraft;
     viasubs lth;
     (fun t -> EQT_ELIM((DEPTH_CONV EL_CONV THENC NUM_REDUCE_CONV) t));
     okc; okc; viasubs cth] in
  (EQ_MP (SYM th1)
     (EXISTS_RULE (rand(concl th1))
        [mk_n nlen; mk_n ndist; mk_n ncode; cl.lterm; mk_nums lens; mk_n q]
        body),
   out',q');;

let BLOCK_RULE inp btype out p =
  (* |- deflate_block l btype (out,p) r, with the new output and position *)
  let bth,out',q =
    if btype = 0 then STORED_RULE inp out p
    else if btype = 1 then
      let steps,out',q =
        decode_codes inp fixed_ll_table fixed_dl_table out p in
      codes_chain inp fixed_ll_table fixed_dl_table steps,out',q
    else if btype = 2 then DYNAMIC_RULE inp out p
    else raise (Bad "block type 3") in
  let r = rand(concl bth) in
  let tm = list_mk_icomb "deflate_block"
             [inp.ltm; mk_n btype; mk_pair(mk_out out,mk_n p); r] in
  let th1 = REWR_CONV deflate_block tm in
  let d = rand(concl th1) in
  let a,bc = dest_disj d in
  let b,c = dest_disj bc in
  let pick t = CONJ (REFL(lhand(lhand t))) bth in
  let dth = if btype = 0 then DISJ1 (pick a) bc
            else if btype = 1 then DISJ2 a (DISJ1 (pick b) c)
            else DISJ2 a (DISJ2 b (pick c)) in
  (EQ_MP (SYM th1) dth,out',q);;

let DEFLATE_DECODE_RULE bs =
  let inp = make_input bs in
  let [f1;f2] = CONJUNCTS(SPEC inp.ltm DEFLATE_BLOCKS_RULES) in
  let side = SIDE_RULE inp [] in
  let rec blocks out p =
    if p + 3 > 8 * Array.length inp.bytes then raise (Bad "out of input");
    let final = bitv inp p = 1 and btype = bitsv inp (p + 1) 2 in
    let bth,out',q = BLOCK_RULE inp btype out (p + 3) in
    if final then
      let th = SPECL [mk_out out; mk_n p; rand(concl bth)] f1 in
      MP th (CONJ_RULE [side; (fun t -> EQT_ELIM(inp.bitf p));
                        (fun t -> let eq = (NUM_REDUCE_CONV THENC
                                    DEPTH_CONV(BITS_CONV inp)) t in
                                  EQ_MP (SYM eq) bth)]
                 (lhand(concl th)))
    else
      let nth = blocks out' q in
      let th = SPECL [mk_out out; mk_n p; rand(concl nth); rand(concl bth)] f2
      in
      MP th (CONJ_RULE [side;
                        (fun t -> EQ_MP (SYM(RAND_CONV(fun _ -> inp.bitf p) t
                                            |> CONV_RULE(RAND_CONV
                                               (REWRITE_CONV[]))))
                                    TRUTH);
                        (fun t -> let eq = (NUM_REDUCE_CONV THENC
                                    DEPTH_CONV(BITS_CONV inp)) t in
                                  EQ_MP (SYM eq) bth);
                        (fun t -> nth)]
                 (lhand(concl th))) in
  let bth = blocks [] 0 in
  let outq = rand(concl bth) in
  let out,q = dest_pair outq in
  let n = (dest_small_numeral q + 7) / 8 in
  let tm = list_mk_icomb "deflate_decode" [inp.ltm; out; mk_n n] in
  let th1 = REWR_CONV deflate_decode tm in
  EQ_MP (SYM th1)
    (EXISTS (rand(concl th1),q)
       (CONJ bth (EQT_ELIM(NUM_REDUCE_CONV
                    (mk_eq(mk_n n,mk_binop `(DIV)` (mk_binop `(+)` q `7`)
                                               `8`))))));;
