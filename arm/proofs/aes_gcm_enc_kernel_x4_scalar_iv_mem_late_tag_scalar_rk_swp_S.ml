(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of the SLOTHY-scheduled AES-GCM kernel                       *)
(*   aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S            *)
(*                                                                           *)
(* SELF-CONTAINED, SINGLE-FILE version: this file inlines the whole          *)
(* program-equivalence development (formerly the six files                   *)
(*   aes_gcm_enc_kernel_..._swp_equiv.ml, swp_equiv_leg2.ml,                 *)
(*   swp_equiv_preamble.ml, swp_equiv_tail.ml, swp_equiv_whole.ml,           *)
(*   swp_equiv_degenerate.ml)                                                *)
(* in dependency order, so the _swp_S kernel has ONE proof file matching its *)
(* name.                                                                     *)
(*                                                                           *)
(* STATUS: _swp_S is verified INDIRECTLY, by a whole-function PROGRAM        *)
(* EQUIVALENCE to its de-interleaved sibling _swp_deint, which has a direct  *)
(* cheat-free functional-correctness proof (..._SWP_DEINT_CORRECT, in        *)
(* aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_deint.ml).     *)
(* The two kernels are byte-identical outside the steady 4x-loop body        *)
(* [0x1ec,0x4b0); that block is the same 177-instruction multiset (identical *)
(* encodings, zero register renaming) in a dataflow-equivalent              *)
(* software-pipelined schedule.  So the equivalence is lockstep everywhere   *)
(* except that one reordered block.                                          *)
(*                                                                           *)
(* The six theorems at the very bottom (all axiom-free, all ensures2 from    *)
(* the shared entry 0x88 to the shared exit 0x710) together cover EVERY      *)
(* loop_count and EVERY loop_remain < 4:                                     *)
(*                                                                           *)
(*   loop_count    loop_remain   theorem                                     *)
(*   ----------    -----------   -------                                     *)
(*    >= 2          >= 1         ..._SWP_S_EQUIV_STEADY                       *)
(*    >= 2          =  0         ..._SWP_S_EQUIV_REM0                         *)
(*    =  1          >= 1         ..._SWP_S_EQUIV_LC1_REMPOS                   *)
(*    =  1          =  0         ..._SWP_S_EQUIV_LC1_REM0                     *)
(*    =  0          >= 1         ..._SWP_S_EQUIV_LC0_REMPOS                   *)
(*    =  0          =  0         ..._SWP_S_EQUIV_LC0_REM0                     *)
(*                                                                           *)
(* WORK IN PROGRESS: extend to a direct standalone functional-correctness    *)
(* theorem ..._SWP_S_CORRECT (an `ensures`, matching ..._SWP_DEINT_CORRECT),  *)
(* by transferring _swp_deint's correctness across the equivalence.  The      *)
(* full design (validated, mechanics resolved) - see also                     *)
(* ~/.claude/.../memory/gcm-deint-swp-equivalence.md:                         *)
(*                                                                           *)
(* TRANSFER CHAIN (this is the ONLY route: ensures2 -> single-program spec    *)
(* must pass through ensures_n; the montmul/montsqr proofs do exactly this    *)
(* via PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC in arm/proofs/equiv.ml):    *)
(*   deint ensures  --ENSURES_AND_EVENTUALLY_N_AT_PC_PROVES_ENSURES_N-->      *)
(*     deint ensures_n @ f_n1                                                  *)
(*   deint ensures_n /\ this-file's ensures2  --ENSURES_N_ENSURES2_CONJ-->    *)
(*     combined ensures2 (exit relation now carries deint's ABSOLUTE post     *)
(*     on the s1/deint side)                                                   *)
(*   combined ensures2  --ENSURES2_ENSURES_N-->  swpS ensures_n @ f_n2        *)
(*   swpS ensures_n  --ENSURES_N_ENSURES-->  swpS ensures    (FINAL; the      *)
(*     conclusion is a plain `ensures`, no ensures_n restatement needed)      *)
(*                                                                           *)
(* Two ingredients:                                                           *)
(*  (A) deint's step count is NOT re-derived: the ensures2 proved here already *)
(*      carries a concrete closed-form f_n1 (an nsum over the loop counts),   *)
(*      and ensures2 unfolds to nested eventually_n whose OUTER component is   *)
(*      exactly deint's `eventually_n arm (f_n1 s1) (\s1'. read PC s1' =      *)
(*      word(pc+0x710)) s1`.  EVENTUALLY_N_MONO collapses the inner (s2)       *)
(*      eventually_n, since `read PC s1' = pc+0x710` is already an s1-side     *)
(*      conjunct of the exit relation.  That yields deint's eventually_n_at_pc.*)
(*  (B) STRENGTHEN the exit relation (post_exit_body) from the current        *)
(*      (Q30 + bytes32(ivec_p+12)) to full output agreement s1=s2 at 0x710:   *)
(*        - out-buffer  bytes128(out_b+16i), i<nblocks: frame-stable across    *)
(*          the postamble (neither side writes out_b); forward the entry       *)
(*          forall (rem_accum_at loop_remain = nblocks blocks) by frame.       *)
(*        - tag bytes128 tag_p: from Q30 equality (postamble does rev64 v30 ;  *)
(*          str q30,[x3=tag_p]); read-of-store gives bytes128 tag_p = Q30 s5.  *)
(*        - ivec bytes128 ivec_p: the kernel writes ONLY ivec[12..16) (the     *)
(*          full `str [ivec]` is commented out); ivec[0..12) is never written. *)
(*          bytes32(ivec_p+12) equality is already proven; ivec[0..12) is      *)
(*          frame-stable from the 0x88 entry, where entry88 pins the absolute  *)
(*          value read(bytes128 ivec_p) = word_reversefields 8 (ctr_block      *)
(*          nonce 2) on BOTH sides.  Thread ivec[0..12) as an f_ptr-style      *)
(*          frame graft, or split bytes128 = bytes12 ++ bytes32.               *)
(*      Strengthening post_exit_body propagates to all six SWP_DEINT_SWPS_     *)
(*      EQUIV_* theorems automatically (they carry POSTAMBLE's exit to 0x710   *)
(*      via trans_weaken); only the WEAKEN_* lemmas need re-proving (MESON).   *)
(*                                                                           *)
(* The final assembly file must `needs` BOTH this equivalence and the          *)
(* _swp_deint correctness proof (aes_gcm_..._swp_deint.ml, ..._SWP_DEINT_     *)
(* CORRECT / DEINT_FROM88).  ENSURES2_ENSURES_N's 3 side-conditions: (a) exists*)
(* deint entry state given a swpS one (entry88 same predicate, same params);  *)
(* (b) exit relation implies deint's postcondition shape on s2 (needs (B));   *)
(* (c) frame factors as C1 s1 s2 /\ C2 s1' s2' (maych_post is already that).   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;
(* GHASH / AES abstractions used by the entry-state predicate htable_mem_4 and
   the invariants: karatsuba_mid / byteswap128 / h_power (polyval_ghash),
   ghash_twist / nist_ghash (ghash_nist_bridge), aes128_cipher (fips197),
   karatsuba_pmul.  These match the _swp_deint correctness proof's needs; the
   aes_gcm DMTCP checkpoint happens to preload them, but a from-scratch build
   (tools/build-proof.sh) needs them explicitly, else htable_mem_4's
   new_definition fails with "term not closed: karatsuba_mid, ...". *)
needs "common/fips197.ml";;
needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;


(* ===== inlined from aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_equiv.ml ===== *)

(* ========================================================================= *)
(* Program equivalence between the de-interleaved AES-GCM kernel             *)
(*   aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_deint        *)
(* (proved functionally correct in                                           *)
(*  aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_deint.ml)     *)
(* and its SLOTHY-scheduled sibling                                          *)
(*   aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S.           *)
(*                                                                           *)
(* The two kernels are BYTE-IDENTICAL outside the steady body of the 4x      *)
(* unrolled loop [0x1ec,0x4b0): 464 instructions each, identical control     *)
(* flow at identical addresses.  The ONLY difference is the instruction      *)
(* ORDER inside that one straight-line loop body: the two bodies are the     *)
(* same 177-instruction multiset (identical encodings, zero register         *)
(* renaming) in a different, dataflow-equivalent (software-pipelined)        *)
(* schedule.  So the equivalence is lockstep everywhere except that one      *)
(* reordered block.                                                          *)
(*                                                                           *)
(* WORK IN PROGRESS.  See                                                    *)
(*   ~/.claude/.../memory/gcm-deint-swp-equivalence.md                       *)
(* for the full running record.  Approach + status summary at the bottom.    *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* The two machine-code programs.                                            *)
(* mc1 = LEFT  = _swp_deint.   mc2 = RIGHT = _swp_S.                          *)
(* ------------------------------------------------------------------------- *)

let deint_mc =
  define_from_elf "deint_mc"
    "arm/aes_gcm/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_deint.o";;

let DEINT_EXEC = ARM_MK_EXEC_RULE deint_mc;;

let swpS_mc =
  define_from_elf "swpS_mc"
    "arm/aes_gcm/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S.o";;

let SWPS_EXEC = ARM_MK_EXEC_RULE swpS_mc;;

(* ========================================================================= *)
(* APPROACH: the abbrev-left / rewrite-right reorder engine over the steady   *)
(* loop body [0x1ec,0x4b0) (177 machine instructions), driven by an inst_map  *)
(* (RIGHT-slot -> LEFT-instruction permutation).  This mirrors the master     *)
(* pipelined-loop template bignum_emontredc_8n_cdiff.ml                       *)
(* MADDLOOP_STEP1_STEP2_X30_EQUIV, which handles exactly this shape: a        *)
(* genuine reorder (its inst_map is a permutation, most instructions at       *)
(* different indices on the two sides) with loop-carried registers written    *)
(* at reordered positions.                                                    *)
(*                                                                           *)
(*   ARM_N_STEPS_AND_ABBREV_TAC  DEINT_EXEC ..            (* LEFT: abbrev *)  *)
(*   ARM_N_STEPS_AND_REWRITE_TAC SWPS_EXEC .. inst_map .. (* RIGHT: rewrite *) *)
(*                                                                           *)
(* HOW carried registers come out equal: the RIGHT rewrite looks up, per      *)
(* right-slot n, its LEFT twin inst_map[n-1] and rewrites the right output    *)
(* RHS to the SAME fresh abbreviation the left instruction produced -         *)
(* REGARDLESS of position.  So a register written at deint-instr i and        *)
(* swpS-instr j (i<>j) ends up as `read R sfinal = temp` (left) and           *)
(* `read R sfinal' = temp` (right, SAME temp); the eqout conjunct             *)
(* `?a. read R sfinal = a /\ read R sfinal' = a` then closes trivially by     *)
(* ASM_REWRITE_TAC + MESON_TAC.  This is ~10x faster than EQUIV_STEPS_TAC     *)
(* lockstep (~70s vs ~700s for the 177-instruction body) AND keeps the        *)
(* carried-register equivalences that lockstep's stutter (hard-wired          *)
(* no-discard = []) would drop for registers written in the reordered region. *)
(*                                                                           *)
(* CAVEAT (matters for the loop wrap, not this per-body lemma): a register    *)
(* written mid-RIGHT-body and NOT re-read on the right before the seam has    *)
(* its right read discarded by the per-step DISCARD_OLDSTATE (equiv.ml:1172), *)
(* so it cannot appear in eqout at the natural 0x1ec seam.  Here that only     *)
(* affects the pipeline transients X28/X23/Q15/Q10, which are dead-out at the *)
(* body boundary and correctly excluded from eqout (see out_eq_regs).  For    *)
(* the whole-loop invariant, wrap at the rotated 0x354 seam (as the _deint    *)
(* correctness proof does) where those transients are dead.                   *)
(*                                                                           *)
(* inst_map (below, 177 entries) is derived from the machine-instruction diff *)
(* of the two bodies (identical 32-register allocation, zero renaming; only 4 *)
(* aesmc encodings repeat, disambiguated by their preceding aese round key).  *)
(* The actions list (also below) is the same diff as an "equal"/"insert"/     *)
(* "delete" script; it drives the alternative EQUIV_STEPS_TAC lockstep proof  *)
(* kept commented for reference.                                             *)
(* ------------------------------------------------------------------------- *)

(* RIGHT-slot -> LEFT-instruction permutation of 1..177 for the reordered    *)
(* body.  Also saved in swp_equiv_inst_map.txt.                              *)
let inst_map = [
  1;2;3;91;92;4;5;6;93;7;8;9;10;94;95;11;12;96;13;14;15;97;98;16;17;18;99;100;
  19;20;101;102;103;21;22;23;24;25;26;104;27;28;29;30;105;106;31;32;107;108;33;
  34;35;36;109;110;37;38;39;40;111;112;113;41;42;43;114;115;116;117;118;44;45;
  46;119;47;48;49;50;51;120;121;52;53;122;54;55;56;57;123;124;58;59;125;126;60;
  127;61;62;63;128;129;64;130;131;132;133;134;135;136;65;66;137;138;139;140;67;
  68;69;70;71;72;141;142;73;74;75;143;144;76;77;145;146;78;79;147;148;80;149;150;
  81;82;83;151;152;84;153;154;155;156;157;85;158;159;160;161;162;86;163;164;165;
  87;166;167;88;168;169;89;170;171;172;173;174;175;176;90;177];;

(* Registers kept un-abbreviated through stepping (address bases + loop       *)
(* pointers/counter): their exact symbolic value must survive to prove the    *)
(* pointer/counter recurrences and to keep store addresses concrete.          *)
let regs_pin = [`X0`;`X2`;`X6`;`SP`;`X1`;`X13`];;

(* ------------------------------------------------------------------------- *)

let actions_raw = [
  ("equal", 0, 3, 0, 3); ("insert", 3, 3, 3, 5); ("equal", 3, 6, 5, 8);
  ("insert", 6, 6, 8, 9); ("equal", 6, 10, 9, 13); ("insert", 10, 10, 13, 15);
  ("equal", 10, 12, 15, 17); ("insert", 12, 12, 17, 18); ("equal", 12, 15, 18, 21);
  ("insert", 15, 15, 21, 23); ("equal", 15, 18, 23, 26); ("insert", 18, 18, 26, 28);
  ("equal", 18, 20, 28, 30); ("insert", 20, 20, 30, 33); ("equal", 20, 26, 33, 39);
  ("insert", 26, 26, 39, 40); ("equal", 26, 30, 40, 44); ("insert", 30, 30, 44, 46);
  ("equal", 30, 32, 46, 48); ("insert", 32, 32, 48, 50); ("equal", 32, 36, 50, 54);
  ("insert", 36, 36, 54, 56); ("equal", 36, 40, 56, 60); ("insert", 40, 40, 60, 63);
  ("equal", 40, 43, 63, 66); ("insert", 43, 43, 66, 71); ("equal", 43, 46, 71, 74);
  ("insert", 46, 46, 74, 75); ("equal", 46, 51, 75, 80); ("insert", 51, 51, 80, 82);
  ("equal", 51, 53, 82, 84); ("insert", 53, 53, 84, 85); ("equal", 53, 57, 85, 89);
  ("insert", 57, 57, 89, 91); ("equal", 57, 59, 91, 93); ("insert", 59, 59, 93, 95);
  ("equal", 59, 60, 95, 96); ("insert", 60, 60, 96, 97); ("equal", 60, 63, 97, 100);
  ("delete", 63, 127, 100, 100); ("equal", 127, 129, 100, 102); ("insert", 129, 129, 102, 103);
  ("equal", 129, 136, 103, 110); ("insert", 136, 136, 110, 112); ("equal", 136, 140, 112, 116);
  ("insert", 140, 140, 116, 122); ("equal", 140, 142, 122, 124); ("insert", 142, 142, 124, 127);
  ("equal", 142, 144, 127, 129); ("insert", 144, 144, 129, 131); ("equal", 144, 146, 131, 133);
  ("insert", 146, 146, 133, 135); ("equal", 146, 148, 135, 137); ("insert", 148, 148, 137, 138);
  ("equal", 148, 150, 138, 140); ("insert", 150, 150, 140, 143); ("equal", 150, 152, 143, 145);
  ("insert", 152, 152, 145, 146); ("equal", 152, 157, 146, 151); ("insert", 157, 157, 151, 152);
  ("equal", 157, 162, 152, 157); ("insert", 162, 162, 157, 158); ("equal", 162, 165, 158, 161);
  ("insert", 165, 165, 161, 162); ("equal", 165, 167, 162, 164); ("insert", 167, 167, 164, 165);
  ("equal", 167, 169, 165, 167); ("insert", 169, 169, 167, 168); ("equal", 169, 176, 168, 175);
  ("insert", 176, 176, 175, 176); ("equal", 176, 177, 176, 177)
];;

(* Split LD instructions out of "equal" segments into "replace". *)
let actions = break_equal_loads actions_raw (snd DEINT_EXEC) 0x1ec (snd SWPS_EXEC) 0x1ec;;

(* ------------------------------------------------------------------------- *)
(* eqin / eqout builders.                                                    *)
(* Concrete symbolic pointers X0=in_b, X2=out_b, X6=htab_b, SP=stackpointer  *)
(* (needed so store obligations discharge), a GENEROUS live-in register set  *)
(* (get_input_output_regs UNDER-reports - it misses AES source operands like *)
(* the round keys Q18-Q27 and the accumulators Q9/Q12/Q28 - so hand-list),   *)
(* the loaded memory regions shared-value, and the input.                    *)
(*                                                                           *)
(* IMPORTANT: register components are CONSTANTS - build with parse_term, NOT *)
(* mk_var (mk_var makes a free VARIABLE that never connects to what the      *)
(* stepper emits; symptom = "Free variables in goal" warning).              *)
(* ------------------------------------------------------------------------- *)

let mkqc n = parse_term ("Q" ^ string_of_int n ^ ":(armstate,int128)component");;
let mkxc n = parse_term ("X" ^ string_of_int n ^ ":(armstate,int64)component");;

(* live-in registers (excluding the concrete pointers X0/X2/X6/SP). *)
let in_eq_regs =
  (map mkxc [1;7;11;12;13;20;21;23;28]) @
  (map mkqc [1;5;6;7;9;10;12;15;17;18;19;20;21;22;23;24;25;26;27;28;30;31]);;

(* live-out registers.  NB: X7 is NOT live-out even though it is in both the   *)
(* body's IN and OUT sets: reduce_last (the loop-exit epilogue at 0x4b4) begins *)
(* with `ldp x17,x7,[x0]` which OVERWRITES x7 before any read, so the body's    *)
(* final x7 is dead at the loop seam.  The genuinely live-out registers are the *)
(* counter X13 and the GHASH/AES accumulators Q9,Q12,Q28 (all read by           *)
(* reduce_last's opening aese/eor before being written).                        *)
let out_eq_regs = [`X13`; `Q12`; `Q9`; `Q28`];;

let equiv_regs_inline regs (s1v,s2v) =
  let xs = filter (fun t -> type_of t = `:(armstate,int64)component`) regs in
  let qs = filter (fun t -> type_of t = `:(armstate,int128)component`) regs in
  let pair = mk_pair(s1v,s2v) in
  let mkc l ty = list_mk_icomb "mk_equiv_regs" [mk_list(l,ty); pair] in
  (if xs=[] then [] else [mkc xs `:(armstate,int64)component`]) @
  (if qs=[] then [] else [mkc qs `:(armstate,int128)component`]);;

let comp128 addr =
  mk_icomb(mk_icomb(`(:>):(armstate,(64)word->(8)word)component -> ((64)word->(8)word,int128)component -> (armstate,int128)component`, `memory`),
           mk_comb(`bytes128:int64->((64)word->(8)word,int128)component`, addr));;
let addr_of base off = if off=0 then base
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,base), mk_comb(`word:num->int64`,mk_small_numeral off));;
let mk_read r sv = list_mk_icomb "read" [r; sv];;
let concrete_ptr_conjs (s1v,s2v) =
  List.concat (map (fun (r,b) -> [mk_eq(mk_read r s1v, b); mk_eq(mk_read r s2v, b)])
    [(`X0`,`in_b:int64`);(`X2`,`out_b:int64`);(`X6`,`htab_b:int64`);(`SP`,`stackpointer:int64`)]);;
let shared128 (base,off) (s1v,s2v) =
  let r1=list_mk_icomb "read" [comp128 (addr_of base off); s1v]
  and r2=list_mk_icomb "read" [comp128 (addr_of base off); s2v] in
  mk_exists(`v:int128`, mk_conj(mk_eq(r1,`v:int128`), mk_eq(r2,`v:int128`)));;
let comp64 addr =
  mk_icomb(mk_icomb(`(:>):(armstate,(64)word->(8)word)component -> ((64)word->(8)word,int64)component -> (armstate,int64)component`, `memory`),
           mk_comb(`bytes64:int64->((64)word->(8)word,int64)component`, addr));;
let shared64 (base,off) (s1v,s2v) =
  let r1=list_mk_icomb "read" [comp64 (addr_of base off); s1v]
  and r2=list_mk_icomb "read" [comp64 (addr_of base off); s2v] in
  mk_exists(`v:int64`, mk_conj(mk_eq(r1,`v:int64`), mk_eq(r2,`v:int64`)));;
let sp_b = `stackpointer:int64` and ht_b = `htab_b:int64` and inp_b = `in_b:int64`;;
(* stack scratch + htable are read by `ldr q` (bytes128); the input block is read *)
(* by `ldp x,x` (bytes64 pairs) - the shared-memory granularity must match each   *)
(* load so its output value is picked up as the shared value.                     *)
let regions128 = [ (sp_b,160);(sp_b,176);(sp_b,192);(sp_b,208);
                   (ht_b,0);(ht_b,16);(ht_b,32);(ht_b,48);(ht_b,64);(ht_b,80) ];;
let regions64  = [ (inp_b,0);(inp_b,8);(inp_b,16);(inp_b,24);
                   (inp_b,32);(inp_b,40);(inp_b,48);(inp_b,56) ];;

let eqin = mk_gabs(`(s1:armstate,s2:armstate)`,
  list_mk_conj (concrete_ptr_conjs(`s1:armstate`,`s2:armstate`)
    @ equiv_regs_inline in_eq_regs (`s1:armstate`,`s2:armstate`)
    @ (map (fun r -> shared128 r (`s1:armstate`,`s2:armstate`)) regions128)
    @ (map (fun r -> shared64  r (`s1:armstate`,`s2:armstate`)) regions64)));;

let out_region_eq (s1v,s2v) =
  map (fun off -> mk_eq(list_mk_icomb "read" [comp128 (addr_of `out_b:int64` off); s1v],
                        list_mk_icomb "read" [comp128 (addr_of `out_b:int64` off); s2v])) [0;16;32;48];;
let eqout = mk_gabs(`(s1:armstate,s2:armstate)`,
  list_mk_conj (equiv_regs_inline out_eq_regs (`s1:armstate`,`s2:armstate`)
    @ out_region_eq(`s1:armstate`,`s2:armstate`)));;

(* Frame: MAYCHANGE over EXACTLY the set of components the body writes (the    *)
(* accumulated MAYCHANGE from stepping), plus the two written memory regions   *)
(* (stack scratch [sp+160,64) and output [out_b,64)).  This must MATCH the      *)
(* accumulated frame for MONOTONE_MAYCHANGE_CONJ_TAC to discharge it - note it  *)
(* includes X0/X2 (post-increment pointer updates) and Q0..Q6 (AES temps) that  *)
(* get_input_output_regs' OUT set omits, and uses out_b length 64 (not 65536).  *)
let maych_xregs =
  [`X0`;`X1`;`X2`;`X7`;`X8`;`X10`;`X13`;`X14`;`X17`;`X19`;`X22`;`X23`;`X24`;
   `X25`;`X26`;`X27`;`X28`;`X29`;`X30`];;
let maych_qregs = map mkqc [0;1;2;3;4;5;6;8;9;10;11;12;13;14;15;16;17;28;29;30;31];;
let maych_one =
  list_mk_icomb ",," [
    list_mk_icomb ",," [
      list_mk_icomb ",," [
        mk_icomb(`MAYCHANGE`, mk_list(maych_xregs,`:(armstate,int64)component`));
        mk_icomb(`MAYCHANGE`, mk_list(maych_qregs,`:(armstate,int128)component`))];
      `MAYCHANGE [memory :> bytes (word_add stackpointer (word 160), 64);
                  memory :> bytes (out_b:int64, 64)]`];
    `MAYCHANGE [PC] ,, MAYCHANGE [events] ,, MAYCHANGE SOME_FLAGS`];;

(* Comprehensive nonoverlapping: the KEY precondition.  The read-only input     *)
(* and htable memory must FORWARD across the body's stack/output stores, which  *)
(* requires in_b/htab_b to be disjoint from the stack and output regions (and   *)
(* code from all).  Without in_b#stack, in_b#out etc. the aggressive old-state  *)
(* discard drops the input reads at the first store and the ldp-loaded values   *)
(* vanish.                                                                      *)
let body_equiv_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`stackpointer:int64`],
  mk_imp(
    `nonoverlapping (word pc:int64, 1856) (word pc2:int64, 1856) /\
     nonoverlapping (word pc:int64, 1856) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (word pc2:int64, 1856) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (word pc:int64, 1856) (out_b:int64, 0x10000) /\
     nonoverlapping (word pc2:int64, 1856) (out_b:int64, 0x10000) /\
     nonoverlapping (in_b:int64, 64) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (in_b:int64, 64) (out_b:int64, 0x10000) /\
     nonoverlapping (htab_b:int64, 96) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (htab_b:int64, 96) (out_b:int64, 0x10000) /\
     nonoverlapping (word_add stackpointer (word 160), 64) (out_b:int64, 0x10000) /\
     aligned 16 (stackpointer:int64)`,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x1ec)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x1ec)`;
          mk_comb(eqin, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x4b0)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x4b0)`;
          mk_comb(eqout, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_one,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_one,[`s2:armstate`;`s2':armstate`]))));
       `\(s:armstate). 177`; `\(s:armstate). 177`]));;

(* AES lane-extract (mov d, v.d[1]) congruence helper for ARM_LOCKSTEP_TAC. *)
extra_word_CONV := [WORD_SIMPLE_SUBWORD_CONV] @ (!extra_word_CONV);;

(* Close a single reg-equivalence existential `?a. read R s = a /\ read R s' = a` *)
(* by witnessing with the (shared, lockstep-paired) value and discharging both   *)
(* conjuncts from assumptions.  Used instead of HINT_EXISTS_REFL_TAC / MESON,     *)
(* which choke / blow up on the ~150 scratch assumptions (some holding huge       *)
(* unabbreviated GHASH expressions).                                             *)
let CLOSE_REG_EXISTS : tactic =
  fun (asl,g) ->
    let _,body = dest_exists g in
    let c1,_ = dest_conj body in
    let lread = lhs c1 in
    let _,lth = List.find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> l = lread | _ -> false) asl in
    (EXISTS_TAC (rhs (concl lth)) THEN
     CONJ_TAC THENL [ ACCEPT_TAC lth; FIRST_ASSUM ACCEPT_TAC ]) (asl,g);;

(* ------------------------------------------------------------------------- *)
(* The steady-loop-body equivalence.  PROVED (axiom-free), ~700s.            *)
(*                                                                           *)
(* Stepping: EQUIV_STEPS_TAC over the diff-derived action list steps both    *)
(* 177-instruction bodies, lockstepping the shared ("equal") instructions    *)
(* (which pairs their register reads into shared abbreviations) and          *)
(* stuttering the reordered ("insert"/"delete") instructions.  All 86        *)
(* actions succeed once the read-only input/htable memory can forward across  *)
(* the stores (comprehensive nonoverlapping) and X7 is excluded from eqout.   *)
(* Closer: the 4 live-out register equivalences close from the paired shared  *)
(* abbreviations, the 4 output ciphertext blocks by reflexivity, and the     *)
(* frame by MONOTONE_MAYCHANGE_CONJ_TAC.                                     *)
(* ------------------------------------------------------------------------- *)

(* The fixed-pointer form (i = 0 shape) - subsumed by BODY_EQUIV_PARAM below, *)
(* which is the version the loop wrap actually needs.  Kept here (commented)  *)
(* only to avoid re-running its ~700s proof on every load; uncomment to check.*)
(*
let BODY_EQUIV = prove(body_equiv_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs; BIGNUM_FROM_MEMORY_BYTES]) THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
     if is_conj (concl th) then (CONJUNCTS_THEN ASSUME_TAC th)
     else if is_exists (concl th) then (CHOOSE_THEN ASSUME_TAC th)
     else fail())) THEN
  EQUIV_STEPS_TAC actions DEINT_EXEC SWPS_EXEC THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[mk_equiv_regs] THEN
  CONJ_TAC THENL [
    REPEAT CONJ_TAC THEN CLOSE_REG_EXISTS;
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;
*)

(* ========================================================================= *)
(* PARAMETRIC body equivalence, for iteration i of the 4x main loop.         *)
(*                                                                           *)
(* Same as BODY_EQUIV but with per-iteration pointers X0 = in_b + 64*i,      *)
(* X2 = out_b + 64*i, over disjoint full input/output buffers of            *)
(* 64*loop_count bytes with 0 <= i < loop_count.  This is the loop-body leg  *)
(* required by ENSURES2_WHILE_PAUP_TAC to wrap the whole 4x loop.            *)
(*                                                                           *)
(* KEY: the shared input-load and output-store memory addresses must be      *)
(* written in the MERGED offset form `word_add b (word (64*i + off))` (not   *)
(* the nested `word_add (word_add b (word (64*i))) (word off)`), because the *)
(* symbolic stepper normalises the effective addresses that way; otherwise   *)
(* the loaded/stored values fail to match the shared abbreviations.          *)
(* ------------------------------------------------------------------------- *)

let inbi  = `word_add in_b  (word (64 * i)):int64`;;
let outbi = `word_add out_b (word (64 * i)):int64`;;
let mrg base off =  (* base + (64*i + off) in merged form *)
  if off=0 then (if base = `in_b:int64` then inbi else outbi)
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
               mk_comb(`word:num->int64`,
                       mk_comb(mk_comb(`(+):num->num->num`,`64*i`),mk_small_numeral off)));;

let concrete_ptr_conjs_i (s1v,s2v) =
  List.concat (map (fun (r,b) -> [mk_eq(mk_read r s1v, b); mk_eq(mk_read r s2v, b)])
    [(`X0`,inbi);(`X2`,outbi);(`X6`,`htab_b:int64`);(`SP`,`stackpointer:int64`)]);;
let shared64_i off (s1v,s2v) =
  let a = mrg `in_b:int64` off in
  let r1=list_mk_icomb "read" [comp64 a; s1v] and r2=list_mk_icomb "read" [comp64 a; s2v] in
  mk_exists(`v:int64`, mk_conj(mk_eq(r1,`v:int64`), mk_eq(r2,`v:int64`)));;
let out_region_eq_i (s1v,s2v) =
  map (fun off -> let a = mrg `out_b:int64` off in
        mk_eq(list_mk_icomb "read" [comp128 a; s1v], list_mk_icomb "read" [comp128 a; s2v]))
    [0;16;32;48];;

let eqin_i = mk_gabs(`(s1:armstate,s2:armstate)`,
  list_mk_conj (concrete_ptr_conjs_i(`s1:armstate`,`s2:armstate`)
    @ equiv_regs_inline in_eq_regs (`s1:armstate`,`s2:armstate`)
    @ (map (fun r -> shared128 r (`s1:armstate`,`s2:armstate`)) regions128)
    @ (map (fun off -> shared64_i off (`s1:armstate`,`s2:armstate`)) [0;8;16;24;32;40;48;56])));;
let eqout_i = mk_gabs(`(s1:armstate,s2:armstate)`,
  list_mk_conj (equiv_regs_inline out_eq_regs (`s1:armstate`,`s2:armstate`)
    @ out_region_eq_i(`s1:armstate`,`s2:armstate`)));;

(* frame with the per-iteration output block out_b + 64*i. *)
let maych_i =
  list_mk_icomb ",," [
    list_mk_icomb ",," [
      list_mk_icomb ",," [
        mk_icomb(`MAYCHANGE`, mk_list(maych_xregs,`:(armstate,int64)component`));
        mk_icomb(`MAYCHANGE`, mk_list(maych_qregs,`:(armstate,int128)component`))];
      subst [outbi,`OUTA:int64`]
        `MAYCHANGE [memory :> bytes (word_add stackpointer (word 160), 64);
                    memory :> bytes (OUTA:int64, 64)]`];
    `MAYCHANGE [PC] ,, MAYCHANGE [events] ,, MAYCHANGE SOME_FLAGS`];;

let body_equiv_i_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`stackpointer:int64`;
   `loop_count:num`;`i:num`],
  mk_imp(
    `i < loop_count /\
     nonoverlapping (word pc:int64, 1856) (word pc2:int64, 1856) /\
     nonoverlapping (word pc:int64, 1856) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (word pc2:int64, 1856) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (word pc:int64, 1856) (out_b:int64, 64 * loop_count) /\
     nonoverlapping (word pc2:int64, 1856) (out_b:int64, 64 * loop_count) /\
     nonoverlapping (in_b:int64, 64 * loop_count) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (in_b:int64, 64 * loop_count) (out_b:int64, 64 * loop_count) /\
     nonoverlapping (htab_b:int64, 96) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (htab_b:int64, 96) (out_b:int64, 64 * loop_count) /\
     nonoverlapping (word_add stackpointer (word 160), 64) (out_b:int64, 64 * loop_count) /\
     aligned 16 (stackpointer:int64)`,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x1ec)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x1ec)`;
          mk_comb(eqin_i, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x4b0)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x4b0)`;
          mk_comb(eqout_i, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_i,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_i,[`s2:armstate`;`s2':armstate`]))));
       `\(s:armstate). 177`; `\(s:armstate). 177`]));;

(* leaf closer that also handles the parametric output-memory equalities. *)
let CLOSE_LEAF : tactic =
  fun (asl,g) ->
    if is_exists g then
      (let _,body = dest_exists g in
       let c1,_ = dest_conj body in
       let lread = lhs c1 in
       let _,lth = List.find (fun (_,th) -> match concl th with
           Comb(Comb(Const("=",_),l),_) -> l = lread | _ -> false) asl in
       (EXISTS_TAC (rhs (concl lth)) THEN
        CONJ_TAC THENL [ ACCEPT_TAC lth; FIRST_ASSUM ACCEPT_TAC ]) (asl,g))
    else
      (FIRST [ (ASM_REWRITE_TAC[] THEN REFL_TAC);
               PROVE_CONJ_OF_EQ_READS_TAC DEINT_EXEC;
               ASM_REWRITE_TAC[] ]) (asl,g);;

(* Proved via the abbrev-left / rewrite-right reorder engine (see the header  *)
(* comment).  ~77s (vs ~700s for the EQUIV_STEPS_TAC lockstep version kept     *)
(* commented below).  regs_pin keeps the pointer/counter regs un-abbreviated;  *)
(* the RIGHT rewrite unifies every other output to the left's fresh temp via   *)
(* inst_map, so the eqout register equivalences close by ASM_REWRITE+MESON and  *)
(* the output-block memory equalities by reflexivity (both sides = same temp). *)
let sta_param : (int * thm) list ref = ref [];;
let BODY_EQUIV_PARAM = prove(body_equiv_i_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs; BIGNUM_FROM_MEMORY_BYTES]) THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
     if is_conj (concl th) then (CONJUNCTS_THEN ASSUME_TAC th)
     else if is_exists (concl th) then (CHOOSE_THEN ASSUME_TAC th)
     else fail())) THEN
  ARM_N_STEPS_AND_ABBREV_TAC  DEINT_EXEC (1--177) sta_param (Some (replicate regs_pin 177)) THEN
  ARM_N_STEPS_AND_REWRITE_TAC SWPS_EXEC  (1--177) inst_map sta_param (Some (replicate regs_pin 177)) THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

(* Alternative (slower) EQUIV_STEPS_TAC lockstep proof of the same lemma, kept *)
(* for reference.  ~700s.  Closes via CLOSE_LEAF (per-leaf existential witness *)
(* + PROVE_CONJ_OF_EQ_READS for memory).                                       *)
(*
let BODY_EQUIV_PARAM = prove(body_equiv_i_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs; BIGNUM_FROM_MEMORY_BYTES]) THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
     if is_conj (concl th) then (CONJUNCTS_THEN ASSUME_TAC th)
     else if is_exists (concl th) then (CHOOSE_THEN ASSUME_TAC th)
     else fail())) THEN
  EQUIV_STEPS_TAC actions DEINT_EXEC SWPS_EXEC THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[mk_equiv_regs] THEN
  CONJ_TAC THENL [
    REPEAT CONJ_TAC THEN CLOSE_LEAF;
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;
*)

(* ========================================================================= *)
(* WHOLE 4x-LOOP EQUIVALENCE (work in progress).                             *)
(*                                                                           *)
(* The relational loop invariant at the natural head 0x1ec, iteration i:     *)
(* per-iteration pointers X0 = in_b + 64*i / X2 = out_b + 64*i, the          *)
(* loop-carried registers equal (round keys, accumulators, counter),         *)
(* the stack scratch / htable shared, the WHOLE input buffer shared, and     *)
(* the ACCUMULATING output ("blocks 0..4*i written so far are equal").       *)
(*                                                                           *)
(* VALIDATED: ENSURES2_WHILE_PAUP_TAC applies at head 0x1ec / backedge 0x4b0 *)
(* with a=0, b=loop_count-1 and decomposes into the 7 standard legs.  The    *)
(* one non-obvious requirement: the frame's flags must be written out as     *)
(* MAYCHANGE [NF;ZF;CF;VF] (NOT MAYCHANGE SOME_FLAGS), so the tactic's        *)
(* internal C,,C=C idempotence check (MAYCHANGE_IDEMPOT_TAC) succeeds.       *)
(*                                                                           *)
(* Remaining: the body leg [2] needs BODY_EQUIV_PARAM re-cast with its       *)
(* postcondition strengthened to loopinv(i+1) (carried regs + accumulating   *)
(* output + concrete X1 + flag); the backedge [3] and post [4] legs are      *)
(* single-step lockstep; legs [0],[5],[6] are arithmetic.                    *)
(* ------------------------------------------------------------------------- *)

(*
let loopinv = `\i s1 s2.
    read X0 s1 = word_add in_b (word (64 * i)) /\ read X0 s2 = word_add in_b (word (64 * i)) /\
    read X2 s1 = word_add out_b (word (64 * i)) /\ read X2 s2 = word_add out_b (word (64 * i)) /\
    read X6 s1 = htab_b /\ read X6 s2 = htab_b /\
    read SP s1 = stackpointer /\ read SP s2 = stackpointer /\
    mk_equiv_regs [X1; X7; X11; X12; X13; X20; X21; X23; X28] (s1,s2) /\
    mk_equiv_regs [Q1;Q5;Q6;Q7;Q9;Q10;Q12;Q15;Q17;Q18;Q19;Q20;Q21;Q22;Q23;
                   Q24;Q25;Q26;Q27;Q28;Q30;Q31] (s1,s2) /\
    (?v. read (memory :> bytes128 (word_add stackpointer (word 160))) s1 = v /\ ...) /\  (* stack x4 *)
    (?v. read (memory :> bytes128 htab_b) s1 = v /\ ...) /\ ...                            (* htable x6 *)
    (!j. j < 8 * loop_count ==>                                                            (* whole input *)
         ?v. read (memory :> bytes64 (word_add in_b (word (8*j)))) s1 = v /\
             read (memory :> bytes64 (word_add in_b (word (8*j)))) s2 = v) /\
    (!j. j < 4 * i ==>                                                                     (* accum output *)
         read (memory :> bytes128 (word_add out_b (word (16*j)))) s1 =
         read (memory :> bytes128 (word_add out_b (word (16*j)))) s2)` in
let flagpred = `\i s. read X1 s = word (loop_count - 1 - i)` in
... ENSURES2_WHILE_PAUP_TAC `0` `loop_count-1`
      `pc+0x1ec` `pc+0x4b0` `pc2+0x1ec` `pc2+0x4b0`
      loopinv flagpred flagpred (\i. 177) (\i. 177) 0 0 1 1 1 1 ...
   (frame must use MAYCHANGE [NF;ZF;CF;VF], not SOME_FLAGS)
*)

(* ========================================================================= *)
(* BODY_LEG_FULL: the per-iteration body equivalence with the FULL loop-      *)
(* carried invariant (all registers live across the loop head 0x1ec), i.e.    *)
(* the loop-body leg that ENSURES2_WHILE_PAUP_TAC needs (loopinv i -> the same *)
(* carried relation at i+1's shape).  Unlike BODY_EQUIV_PARAM (whose eqout was *)
(* just the minimal live-out {X13;Q12;Q9;Q28}+4 blocks), this carries the      *)
(* whole set: round keys Q18-27, X20/21, Q7, counter X11/12/13, GHASH          *)
(* accumulators Q9/Q12/Q28/Q30, AND the pipeline transients X22/X23/X28/X29/   *)
(* Q10/Q11/Q15 that the body reads before overwriting.                        *)
(*                                                                           *)
(* THREE ingredients make every carried register identify across the two      *)
(* (permuted) programs:                                                       *)
(*                                                                           *)
(* 1. `i + 2 <= loop_count`.  The A-block PREFETCHES the NEXT group's input    *)
(*    (ldp ...,[x0],#64 then [x0,#16/32/48] reads in_b+64*i+{80..120} = block   *)
(*    i+1).  Without the bound the nonoverlapping driver cannot prove those    *)
(*    prefetch addresses in-bounds vs the stack stores, so the shared-input    *)
(*    facts for block i+1 get discarded before the loads.  With it, block-i+1  *)
(*    input shares survive.  (Mirrors the _deint correctness proof's           *)
(*    loop_count-2 bound + FILL/DRAIN; the last iteration's prefetch is         *)
(*    handled in the drain leg, not here.)                                     *)
(*                                                                           *)
(* 2. Input shares in BOTH the merged form `word_add in_b (word (64*i+off))`   *)
(*    AND the nested form `word_add (word_add in_b (word (64*i))) (word off)`.  *)
(*    The symbolic stepper does NOT canonicalise the post-increment            *)
(*    `ldp ...,[x0],#64` effective addresses consistently (some come out       *)
(*    merged, some nested), so a load matches whichever form it produced       *)
(*    (identically on both programs, being the same instruction).  Providing   *)
(*    both forms lets every input load forward to the shared value.            *)
(*                                                                           *)
(* 3. Stack-scratch keystream: the read-first slots (sp+160/176, loop-carried) *)
(*    are shared bytes128 in regions128; the write-first slots (sp+192/208)    *)
(*    are store-forwarded within each side via read-over-write (SP stays       *)
(*    concrete because it is in regs_pin).  The vector reloads (Q10/Q15) then   *)
(*    identify once their scalar sources do.                                   *)
(*                                                                           *)
(* Only the address-base + loop-counter registers are kept un-abbreviated      *)
(* (regs_pin); everything else abbreviates and unifies via inst_map, and the   *)
(* loads identify via the shared-memory forwarding above.  Proved axiom-free.  *)
(* ------------------------------------------------------------------------- *)

(* No-drop variant of ARM_N_STEPS_AND_REWRITE_TAC: on a right-instruction      *)
(* output whose RHS matches no left abbreviation (the None case), KEEP the     *)
(* equation as-is instead of dropping it, so reordered-written reads survive.  *)
let ARM_N_STEPS_AND_REWRITE_KEEP_TAC execth (snums:int list) (inst_map: int list)
      (abbrevs: (int * thm) list ref)
      (regs_to_avoid_abbrev: (term list) list option): tactic =
  let abbrevs_cpy:(int * thm) list ref = ref [] in
  let regs_to_avoid_abbrev =
    match regs_to_avoid_abbrev with Some l -> l | None -> replicate [] (length snums) in
  if length regs_to_avoid_abbrev <> length snums
  then failwith "regs_to_avoid_abbrev: length mismatch" else
  (fun (asl,g) ->
    abbrevs_cpy := !abbrevs;
    let cur_stname = name_of (rand g) in
    STASH_ASMS_OF_READ_STATES [cur_stname] (asl,g)) THEN
  MAP_EVERY
    (fun n,regs_to_avoid_abbrev ->
      let stname = "s" ^ (string_of_int n) ^ "'" in
      let new_state_eq = ref ([],[]) in
      let inst_term = ref `T` in
      MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
      ARM_N_STEP_TAC execth [] stname (Some new_state_eq) (Some inst_term) THEN
      DISCARD_OLDSTATE_AGGRESSIVELY_TAC [stname] false THEN
      MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
      (fun (asl,g) ->
        let n_at_lprog = List.nth inst_map (n-1) in
        let abbrevs_for_st_n, leftover = List.partition (fun (n',t)->n'=n_at_lprog) !abbrevs_cpy in
        let _ = abbrevs_cpy := leftover in
        let new_state_eqs, new_aux_mem_eqs = !new_state_eq in
        let new_state_eqs_norewrite,new_state_eqs =
          List.partition
            (fun th -> not (is_eq (concl th)) || (is_read_pc (lhs (concl th))) || (is_read_events (lhs (concl th))))
          new_state_eqs in
        let new_state_eqs_noabbrev, new_state_eqs =
          if is_store_inst !inst_term then new_state_eqs,[]
          else partition
            (fun th -> let updating_comp = hd (snd (strip_comb (lhs (concl th)))) in
              mem updating_comp regs_to_avoid_abbrev) new_state_eqs in
        let new_state_eqs = map
            (fun new_state_eq ->
              let r = rhs (concl new_state_eq) in
              match List.find_opt (fun (_,th') -> lhs (concl th') = r) abbrevs_for_st_n with
              | Some (_,rhs_to_abbrev) -> GEN_REWRITE_RULE RAND_CONV [rhs_to_abbrev] new_state_eq
              | None -> new_state_eq)
            new_state_eqs in
        MAP_EVERY ASSUME_TAC (new_aux_mem_eqs @ new_state_eqs_norewrite @
                              new_state_eqs_noabbrev @ new_state_eqs) (asl,g))
      THEN CLARIFY_TAC)
    (zip snums regs_to_avoid_abbrev) THEN
  RECOVER_ASMS_OF_READ_STATES THEN CLARIFY_TAC;;

(* Fast per-leaf closer for `?a. read R sL = a /\ read R sR' = a`: find the two *)
(* recorded reads, witness with the left value; accept both if equal, else     *)
(* discharge the right via WORD_RULE.  Avoids the MESON blow-up on the ~150     *)
(* scratch assumptions that HINT_EXISTS_REFL/MESON hit.                         *)
let CHEAP_LEAF : tactic =
  fun (asl,g) ->
    let _,body = dest_exists g in
    let c1,c2 = dest_conj body in
    let l1 = lhs c1 and l2 = lhs c2 in
    let find l =
      try Some(snd(List.find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),lhs'),_) -> lhs' = l | _ -> false) asl))
      with Not_found -> None in
    (match find l1, find l2 with
     | Some th1, Some th2 ->
         let r1 = rhs(concl th1) and r2 = rhs(concl th2) in
         if r1 = r2
         then (EXISTS_TAC r1 THEN CONJ_TAC THENL [ACCEPT_TAC th1; ACCEPT_TAC th2]) (asl,g)
         else (EXISTS_TAC r1 THEN CONJ_TAC THENL
                 [ACCEPT_TAC th1; ONCE_REWRITE_TAC[th2] THEN CONV_TAC WORD_RULE]) (asl,g)
     | _ -> failwith "CHEAP_LEAF: missing read") ;;

(* Full loop-carried register set (live across the 0x1ec loop head).           *)
let carried_full =
  (map mkxc [11;12;13;20;21;22;23;27;28;29;30;3;4;15;16]) @
  (map mkqc [1;5;6;7;9;10;11;12;15;17;18;19;20;21;22;23;24;25;26;27;28;30;31]);;

(* Input shared value in the NESTED effective-address form. *)
let shared64_nested off (s1v,s2v) =
  let a = mk_comb(mk_comb(`word_add:int64->int64->int64`, inbi),
             mk_comb(`word:num->int64`,mk_small_numeral off)) in
  let r1=list_mk_icomb "read" [comp64 a; s1v] and r2=list_mk_icomb "read" [comp64 a; s2v] in
  mk_exists(`v:int64`, mk_conj(mk_eq(r1,`v:int64`), mk_eq(r2,`v:int64`)));;

(* Two input blocks (this iter + prefetched next), offsets 0..120 by 8. *)
let body_input_offs = [0;8;16;24;32;40;48;56;64;72;80;88;96;104;112;120];;

let eqin_full = mk_gabs(`(s1:armstate,s2:armstate)`,
  list_mk_conj (concrete_ptr_conjs_i(`s1:armstate`,`s2:armstate`)
    @ equiv_regs_inline carried_full (`s1:armstate`,`s2:armstate`)
    @ (map (fun r -> shared128 r (`s1:armstate`,`s2:armstate`)) regions128)
    @ (map (fun off -> shared64_i off (`s1:armstate`,`s2:armstate`)) body_input_offs)
    @ (map (fun off -> shared64_nested off (`s1:armstate`,`s2:armstate`)) body_input_offs)));;
let eqout_full = mk_gabs(`(s1:armstate,s2:armstate)`,
  list_mk_conj (equiv_regs_inline carried_full (`s1:armstate`,`s2:armstate`)
    @ out_region_eq_i(`s1:armstate`,`s2:armstate`)));;

let body_leg_full_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`stackpointer:int64`;
   `loop_count:num`;`i:num`],
  mk_imp(
    `i + 2 <= loop_count /\
     nonoverlapping (word pc:int64, 1856) (word pc2:int64, 1856) /\
     nonoverlapping (word pc:int64, 1856) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (word pc2:int64, 1856) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (word pc:int64, 1856) (out_b:int64, 64 * loop_count) /\
     nonoverlapping (word pc2:int64, 1856) (out_b:int64, 64 * loop_count) /\
     nonoverlapping (in_b:int64, 64 * loop_count) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (in_b:int64, 64 * loop_count) (out_b:int64, 64 * loop_count) /\
     nonoverlapping (htab_b:int64, 96) (word_add stackpointer (word 160), 64) /\
     nonoverlapping (htab_b:int64, 96) (out_b:int64, 64 * loop_count) /\
     nonoverlapping (word_add stackpointer (word 160), 64) (out_b:int64, 64 * loop_count) /\
     aligned 16 (stackpointer:int64)`,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x1ec)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x1ec)`;
          mk_comb(eqin_full, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x4b0)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x4b0)`;
          mk_comb(eqout_full, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_i,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_i,[`s2:armstate`;`s2':armstate`]))));
       `\(s:armstate). 177`; `\(s:armstate). 177`]));;

let sta_body_full : (int * thm) list ref = ref [];;
let BODY_LEG_FULL = prove(body_leg_full_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs; BIGNUM_FROM_MEMORY_BYTES]) THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
     if is_conj (concl th) then (CONJUNCTS_THEN ASSUME_TAC th)
     else if is_exists (concl th) then (CHOOSE_THEN ASSUME_TAC th)
     else fail())) THEN
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--177) sta_body_full (Some (replicate regs_pin 177)) THEN
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--177) inst_map sta_body_full (Some (replicate regs_pin 177)) THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN TRY CHEAP_LEAF;
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;
Printf.printf "*** BODY_LEG_FULL PROVED ***\n";;



(* ===== inlined from swp_equiv_leg2.ml ===== *)

(* ========================================================================= *)
(* LEG [2] of the _swp_deint <-> _swp_S 4x-loop equivalence:                 *)
(*   the per-iteration body leg  loopinv i  -->  loopinv (i+1)               *)
(* required by ENSURES2_WHILE_PAUP_TAC to wrap the whole steady loop.        *)
(*                                                                           *)
(* This file loads the committed base equivalence proof (which defines       *)
(* deint_mc / swpS_mc / DEINT_EXEC / SWPS_EXEC / inst_map / regs_pin /        *)
(* the eqin builders / ARM_N_STEPS_AND_REWRITE_KEEP_TAC / CHEAP_LEAF /        *)
(* carried_full / BODY_LEG_FULL), then proves the fully inductive body leg    *)
(* whose invariant carries the WHOLE input buffer (i-independent) and the     *)
(* accumulating output.                                                       *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* The relational loop invariant loopinv i, built parametrically in the       *)
(* iteration counter e so that both loopinv i (eqin) and loopinv (i+1)         *)
(* (eqout) are one substitution apart.                                        *)
(*                                                                           *)
(*   - per-iteration pointers X0 = in_b + 64 i, X2 = out_b + 64 i             *)
(*   - the concrete htable/stack pointers X6 = htab_b, SP = stackpointer      *)
(*   - the loop counter X1 = loop_count - 1 - i                              *)
(*   - the FULL loop-carried register set carried_full (round keys, GHASH     *)
(*     accumulators, pipeline transients) equal on both states               *)
(*   - the stack scratch + htable regions shared (shared128 over regions128)  *)
(*   - the WHOLE input buffer shared as a single bignum_from_memory value     *)
(*     (i-INDEPENDENT: forwards across the body by a pure frame argument, and *)
(*     digitizes into the per-block input loads before stepping)             *)
(*   - the ACCUMULATING output: blocks 0..4 i written so far are equal.       *)
(* ------------------------------------------------------------------------- *)

let ptrs_at e (s1v,s2v) =
  let w64 = mk_comb(`word:num->int64`, mk_binop `( * ):num->num->num` `64` e) in
  let lc1e = mk_binop `(-):num->num->num` (mk_binop `(-):num->num->num` `loop_count:num` `1`) e in
  [ mk_eq(mk_read `X0` s1v, mk_binop `word_add:int64->int64->int64` `in_b:int64` w64);
    mk_eq(mk_read `X0` s2v, mk_binop `word_add:int64->int64->int64` `in_b:int64` w64);
    mk_eq(mk_read `X2` s1v, mk_binop `word_add:int64->int64->int64` `out_b:int64` w64);
    mk_eq(mk_read `X2` s2v, mk_binop `word_add:int64->int64->int64` `out_b:int64` w64);
    mk_eq(mk_read `X6` s1v, `htab_b:int64`);
    mk_eq(mk_read `X6` s2v, `htab_b:int64`);
    mk_eq(mk_read `SP` s1v, `stackpointer:int64`);
    mk_eq(mk_read `SP` s2v, `stackpointer:int64`);
    mk_eq(mk_read `X1` s1v, mk_comb(`word:num->int64`, lc1e));
    mk_eq(mk_read `X1` s2v, mk_comb(`word:num->int64`, lc1e)) ];;

let bfm_at (s1v,s2v) =
  let r1 = mk_comb(mk_comb(`bignum_from_memory`, `(in_b:int64, 8 * loop_count)`), s1v) in
  let r2 = mk_comb(mk_comb(`bignum_from_memory`, `(in_b:int64, 8 * loop_count)`), s2v) in
  mk_exists(`a:num`, mk_conj(mk_eq(r1,`a:num`), mk_eq(r2,`a:num`)));;

let accum_at e (s1v,s2v) =
  let ad = mk_binop `word_add:int64->int64->int64` `out_b:int64` (mk_comb(`word:num->int64`,`16 * j`)) in
  let a1 = list_mk_icomb "read" [comp128 ad; s1v] and a2 = list_mk_icomb "read" [comp128 ad; s2v] in
  mk_forall(`j:num`, mk_imp(mk_binop `(<):num->num->bool` `j:num` (mk_binop `( * ):num->num->num` `4` e), mk_eq(a1,a2)));;

let loopinv_conj e (s1v,s2v) =
  list_mk_conj (
      ptrs_at e (s1v,s2v)
    @ equiv_regs_inline carried_full (s1v,s2v)
    @ (map (fun r -> shared128 r (s1v,s2v)) regions128)
    @ [ bfm_at (s1v,s2v); accum_at e (s1v,s2v) ]);;

let eqin_L  = mk_gabs(`(s1:armstate,s2:armstate)`, loopinv_conj `i:num` (`s1:armstate`,`s2:armstate`));;
let eqout_L = mk_gabs(`(s1:armstate,s2:armstate)`, loopinv_conj `i + 1` (`s1:armstate`,`s2:armstate`));;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas.                                                            *)
(* ------------------------------------------------------------------------- *)

(* read-over-write for orthogonal components. *)
let ROW_ORTH = prove
 (`orthogonal_components c d ==> read c (write d y s) = read c s`,
  SIMP_TAC[orthogonal_components]);;

(* Two distinct 16-byte output blocks (index j < 4 i) and (index i's 64-byte  *)
(* group) do not overlap, given the buffer fits in the address space.         *)
let ACCUM_NOVL = prove
 (`!(out_b:int64) i j. j < 4 * i /\ 64 * i + 64 < 2 EXP 64 ==>
     nonoverlapping (word_add out_b (word (16*j)):int64, 16)
                    (word_add out_b (word (64*i)), 64)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 * j + 16 <= 64 * i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  NONOVERLAPPING_TAC);;

(* ------------------------------------------------------------------------- *)
(* From a whole-buffer  bignum_from_memory (in_b, 8*loop_count) s = a  fact    *)
(* and the precondition i + 2 <= loop_count, synthesise the shared per-block  *)
(* input word  read (mem :> bytes64 (in_b + 64 i + 8 m)) s = word(bigdigit a  *)
(* (8 i + m))  for m = 0..15 (this iteration's block i and the prefetched     *)
(* block i+1), in BOTH the merged and the nested effective-address forms that *)
(* the symbolic stepper produces.                                            *)
(* ------------------------------------------------------------------------- *)

let derive_slot_read bfm_th k_tm precond_th =
  let lhs_bfm, _ = dest_eq (concl bfm_th) in
  let bfm_app, s_tm = dest_comb lhs_bfm in
  let _, pair = dest_comb bfm_app in
  let base, size = dest_pair pair in
  let inst = ISPECL [size; base; s_tm; k_tm] BIGDIGIT_BIGNUM_FROM_MEMORY in
  let sidecond = mk_binop `(<):num->num->bool` k_tm size in
  let side_imp = prove(mk_imp(concl precond_th, sidecond), DISCH_TAC THEN ASM_ARITH_TAC) in
  let side_th = MP side_imp precond_th in
  let inst3 = REWRITE_RULE [bfm_th; side_th] inst in
  let read_tm = rand (rhs (concl inst3)) in
  let read_eq_wval = SYM (ISPEC read_tm WORD_VAL) in
  let wbd_eq_wval = AP_TERM `word:num->int64` inst3 in
  TRANS read_eq_wval (SYM wbd_eq_wval);;

let norm_addr th =
  let c = concl th in
  let lhs_read = lhs c in
  let word_exprs = find_terms (fun t -> match t with
     Comb(Const("word",_), e) when not (is_numeral e) && (is_binary "*" e || is_binary "+" e) -> true |_->false) lhs_read in
  match word_exprs with
  | wexpr::_ ->
      let e = rand wexpr in
      let simp = rhs (concl (NUM_NORMALIZE_CONV e)) in
      let eqn = ARITH_RULE (mk_eq(e, simp)) in
      GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [eqn] th
  | [] -> th;;

let to_nested_addr th =
  let c = concl th in
  let addr = find_term (fun t -> match t with
     Comb(Comb(Const("word_add",_),Var("in_b",_)), Comb(Const("word",_),_)) -> true |_->false) (lhs c) in
  let inner = rand addr in
  let e = rand inner in
  if is_binary "+" e then
    let hd,off = dest_binary "+" e in
    let nested = mk_binop `word_add:int64->int64->int64`
        (mk_binop `word_add:int64->int64->int64` `in_b:int64` (mk_comb(`word:num->int64`,hd)))
        (mk_comb(`word:num->int64`,off)) in
    let eqn = WORD_RULE (mk_eq(addr, nested)) in
    GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [eqn] th
  else th;;

let DERIVE_INPUT_SLOTS_TAC : tactic =
  fun (asl,w) ->
    let precond_th = try snd(find (fun (_,th) -> concl th = `i + 2 <= loop_count`) asl)
                     with Not_found -> failwith "no precond i+2<=loop_count" in
    let bfm_ths = filter (fun (_,th) -> match concl th with
       | Comb(Comb(Const("=",_), Comb(Comb(Const("bignum_from_memory",_),_),_)),_) -> true |_->false) asl in
    let derived = List.concat (map (fun (_,bfm_th) ->
        List.concat (map (fun m ->
            let k = if m=0 then `8 * i` else mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral m) in
            let base = norm_addr (derive_slot_read bfm_th k precond_th) in
            let nested = to_nested_addr base in
            if concl base = concl nested then [base] else [base; nested])
          (0--15))) bfm_ths) in
    MAP_EVERY ASSUME_TAC derived (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Closer helpers.                                                           *)
(* ------------------------------------------------------------------------- *)

(* the loop counter arithmetic  word_sub (word (lc-1-i)) 1 = word (lc-1-(i+1)). *)
let SOLVE_COUNTER_TAC =
  SUBGOAL_THEN `loop_count - 1 - i = (loop_count - 1 - (i+1)) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; CONV_TAC WORD_RULE];;

(* the accumulating-output forall at i+1:  split off the 4 freshly-written    *)
(* blocks, keep the old accumulation.                                        *)
let ACCUM_SPLIT_TAC =
  REWRITE_TAC[ARITH_RULE
    `j < 4 * (i + 1) <=> j < 4 * i \/ j = 4*i \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
  REWRITE_TAC[TAUT `(p \/ q) ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM];;

(* close a trivial existential  ?v. E = v  (E already fully evaluated). *)
let TRIV_EXISTS_TAC : tactic = fun (asl,w) ->
  let _,body = dest_exists w in let l,_ = dest_eq body in
  (EXISTS_TAC l THEN REFL_TAC) (asl,w);;

(* close a cross-state stack-scratch pair  ?v. read C s177 = v /\ read C s177' = v *)
(* by showing the two 128-bit reads equal via their two 64-bit halves.          *)
let STACK_PAIR_TAC : tactic = fun (asl,w) ->
  let _,body = dest_exists w in
  let c1,_ = dest_conj body in
  let readC = lhs c1 in
  let comp = rator readC in
  (SUBGOAL_THEN (mk_eq(readC, mk_comb(comp, `s177':armstate`)))
     (fun th -> MESON_TAC[th]) THEN
   REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV
     [WORD_RULE `word_add (word_add x (word a)) (word b):int64 = word_add x (word (a+b))`] THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]) (asl,w);;

(* the four freshly-written output blocks (j = 4 i .. 4 i + 3). *)
let ACCUM_NEWBLOCK_TAC =
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * i + b) = 64 * i + 16 * b`;
              ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[];;

(* the whole omnibus for the relational post-condition.  The accumulating     *)
(* output forall at i+1 is split into the old accumulation (discharged by the  *)
(* forwarded snapshot) and the four freshly-written blocks.                    *)
let LEG2_POST_TAC =
  REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN
  TRY (ACCUM_SPLIT_TAC THEN REPEAT CONJ_TAC) THEN
  TRY CHEAP_LEAF THEN                    (* loop-carried registers *)
  TRY (CONV_TAC WORD_RULE) THEN          (* pointers X0/X2 at i+1 *)
  TRY SOLVE_COUNTER_TAC THEN             (* down-counter X1 *)
  TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THEN(* the forwarded old accumulation *)
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN  (* forwarded whole-buffer input equality *)
  TRY STACK_PAIR_TAC THEN                (* stack scratch, as a 128-bit pair *)
  TRY TRIV_EXISTS_TAC THEN               (* already-evaluated stack/htable existentials *)
  TRY ACCUM_NEWBLOCK_TAC;;               (* the 4 freshly-written output blocks *)

Printf.printf "*** swp_equiv_leg2 preamble loaded ***\n";;

(* read-over-write across a whole MAYCHANGE frame `frame_th : CHAIN sfrom sto`,     *)
(* forwarding `read C sfrom = rhs` to `read C sto = rhs`, using nonoverlapping       *)
(* drivers from the ambient assumptions `asl_thms` plus any `extra_novl`.            *)
let FRAME_FORWARD_READ (asl_thms:thm list) (read_th:thm) (frame_th:thm) (extra_novl:thm list) : thm =
  let readtm = lhs (concl read_th) in
  let readcomp = rator readtm in
  let sto = rand (concl frame_th) in
  let a_tm = rhs (concl read_th) in
  let goal = mk_eq(mk_comb(readcomp, sto), a_tm) in
  let drivers = NONOVERLAPPING_DRIVERS (asl_thms @ extra_novl) in
  let ariths = FILTER_CANONIZE_ASSUMPTIONS (asl_thms @ extra_novl) in
  TAC_PROOF(
    (map (fun t -> ("",t)) (asl_thms @ extra_novl @ [read_th; frame_th]), goal),
    MP_TAC frame_th THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    CONV_TAC(LAND_CONV(COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV (drivers,ariths))) THEN
    ACCEPT_TAC read_th);;

(* ------------------------------------------------------------------------- *)
(* Whole-frame forwarding of the loop-carried MEMORY clauses (input buffer     *)
(* and accumulating output) across the reordered body, wired as inline tactic  *)
(* steps.  These run AFTER both symbolic-execution passes, when the two         *)
(* accumulated frames `CHAIN s0 s177` (left) and `CHAIN s0' s177'` (right) are  *)
(* both present in the assumptions, and the pre-stepping snapshots of the       *)
(* whole-buffer bignum and the accumulating output have been captured.          *)
(* ------------------------------------------------------------------------- *)

(* find the accumulated frame theorem ending at state named `sto_name`. *)
let find_body_frame asl sto_name =
  snd(find (fun (_,th) -> match concl th with
     Comb(Comb(_,sa),sb) when is_var sa && is_var sb && name_of sb=sto_name
       && (let n=name_of sa in n="s0" || n="s0'") -> true|_->false) asl);;

(* ------------------------------------------------------------------------- *)
(* THE BODY LEG.  loopinv i --> loopinv (i+1).                               *)
(* ------------------------------------------------------------------------- *)

let leg2_precond_L =
  `i + 2 <= loop_count /\
   64 * loop_count < 2 EXP 64 /\
   nonoverlapping (word pc:int64, 1856) (word pc2:int64, 1856) /\
   nonoverlapping (word pc:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc2:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc:int64, 1856) (out_b:int64, 64 * loop_count) /\
   nonoverlapping (word pc2:int64, 1856) (out_b:int64, 64 * loop_count) /\
   nonoverlapping (in_b:int64, 64 * loop_count) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (in_b:int64, 64 * loop_count) (out_b:int64, 64 * loop_count) /\
   nonoverlapping (htab_b:int64, 96) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (htab_b:int64, 96) (out_b:int64, 64 * loop_count) /\
   nonoverlapping (word_add stackpointer (word 160), 64) (out_b:int64, 64 * loop_count) /\
   aligned 16 (stackpointer:int64)`;;

let leg2_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`stackpointer:int64`;
   `loop_count:num`;`i:num`],
  mk_imp(leg2_precond_L,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x1ec)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x1ec)`;
          mk_comb(eqin_L, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x4b0)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x4b0)`;
          mk_comb(eqout_L, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_i,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_i,[`s2:armstate`;`s2':armstate`]))));
       `\(s:armstate). 177`; `\(s:armstate). 177`]));;

let sta_leg2 : (int * thm) list ref = ref [];;
let saved_bfm_leg2 : thm list ref = ref [];;
let saved_accum_leg2 : thm ref = ref TRUTH;;

let BODY_LEG2 = prove(leg2_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
     if is_conj (concl th) then (CONJUNCTS_THEN ASSUME_TAC th)
     else if is_exists (concl th) then (CHOOSE_THEN ASSUME_TAC th)
     else fail())) THEN
  (* snapshot the whole-buffer bignum and the accumulating-output invariant *)
  W(fun (asl,_) ->
     saved_bfm_leg2 := map snd (filter (fun (_,th) -> match concl th with
        | Comb(Comb(Const("=",_), Comb(Comb(Const("bignum_from_memory",_),_),_)),_) -> true |_->false) asl);
     saved_accum_leg2 := (try snd(find (fun (_,th) ->
        is_forall (concl th) && can (find_term (fun t->t=`out_b:int64`)) (concl th)) asl)
       with Not_found -> TRUTH);
     ALL_TAC) THEN
  (* digitize the per-block input loads (this block i and the prefetched i+1) *)
  DERIVE_INPUT_SLOTS_TAC THEN
  (* left program: abbreviate the reordered outputs *)
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--177) sta_leg2 (Some (replicate regs_pin 177)) THEN
  (* the raw bignum / accum forall reference the stashed left state; drop them before   *)
  (* the right pass (they are re-established by frame forwarding in the closer).         *)
  DISCARD_ASSUMPTIONS_TAC (fun th ->
     can (find_term (fun t->match t with Comb(Const("bignum_from_memory",_),_)->true|_->false)) (concl th)
     || (is_forall (concl th) && can (find_term (fun t->t=`out_b:int64`)) (concl th))) THEN
  (* right program: rewrite its reordered outputs onto the same abbreviations *)
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--177) inst_map sta_leg2 (Some (replicate regs_pin 177)) THEN
  (* re-establish the whole-buffer input and the accumulating output at the loop-back    *)
  (* states s177 / s177' by forwarding the pre-stepping snapshots across the two frames.  *)
  W(fun (asl,_) ->
     let asl_thms = map snd asl in
     let frame_L = find_body_frame asl "s177" and frame_R = find_body_frame asl "s177'" in
     let bfm_s0  = find (fun th -> can (find_term (fun t->t=`s0:armstate`)) (concl th)) !saved_bfm_leg2 in
     let bfm_s0' = find (fun th -> can (find_term (fun t->t=`s0':armstate`)) (concl th)) !saved_bfm_leg2 in
     let bL = REWRITE_RULE[GSYM BIGNUM_FROM_MEMORY_BYTES]
                (FRAME_FORWARD_READ asl_thms (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES] bfm_s0) frame_L []) in
     let bR = REWRITE_RULE[GSYM BIGNUM_FROM_MEMORY_BYTES]
                (FRAME_FORWARD_READ asl_thms (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES] bfm_s0') frame_R []) in
     let accum_goal = `!j. j < 4 * i ==>
         read (memory :> bytes128 (word_add out_b (word (16*j)))) s177 =
         read (memory :> bytes128 (word_add out_b (word (16*j)))) s177'` in
     let accfwd = TAC_PROOF(
       (map (fun t->("",t)) (asl_thms @ [!saved_accum_leg2; frame_L; frame_R]), accum_goal),
       GEN_TAC THEN DISCH_TAC THEN
       SUBGOAL_THEN `16 * j + 16 <= 64 * i /\ 16 * j + 16 <= 64 * loop_count` STRIP_ASSUME_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN
         `nonoverlapping (word_add out_b (word (16*j)):int64,16) (word_add out_b (word (64*i)),16) /\
          nonoverlapping (word_add out_b (word (16*j)):int64,16) (word_add out_b (word (64*i+16)),16) /\
          nonoverlapping (word_add out_b (word (16*j)):int64,16) (word_add out_b (word (64*i+32)),16) /\
          nonoverlapping (word_add out_b (word (16*j)):int64,16) (word_add out_b (word (64*i+48)),16)`
         STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
       SUBGOAL_THEN `read (memory :> bytes128 (word_add out_b (word (16*j)))) s177 =
                     read (memory :> bytes128 (word_add out_b (word (16*j)))) s0` SUBST1_TAC THENL
        [MP_TAC frame_L THEN
         REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
         CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
         REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN READ_OVER_WRITE_ORTHOGONAL_TAC;
         ALL_TAC] THEN
       SUBGOAL_THEN `read (memory :> bytes128 (word_add out_b (word (16*j)))) s177' =
                     read (memory :> bytes128 (word_add out_b (word (16*j)))) s0'` SUBST1_TAC THENL
        [MP_TAC frame_R THEN
         REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
         CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
         REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN READ_OVER_WRITE_ORTHOGONAL_TAC;
         ALL_TAC] THEN
       ASM_SIMP_TAC[]) in
     MAP_EVERY ASSUME_TAC [bL; bR; accfwd]) THEN
  (* finalise: the loop-carried registers, pointers, counter, stack scratch,   *)
  (* the forwarded whole-buffer input and the extended accumulating output.     *)
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    ACCUM_SPLIT_TAC THEN LEG2_POST_TAC;
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

Printf.printf "*** BODY_LEG2 PROVED ***\n";;

(* ========================================================================= *)
(* MAIN_LOOP_EQUIV: the whole steady 4x loop, from head 0x1ec (loopinv 0) to  *)
(* the loop exit 0x4b4 (loopinv (loop_count-1)), via ENSURES2_WHILE_PAUP_TAC.  *)
(*                                                                           *)
(* Loop topology (deint_mc, identical to swpS_mc outside the body):           *)
(*   0x1e4 sub x1,x1,#1 ; 0x1e8 cbz x1,0x4b4  (one-time entry guard)          *)
(*   0x1ec..0x4ab       body (177 instrs)                                     *)
(*   0x4ac sub x1,x1,#1 ; 0x4b0 cbnz x1,0x1ec (steady backedge)               *)
(*   0x4b4              loop exit / 1x remainder tail                         *)
(* At head iteration i, X1 = loop_count-1-i; the steady loop runs i=0..        *)
(* loop_count-2 (loop_count-1 iterations), so a=0, b=loop_count-1.            *)
(* ------------------------------------------------------------------------- *)

let loopinv_lam =
  list_mk_abs([`i:num`;`s1:armstate`;`s2:armstate`], loopinv_conj `i:num` (`s1:armstate`,`s2:armstate`));;
let eqin_at e = mk_gabs(`(s1:armstate,s2:armstate)`, loopinv_conj e (`s1:armstate`,`s2:armstate`));;

(* whole-loop MAYCHANGE frame: full output region + stack + all regs + flags. *)
let maych_loop =
  list_mk_icomb ",," [
    list_mk_icomb ",," [
      list_mk_icomb ",," [
        mk_icomb(`MAYCHANGE`, mk_list(maych_xregs,`:(armstate,int64)component`));
        mk_icomb(`MAYCHANGE`, mk_list(maych_qregs,`:(armstate,int128)component`))];
      `MAYCHANGE [memory :> bytes (word_add stackpointer (word 160), 64);
                  memory :> bytes (out_b:int64, 64 * loop_count)]`];
    `MAYCHANGE [PC] ,, MAYCHANGE [events] ,, MAYCHANGE [NF;ZF;CF;VF]`];;

let mainloop_precond =
  `2 <= loop_count /\
   64 * loop_count < 2 EXP 64 /\
   nonoverlapping (word pc:int64, 1856) (word pc2:int64, 1856) /\
   nonoverlapping (word pc:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc2:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc:int64, 1856) (out_b:int64, 64 * loop_count) /\
   nonoverlapping (word pc2:int64, 1856) (out_b:int64, 64 * loop_count) /\
   nonoverlapping (in_b:int64, 64 * loop_count) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (in_b:int64, 64 * loop_count) (out_b:int64, 64 * loop_count) /\
   nonoverlapping (htab_b:int64, 96) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (htab_b:int64, 96) (out_b:int64, 64 * loop_count) /\
   nonoverlapping (word_add stackpointer (word 160), 64) (out_b:int64, 64 * loop_count) /\
   aligned 16 (stackpointer:int64)`;;

let mainloop_nsteps =
  `0 + (nsum(0..(loop_count-1)-1)(\i. 177) + ((loop_count-1)-1-0) * 1) + 1`;;

let mainloop_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`stackpointer:int64`;`loop_count:num`],
  mk_imp(mainloop_precond,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x1ec)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x1ec)`;
          mk_comb(eqin_at `0`, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x4b4)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x4b4)`;
          mk_comb(eqin_at `loop_count - 1`, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_loop,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_loop,[`s2:armstate`;`s2':armstate`]))));
       mk_abs(`s:armstate`, mainloop_nsteps); mk_abs(`s:armstate`, mainloop_nsteps)]));;

let WEAKEN_COMBINED = REWRITE_RULE[IMP_IMP] ENSURES2_WEAKEN;;

(* resolve  ~(val (word (loop_count-1-i):int64) = 0)  from 0<=i, i<loop_count-1, 64*loop_count<2^64 *)
let COUNTER_NONZERO_TAC =
  SUBGOAL_THEN `~(val (word (loop_count - 1 - i):int64) = 0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `loop_count - 1 - i < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC;
    ALL_TAC];;

(* close a trivial existential  ?v. E = v *)
let TRIV_EXISTS_TAC : tactic = fun (asl,w) ->
  let _,body = dest_exists w in let l,_ = dest_eq body in (EXISTS_TAC l THEN REFL_TAC) (asl,w);;

(* find the 1-step frame theorem CHAIN sa sb in the assumptions *)
let find_frame_by_states asl sa_name sb_name =
  snd(find (fun (_,th) -> match concl th with
    | Comb(Comb(_,sa),sb) when is_var sa && is_var sb && name_of sa=sa_name && name_of sb=sb_name
      && type_of sa = `:armstate` -> true |_->false) asl);;

Printf.printf "*** MAIN_LOOP_EQUIV scaffold loaded ***\n";;

(* The loop-carried whole-buffer input and accumulating output are captured as   *)
(* theorems BEFORE the cbnz step (which discards forall/bignum assumptions), then *)
(* forwarded across the PC-only cbnz frame afterwards.                            *)
let cbnz_oldacc : thm ref = ref TRUTH;;
let cbnz_bfm0 : thm ref = ref TRUTH;;
let cbnz_bfm0' : thm ref = ref TRUTH;;

let CBNZ_SNAPSHOT_TAC : tactic =
  W(fun (asl,_) ->
     cbnz_oldacc := snd(find (fun (_,th) ->
       is_forall (concl th) && can (find_term (fun t->t=`out_b:int64`)) (concl th)) asl);
     cbnz_bfm0  := snd(find (fun (_,th) -> concl th = `bignum_from_memory (in_b,8 * loop_count) s0 = a`) asl);
     cbnz_bfm0' := snd(find (fun (_,th) -> concl th = `bignum_from_memory (in_b,8 * loop_count) s0' = a`) asl);
     ALL_TAC);;

(* forward the snapshots across the cbnz frames s0->s1 / s0'->s1'; `cnt` is the    *)
(* accumulating-output bound (`i` for the backedge, `loop_count-1` for post).      *)
let CBNZ_FORWARD_TAC cnt : tactic =
  fun (asl,w) ->
    let asl_thms = map snd asl in
    let frameL = find_frame_by_states asl "s0" "s1" and frameR = find_frame_by_states asl "s0'" "s1'" in
    let bL = REWRITE_RULE[GSYM BIGNUM_FROM_MEMORY_BYTES]
               (FRAME_FORWARD_READ asl_thms (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES] !cbnz_bfm0) frameL []) in
    let bR = REWRITE_RULE[GSYM BIGNUM_FROM_MEMORY_BYTES]
               (FRAME_FORWARD_READ asl_thms (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES] !cbnz_bfm0') frameR []) in
    let accum_goal = subst [cnt,`CNT:num`]
      `!j. j < 4 * CNT ==>
        read (memory :> bytes128 (word_add out_b (word (16*j)))) s1 =
        read (memory :> bytes128 (word_add out_b (word (16*j)))) s1'` in
    let step frame_th =
      MP_TAC frame_th THEN REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
      PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
      REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN READ_OVER_WRITE_ORTHOGONAL_TAC in
    let accfwd = TAC_PROOF(
      (map (fun t->("",t)) (asl_thms @ [!cbnz_oldacc; frameL; frameR]), accum_goal),
      GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `read (memory :> bytes128 (word_add out_b (word (16*j)))) s1 =
                    read (memory :> bytes128 (word_add out_b (word (16*j)))) s0` SUBST1_TAC THENL
       [step frameL; ALL_TAC] THEN
      SUBGOAL_THEN `read (memory :> bytes128 (word_add out_b (word (16*j)))) s1' =
                    read (memory :> bytes128 (word_add out_b (word (16*j)))) s0'` SUBST1_TAC THENL
       [step frameR; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) in
    MAP_EVERY ASSUME_TAC [bL; bR; accfwd] (asl,w);;

(* HBACKEDGE leg: the cbnz at 0x4b0 is TAKEN (X1 = loop_count-1-i /= 0), PC->0x1ec.  *)
let BACKEDGE_LEG_TAC : tactic =
  REPEAT STRIP_TAC THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  CBNZ_SNAPSHOT_TAC THEN
  ARM_N_STUTTER_LEFT_TAC DEINT_EXEC [1] None THEN
  COUNTER_NONZERO_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val (word (loop_count - 1 - i):int64) = 0)`]) THEN
  ARM_N_STUTTER_RIGHT_TAC SWPS_EXEC [1] "'" None THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CBNZ_FORWARD_TAC `i:num` THEN
  CONJ_TAC THENL [
    REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN
    TRY CHEAP_LEAF THEN TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
    TRY (COUNTER_NONZERO_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN TRY TRIV_EXISTS_TAC;
    MONOTONE_MAYCHANGE_CONJ_TAC ];;

(* resolve  val (word (loop_count-1-(loop_count-1)):int64) = 0  (counter hits 0). *)
let COUNTER_ZERO_TAC =
  SUBGOAL_THEN `val (word (loop_count - 1 - (loop_count - 1)):int64) = 0` ASSUME_TAC THENL
   [REWRITE_TAC[SUB_REFL; VAL_WORD_0]; ALL_TAC];;

(* HPOST leg: at i = loop_count-1 the cbnz at 0x4b0 is NOT taken (X1 = 0), so       *)
(* control falls through to the loop exit 0x4b4.                                   *)
let POST_LEG_TAC : tactic =
  REPEAT STRIP_TAC THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  CBNZ_SNAPSHOT_TAC THEN
  ARM_N_STUTTER_LEFT_TAC DEINT_EXEC [1] None THEN
  COUNTER_ZERO_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val (word (loop_count - 1 - (loop_count - 1)):int64) = 0`]) THEN
  ARM_N_STUTTER_RIGHT_TAC SWPS_EXEC [1] "'" None THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CBNZ_FORWARD_TAC `loop_count - 1` THEN
  CONJ_TAC THENL [
    REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN
    TRY CHEAP_LEAF THEN TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
    TRY (ASM_REWRITE_TAC[SUB_REFL;VAL_WORD_0] THEN NO_TAC) THEN TRY TRIV_EXISTS_TAC;
    MONOTONE_MAYCHANGE_CONJ_TAC ];;

(* HLOOP leg: loopinv i --> loopinv (i+1), via BODY_LEG2 weakened (append the      *)
(* trivial flag conjuncts, widen the per-block output frame to the whole loop      *)
(* frame).                                                                        *)
let HLOOP_LEG_TAC : tactic =
  fun (asl0,w0) ->
  (GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
   REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th else fail())) THEN
   SUBGOAL_THEN leg2_precond_L ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   (fun (asl,w) ->
     let g_args = snd(strip_comb w) in
     let pP' = el 1 g_args and qQ' = el 2 g_args and cC' = el 3 g_args in
     let bl2_inst = SPECL [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;
                           `stackpointer:int64`;`loop_count:num`;`i:num`] BODY_LEG2 in
     let precond_th = snd(find (fun (_,th) -> concl th = leg2_precond_L) asl) in
     let base = MP bl2_inst precond_th in
     let b_args = snd(strip_comb (concl base)) in
     let pP = el 1 b_args and qQ = el 2 b_args and cC = el 3 b_args in
     let cond1 = mk_forall(`s:armstate`, mk_forall(`s':armstate`,
        mk_imp(mk_comb(pP', `(s:armstate,s':armstate)`), mk_comb(pP, `(s:armstate,s':armstate)`)))) in
     let cond2 = mk_forall(`s:armstate`, mk_forall(`s':armstate`,
        mk_imp(mk_comb(qQ, `(s:armstate,s':armstate)`), mk_comb(qQ', `(s:armstate,s':armstate)`)))) in
     let cond3 = mk_icomb(mk_icomb(`subsumed`, cC), cC') in
     let c1_th = prove(cond1, REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
                              CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]) in
     let c2_th = prove(cond2, REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
                              CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]) in
     let c3_th = prove(mk_imp(`i < loop_count /\ 64 * loop_count < 2 EXP 64`, cond3),
        STRIP_TAC THEN
        REWRITE_TAC[subsumed;FORALL_PAIR_THM;SEQ_PAIR_SPLIT;ETA_AX;SOME_FLAGS] THEN
        REPEAT STRIP_TAC THEN
        (fun (a2,g2) ->
            let st,st' = rand(rator g2), rand g2 in
            (FIRST_X_ASSUM (fun th ->
              if rand(concl th) = st' then MP_TAC th THEN MAP_EVERY SPEC_TAC [(st',st');(st,st)]
              else NO_TAC)) (a2,g2)) THEN
        REWRITE_TAC[GSYM subsumed; ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC) in
     let ith = MP (ARITH_RULE `i < loop_count - 1 ==> i < loop_count`)
                  (snd(find (fun (_,th)->concl th=`i < loop_count - 1`) asl)) in
     let bth = snd(find (fun (_,th)->concl th=`64 * loop_count < 2 EXP 64`) asl) in
     let cond3_th = MP c3_th (CONJ ith bth) in
     let weaken_inst = ISPECL [`arm`; pP; qQ; pP'; qQ'; cC; cC'; `\(s:armstate). 177`; `\(s:armstate). 177`]
                             WEAKEN_COMBINED in
     let final = MP weaken_inst (CONJ (CONJ c1_th (CONJ c2_th cond3_th)) base) in
     ACCEPT_TAC final (asl,w))) (asl0,w0);;

Printf.printf "*** MAIN_LOOP_EQUIV leg tactics loaded ***\n";;

(* ------------------------------------------------------------------------- *)
(* Assemble the whole steady loop.                                           *)
(* ------------------------------------------------------------------------- *)

let MAIN_LOOP_EQUIV = prove(mainloop_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ENSURES2_WHILE_PAUP_TAC `0` `loop_count - 1`
    `pc + 0x1ec` `pc + 0x4b0` `pc2 + 0x1ec` `pc2 + 0x4b0`
    loopinv_lam `\(i:num) (s:armstate). T` `\(i:num) (s:armstate). T`
    `\(i:num). 177` `\(i:num). 177` `0` `0` `1` `1` `1` `1` THEN
  REPEAT CONJ_TAC THENL [
    (* [0] a < b *)
    ASM_ARITH_TAC;
    (* [1] HPRE: loopinv 0 at head, 0-step *)
    MATCH_MP_TAC ENSURES2_TRIVIAL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN MONOTONE_MAYCHANGE_CONJ_TAC;
    (* [2] HLOOP: loopinv i -> loopinv (i+1), via BODY_LEG2 weakened *)
    HLOOP_LEG_TAC;
    (* [3] HBACKEDGE: the taken cbnz *)
    BACKEDGE_LEG_TAC;
    (* [4] HPOST: the fall-through cbnz to the loop exit *)
    POST_LEG_TAC;
    (* [5][6] step-count arithmetic *)
    REWRITE_TAC[];
    REWRITE_TAC[]
  ]);;

Printf.printf "*** MAIN_LOOP_EQUIV PROVED ***\n";;



(* ===== inlined from swp_equiv_preamble.ml ===== *)

(* ========================================================================= *)
(* PREAMBLE leg of the _swp_deint <-> _swp_S whole-function equivalence.      *)
(*                                                                           *)
(*   PREAMBLE_EQUIV : the straight-line preamble 0x88 -> 0x1ec establishes    *)
(*   the steady-loop invariant  loopinv 0  from the deint/swpS entry state    *)
(*   at PC = pc + 0x88 (the point DEINT_FROM88 starts).                       *)
(*                                                                           *)
(* This is the first of the three legs that compose (via ENSURES2_TRANS) into *)
(* the whole-function equivalence:                                            *)
(*     PREAMBLE_EQUIV ++ MAIN_LOOP_EQUIV ++ TAIL_EQUIV.                        *)
(*                                                                           *)
(* KEY STRUCTURAL FACT (verified): the two kernels are BYTE-IDENTICAL over    *)
(* [0x88,0x1ec) (all 587 differing bytes are inside the steady loop body      *)
(* [0x1ec,0x4b0)).  So the preamble is proven with the SAME abbrev/rewrite    *)
(* engine as the body leg, using the IDENTITY instruction map (1--89).        *)
(*                                                                           *)
(* Two subtleties that the recipe handles:                                    *)
(*  (1) input-load GP registers (X10/X22/X28/X29/X24 loaded by the 3 ldp from *)
(*      x0=in_b) must be DIGITIZED - shared read(bytes64 in_b+8k)=            *)
(*      word(bigdigit a k) on both sides so the two loads unify.              *)
(*  (2) htable-constant vector loads (Q5/Q6/Q17/Q31 = byteswap128(h_power..)  *)
(*      / word_join(karatsuba_mid..)) must CONCRETIZE against the invariant   *)
(*      htable memory - so the htable reads must be KEPT ALIVE across the     *)
(*      right pass (discard ONLY the bignum before the right pass, not the    *)
(*      htable).                                                              *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* The compound htable-memory predicate carried by the deint entry state.     *)
(* Defined identically in the deint correctness proof; repeated here so the    *)
(* equivalence chain is self-contained (it does not load that proof).  HOL     *)
(* Light returns the cached theorem if the constant is already defined.        *)
(* ------------------------------------------------------------------------- *)

let htable_mem_4 = new_definition
 `htable_mem_4 (h:int128) (ptr:int64) (s:armstate) <=>
  read (memory :> bytes128 ptr) s =
    byteswap128(h_power h 0) /\
  read (memory :> bytes128 (word_add ptr (word 16))) s =
    word_join (karatsuba_mid(h_power h 1) : 64 word)
              (karatsuba_mid(h_power h 0) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 32))) s =
    byteswap128(h_power h 1) /\
  read (memory :> bytes128 (word_add ptr (word 48))) s =
    byteswap128(h_power h 2) /\
  read (memory :> bytes128 (word_add ptr (word 64))) s =
    word_join (karatsuba_mid(h_power h 3) : 64 word)
              (karatsuba_mid(h_power h 2) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 80))) s =
    byteswap128(h_power h 3)`;;

(* ------------------------------------------------------------------------- *)
(* The 0x88 entry-state predicate (the concrete state DEINT_FROM88 starts     *)
(* from), parametrized on the standard names and as a lambda on s.  Uses      *)
(* in_b/out_b/htab_b/stackpointer to match loopinv (deint used               *)
(* in_p/out_p/htable_p).                                                      *)
(* ------------------------------------------------------------------------- *)

let entry88 = `\s:armstate.
    aligned_bytes_loaded s (word pc) deint_mc /\
    read PC s = word (pc + 0x88) /\
    read X0 s = in_b /\ read X2 s = out_b /\ read X3 s = tag_p /\
    read X4 s = ivec_p /\ read X6 s = htab_b /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\
    read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\
    read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\
    read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\
    read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\
    read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
    read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
    read Q7 s = word 13979173243358019584 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword
        (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word 2:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
    read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
    read Q30 s = byteswap128 tag0 /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htab_b s /\
    (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_b (word(16*i)))) s = inblock i)`;;

(* the swpS-side entry state (same predicate, pc2 / swpS_mc). *)
let entry88_2 = subst [`pc2:num`,`pc:num`; `swpS_mc`,`deint_mc`] entry88;;

(* ------------------------------------------------------------------------- *)
(* Precondition: the DEINT_FROM88 nonoverlapping hypotheses (in the           *)
(* out_b/in_b/htab_b naming), PLUS the stack-vs-htable disjointness that the   *)
(* deint spec carries but that the body-leg precond omitted (needed to        *)
(* forward the htable reads across the preamble's stack writes).              *)
(* ------------------------------------------------------------------------- *)

let preamble_precond = `
   [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
    EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
   len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
   16 * nblocks < 2 EXP 64 /\ 2 <= loop_count /\ aligned 16 stackpointer /\
   nonoverlapping (out_b:int64,16 * nblocks) (word pc:int64,1856) /\
   nonoverlapping (out_b:int64,16 * nblocks) (word pc2:int64,1856) /\
   nonoverlapping (out_b:int64,16 * nblocks) (in_b:int64,16 * nblocks) /\
   nonoverlapping (out_b:int64,16 * nblocks) (htab_b:int64,192) /\
   nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
   nonoverlapping (tag_p:int64,16) (word pc2:int64,1856) /\
   nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
   nonoverlapping (ivec_p:int64,16) (word pc2:int64,1856) /\
   nonoverlapping (word_add stackpointer (word 160),64) (word pc:int64,1856) /\
   nonoverlapping (word_add stackpointer (word 160),64) (word pc2:int64,1856) /\
   nonoverlapping (word_add stackpointer (word 160),64) (in_b:int64,16 * nblocks) /\
   nonoverlapping (word_add stackpointer (word 160),64) (out_b:int64,16 * nblocks) /\
   nonoverlapping (word_add stackpointer (word 160),64) (htab_b:int64,192)`;;

(* entry relation: entry88 on each side + full loop-carried register agreement *)
(* + the shared whole-buffer input as a per-state raw bignum.                  *)
let preamble_eqin = mk_gabs(`(s1:armstate,s2:armstate)`,
  list_mk_conj [
    mk_comb(entry88,`s1:armstate`);
    mk_comb(entry88_2,`s2:armstate`);
    list_mk_conj (equiv_regs_inline carried_full (`s1:armstate`,`s2:armstate`));
    `?a. bignum_from_memory (in_b,8 * loop_count) s1 = a /\
         bignum_from_memory (in_b,8 * loop_count) s2 = a` ]);;

(* postcondition: the steady-loop invariant at i = 0, wrapped with the two    *)
(* concrete PC facts (heads at 0x1ec).  eqin_at is from swp_equiv_leg2.        *)
let preamble_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`tag_p:int64`;`ivec_p:int64`;
   `stackpointer:int64`;`len_bits:num`;`nblocks:num`;`loop_count:num`;`loop_remain:num`;
   `tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`],
  mk_imp(preamble_precond,
    list_mk_icomb "ensures2"
      [`arm`;
       preamble_eqin;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x1ec)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x1ec)`;
          mk_comb(eqin_at `0`, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_loop,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_loop,[`s2:armstate`;`s2':armstate`]))));
       `\(s:armstate). 89`; `\(s:armstate). 89`]));;

(* the identity instruction map for the byte-identical preamble. *)
let preamble_inst_map = 1--89;;

(* address bases kept concrete (pointers + counter) PLUS the four htable-      *)
(* constant vector-load destinations (Q5/Q6/Q17/Q31) so the right pass keeps   *)
(* their reads.  (The Q-pins are belt-and-braces; the decisive fix is keeping  *)
(* the htable MEMORY alive - see PREAMBLE_DISCARD_BIGNUM_ONLY_TAC below.)       *)
let preamble_regs_pin = [`X0`;`X2`;`X6`;`SP`;`X3`;`X4`;`X1`;`Q5`;`Q6`;`Q17`;`Q31`];;

(* ------------------------------------------------------------------------- *)
(* Snapshot / discard / forward helpers (memory-clause plumbing).             *)
(* ------------------------------------------------------------------------- *)

let saved_ht_pre : thm list ref = ref [];;
let saved_bfm_pre : thm list ref = ref [];;

let preamble_contains hay needle =
  let nl=String.length needle and hl=String.length hay in
  let rec go i = if i+nl>hl then false else if String.sub hay i nl = needle then true else go (i+1) in
  go 0;;

(* capture the entry htable reads (kept alive) + the shared bignum (forwarded). *)
let PREAMBLE_SNAPSHOT_TAC : tactic = fun (asl,w) ->
  saved_ht_pre := map snd (List.filter (fun (_,th) ->
     let c=string_of_term(concl th) in
     preamble_contains c "htab_b" && preamble_contains c "read (memory") asl);
  saved_bfm_pre := map snd (List.filter (fun (_,th) ->
     preamble_contains (string_of_term(concl th)) "bignum_from_memory") asl);
  ALL_TAC (asl,w);;

(* digitize the whole-buffer input into per-slot  read(bytes64 in_b+8k)=       *)
(* word(bigdigit a k)  facts (k = 0..15, both bignum sides), normalized to     *)
(* concrete offsets.  derive_slot_read / (0--15) are from swp_equiv_leg2.       *)
let PREAMBLE_DIGITIZE_TAC : tactic = fun (asl,w) ->
  let bfm_ths = filter (fun (_,th) -> match concl th with
     | Comb(Comb(Const("=",_), Comb(Comb(Const("bignum_from_memory",_),_),_)),_) -> true |_->false) asl in
  let precond_th = try snd(find (fun (_,th) -> concl th = `2 <= loop_count`) asl)
                   with Not_found -> failwith "PREAMBLE_DIGITIZE_TAC: no 2<=loop_count" in
  let derived = List.concat (map (fun (_,bfm_th) ->
      map (fun k -> CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)
                      (derive_slot_read bfm_th (mk_small_numeral k) precond_th)) (0--15)) bfm_ths) in
  MAP_EVERY ASSUME_TAC derived (asl,w);;

(* between the two passes: discard ONLY the raw bignum (it references the       *)
(* stashed left state and breaks the right pass).  KEEP the htable reads alive  *)
(* so the right ldr-q loads concretize to the shared invariant values.          *)
let PREAMBLE_DISCARD_BIGNUM_ONLY_TAC : tactic =
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    can (find_term (fun t->match t with Comb(Const("bignum_from_memory",_),_)->true|_->false)) (concl th));;

(* find the accumulated MAYCHANGE frame ending at named state (from s0/s0'). *)
let find_frame_to asl sto_name =
  snd(find (fun (_,th) -> match concl th with
     Comb(Comb(_,sa),sb) when is_var sa && is_var sb && name_of sb=sto_name
       && (let n=name_of sa in n="s0" || n="s0'") -> true|_->false) asl);;

(* re-establish the shared whole-buffer input at s89 / s89' by forwarding the   *)
(* entry snapshots across the two accumulated frames.  (The htable survives     *)
(* natively - it was never discarded - so only the bignum needs forwarding.)    *)
let PREAMBLE_FORWARD_BIGNUM_TAC : tactic = fun (asl,w) ->
  let asl_thms = map snd asl in
  let frame_L = find_frame_to asl "s89" and frame_R = find_frame_to asl "s89'" in
  let is_s0 th = can (find_term (fun t->t=`s0:armstate`)) (concl th) in
  let bfm_s0  = find is_s0 !saved_bfm_pre
  and bfm_s0' = find (fun th->not(is_s0 th)) !saved_bfm_pre in
  let bL = REWRITE_RULE[GSYM BIGNUM_FROM_MEMORY_BYTES]
             (FRAME_FORWARD_READ asl_thms (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES] bfm_s0) frame_L []) in
  let bR = REWRITE_RULE[GSYM BIGNUM_FROM_MEMORY_BYTES]
             (FRAME_FORWARD_READ asl_thms (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES] bfm_s0') frame_R []) in
  MAP_EVERY ASSUME_TAC [bL; bR] (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Per-conjunct leaf closers for the relational postcondition (loopinv 0).    *)
(* ------------------------------------------------------------------------- *)

(* close  ?a. read c sL = a /\ read c sR = a  by finding a witness present on   *)
(* BOTH sides (some carried regs have BOTH a concrete value AND an abbrev; we   *)
(* must pick the common one, which CHEAP_LEAF's first-match could miss).        *)
let EQUIV_EXISTS_TAC : tactic = fun (asl,w) ->
  let v,body = dest_exists w in
  let c1,c2 = dest_conj body in
  let l1 = lhs c1 and l2 = lhs c2 in
  let rhses l = setify (map (fun (_,th) -> rhs (concl th))
     (filter (fun (_,th) -> is_eq(concl th) && lhs(concl th) = l) asl)) in
  let common = intersect (rhses l1) (rhses l2) in
  (match common with
   | w0::_ ->
      let th1 = snd(find (fun (_,th)->is_eq(concl th)&&lhs(concl th)=l1&&rhs(concl th)=w0) asl) in
      let th2 = snd(find (fun (_,th)->is_eq(concl th)&&lhs(concl th)=l2&&rhs(concl th)=w0) asl) in
      (EXISTS_TAC w0 THEN CONJ_TAC THENL [ACCEPT_TAC th1; ACCEPT_TAC th2]) (asl,w)
   | [] -> failwith "EQUIV_EXISTS_TAC: no common witness");;

(* close  ?v. read (bytes128 A) sa = v /\ read (bytes128 A) sb = v  by showing   *)
(* the two 128-bit reads equal (via their two 64-bit halves).                   *)
let STACK_PAIR_GEN_TAC : tactic = fun (asl,w) ->
  let _,body = dest_exists w in
  let c1,c2 = dest_conj body in
  let readA = lhs c1 and readB = lhs c2 in
  (SUBGOAL_THEN (mk_eq(readA, readB)) (fun th -> EXISTS_TAC readB THEN REWRITE_TAC[th]) THEN
   REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV
     [WORD_RULE `word_add (word_add x (word a)) (word b):int64 = word_add x (word (a+b))`] THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]) (asl,w);;

(* the omnibus leaf closer for the loopinv-0 conjuncts. *)
let PREAMBLE_LEAF_TAC : tactic =
  TRY (REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `~(j < 0)`] THEN NO_TAC) THEN     (* vacuous accum + X0/X2 mult=0 *)
  TRY (FIRST [EQUIV_EXISTS_TAC; STACK_PAIR_GEN_TAC; TRIV_EXISTS_TAC] THEN NO_TAC) THEN  (* all existentials *)
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN                                    (* forwarded bignum *)
  TRY (CONV_TAC WORD_RULE THEN NO_TAC) THEN                                   (* pointers X0/X2 *)
  TRY (REWRITE_TAC[SUB_0] THEN                                                (* down-counter X1 *)
       SUBGOAL_THEN `word_sub (word loop_count:int64) (word 1) = word (loop_count - 1)` SUBST1_TAC THENL
        [SUBGOAL_THEN `loop_count = (loop_count-1)+1` (fun t->ONCE_REWRITE_TAC[t]) THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[ADD_SUB] THEN CONV_TAC WORD_RULE;
         CONV_TAC WORD_RULE]);;

Printf.printf "*** swp_equiv_preamble scaffold loaded ***\n";;

(* ------------------------------------------------------------------------- *)
(* THE PREAMBLE LEG.  entry (0x88) --> loopinv 0 (0x1ec).                      *)
(* ------------------------------------------------------------------------- *)

let sta_preamble : (int * thm) list ref = ref [];;

let PREAMBLE_EQUIV = prove(preamble_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(BETA_RULE) THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4; mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  (* both cbz-branch resolutions: the entry-guard and the down-count both nonzero *)
  SUBGOAL_THEN `~(val (word loop_count:int64) = 0) /\
                ~(val (word_sub (word loop_count) (word 1):int64) = 0)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `loop_count < 2 EXP 64 /\ loop_count - 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `16 * nblocks < 2 EXP 64`) THEN MP_TAC(ASSUME `nblocks DIV 4 = loop_count`) THEN
      ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `word_sub (word loop_count) (word 1):int64 = word (loop_count - 1)` SUBST1_TAC THENL
       [SUBGOAL_THEN `loop_count = (loop_count-1)+1` (fun t->ONCE_REWRITE_TAC[t]) THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[ADD_SUB] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC]; ALL_TAC] THEN
  (* snapshot htable + bignum, digitize the input loads *)
  PREAMBLE_SNAPSHOT_TAC THEN PREAMBLE_DIGITIZE_TAC THEN
  (* left program: abbreviate the reordered outputs *)
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--89) sta_preamble (Some (replicate preamble_regs_pin 89)) THEN
  (* drop ONLY the raw bignum before the right pass (keep htable alive) *)
  PREAMBLE_DISCARD_BIGNUM_ONLY_TAC THEN
  (* right program: rewrite its reordered outputs onto the same abbreviations *)
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--89) preamble_inst_map sta_preamble
    (Some (replicate preamble_regs_pin 89)) THEN
  (* re-establish the shared whole-buffer input at the loop-head states *)
  PREAMBLE_FORWARD_BIGNUM_TAC THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN PREAMBLE_LEAF_TAC;
    MONOTONE_MAYCHANGE_CONJ_TAC ]);;

Printf.printf "*** PREAMBLE_EQUIV PROVED ***\n";;



(* ===== inlined from swp_equiv_tail.ml ===== *)

(* ========================================================================= *)
(* TAIL leg of the _swp_deint <-> _swp_S whole-function equivalence.          *)
(*                                                                           *)
(* The tail [0x4b4, 0x740) is BYTE-IDENTICAL between the two kernels (all     *)
(* schedule differences are inside the steady 4x body [0x1ec,0x4b0)). It is:  *)
(*   [0x4b4, 0x628)  reduce_last          (straight-line, 93 instrs)          *)
(*   0x628 cbz X16,0x6fc                  (1x remainder-loop entry guard)     *)
(*   [0x62c, 0x6f8)  remainder-loop body  (51 instrs; runs loop_remain times) *)
(*   0x6f8 cbnz X16,0x62c                 (remainder-loop back-edge)          *)
(*   [0x6fc, 0x73c]  finalize + epilogue  (ends RET @ 0x73c)                  *)
(*                                                                           *)
(* This file proves REMBODY_LEG: the per-iteration body leg of the 1x         *)
(* remainder loop (reminv i --> reminv (i+1)), the loop-body crux of the      *)
(* tail. The remainder loop counts UP (X16 = loop_remain - i), advancing the  *)
(* pointers by one 16-byte block per iteration from the 4x-loop end.          *)
(*                                                                           *)
(* Same identical-code equivalence engine as the preamble (abbrev-left /      *)
(* rewrite-right, IDENTITY instruction map, keep the invariant htable memory  *)
(* alive across the right pass). The remainder block's input is derived from  *)
(* the whole-buffer per-128-block shared-input invariant on entry (splitting  *)
(* the bytes128 read into the two bytes64 halves the ldp reads).              *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* The remainder-loop equivalence invariant.                                  *)
(* ------------------------------------------------------------------------- *)

(* The registers genuinely carried across the 1x loop (matching the deint     *)
(* correctness proof's remainder invariant): round keys, the settled GHASH    *)
(* accumulator Q30, Q12/Q14, the counter-block scalars, and pointers.  This   *)
(* is a SUBSET of the 4x carried_full - the 4x-body transients (X22/X23/Q1/   *)
(* Q9/Q10/Q11) are dead on entry to the 1x loop and are NOT carried.          *)
let rem_carried =
  (map mkxc [11;12;13;20;21;15;3;4]) @
  (map mkqc [7;12;14;18;19;20;21;22;23;24;25;26;27;30]);;

(* Pointers/counter at iteration e: X0/X2 advance by 16*e from the 4x end     *)
(* (base offset 64*loop_count), X16 counts down from loop_remain.             *)
let rem_ptrs_at e (s1v,s2v) =
  let off = mk_binop `(+):num->num->num`
              (mk_binop `( * ):num->num->num` `64` `loop_count:num`)
              (mk_binop `( * ):num->num->num` `16` e) in
  let woff = mk_comb(`word:num->int64`, off) in
  let x16v = mk_comb(`word:num->int64`, mk_binop `(-):num->num->num` `loop_remain:num` e) in
  [ mk_eq(mk_read `X0` s1v, mk_binop `word_add:int64->int64->int64` `in_b:int64` woff);
    mk_eq(mk_read `X0` s2v, mk_binop `word_add:int64->int64->int64` `in_b:int64` woff);
    mk_eq(mk_read `X2` s1v, mk_binop `word_add:int64->int64->int64` `out_b:int64` woff);
    mk_eq(mk_read `X2` s2v, mk_binop `word_add:int64->int64->int64` `out_b:int64` woff);
    mk_eq(mk_read `X6` s1v, `htab_b:int64`);
    mk_eq(mk_read `X6` s2v, `htab_b:int64`);
    mk_eq(mk_read `SP` s1v, `stackpointer:int64`);
    mk_eq(mk_read `SP` s2v, `stackpointer:int64`);
    mk_eq(mk_read `X16` s1v, x16v);
    mk_eq(mk_read `X16` s2v, x16v) ];;

(* accumulating output: blocks 0 .. 4*loop_count+e written so far are equal. *)
let rem_accum_at e (s1v,s2v) =
  let ad = mk_binop `word_add:int64->int64->int64` `out_b:int64` (mk_comb(`word:num->int64`,`16 * j`)) in
  let a1 = list_mk_icomb "read" [comp128 ad; s1v] and a2 = list_mk_icomb "read" [comp128 ad; s2v] in
  let bound = mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `4` `loop_count:num`) e in
  mk_forall(`j:num`, mk_imp(mk_binop `(<):num->num->bool` `j:num` bound, mk_eq(a1,a2)));;

(* the whole input buffer shared per 128-bit block (i-independent). *)
let rem_input_shared (s1v,s2v) =
  let ad = mk_binop `word_add:int64->int64->int64` `in_b:int64` (mk_comb(`word:num->int64`,`16 * j`)) in
  let a1 = list_mk_icomb "read" [comp128 ad; s1v] and a2 = list_mk_icomb "read" [comp128 ad; s2v] in
  mk_forall(`j:num`, mk_imp(mk_binop `(<):num->num->bool` `j:num` `nblocks:num`, mk_eq(a1,a2)));;

let reminv_u e (s1v,s2v) =
  list_mk_conj (
      rem_ptrs_at e (s1v,s2v)
    @ equiv_regs_inline rem_carried (s1v,s2v)
    @ (map (fun r -> shared128 r (s1v,s2v)) regions128)
    @ [ rem_input_shared (s1v,s2v); rem_accum_at e (s1v,s2v) ]);;

(* ------------------------------------------------------------------------- *)
(* The remainder-loop MAYCHANGE frame: like the 4x maych_loop but the         *)
(* register list ALSO includes X16 (the 1x-loop counter, written by          *)
(* sub x16,x16,#1 - the 4x loop uses X1 instead), and the output region       *)
(* covers the WHOLE output [out_b, 16*nblocks) (the remainder writes blocks    *)
(* beyond the 4x [out_b, 64*loop_count) range).                               *)
let maych_xregs_rem = maych_xregs @ [`X16`];;

let maych_rem =
  list_mk_icomb ",," [
    list_mk_icomb ",," [
      list_mk_icomb ",," [
        mk_icomb(`MAYCHANGE`, mk_list(maych_xregs_rem,`:(armstate,int64)component`));
        mk_icomb(`MAYCHANGE`, mk_list(maych_qregs,`:(armstate,int128)component`))];
      `MAYCHANGE [memory :> bytes (word_add stackpointer (word 160), 64);
                  memory :> bytes (out_b:int64, 16 * nblocks)]`];
    `MAYCHANGE [PC] ,, MAYCHANGE [events] ,, MAYCHANGE [NF;ZF;CF;VF]`];;

(* ------------------------------------------------------------------------- *)
(* The body-leg goal + precondition.                                          *)
(* ------------------------------------------------------------------------- *)

let rembody_precond =
  `i + 1 <= loop_remain /\
   nblocks = 4 * loop_count + loop_remain /\ loop_remain < 4 /\
   64 * loop_count + 16 * loop_remain < 2 EXP 64 /\
   nonoverlapping (word pc:int64, 1856) (word pc2:int64, 1856) /\
   nonoverlapping (word pc:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc2:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc:int64, 1856) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (word pc2:int64, 1856) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (in_b:int64, 16 * nblocks) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (in_b:int64, 16 * nblocks) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (htab_b:int64, 192) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (htab_b:int64, 192) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (word_add stackpointer (word 160), 64) (out_b:int64, 16 * nblocks) /\
   aligned 16 (stackpointer:int64)`;;

let rembody_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`stackpointer:int64`;
   `nblocks:num`;`loop_count:num`;`loop_remain:num`;`i:num`],
  mk_imp(rembody_precond,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x62c)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x62c)`;
          mk_comb(mk_gabs(`(s1:armstate,s2:armstate)`, reminv_u `i:num` (`s1:armstate`,`s2:armstate`)),
                  `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x6f8)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x6f8)`;
          mk_comb(mk_gabs(`(s1:armstate,s2:armstate)`, reminv_u `i+1` (`s1:armstate`,`s2:armstate`)),
                  `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_rem,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_rem,[`s2:armstate`;`s2':armstate`]))));
       `\(s:armstate). 51`; `\(s:armstate). 51`]));;

let rem_inst_map = 1--51;;
let rem_pin = [`X0`;`X2`;`X6`;`SP`;`X3`;`X4`;`X16`;`Q5`;`Q6`;`Q17`;`Q31`];;

(* ------------------------------------------------------------------------- *)
(* Tactics.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* the down-counter step  word_sub (word (loop_remain-i)) 1 = word (loop_remain-(i+1)). *)
let REM_CTR_TAC =
  SUBGOAL_THEN `loop_remain - i = (loop_remain - (i+1)) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[ADD_SUB] THEN CONV_TAC WORD_RULE];;

(* On entry, derive the current remainder block's TWO shared bytes64 input     *)
(* reads (offsets 64*loop_count+16*i and +8, on both states) from the whole-   *)
(* buffer per-128-block shared input, by specializing to block 4*loop_count+i  *)
(* and splitting the bytes128 read into its two bytes64 halves.                *)
let REM_DERIVE_INPUT_TAC : tactic = fun (asl,w) ->
  let inpf = snd(find (fun (_,th) -> is_forall(concl th) &&
      let s=string_of_term(concl th) in preamble_contains s "in_b" && preamble_contains s "nblocks") asl) in
  let j0lt = try snd(find (fun (_,th)->concl th=`4 * loop_count + i < nblocks`) asl)
             with Not_found -> TAC_PROOF((asl,`4 * loop_count + i < nblocks`), ASM_ARITH_TAC) in
  let bytes128_eq = REWRITE_RULE[ARITH_RULE `16 * (4 * loop_count + i) = 64 * loop_count + 16 * i`]
                      (MP (SPEC `4 * loop_count + i` inpf) j0lt) in
  let lhs_e, rhs_e = dest_eq (concl bytes128_eq) in
  let sA = rand lhs_e and sB = rand rhs_e in
  let mkread comp s = list_mk_icomb "read" [comp; s] in
  let c_lo = `memory :> bytes64 (word_add in_b (word (64*loop_count+16*i)))` in
  let c_hi = `memory :> bytes64 (word_add (word_add in_b (word (64*loop_count+16*i))) (word 8))` in
  let split_imp = prove(
    mk_imp(concl bytes128_eq,
      mk_conj(mk_eq(mkread c_lo sA, mkread c_lo sB), mk_eq(mkread c_hi sA, mkread c_hi sB))),
    GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    MAP_EVERY (fun t -> ABBREV_TAC t) [
      mk_eq(`a1:int64`, mkread c_lo sA); mk_eq(`a2:int64`, mkread c_lo sB);
      mk_eq(`b1:int64`, mkread c_hi sA); mk_eq(`b2:int64`, mkread c_hi sB)] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\w:int128. (word_subword w (0,64):int64, word_subword w (64,64):int64)`) THEN
    REWRITE_TAC[PAIR_EQ] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_JOIN_SELF] THEN CONV_TAC WORD_BLAST) in
  let two = MP split_imp bytes128_eq in
  let fold_eq = WORD_RULE `word_add (word_add in_b (word (64*loop_count+16*i))) (word 8):int64 =
                           word_add in_b (word ((64*loop_count+16*i)+8))` in
  (CONJUNCTS_THEN ASSUME_TAC (REWRITE_RULE[fold_eq] two)) (asl,w);;

(* snapshot the whole-buffer input and accumulating-output foralls before      *)
(* stepping (they reference the stashed left state and must be dropped before   *)
(* the right pass, then forwarded across the two frames afterwards).            *)
let rem_saved_inpf : thm ref = ref TRUTH;;
let rem_saved_accf : thm ref = ref TRUTH;;

let REM_SNAPSHOT_TAC : tactic = fun (asl,w) ->
  rem_saved_inpf := (try snd(find (fun (_,th) -> is_forall(concl th) &&
      let s=string_of_term(concl th) in preamble_contains s "in_b" && preamble_contains s "nblocks") asl)
    with Not_found->TRUTH);
  rem_saved_accf := (try snd(find (fun (_,th) -> is_forall(concl th) &&
      preamble_contains (string_of_term(concl th)) "out_b") asl) with Not_found->TRUTH);
  ALL_TAC (asl,w);;

let find_frame_rb asl sto = snd(find (fun (_,th) -> match concl th with
   Comb(Comb(_,sa),sb) when is_var sa && is_var sb && name_of sb=sto
     && (let n=name_of sa in n="s0"||n="s0'") -> true|_->false) asl);;

(* re-establish the read-only whole-buffer input equality and the accumulating  *)
(* output equality at the loop-back states s51/s51' by forwarding across the     *)
(* two accumulated frames (in_b and the old output blocks are disjoint from the  *)
(* single freshly-written block).                                               *)
let REM_FWD_TAC : tactic = fun (asl,w) ->
  let asl_thms = map snd asl in
  let fL = find_frame_rb asl "s51" and fR = find_frame_rb asl "s51'" in
  let step_ro frame =
    MP_TAC frame THEN REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN READ_OVER_WRITE_ORTHOGONAL_TAC in
  let inp_goal = `!j. j < nblocks
      ==> read (memory :> bytes128 (word_add in_b (word (16*j)))) s51 =
          read (memory :> bytes128 (word_add in_b (word (16*j)))) s51'` in
  let inpfwd = TAC_PROOF(
    (map (fun t->("",t)) (asl_thms @ [!rem_saved_inpf; fL; fR]), inp_goal),
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `nonoverlapping (word_add in_b (word (16*j)):int64,16)
                    (word_add out_b (word (64*loop_count+16*i)),16)` ASSUME_TAC THENL
     [NONOVERLAPPING_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_b (word (16*j)))) s51 =
                  read (memory :> bytes128 (word_add in_b (word (16*j)))) s0` SUBST1_TAC THENL
     [step_ro fL; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_b (word (16*j)))) s51' =
                  read (memory :> bytes128 (word_add in_b (word (16*j)))) s0'` SUBST1_TAC THENL
     [step_ro fR; ALL_TAC] THEN ASM_SIMP_TAC[]) in
  let acc_goal = `!j. j < 4*loop_count+i
      ==> read (memory :> bytes128 (word_add out_b (word (16*j)))) s51 =
          read (memory :> bytes128 (word_add out_b (word (16*j)))) s51'` in
  let accfwd = TAC_PROOF(
    (map (fun t->("",t)) (asl_thms @ [!rem_saved_accf; fL; fR]), acc_goal),
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `16 * j + 16 <= 64 * loop_count + 16 * i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word_add out_b (word (16*j)):int64,16)
                    (word_add out_b (word (64*loop_count+16*i)),16)` ASSUME_TAC THENL
     [NONOVERLAPPING_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add out_b (word (16*j)))) s51 =
                  read (memory :> bytes128 (word_add out_b (word (16*j)))) s0` SUBST1_TAC THENL
     [step_ro fL; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add out_b (word (16*j)))) s51' =
                  read (memory :> bytes128 (word_add out_b (word (16*j)))) s0'` SUBST1_TAC THENL
     [step_ro fR; ALL_TAC] THEN ASM_SIMP_TAC[]) in
  MAP_EVERY ASSUME_TAC [inpfwd; accfwd] (asl,w);;

Printf.printf "*** swp_equiv_tail scaffold loaded ***\n";;

(* ------------------------------------------------------------------------- *)
(* THE REMAINDER-LOOP BODY LEG.  reminv i --> reminv (i+1).                    *)
(* ------------------------------------------------------------------------- *)

let sta_rembody : (int * thm) list ref = ref [];;

let REMBODY_LEG = prove(rembody_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  SUBGOAL_THEN `4 * loop_count + i < nblocks` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (* on entry: derive the current block's shared bytes64 input, snapshot the foralls *)
  REM_DERIVE_INPUT_TAC THEN REM_SNAPSHOT_TAC THEN
  (* left program: abbreviate the reordered outputs *)
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--51) sta_rembody (Some (replicate rem_pin 51)) THEN
  (* drop the whole-buffer foralls before the right pass (re-established by forwarding) *)
  DISCARD_ASSUMPTIONS_TAC (fun th ->
     (is_forall (concl th) && can (find_term (fun t->t=`out_b:int64`)) (concl th))
     || (is_forall (concl th) && can (find_term (fun t->t=`in_b:int64`)) (concl th))) THEN
  (* right program: rewrite its reordered outputs onto the same abbreviations *)
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--51) rem_inst_map sta_rembody (Some (replicate rem_pin 51)) THEN
  (* forward the whole-buffer input + accumulating output to the loop-back states *)
  REM_FWD_TAC THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  CONJ_TAC THENL [
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN
    TRY (REWRITE_TAC[ARITH_RULE `64*loop_count+16*(i+1) = (64*loop_count+16*i)+16`] THEN
         CONV_TAC WORD_RULE THEN NO_TAC) THEN                            (* pointers X0/X2 at i+1 *)
    TRY (REM_CTR_TAC THEN NO_TAC) THEN                                   (* down-counter X16 *)
    TRY (FIRST [EQUIV_EXISTS_TAC; STACK_PAIR_GEN_TAC; TRIV_EXISTS_TAC] THEN NO_TAC) THEN  (* reg/stack/htab *)
    TRY (SUBGOAL_THEN `4 * loop_count + loop_remain = nblocks` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN NO_TAC) THEN          (* whole-buffer input forall *)
    TRY (REWRITE_TAC[ARITH_RULE `j < 4*loop_count+i+1 <=> j < 4*loop_count+i \/ j = 4*loop_count+i`] THEN
         REWRITE_TAC[TAUT `(p\/q)==>r <=> (p==>r)/\(q==>r)`; FORALL_AND_THM] THEN CONJ_TAC THENL
          [ASM_REWRITE_TAC[];                                           (* old accumulated blocks *)
           REWRITE_TAC[FORALL_UNWIND_THM2] THEN                         (* the one new block *)
           REWRITE_TAC[ARITH_RULE `16 * (4 * loop_count + i) = 64 * loop_count + 16 * i`] THEN
           ASM_REWRITE_TAC[]] THEN NO_TAC) THEN
    TRY (ASM_REWRITE_TAC[] THEN NO_TAC);
    MONOTONE_MAYCHANGE_CONJ_TAC ]);;

Printf.printf "*** REMBODY_LEG PROVED ***\n";;

(* ========================================================================= *)
(* REMLOOP_EQUIV: the whole 1x remainder loop, from head 0x62c (reminv 0) to  *)
(* the loop exit 0x6fc (reminv loop_remain), via ENSURES2_WHILE_PAUP_TAC.     *)
(*                                                                           *)
(* Loop topology (identical in both kernels):                                 *)
(*   0x628 cbz  x16,0x6fc     (one-time entry guard; loop_remain=0 -> skip)   *)
(*   0x62c..0x6f7            body (51 instrs), incl. sub x16,x16,#1 @ 0x6f4   *)
(*   0x6f8 cbnz x16,0x62c     (back-edge)                                      *)
(*   0x6fc                    loop exit / finalize                            *)
(* At head iteration i, X16 = loop_remain-i.  The loop runs i=0..loop_remain-1 *)
(* (loop_remain iterations), so a=0, b=loop_remain.  This theorem covers the   *)
(* loop_remain>=1 case; the loop_remain=0 path (0x628 -> 0x6fc directly) is a   *)
(* separate lockstep-only segment handled in the tail assembly.               *)
(* ------------------------------------------------------------------------- *)

let rem_loopinv_lam =
  list_mk_abs([`i:num`;`s1:armstate`;`s2:armstate`], reminv_u `i:num` (`s1:armstate`,`s2:armstate`));;
let rem_eqin_at e = mk_gabs(`(s1:armstate,s2:armstate)`, reminv_u e (`s1:armstate`,`s2:armstate`));;

let remloop_precond =
  `1 <= loop_remain /\
   nblocks = 4 * loop_count + loop_remain /\ loop_remain < 4 /\
   64 * loop_count + 16 * loop_remain < 2 EXP 64 /\
   nonoverlapping (word pc:int64, 1856) (word pc2:int64, 1856) /\
   nonoverlapping (word pc:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc2:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc:int64, 1856) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (word pc2:int64, 1856) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (in_b:int64, 16 * nblocks) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (in_b:int64, 16 * nblocks) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (htab_b:int64, 192) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (htab_b:int64, 192) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (word_add stackpointer (word 160), 64) (out_b:int64, 16 * nblocks) /\
   aligned 16 (stackpointer:int64)`;;

let remloop_nsteps =
  `0 + (nsum(0..loop_remain-1)(\i. 51) + (loop_remain-1-0) * 1) + 1`;;

let remloop_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`stackpointer:int64`;
   `nblocks:num`;`loop_count:num`;`loop_remain:num`],
  mk_imp(remloop_precond,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x62c)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x62c)`;
          mk_comb(rem_eqin_at `0`, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x6fc)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x6fc)`;
          mk_comb(rem_eqin_at `loop_remain:num`, `(s1:armstate,s2:armstate)`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_rem,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_rem,[`s2:armstate`;`s2':armstate`]))));
       mk_abs(`s:armstate`, remloop_nsteps); mk_abs(`s:armstate`, remloop_nsteps)]));;

let WEAKEN_COMBINED = REWRITE_RULE[IMP_IMP] ENSURES2_WEAKEN;;

(* find the 1-step frame theorem CHAIN sa sb (used by the cbnz-forward). *)
let find_frame_by_states asl sa_name sb_name =
  snd(find (fun (_,th) -> match concl th with
    | Comb(Comb(_,sa),sb) when is_var sa && is_var sb && name_of sa=sa_name && name_of sb=sb_name
      && type_of sa = `:armstate` -> true |_->false) asl);;

(* The whole-buffer input + accumulating output foralls are relational; the    *)
(* single cbnz step (0x6f8) touches only PC/events, so they forward across the  *)
(* 1-step frame trivially.  Snapshot them before stepping, forward after.       *)
let rem_cbnz_inpf : thm ref = ref TRUTH;;
let rem_cbnz_accf : thm ref = ref TRUTH;;

let REM_CBNZ_SNAPSHOT_TAC : tactic =
  W(fun (asl,_) ->
    rem_cbnz_inpf := (try snd(find (fun (_,th) -> is_forall(concl th) &&
        let s=string_of_term(concl th) in preamble_contains s "in_b" && preamble_contains s "nblocks") asl)
      with Not_found->TRUTH);
    rem_cbnz_accf := (try snd(find (fun (_,th) -> is_forall(concl th) &&
        preamble_contains (string_of_term(concl th)) "out_b") asl) with Not_found->TRUTH);
    ALL_TAC);;

(* cnt = accumulating-output bound at the target (i for backedge, loop_remain for post). *)
let REM_CBNZ_FORWARD_TAC cnt : tactic = fun (asl,w) ->
  let asl_thms = map snd asl in
  let fL = find_frame_by_states asl "s0" "s1" and fR = find_frame_by_states asl "s0'" "s1'" in
  let step frame =
    MP_TAC frame THEN REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN READ_OVER_WRITE_ORTHOGONAL_TAC in
  let inp_goal = `!j. j < nblocks
      ==> read (memory :> bytes128 (word_add in_b (word (16*j)))) s1 =
          read (memory :> bytes128 (word_add in_b (word (16*j)))) s1'` in
  let inpfwd = TAC_PROOF(
    (map (fun t->("",t)) (asl_thms @ [!rem_cbnz_inpf; fL; fR]), inp_goal),
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_b (word (16*j)))) s1 =
                  read (memory :> bytes128 (word_add in_b (word (16*j)))) s0` SUBST1_TAC THENL
     [step fL; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_b (word (16*j)))) s1' =
                  read (memory :> bytes128 (word_add in_b (word (16*j)))) s0'` SUBST1_TAC THENL
     [step fR; ALL_TAC] THEN ASM_SIMP_TAC[]) in
  let acc_goal = subst [cnt,`CNT:num`]
    `!j. j < 4*loop_count+CNT
      ==> read (memory :> bytes128 (word_add out_b (word (16*j)))) s1 =
          read (memory :> bytes128 (word_add out_b (word (16*j)))) s1'` in
  let accfwd = TAC_PROOF(
    (map (fun t->("",t)) (asl_thms @ [!rem_cbnz_accf; fL; fR]), acc_goal),
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add out_b (word (16*j)))) s1 =
                  read (memory :> bytes128 (word_add out_b (word (16*j)))) s0` SUBST1_TAC THENL
     [step fL; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add out_b (word (16*j)))) s1' =
                  read (memory :> bytes128 (word_add out_b (word (16*j)))) s0'` SUBST1_TAC THENL
     [step fR; ALL_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) in
  MAP_EVERY ASSUME_TAC [inpfwd; accfwd] (asl,w);;

(* HLOOP leg: reminv i --> reminv (i+1), via REMBODY_LEG weakened (append the   *)
(* trivial flag conjuncts; the frame is already maych_rem so subsumption is     *)
(* reflexive).                                                                  *)
let REM_HLOOP_LEG_TAC : tactic =
  fun (asl0,w0) ->
  (GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
   REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th else fail())) THEN
   SUBGOAL_THEN rembody_precond ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   (fun (asl,w) ->
     let g_args = snd(strip_comb w) in
     let pP' = el 1 g_args and qQ' = el 2 g_args and cC' = el 3 g_args in
     let bl_inst = SPECL [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;
                          `stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`;`i:num`] REMBODY_LEG in
     let precond_th = snd(find (fun (_,th) -> concl th = rembody_precond) asl) in
     let base = MP bl_inst precond_th in
     let b_args = snd(strip_comb (concl base)) in
     let pP = el 1 b_args and qQ = el 2 b_args and cC = el 3 b_args in
     let cond1 = mk_forall(`s:armstate`, mk_forall(`s':armstate`,
        mk_imp(mk_comb(pP', `(s:armstate,s':armstate)`), mk_comb(pP, `(s:armstate,s':armstate)`)))) in
     let cond2 = mk_forall(`s:armstate`, mk_forall(`s':armstate`,
        mk_imp(mk_comb(qQ, `(s:armstate,s':armstate)`), mk_comb(qQ', `(s:armstate,s':armstate)`)))) in
     let cond3 = mk_icomb(mk_icomb(`subsumed`, cC), cC') in
     let c1_th = prove(cond1, REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
                              CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]) in
     let c2_th = prove(cond2, REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
                              CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]) in
     let c3_th = prove(cond3,
        REWRITE_TAC[subsumed;FORALL_PAIR_THM;SEQ_PAIR_SPLIT;ETA_AX;SOME_FLAGS] THEN
        REPEAT STRIP_TAC THEN
        (fun (a2,g2) ->
            let st,st' = rand(rator g2), rand g2 in
            (FIRST_X_ASSUM (fun th ->
              if rand(concl th) = st' then MP_TAC th THEN MAP_EVERY SPEC_TAC [(st',st');(st,st)]
              else NO_TAC)) (a2,g2)) THEN
        REWRITE_TAC[GSYM subsumed; ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC) in
     let weaken_inst = ISPECL [`arm`; pP; qQ; pP'; qQ'; cC; cC'; `\(s:armstate). 51`; `\(s:armstate). 51`]
                             WEAKEN_COMBINED in
     let final = MP weaken_inst (CONJ (CONJ c1_th (CONJ c2_th c3_th)) base) in
     ACCEPT_TAC final (asl,w))) (asl0,w0);;

(* HBACKEDGE leg: at 0x6f8 reminv i (0<i<loop_remain), cbnz X16 taken (X16 =    *)
(* loop_remain-i /= 0), PC -> 0x62c.                                            *)
let REM_BACKEDGE_LEG_TAC : tactic =
  REPEAT STRIP_TAC THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  REM_CBNZ_SNAPSHOT_TAC THEN
  SUBGOAL_THEN `~(val (word (loop_remain - i):int64) = 0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `loop_remain - i < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ARM_N_STUTTER_LEFT_TAC DEINT_EXEC [1] None THEN
  ARM_N_STUTTER_RIGHT_TAC SWPS_EXEC [1] "'" None THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REM_CBNZ_FORWARD_TAC `i:num` THEN
  CONJ_TAC THENL [
    REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN
    TRY (FIRST[EQUIV_EXISTS_TAC;STACK_PAIR_GEN_TAC;TRIV_EXISTS_TAC] THEN NO_TAC) THEN
    TRY (SUBGOAL_THEN `4 * loop_count + loop_remain = nblocks` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN NO_TAC) THEN
    TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN TRY (CONV_TAC WORD_RULE);
    MONOTONE_MAYCHANGE_CONJ_TAC ];;

(* HPOST leg: at 0x6f8 reminv loop_remain, cbnz X16 NOT taken (X16 = 0), so     *)
(* control falls through to the loop exit 0x6fc.                                *)
let REM_POST_LEG_TAC : tactic =
  REPEAT STRIP_TAC THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  REM_CBNZ_SNAPSHOT_TAC THEN
  SUBGOAL_THEN `val (word (loop_remain - loop_remain):int64) = 0` ASSUME_TAC THENL
   [REWRITE_TAC[SUB_REFL; VAL_WORD_0]; ALL_TAC] THEN
  ARM_N_STUTTER_LEFT_TAC DEINT_EXEC [1] None THEN
  ARM_N_STUTTER_RIGHT_TAC SWPS_EXEC [1] "'" None THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REM_CBNZ_FORWARD_TAC `loop_remain:num` THEN
  CONJ_TAC THENL [
    REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN
    TRY (FIRST[EQUIV_EXISTS_TAC;STACK_PAIR_GEN_TAC;TRIV_EXISTS_TAC] THEN NO_TAC) THEN
    TRY (SUBGOAL_THEN `4 * loop_count + loop_remain = nblocks` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN NO_TAC) THEN
    TRY (ASM_REWRITE_TAC[SUB_REFL;VAL_WORD_0] THEN NO_TAC) THEN TRY (CONV_TAC WORD_RULE);
    MONOTONE_MAYCHANGE_CONJ_TAC ];;

let REMLOOP_EQUIV = prove(remloop_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ENSURES2_WHILE_PAUP_TAC `0` `loop_remain:num`
    `pc + 0x62c` `pc + 0x6f8` `pc2 + 0x62c` `pc2 + 0x6f8`
    rem_loopinv_lam `\(i:num) (s:armstate). T` `\(i:num) (s:armstate). T`
    `\(i:num). 51` `\(i:num). 51` `0` `0` `1` `1` `1` `1` THEN
  REPEAT CONJ_TAC THENL [
    (* [0] a < b *)
    ASM_ARITH_TAC;
    (* [1] HPRE: reminv 0 at head, 0-step *)
    MATCH_MP_TAC ENSURES2_TRIVIAL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      REPEAT GEN_TAC THEN MONOTONE_MAYCHANGE_CONJ_TAC;
    (* [2] HLOOP: reminv i -> reminv (i+1), via REMBODY_LEG weakened *)
    REM_HLOOP_LEG_TAC;
    (* [3] HBACKEDGE: the taken cbnz *)
    REM_BACKEDGE_LEG_TAC;
    (* [4] HPOST: the fall-through cbnz to the loop exit *)
    REM_POST_LEG_TAC;
    (* [5][6] step-count arithmetic *)
    REWRITE_TAC[];
    REWRITE_TAC[]
  ]);;

Printf.printf "*** REMLOOP_EQUIV PROVED ***\n";;

(* ========================================================================= *)
(* REDUCE_LAST_EQUIV: the straight-line "reduce_last" drain [0x4b4, 0x628).    *)
(*                                                                           *)
(* This is the segment between the steady 4x loop exit (0x4b4, where          *)
(* MAIN_LOOP_EQUIV lands with the 4x loop invariant at i = loop_count-1) and   *)
(* the 1x remainder loop head (0x628 / 0x62c).  It drains the last 4x GHASH    *)
(* and finishes the last output group, arriving at the remainder-loop entry    *)
(* shape reminv_u 0.                                                          *)
(*                                                                           *)
(* Byte-identical straight-line code (93 instrs), so the same abbrev/rewrite   *)
(* engine with the IDENTITY map.  Its one input ldp (0x4e4, block             *)
(* 4*(loop_count-1), within the 4x region) is digitized from the 4x           *)
(* bignum(8*loop_count); the whole-buffer input (!j<nblocks) is threaded       *)
(* read-only for the remainder-loop entry; the counter X16 = loop_remain is    *)
(* carried concretely from the entry seam (it is untouched through the 4x      *)
(* loop and reduce_last).                                                     *)
(* ------------------------------------------------------------------------- *)

(* entry seam at 0x4b4: the 4x loop invariant at i = loop_count-1 (=          *)
(* MAIN_LOOP_EQUIV's exit), PLUS the concrete counter X16 = loop_remain and    *)
(* the whole-buffer per-128-block shared input (both threaded through).        *)
let rl_whole_input (s1v,s2v) =
  let ad = mk_binop `word_add:int64->int64->int64` `in_b:int64` (mk_comb(`word:num->int64`,`16 * j`)) in
  let a1 = list_mk_icomb "read" [comp128 ad; s1v] and a2 = list_mk_icomb "read" [comp128 ad; s2v] in
  mk_forall(`j:num`, mk_imp(mk_binop `(<):num->num->bool` `j:num` `nblocks:num`, mk_eq(a1,a2)));;

let rl_entry_body (s1v,s2v) =
  list_mk_conj (
    [ loopinv_conj `loop_count - 1` (s1v,s2v);
      mk_eq(mk_read `X16` s1v, `word loop_remain:int64`);
      mk_eq(mk_read `X16` s2v, `word loop_remain:int64`);
      rl_whole_input (s1v,s2v) ]);;

let rl_precond =
  `2 <= loop_count /\
   nblocks = 4 * loop_count + loop_remain /\ loop_remain < 4 /\
   64 * loop_count + 16 * loop_remain < 2 EXP 64 /\
   nonoverlapping (word pc:int64, 1856) (word pc2:int64, 1856) /\
   nonoverlapping (word pc:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc2:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc:int64, 1856) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (word pc2:int64, 1856) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (in_b:int64, 16 * nblocks) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (in_b:int64, 16 * nblocks) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (htab_b:int64, 192) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (htab_b:int64, 192) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (word_add stackpointer (word 160), 64) (out_b:int64, 16 * nblocks) /\
   aligned 16 (stackpointer:int64)`;;

let rl_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`stackpointer:int64`;
   `nblocks:num`;`loop_count:num`;`loop_remain:num`],
  mk_imp(rl_precond,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x4b4)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x4b4)`;
          rl_entry_body (`s1:armstate`,`s2:armstate`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x628)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x628)`;
          reminv_u `0` (`s1:armstate`,`s2:armstate`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_rem,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_rem,[`s2:armstate`;`s2':armstate`]))));
       `\(s:armstate). 93`; `\(s:armstate). 93`]));;

let rl_inst_map = 1--93;;
let rl_pin = [`X0`;`X2`;`X6`;`SP`;`X3`;`X4`;`X1`;`Q5`;`Q6`;`Q17`;`Q31`];;

(* digitize the last-group input block (4*(loop_count-1)) that reduce_last's    *)
(* ldp @0x4e4 reads, from the 4x bignum(8*loop_count).                          *)
let RL_DIGITIZE_TAC : tactic = fun (asl,w) ->
  let bfm_ths = filter (fun (_,th) -> match concl th with
     | Comb(Comb(Const("=",_), Comb(Comb(Const("bignum_from_memory",_),_),_)),_) -> true |_->false) asl in
  (* need any lower bound n <= loop_count with n >= 1 (derive_slot_read's k < 8*loop_count
     side-condition holds for loop_count >= 1); accept 1 <= or 2 <= loop_count.
     NB HOL's `find` raises Failure "find", not Not_found. *)
  let precond_th = try snd(find (fun (_,th) -> concl th = `2 <= loop_count`) asl)
                   with Failure _ ->
                   try snd(find (fun (_,th) -> concl th = `1 <= loop_count`) asl)
                   with Failure _ -> failwith "RL_DIGITIZE_TAC: no 1<=/2<= loop_count" in
  let norm0 = ARITH_RULE `8 * 8 * (loop_count - 1) = 64 * (loop_count - 1)` in
  let norm1 = ARITH_RULE `8 * (8 * (loop_count - 1) + 1) = 64 * (loop_count - 1) + 8` in
  let mk_slot k_tm =
    List.map (fun (_,bfm) -> REWRITE_RULE[norm0; norm1] (derive_slot_read bfm k_tm precond_th)) bfm_ths in
  let derived = (mk_slot `8 * (loop_count - 1)`)
              @ (mk_slot (mk_binop `(+):num->num->num` `8 * (loop_count - 1)` `1`)) in
  MAP_EVERY ASSUME_TAC derived (asl,w);;

let rl_sv_inpf : thm ref = ref TRUTH;;
let rl_sv_accf : thm ref = ref TRUTH;;
let RL_SNAPSHOT_TAC : tactic = fun (asl,w) ->
  rl_sv_inpf := (try snd(find (fun (_,th) -> is_forall(concl th) &&
      let s=string_of_term(concl th) in preamble_contains s "in_b" && preamble_contains s "nblocks") asl) with Not_found->TRUTH);
  rl_sv_accf := (try snd(find (fun (_,th) -> is_forall(concl th) &&
      preamble_contains (string_of_term(concl th)) "out_b") asl) with Not_found->TRUTH);
  ALL_TAC (asl,w);;

(* re-establish the whole-buffer input (read-only) and the OLD accumulating     *)
(* output (blocks < 4*(loop_count-1)) at s93/s93' by forwarding across the       *)
(* accumulated frames.  The four NEW blocks are handled in the closer.          *)
let RL_FWD_TAC : tactic = fun (asl,w) ->
  let asl_thms = map snd asl in
  let fL = find_frame_rb asl "s93" and fR = find_frame_rb asl "s93'" in
  let step frame =
    MP_TAC frame THEN REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN READ_OVER_WRITE_ORTHOGONAL_TAC in
  let inp_goal = `!j. j < nblocks
      ==> read (memory :> bytes128 (word_add in_b (word (16*j)))) s93 =
          read (memory :> bytes128 (word_add in_b (word (16*j)))) s93'` in
  let inpfwd = TAC_PROOF(
    (map (fun t->("",t)) (asl_thms @ [!rl_sv_inpf; fL; fR]), inp_goal),
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_b (word (16*j)))) s93 =
                  read (memory :> bytes128 (word_add in_b (word (16*j)))) s0` SUBST1_TAC THENL
     [step fL; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_b (word (16*j)))) s93' =
                  read (memory :> bytes128 (word_add in_b (word (16*j)))) s0'` SUBST1_TAC THENL
     [step fR; ALL_TAC] THEN ASM_SIMP_TAC[]) in
  let acc_goal = `!j. j < 4*(loop_count-1)
      ==> read (memory :> bytes128 (word_add out_b (word (16*j)))) s93 =
          read (memory :> bytes128 (word_add out_b (word (16*j)))) s93'` in
  let accfwd = TAC_PROOF(
    (map (fun t->("",t)) (asl_thms @ [!rl_sv_accf; fL; fR]), acc_goal),
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `16 * j + 16 <= 64 * (loop_count-1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word_add out_b (word (16*j)):int64,16)
                    (word_add out_b (word (64*(loop_count-1))),64)` ASSUME_TAC THENL
     [NONOVERLAPPING_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add out_b (word (16*j)))) s93 =
                  read (memory :> bytes128 (word_add out_b (word (16*j)))) s0` SUBST1_TAC THENL
     [step fL; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add out_b (word (16*j)))) s93' =
                  read (memory :> bytes128 (word_add out_b (word (16*j)))) s0'` SUBST1_TAC THENL
     [step fR; ALL_TAC] THEN ASM_SIMP_TAC[]) in
  MAP_EVERY ASSUME_TAC [inpfwd; accfwd] (asl,w);;

(* pointer X0/X2 at 64*(loop_count-1)+64 = 64*loop_count. *)
let RL_PTR_TAC : tactic =
  SUBGOAL_THEN `64*(loop_count-1)+64 = 64*loop_count` (fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THENL
   [ASM_ARITH_TAC; CONV_TAC WORD_RULE];;

(* the accumulating output at the exit (!j<4*loop_count): old blocks via the    *)
(* forwarded accfwd, the four newly-written last-group blocks from the surviving *)
(* store facts (both sides unify via the identity instruction map).             *)
let RL_ACCUM_TAC : tactic =
  SUBGOAL_THEN `4 * loop_count = 4*(loop_count-1)+4` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE
    `j < 4*(loop_count-1)+4 <=> j < 4*(loop_count-1) \/ j = 4*(loop_count-1) \/
       j = 4*(loop_count-1)+1 \/ j = 4*(loop_count-1)+2 \/ j = 4*(loop_count-1)+3`] THEN
  REWRITE_TAC[TAUT `(p\/q)==>r <=> (p==>r)/\(q==>r)`; FORALL_AND_THM] THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16*(4*(loop_count-1)) = 64*(loop_count-1)`;
              ARITH_RULE `16*(4*(loop_count-1)+1) = 64*(loop_count-1)+16`;
              ARITH_RULE `16*(4*(loop_count-1)+2) = 64*(loop_count-1)+32`;
              ARITH_RULE `16*(4*(loop_count-1)+3) = 64*(loop_count-1)+48`] THEN
  ASM_REWRITE_TAC[];;

let sta_reduce_last : (int * thm) list ref = ref [];;

let REDUCE_LAST_EQUIV = prove(rl_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  RL_DIGITIZE_TAC THEN RL_SNAPSHOT_TAC THEN
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--93) sta_reduce_last (Some (replicate rl_pin 93)) THEN
  DISCARD_ASSUMPTIONS_TAC (fun th ->
     (is_forall (concl th) && can (find_term (fun t->t=`out_b:int64`)) (concl th))
     || (is_forall (concl th) && can (find_term (fun t->t=`in_b:int64`)) (concl th))
     || can (find_term (fun t->match t with Comb(Const("bignum_from_memory",_),_)->true|_->false)) (concl th)) THEN
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--93) rl_inst_map sta_reduce_last (Some (replicate rl_pin 93)) THEN
  RL_FWD_TAC THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  CONJ_TAC THENL [
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[mk_equiv_regs] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0] THEN REPEAT CONJ_TAC THEN
    TRY (RL_PTR_TAC THEN NO_TAC) THEN                                    (* pointers X0/X2 *)
    TRY (FIRST[EQUIV_EXISTS_TAC;STACK_PAIR_GEN_TAC;TRIV_EXISTS_TAC] THEN NO_TAC) THEN  (* regs/stack/htab *)
    TRY (SUBGOAL_THEN `4 * loop_count + loop_remain = nblocks` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN NO_TAC) THEN          (* whole-buffer input forall *)
    TRY (RL_ACCUM_TAC THEN NO_TAC) THEN                                 (* accumulating output *)
    TRY (FIRST_X_ASSUM(fun t -> if concl t = `read X16 s93 = word loop_remain` then MP_TAC t else NO_TAC) THEN
         FIRST_X_ASSUM(fun t -> let s=string_of_term(concl t) in
           let c s n=let nl=String.length n and hl=String.length s in
             let rec g i=if i+nl>hl then false else if String.sub s i nl=n then true else g(i+1) in g 0 in
           if c s "X16 s93 =" && c s "a''" then MP_TAC t else NO_TAC) THEN MESON_TAC[]) THEN  (* X16 *)
    TRY (ASM_REWRITE_TAC[] THEN NO_TAC);
    MONOTONE_MAYCHANGE_CONJ_TAC ]);;

Printf.printf "*** REDUCE_LAST_EQUIV PROVED ***\n";;

(* ========================================================================= *)
(* POSTAMBLE_EQUIV: the finalize [0x6fc, 0x710).                               *)
(*                                                                           *)
(* The 5-instruction finalize between the remainder-loop exit (0x6fc, where   *)
(* REMLOOP_EQUIV lands with reminv_u loop_remain) and 0x710 (where the deint   *)
(* correctness theorem DEINT_FROM88 ends, before the callee-save epilogue).    *)
(* It does mov x0,x15; rev64 v30; str q30,[x3] (tag writeback); rev w14;       *)
(* str w14,[x4,#12] (ivec counter writeback).                                 *)
(*                                                                           *)
(* Byte-identical, proven with the identity-map engine.  Exit asserts the      *)
(* settled GHASH accumulator Q30 equal (from which the byteswapped tag written *)
(* to tag_p is equal - the tag-in-memory equality is a deterministic          *)
(* consequence, established at composition / _deint-bridge time) and the       *)
(* written ivec counter (bytes32 at ivec_p+12) equal.  X3=tag_p / X4=ivec_p    *)
(* are carried concretely so the two stores' addresses resolve.               *)
(* ------------------------------------------------------------------------- *)

let post_exit_body (s1v,s2v) =
  list_mk_conj [
    mk_eq(list_mk_icomb "read" [`Q30:(armstate,int128)component`; s1v],
          list_mk_icomb "read" [`Q30:(armstate,int128)component`; s2v]);
    mk_eq(list_mk_icomb "read" [`memory :> bytes32 (word_add ivec_p (word 12))`; s1v],
          list_mk_icomb "read" [`memory :> bytes32 (word_add ivec_p (word 12))`; s2v]) ];;

let post_entry_body (s1v,s2v) =
  list_mk_conj [
    reminv_u `loop_remain:num` (s1v,s2v);
    mk_eq(mk_read `X3` s1v, `tag_p:int64`); mk_eq(mk_read `X3` s2v, `tag_p:int64`);
    mk_eq(mk_read `X4` s1v, `ivec_p:int64`); mk_eq(mk_read `X4` s2v, `ivec_p:int64`) ];;

let maych_post =
  list_mk_icomb ",," [
    list_mk_icomb ",," [
      list_mk_icomb ",," [
        mk_icomb(`MAYCHANGE`, mk_list(maych_xregs_rem,`:(armstate,int64)component`));
        mk_icomb(`MAYCHANGE`, mk_list(maych_qregs,`:(armstate,int128)component`))];
      `MAYCHANGE [memory :> bytes (word_add stackpointer (word 160), 64);
                  memory :> bytes (out_b:int64, 16 * nblocks);
                  memory :> bytes (tag_p:int64, 16);
                  memory :> bytes (ivec_p:int64, 16)]`];
    `MAYCHANGE [PC] ,, MAYCHANGE [events] ,, MAYCHANGE [NF;ZF;CF;VF]`];;

let post_precond =
  `nblocks = 4 * loop_count + loop_remain /\ loop_remain < 4 /\
   64 * loop_count + 16 * loop_remain < 2 EXP 64 /\
   nonoverlapping (word pc:int64, 1856) (word pc2:int64, 1856) /\
   nonoverlapping (word pc:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc2:int64, 1856) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (word pc:int64, 1856) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (word pc2:int64, 1856) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (word pc:int64, 1856) (tag_p:int64, 16) /\
   nonoverlapping (word pc2:int64, 1856) (tag_p:int64, 16) /\
   nonoverlapping (word pc:int64, 1856) (ivec_p:int64, 16) /\
   nonoverlapping (word pc2:int64, 1856) (ivec_p:int64, 16) /\
   nonoverlapping (in_b:int64, 16 * nblocks) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (in_b:int64, 16 * nblocks) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (htab_b:int64, 192) (word_add stackpointer (word 160), 64) /\
   nonoverlapping (htab_b:int64, 192) (out_b:int64, 16 * nblocks) /\
   nonoverlapping (word_add stackpointer (word 160), 64) (out_b:int64, 16 * nblocks) /\
   aligned 16 (stackpointer:int64)`;;

let post_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`tag_p:int64`;`ivec_p:int64`;
   `stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`],
  mk_imp(post_precond,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x6fc)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x6fc)`;
          post_entry_body (`s1:armstate`,`s2:armstate`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x710)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x710)`;
          post_exit_body (`s1:armstate`,`s2:armstate`)]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_post,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_post,[`s2:armstate`;`s2':armstate`]))));
       `\(s:armstate). 5`; `\(s:armstate). 5`]));;

let post_inst_map = 1--5;;
let post_pin = [`X0`;`X2`;`X6`;`SP`;`X3`;`X4`;`X16`;`Q5`;`Q6`;`Q17`;`Q31`];;
let sta_postamble : (int * thm) list ref = ref [];;

let POSTAMBLE_EQUIV = prove(post_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--5) sta_postamble (Some (replicate post_pin 5)) THEN
  DISCARD_ASSUMPTIONS_TAC (fun th ->
     (is_forall (concl th) && can (find_term (fun t->t=`out_b:int64`)) (concl th))
     || (is_forall (concl th) && can (find_term (fun t->t=`in_b:int64`)) (concl th))) THEN
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--5) post_inst_map sta_postamble (Some (replicate post_pin 5)) THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  CONJ_TAC THENL [ ASM_REWRITE_TAC[]; MONOTONE_MAYCHANGE_CONJ_TAC ]);;

Printf.printf "*** POSTAMBLE_EQUIV PROVED ***\n";;



(* ===== inlined from swp_equiv_whole.ml ===== *)

(* ========================================================================= *)
(* WHOLE-FUNCTION equivalence  _swp_deint <-> _swp_S.                          *)
(*                                                                           *)
(* Composes the six proven straight-line/loop legs (PREAMBLE, MAIN_LOOP,      *)
(* REDUCE_LAST, the cbz bridge, REMLOOP, POSTAMBLE) into a single ensures2    *)
(* covering the whole body [0x88, 0x710) for the interesting steady-state     *)
(* case 2 <= loop_count and 1 <= loop_remain.                                 *)
(*                                                                           *)
(*   0x88 --PREAMBLE--> 0x1ec --MAIN_LOOP--> 0x4b4 --REDUCE_LAST--> 0x628      *)
(*        --cbz(x16!=0)--> 0x62c --REMLOOP--> 0x6fc --POSTAMBLE--> 0x710       *)
(*                                                                           *)
(* Seam threading (frame-stable facts grafted via ENSURES2_CONJ_FRAME):       *)
(*  - f_x16in (X16=loop_remain both, whole-buffer input equal) onto PREAMBLE  *)
(*    and MAIN so MAIN's post feeds REDUCE_LAST's pre (seam 0x4b4).            *)
(*  - f_ptr (X3=tag_p, X4=ivec_p both) onto REDUCE_LAST and REMLOOP so the    *)
(*    remainder-loop exit feeds POSTAMBLE's pre (seam 0x6fc).                  *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Generic helpers.                                                           *)
(* ------------------------------------------------------------------------- *)

let ens_args g =
  let core = snd(strip_forall g) in
  let core = if is_imp core then snd(dest_imp core) else core in
  snd(strip_comb core);;

(* the relational-frame-preservation goal for ENSURES2_CONJ_FRAME. *)
let frame_preservation_goal legc f =
  let r = List.nth (ens_args legc) 3 in
  let s = `s:armstate` and s2 = `s2:armstate` and sf = `s_final:armstate` and sf2 = `s_final2:armstate` in
  let rapp = list_mk_comb(r,[mk_pair(s,s2); mk_pair(sf,sf2)]) in
  list_mk_forall([s;s2;sf;sf2],
    mk_imp(rapp, mk_eq(list_mk_comb(f,[s;s2]), list_mk_comb(f,[sf;sf2]))));;

(* wrap a leg's ensures2 pre AND post with an extra frame-stable conjunct f. *)
let graft_goal legc f =
  let quants,body = strip_forall legc in
  let ante,concl0 = if is_imp body then dest_imp body else (`T`,body) in
  let ens,args = strip_comb concl0 in
  let step = List.nth args 0 in
  let rest = [List.nth args 3; List.nth args 4; List.nth args 5] in
  let graft p =
    let a,_ = dest_gabs p in
    let s1,s2 = dest_pair a in
    mk_gabs(a, mk_conj(mk_comb(p,a), list_mk_comb(f,[s1;s2]))) in
  let newconcl = list_mk_comb(ens, step::(graft (List.nth args 1))::(graft (List.nth args 2))::rest) in
  list_mk_forall(quants, mk_imp(ante, newconcl));;

(* graft f onto leg_thm via ENSURES2_CONJ_FRAME.  fp_tac proves the frame-preservation
   subgoal (may use ambient hyps for nonoverlaps); leg_tac discharges the leg. *)
let GRAFT_TAC f fp_tac leg_thm : tactic =
  W(fun (asl,w) ->
    let a = ens_args w in
    let step = List.nth a 0 in
    let la = ens_args (concl leg_thm) in
    let bigP = List.nth la 1 and bigQ = List.nth la 2 in
    let r = List.nth a 3 and n1 = List.nth a 4 and n2 = List.nth a 5 in
    let cf = ISPECL [step; bigP; bigQ; r; n1; n2; f] ENSURES2_CONJ_FRAME in
    MP_TAC cf THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [fp_tac;
        MATCH_MP_TAC leg_thm THEN ASM_REWRITE_TAC[]];
      CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN DISCH_THEN ACCEPT_TAC]);;

Printf.printf "*** swp_equiv_whole helpers loaded ***\n";;

(* ------------------------------------------------------------------------- *)
(* The two frame-stable facts and their frame-preservation lemmas.            *)
(* ------------------------------------------------------------------------- *)

(* X3=tag_p, X4=ivec_p on both sides (never in any leg's maychange). *)
let f_ptr = `\(s1:armstate) (s2:armstate).
   read X3 s1 = tag_p /\ read X3 s2 = tag_p /\
   read X4 s1 = ivec_p /\ read X4 s2 = ivec_p`;;

(* X16=loop_remain both, and the whole-buffer input equal (frame-stable in the
   preamble and 4x loop, which never write in_b nor X16). *)
let f_x16in = `\(s1:armstate) (s2:armstate).
   read X16 s1 = word loop_remain /\ read X16 s2 = word loop_remain /\
   (!j. j < nblocks
        ==> read (memory :> bytes128 (word_add in_b (word (16 * j)))) s1 =
            read (memory :> bytes128 (word_add in_b (word (16 * j)))) s2)`;;

(* the single-frame read-preservation micro-step (write-set orthogonal to a read). *)
let step_ro frame =
  MP_TAC frame THEN REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
  PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN READ_OVER_WRITE_ORTHOGONAL_TAC;;

(* frame-preservation of f_ptr (register reads only) over any leg frame. *)
let FP_REGS_TAC (comps:term list) : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN BETA_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT2 th)) THEN
  W(fun (asl,w) ->
    let h1 = snd(el 1 asl) and h2 = snd(el 0 asl) in
    MAP_EVERY (fun c ->
      SUBGOAL_THEN (mk_conj(
          mk_eq(list_mk_icomb "read" [c;`s_final:armstate`], list_mk_icomb "read" [c;`s:armstate`]),
          mk_eq(list_mk_icomb "read" [c;`s_final2:armstate`], list_mk_icomb "read" [c;`s2:armstate`])))
        STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [step_ro h1; step_ro h2]; ALL_TAC]) comps THEN
    ASM_REWRITE_TAC[]);;

(* sanity: f_ptr frame-preservation over the REDUCE/REMLOOP frames (standalone, no hyps). *)
let FP_PTR_REDUCE = prove(frame_preservation_goal (concl REDUCE_LAST_EQUIV) f_ptr,
  FP_REGS_TAC [`X3`; `X4`]);;
let FP_PTR_REMLOOP = prove(frame_preservation_goal (concl REMLOOP_EQUIV) f_ptr,
  FP_REGS_TAC [`X3`; `X4`]);;

Printf.printf "*** FP_PTR lemmas proved ***\n";;

(* frame-preservation of f_x16in over the PREAMBLE / MAIN frame (identical frames).
   Needs the nonoverlap of in_b vs (out_b, 64*loop_count) and stack; supply them via
   the whole-fn precond context at the graft site (the leg's own precond has them). *)
let FP_X16IN_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN BETA_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT2 th)) THEN
  W(fun (asl,w) ->
    let h1 = snd(el 1 asl) and h2 = snd(el 0 asl) in
    SUBGOAL_THEN `read X16 s_final = read X16 s /\ read X16 s_final2 = read X16 s2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [step_ro h1; step_ro h2]; ALL_TAC] THEN
    SUBGOAL_THEN `!j. j < nblocks
        ==> read (memory :> bytes128 (word_add in_b (word (16*j)))) s_final =
            read (memory :> bytes128 (word_add in_b (word (16*j)))) s /\
            read (memory :> bytes128 (word_add in_b (word (16*j)))) s_final2 =
            read (memory :> bytes128 (word_add in_b (word (16*j)))) s2`
      (LABEL_TAC "INP") THENL
     [GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `nonoverlapping (word_add in_b (word (16*j)):int64,16) (out_b:int64,64*loop_count) /\
                    nonoverlapping (word_add in_b (word (16*j)):int64,16)
                       (word_add stackpointer (word 160),64)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [step_ro h1; step_ro h2];
      ALL_TAC] THEN
    EQ_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
    TRY(GEN_TAC THEN DISCH_TAC THEN
        REMOVE_THEN "INP" (MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[]) THEN
    ASM_MESON_TAC[]);;

Printf.printf "*** swp_equiv_whole frame lemmas scaffold loaded ***\n";;

(* ------------------------------------------------------------------------- *)
(* The cbz x16 @ 0x628 bridge (0x628 -> 0x62c), taken only when loop_remain=0. *)
(* Here (1 <= loop_remain) it falls through; REDUCE_LAST.post -> REMLOOP.pre.  *)
(* ------------------------------------------------------------------------- *)

let cbz_rl_post = List.nth (ens_args (concl REDUCE_LAST_EQUIV)) 2;;
let cbz_rem_pre = List.nth (ens_args (concl REMLOOP_EQUIV)) 1;;

let cbz_bridge_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`tag_p:int64`;`ivec_p:int64`;
   `stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`],
  mk_imp(`1 <= loop_remain /\ nblocks = 4 * loop_count + loop_remain /\ loop_remain < 4 /\
          64 * loop_count + 16 * loop_remain < 2 EXP 64`,
    list_mk_icomb "ensures2"
      [`arm`; cbz_rl_post; cbz_rem_pre;
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          `(MAYCHANGE [PC] ,, MAYCHANGE [events]) s1 s1' /\
           (MAYCHANGE [PC] ,, MAYCHANGE [events]) s2 s2'`));
       `\(s:armstate). 1`; `\(s:armstate). 1`]));;

let sta_cbz : (int * thm) list ref = ref [];;
let cbz_pin = [`X0`;`X2`;`X6`;`SP`;`X3`;`X4`;`X16`];;
let cbz_saved : thm list ref = ref [];;
let CBZ_SNAPSHOT_TAC : tactic = fun (asl,w) ->
  cbz_saved := map snd (List.filter (fun (_,th) -> is_forall(concl th)) asl);
  ALL_TAC (asl,w);;
let find_cbz_frame asl sto =
  snd(find (fun (_,th) -> match concl th with
     Comb(Comb(_,sa),sb) when is_var sa && is_var sb && name_of sb=sto -> true |_->false) asl);;
let CBZ_FWD_TAC : tactic = fun (asl,w) ->
  let fL = find_cbz_frame asl "s1" and fR = find_cbz_frame asl "s1'" in
  let fwd saved =
    let jv = `j:num` in
    let bod = snd(dest_forall(concl saved)) in
    let ante,cc = dest_imp bod in
    let l,_ = dest_eq cc in
    let comp = rand(rator l) in
    let goal = mk_forall(jv, mk_imp(ante,
      mk_eq(list_mk_icomb "read" [comp;`s1:armstate`], list_mk_icomb "read" [comp;`s1':armstate`]))) in
    TAC_PROOF((map (fun t->("",t)) (map snd asl @ [saved; fL; fR]), goal),
      GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN (mk_eq(list_mk_icomb "read" [comp;`s1:armstate`], list_mk_icomb "read" [comp;`s0:armstate`]))
        SUBST1_TAC THENL [step_ro fL; ALL_TAC] THEN
      SUBGOAL_THEN (mk_eq(list_mk_icomb "read" [comp;`s1':armstate`], list_mk_icomb "read" [comp;`s0':armstate`]))
        SUBST1_TAC THENL [step_ro fR; ALL_TAC] THEN
      ASM_SIMP_TAC[]) in
  MAP_EVERY ASSUME_TAC (map fwd !cbz_saved) (asl,w);;

let CBZ_BRIDGE = prove(cbz_bridge_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(BETA_RULE) THEN RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  CBZ_SNAPSHOT_TAC THEN
  SUBGOAL_THEN `~(val (word (loop_remain - 0):int64) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[SUB_0] THEN ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT;
      ARITH_RULE `loop_remain < 4 ==> loop_remain < 2 EXP 64`] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--1) sta_cbz (Some (replicate cbz_pin 1)) THEN
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--1) (1--1) sta_cbz (Some (replicate cbz_pin 1)) THEN
  CBZ_FWD_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `nblocks = 4 * loop_count + loop_remain`]) THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ASSUME `nblocks = 4 * loop_count + loop_remain`] THEN
  REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST [EQUIV_EXISTS_TAC; TRIV_EXISTS_TAC] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

Printf.printf "*** CBZ_BRIDGE proved ***\n";;

(* ------------------------------------------------------------------------- *)
(* The whole-function precondition (PREAMBLE's precond plus the two-kernel     *)
(* code-region disjointness needed by the cross abbrev/rewrite legs).          *)
(* ------------------------------------------------------------------------- *)

let whole_precond = `
   [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
    EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
   len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
   16 * nblocks < 2 EXP 64 /\ 2 <= loop_count /\ 1 <= loop_remain /\ aligned 16 stackpointer /\
   nonoverlapping (word pc:int64,1856) (word pc2:int64,1856) /\
   nonoverlapping (out_b:int64,16 * nblocks) (word pc:int64,1856) /\
   nonoverlapping (out_b:int64,16 * nblocks) (word pc2:int64,1856) /\
   nonoverlapping (out_b:int64,16 * nblocks) (in_b:int64,16 * nblocks) /\
   nonoverlapping (out_b:int64,16 * nblocks) (htab_b:int64,192) /\
   nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
   nonoverlapping (tag_p:int64,16) (word pc2:int64,1856) /\
   nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
   nonoverlapping (ivec_p:int64,16) (word pc2:int64,1856) /\
   nonoverlapping (word_add stackpointer (word 160),64) (word pc:int64,1856) /\
   nonoverlapping (word_add stackpointer (word 160),64) (word pc2:int64,1856) /\
   nonoverlapping (word_add stackpointer (word 160),64) (in_b:int64,16 * nblocks) /\
   nonoverlapping (word_add stackpointer (word 160),64) (out_b:int64,16 * nblocks) /\
   nonoverlapping (word_add stackpointer (word 160),64) (htab_b:int64,192) /\
   nonoverlapping (tag_p:int64,16) (in_b:int64,16 * nblocks) /\
   nonoverlapping (tag_p:int64,16) (out_b:int64,16 * nblocks) /\
   nonoverlapping (tag_p:int64,16) (htab_b:int64,192) /\
   nonoverlapping (ivec_p:int64,16) (in_b:int64,16 * nblocks) /\
   nonoverlapping (ivec_p:int64,16) (out_b:int64,16 * nblocks) /\
   nonoverlapping (ivec_p:int64,16) (htab_b:int64,192) /\
   nonoverlapping (tag_p:int64,16) (ivec_p:int64,16)`;;

Printf.printf "*** swp_equiv_whole cbz + precond loaded ***\n";;

(* ------------------------------------------------------------------------- *)
(* Grafted legs.                                                              *)
(*  f_pm  = f_x16in /\ f_ptr   grafted onto PREAMBLE + MAIN (threads X16,      *)
(*          input, X3, X4 from entry through the 4x loop).                     *)
(*  f_ptr grafted onto REDUCE_LAST + CBZ + REMLOOP (threads X3, X4 to the      *)
(*          postamble; X16 no longer invariant past the reduce/remainder).     *)
(* ------------------------------------------------------------------------- *)

let f_pm = `\(s1:armstate) (s2:armstate).
   (read X16 s1 = word loop_remain /\ read X16 s2 = word loop_remain /\
    (!j. j < nblocks
         ==> read (memory :> bytes128 (word_add in_b (word (16 * j)))) s1 =
             read (memory :> bytes128 (word_add in_b (word (16 * j)))) s2)) /\
   read X3 s1 = tag_p /\ read X3 s2 = tag_p /\
   read X4 s1 = ivec_p /\ read X4 s2 = ivec_p`;;

(* frame-preservation of f_pm over the (identical) PREAMBLE / MAIN frame. *)
let FP_PM_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN BETA_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT2 th)) THEN
  W(fun (asl,w) ->
    let h1 = snd(el 1 asl) and h2 = snd(el 0 asl) in
    MAP_EVERY (fun c ->
      SUBGOAL_THEN (mk_conj(
          mk_eq(list_mk_icomb "read" [c;`s_final:armstate`], list_mk_icomb "read" [c;`s:armstate`]),
          mk_eq(list_mk_icomb "read" [c;`s_final2:armstate`], list_mk_icomb "read" [c;`s2:armstate`])))
        STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [step_ro h1; step_ro h2]; ALL_TAC]) [`X16`;`X3`;`X4`] THEN
    SUBGOAL_THEN `!j. j < nblocks
        ==> read (memory :> bytes128 (word_add in_b (word (16*j)))) s_final =
            read (memory :> bytes128 (word_add in_b (word (16*j)))) s /\
            read (memory :> bytes128 (word_add in_b (word (16*j)))) s_final2 =
            read (memory :> bytes128 (word_add in_b (word (16*j)))) s2`
      (LABEL_TAC "INP") THENL
     [GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `nonoverlapping (word_add in_b (word (16*j)):int64,16) (out_b:int64,64*loop_count) /\
                    nonoverlapping (word_add in_b (word (16*j)):int64,16)
                       (word_add stackpointer (word 160),64)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [step_ro h1; step_ro h2];
      ALL_TAC] THEN
    EQ_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
    TRY(GEN_TAC THEN DISCH_TAC THEN
        REMOVE_THEN "INP" (MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[]) THEN
    ASM_MESON_TAC[]);;

let PREAMBLE_G = prove(graft_goal (concl PREAMBLE_EQUIV) f_pm,
  REPEAT STRIP_TAC THEN GRAFT_TAC f_pm FP_PM_TAC PREAMBLE_EQUIV);;

(* MAIN needs the wide (16*nblocks) in/out nonoverlaps (its own precond only knows
   64*loop_count) to preserve the whole-buffer input; carry them as extra precond. *)
let main_gpm_goal =
  let q,b = strip_forall (concl MAIN_LOOP_EQUIV) in
  let pre = fst(dest_imp b) in
  let extra = `nblocks = 4 * loop_count + loop_remain /\ 16 * nblocks < 2 EXP 64 /\
               nonoverlapping (in_b:int64,16 * nblocks) (out_b:int64,16 * nblocks) /\
               nonoverlapping (word_add stackpointer (word 160),64) (in_b:int64,16*nblocks)` in
  let gg = graft_goal (concl MAIN_LOOP_EQUIV) f_pm in
  let q2,_ = strip_forall gg in
  let _,cc = dest_imp (snd(strip_forall gg)) in
  list_mk_forall(union q2 [`nblocks:num`;`loop_remain:num`;`tag_p:int64`;`ivec_p:int64`],
    mk_imp(mk_conj(pre,extra), cc));;
let MAIN_G = prove(main_gpm_goal,
  REPEAT STRIP_TAC THEN GRAFT_TAC f_pm FP_PM_TAC MAIN_LOOP_EQUIV);;

let REDUCE_G = prove(graft_goal (concl REDUCE_LAST_EQUIV) f_ptr,
  REPEAT STRIP_TAC THEN GRAFT_TAC f_ptr (FP_REGS_TAC [`X3`;`X4`]) REDUCE_LAST_EQUIV);;
let CBZ_G = prove(graft_goal (concl CBZ_BRIDGE) f_ptr,
  REPEAT STRIP_TAC THEN GRAFT_TAC f_ptr (FP_REGS_TAC [`X3`;`X4`]) CBZ_BRIDGE);;
let REMLOOP_G = prove(graft_goal (concl REMLOOP_EQUIV) f_ptr,
  REPEAT STRIP_TAC THEN GRAFT_TAC f_ptr (FP_REGS_TAC [`X3`;`X4`]) REMLOOP_EQUIV);;

Printf.printf "*** swp_equiv_whole grafted legs proved ***\n";;

(* ------------------------------------------------------------------------- *)
(* The two weakening implications for the non-exact seams (0x4b4, 0x6fc).      *)
(* ------------------------------------------------------------------------- *)

let post_of th = List.nth (ens_args (concl th)) 2;;
let pre_of th = List.nth (ens_args (concl th)) 1;;
let mk_weaken post pre =
  let sp = `(s:armstate,s':armstate)` in
  mk_forall(`s:armstate`, mk_forall(`s':armstate`, mk_imp(mk_comb(post,sp), mk_comb(pre,sp))));;
let WEAKEN_TAC =
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MESON_TAC[];;

let WEAKEN_MAIN_REDUCE = prove(mk_weaken (post_of MAIN_G) (pre_of REDUCE_G), WEAKEN_TAC);;
let WEAKEN_REMLOOP_POST = prove(mk_weaken (post_of REMLOOP_G) (pre_of POSTAMBLE_EQUIV), WEAKEN_TAC);;

Printf.printf "*** swp_equiv_whole weakening lemmas proved ***\n";;

(* ------------------------------------------------------------------------- *)
(* Compose.  Each leg is instantiated (SPEC_ALL) and its precond UNDISCHed, so *)
(* the composite carries the (per-leg) preconds as hypotheses; they are all    *)
(* discharged from whole_precond at the very end.                              *)
(* ------------------------------------------------------------------------- *)

(* exact-seam transitivity: ensures2 P Q C n1 , ensures2 Q R C' n2 -> ensures2 P R (C,,C') ... *)
let trans_exact th1 th2 = MATCH_MP ENSURES2_TRANS (CONJ th1 th2);;

(* weakening-seam transitivity via ENSURES2_TRANS_GEN with C'' = C ,, C' (SUBSUMED_REFL). *)
let trans_weaken th1 wk th2 =
  let c1 = concl th1 and c2 = concl th2 in
  let frame1 = List.nth (ens_args c1) 3 and frame2 = List.nth (ens_args c2) 3 in
  let cpp = mk_icomb(mk_icomb(`(,,)`,frame1),frame2) in
  let subsumed_th = ISPEC cpp SUBSUMED_REFL in
  MATCH_MP ENSURES2_TRANS_GEN (end_itlist CONJ [th1; th2; wk; subsumed_th]);;

(* the fully-composed theorem, carrying the six per-leg preconds as hypotheses. *)
let composed_equiv =
  let pg = UNDISCH (SPEC_ALL PREAMBLE_G) in
  let mg = UNDISCH (SPEC_ALL MAIN_G) in
  let rg = UNDISCH (SPEC_ALL REDUCE_G) in
  let cg = UNDISCH (SPEC_ALL CBZ_G) in
  let lg = UNDISCH (SPEC_ALL REMLOOP_G) in
  let pog = UNDISCH (SPEC_ALL POSTAMBLE_EQUIV) in
  let c1 = trans_exact pg mg in                       (* 0x88  -> 0x4b4 *)
  let c2 = trans_weaken c1 WEAKEN_MAIN_REDUCE rg in    (*       -> 0x628 *)
  let c3 = trans_exact c2 cg in                        (*       -> 0x62c *)
  let c4 = trans_exact c3 lg in                        (*       -> 0x6fc *)
  trans_weaken c4 WEAKEN_REMLOOP_POST pog;;            (*       -> 0x710 *)

Printf.printf "*** composed_equiv built (%d hyps) ***\n" (length(hyp composed_equiv));;

(* discharge each per-leg precond hypothesis from whole_precond. *)
let DISCHARGE_ONE wp h =
  prove(mk_imp(whole_precond, h),
    STRIP_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN TRY(ASM_ARITH_TAC) THEN
    TRY(NONOVERLAPPING_TAC) THEN
    TRY(MP_TAC(ASSUME `16 * nblocks < 2 EXP 64`) THEN
        MP_TAC(ASSUME `nblocks DIV 4 = loop_count`) THEN ARITH_TAC));;

let SWP_DEINT_SWPS_EQUIV_STEADY =
  let quants =
    [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`tag_p:int64`;`ivec_p:int64`;
     `stackpointer:int64`;`len_bits:num`;`nblocks:num`;`loop_count:num`;`loop_remain:num`;
     `tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`] in
  let wp = ASSUME whole_precond in
  (* remove every hypothesis by proving it under whole_precond *)
  let discharged =
    itlist (fun h th -> PROVE_HYP (MP (DISCHARGE_ONE wp h) wp) th)
           (hyp composed_equiv) composed_equiv in
  GENL quants (DISCH whole_precond discharged);;

Printf.printf "*** SWP_DEINT_SWPS_EQUIV_STEADY proved (hyps=%d) ***\n"
  (length(hyp SWP_DEINT_SWPS_EQUIV_STEADY));;

(* ------------------------------------------------------------------------- *)
(* SWP_DEINT_SWPS_EQUIV_STEADY :                                              *)
(*                                                                           *)
(*   for all the standard parameters, under the whole-function precondition   *)
(*   (the deint nonoverlap/alignment hypotheses PLUS the two-kernel code       *)
(*   disjointness  nonoverlapping (word pc,1856) (word pc2,1856),  and the     *)
(*   steady-state guards  2 <= loop_count /\ 1 <= loop_remain):                *)
(*                                                                           *)
(*     ensures2 arm                                                           *)
(*       (\ (s1,s2). <entry 0x88 relation: entry88 on the deint side (s1) and  *)
(*                    the swpS side (s2), the loop-carried registers agreeing, *)
(*                    the shared whole-buffer input, X16=loop_remain, X3=tag_p,*)
(*                    X4=ivec_p>)                                              *)
(*       (\ (s1,s2). read PC s1 = word (pc + 0x710) /\                         *)
(*                    read PC s2 = word (pc2 + 0x710) /\                       *)
(*                    read Q30 s1 = read Q30 s2 /\                             *)
(*                    read (memory :> bytes32 (word_add ivec_p (word 12))) s1 =*)
(*                    read (memory :> bytes32 (word_add ivec_p (word 12))) s2) *)
(*       (relational MAYCHANGE frame) (n1) (n2)                               *)
(*                                                                           *)
(* i.e. the deint and swpS kernels run in lockstep from the shared entry at    *)
(* 0x88 to the shared exit at 0x710, agreeing on the GHASH accumulator Q30 and *)
(* the counter tail.  Composing this (LEFT = deint) with the deint functional  *)
(* spec DEINT_FROM88 transfers deint's correctness to the swpS schedule.       *)
(*                                                                           *)
(* The companion theorem SWP_DEINT_SWPS_EQUIV_REM0 below covers loop_remain = 0  *)
(* (the cbz at 0x628 is taken, skipping the remainder loop).  Together they      *)
(* cover every loop_remain (< 4).  Still open: loop_count < 2 (the deint         *)
(* correctness proof dispatches those degenerate cases internally).             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The loop_remain = 0 case.                                                   *)
(*   0x88 --PREAMBLE--> 0x1ec --MAIN--> 0x4b4 --REDUCE_LAST--> 0x628            *)
(*        --cbz(x16=0, TAKEN)--> 0x6fc --POSTAMBLE--> 0x710                     *)
(* (the remainder loop [0x62c,0x6fc) is skipped).                              *)
(* ------------------------------------------------------------------------- *)

(* the cbz x16 @ 0x628 TAKEN bridge (0x628 -> 0x6fc): REDUCE_LAST.post[lr:=0]    *)
(* to the same relation at 0x6fc.  X3/X4 stay in mk_equiv_regs; the concrete     *)
(* tag_p/ivec_p for the postamble entry come from the f_ptr graft at compose.    *)
let cbzt_rl_post0 = subst [`0`,`loop_remain:num`] (List.nth (ens_args (concl REDUCE_LAST_EQUIV)) 2);;
let cbzt_post_pre0 = subst [`pc + 1788`,`pc + 1576`; `pc2 + 1788`,`pc2 + 1576`] cbzt_rl_post0;;

let cbzt_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`tag_p:int64`;`ivec_p:int64`;
   `stackpointer:int64`;`nblocks:num`;`loop_count:num`],
  mk_imp(`nblocks = 4 * loop_count + 0 /\ 64 * loop_count + 16 * 0 < 2 EXP 64`,
    list_mk_icomb "ensures2"
      [`arm`; cbzt_rl_post0; cbzt_post_pre0;
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          `(MAYCHANGE [PC] ,, MAYCHANGE [events]) s1 s1' /\
           (MAYCHANGE [PC] ,, MAYCHANGE [events]) s2 s2'`));
       `\(s:armstate). 1`; `\(s:armstate). 1`]));;

let sta_cbzt : (int * thm) list ref = ref [];;
let cbzt_saved : thm list ref = ref [];;
let CBZT_SNAPSHOT_TAC : tactic = fun (asl,w) ->
  cbzt_saved := map snd (List.filter (fun (_,th) -> is_forall(concl th)) asl);
  ALL_TAC (asl,w);;
let CBZT_FWD_TAC : tactic = fun (asl,w) ->
  let fL = find_cbz_frame asl "s1" and fR = find_cbz_frame asl "s1'" in
  let fwd saved =
    let jv = `j:num` in
    let bod = snd(dest_forall(concl saved)) in
    let ante,cc = dest_imp bod in
    let l,_ = dest_eq cc in
    let comp = rand(rator l) in
    let goal = mk_forall(jv, mk_imp(ante,
      mk_eq(list_mk_icomb "read" [comp;`s1:armstate`], list_mk_icomb "read" [comp;`s1':armstate`]))) in
    TAC_PROOF((map (fun t->("",t)) (map snd asl @ [saved; fL; fR]), goal),
      GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN (mk_eq(list_mk_icomb "read" [comp;`s1:armstate`], list_mk_icomb "read" [comp;`s0:armstate`]))
        SUBST1_TAC THENL [step_ro fL; ALL_TAC] THEN
      SUBGOAL_THEN (mk_eq(list_mk_icomb "read" [comp;`s1':armstate`], list_mk_icomb "read" [comp;`s0':armstate`]))
        SUBST1_TAC THENL [step_ro fR; ALL_TAC] THEN
      ASM_SIMP_TAC[]) in
  MAP_EVERY ASSUME_TAC (map fwd !cbzt_saved) (asl,w);;

let CBZ_TAKEN_BRIDGE = prove(cbzt_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(BETA_RULE) THEN RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  CBZT_SNAPSHOT_TAC THEN
  SUBGOAL_THEN `val (word (0 - 0):int64) = 0` ASSUME_TAC THENL
   [REWRITE_TAC[SUB_0] THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--1) sta_cbzt (Some (replicate cbz_pin 1)) THEN
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--1) (1--1) sta_cbzt (Some (replicate cbz_pin 1)) THEN
  CBZT_FWD_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `nblocks = 4 * loop_count + 0`]) THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ASSUME `nblocks = 4 * loop_count + 0`] THEN
  REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST [EQUIV_EXISTS_TAC; TRIV_EXISTS_TAC] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[SUB_0] THEN NO_TAC));;

Printf.printf "*** CBZ_TAKEN_BRIDGE proved ***\n";;

let CBZ_TAKEN_G = prove(graft_goal (concl CBZ_TAKEN_BRIDGE) f_ptr,
  REPEAT STRIP_TAC THEN GRAFT_TAC f_ptr (FP_REGS_TAC [`X3`;`X4`]) CBZ_TAKEN_BRIDGE);;

(* the loop_remain = 0 whole-function precondition (drop "1 <= loop_remain",     *)
(* set loop_remain := 0 everywhere; MOD gives loop_remain = 0).                  *)
let whole_precond_rem0 = subst [`0`,`loop_remain:num`]
  (list_mk_conj (filter (fun t -> t <> `1 <= loop_remain`) (conjuncts whole_precond)));;

(* discharge a REM0 leg precond hypothesis from whole_precond_rem0. *)
let DISCHARGE_ONE_REM0 wp h =
  prove(mk_imp(whole_precond_rem0, h),
    STRIP_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN TRY(ASM_ARITH_TAC) THEN
    TRY(NONOVERLAPPING_TAC) THEN
    TRY(MP_TAC(ASSUME `16 * nblocks < 2 EXP 64`) THEN
        MP_TAC(ASSUME `nblocks DIV 4 = loop_count`) THEN ARITH_TAC));;

let SWP_DEINT_SWPS_EQUIV_REM0 =
  let quants =
    [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`tag_p:int64`;`ivec_p:int64`;
     `stackpointer:int64`;`len_bits:num`;`nblocks:num`;`loop_count:num`;
     `tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`] in
  let inst0 th = INST [`0`,`loop_remain:num`] (SPEC_ALL th) in
  let pg0 = UNDISCH (inst0 PREAMBLE_G) in
  let mg0 = UNDISCH (inst0 MAIN_G) in
  let rg0 = UNDISCH (inst0 REDUCE_G) in
  let ctg0 = UNDISCH (SPEC_ALL CBZ_TAKEN_G) in
  let pog0 = UNDISCH (inst0 POSTAMBLE_EQUIV) in
  let po th = List.nth (ens_args (concl th)) 2 and pr th = List.nth (ens_args (concl th)) 1 in
  let wk_mr0 = prove(mk_weaken (po mg0) (pr rg0), WEAKEN_TAC) in
  let wk_cp0 = prove(mk_weaken (po ctg0) (pr pog0), WEAKEN_TAC) in
  let c1 = trans_exact pg0 mg0 in
  let c2 = trans_weaken c1 wk_mr0 rg0 in
  let c3 = trans_exact c2 ctg0 in
  let composed0 = trans_weaken c3 wk_cp0 pog0 in
  let wp = ASSUME whole_precond_rem0 in
  let discharged =
    itlist (fun h th -> PROVE_HYP (MP (DISCHARGE_ONE_REM0 wp h) wp) th)
           (hyp composed0) composed0 in
  GENL quants (DISCH whole_precond_rem0 discharged);;

Printf.printf "*** SWP_DEINT_SWPS_EQUIV_REM0 proved (hyps=%d) ***\n"
  (length(hyp SWP_DEINT_SWPS_EQUIV_REM0));;

(* ------------------------------------------------------------------------- *)
(* SUMMARY.  Two theorems together give the whole-body equivalence for every   *)
(* remainder count loop_remain < 4 (with 2 <= loop_count):                     *)
(*                                                                           *)
(*   SWP_DEINT_SWPS_EQUIV_STEADY : 1 <= loop_remain  (runs the remainder loop) *)
(*   SWP_DEINT_SWPS_EQUIV_REM0   : loop_remain = 0    (cbz taken, loop skipped) *)
(*                                                                           *)
(* Both are ensures2 from the shared entry 0x88 to the shared exit 0x710,      *)
(* axiom-free, agreeing on the GHASH accumulator Q30 and the counter tail at   *)
(* the exit.  Composing either (LEFT = deint) with the deint functional spec   *)
(* DEINT_FROM88 transfers deint's correctness to the swpS schedule; the caller *)
(* case-splits on nblocks MOD 4 = 0 to pick the branch.                        *)
(* ------------------------------------------------------------------------- *)



(* ===== inlined from swp_equiv_degenerate.ml ===== *)

(* ========================================================================= *)
(* DEGENERATE loop_count cases of the _swp_deint <-> _swp_S equivalence.       *)
(*                                                                           *)
(* swp_equiv_whole.ml proves the two steady-state theorems (2 <= loop_count): *)
(*   SWP_DEINT_SWPS_EQUIV_STEADY : 2 <= loop_count /\ 1 <= loop_remain         *)
(*   SWP_DEINT_SWPS_EQUIV_REM0   : 2 <= loop_count /\ loop_remain = 0          *)
(* This file dispatches the two remaining head counts loop_count = 0 and       *)
(* loop_count = 1, each split on loop_remain, giving four more axiom-free       *)
(* theorems.  Together the six cover EVERY loop_count and EVERY loop_remain<4.  *)
(*                                                                           *)
(*   loop_count = 0 : cbz x1,0x61c @0x88 TAKEN; 0x88 -> 0x628 lockstep         *)
(*                    (HEAD_LC0), then the shared tail from 0x628.             *)
(*   loop_count = 1 : cbz @0x88 falls through, group-0 producer runs, then     *)
(*                    cbz x1,0x4b4 @0x1e8 TAKEN (X1 counts down to 0);          *)
(*                    0x88 -> 0x4b4 (HEAD_LC1_A) ++ REDUCE_LAST_GEN -> 0x628,   *)
(*                    then the shared tail from 0x628.                         *)
(*                                                                           *)
(* The tail legs from 0x628 (CBZ_BRIDGE, CBZ_TAKEN_BRIDGE, REMLOOP_EQUIV,       *)
(* POSTAMBLE_EQUIV and their f_ptr grafts) carry NO loop_count lower bound, so  *)
(* they are reused verbatim; the head's post at 0x628 is (by construction)      *)
(* exactly REDUCE_LAST_EQUIV's post, so the STEADY-tail plumbing applies.       *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* REDUCE_LAST generalized to 1 <= loop_count.                                *)
(*                                                                           *)
(* REDUCE_LAST_EQUIV was stated with 2 <= loop_count, but its proof only uses  *)
(* the bound to (a) prove the pointer identity 64*(loop_count-1)+64 =          *)
(* 64*loop_count (holds for loop_count >= 1) and (b) discharge the             *)
(* derive_slot_read side-condition k < 8*loop_count for k = 8*(loop_count-1),  *)
(* 8*(loop_count-1)+1 (holds for loop_count >= 1).  RL_DIGITIZE_TAC in          *)
(* swp_equiv_tail.ml already accepts a 1 <= loop_count precond.  So re-running  *)
(* the identical proof against the weakened goal succeeds.                     *)
(* ------------------------------------------------------------------------- *)

let rl_goal_gen =
  let q,b = strip_forall (concl REDUCE_LAST_EQUIV) in
  let ante,cc = dest_imp b in
  let ante' = list_mk_conj
    (map (fun t -> if t = `2 <= loop_count` then `1 <= loop_count` else t) (conjuncts ante)) in
  list_mk_forall(q, mk_imp(ante', cc));;

let sta_rl_gen : (int*thm) list ref = ref [];;

let REDUCE_LAST_GEN = prove(rl_goal_gen,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  RL_DIGITIZE_TAC THEN RL_SNAPSHOT_TAC THEN
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--93) sta_rl_gen (Some (replicate rl_pin 93)) THEN
  DISCARD_ASSUMPTIONS_TAC (fun th ->
     (is_forall (concl th) && can (find_term (fun t->t=`out_b:int64`)) (concl th))
     || (is_forall (concl th) && can (find_term (fun t->t=`in_b:int64`)) (concl th))
     || can (find_term (fun t->match t with Comb(Const("bignum_from_memory",_),_)->true|_->false)) (concl th)) THEN
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--93) rl_inst_map sta_rl_gen (Some (replicate rl_pin 93)) THEN
  RL_FWD_TAC THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  CONJ_TAC THENL [
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[mk_equiv_regs] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0] THEN REPEAT CONJ_TAC THEN
    TRY (RL_PTR_TAC THEN NO_TAC) THEN
    TRY (FIRST[EQUIV_EXISTS_TAC;STACK_PAIR_GEN_TAC;TRIV_EXISTS_TAC] THEN NO_TAC) THEN
    TRY (SUBGOAL_THEN `4 * loop_count + loop_remain = nblocks` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN NO_TAC) THEN
    TRY (RL_ACCUM_TAC THEN NO_TAC) THEN
    TRY (FIRST_X_ASSUM(fun t -> if concl t = `read X16 s93 = word loop_remain` then MP_TAC t else NO_TAC) THEN
         FIRST_X_ASSUM(fun t -> let s=string_of_term(concl t) in
           let c s n=let nl=String.length n and hl=String.length s in
             let rec g i=if i+nl>hl then false else if String.sub s i nl=n then true else g(i+1) in g 0 in
           if c s "X16 s93 =" && c s "a''" then MP_TAC t else NO_TAC) THEN MESON_TAC[]) THEN
    TRY (ASM_REWRITE_TAC[] THEN NO_TAC);
    MONOTONE_MAYCHANGE_CONJ_TAC ]);;

Printf.printf "*** REDUCE_LAST_GEN proved (1 <= loop_count) ***\n";;

(* ------------------------------------------------------------------------- *)
(* HEAD_LC0 : loop_count = 0, entry 0x88 -> 0x628, byte-identical lockstep.    *)
(* cbz x1,0x61c @0x88 is TAKEN (X1 = word loop_count = word 0), the group-0     *)
(* loop is skipped entirely, and 4 stack-slot exists facts thread through.     *)
(* Target = REDUCE_LAST_EQUIV's post with loop_count := 0.                     *)
(* ------------------------------------------------------------------------- *)

(* memory :> bytes128 a  (built with the full (:>) type; mk_icomb is ill-typed). *)
let mk_bytes128_at a =
  mk_binop `(:>):(armstate,(64)word->(8)word)component ->
                 ((64)word->(8)word,int128)component -> (armstate,int128)component`
    `memory` (mk_comb(`bytes128`,a));;

let head_lc0_goal =
  let heb = List.nth (ens_args (concl PREAMBLE_EQUIV)) 1 in
  let stack_eq off =
    let a = subst [mk_small_numeral off, `off:num`] `word_add stackpointer (word off):int64` in
    let rd s = list_mk_icomb "read" [mk_bytes128_at a; s] in
    mk_exists(`v:int128`, mk_conj(mk_eq(rd `s1:armstate`,`v:int128`), mk_eq(rd `s2:armstate`,`v:int128`))) in
  let he = let a,body = dest_gabs heb in mk_gabs(a, list_mk_conj (body :: map stack_eq [160;176;192;208])) in
  let heb0 = subst [`0`,`loop_count:num`] he in
  let hp0 = subst [`0`,`loop_count:num`] (List.nth (ens_args (concl REDUCE_LAST_EQUIV)) 2) in
  let pre_conjs = filter (fun t -> t <> `2 <= loop_count`)
                    (conjuncts (fst(dest_imp(snd(strip_forall(concl PREAMBLE_EQUIV)))))) in
  let prec0 = subst [`0`,`loop_count:num`]
     (list_mk_conj (`nonoverlapping (word pc:int64,1856) (word pc2:int64,1856)` :: pre_conjs)) in
  list_mk_forall(
    [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`tag_p:int64`;`ivec_p:int64`;
     `stackpointer:int64`;`len_bits:num`;`nblocks:num`;`loop_remain:num`;
     `tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`],
    mk_imp(prec0,
      list_mk_icomb "ensures2"
        [`arm`; heb0; hp0;
         mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
            mk_conj(list_mk_comb(maych_loop,[`s1:armstate`;`s1':armstate`]),
                    list_mk_comb(maych_loop,[`s2:armstate`;`s2':armstate`]))));
         `\(s:armstate). 4`; `\(s:armstate). 4`]));;

let sta_h0 : (int * thm) list ref = ref [];;
let h0_pin = [`X0`;`X2`;`X6`;`SP`;`X3`;`X4`;`X16`];;
let step_ro_h0 frame =
    MP_TAC frame THEN REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN READ_OVER_WRITE_ORTHOGONAL_TAC;;
let find_h0_frame asl sto =
  snd(find (fun (_,th) -> match concl th with
     Comb(Comb(_,sa),sb) when is_var sa && is_var sb && name_of sb=sto
       && (name_of sa = "s0" || name_of sa = "s0'") -> true |_->false) asl);;
let H0_STACK_TAC : tactic = fun (asl,w) ->
  let _,body = dest_exists w in let c1,_ = dest_conj body in
  (EXISTS_TAC (lhs c1) THEN ASM_REWRITE_TAC[]) (asl,w);;

(* snapshot the entry input-foralls at INIT (the abbrev engine drops them). *)
let h0_saved : thm list ref = ref [];;
let H0_SNAPSHOT_TAC : tactic = fun (asl,w) ->
  h0_saved := map snd (List.filter (fun (_,th) -> is_forall(concl th)) asl);
  ALL_TAC (asl,w);;

(* forward the input-forall s0->s4 across the PC/events/Q12-14 frame (no in_b write). *)
let H0_FWD_TAC : tactic = fun (asl,w) ->
  let fL = find_h0_frame asl "s4" and fR = find_h0_frame asl "s4'" in
  let comp_in = `memory :> bytes128 (word_add in_b (word (16 * j)))` in
  let inp_goal = `!j. j < nblocks
      ==> read (memory :> bytes128 (word_add in_b (word (16*j)))) s4 =
          read (memory :> bytes128 (word_add in_b (word (16*j)))) s4'` in
  let inp_fwd = TAC_PROOF((map (fun t->("",t)) (map snd asl @ !h0_saved @ [fL; fR]), inp_goal),
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (mk_eq(list_mk_icomb "read" [comp_in;`s4:armstate`], list_mk_icomb "read" [comp_in;`s0:armstate`]))
      SUBST1_TAC THENL [step_ro_h0 fL; ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(list_mk_icomb "read" [comp_in;`s4':armstate`], list_mk_icomb "read" [comp_in;`s0':armstate`]))
      SUBST1_TAC THENL [step_ro_h0 fR; ALL_TAC] THEN
    ASM_SIMP_TAC[]) in
  ASSUME_TAC inp_fwd (asl,w);;

let HEAD_LC0 = prove(head_lc0_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(BETA_RULE) THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4; mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  H0_SNAPSHOT_TAC THEN
  SUBGOAL_THEN `val (word 0:int64) = 0` ASSUME_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--4) sta_h0 (Some (replicate h0_pin 4)) THEN
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--4) (1--4) sta_h0 (Some (replicate h0_pin 4)) THEN
  H0_FWD_TAC THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* KEEP the frame conjunction intact for MONOTONE_MAYCHANGE_CONJ_TAC. *)
  CONJ_TAC THENL [
    REWRITE_TAC[mk_equiv_regs] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
    TRY(EQUIV_EXISTS_TAC THEN NO_TAC) THEN TRY(H0_STACK_TAC THEN NO_TAC) THEN
    TRY(TRIV_EXISTS_TAC THEN NO_TAC) THEN
    TRY(REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; ARITH_RULE `~(j < 0)`] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    ASM_REWRITE_TAC[];
    MONOTONE_MAYCHANGE_CONJ_TAC ]);;

Printf.printf "*** HEAD_LC0 proved ***\n";;

(* ------------------------------------------------------------------------- *)
(* HEAD_LC1_A : loop_count = 1, entry 0x88 -> 0x4b4.                           *)
(* cbz @0x88 falls through (X1 = word 1, val != 0), the group-0 producer runs  *)
(* (89 byte-identical steps, IDENTITY inst_map like PREAMBLE), then cbz        *)
(* x1,0x4b4 @0x1e8 is TAKEN (X1 counts down to word 0).  Lands at REDUCE_LAST's *)
(* pre (symbolic loop_count; here loop_count = 1).                             *)
(* ------------------------------------------------------------------------- *)

let preamble_pre = List.nth (ens_args (concl PREAMBLE_EQUIV)) 1;;
let preamble_frame = List.nth (ens_args (concl PREAMBLE_EQUIV)) 3;;

let head_lc1a_goal =
  let pre_conjs = map (fun t -> if t = `2 <= loop_count` then `loop_count = 1` else t)
                    (conjuncts (fst(dest_imp(snd(strip_forall(concl PREAMBLE_EQUIV)))))) in
  let prec = list_mk_conj pre_conjs in
  let q,_ = strip_forall (concl PREAMBLE_EQUIV) in
  let tgt = List.nth (ens_args (concl REDUCE_LAST_EQUIV)) 1 in
  list_mk_forall(q,
    mk_imp(prec,
      list_mk_icomb "ensures2"
        [`arm`; preamble_pre; tgt; preamble_frame; `\(s:armstate). 89`; `\(s:armstate). 89`]));;

(* digitize k=0..7 (loop_count = 1 => the input bignum is 8*loop_count = 8 digits). *)
let HEAD_DIGITIZE_TAC : tactic = fun (asl,w) ->
  let bfm_ths = filter (fun (_,th) -> match concl th with
     | Comb(Comb(Const("=",_), Comb(Comb(Const("bignum_from_memory",_),_),_)),_) -> true |_->false) asl in
  let precond_th = try snd(find (fun (_,th) -> concl th = `2 <= loop_count`) asl)
                   with Failure _ ->
                   (try snd(find (fun (_,th) -> concl th = `1 <= loop_count`) asl)
                    with Failure _ ->
                    (try snd(find (fun (_,th) -> concl th = `loop_count = 1`) asl)
                     with Failure _ -> failwith "HEAD_DIGITIZE_TAC: no loop_count bound")) in
  let derived = List.concat (map (fun (_,bfm_th) ->
      map (fun k -> CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)
                      (derive_slot_read bfm_th (mk_small_numeral k) precond_th)) (0--7)) bfm_ths) in
  MAP_EVERY ASSUME_TAC derived (asl,w);;

(* snapshot the entry input-foralls; forward s0 -> s89 across the accumulated frame. *)
let h1a_saved : thm list ref = ref [];;
let H1A_SNAPSHOT_TAC : tactic = fun (asl,w) ->
  h1a_saved := map snd (List.filter (fun (_,th) -> is_forall(concl th) &&
     preamble_contains (string_of_term(concl th)) "in_b") asl);
  ALL_TAC (asl,w);;
let find_h1a_frame asl sto = snd(find (fun (_,th) -> match concl th with
     Comb(Comb(_,sa),sb) when is_var sa && is_var sb && name_of sb=sto
       && (name_of sa="s0"||name_of sa="s0'") -> true |_->false) asl);;
let H1A_FWD_TAC : tactic = fun (asl,w) ->
  let fL = find_h1a_frame asl "s89" and fR = find_h1a_frame asl "s89'" in
  let step_ro frame =
    MP_TAC frame THEN REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN READ_OVER_WRITE_ORTHOGONAL_TAC in
  let comp = `memory :> bytes128 (word_add in_b (word (16 * j)))` in
  let inp_goal = `!j. j < nblocks ==>
     read (memory :> bytes128 (word_add in_b (word (16*j)))) s89 =
     read (memory :> bytes128 (word_add in_b (word (16*j)))) s89'` in
  let inp_fwd = TAC_PROOF((map (fun t->("",t)) (map snd asl @ !h1a_saved @ [fL;fR]), inp_goal),
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (mk_eq(list_mk_icomb "read" [comp;`s89:armstate`], list_mk_icomb "read" [comp;`s0:armstate`]))
      SUBST1_TAC THENL [step_ro fL; ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(list_mk_icomb "read" [comp;`s89':armstate`], list_mk_icomb "read" [comp;`s0':armstate`]))
      SUBST1_TAC THENL [step_ro fR; ALL_TAC] THEN
    ASM_SIMP_TAC[]) in
  ASSUME_TAC inp_fwd (asl,w);;

(* X16 closer: goal `a = word loop_remain` with hyps `read X16 s89 = a` and
   `read X16 s89 = word loop_remain`; rewrite a <- read X16 s89 then accept. *)
let H1A_X16_TAC : tactic = fun (asl,w) ->
  let l = lhs w in
  let h_abb = snd(find (fun (_,th) -> is_eq(concl th) && rhs(concl th) = l &&
     (match lhs(concl th) with Comb(Comb(Const("read",_),Const("X16",_)),_)->true|_->false)) asl) in
  (ONCE_REWRITE_TAC[SYM h_abb] THEN FIRST_ASSUM ACCEPT_TAC) (asl,w);;

(* bignum closer: goal `?a. bignum(in_b,8) s89 = a /\ ... s89' = a`.  The goal's
   size printed as literal 8 (8*loop_count reduced), but the forwarded fact is
   bignum(in_b, 8*loop_count); bridge with 8 = 8*loop_count (loop_count = 1). *)
let SUPPLY_BIGNUM_WITNESS : tactic = fun (asl,w) ->
  let _,body = dest_exists w in
  let c1,_ = dest_conj body in
  let l1 = lhs c1 in
  let wit = rhs(concl(snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = l1) asl))) in
  (EXISTS_TAC wit THEN ASM_REWRITE_TAC[]) (asl,w);;
let H1A_BIGNUM_TAC : tactic =
  SUBGOAL_THEN `(8:num) = 8 * loop_count` SUBST1_TAC THENL
   [UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC; SUPPLY_BIGNUM_WITNESS];;

let sta_h1a : (int * thm) list ref = ref [];;

let HEAD_LC1_A = prove(head_lc1a_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(BETA_RULE) THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4; mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  (* stepper needs the word bounds in context for the two cbz VAL_WORD resolutions *)
  SUBGOAL_THEN `loop_count < 2 EXP 64 /\ loop_count - 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(val (word loop_count:int64) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_sub (word loop_count) (word 1):int64) = 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `word_sub (word loop_count) (word 1):int64 = word (loop_count - 1)` SUBST1_TAC THENL
     [SUBGOAL_THEN `loop_count = (loop_count-1)+1` (fun th->ONCE_REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[ADD_SUB] THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC; ALL_TAC] THEN
  PREAMBLE_SNAPSHOT_TAC THEN H1A_SNAPSHOT_TAC THEN HEAD_DIGITIZE_TAC THEN
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--89) sta_h1a (Some (replicate preamble_regs_pin 89)) THEN
  PREAMBLE_DISCARD_BIGNUM_ONLY_TAC THEN
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--89) (1--89) sta_h1a (Some (replicate preamble_regs_pin 89)) THEN
  PREAMBLE_FORWARD_BIGNUM_TAC THEN H1A_FWD_TAC THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  CONJ_TAC THENL [
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[mk_equiv_regs] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0] THEN REPEAT CONJ_TAC THEN
    TRY(PREAMBLE_LEAF_TAC THEN NO_TAC) THEN
    TRY(FIRST_ASSUM MATCH_ACCEPT_TAC THEN NO_TAC) THEN
    TRY(H1A_BIGNUM_TAC THEN NO_TAC) THEN
    TRY(H1A_X16_TAC THEN NO_TAC) THEN
    ASM_REWRITE_TAC[];
    MONOTONE_MAYCHANGE_CONJ_TAC ]);;

Printf.printf "*** HEAD_LC1_A proved ***\n";;

(* ------------------------------------------------------------------------- *)
(* HEAD_LC1 : loop_count = 1, entry 0x88 -> 0x628 = HEAD_LC1_A ++ REDUCE_GEN.  *)
(* The 0x4b4 seam is exact (HEAD_LC1_A.post = REDUCE_LAST_GEN.pre), so plain    *)
(* ENSURES2_TRANS composes them.  Rebuilt as a clean forall-imp theorem        *)
(* (carrying the two per-leg preconds conjoined) so it can be grafted below.    *)
(* ------------------------------------------------------------------------- *)

let whole_params =
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`tag_p:int64`;`ivec_p:int64`;
   `stackpointer:int64`;`len_bits:num`;`nblocks:num`;`loop_count:num`;`loop_remain:num`;
   `tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`];;

let rec top_conjuncts n th = if n <= 1 then [th] else CONJUNCT1 th :: top_conjuncts (n-1) (CONJUNCT2 th);;

let HEAD_LC1 =
  let h = trans_exact (UNDISCH(SPEC_ALL HEAD_LC1_A)) (UNDISCH(SPEC_ALL REDUCE_LAST_GEN)) in
  let hs = hyp h in
  let conjP = list_mk_conj hs in
  let parts = top_conjuncts (length hs) (ASSUME conjP) in
  let discharged = itlist (fun ci th -> PROVE_HYP ci th) parts h in
  GENL whole_params (DISCH conjP discharged);;

Printf.printf "*** HEAD_LC1 composed (0x88 -> 0x628) ***\n";;

(* ------------------------------------------------------------------------- *)
(* Graft f_ptr (X3=tag_p, X4=ivec_p on both sides) onto the SMALL simple-frame  *)
(* head/reduce legs, so their 0x628 post matches the STEADY tail's CBZ pre.     *)
(* (Grafting onto HEAD_LC1 directly fails: its frame is a ,,-composed relation.)*)
(* ------------------------------------------------------------------------- *)

let HEAD_LC0_G = prove(graft_goal (concl HEAD_LC0) f_ptr,
  REPEAT STRIP_TAC THEN GRAFT_TAC f_ptr (FP_REGS_TAC [`X3`;`X4`]) HEAD_LC0);;
let HEAD_LC1_A_G = prove(graft_goal (concl HEAD_LC1_A) f_ptr,
  REPEAT STRIP_TAC THEN GRAFT_TAC f_ptr (FP_REGS_TAC [`X3`;`X4`]) HEAD_LC1_A);;
let REDUCE_GEN_G = prove(graft_goal (concl REDUCE_LAST_GEN) f_ptr,
  REPEAT STRIP_TAC THEN GRAFT_TAC f_ptr (FP_REGS_TAC [`X3`;`X4`]) REDUCE_LAST_GEN);;

Printf.printf "*** degenerate grafted legs proved ***\n";;

(* ------------------------------------------------------------------------- *)
(* Compose the four degenerate whole-function theorems and discharge each's     *)
(* per-leg preconds from a case-specific whole-function precondition.           *)
(* ------------------------------------------------------------------------- *)

let po th = List.nth (ens_args (concl th)) 2 and pr th = List.nth (ens_args (concl th)) 1;;

(* case loop_count = 1, 1 <= loop_remain *)
let composed_lc1_rempos =
  let hg  = UNDISCH (SPEC_ALL HEAD_LC1_A_G) in
  let rg  = UNDISCH (SPEC_ALL REDUCE_GEN_G) in
  let cg  = UNDISCH (SPEC_ALL CBZ_G) in
  let lg  = UNDISCH (SPEC_ALL REMLOOP_G) in
  let pog = UNDISCH (SPEC_ALL POSTAMBLE_EQUIV) in
  let c1 = trans_exact hg rg in
  let c2 = trans_exact c1 cg in
  let c3 = trans_exact c2 lg in
  trans_weaken c3 WEAKEN_REMLOOP_POST pog;;

(* case loop_count = 1, loop_remain = 0 *)
let composed_lc1_rem0 =
  let inst0 th = INST [`0`,`loop_remain:num`] (SPEC_ALL th) in
  let hg  = UNDISCH (inst0 HEAD_LC1_A_G) in
  let rg  = UNDISCH (inst0 REDUCE_GEN_G) in
  let ctg = UNDISCH (SPEC_ALL CBZ_TAKEN_G) in
  let pog = UNDISCH (inst0 POSTAMBLE_EQUIV) in
  let wk_cp0 = prove(mk_weaken (po ctg) (pr pog), WEAKEN_TAC) in
  let c1 = trans_exact hg rg in
  let c2 = trans_exact c1 ctg in
  trans_weaken c2 wk_cp0 pog;;

(* case loop_count = 0, 1 <= loop_remain *)
let instlc0 th = INST [`0`,`loop_count:num`] (SPEC_ALL th);;
let composed_lc0_rempos =
  let hg  = UNDISCH (SPEC_ALL HEAD_LC0_G) in
  let cg  = UNDISCH (instlc0 CBZ_G) in
  let lg  = UNDISCH (instlc0 REMLOOP_G) in
  let pog = UNDISCH (instlc0 POSTAMBLE_EQUIV) in
  let wk = prove(mk_weaken (po lg) (pr pog), WEAKEN_TAC) in
  let c1 = trans_exact hg cg in
  let c2 = trans_exact c1 lg in
  trans_weaken c2 wk pog;;

(* case loop_count = 0, loop_remain = 0 *)
let composed_lc0_rem0 =
  let inst00 th = INST [`0`,`loop_count:num`; `0`,`loop_remain:num`] (SPEC_ALL th) in
  let hg  = UNDISCH (INST [`0`,`loop_remain:num`] (SPEC_ALL HEAD_LC0_G)) in
  let ctg = UNDISCH (instlc0 CBZ_TAKEN_G) in
  let pog = UNDISCH (inst00 POSTAMBLE_EQUIV) in
  let wk = prove(mk_weaken (po ctg) (pr pog), WEAKEN_TAC) in
  let c1 = trans_exact hg ctg in
  trans_weaken c1 wk pog;;

Printf.printf "*** four degenerate composites built ***\n";;

(* case-specific whole-function preconditions (from whole_precond). *)
let base_conjs = conjuncts whole_precond;;
let wp_lc1_rempos = list_mk_conj
  (map (fun t -> if t = `2 <= loop_count` then `loop_count = 1` else t) base_conjs);;
let wp_lc1_rem0 = subst[`0`,`loop_remain:num`] (list_mk_conj
  (filter (fun t->t <> `1 <= loop_remain`)
    (map (fun t->if t=`2 <= loop_count` then `loop_count = 1` else t) base_conjs)));;
let wp_lc0_rempos = subst[`0`,`loop_count:num`] (list_mk_conj
  (filter (fun t->t <> `2 <= loop_count`) base_conjs));;
let wp_lc0_rem0 = subst[`0`,`loop_count:num`;`0`,`loop_remain:num`] (list_mk_conj
  (filter (fun t->t <> `2 <= loop_count` && t <> `1 <= loop_remain`) base_conjs));;

let DISCHARGE_GEN wp_tm h =
  prove(mk_imp(wp_tm, h),
    STRIP_TAC THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN TRY(ASM_ARITH_TAC) THEN
    TRY(NONOVERLAPPING_TAC) THEN
    TRY(MP_TAC(ASSUME `16 * nblocks < 2 EXP 64`) THEN
        (TRY(MP_TAC(ASSUME `nblocks DIV 4 = loop_count`))) THEN ARITH_TAC));;

let finalize wp_tm quants composed =
  let wp = ASSUME wp_tm in
  let discharged =
    itlist (fun h th -> PROVE_HYP (MP (DISCHARGE_GEN wp_tm h) wp) th)
           (hyp composed) composed in
  GENL quants (DISCH wp_tm discharged);;

let quants_lc = whole_params;;
let quants_lc0 = filter (fun t->t <> `loop_count:num`) quants_lc;;
let quants_lc1_rem0 = filter (fun t->t <> `loop_remain:num`) quants_lc;;
let quants_lc0_rem0 = filter (fun t->t <> `loop_remain:num`) quants_lc0;;

let SWP_DEINT_SWPS_EQUIV_LC1_REMPOS = finalize wp_lc1_rempos quants_lc composed_lc1_rempos;;
Printf.printf "*** SWP_DEINT_SWPS_EQUIV_LC1_REMPOS proved (hyps=%d) ***\n"
  (length(hyp SWP_DEINT_SWPS_EQUIV_LC1_REMPOS));;

let SWP_DEINT_SWPS_EQUIV_LC1_REM0 = finalize wp_lc1_rem0 quants_lc1_rem0 composed_lc1_rem0;;
Printf.printf "*** SWP_DEINT_SWPS_EQUIV_LC1_REM0 proved (hyps=%d) ***\n"
  (length(hyp SWP_DEINT_SWPS_EQUIV_LC1_REM0));;

let SWP_DEINT_SWPS_EQUIV_LC0_REMPOS = finalize wp_lc0_rempos quants_lc0 composed_lc0_rempos;;
Printf.printf "*** SWP_DEINT_SWPS_EQUIV_LC0_REMPOS proved (hyps=%d) ***\n"
  (length(hyp SWP_DEINT_SWPS_EQUIV_LC0_REMPOS));;

let SWP_DEINT_SWPS_EQUIV_LC0_REM0 = finalize wp_lc0_rem0 quants_lc0_rem0 composed_lc0_rem0;;
Printf.printf "*** SWP_DEINT_SWPS_EQUIV_LC0_REM0 proved (hyps=%d) ***\n"
  (length(hyp SWP_DEINT_SWPS_EQUIV_LC0_REM0));;

(* ------------------------------------------------------------------------- *)
(* SUMMARY.  Six theorems together give the whole-body equivalence for EVERY   *)
(* (loop_count, loop_remain < 4):                                              *)
(*                                                                           *)
(*   swp_equiv_whole.ml:                                                       *)
(*     SWP_DEINT_SWPS_EQUIV_STEADY      : 2 <= loop_count /\ 1 <= loop_remain   *)
(*     SWP_DEINT_SWPS_EQUIV_REM0        : 2 <= loop_count /\ loop_remain = 0    *)
(*   here:                                                                     *)
(*     SWP_DEINT_SWPS_EQUIV_LC1_REMPOS  : loop_count = 1 /\ 1 <= loop_remain    *)
(*     SWP_DEINT_SWPS_EQUIV_LC1_REM0    : loop_count = 1 /\ loop_remain = 0     *)
(*     SWP_DEINT_SWPS_EQUIV_LC0_REMPOS  : loop_count = 0 /\ 1 <= loop_remain    *)
(*     SWP_DEINT_SWPS_EQUIV_LC0_REM0    : loop_count = 0 /\ loop_remain = 0     *)
(*                                                                           *)
(* All axiom-free, all ensures2 from the shared entry 0x88 to the shared exit  *)
(* 0x710.  Composing each (LEFT = deint) with the deint functional spec         *)
(* DEINT_FROM88 transfers deint's correctness to the swpS schedule for every    *)
(* input length.                                                               *)
(* ------------------------------------------------------------------------- *)



(* ========================================================================= *)
(* Convenience re-exports under the kernel's own name.  These are the SAME    *)
(* SWP_DEINT_SWPS_EQUIV_... theorems proved above; no new obligation here.     *)
(* ========================================================================= *)

let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_STEADY =
  SWP_DEINT_SWPS_EQUIV_STEADY;;
let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_REM0 =
  SWP_DEINT_SWPS_EQUIV_REM0;;
let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_LC1_REMPOS =
  SWP_DEINT_SWPS_EQUIV_LC1_REMPOS;;
let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_LC1_REM0 =
  SWP_DEINT_SWPS_EQUIV_LC1_REM0;;
let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_LC0_REMPOS =
  SWP_DEINT_SWPS_EQUIV_LC0_REMPOS;;
let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_LC0_REM0 =
  SWP_DEINT_SWPS_EQUIV_LC0_REM0;;

let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV =
  [ AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_STEADY;
    AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_REM0;
    AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_LC1_REMPOS;
    AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_LC1_REM0;
    AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_LC0_REMPOS;
    AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_EQUIV_LC0_REM0 ];;

Printf.printf "*** _swp_S <-> _swp_deint equivalence: 6/6 cases (all loop_count, all loop_remain<4) ***\n";;

(* ========================================================================= *)
(* Towards ..._SWP_S_CORRECT: step-count extraction (transfer ingredient A).  *)
(*                                                                           *)
(* ensures2 unfolds to nested eventually_n; its OUTER component is exactly    *)
(* the LEFT (deint) program's step-count fact.  These two general lemmas peel *)
(* a state-independent conclusion out of an eventually_n, and                 *)
(* EXTRACT_DEINT_EVN specialises the outer eventually_n of a proved           *)
(* equivalence to `eventually_n arm (f_n1 s1) (\s1'. read PC s1' =            *)
(* word(pc+0x710)) s1` - deint's eventually_n_at_pc content at the            *)
(* equivalence's own (data-dependent) step count, with NO re-derivation.      *)
(* Feeds ENSURES_AND_EVENTUALLY_N_AT_PC_PROVES_ENSURES_N to obtain deint's    *)
(* ensures_n, the LEFT premise of the ENSURES2_ENSURES_N transfer.            *)
(* ------------------------------------------------------------------------- *)

(* A state-independent conjunct escapes an eventually_n (non-vacuous by       *)
(* STEPS_NOSTUCK): the trace of length n has an endpoint where the body       *)
(* holds, and the conjunct does not depend on that endpoint.                  *)
let EVENTUALLY_N_CONST_OUT = prove(
  `!(step:S->S->bool) (A:bool) Q n s0.
      eventually_n step n (\s. A /\ Q s) s0 ==> A`,
  REWRITE_TAC[eventually_n] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`step:S->S->bool`;`n:num`;`s0:S`] STEPS_NOSTUCK) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(fun th2 ->
     MP_TAC(MATCH_MP th th2))) THEN
  SIMP_TAC[]);;

(* More convenient forward form: eventually_n plus a body-implication yields   *)
(* the (state-independent) consequent.                                        *)
let EVENTUALLY_N_IMP_CONST = prove(
  `!(step:S->S->bool) P n s (A:bool).
      eventually_n step n P s /\ (!x. P x ==> A) ==> A`,
  REWRITE_TAC[eventually_n] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`step:S->S->bool`;`n:num`;`s:S`] STEPS_NOSTUCK) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

(* From a proved whole-function equivalence theorem `equiv_th` (one of the six *)
(* SWP_DEINT_SWPS_EQUIV_... theorems), build the deint-side eventually_n at    *)
(* the equivalence's own step count f_n1:                                     *)
(*   forall <params>. precond ==> !s1 s2. P (s1,s2) ==>                        *)
(*      eventually_n arm (f_n1 s1) (\s1'. read PC s1' = word (pc + 0x710)) s1  *)
let mk_extract_deint_evn equiv_th =
  let qs, body = strip_forall (concl equiv_th) in
  let precond, ens = dest_imp body in
  let eargs = snd(strip_comb ens) in
  let eP = List.nth eargs 1 and ef1 = List.nth eargs 4 in
  let s1v = `s1:armstate` and s2v = `s2:armstate` in
  let leftpc = `\s1':armstate. read PC s1' = word (pc + 0x710)` in
  let evn = list_mk_icomb "eventually_n" [`arm`; mk_comb(ef1,s1v); leftpc; s1v] in
  let inner = list_mk_forall([s1v;s2v], mk_imp(mk_comb(eP, mk_pair(s1v,s2v)), evn)) in
  let goal = list_mk_forall(qs, mk_imp(precond, inner)) in
  prove(goal,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (SPEC_ALL equiv_th) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ensures2] THEN
    DISCH_THEN(fun th -> REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC (SPECL [s1v;s2v] th)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] EVENTUALLY_N_MONO) THEN
    BETA_TAC THEN GEN_TAC THEN
    W(fun (asl,w) -> DISCH_THEN(fun hyp ->
       let args = snd(strip_comb(concl hyp)) in
       let nN = List.nth args 1 and bdy = List.nth args 2 and s2t = List.nth args 3 in
       MP_TAC(ISPECL [`arm`; bdy; nN; s2t; w] EVENTUALLY_N_IMP_CONST) THEN
       REWRITE_TAC[hyp] THEN
       DISCH_THEN MATCH_MP_TAC THEN
       GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[])));;

let EXTRACT_DEINT_EVN_STEADY =
  mk_extract_deint_evn SWP_DEINT_SWPS_EQUIV_STEADY;;
let EXTRACT_DEINT_EVN_REM0 =
  mk_extract_deint_evn SWP_DEINT_SWPS_EQUIV_REM0;;
let EXTRACT_DEINT_EVN_LC1_REMPOS =
  mk_extract_deint_evn SWP_DEINT_SWPS_EQUIV_LC1_REMPOS;;
let EXTRACT_DEINT_EVN_LC1_REM0 =
  mk_extract_deint_evn SWP_DEINT_SWPS_EQUIV_LC1_REM0;;
let EXTRACT_DEINT_EVN_LC0_REMPOS =
  mk_extract_deint_evn SWP_DEINT_SWPS_EQUIV_LC0_REMPOS;;
let EXTRACT_DEINT_EVN_LC0_REM0 =
  mk_extract_deint_evn SWP_DEINT_SWPS_EQUIV_LC0_REM0;;

Printf.printf "*** deint step-count (eventually_n) extracted for all 6 cases ***\n";;
