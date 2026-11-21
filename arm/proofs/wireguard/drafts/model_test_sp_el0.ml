(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* The test of drafts/arm_model_sp_el0.patch, run in a fresh session with    *)
(* the patch applied: the decoding of the forms of the new instructions in   *)
(* the image, and an LL/SC increment loop as in the kernel's atomics.        *)

loadt "arm/proofs/base.ml";;
Printf.printf "BASELOADED %.1f\n%!" (Sys.time());;
let test_words = [0xd5384101; 0xc89ffc61; 0xc85f7c20; 0xc802fc20; 0xd5033bbf;
                  0xd50339bf; 0xf9800031; 0x885f7c03; 0x88057c01; 0x8804fca3];;
List.iter (fun w ->
  let tm = mk_comb(`decode`, mk_comb(`word:num->int32`, mk_small_numeral w)) in
  Printf.printf "DECODE %x: %s\n%!" w (string_of_term(rand(concl(DECODE_CONV tm)))))
  test_words;;
let define_mc_from_intlist (newname:string) (ops:int list) =
  let charlist = flat (map
    (fun op32 ->
      [Char.chr (op32 land 255);
       Char.chr ((op32 lsr 8) land 255);
       Char.chr ((op32 lsr 16) land 255);
       Char.chr ((op32 lsr 24) land 255)]) ops) in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list newname (term_of_bytes byte_list);;
let test_mc = define_mc_from_intlist "test_mc"
  [0xf9800031; 0xc85f7c20; 0x91000400; 0xc802fc20; 0x35ffffa2;
   0xd5033bbf; 0xd5384103; 0xc89ffc61; 0xd65f03c0];;
let TEST_EXEC = ARM_MK_EXEC_RULE test_mc;;
let TEST_CORRECT = prove
 (`!x c t pc returnaddress.
     nonoverlapping (word pc,36) (x,8) /\ nonoverlapping (word pc,36) (t,8) /\
     nonoverlapping (x,8) (t,8)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) test_mc /\
               read PC s = word pc /\ read X30 s = returnaddress /\
               read X1 s = x /\ read SP_EL0 s = t /\
               read (memory :> bytes64 x) s = c)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes64 x) s = word_add c (word 1) /\
               read X0 s = word_add c (word 1) /\
               read (memory :> bytes64 t) s = x /\
               read SP_EL0 s = t)
          (MAYCHANGE [PC; X0; X2; X3] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes64 x; memory :> bytes64 t])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC TEST_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
Printf.printf "MODELTEST %b\n%!" (hyp TEST_CORRECT = []);;
