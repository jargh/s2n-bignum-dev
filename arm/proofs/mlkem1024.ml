(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The API of ML-KEM-1024 in mlkem_native2 (arm/mlkem_native2/mlkem1024.S),  *)
(* in the image: so far the key checks of FIPS 203 (section 7), with the     *)
(* results stated as in the proofs of mlkem-native's compiled C.             *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native2_api.ml";;

(* ------------------------------------------------------------------------- *)
(* The modulus check of an encapsulation key pk: 0 if the 1024 12-bit        *)
(* fields of its polynomial vector are all < q, else -4                      *)
(* (MLK_ERR_INVALID_PK).                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_CHECK_PK_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem1024_check_pk"];;

let MLKEM1024_CHECK_PK_SUBROUTINE_CORRECT = prove
 (`!pk n pc stackpointer returnaddress.
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 16),16))
         [(word pc,mlkem_native2_image_size); (pk,1536)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem1024_check_pk) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [pk] s /\
               read (memory :> bytes(pk,1536)) s = n)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
               if !i. i < 1024 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
               then word 0 else word 0xfffffffc)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MLKEM_NATIVE2_CHECK_PK_CORRECT_TAC MLKEM1024_CHECK_PK_EXEC 4);;

let MLKEM1024_CHECK_PK_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e pk pc stackpointer returnaddress.
       aligned 16 stackpointer /\
       ALL (nonoverlapping (word_sub stackpointer (word 16),16))
           [(word pc,mlkem_native2_image_size); (pk,1536)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem1024_check_pk) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [pk] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events pk pc (word_sub stackpointer (word 16))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [pk,1536; word_sub stackpointer (word 16),16]
                     [word_sub stackpointer (word 16),16]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MLKEM_NATIVE2_CHECK_PK_SAFE_TAC MLKEM1024_CHECK_PK_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The hash check of a decapsulation key sk, with ek at offset 1536 and the  *)
(* hash h of ek at offset 3104: 0 if h = H(ek), else -5                      *)
(* (MLK_ERR_INVALID_SK). The stack is the 64 bytes of the frame and the 384  *)
(* used by mlkem_hash_h. As for all the API functions, the image must be at  *)
(* a multiple of 4096, for the address of the constants block by ADRP.       *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_CHECK_SK_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem1024_check_sk"];;

let MLKEM1024_CHECK_SK_SUBROUTINE_CORRECT = prove
 (`!sk (ek:byte list) h pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH ek = 1568 /\
     ALL (nonoverlapping (word_sub stackpointer (word 448),448))
         [(word pc,mlkem_native2_image_size); (sk,3168)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem1024_check_sk) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [sk] s /\
               read (memory :> bytes(word_add sk (word 1536),1568)) s =
               num_of_bytelist ek /\
               read (memory :> bytes(word_add sk (word 3104),32)) s = h)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
               if h = num_of_bytelist(sha3_256 ek) then word 0
               else word 0xfffffffb)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 448),448)])`,
  MLKEM_NATIVE2_CHECK_SK_CORRECT_TAC MLKEM1024_CHECK_SK_EXEC 3104);;

let MLKEM1024_CHECK_SK_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e sk pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       ALL (nonoverlapping (word_sub stackpointer (word 448),448))
           [(word pc,mlkem_native2_image_size); (sk,3168)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem1024_check_sk) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk pc (word_sub stackpointer (word 448))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [sk,3168; word(pc + mlkem_native2_constants),192;
                      word_sub stackpointer (word 448),448]
                     [word_sub stackpointer (word 448),448]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 448),448)])`,
  MLKEM_NATIVE2_CHECK_SK_SAFE_TAC MLKEM1024_CHECK_SK_EXEC 1568);;
