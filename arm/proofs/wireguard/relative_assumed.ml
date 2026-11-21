(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Contracts that are assumed rather than proved, for the link file: some    *)
(* functions of the image are not proved (yet), and the theorems of their    *)
(* callers keep their statements as explicit assumptions.                    *)
(*                                                                           *)
(* relative_assume T_STMT marks the contract stated by assume_spec T_STMT as *)
(* assumed. relative_close_assuming then closes a theorem as relative_close  *)
(* (relative.ml) does, except that the assumptions that are assumed          *)
(* contracts are left as assumptions, and relative_report_assumed is         *)
(* relative_report except that it lists the assumed contracts that have no   *)
(* proof instead of failing for them.                                        *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;

let relative_assumed = ref ([]:term list);;

let relative_assume tm =
  match relative_find_contract (relative_contract_of tm) with
    Some(s,_,_) ->
      if not (exists (aconv s) (!relative_assumed))
      then relative_assumed := s::(!relative_assumed)
  | None -> failwith("relative_assume: not a contract: "^string_of_term tm);;

let relative_is_assumed h =
  match relative_find_contract h with
    Some(s,_,_) -> exists (aconv s) (!relative_assumed)
  | None -> false;;

let relative_close_assuming =
  let rec close_hyp visiting h =
    if relative_is_assumed h then ASSUME h else
    try relative_close (ASSUME h) with Failure _ ->
    let s,p,_ =
      match relative_find_contract h with
        Some x -> x
      | None ->
          failwith("relative_close_assuming: no contract for "^
                   string_of_term h) in
    let pth =
      match !p with
        Some pth -> pth
      | None -> failwith("relative_close_assuming: contract not proved: "^
                         string_of_term s) in
    if exists (aconv s) visiting then
      failwith("relative_close_assuming: circular contract: "^
               string_of_term s) else
    let cth = close (s::visiting) pth in
    let ith = INSTANTIATE (term_match [] (concl cth) h) cth in
    if concl ith = h then ith else EQ_MP (ALPHA (concl ith) h) ith
  and close visiting th =
    itlist (fun h th -> PROVE_HYP (close_hyp visiting h) th) (hyp th) th in
  fun th ->
    let cth = close [] th in
    if exists (fun h -> not(relative_is_assumed h)) (hyp cth)
    then failwith "relative_close_assuming: assumptions left"
    else cth;;

let relative_report_assumed () =
  let l = rev(!relative_contracts) in
  let unproved = filter (fun (_,p,_) -> !p = None) l in
  let assumed,missing =
    partition (fun (s,_,_) -> exists (aconv s) (!relative_assumed))
              unproved in
  do_list (fun (s,p,_) ->
    match !p with
      Some th -> ignore(relative_close_assuming th)
    | None -> ()) l;
  Format.print_string(Printf.sprintf
    "relative: %d contracts stated, %d proved and closed, %d assumed"
    (length l) (length l - length unproved) (length assumed));
  Format.print_newline();
  do_list (fun (s,_,_) ->
    Format.print_string "relative: assumed: "; print_qterm s;
    Format.print_newline()) assumed;
  if missing <> [] then
   (do_list (fun (s,_,_) ->
      Format.print_string "relative: not proved: "; print_qterm s;
      Format.print_newline()) missing;
    failwith "relative_report_assumed: contracts not proved");;
