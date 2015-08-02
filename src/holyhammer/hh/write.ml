(*--------------------------------------------------------------------------- *)
(* Write problems to fof from the axioms' name and the conjecture name        *)
(* The hash term_hash used by term_of needs to be initialized beforehand by   *)
(* Thf1hh1.parse or init_dep_env or init_acc_env                              *) 
(*--------------------------------------------------------------------------- *)

open Hh_parse
open Thf1hh1
open Dependency

(* Required theorems for the ATPs. *)
let additional_theorems () =
  let falsity = Fusion.Sequent([],Hl_parser.parse_term "~F") in
  let ext = Fusion.Sequent([],Hl_parser.parse_term "!f g. (!x. f x = g x) ==> f = g") in
  [Bool.tRUTH; falsity; Bool.bOOL_CASES_AX; ext],
  ["HL_TRUTH"; "HL_FALSITY"; "HL_BOOL_CASES"; "HL_EXT"]

(* Make a theorem without premises (?) from a theorem name. *)
let mk_thm (thm_name : string) = Fusion.Sequent ([], term_of thm_name)

(* Write a FOF file from given conjecture and axioms for use with an ATP. *)
let write_fof file_name (cj_name, axioms) =
  let (ath, a) = additional_theorems () in
  let (pth, p) = (ath @ List.map mk_thm axioms, a @ axioms) in
  Hh_write.write_atp_proof file_name (pth,p) cj_name (term_of cj_name)
