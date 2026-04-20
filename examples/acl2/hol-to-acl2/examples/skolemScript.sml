Theory skolem
Ancestors
  hol_to_acl2
Libs
  HOL_to_ACL2 Elim_Lambda

val skolem = thm_bundle "SKOLEM_THM" SKOLEM_THM;

(*---------------------------------------------------------------------------*)
(* Output defhol file                                                        *)
(*---------------------------------------------------------------------------*)

val _ = print_bundles_to_file "skolem.defhol" [skolem];
