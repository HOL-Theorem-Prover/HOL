let check_oracle_results () =
  let b = mk_type ("bool", []) in
  let p = mk_var ("p", b) in
  let q = mk_var ("q", b) in
  let r = mk_var ("r", b) in
  let th = load_th "oracle_hyps$hyps" in
  if length (hyp th) = 2 && exists (aconv q) (hyp th) &&
     exists (aconv r) (hyp th) && aconv (concl th) p
  then print_endline "PFT_ORACLE_ALL_CHECKS_PASSED"
  else failwith "oracle replay lost hypotheses or changed its conclusion";;

let check_deduct_results () =
  let b = mk_type ("bool", []) in
  let p = mk_var ("p", b) in
  let q = mk_var ("q", b) in
  let r = mk_var ("r", b) in
  let th = load_th "deduct_antisym$deduct" in
  if length (hyp th) = 1 && aconv (hd (hyp th)) r &&
     aconv (concl th) (mk_eq (p,q))
  then print_endline "PFT_DEDUCT_ALL_CHECKS_PASSED"
  else failwith "wrong deductAntisym sequent";;
