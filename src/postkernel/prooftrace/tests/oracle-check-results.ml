let check_oracle_results () =
  let b = mk_type ("bool", []) in
  let p = mk_var ("p", b) in
  let q = mk_var ("q", b) in
  let r = mk_var ("r", b) in
  let th = load_th "oracle_hyps$hyps" in
  if length (hyp th) = 2 && exists (aconv q) (hyp th) &&
     exists (aconv r) (hyp th) && aconv (concl th) p
  then ()
  else failwith "oracle replay lost hypotheses or changed its conclusion";
  let x = mk_var ("x",b) in
  let y = mk_var ("y",b) in
  let synthetic = mk_var ("x pft%0",b) in
  let lam = mk_abs (y,mk_eq (x,synthetic)) in
  let capture = load_th "oracle_hyps$capture" in
  if hyp capture = [] && aconv (concl capture) (mk_eq (lam,lam)) then
    print_endline "PFT_ORACLE_CAPTURE_EXACT_PASS"
  else failwith "oracle abstraction captured a free variable";
  print_endline "PFT_ORACLE_ALL_CHECKS_PASSED";;
