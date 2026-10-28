let check_oracle_results () =
  let bool_ty = mk_type ("bool", []) in
  let p = mk_var ("p", bool_ty) in
  let q = mk_var ("q", bool_ty) in
  let r = mk_var ("r", bool_ty) in
  let cases =
    [("empty", [], p);
     ("one", [q], p);
     ("two", [q; r], p);
     ("overlap", [p; q], p);
     ("duplicate", [q; r], p)] in
  let subset xs ys = forall (fun x -> exists (aconv x) ys) xs in
  let check (name, hyps, conclusion) =
    let key = "oracle_hyps$" ^ name in
    let th = load_th key in
    let actual = hyp th in
    if length actual = length hyps &&
       subset actual hyps && subset hyps actual &&
       aconv (concl th) conclusion then
      print_endline ("CHECKED: " ^ key)
    else failwith ("wrong oracle sequent: " ^ key) in
  do_list check cases;
  print_endline "PFT_ORACLE_ALL_CHECKS_PASSED";;

let check_deduct_results () =
  let bool_ty = mk_type ("bool", []) in
  let p = mk_var ("p", bool_ty) in
  let q = mk_var ("q", bool_ty) in
  let r = mk_var ("r", bool_ty) in
  let cases =
    [("deduct", [r], mk_eq (p, q));
     ("deduct_reverse", [r], mk_eq (q, p));
     ("deduct_empty", [], mk_eq (p, p))] in
  let subset xs ys = forall (fun x -> exists (aconv x) ys) xs in
  let check (name, hyps, conclusion) =
    let key = "deduct_antisym$" ^ name in
    let th = load_th key in
    let actual = hyp th in
    if length actual = length hyps &&
       subset actual hyps && subset hyps actual &&
       aconv (concl th) conclusion then
      print_endline ("CHECKED: " ^ key)
    else failwith ("wrong deductAntisym sequent: " ^ key) in
  do_list check cases;
  print_endline "PFT_DEDUCT_ALL_CHECKS_PASSED";;
