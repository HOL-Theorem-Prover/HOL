(* Run after Candle replay of compute-binders.pft.bin and its dependencies,
   or the corresponding merged trace. *)
let check_compute name input result =
  let th = assoc ("pft_compute_binders$" ^ name) (!saved_ths) in
  if hyp th = [] && aconv (concl th) (mk_eq (input,result)) then
    print_endline ("COMPUTE_BINDER_EXACT " ^ name)
  else failwith ("compute binder sequent mismatch: " ^ name);;
let _ =
  let cv = mk_type ("cval",[]) in
  let num = mk_type ("num",[]) in
  let nn = mk_fun_ty num num in
  let zero = mk_mconst ("_0",num) in
  let bit name tm = mk_comb (mk_mconst(name,nn),tm) in
  let numeral tm = mk_comb (mk_mconst("NUMERAL",nn),tm) in
  let two = numeral (bit "BIT2" zero) in
  let four = numeral (bit "BIT2" (bit "BIT1" zero)) in
  let six = numeral (bit "BIT2" (bit "BIT2" zero)) in
  let cvnum tm = mk_comb (mk_mconst("Cexp_num",mk_fun_ty num cv),tm) in
  let letc = mk_mconst("LET",mk_fun_ty (mk_fun_ty cv cv) (mk_fun_ty cv cv)) in
  let let_tm v body arg = mk_comb (mk_comb (letc,mk_abs(v,body)),arg) in
  let x = mk_var("x",cv) in
  let y = mk_var("y",cv) in
  let add = mk_mconst("Cexp_add",mk_fun_ty cv (mk_fun_ty cv cv)) in
  let simple = let_tm x x (cvnum zero) in
  let nested = let_tm x
    (let_tm y (mk_comb(mk_comb(add,x),y)) (cvnum four)) (cvnum two) in
  check_compute "SIMPLE" simple (cvnum zero);
  check_compute "NESTED" nested (cvnum six);
  check_compute "CAPTURE" nested (cvnum six);
  print_endline "COMPUTE_BINDER_ALL_EXACT_PASS";;
