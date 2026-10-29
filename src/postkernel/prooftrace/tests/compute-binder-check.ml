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
  let rec bits n =
    if n = 0 then zero
    else if n mod 2 = 1 then bit "BIT1" (bits (n / 2))
    else bit "BIT2" (bits ((n - 2) / 2)) in
  let numeral n =
    if n = 0 then zero else
    mk_comb (mk_mconst("NUMERAL",nn),bits n) in
  let cvnum n = mk_comb
    (mk_mconst("Cexp_num",mk_fun_ty num cv),numeral n) in
  let letc = mk_mconst("LET",mk_fun_ty (mk_fun_ty cv cv) (mk_fun_ty cv cv)) in
  let let_tm v body arg = mk_comb (mk_comb (letc,mk_abs(v,body)),arg) in
  let x = mk_var("x",cv) in
  let y = mk_var("y",cv) in
  let addc = mk_mconst("Cexp_add",mk_fun_ty cv (mk_fun_ty cv cv)) in
  let add a b = mk_comb(mk_comb(addc,a),b) in
  let simple = let_tm x x (cvnum 0) in
  let nested = let_tm x (let_tm y (add x y) (cvnum 4)) (cvnum 2) in
  check_compute "SIMPLE" simple (cvnum 0);
  check_compute "NESTED" nested (cvnum 6);
  check_compute "CAPTURE" nested (cvnum 6);
  check_compute "CLOSURE" (add (cvnum 4) (cvnum 2)) (cvnum 6);
  check_compute "CLOSURE_NESTED"
    (let_tm x (add (cvnum 4) x) (cvnum 2)) (cvnum 6);
  check_compute "CLOSURE_CAPTURE" nested (cvnum 6);
  List.iter (fun (name,n) -> check_compute name (cvnum n) (cvnum n))
    [("NUM_255",255);("NUM_256",256);("NUM_257",257);
     ("NUM_18446744073709551616",18446744073709551616)];
  let b = mk_type("bool",[]) in
  let f = mk_var("f",mk_fun_ty b b) in
  let v = mk_var("kind_x",b) in
  let abstraction = mk_abs(f,v) in
  check_compute "KIND_COLLISION" abstraction abstraction;
  let capture = mk_abs(f,abstraction) in
  check_compute "KIND_CAPTURE" capture capture;
  print_endline "COMPUTE_BINDER_ALL_EXACT_PASS";;
