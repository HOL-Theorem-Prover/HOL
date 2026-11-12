let check_sequent name hs tm th =
  if length (hyp th) = length hs &&
     forall (fun h -> exists (aconv h) (hyp th)) hs &&
     aconv (concl th) tm then print_endline ("PFT_EXACT " ^ name)
  else failwith ("wrong sequent: " ^ name);;
let check_saved name hs tm = check_sequent name hs tm (load_th name);;
let check_refl name tm = check_saved name [] (mk_eq(tm,tm));;
let forall_bool v tm = mk_comb
  (inst [bool_ty,mk_vartype "'a"] (mk_const("!",[])),mk_abs(v,tm));;
let conj p q = mk_comb(mk_comb(mk_const("/\\",[]),p),q);;
let imp p q = mk_comb(mk_comb(mk_const("==>",[]),p),q);;

let check_export_results () =
  let x = mk_var("x",bool_ty) in
  let a = mk_const("pftExport_shadow$first",[]) in
  let b = mk_const("pftExport_shadow$second",[]) in
  check_saved "pftExport_shadow$SHADOW" []
    (conj (mk_eq(a,a)) (conj (forall_bool x (mk_eq(x,x))) (mk_eq(b,b))));
  check_saved "pftExport_vacuous$VACUOUS" [] (mk_const("T",[]));
  check_refl "pftExport_vacuous$UNUSED_REFL"
    (mk_const("pftExport_vacuous$unused",[]));
  let v = mk_var("pftExport_overlap$first",bool_ty) in
  let first = mk_const("pftExport_overlap$first",[]) in
  check_saved "pftExport_overlap$OVERLAP" []
    (forall_bool v (mk_eq(first,first)));
  let p = mk_eq(x,x) in
  let check name = check_saved ("pftExport_hypotheses$" ^ name) in
  check "CONJ_LEFT" [p] (conj p p);
  check "CONJ_RIGHT" [p] (conj p p);
  let truth = mk_const("T",[]) in
  check "MP" [truth] p;
  check "DISJ_CASES" [p;imp p p] p;
  let y = mk_var("y",bool_ty) in
  check "CHOOSE" [forall_bool y (imp (mk_comb(mk_abs(y,truth),y)) p)] p;
  let let_tm = inst [bool_ty,mk_vartype "'a";bool_ty,mk_vartype "'b"]
    (mk_const("LET",[])) in
  check_refl "pftExport_binder$LET" (mk_comb(let_tm,mk_abs(x,truth)));;

let check_oracle_results () =
  let v name = mk_var(name,bool_ty) in
  check_saved "oracle_hyps$hyps" [v "q";v "r"] (v "p");
  let lam = mk_abs(v "y",mk_eq(v "x",v "x pft%0")) in
  check_saved "oracle_hyps$capture" [mk_eq(lam,lam)] (v "p");
  let c = mk_const("oracle_hyps$c",[]) in
  List.iter (fun (name,ty) ->
    check_refl ("oracle_hyps$" ^ name) (inst [ty,mk_vartype "'a"] c))
    ["POLY_BOOL",bool_ty; "POLY_FUN",mk_fun_ty bool_ty bool_ty];
  check_refl "oracle_retired_instance$RESULT" (mk_const("T",[]));;

let term_kind_check () =
  let f = mk_var("f",mk_fun_ty bool_ty bool_ty) in
  let x = mk_var("x",bool_ty) in
  let y = mk_var("y",bool_ty) in
  List.iter (fun (name,tm) -> check_refl ("pft_term_kinds$" ^ name) tm)
    [("RENAME",mk_abs(f,mk_abs(f,x)));
     ("SPEC",mk_abs(f,mk_const("T",[])));
     ("EMPTY_BINDER",mk_abs(x,mk_abs(y,x)))];
  ignore (mk_mconst("pft_term_kinds$unused",bool_ty));;

let check_identity_results () =
  let n = mk_comb(mk_const("~",[]),mk_const("T",[])) in
  check_saved "identity_negation$NEGATION" [n] n;
  let stream = mk_type("identity_type_names$stream",[]) in
  let a = mk_var("a",stream) in
  let abs = mk_const("identity_type_names$stream_abs",[]) in
  let rep = mk_const("identity_type_names$stream_rep",[]) in
  let all = mk_mconst("!",mk_fun_ty (mk_fun_ty stream bool_ty) bool_ty) in
  check_saved "identity_type_names$RESULT" []
    (mk_comb(all,mk_abs(a,mk_eq(mk_comb(abs,mk_comb(rep,a)),a))));;

let check_compute_results () =
  let check name input result =
    check_saved ("pft_compute_binders$" ^ name) [] (mk_eq(input,result)) in
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
  let nested = let_tm x (let_tm y (add x y) (cvnum 4)) (cvnum 2) in
  check "CAPTURE" nested (cvnum 6);
  check "CLOSURE_NESTED"
    (let_tm x (add (cvnum 4) x) (cvnum 2)) (cvnum 6);
  let large = cvnum 18446744073709551616 in
  check "LARGE_NUMERAL" large large;
  let b = mk_type("bool",[]) in
  let f = mk_var("f",mk_fun_ty b b) in
  let v = mk_var("kind_x",b) in
  let abstraction = mk_abs(f,v) in
  let capture = mk_abs(f,abstraction) in
  check "KIND_CAPTURE" capture capture;;
