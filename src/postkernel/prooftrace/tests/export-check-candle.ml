(* Load after the PFT reader has replayed all export fixtures. *)
let pft_export_check_hyps name expected_hyps expected =
  let th = assoc name (!saved_ths) in
  if length (hyp th) = length expected_hyps &&
     forall (fun h -> exists (aconv h) (hyp th)) expected_hyps &&
     aconv (concl th) expected then
    print_endline ("EXPORT_EXACT " ^ name)
  else failwith ("wrong replay sequent: " ^ name);;

let pft_export_check name expected =
  pft_export_check_hyps name [] expected;;

let _ =
  let x = mk_var ("x",bool_ty) in
  let a = mk_const ("pftExport_shadow$first",[]) in
  let b = mk_const ("pftExport_shadow$second",[]) in
  let and_tm = mk_const ("/\\",[]) in
  let conj p q = mk_comb (mk_comb (and_tm,p),q) in
  let forall_bool =
    inst [bool_ty,mk_vartype "'a"] (mk_const ("!",[])) in
  let inner = mk_comb (forall_bool,mk_abs (x,mk_eq (x,x))) in
  let expected = conj (mk_eq (a,a)) (conj inner (mk_eq (b,b))) in
  pft_export_check "pftExport_shadow$SHADOW" expected;
  pft_export_check "pftExport_vacuous$VACUOUS" (mk_const ("T",[]));
  let unused = mk_const ("pftExport_vacuous$unused",[]) in
  pft_export_check "pftExport_vacuous$UNUSED_REFL" (mk_eq (unused,unused));
  let v = mk_var ("pftExport_overlap$first",bool_ty) in
  let first = mk_const ("pftExport_overlap$first",[]) in
  let expected = mk_comb (forall_bool,mk_abs (v,mk_eq (first,first))) in
  pft_export_check "pftExport_overlap$OVERLAP" expected;
  let p = mk_eq (x,x) in
  let collision name hs tm =
    pft_export_check_hyps ("pftExport_hypotheses$" ^ name) hs tm in
  collision "CONJ_LEFT" [p] (conj p p);
  collision "CONJ_RIGHT" [p] (conj p p);
  let truth = mk_const ("T",[]) in
  collision "MP" [truth] p;
  let imp p q = mk_comb (mk_comb (mk_const ("==>",[]),p),q) in
  collision "DISJ_CASES" [p;imp p p] p;
  let y = mk_var ("y",bool_ty) in
  let guard = mk_comb (forall_bool,
    mk_abs (y,imp (mk_comb (mk_abs (y,truth),y)) p)) in
  collision "CHOOSE" [guard] p;
  let let_tm = inst [bool_ty,mk_vartype "'a";bool_ty,mk_vartype "'b"]
    (mk_const ("LET",[])) in
  let result = mk_comb (let_tm,mk_abs (x,truth)) in
  pft_export_check "pftExport_binder$LET" (mk_eq (result,result));
  print_endline "EXPORTS_REPLAYED_EXACT";;
