(* Load after the PFT reader has replayed both specification fixtures. *)
let pft_export_check name expected =
  let th = assoc name (!saved_ths) in
  if hyp th = [] && aconv (concl th) expected then
    print_endline ("EXPORT_EXACT " ^ name)
  else failwith ("wrong replay sequent: " ^ name);;

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
  print_endline "EXPORTS_REPLAYED_EXACT";;
