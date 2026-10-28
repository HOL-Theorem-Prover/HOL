(* Run after separate or merged Candle replay of the term-kind export. *)
let _ =
  let b = mk_type("bool",[]) in
  let f = mk_var("f",mk_fun_ty b b) in
  let x = mk_var("x",b) in
  let nested = mk_abs(f,mk_abs(f,x)) in
  let closed = mk_abs(f,mk_mconst("T",b)) in
  List.iter (fun (name,tm) ->
    let th = assoc ("pft_term_kinds$" ^ name) (!saved_ths) in
    if hyp th = [] && aconv (concl th) (mk_eq(tm,tm)) then
      print_endline ("TERM_KIND_CANDLE_EXACT " ^ name)
    else failwith ("term-kind sequent mismatch: " ^ name))
    [("RENAME",nested);("SPEC",closed)];
  ignore (mk_mconst("pft_term_kinds$unused",b));
  print_endline "TERM_KIND_CANDLE_ALL_EXACT_PASS";;
