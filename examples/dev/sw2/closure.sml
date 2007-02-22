
(*---------------------------------------------------------------------------*)
(* Closure conversion                                                        *)
(* Eliminate nested function definitions                                     *)
(*---------------------------------------------------------------------------*)

val CLOSE_ONE = store_thm (
  "CLOSE_ONE",
  ``(let v = atom v in let f = fun (e1 v) in e2 f) = 
    let f = fun (\v. e1 v) in e2 (f v)``,
   SIMP_TAC std_ss [LET_THM, fun_def, atom_def]
  );

(*---------------------------------------------------------------------------*)
(* Eliminate administrative terms                                            *)
(*---------------------------------------------------------------------------*)

val LET_ATOM = store_thm (
  "LET_ATOM",
  ``(let x = atom x in f x) = f x``,
   SIMP_TAC std_ss [LET_THM, atom_def]
  );

val LET_FUN = store_thm (
  "LET_FUN",
  ``(let f = fun e1 in e2 f) = e2 e1``,
   SIMP_TAC std_ss [LET_THM, fun_def]
  );

(*---------------------------------------------------------------------------*)
(* Close the function variable by variable                                   *)
(* Consider a free variable each time                                        *)
(*---------------------------------------------------------------------------*)

fun abs_fvars tm = 
  let 
     fun close_up f body = 
       List.foldl (fn (v,t) => mk_plet (v, mk_comb (inst [alpha |-> type_of v] ``atom``, v), t)) f (free_vars body)
     fun trav t = 
       if is_let t then 
           let val (v,M,N) = dest_plet t in
               if is_pabs M then 
                 close_up (mk_plet (v, mk_comb (inst [alpha |-> type_of M] ``fun``, trav M), trav N)) M 
               else mk_plet (v, trav M, trav N)
           end
       else if is_cond t then
           let val (J,M,N) = dest_cond t in
             mk_cond (J, trav M, trav N)
           end
       else if is_pabs t then
            let val (M,N) = dest_pabs t in
            mk_pabs (trav M, trav N) end
       else t
  in 
    trav tm
  end;

fun close_one_by_one def = 
  let
    val th1 = abs_fun def
    val body = rhs (concl th1)
    val t1 = abs_fvars body
    val th2 = CONV_RULE (LHS_CONV (SIMP_CONV bool_ss [fun_def]))
          (GSYM (SIMP_CONV std_ss [LET_ATOM] t1))
    val th3 = ONCE_REWRITE_RULE [th2] th1          (* abs forms *)
    val th4 = CONV_RULE (RHS_CONV (SIMP_CONV bool_ss [CLOSE_ONE])) th3
  in
    th4
  end

(*---------------------------------------------------------------------------*)
(* Close the function variable by variable                                   *)
(* Consider all free variable each time                                      *)
(*---------------------------------------------------------------------------*)

fun identify_fun tm = 
  let 
     fun trav t = 
       if is_let t then 
           let val (v,M,N) = dest_plet t in
               if is_pabs M then 
                 mk_plet (v, mk_comb (inst [alpha |-> type_of M] ``fun``, trav M), trav N) 
               else mk_plet (v, trav M, trav N)
           end
       else if is_cond t then
           let val (J,M,N) = dest_cond t in
             mk_cond (J, trav M, trav N)
           end
       else if is_pabs t then
            let val (M,N) = dest_pabs t in
            mk_pabs (trav M, trav N) end
       else t
  in 
    trav tm
  end;

fun abs_all_fvars tm = 
  let 
     fun trav t = 
       if is_let t then 
           let val (v,M,N) = dest_plet t in
               if is_pabs M then 
                  let val cls = list_mk_pair (free_vars M) 
                      val (args, d) = dest_pabs M
                      val (M',N') = (trav M, trav N)
                      val f = mk_pabs (cls, M')
                      val v' = (mk_var (term_to_string v, type_of f))
                      val f' = mk_comb (inst [alpha |-> type_of f] ``fun``, f)
                      val N'' = subst_exp [v |-> mk_comb (v', cls)] N'
                  in
                     mk_plet (v', f', N'')
                  end 
               else mk_plet (v, trav M, trav N)
           end
       else if is_cond t then
           let val (J,M,N) = dest_cond t in
             mk_cond (J, trav M, trav N)
           end
       else if is_pabs t then
            let val (M,N) = dest_pabs t in
            mk_pabs (trav M, trav N) end
       else t
  in 
    trav tm
  end;

fun close_all def = 
  let
    val th1 = abs_fun def
    val body = rhs (concl th1)
    val t1 = abs_all_fvars body
    val th2 = GSYM (PBETA_RULE (SIMP_CONV pure_ss [INLINE_EXPAND] t1))
    val t2 = identify_fun body
    val th3 = PBETA_RULE (CONV_RULE (RHS_CONV (SIMP_CONV bool_ss [LET_FUN])) (REFL t2))
    val th4 = TRANS th3 th2
    val th5 = TRANS th1 (CONV_RULE (LHS_CONV (SIMP_CONV bool_ss [fun_def])) th4)
  in
    th5
  end

(*---------------------------------------------------------------------------*)
(*   Closure conversion                                                      *)
(*   Move all functions definitions to top level                             *)  
(*---------------------------------------------------------------------------*)

val TOP_LEVEL_ABS = store_thm (
  "TOP_LEVEL",
  ``(\x. let f = fun e1 in e2 f) = (let f = fun e1 in (\x. e2 f))``,
   SIMP_TAC std_ss [LET_THM]
  );

val TOP_LEVEL_LET = store_thm (
  "TOP_LEVEL_LET",
  ``(let v = e1 in let f = fun e2 in e3 v f) = 
    (let f = fun e2 in let v = e1 in e3 v f)``,
   SIMP_TAC std_ss [LET_THM]
  );

val TOP_LEVEL_COND_1 = store_thm (
  "TOP_LEVEL_COND_1",
  ``(if e1 then let f = fun k1 in e2 f else e3) = 
        (let f = fun k1 in if e1 then e2 f else e3)``,
   SIMP_TAC std_ss [LET_THM]
  );

val TOP_LEVEL_COND_2 = store_thm (
  "TOP_LEVEL_COND_2",
  ``(if e1 then e2 else let f = fun k1 in e3 f) =
        (let f = fun k1 in if e1 then e2 else e3 f)``,
   SIMP_TAC std_ss [LET_THM]
  );

val TOP_LEVEL_RULE = SIMP_RULE pure_ss [TOP_LEVEL_LET, TOP_LEVEL_COND_1, TOP_LEVEL_COND_2];
 (* may loop forever, to be improved *)

(*---------------------------------------------------------------------------*)
(*   Closure conversion                                                      *)
(*   Interface                                                               *)  
(*---------------------------------------------------------------------------*)

fun closure_convert def = 
  let 
    val th1 = close_all def
    val th2 = TOP_LEVEL_RULE th1
    val th3 = SIMP_RULE pure_ss [FLATTEN_LET] th2
    val th4 = SSA_RULE th3
  in
    th4
  end
