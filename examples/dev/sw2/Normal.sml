

(*
quietdec := true;

app load ["basic", "preProcess"];

open HolKernel Parse boolLib bossLib pairLib pairSyntax pairTheory PairRules basic preProcess;

quietdec := false;
*)

quietdec := true;

open HolKernel Parse boolLib bossLib pairLib pairSyntax pairTheory PairRules basic; (* preProcess; *)

quietdec := false;

(*---------------------------------------------------------------------------*)
(* Normalization                                                             *)
(* This intermediate language is a combination of K-normal forms             *)
(* and A-normal forms                                                        *)
(*---------------------------------------------------------------------------*)

val _ = (Globals.priming := SOME "");

(*---------------------------------------------------------------------------*)
(* Apply the continuation k to the expression e                              *)
(*---------------------------------------------------------------------------*)

val C_def = Define `
    C e = \k. k e`;

val atom_def = Define `
    atom = \x.x`;

val C_ATOM_INTRO = Q.store_thm (
  "C_ATOM_INTRO",
  `!v. C v = C (atom v)`,
  SIMP_TAC std_ss [atom_def, C_def]
 );

val ATOM_ID = Q.store_thm (
   "ATOM_ID",
   `atom x = x`,
   SIMP_TAC std_ss [atom_def]
  );

val C_ATOM = Q.store_thm (
  "C_ATOM",
  `C (atom v) =
      \k. k v`,
  SIMP_TAC std_ss [C_def, atom_def]
 );

val C_INTRO = Q.store_thm (
  "C_INTRO",
  `!f. f = C f (\x.x)`,
  SIMP_TAC std_ss [C_def, LET_THM]
 );

val C_2_LET = Q.store_thm (
  "C_2_LET",
  `(C e k = let x = e in k x)`,
  SIMP_TAC std_ss [C_def, atom_def, LET_THM]
 );

(*---------------------------------------------------------------------------*)
(* Convert an expression to it continuation format                           *)
(* Theorems used for rewriting                                               *)	
(*---------------------------------------------------------------------------*)

val C_BINOP = Q.store_thm (
  "C_BINOP",
   `(C (e1 + e2) = \k. C e1 (\x. C e2 (\y. C (x + y) k))) /\
    (C (e1 - e2) = \k. C e1 (\x. C e2 (\y. C (x - y) k))) /\
    (C (e1 * e2) = \k. C e1 (\x. C e2 (\y. C (x * y) k))) /\
    (C (e1 ** e2) = \k. C e1 (\x. C e2 (\y. C (x ** y) k)))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

val C_PAIR = Q.store_thm (
  "C_PAIR",
  `C (e1, e2) = \k. C e1 (\x. C e2 (\y. k (x,y)))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

(*  LET expressions are processed in a way that generate A-normal forms *)

val C_LET = Q.store_thm (
  "C_LET",
  `C (let v = e in f v) = \k. C e (\x. C (f x) (\y. k y))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

(*  For K-normal forms, use the following for LET expressions *)

val C_LET_K = Q.store_thm (
  "C_LET_K",
   `C (let v = e in f v) = \k. C e (\x. C x (\y. C (f y) (\z.k z)))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

val C_ABS = Q.store_thm (
  "C_ABS",
   `C (\v. f v) = C (\v. (C (f v) (\x. x)))`,
   RW_TAC std_ss [C_def, LET_THM]
  );

val C_APP = Q.store_thm (
  "C_APP",
   `C (f e) = \k. C f (\g. C e (\x. C (g x) (\y. k y)))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

val C_ATOM_COND = Q.store_thm (
  "C_ATOM_COND",
   `C (if cmpop c1 c2 then e1 else e2) = 
       \k. C c1 (\p. C c2 (\q.
         C (if cmpop p q then C e1 (\x.x) 
            else C e2 (\y.y)) (\z. k z)))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

(*
val C_COMPOUND_COND = Q.store_thm (
  "C_COMPOUND_COND",
   `C (if c1 /\ c2 then e1 else e2) = 
       \k. C c1 (\p. C c2 (\q. C e1 (\x. C e2 
           (\y. k (if p then 
                   if q then x else y
                   else y)))))`,
   RW_TAC std_ss [C_def, LET_THM] THEN
   METIS_TAC []
  );
*)

(*---------------------------------------------------------------------------*)
(* Convert an expression to it continuous form                               *)
(* Algorithm of the conversion                                               *)
(*---------------------------------------------------------------------------*)

(* Rewrite the first two components with the obtained theorems *)

fun SUBST_2_RULE (lem1,lem2) = 
         CONV_RULE (RHS_CONV (PABS_CONV (
                      RATOR_CONV (REWRITE_CONV [Once lem1]) THENC
                      RAND_CONV (PABS_CONV (RATOR_CONV (REWRITE_CONV [Once lem2]))))));

(* Rewrite the four components of atomic branch with the obtained theorems *)

fun Normalize_Atom_Cond (lem0,lem1,lem2,lem3) exp =
   let 
     val th1 =  ONCE_REWRITE_CONV [C_ATOM_COND] exp
     val th2 =  CONV_RULE (RHS_CONV (PABS_CONV (
                  RATOR_CONV (REWRITE_CONV [Once lem0]) THENC
                  RAND_CONV (PABS_CONV (
                    RATOR_CONV (REWRITE_CONV [Once lem1]) THENC
                    RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV (
                      RATOR_CONV (RAND_CONV (RATOR_CONV (REWRITE_CONV [Once lem2]))) THENC 
                      RAND_CONV (RATOR_CONV (REWRITE_CONV [Once lem3]))))))
                    ))
                 ))) th1
     val th3 = (PBETA_RULE o REWRITE_RULE [C_ATOM]) th2
   in
      th3
   end;

fun K_Normalize exp =
   let val (C, t) = dest_comb exp               (* eliminate the C *)
   in

   if is_atom t then 
      ISPEC t C_ATOM_INTRO

   else if is_let t then                        (*  exp = LET (\v. N) M  *)
     let 
         val (v,M,N) = dest_plet t
         val (th0, th1) = (K_Normalize (mk_comb (inst [alpha |-> type_of M] ``C``, M)), 
                           K_Normalize (mk_comb (inst [alpha |-> type_of N] ``C``, N)))
         val th2 =  SIMP_CONV bool_ss [Once C_LET] exp
         val th3 =  SUBST_2_RULE (th0,th1) th2
         val th4 = (PBETA_RULE o REWRITE_RULE [C_ATOM]) th3
     in
         th4
     end

    else if is_pabs t then                        (*  exp = \(x...).M *)
      let 
         val (v,M) = dest_pabs t
	 val (v_type, m_type) = (type_of v, type_of M);
	 val t1 = mk_comb (inst [alpha |-> m_type] ``C``, M);
	 val t2 = mk_comb (inst [beta |-> m_type] t1, inst [alpha |-> m_type] ``\x.x``);
         val t3 = mk_comb (C, mk_pabs(v, t2));
	 val th1 = prove (mk_eq(exp, t3), SIMP_TAC std_ss [C_def]);
         val th0 = K_Normalize (mk_comb (inst [alpha |-> type_of M] ``C``, M))

         val th2 = CONV_RULE (RHS_CONV (RAND_CONV (PABS_CONV (
                      RATOR_CONV (ONCE_REWRITE_CONV [th0]))))) th1
         val th3 = (PBETA_RULE o REWRITE_RULE [C_ATOM]) th2
      in
         th3
      end

    else if is_pair t then                        (*  exp = (M,N) *)
      let 
         val (M,N) = dest_pair t
         val (th0, th1) = (K_Normalize (mk_comb (inst [alpha |-> type_of M] ``C``, M)), 
                           K_Normalize (mk_comb (inst [alpha |-> type_of N] ``C``, N)))

         val th2 =  ONCE_REWRITE_CONV [C_PAIR] exp
         val th3 =  SUBST_2_RULE (th0,th1) th2
         val th4 = (PBETA_RULE o REWRITE_RULE [C_ATOM]) th3
      in
         th4
      end

    else if is_cond t then                        (*  exp = if P then M else N *)
      let 
         val (J,M,N) = dest_cond t
      in 
         if is_atom_cond J then
           let 
              val (op0, xL) = strip_comb J 
              val (P,Q) = (hd xL, hd (tl xL))
              val (lem0, lem1, lem2, lem3) = 
                 (K_Normalize (mk_comb (inst [alpha |-> type_of P] ``C``, P)),
                  K_Normalize (mk_comb (inst [alpha |-> type_of Q] ``C``, Q)), 
                  K_Normalize (mk_comb (inst [alpha |-> type_of M] ``C``, M)), 
                  K_Normalize (mk_comb (inst [alpha |-> type_of N] ``C``, N)))

              val th4 = Normalize_Atom_Cond (lem0,lem1,lem2,lem3) exp
           in
              th4
           end

        else 
          REFL exp
      end

   else if is_comb t then
      let val (operator, operands) = strip_comb t
      in

        if is_binop operator then (* Arithmetic and Logical Operations *)
             let 
               val (d0, d1) =  (hd operands, hd (tl operands))
               val (th0, th1) = (K_Normalize (mk_comb (inst [alpha |-> type_of d0] ``C``, d0)),
                                 K_Normalize (mk_comb (inst [alpha |-> type_of d1] ``C``, d1)))
               val th2 =  ONCE_REWRITE_CONV [C_BINOP] exp
	       val th3 =  SUBST_2_RULE (th0,th1) th2
               val th4 = (PBETA_RULE o REWRITE_RULE [C_ATOM]) th3
             in
                th4
             end

        else (* Application *)
           let
             val (M,N) = dest_comb t
             val (th0, th1) = (K_Normalize (mk_comb (inst [alpha |-> type_of M] ``C``, M)), 
                               K_Normalize (mk_comb (inst [alpha |-> type_of N] ``C``, N)))
             val th2 = ONCE_REWRITE_CONV [C_APP] exp
             val th3 =  SUBST_2_RULE (th0,th1) th2
             val th4 = (PBETA_RULE o REWRITE_RULE [C_ATOM]) th3
           in
             th4
           end
      end

    else
     REFL exp
  end

(*---------------------------------------------------------------------------*)
(*   Convert a function to its equivalent KNF                                *)
(*---------------------------------------------------------------------------*)

fun normalize def = 
  let 
    val thm0 = SIMP_RULE arith_ss [] def                     (* Basic simplification *)
    val thm1 = REWRITE_RULE [AND_COND, OR_COND] thm0         (* Break compound condition jumps *)
    val thm2 = CONV_RULE (RHS_CONV (ONCE_REWRITE_CONV [C_INTRO])) (SPEC_ALL thm1)
    val exp = #1 (dest_comb (rhs (concl thm2)))
    val lem3 = K_Normalize exp                               (* Continuation Norm *)
    val thm4 = REWRITE_RULE [lem3] thm2
    val thm5 = SIMP_RULE bool_ss [C_2_LET] thm4              (* "Let" Form *)
    val thm6 = REWRITE_RULE [BRANCH_NORM] thm5       
  in
    thm6
  end

(*---------------------------------------------------------------------------*)
(* Beta-Reduction on Let expressions (rule "atom_let")                       *)
(* Reduce expressions such as let x = y in x + y to y + y, expanding         *)
(* the aliasing of variables                                                 *)
(*---------------------------------------------------------------------------*)

fun identify_atom tm = 
  let 
     fun trav t = 
       if is_let t then 
           let val (v,M,N) = dest_plet t
               val M' = if is_atom M then mk_comb (inst [alpha |-> type_of M] (Term `atom`), M) 
                        else trav M
           in mk_plet (v, M', trav N)
           end
       else if is_comb t then
            let val (M1,M2) = dest_comb t
                val M1' = trav M1
                val M2' = trav M2 
            in mk_comb(M1',M2')
            end
       else if is_pabs t then 
           let val (v,M) = dest_pabs t
           in mk_pabs(v,trav M)
           end 
       else t
  in 
    trav tm
  end;

val BETA_REDUCTION = Q.store_thm (
   "BETA_REDUCTION",
   `(let x = atom y in f x) = f y`,
   SIMP_TAC std_ss [atom_def, LET_THM]
  );

fun beta_reduction def = 
  let
    val t0 = rhs (concl (SPEC_ALL def))
    val t1 = identify_atom t0
    val lem0 = REFL t1
    val lem1 = CONV_RULE (LHS_CONV (REWRITE_CONV [ATOM_ID])) lem0
    val thm1 = ONCE_REWRITE_RULE [lem1] def
    val thm2 = SIMP_RULE bool_ss [BETA_REDUCTION] thm1
  in
    thm2
  end

(*---------------------------------------------------------------------------*)
(* Elimination of Unnecessary Definitions                                    *)
(* If e1 has no side effect and x does not appear free in                    *)
(* e2, we can replace let x = e1 in e2 just with e2.                         *)
(*---------------------------------------------------------------------------*)

val ELIM_USELESS_LET = Q.store_thm (
  "ELIM_USELESS_LET",
   `(let x = e1 in e2) = e2`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

val ELIM_LET_RULE = 
    SIMP_RULE bool_ss [ELIM_USELESS_LET]

(*---------------------------------------------------------------------------*)
(* Elimination of Unnecessary Definitions                                    *)
(* If e1 has no side effect and x does not appear free in                    *)
(* e2, we can replace let x = e1 in e2 just with e2.                         *)
(*---------------------------------------------------------------------------*)

val FLATTEN_LET = Q.store_thm (
  "FLATTEN_LET",
   `(let x = (let y = e1 in e2 y) in e3 x) = (let y = e1 in let x = e2 y in e3 x)`,
   SIMP_TAC std_ss [LET_THM]
  );

val FLATTEN_LET_RULE = 
    SIMP_RULE std_ss [FLATTEN_LET]

(*---------------------------------------------------------------------------*)
(* Convert the normal form into SSA form                                     *)
(* Ensure that each let-bound variable name in a term is different than the  *)
(* others.                                                                   *)
(*---------------------------------------------------------------------------*)

fun to_ssa stem tm = 
 let open Lib
     fun num2name i = stem^Lib.int_to_string i
     val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
     fun next_name () = state(next nameStrm)
     fun trav M = 
       if is_comb M then 
            let val (M1,M2) = dest_comb M
                val M1' = trav M1
                val M2' = trav M2 
            in mk_comb(M1',M2')
            end else 
       if is_pabs M then 
           let val (v,N) = dest_pabs(rename_bvar (next_name()) M)
           in mk_pabs(v,trav N)
           end
       else M
 in 
   trav tm
 end; 

fun SSA_CONV tm = 
  let val tm' = to_ssa "v" tm
  in Thm.ALPHA tm tm'
  end;

fun SSA_RULE def = 
  let 
      val t0 = concl (SPEC_ALL def)
      val (t1,t2) = (lhs t0, rhs t0)
      val flag = is_pabs t2
      val (fname, args) = 
          if is_comb t1 then dest_comb t1
          else (t1, #1 (dest_pabs t2)) 
      val body = if flag then #2 (dest_pabs t2) else t2 
      val lem1 = prove (mk_eq (fname, mk_pabs(args,body)), 
		    SIMP_TAC std_ss [FUN_EQ_THM, FORALL_PROD, Once def]);
      val t3 = if flag then t2 else mk_pabs (args,body) 
      val lem2 = SSA_CONV t3;
      val lem3 = ONCE_REWRITE_RULE [lem2] lem1
  in
    lem3
  end

(*---------------------------------------------------------------------------*)
(* Normalized forms with after a series of optimizations                     *)
(*---------------------------------------------------------------------------*)

