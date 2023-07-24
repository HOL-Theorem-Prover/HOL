(*****************************************************************************)
(* Very simple compiler, with programs represented as ML list of HOL         *)
(* definitions.                                                              *)
(*****************************************************************************)

structure compile :> compile =
struct

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)
(******************************************************************************
* Load theories
******************************************************************************)
(*
quietdec := true;
loadPath :="dff" :: !loadPath;
app load ["composeTheory","compileTheory", "unwindLib", "wordsLib"];
open arithmeticTheory pairLib pairTheory PairRules pairSyntax
     combinTheory listTheory unwindLib composeTheory compileTheory;
open wordsTheory wordsLib;

quietdec := false;
*)

(******************************************************************************
 * Boilerplate needed for compilation
 ******************************************************************************)

open HolKernel Parse boolLib bossLib;

(******************************************************************************
 * Open theories
 ******************************************************************************)

open arithmeticTheory pairLib pairTheory PairRules pairSyntax
     combinTheory listTheory unwindLib composeTheory compileTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Error reporting function                                                  *)
(*****************************************************************************)

val ERR = mk_HOL_ERR "compile";

(*****************************************************************************)
(* List of definitions (useful for rewriting)                                *)
(*****************************************************************************)

val SimpThms = [Seq_def,Par_def,Ite_def,Rec_def];

(*---------------------------------------------------------------------------*)
(* Make an application TOTAL f1 f2 f3                                        *)
(*---------------------------------------------------------------------------*)

val total_tm = prim_mk_const{Name="TOTAL",Thy="compose"};

fun mk_total (tm1,tm2,tm3) =
 let val ty1 = fst(dom_rng(type_of tm1))
     val ty2 = type_of tm2
 in
   mk_comb(inst[alpha |-> ty1, beta |-> ty2] total_tm,
           pairLib.list_mk_pair[tm1,tm2,tm3])
 end;

(*****************************************************************************)
(* Destruct ``d1 ===> d2`` into (``d1``,``d2``)                              *)
(*****************************************************************************)

fun dest_dev_imp tm =
 if is_comb tm
     andalso is_comb(rator tm)
     andalso is_const(rator(rator tm))
     andalso (fst(dest_const(rator(rator tm))) = "DEV_IMP")
  then (rand(rator tm), rand tm)
  else raise ERR "dest_dev_imp" "attempt to dest a non-DEV";

(*****************************************************************************)
(* An expression is just a HOL term built using expressions defined earlier  *)
(* in a program (see description of programs below) and Seq, Par,            *)
(* Ite and Rec:                                                              *)
(*                                                                           *)
(*  expr := Seq expr expr                                                    *)
(*        | Par expr expr                                                    *)
(*        | Ite expr expr expr                                               *)
(*        | Rec expr expr expr                                               *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Convert_CONV ``\(x1,...,xn). tm[x1,...,xn]`` returns a theorem            *)
(*                                                                           *)
(*  |- (\(x1,...,xn). tm[x1,...,xn]) = p                                     *)
(*                                                                           *)
(* where p is a combinatory expression built from the combinators            *)
(* Seq, Par and Ite. An example is:                                          *)
(*                                                                           *)
(*  - Convert_CONV ``\(x,y). if x < y then y-x else x-y``;                   *)
(* > val it =                                                                *)
(*     |- (\(x,y). (if x < y then y - x else x - y)) =                       *)
(*        Ite (Seq (Par (\(x,y). x) (\(x,y). y)) (UNCURRY $<))               *)
(*            (Seq (Par (\(x,y). y) (\(x,y). x)) (UNCURRY $-))               *)
(*            (Seq (Par (\(x,y). x) (\(x,y). y)) (UNCURRY $-))               *)
(*                                                                           *)
(* Notice that curried operators are uncurried.                              *)
(*                                                                           *)
(*****************************************************************************)

val LET_SEQ_PAR_THM = Q.prove
(`!f1 f2 f3. Seq (Par f1 f2) f3 = \x. let v = f2 x in f3 (f1 x,v)`,
 RW_TAC std_ss [Seq_def, Par_def, LET_DEF]);

val SEQ_PAR_I_THM = Q.prove
(`!f2 f3. Seq (Par (\x.x) f2) f3 = \x. let v = f2 x in f3 (x,v)`,
 RW_TAC std_ss [LET_SEQ_PAR_THM,combinTheory.I_THM]);

fun Convert_CONV f =
 let val (args,t) =
         dest_pabs f
         handle HOL_ERR _
          => (print_term f; print"\n";
              print "is not an abstraction\n";
              raise ERR "Convert_CONV" "not an abstraction")
  in
  if not(null (free_vars f))
  then (print_term f; print "\n";
        print "has free variables: ";
        map (fn t => (print_term t; print " "))(rev(free_vars f)); print "\n";
        raise ERR "Convert_CONV" "disallowed free variables")
  else if null(free_vars t) orelse is_var t
   then REFL f
  else if is_pair t
   then let val (t1,t2) = dest_pair t
            val f1 = mk_pabs(args,t1)
            val f2 = mk_pabs(args,t2)
            val th1 = PBETA_CONV (mk_comb(f1,args))
            val th2 = PBETA_CONV (mk_comb(f2,args))
            val th3 = ISPECL [f1,f2] Par_def
            val ptm = mk_pabs(args, mk_pair(mk_comb(f1,args),mk_comb(f2,args)))
            val th4 = TRANS th3 (PALPHA  (rhs(concl th3)) ptm)
            val th5 = CONV_RULE
                       (RHS_CONV
                         (PABS_CONV
                           (RAND_CONV(REWR_CONV th2)
                             THENC RATOR_CONV(RAND_CONV(REWR_CONV th1)))))
                       th4
            val th6 = GSYM th5
        in
         if aconv (lhs(concl th6)) f
          then CONV_RULE
                (RHS_CONV
                  ((RAND_CONV Convert_CONV)
                   THENC (RATOR_CONV(RAND_CONV Convert_CONV))))
                th6
          else (print "bad Par case\n";
                raise ERR "Convert_CONV" "shouldn't happen")
        end
  else if is_cond t
   then let val (b,t1,t2) = dest_cond t
            val fb = mk_pabs(args,b)
            val f1 = mk_pabs(args,t1)
            val f2 = mk_pabs(args,t2)
            val thb = PBETA_CONV (mk_comb(fb,args))
            val th1 = PBETA_CONV (mk_comb(f1,args))
            val th2 = PBETA_CONV (mk_comb(f2,args))
            val th3 = ISPECL [fb,f1,f2] Ite_def
            val ptm = mk_pabs
                       (args,
                        mk_cond(mk_comb(fb,args),mk_comb(f1,args),mk_comb(f2,args)))
            val th4 = TRANS th3 (PALPHA  (rhs(concl th3)) ptm)
            val th5 = CONV_RULE
                       (RHS_CONV
                         (PABS_CONV
                           (RAND_CONV(REWR_CONV th2)
                             THENC RATOR_CONV(RAND_CONV(REWR_CONV th1))
                             THENC RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV thb))))))
                       th4
            val th6 = GSYM th5
        in
         if aconv (lhs(concl th6)) f
          then CONV_RULE
                (RHS_CONV
                  ((RAND_CONV Convert_CONV)
                   THENC (RATOR_CONV(RAND_CONV Convert_CONV))
                   THENC (RATOR_CONV(RATOR_CONV(RAND_CONV Convert_CONV)))))
                th6
          else (print "bad Ite case\n";
                raise ERR "Convert_CONV" "shouldn't happen")
        end
  else if is_let t   (*  t = LET (\v. N) M  *)
   then let val (v,M,N) = dest_plet t
            val f1 = mk_pabs(args,M)
            val f2 = mk_pabs(mk_pair(args,v),N)
            val th1 = ISPECL [f1,f2] Let_def
            val th2 = CONV_RULE(RHS_CONV(SIMP_CONV std_ss [LAMBDA_PROD])) th1
            val th3 = TRANS th2 (SYM (QCONV (SIMP_CONV std_ss [LAMBDA_PROD]) f))
            val th4 = SYM th3
        in
         if aconv (lhs(concl th4)) f
          then CONV_RULE
                (RHS_CONV
                  ((RAND_CONV Convert_CONV)
                   THENC RATOR_CONV(RAND_CONV Convert_CONV)))
                th4
          else (print "bad let case\n";
                raise ERR "Convert_CONV" "shouldn't happen")
        end
(*  else if is_let t   (*  t = LET (\v. N) M  *)
   then let val (v,M,N) = dest_plet t
            val f1 = mk_pabs(args,args)
            val f2 = mk_pabs(args,M)
            val f3 = mk_pabs(mk_pair(args,v),N)
            val th1 = ISPECL [f1,f2,f3] LET_SEQ_PAR_THM
            val th2 = CONV_RULE(RHS_CONV(SIMP_CONV std_ss [LAMBDA_PROD])) th1
            val th3 = TRANS th2 (SYM (QCONV (SIMP_CONV std_ss [LAMBDA_PROD]) f))
            val th4 = SYM th3
        in
         if aconv (lhs(concl th4)) f
          then CONV_RULE
                (RHS_CONV
                  ((RAND_CONV Convert_CONV)
                   THENC (RATOR_CONV(RAND_CONV (RAND_CONV Convert_CONV)))))
                th4
          else (print "bad let case\n";
                raise ERR "Convert_CONV" "shouldn't happen")
        end
*)

  else if is_comb t
   then let val th0 = (REWR_CONV (GSYM UNCURRY_DEF) ORELSEC REFL) t
            val (t1,t2) = dest_comb(rhs(concl th0))
            val f1 = mk_pabs(args,t1)
            val f2 = mk_pabs(args,t2)
            val th1 = ISPECL [f2,t1] Seq_def
            val ptm = mk_pabs(args, mk_comb(t1,mk_comb(f2,args)))
            val th2 = TRANS th1 (PALPHA (rhs(concl th1)) ptm)
            val th3 = PBETA_CONV(mk_comb(f2,args))
            val th4 = GSYM(CONV_RULE(RHS_CONV(PABS_CONV(RAND_CONV(REWR_CONV th3))))th2)
            val th5 = CONV_RULE(LHS_CONV(PABS_CONV(REWR_CONV(GSYM th0)))) th4
        in
         if aconv (lhs(concl th5)) f
          then CONV_RULE
                (RHS_CONV
                  (RATOR_CONV(RAND_CONV Convert_CONV)))
                th5
          else (print "bad Seq case\n";
                raise ERR "Convert_CONV" "shouldn't happen")
        end
  else (print_term f; print "\n";
        print "shouldn't get this case (not first-order)!\n";
        raise ERR "Convert_CONV" "shouldn't happen")
 end;

(*****************************************************************************)
(* Predicate to test whether a term occurs in another term                   *)
(*****************************************************************************)

fun occurs_in t1 t2 = can (find_term (aconv t1)) t2;

(*****************************************************************************)
(* Convert (|- f x = e) returns a theorem                                    *)
(*                                                                           *)
(*  |- f = p                                                                 *)
(*                                                                           *)
(* where p is a combinatory expression built from the combinators Seq, Par   *)
(* and Ite.                                                                  *)
(*****************************************************************************)

fun Convert defth =
 let val (lt,rt) =
         dest_eq(concl(SPEC_ALL defth))
         handle HOL_ERR _
         => (print "not an equation\n";
             raise ERR "Convert" "not an equation")
 in
  if is_const lt
   then defth
   else
   let  val (func,args) =
            dest_comb lt
            handle HOL_ERR _ =>
            (print "lhs not a comb\n";
             raise ERR "Convert" "lhs not a comb")
        val _ = if not(is_const func)
                 then (print_term func; print " is not a constant\n";
                       raise ERR "Convert" "rator of lhs not a constant")
                 else ()
        val _ = if not(null (op_set_diff aconv (free_vars rt) (free_vars lt)))
                 then (print "definition rhs has unbound variables: ";
                       map (fn t => (print_term t; print " "))
                           (rev
                              (op_set_diff aconv (free_vars rt) (free_vars lt)));
                       print "\n";
                       raise ERR "Convert" "definition rhs has unbound variables")
                 else ()
    in
     let val f = mk_pabs(args,rt)
         val th1 = Convert_CONV f
         val th2 = PABS args (SPEC_ALL defth)
         val th3 = TRANS th2 th1
     in
      CONV_RULE (LHS_CONV PETA_CONV) th3
     end
    end
 end;

(*****************************************************************************)
(* RecConvert (|- f x = if f1 x then f2 x else f(f3 x)) (|- TOTAL(f1,f2,f3)) *)
(* returns a theorem                                                         *)
(*                                                                           *)
(*  |- f = Rec(p1,p2,p3)                                                     *)
(*                                                                           *)
(* where p1, p2 and p3 are combinatory expressions built from the            *)
(* combinators Seq, Par and Ite.                                             *)
(*                                                                           *)
(* For example, given:                                                       *)
(*                                                                           *)
(*  FactIter;                                                                *)
(*  > val it =                                                               *)
(*      |- FactIter (n,acc) =                                                *)
(*         (if n = 0 then (n,acc) else FactIter (n - 1,n * acc))             *)
(*                                                                           *)
(*  - FactIter_TOTAL;                                                        *)
(*  > val it =                                                               *)
(*      |- TOTAL                                                             *)
(*           ((\(n,acc). n = 0),                                             *)
(*            (\(n,acc). (n,acc)),                                           *)
(*            (\(n,acc). (n - 1,n * acc)))                                   *)
(*                                                                           *)
(* then:                                                                     *)
(*                                                                           *)
(*  - RecConvert FactIter FactIter_TOTAL;                                    *)
(* > val it =                                                                *)
(*     |- FactIter =                                                         *)
(*        Rec (Seq (Par (\(n,acc). n) (\(n,acc). 0)) (UNCURRY $=))           *)
(*            (Par (\(n,acc). n) (\(n,acc). acc))                            *)
(*            (Par (Seq (Par (\(n,acc). n) (\(n,acc). 1)) (UNCURRY $-))      *)
(*                (Seq (Par (\(n,acc). n) (\(n,acc). acc)) (UNCURRY $* )))   *)
(*                                                                           *)
(*****************************************************************************)

fun RecConvert defth totalth =
 let val (lt,rt) =
         dest_eq(concl(SPEC_ALL defth))
         handle HOL_ERR _
         => (print "not an equation\n";
             raise ERR "RecConvert" "not an equation")
     val (func,args) =
         dest_comb lt
         handle HOL_ERR _ =>
         (print "lhs not a comb\n";
          raise ERR "RecConvert" "lhs not a comb")
     val _ = if not(is_const func)
              then (print_term func; print " is not a constant\n";
                    raise ERR "RecConvert" "rator of lhs not a constant")
              else ()
     val (b,t1,t2) =
         dest_cond rt
         handle HOL_ERR _
         => (print "rhs not a conditional\n";
             raise ERR "RecConvert" "rhs not a conditional")
     val rml = HOLset.difference(FVs rt, FVs lt)
     val _ = if not(HOLset.isEmpty rml)
              then (print "definition rhs has unbound variables: ";
                    HOLset.app (fn t => (print_term t; print " ")) rml;
                    print "\n";
                    raise ERR "RecConvert" "definition rhs has unbound variables")
              else()
 in
  if (is_comb t2
       andalso aconv (rator t2) func
       andalso not(occurs_in func b)
       andalso not(occurs_in func t1)
       andalso not(occurs_in func (rand t2)))
  then
   let val fb = mk_pabs(args,b)
       val f1 = mk_pabs(args,t1)
       val f2 = mk_pabs(args,rand t2)
       val _  = if aconv (concl(SPEC_ALL totalth)) (mk_total(fb,f1,f2))
                 then ()
                 else (print "bad TOTAL theorem\n";
                       raise ERR "RecConvert" "bad TOTAL theorem")
       val thb = PBETA_CONV (mk_comb(fb,args))
       val th1 = PBETA_CONV (mk_comb(f1,args))
       val th2 = PBETA_CONV (mk_comb(f2,args))
       val th3 = SPEC func (MATCH_MP TOTAL_THM totalth)
       val ptm = mk_pforall
                  (args,
                   mk_eq
                    (mk_comb(func,args),
                      mk_cond
                       (mk_comb(fb,args),
                        mk_comb(f1,args),
                        mk_comb(func,mk_comb(f2,args)))))
       val th4 = CONV_RULE
                    (RATOR_CONV
                      (RAND_CONV
                        (REWR_CONV(PALPHA  (fst(dest_imp(concl th3))) ptm))))
                    th3
       val th5 = REWRITE_RULE [thb,th1,th2] th4
       val th6 = MP th5 (PGEN args (SPEC_ALL defth))
   in
    CONV_RULE
     (RHS_CONV
      ((RAND_CONV Convert_CONV)
        THENC (RATOR_CONV(RAND_CONV Convert_CONV))
        THENC (RATOR_CONV(RATOR_CONV(RAND_CONV Convert_CONV)))))
     th6
   end
  else if occurs_in func rt
   then (print "definition of: "; print_term func;
         print " is not tail recursive"; print "\n";
         raise ERR "RecConvert" "not tail recursive")
   else raise ERR "RecConvert" "this shouldn't happen"
 end;

(*---------------------------------------------------------------------------*)
(* Extract totality predicate of the form TOTAL (f1,f2,f3) for a recursive   *)
(* function of the form f(x) = if f1(x) then f2(x) else f (f3(x))            *)
(*---------------------------------------------------------------------------*)

fun getTotal def =
 let val (lt,rt) = boolSyntax.dest_eq(concl (SPEC_ALL def))
     val (func,args) = dest_comb lt
     val (b1,t1,t2) = dest_cond rt
     val fb = mk_pabs(args,b1)
     val f1 = mk_pabs(args,t1)
     val f2 = mk_pabs(args,rand t2)
 in
   mk_total(fb,f1,f2)
 end
 handle e as HOL_ERR _ => raise wrap_exn "getTotal" "failed" e;



(*****************************************************************************)
(* Check if term tm is a well-formed expression built out of Seq, Par, Ite,  *)
(* Rec or Let. If so return a pair (constructor, args), else return (tm,[])  *)
(*****************************************************************************)

fun dest_exp tm =
 if not(fst(dest_type(type_of tm)) = "fun")
  then (print_term tm;print "\n";
        print "is not a function\n";
        raise ERR "dest_exp" "dest_exp failure")
  else if is_comb tm
          andalso is_const(fst(strip_comb tm))
          andalso mem
                   (fst(dest_const(fst(strip_comb tm))))
                   ["Seq","Par","Ite","Rec","Let"]
  then
   let val (opr,args) = strip_comb tm
   in
   case fst(dest_const opr) of
      "Seq" => if length args = 2
                then (opr, args)
                else raise ERR "dest_exp" "bad Seq"
    | "Par" => if length args = 2
                then (opr, args)
                else raise ERR "dest_exp" "bad Par"
    | "Ite" => if length args = 3
                then (opr, args)
                else raise ERR "dest_exp" "bad Ite"
    | "Rec" => if length args = 3
                then (opr, args)
                else raise ERR "dest_exp" "bad Rec"
    | "Let" => if length args = 2
                then (opr, args)
                else raise ERR "dest_exp" "bad Let"
    | _     => raise ERR "dest_exp" "this shouldn't happen"
   end
  else (tm,[]);

(*****************************************************************************)
(* A combinational term is one that only contains constants declared         *)
(* combinational by having their names included in the assignable list       *)
(* combinational_constants                                                   *)
(*****************************************************************************)

val combinational_constants =
 ref["T","F","/\\","\\/","~",",","o","CURRY","UNCURRY","COND",
     "FST","SND","=","Seq","Par","Ite","Let",
     "0","NUMERAL","BIT1","BIT2","ZERO","+","-"];

fun add_combinational l =
 (combinational_constants := union l (!combinational_constants));

fun is_combinational tm =
 is_var tm
  orelse (is_const tm
           andalso  mem (fst(dest_const tm))  (!combinational_constants))
  orelse (is_abs tm
           andalso is_combinational(body tm))
  orelse (is_comb tm
           andalso is_combinational(rator tm)
           andalso is_combinational(rand tm));

(*****************************************************************************)
(* Test if a term is built from combinational constants using only           *)
(* function application.                                                     *)
(*****************************************************************************)

fun is_combinational_const tm =
 (is_const tm andalso  mem (fst(dest_const tm))  (!combinational_constants))
  orelse (is_comb tm
           andalso is_combinational_const(rator tm)
           andalso is_combinational_const(rand tm));

(*****************************************************************************)
(* CompileExp exp                                                            *)
(* -->                                                                       *)
(* [REC assumption] |- <circuit> ===> DEV exp                                *)
(*****************************************************************************)

fun CompileExp tm =
 let val _ = if not(fst(dest_type(type_of tm)) = "fun")
              then (print_term tm; print "\n";
                    print "Devices can only compute functions.\n";
                    raise ERR "CompileExp" "attempt to compile non-function")
              else ()
     val (opr,args) = dest_exp tm
                      handle HOL_ERR _
                      => raise ERR "CompileExp" "bad expression"
 in
  if null args orelse is_combinational tm
   then ISPEC ``DEV ^tm`` DEV_IMP_REFL
   else
    case fst(dest_const opr) of
       "Seq" => let val tm1 = hd args
                    val tm2 = hd(tl args)
                in
                 if is_combinational tm1
                  then MATCH_MP
                        (ISPEC tm1 PRECEDE_DEV)
                        (CompileExp tm2)
                  else if is_combinational tm2
                  then MATCH_MP
                        (ISPEC tm2 FOLLOW_DEV)
                        (CompileExp tm1)
                  else MATCH_MP
                        SEQ_INTRO
                        (CONJ (CompileExp tm1) (CompileExp tm2))
                end
     | "Par" => MATCH_MP PAR_INTRO (LIST_CONJ(map CompileExp args))
     | "Ite" => MATCH_MP ITE_INTRO (LIST_CONJ(map CompileExp args))
     | "Rec" => let val thl = map (CompileExp) args
                    val var_list = map (rand o rand o concl o SPEC_ALL) thl
                in
                 MATCH_MP
                  (UNDISCH(SPEC_ALL(ISPECL var_list REC_INTRO)))
                  (LIST_CONJ thl)
                end
     | "Let" => let val th1 = REWR_CONV Let tm
                    val th2 = CompileExp(rhs(concl th1))
                in
                 CONV_RULE (RAND_CONV(RAND_CONV(REWR_CONV(SYM th1)))) th2
                end
     | _     => raise ERR "CompileExp" "this shouldn't happen"
 end;

(*****************************************************************************)
(* CompileProg prog tm --> rewrite tm with prog, then compiles the result    *)
(*****************************************************************************)

fun CompileProg prog tm =
 let val expand_th = REWRITE_CONV prog tm
     val compile_th = CompileExp (rhs(concl expand_th))
 in
  CONV_RULE (RAND_CONV(REWRITE_CONV[GSYM expand_th])) compile_th
 end;

(*****************************************************************************)
(* Compile (|- f args = bdy) = CompileProg [|- f args = bdy] ``f``           *)
(*****************************************************************************)

fun Compile th =
 let val (func,_) =
      dest_eq(concl(SPEC_ALL th))
      handle HOL_ERR _ => raise ERR "Compile" "not an equation"
     val _ = if not(is_const func)
              then raise ERR "Compile" "rator of lhs not a constant"
              else ()
 in
  CompileProg [th] func
 end;

(*****************************************************************************)
(*  ``(f = \(x1,x2,...,xn). B)``                                             *)
(*   -->                                                                     *)
(*   |- (f = \(x1,x2,...,xn). B) = !x1 x2 ... xn. f(x1,x2,...,xn) = B        *)
(*****************************************************************************)

fun FUN_DEF_CONV tm =                            (* Supplied by Konrad Slind *)
  let val (M,N) = dest_eq tm
      val th1 = ISPECL [M,N] FUN_EQ_THM
      val th2 = Ho_Rewrite.REWRITE_RULE [LAMBDA_PROD] th1
      val th3 = pairLib.GEN_BETA_RULE th2
  in
     CONV_RULE (RHS_CONV pairTools.ELIM_TUPLED_QUANT_CONV) th3
  end;

fun FUN_DEF_RULE th = CONV_RULE(DEPTH_CONV FUN_DEF_CONV) th handle _ => th;

(*****************************************************************************)
(* Simp prog thm rewrites thm using definitions in prog                      *)
(*****************************************************************************)

fun Simp prog =
 FUN_DEF_RULE o (SIMP_RULE list_ss (LAMBDA_PROD::SimpThms@prog));

(*****************************************************************************)
(* SimpExp prog term expands term using definitions in prog                  *)
(*****************************************************************************)

fun SimpExp prog =
 FUN_DEF_RULE o (SIMP_CONV list_ss (LAMBDA_PROD::SimpThms@prog));

(*****************************************************************************)
(*            |- TOTAL(f1,f2,f3)                                             *)
(*  -------------------------------------------                              *)
(*  |- TOTAL((\x. f1 x), (\x. f2 x), (\x. f3 x))                             *)
(*****************************************************************************)

val UNPAIR_TOTAL =
 CONV_RULE
  (RAND_CONV
   (RATOR_CONV(RAND_CONV(REWR_CONV(GSYM ETA_AX)))
     THENC RAND_CONV
            (RATOR_CONV(RAND_CONV(REWR_CONV(GSYM ETA_AX)))
              THENC RAND_CONV(REWR_CONV(GSYM ETA_AX))))
   THENC DEPTH_CONV GEN_BETA_CONV);

(*****************************************************************************)
(* Convert a non-recursive definition to an expression and then compile it   *)
(*****************************************************************************)

fun CompileConvert defth = Compile(Convert defth);

(*****************************************************************************)
(* Convert a recursive definition to an expression and then compile it.      *)
(*****************************************************************************)

fun prove(t,tac) = Tactical.TAC_PROOF(([],t), tac)
fun RecCompileConvert defth totalth =
 let val previousShowTypes = !show_types
     val (l,r) = dest_eq(concl(SPEC_ALL defth))
     val (func,args) = dest_comb l
     val impth =
        (GEN_BETA_RULE o
         SIMP_RULE std_ss [Seq_def,Par_def,Ite_def])
        (DISCH_ALL(Compile (RecConvert defth totalth)))
     val (_,args) = dest_comb (fst(dest_imp(concl impth)))
     val (_,args') = dest_comb (concl totalth)
     val (fb,(f1,f2)) = (fst(dest_pair args),dest_pair(snd (dest_pair args)))
     val (fb',(f1',f2')) = (fst(dest_pair args'),dest_pair(snd (dest_pair args')))
     val h = fst(dest_imp(concl impth))
     val _ = (show_types := true)
     val hthm = prove (h,
              `(^fb = ^fb') /\ (^f1 = ^f1') /\ (^f2 = ^f2')`
               by RW_TAC std_ss [LAMBDA_PROD]
           THEN RW_TAC std_ss [totalth])
     val _ = (show_types := previousShowTypes)
 in
  SIMP_RULE std_ss [] (MP impth hthm)
 end;


(*---------------------------------------------------------------------------*)
(* For termination prover.                                                   *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Single entrypoint for definitions where proof of termination will succeed *)
(* Allows measure function to be indicated in same quotation as definition,  *)
(* or not.                                                                   *)
(*                                                                           *)
(*     hwDefine `(eqns) measuring f`                                         *)
(*                                                                           *)
(* will use f as the measure function and attempt automatic termination      *)
(* proof. If successful, returns (|- eqns, |- ind, |- dev)                   *)
(* NB. the recursion equations must be parenthesized; otherwise, strange     *)
(* parse errors result. Also, the name of the defined function must be       *)
(* alphanumeric.                                                             *)
(*                                                                           *)
(* One can also omit the measure function, as in Define:                     *)
(*                                                                           *)
(*     hwDefine `eqns`                                                       *)
(*                                                                           *)
(* which will accept either non-recursive or recursive specifications. It    *)
(* returns a triple (|- eqns, |- ind, |- dev) where the ind theorem should   *)
(* be ignored for now (it will be boolTheory.TRUTH).                         *)
(*                                                                           *)
(* The results of hwDefine are stored in a reference hwDefineLib.            *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val hwDefineLib = ref([] : (thm * thm * thm)list);

fun hwDefine defq =
 let val absyn0 = Parse.Absyn defq
 in
  case absyn0
  of Absyn.APP(_,Absyn.APP(_,Absyn.IDENT(loc,"measuring"),def),f) =>
       let val (deftm,names) = Defn.parse_absyn def
           val hdeqn = hd (boolSyntax.strip_conj deftm)
           val (l,r) = boolSyntax.dest_eq hdeqn
           val domty = pairSyntax.list_mk_prod
                         (map type_of (snd (boolSyntax.strip_comb l)))
           val fty = Pretype.fromType (domty --> numSyntax.num)
           val typedf = Parse.absyn_to_term
                            (Parse.term_grammar())
                            (Absyn.TYPED(loc,f,fty))
           val defn = Defn.mk_defn (hd names) deftm
           val tac = EXISTS_TAC (numSyntax.mk_cmeasure typedf)
                      THEN CONJ_TAC
                      THENL [TotalDefn.WF_TAC,
                             TotalDefn.TC_SIMP_TAC
                             THEN (PROVE_TAC[wordsTheory.WORD_PRED_THM])]
           val (defth,ind) = Defn.tprove(defn, tac)
           val totalth = prove
                 (getTotal defth,
                  RW_TAC std_ss [TOTAL_def,pairTheory.FORALL_PROD]
                  THEN EXISTS_TAC typedf THEN TotalDefn.TC_SIMP_TAC
                  THEN PROVE_TAC [wordsTheory.WORD_PRED_THM])
            val devth = PURE_REWRITE_RULE [GSYM DEV_IMP_def]
                          (RecCompileConvert defth totalth)
        in
         hwDefineLib := (defth,ind,devth) :: !hwDefineLib;
         (defth,ind,devth)
        end
   | otherwise =>
     let val (deftm,names) = Defn.parse_absyn absyn0
         val defn = Defn.mk_defn (hd names) deftm
     in
      case TotalDefn.primDefine defn
       of (defth,NONE,NONE) =>   (* non-recursive *)
          let val defth' = SPEC_ALL defth
              val devth = PURE_REWRITE_RULE[GSYM DEV_IMP_def]
                              (CompileConvert defth')
          in
             hwDefineLib := (defth',boolTheory.TRUTH,devth) :: !hwDefineLib;
             (defth',boolTheory.TRUTH,devth)
          end
       | (defth, SOME ind, SOME terminates) =>  (* recursive *)
          let val reln = rand(concl(CONJUNCT1 terminates))
              val totalth = prove (getTotal defth,
                      RW_TAC std_ss [TOTAL_def,pairTheory.FORALL_PROD]
                      THEN EXISTS_TAC (rand reln) THEN TotalDefn.TC_SIMP_TAC)
              val devth = PURE_REWRITE_RULE [GSYM DEV_IMP_def]
                                (RecCompileConvert defth totalth)
          in
            hwDefineLib := (defth,ind,devth) :: !hwDefineLib;
            (defth,ind,devth)
          end
        | otherwise => raise ERR "hwDefine" "should not happen"
     end
 end
 handle e as HOL_ERR _ => raise wrap_exn "hwDefine" "failed" e;

(*****************************************************************************)
(* Recognisers, destructors and constructors for harware combinatory         *)
(* expressions.                                                              *)
(*****************************************************************************)

(*****************************************************************************)
(* PRECEDE abstract syntax functions                                         *)
(*****************************************************************************)

fun is_PRECEDE tm =
 is_comb tm
  andalso is_comb(rator tm)
  andalso is_const(rator(rator tm))
  andalso (fst(dest_const(rator(rator tm))) = "PRECEDE");

fun dest_PRECEDE tm = (rand(rator tm), rand tm);

fun mk_PRECEDE(f,d) = ``PRECEDE ^f ^d``;

(*****************************************************************************)
(* FOLLOW abstract syntax functions                                          *)
(*****************************************************************************)

fun is_FOLLOW tm =
 is_comb tm
  andalso is_comb(rator tm)
  andalso is_const(rator(rator tm))
  andalso (fst(dest_const(rator(rator tm))) = "FOLLOW");

fun dest_FOLLOW tm = (rand(rator tm), rand tm);

fun mk_FOLLOW(d,f) = ``FOLLOW ^d ^f``;

(*****************************************************************************)
(* ATM                                                                       *)
(*****************************************************************************)

fun is_ATM tm =
 is_comb tm
  andalso is_const(rator tm)
  andalso (fst(dest_const(rator tm)) = "ATM");

fun dest_ATM tm = rand tm;

fun mk_ATM tm = ``ATM ^tm``;

(*****************************************************************************)
(* SEQ                                                                       *)
(*****************************************************************************)

fun is_SEQ tm =
 is_comb tm
  andalso is_comb(rator tm)
  andalso is_const(rator(rator tm))
  andalso (fst(dest_const(rator(rator tm))) = "SEQ");

fun dest_SEQ tm = (rand(rator tm), rand tm);

fun mk_SEQ(tm1,tm2) = ``SEQ ^tm1 ^tm2``;

(*****************************************************************************)
(* PAR                                                                       *)
(*****************************************************************************)

fun is_PAR tm =
 is_comb tm
  andalso is_comb(rator tm)
  andalso is_const(rator(rator tm))
  andalso (fst(dest_const(rator(rator tm))) = "PAR");

fun dest_PAR tm = (rand(rator tm), rand tm);

fun mk_PAR(tm1,tm2) = ``PAR ^tm1 ^tm2``;

(*****************************************************************************)
(* ITE                                                                       *)
(*****************************************************************************)

fun is_ITE tm =
 is_comb tm
  andalso is_comb(rator tm)
  andalso is_comb(rator(rator tm))
  andalso is_const(rator(rator(rator tm)))
  andalso (fst(dest_const(rator(rator(rator tm)))) = "ITE");

fun dest_ITE tm = (rand(rator(rator tm)), rand(rator tm), rand tm);

fun mk_ITE(tm1,tm2,tm3) = ``ITE ^tm1 ^tm2 ^tm3``;

(*****************************************************************************)
(* REC                                                                       *)
(*****************************************************************************)

fun is_REC tm =
 is_comb tm
  andalso is_comb(rator tm)
  andalso is_comb(rator(rator tm))
  andalso is_const(rator(rator(rator tm)))
  andalso (fst(dest_const(rator(rator(rator tm)))) = "REC");

fun dest_REC tm = (rand(rator(rator tm)), rand(rator tm), rand tm);

fun mk_REC(tm1,tm2,tm3) = ``REC ^tm1 ^tm2 ^tm3``;

(*****************************************************************************)
(* Dev                                                                       *)
(*****************************************************************************)

fun is_DEV tm =
 is_comb tm
  andalso is_const(rator tm)
  andalso (fst(dest_const(rator tm)) = "DEV");

fun dest_DEV tm = rand tm;

fun mk_DEV tm = ``DEV ^tm``;

(*****************************************************************************)
(* A refinement function is an ML function that maps a term ``DEV f`` to     *)
(* a theorem                                                                 *)
(*                                                                           *)
(*  |- DEV g ===> DEV f                                                      *)
(*                                                                           *)
(* it is a bit like a conversion, but for device implication (===>)          *)
(* instead of for equality (=)                                               *)
(*****************************************************************************)

(*****************************************************************************)
(* Refine a device to a combinational circuit (i.e. an ATM):                 *)
(*                                                                           *)
(* ATM_REFINE ``DEV f``  =  |- ATM f ===> DEV f : thm                        *)
(*                                                                           *)
(*****************************************************************************)

fun ATM_REFINE tm =
 if not(is_comb tm
         andalso is_const(rator tm)
         andalso (fst(dest_const(rator tm)) = "DEV"))
  then raise ERR "ATM_REFINE" "argument not a DEV"
  else ISPEC (rand tm) ATM_INTRO;

(*****************************************************************************)
(* LIB_REFINE                                                                *)
(*  [|- <circuit> ===> DEV f1,                                               *)
(*   |- <circuit> ===> DEV f2                                                *)
(*   ...                                                                     *)
(*   |- <circuit> ===> DEV fn]                                               *)
(*  ``DEV fi``                                                               *)
(*                                                                           *)
(* returns the first theorem <circuit> ===> DEV fi                           *)
(* that it finds in the supplied list (i.e. library).                        *)
(* Fails if no refining theorem found.                                       *)
(*****************************************************************************)

fun LIB_REFINE lib tm =
 if is_DEV tm
  then
   case
     List.find
      (aconv tm o snd o dest_dev_imp o concl o SPEC_ALL)
      lib
   of SOME th => th
    | NONE    => raise ERR "LIB_REFINE" "DEV not in library"
  else raise ERR "LIB_REFINE" "attempt to lookup a non-DEV";

(*****************************************************************************)
(* DEPTHR refine tm scans through a combinatory expression tm built          *)
(* from ATM, SEQ, PAR, ITE, REC and DEV and applies the refine to all        *)
(* arguments of DEV using                                                    *)
(*                                                                           *)
(*  |- !P1 P2 Q1 Q2. P1 ===> Q1 /\ P2 ===> Q2 ==> P1 ;; P2 ===> Q1 ;; Q2     *)
(*                                                                           *)
(*  |- !P1 P2 Q1 Q2. P1 ===> Q1 /\ P2 ===> Q2 ==> P1 || P2 ===> Q1 || Q2     *)
(*                                                                           *)
(*  |- !P1 P2 Q1 Q2.                                                         *)
(*       P1 ===> Q1 /\ P2 ===> Q2 /\ P3 ===> Q3 ==>                          *)
(*       ITE P1 P2 P3 ===> ITE Q1 Q2 Q3                                      *)
(*                                                                           *)
(*  |- !P1 P2 Q1 Q2.                                                         *)
(*       P1 ===> Q1 /\ P2 ===> Q2 /\ P3 ===> Q3 ==>                          *)
(*       REC P1 P2 P3 ===> REC Q1 Q2 Q3                                      *)
(*                                                                           *)
(* to generate a theorem                                                     *)
(*                                                                           *)
(*  |- tm' ===> tm                                                           *)
(*                                                                           *)
(* (if refine fails, then no action is taken, i.e. |- tm ===> tm used)       *)
(*****************************************************************************)

fun DEPTHR refine tm =
 if is_DEV tm
  then (refine tm
        handle _ => ISPEC tm DEV_IMP_REFL)
 else if is_ATM tm
 then ISPEC tm DEV_IMP_REFL
 else if is_PRECEDE tm
  then
   let val (f,d) = dest_PRECEDE tm
       val th = DEPTHR refine d
   in
    MATCH_MP (ISPEC f PRECEDE_DEV_IMP) th
   end
 else if is_FOLLOW tm
  then
   let val (d,f) = dest_FOLLOW tm
       val th = DEPTHR refine d
   in
    MATCH_MP (ISPEC f FOLLOW_DEV_IMP) th
   end
 else if is_SEQ tm
  then
   let val (tm1,tm2) = dest_SEQ tm
       val th1 = DEPTHR refine tm1
       val th2 = DEPTHR refine tm2
   in
    MATCH_MP SEQ_DEV_IMP (CONJ th1 th2)
   end
 else if is_PAR tm
  then
   let val (tm1,tm2) = dest_PAR tm
       val th1 = DEPTHR refine tm1
       val th2 = DEPTHR refine tm2
   in
    MATCH_MP PAR_DEV_IMP (CONJ th1 th2)
   end
 else if is_ITE tm
  then
   let val (tm1,tm2,tm3) = dest_ITE tm
       val th1 = DEPTHR refine tm1
       val th2 = DEPTHR refine tm2
       val th3 = DEPTHR refine tm3
   in
    MATCH_MP ITE_DEV_IMP (LIST_CONJ[th1,th2,th3])
   end
 else if is_REC tm
  then
   let val (tm1,tm2,tm3) = dest_REC tm
       val th1 = DEPTHR refine tm1
       val th2 = DEPTHR refine tm2
       val th3 = DEPTHR refine tm3
   in
    MATCH_MP REC_DEV_IMP (LIST_CONJ[th1,th2,th3])
   end
 else (print_term tm; print"\n";
       raise ERR "DEPTHR" "bad argument");

(*****************************************************************************)
(* REFINE refine (|- <circuit> ===> Dev f) applies refine to <circuit>       *)
(* to generate                                                               *)
(*                                                                           *)
(*  |- <circuit'> ===> <circuit>                                             *)
(*                                                                           *)
(* and then uses transitivity of ===> to deduce                              *)
(*                                                                           *)
(*  |- <circuit'> ===> Dev f                                                 *)
(*****************************************************************************)

fun REFINE refine th =
 MATCH_MP
  DEV_IMP_TRANS
  (CONJ (refine (fst(dest_dev_imp(concl th)))) th)
 handle _ => raise ERR "REFINE" "bad argument";

(*****************************************************************************)
(* Naively implemented refinement combinators                                *)
(*****************************************************************************)

(*****************************************************************************)
(*    |- t2 ===> t1                                                          *)
(*   --------------- refine t2 = |- t3 ===> t2                               *)
(*    |- t3 ===> t1                                                          *)
(*****************************************************************************)

fun ANTE_REFINE th refine =
  MATCH_MP DEV_IMP_TRANS (CONJ (refine (fst(dest_dev_imp(concl th)))) th);

(*****************************************************************************)
(* Apply two refinements in succession;  fail if either does.                *)
(*****************************************************************************)

infixr 3 THENR;

fun (refine1 THENR refine2) tm = ANTE_REFINE (refine1 tm) refine2;

(*****************************************************************************)
(* Apply refine1;  if it raises a HOL_ERR then apply refine2. Note that      *)
(* interrupts and other exceptions will sail on through.                     *)
(*****************************************************************************)

infixr 3 ORELSER;

fun (refine1 ORELSER refine2) tm =
 refine1 tm handle HOL_ERR _ => refine2 tm;

(*****************************************************************************)
(* Identity refinement    tm --> |- tm ===> tm                               *)
(*****************************************************************************)

fun ALL_REFINE tm = ISPEC tm DEV_IMP_REFL;

(*****************************************************************************)
(* Repeat refine until no change                                             *)
(*****************************************************************************)

fun REPEATR refine tm =
 let val th = refine tm
     val (tm1,tm2) = dest_dev_imp(concl th)
 in
  if aconv tm1 tm2
   then th
   else ANTE_REFINE th (REPEATR refine)
 end;

(*****************************************************************************)
(* Refine using hwDefineLib and then convert all remaining DEVs to ATMs      *)
(*****************************************************************************)

fun REFINE_ALL th =
 REFINE
  (REPEATR
    (DEPTHR
      (LIB_REFINE(map #3 (!hwDefineLib))
        ORELSER ATM_REFINE
        ORELSER ALL_REFINE)))
  th;

(*****************************************************************************)
(* Some ancient code for normalising circuits (will need to be updated!)     *)
(*****************************************************************************)

(*****************************************************************************)
(* LIST_EXISTS_ALPHA_CONV s n ``?a b c ...`` =                               *)
(*  |- (?a b c ...) = ?sn sn+1 sn+2 ...                                      *)
(*****************************************************************************)

fun LIST_EXISTS_ALPHA_CONV s n t =
 if is_exists t
  then
   let val (v,_)  = dest_exists t
       val (_,ty) = dest_var v
   in
    (GEN_ALPHA_CONV (mk_var((s^Int.toString n),ty))
      THENC QUANT_CONV(LIST_EXISTS_ALPHA_CONV s (n+1))) t
   end
  else REFL t;

(*****************************************************************************)
(* Standardise apart all quantified variables to ``v0``, ``v1``, ...         *)
(* where "v" is given as an argument                                         *)
(*****************************************************************************)

fun OLD_STANDARDIZE_EXISTS_CONV s =
 let val count_ref = ref 0
     fun mkv ty = let val newv = mk_var((s^Int.toString(!count_ref)),ty)
                  in
                   (count_ref := (!count_ref)+1; newv)
                  end
     fun LOCAL_RENAME_CONV t =
      if is_exists t orelse is_forall t
       then
        let val (v,_)  = if is_exists t then dest_exists t else dest_forall t
            val (_,ty) = dest_var v
        in
         (GEN_ALPHA_CONV(mkv ty) THENC QUANT_CONV LOCAL_RENAME_CONV) t
        end
       else SUB_CONV LOCAL_RENAME_CONV t
 in
  LOCAL_RENAME_CONV
 end;

(*---------------------------------------------------------------------------*)
(* A faster version of STANDARDIZE_EXISTS_CONV.                              *)
(*---------------------------------------------------------------------------*)
(*
fun STANDARDIZE_EXISTS_CONV s =
 let val count_ref = ref 0
     fun mkv ty = let val newv = mk_var((s^Int.toString(!count_ref)),ty)
                  in
                   (count_ref := (!count_ref)+1; newv)
                  end
     fun rename t =
      if is_exists t orelse is_forall t
       then
        let val (vlist,body) = if is_exists t then strip_exists t
                                              else strip_forall t
            val vlist' = map (mkv o type_of) vlist
            val theta  = map2 (curry op|->) vlist vlist'
            val body' = rename (time (Term.subst theta) body) (* slow *)
        in
         (if is_exists t then list_mk_exists else list_mk_forall)
         (vlist', body')
        end
       else if is_abs t then
              let val (v,M) = dest_abs t
              in mk_abs(v,rename t)
              end
       else if is_comb t then
              let val (M,N) = dest_comb t
              in mk_comb(rename M, rename N)
              end
       else t
 in
  fn t => (ALPHA t (rename t)
           handle HOL_ERR _ =>
             (print"STANDARDIZE_EXISTS_CONV: new version broken,\
                  \ so calling the old version";
            OLD_STANDARDIZE_EXISTS_CONV s t))
 end;
*)

local
val init_theta:(term,term)Binarymap.dict = Binarymap.mkDict Term.var_compare;

fun mksubst L1 L2 theta_0 =
 rev_itlist2
    (fn redex:term => fn residue:term => fn theta =>
          Binarymap.insert(theta,redex,residue)) L1 L2 theta_0;

fun subst_fn theta M = Binarymap.find(theta,M);
fun applysubst f x = f x handle Binarymap.NotFound => x;

infix oo;
fun (th2 oo th1) M = th1 M handle Binarymap.NotFound => th2 M;
in
fun STANDARDIZE_EXISTS_CONV s =
 let val count_ref = ref 0
     fun mkv ty = let val newv = mk_var((s^Int.toString(!count_ref)),ty)
                  in
                   (count_ref := (!count_ref)+1; newv)
                  end
     fun rename theta t =
      if is_var t then applysubst theta t else
      if is_const t then t else
      if is_exists t orelse is_forall t
       then
        let val (vlist,body) = if is_exists t then strip_exists t
                                              else strip_forall t
            val vlist' = map (mkv o type_of) vlist
            val block_theta = subst_fn (mksubst vlist vlist' init_theta)
            val body' = rename (theta oo block_theta) body
        in
         (if is_exists t then list_mk_exists else list_mk_forall)
         (vlist', body')
        end
       else if is_abs t then
             let val (vlist,body) = strip_abs t
                 val block_theta = subst_fn (mksubst vlist vlist init_theta)
                 val body' = rename (theta oo block_theta) body
              in list_mk_abs(vlist,body')
              end
       else if is_comb t then
              let val (M,N) = dest_comb t
              in mk_comb(rename theta M, rename theta N)
              end
       else t
 in
  fn t => (ALPHA t (rename (subst_fn init_theta) t)
           handle HOL_ERR _ =>
             (print"STANDARDIZE_EXISTS_CONV: new version broken,\
                  \ so calling the old version";
            OLD_STANDARDIZE_EXISTS_CONV s t))
 end
end;


(*****************************************************************************)
(* Hoist all existential quantifiers to the outside                          *)
(*                                                                           *)
(*   (?x. A) /\ B --> ?x. A /\ B  (check x not free in B)                    *)
(*   A /\ (?x. B) --> ?x. A /\ B  (check x not free in A)                    *)
(*                                                                           *)
(* returns a pair consisting of a list of existentially quantified vars      *)
(* and a list of conjuncts                                                   *)
(*****************************************************************************)

fun EXISTS_OUT t =
 let val vars_ref = ref([]:term list) (* collect existentially quantified variables *)
     fun LOCAL_EXISTS_OUT t =
      if is_exists t
       then
        let val (l,t1) = strip_exists t
            val _ = (vars_ref := l @ (!vars_ref))
        in
         LOCAL_EXISTS_OUT t1
        end else
      if is_conj t
       then
        let val (t1,t2) = dest_conj t
        in
         LOCAL_EXISTS_OUT t1 @ LOCAL_EXISTS_OUT t2
        end
      else [t]
     val tml = LOCAL_EXISTS_OUT t
 in
  (!vars_ref, tml)
 end;

(*****************************************************************************)
(* PRUNE1_FUN(v,[t1,...,tp,v=u,tq,...,tn]) or                                *)
(* PRUNE1_FUN(v,[t1,...,tp,u=v,tq,...,tn])                                   *)
(* returns [t1[u/v],...,tp[u/v],tq[u/v],...,tn[u/v]]                         *)
(* has no effect if there is no equation ``v=u`` or ``u=v`` in the list      *)
(*****************************************************************************)
(*
fun PRUNE1_FUN(v,tml) =
 let val l = filter (fn t => is_eq t andalso ((lhs t = v) orelse (rhs t = v))) tml
 in
  if null l
   then tml
   else
    let val (t1,t2) = dest_eq(hd l)
        val u = if t1=v then t2 else t1
    in
     filter
      (fn t => not(is_eq t andalso (lhs t = rhs t)))
      (map (hol88Lib.subst[(u,v)]) tml)
    end
 end;
*)

fun PRUNE1_FUN(v,tml) =
 let fun is_eqv t =
      let val (l,r) = dest_eq t
      in (l ~~ v) orelse (r ~~ v)
      end handle HOL_ERR _ => false
     fun is_eq_id t =
      let val (l,r) = dest_eq t
      in aconv l r
      end handle HOL_ERR _ => false
 in
   case filter is_eqv tml
    of [] => tml
     | h::_ =>
        let val (t1,t2) = dest_eq h
            val u = if t1 ~~ v then t2 else t1
            val tml' = map (subst [v |-> u]) tml
        in filter (not o is_eq_id) tml'
    end
 end;

fun EXISTS_OUT_CONV t =
 let val th        = (*time*) (STANDARDIZE_EXISTS_CONV "v") t
     val (vl,tml)  = (*time*) EXISTS_OUT (rhs(concl th))
     val tml1      = (*time*) (foldl PRUNE1_FUN tml) vl
     val t1        = (*time*) list_mk_conj tml1
     val vl1       = (*time*) rev (op_intersect aconv vl (free_vars t1))
     val count_ref = ref 0
     fun mkv ty     = let val newv = mk_var(("v"^Int.toString(!count_ref)),ty)
                      in
                       (count_ref := (!count_ref)+1; newv)
                      end
     val theta     = map (fn v => v |-> mkv(snd(dest_var v))) vl1
     val t2        = (*time*) (subst theta) t1
     val vl2       = map #residue theta
     val t3        = (*time*) list_mk_exists (vl2, t2)
     val th        = (*time*)
                      mk_oracle_thm (* YIKES! -- what's this!!! *)
                      "EXISTS_OUT_CONV" ([],mk_eq(t,t3))
 in
  th
 end;

(*****************************************************************************)
(* BUS_CONCAT abstract syntax functions                                      *)
(*****************************************************************************)

fun is_BUS_CONCAT tm =
 is_comb tm
  andalso is_comb(rator tm)
  andalso is_const(rator(rator tm))
  andalso (fst(dest_const(rator(rator tm))) = "BUS_CONCAT");

fun dest_BUS_CONCAT tm = (rand(rator tm), rand tm);

fun mk_BUS_CONCAT(b1,b2) = ``BUS_CONCAT ^b1 ^b2``;

(*****************************************************************************)
(* Match a varstruct with a bus. For example:                                *)
(*                                                                           *)
(* BUS_MATCH ``(m,n,acc)`` ``v102 <> v101 <> v100``                          *)
(* -->                                                                       *)
(* [(``m``,``v102``), (``n``,``v101``), (``acc``, ``v100``)]                 *)
(*                                                                           *)
(*                                                                           *)
(* BUS_MATCH ``(p1 - 1,p1',p1' + p2)`` ``v165 <> v164 <> v163``              *)
(* -->                                                                       *)
(* [(``p1 - 1``,``v165``), (``p1'``,``v164``),(``p1' + p2``,``v163``)        *)
(*****************************************************************************)

fun BUS_MATCH vst bus =
  (if not(is_pair vst) andalso not(is_BUS_CONCAT bus)
     then [(vst,bus)]
      else
        let val (vst1,vst2) = dest_pair vst
            val (bus1,bus2) = dest_BUS_CONCAT bus
        in
         BUS_MATCH vst1 bus1 @ BUS_MATCH vst2 bus2
        end)
  handle HOL_ERR _ => [];

(*****************************************************************************)
(* Convert a varstruct to a matching bus                                     *)
(* Example: varstruct_to_bus ty ``(v1,(v2,v3),v4)`` = ``v1<>(v2<>v3)<>v4``   *)
(* (where types are lifted to functions from domain ty)                      *)
(*****************************************************************************)

fun varstruct_to_bus time_ty vs =
 if is_var vs
  then let val (name,ty) = dest_var vs
       in
        mk_var(name,``:^time_ty -> ^ty``)
       end
  else if is_pair vs
  then let val (vs1,vs2) = dest_pair vs
       in
        ``^(varstruct_to_bus time_ty vs1) <> ^(varstruct_to_bus time_ty vs2)``
       end
  else raise ERR "varstruct_to_bus" "bad varstruct";

(*****************************************************************************)
(* A pure abstraction has the form ``\<varstruct>. <body>`` where            *)
(* <body> is built out of variables in <varstruct> and combinational         *)
(* constants using pairing.                                                  *)
(*****************************************************************************)

fun is_pure_abs tm =
 is_pabs tm
  andalso
   all
    is_combinational_const
    (op_set_diff aconv
     (strip_pair(snd(dest_pabs tm)))
     (strip_pair(fst(dest_pabs tm))));

(* Not used
(*****************************************************************************)
(* Test for ``Let f1 f2``                                                    *)
(*****************************************************************************)
fun is_Let tm =
 is_comb tm
   andalso is_const(fst(strip_comb tm))
   andalso (fst(dest_const(fst(strip_comb tm))) = "Let")
   andalso (length(snd(strip_comb tm)) = 2);
*)


(*****************************************************************************)
(* Generate a bus made of fresh variables from the type of a term            *)
(*****************************************************************************)

fun genbus time_ty v =
    let fun concatbus(tm1,tm2) = ``^tm1 <> ^tm2``
        fun makebus ty =
            let val tys = (snd(dest_type ty))
            in if tys = [] then
                  let val tm = genvar ``:^time_ty -> ^ty``
                  in (tm,[tm])
                  end
               else let val busesdecs =  map makebus tys
                        val buses = map fst busesdecs
                        val decs = map snd busesdecs
                    in (foldr concatbus (List.last buses) (List.take(buses,length buses-1)),
                        flatten decs)
                    end
            end
    in makebus (type_of v)
    end;

(*****************************************************************************)
(* Synthesise combinational circuits.                                        *)
(* Examples (derived from FactScript.sml):                                   *)
(*                                                                           *)
(*  COMB (\(m,n,acc). m) (v102 <> v101 <> v100, v134)                        *)
(*  -->                                                                      *)
(*  (v134 = v102)                                                            *)
(*                                                                           *)
(*  COMB (\(m,n,p). op <term>) (v102 <> v101 <> v100, v134)                  *)
(*  -->                                                                      *)
(*  ?v. COMB(\(m,n,p). <term>)(v102 <> v101 <> v100,v) /\ COMB op (v,v134)   *)
(*                                                                           *)
(*  COMB (\(m,n,p). (op <term1>) <term2>) (v102 <> v101 <> v100, v134)       *)
(*  -->                                                                      *)
(*  ?v1 v2. COMB(\(m,n,p). <term1>)(v102 <> v101 <> v100,v1) /\              *)
(*          COMB(\(m,n,p). <term2>)(v102 <> v101 <> v100,v2) /\              *)
(*          COMB (UNCURRY op) (v1 <> v2,v134)                                *)
(*                                                                           *)
(*  COMB (\(m,n,p). (<term1>, <term2>) (v102 <> v101 <> v100, v134 <> v135)  *)
(*  -->                                                                      *)
(*  ?v1 v2. COMB(\(m,n,p). <term1>)(v102 <> v101 <> v100,v1) /\              *)
(*          COMB(\(m,n,p). <term2>)(v102 <> v101 <> v100,v2) /\              *)
(*          (v134 = v1) /\ (v135 = v2)                                       *)
(*                                                                           *)
(*  COMB (\(p1,p1',p2). (p1 - 1,p1',p1' + p2))                               *)
(*       (v109 <> v108 <> v107, v165 <> v164 <> v163)                        *)
(*  -->                                                                      *)
(*  (?v. (CONSTANT 1 v /\ COMB (UNCURRY $-) (v109 <> v, v165)) /\            *)
(*  (v164 = v108) /\                                                         *)
(*  COMB (UNCURRY $+) (v108 <> v107, v163)                                   *)
(*****************************************************************************)

val comb_synth_goalref = ref T;

val if_print_flag = ref false;
fun if_print s = if !if_print_flag then print s else ();
fun if_print_term tm = if !if_print_flag then print_term tm else ();

fun COMB_SYNTH_CONV tm =    (* need to refactor: ORELSEC smaller conversions *)
 if is_comb tm
     andalso is_comb(rator tm)
     andalso is_const(rator(rator tm))
     andalso (fst(dest_const(rator(rator tm))) = "COMB")
     andalso is_pair(rand tm)
     andalso is_pabs(rand(rator tm))
  then
   let val abstr = rand(rator tm)
       val (args,bdy) = dest_pabs abstr
       val (in_bus,out_bus) = dest_pair(rand tm)
       val time_ty = hd(snd(dest_type(type_of in_bus)))
       val args_match = BUS_MATCH args in_bus
   in
    if is_pair bdy
     then (if is_BUS_CONCAT out_bus
            then let val (bdy1,bdy2) = dest_pair bdy
                     val (out_bus1,out_bus2) = dest_BUS_CONCAT out_bus
                     val goal =
                          ``^tm =
                            COMB ^(mk_pabs(args, bdy1)) (^in_bus,^out_bus1) /\
                            COMB ^(mk_pabs(args, bdy2)) (^in_bus,^out_bus2)``
                     val _ = (if_print "\n COMB_SYNTH_CONV case 4a:\n ";
                              if_print_term goal; if_print "\n")
                     val _ = comb_synth_goalref := goal
                 in
                 prove
                  (goal,
                   REWRITE_TAC[COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
                    THEN GEN_BETA_TAC
                    THEN CONV_TAC(RHS_CONV(UNWIND_AUTO_CONV THENC PRUNE_CONV))
                    THEN REWRITE_TAC[PAIR_EQ]
                    THEN EQ_TAC
                    THEN RW_TAC bool_ss []
                    THEN PROVE_TAC[])
                  handle HOL_ERR _ =>
                  (if_print "COMB_SYNTH_CONV warning, can't prove:\n";if_print_term goal;
                   if_print"\n"; raise ERR "COMB_SYNTH_CONV" "proof validation failure")
                 end
            else let val (arg1,arg2) = dest_pair bdy
                     val v1 = genvar ``:^time_ty -> ^(type_of arg1)``
                     val v2 = genvar ``:^time_ty -> ^(type_of arg2)``
                     val goal = ``^tm = ?^v1 ^v2. ^(rator tm) (^in_bus, ^v1 <> ^v2)
                                                  /\
                                                  (^out_bus = ^v1 <> ^v2)``
                 in
                 prove
                  (goal, PROVE_TAC[BUS_SPLIT])
                  handle HOL_ERR _ =>
                  (if_print "COMB_SYNTH_CONV warning, can't prove:\n";if_print_term goal;
                   if_print"\n"; raise ERR "COMB_SYNTH_CONV" "proof validation failure")
                 end)
     else if is_pure_abs abstr
     then let val bdy_match = BUS_MATCH bdy out_bus
              val goal =
               mk_eq
                (tm,
                 list_mk_conj
                  (map
                   (fn (t1,t2) =>
                     if is_combinational_const t1
                      then ``CONSTANT ^t1 ^(tassoc t1 bdy_match)``
                      else mk_eq(t2,tassoc t1 (rev args_match)))
                   bdy_match))
              val _ = (if_print "\n COMB_SYNTH_CONV case 3:\n ";
                       if_print_term goal; if_print "\n")
              val _ = comb_synth_goalref := goal
          in
           prove
            (goal,
             REWRITE_TAC[COMB_def,BUS_CONCAT_def,CONSTANT_def]
             THEN GEN_BETA_TAC
             THEN Ho_Rewrite.REWRITE_TAC[PAIR_EQ,FORALL_AND_THM]
             THEN Ho_Rewrite.REWRITE_TAC[GSYM FUN_EQ_THM]
             THEN (* PROVE_TAC[] *)
             (EQ_TAC THEN REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC)
              ORELSE PROVE_TAC [])
           handle HOL_ERR _ =>
           (if_print "COMB_SYNTH_CONV warning, can't prove:\n";if_print_term goal;
            if_print"\n"; raise ERR "COMB_SYNTH_CONV" "proof validation failure")
          end
     else if is_var bdy andalso can (tassoc bdy) args_match
     then let val goal = ``^tm = (^out_bus = ^(tassoc bdy (rev args_match)))``
              val _ = (if_print "\n COMB_SYNTH_CONV case 2:\n ";
                       if_print_term goal; if_print "\n")
              val _ = comb_synth_goalref := goal
          in
           prove
            (goal,
             REWRITE_TAC[COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
              THEN GEN_BETA_TAC
              THEN REWRITE_TAC[]
              THEN PROVE_TAC[])
           handle HOL_ERR _ =>
           (if_print "COMB_SYNTH_CONV warning, can't prove:\n";if_print_term goal;
            if_print"\n"; raise ERR "COMB_SYNTH_CONV" "proof validation failure")
          end
     else if is_combinational_const bdy
     then let val goal = ``^tm = CONSTANT ^bdy ^out_bus``
              val _ = (if_print "\n COMB_SYNTH_CONV case 1:\n ";
                       if_print_term goal; if_print "\n")
              val _ = comb_synth_goalref := goal
          in
           prove
            (goal,
             REWRITE_TAC[COMB_def,CONSTANT_def,FUN_EQ_THM]
              THEN GEN_BETA_TAC
              THEN REWRITE_TAC[]
              THEN PROVE_TAC[])
           handle HOL_ERR _ =>
           (if_print "COMB_SYNTH_CONV warning, can't prove:\n";if_print_term goal;
            if_print"\n"; raise ERR "COMB_SYNTH_CONV" "proof validation failure")
          end
     else if is_comb bdy andalso is_combinational_const(rator bdy)
     then let val arg = rand bdy
              val v = genvar ``:^time_ty -> ^(type_of arg)``
              val goal =
                   ``^tm = ?^v. COMB ^(mk_pabs(args, arg)) (^in_bus,^v)
                                /\
                                COMB ^(rator bdy) (^v, ^out_bus)``
              val _ = (if_print "\n COMB_SYNTH_CONV case 5:\n ";
                       if_print_term goal; if_print "\n")
              val _ = comb_synth_goalref := goal
          in
           prove
             (goal,
              REWRITE_TAC[COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
               THEN GEN_BETA_TAC
               THEN CONV_TAC(RHS_CONV(UNWIND_AUTO_CONV THENC PRUNE_CONV))
               THEN REWRITE_TAC[]
               THEN PROVE_TAC[])
           handle HOL_ERR _ =>
           (if_print "COMB_SYNTH_CONV warning, can't prove:\n";if_print_term goal;
            if_print"\n";
            raise ERR "COMB_SYNTH_CONV" "proof validation failure")
          end
     else if is_cond bdy
     then let val (test_tm,then_tm,else_tm) = dest_cond bdy
              val  sw = genvar ``:^time_ty -> ^(type_of test_tm)``
              val  mux_in1 = genvar ``:^time_ty -> ^(type_of then_tm)``
              val  mux_in2 = genvar ``:^time_ty -> ^(type_of else_tm)``
              val goal =
                   ``^tm =
                     ?^sw ^mux_in1 ^mux_in2.
                      COMB ^(mk_pabs(args, test_tm)) (^in_bus, ^sw)     /\
                      COMB ^(mk_pabs(args, then_tm)) (^in_bus,^mux_in1) /\
                      COMB ^(mk_pabs(args, else_tm)) (^in_bus,^mux_in2) /\
                      MUX(^sw,^mux_in1,^mux_in2,^out_bus)``
              val _ = (if_print "\n COMB_SYNTH_CONV case 6:\n ";
                       if_print_term goal; if_print "\n")
              val _ = comb_synth_goalref := goal
          in
          prove
           (goal,
            REWRITE_TAC[COMB_def,BUS_CONCAT_def,FUN_EQ_THM,MUX_def]
             THEN GEN_BETA_TAC
             THEN CONV_TAC(RHS_CONV(UNWIND_AUTO_CONV THENC PRUNE_CONV))
             THEN REWRITE_TAC[PAIR_EQ]
             THEN EQ_TAC
             THEN RW_TAC bool_ss []
             THEN PROVE_TAC[])
           handle HOL_ERR _ =>
           (if_print "COMB_SYNTH_CONV warning, can't prove:\n";if_print_term goal;
            if_print"\n"; raise ERR "COMB_SYNTH_CONV" "proof validation failure")
          end
     else if is_let bdy
     then let val (let_abs,let_tm) = dest_let bdy
              val (let_var, let_bdy) = dest_pabs let_abs
              val bus = varstruct_to_bus time_ty let_var
              val bus_match = BUS_MATCH let_var bus
              val goal =
                   mk_eq
                    (tm,
                     list_mk_exists
                      (rev(free_vars bus),
                       ``COMB ^(mk_pabs(args, let_tm)) (^in_bus,^bus) /\
                         COMB ^(mk_pabs(mk_pair(args,let_var), let_bdy))
                            (^in_bus <> ^bus,^out_bus)``))
              val _ = (if_print "\n COMB_SYNTH_CONV case 7:\n ";
                       if_print_term goal; if_print "\n")
              val _ = comb_synth_goalref := goal
          in
           prove
            (goal,
             RW_TAC std_ss [COMB_def,BUS_CONCAT_def,LET_DEF,FORALL_AND_THM]
              THEN CONV_TAC(RHS_CONV(UNWIND_AUTO_CONV THENC PRUNE_CONV))
              THEN RW_TAC std_ss [GSYM CONJ_ASSOC])
           handle HOL_ERR _ =>
           (if_print "COMB_SYNTH_CONV warning, can't prove:\n";if_print_term goal;
            if_print"\n"; raise ERR "COMB_SYNTH_CONV" "proof validation failure")
          end
     else if is_eq bdy
              andalso is_pair(lhs bdy)
              andalso is_pair(rhs bdy)
     then let val (l1,l2) = dest_pair(lhs bdy)
              val (r1,r2) = dest_pair(rhs bdy)
              val v1 = genvar ``:^time_ty -> bool``
              val v2 = genvar ``:^time_ty -> bool``
              val goal =
                   ``^tm = ?^v1 ^v2.
                       COMB ^(mk_pabs(args, mk_eq(l1,r1))) (^in_bus,^v1) /\
                       COMB ^(mk_pabs(args, mk_eq(l2,r2))) (^in_bus,^v2) /\
                       COMB (UNCURRY $/\) (^v1 <> ^v2, ^out_bus)``
              val _ = (if_print "\n COMB_SYNTH_CONV case 8:\n ";
                       if_print_term goal; if_print "\n")
              val _ = comb_synth_goalref := goal
          in
           prove
            (goal,
             REWRITE_TAC[COMB_def,BUS_CONCAT_def,FUN_EQ_THM,PAIR_EQ,UNCURRY]
              THEN GEN_BETA_TAC
              THEN REWRITE_TAC[FST,SND]
              THEN CONV_TAC(RHS_CONV(UNWIND_AUTO_CONV THENC PRUNE_CONV))
              THEN REWRITE_TAC[]
              THEN PROVE_TAC[])
           handle HOL_ERR _ =>
           (if_print "COMB_SYNTH_CONV warning, can't prove:\n";if_print_term goal;
            if_print"\n"; raise ERR "COMB_SYNTH_CONV" "proof validation failure")
          end
     else if is_comb bdy
              andalso is_comb(rator bdy)
              andalso is_const(rator(rator bdy))
     then let val opr = rator(rator bdy)
              val arg1 = rand(rator bdy)
              val arg2 = rand bdy
              val v1 = genvar ``:^time_ty -> ^(type_of arg1)``
              val v2 = genvar ``:^time_ty -> ^(type_of arg2)``
              val goal =
                   ``^tm = ?^v1 ^v2.
                       COMB ^(mk_pabs(args, arg1)) (^in_bus,^v1) /\
                       COMB ^(mk_pabs(args, arg2)) (^in_bus,^v2) /\
                       COMB (UNCURRY ^opr) (^v1 <> ^v2, ^out_bus)``
              val _ = (if_print "\n COMB_SYNTH_CONV case 9:\n ";
                       if_print_term goal; if_print "\n")
              val _ = comb_synth_goalref := goal
          in
           prove
            (goal,
             PURE_REWRITE_TAC[COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
              THEN GEN_BETA_TAC
              THEN PURE_REWRITE_TAC[UNCURRY,FST,SND]
              THEN CONV_TAC(RHS_CONV(UNWIND_AUTO_CONV THENC PRUNE_CONV))
              THEN REWRITE_TAC[]
              THEN PROVE_TAC[])
           handle HOL_ERR _ =>
           (if_print "COMB_SYNTH_CONV warning, can't prove:\n";if_print_term goal;
            if_print"\n"; raise ERR "COMB_SYNTH_CONV" "proof validation failure")
          end
     else (if_print "COMB_SYNTH_CONV warning, case not handled:\n";
           if_print_term tm;if_print"\n";
           raise ERR "COMB_SYNTH_CONV" "case not handled")
   end
  else raise ERR "COMB_SYNTH_COMB" "not an application of COMB to args";

(* Trace COMB_SYNTH_CONV
val COMB_SYNTH_CONV =
 fn tm => (let val th = COMB_SYNTH_CONV tm
           in
            (print "\nTRACE:\n";print_thm th;print "\n\n"; th)
           end);
*)


(*****************************************************************************)
(* If                                                                        *)
(*                                                                           *)
(*   f tm --> |- tm' ==> tm                                                  *)
(*                                                                           *)
(* then DEPTH_IMP f tm descends recursively through existential              *)
(* quantifications and conjunctions applying f (or tm --> |- tm ==> tm) if   *)
(* f fails) and returning |- tm' ==> tm for some term tm'                    *)
(*                                                                           *)
(*****************************************************************************)

fun DEPTH_IMP f tm =
 if is_exists tm
  then let val (v,bdy) = dest_exists tm
       in
        EXISTS_IMP v (DEPTH_IMP f bdy)
       end
  else if is_conj tm
  then let val (tm1,tm2) = dest_conj tm
           val th1 = SPEC_ALL(DEPTH_IMP f tm1)
           val th2 = SPEC_ALL(DEPTH_IMP f tm2)
       in
        MATCH_MP MONO_AND (CONJ th1 th2)
       end
  else f tm handle _ => DISCH tm (ASSUME tm);

(*****************************************************************************)
(* AP_ANTE_IMP_TRANS f (|- t1 ==> t2) applies f to t1 to get |- t0 ==> t1    *)
(* and then, using transitivity of ==>, returns |- t0 ==> t2                 *)
(*****************************************************************************)

fun AP_ANTE_IMP_TRANS f th =
 IMP_TRANS (f(fst(dest_imp(concl th)))) th;

(*****************************************************************************)
(* DEV_IMP f (|- tm ==> d) applies f to tm to generate an implication        *)
(* |- tm' ==> tm and then returns |- tm' ==> d                               *)
(*****************************************************************************)

fun DEV_IMP f th = IMP_TRANS (f(fst(dest_imp(concl th)))) th;

(*****************************************************************************)
(* DFF_IMP_INTRO ``DFF p`` --> |- DFF_IMP p => DFF p                         *)
(*****************************************************************************)

fun DFF_IMP_INTRO tm =
 if is_comb tm
     andalso is_const(rator tm)
     andalso (fst(dest_const(rator tm)) = "DFF")
  then ISPEC (rand tm) DFF_IMP_THM
  else DISCH tm (ASSUME tm);

(*****************************************************************************)
(* Test is a term is of the from ``s1 at p``                                 *)
(*****************************************************************************)

fun is_at tm =
 is_comb tm
  andalso is_comb(rator tm)
  andalso is_const(rator(rator tm))
  andalso (fst(dest_const(rator(rator tm))) = "at");

(*****************************************************************************)
(* IMP_REFINE (|- tm1 ==> tm2) tm matches tm2 to tm and if a substitution    *)
(* sub is found such that sub tm2 = tm then |- sub tm1 ==> sub tm2 is        *)
(* returned; if the match fails IMP_REFINE_Fail is raised.                   *)
(*****************************************************************************)

exception IMP_REFINE_Fail;

fun IMP_REFINE th tm =
 (let val th1 = SPEC_ALL th
      val (tm1,tm2) = dest_imp(concl th1)
      val (sub,ins) = match_term tm2 tm
  in
   INST sub (INST_TYPE ins th1)
  end)
 handle _ => raise IMP_REFINE_Fail;

(*****************************************************************************)
(* IMP_REFINEL [th1,...,thn] tm applies IMP_REFINE th1,...,IMP_REFINE thn    *)
(* to tm in turn until one succeeds.  If none succeeds then |- tm => tm      *)
(* is returned. Never fails.                                                 *)
(*****************************************************************************)

fun IMP_REFINEL [] tm = DISCH tm (ASSUME tm)
 |  IMP_REFINEL (th::thl) tm =
     IMP_REFINE th tm handle _
     => IMP_REFINEL thl tm;

(*****************************************************************************)
(*               |- !s1 ... sn. P s1 ... sn                                  *)
(*  ------------------------------------------------------- at_SPECL ``clk`` *)
(*  ([``s1``,...,``sn``], |- P (s1 at clk) ... (sn at clk))                  *)
(*****************************************************************************)

fun at_SPEC_ALL clk th =
 let val (vl,bdy) = strip_forall(concl th)
 in
  (vl, SPECL (map (fn v => ``^v at ^clk``) vl) th)
 end;

(*****************************************************************************)
(*      |- P ==> Q                                                           *)
(*   ---------------- (x not free in Q)                                      *)
(*   |- (?x. P) ==> Q                                                        *)
(*****************************************************************************)

fun ANTE_EXISTS_INTRO v th =
 (let val (t1,t2) = dest_imp(concl th)
      val exists_tm = mk_exists(v,t1)
      val th1 = ASSUME exists_tm
      val th2 = UNDISCH th
      val th3 = CHOOSE (v,th1) th2
  in
   DISCH exists_tm th3
  end)
 handle HOL_ERR _ => th;

fun LIST_ANTE_EXISTS_INTRO([],th) = th
 |  LIST_ANTE_EXISTS_INTRO((v::vl),th) =
     ANTE_EXISTS_INTRO v (LIST_ANTE_EXISTS_INTRO(vl,th));

(*****************************************************************************)
(* ``: ty1 # ... # tyn`` --> [`:ty```, ..., :``tyn``]                        *)
(*****************************************************************************)

fun strip_prodtype ty =
 (let val ("prod", [ty1,ty2]) = dest_type ty
  in
  ty1 :: strip_prodtype ty2
  end)
 handle _ => [ty];

(*****************************************************************************)
(* mapcount f [x1,...,xn] = [f 1 x1, ..., f n xn]                            *)
(*****************************************************************************)

local
fun mapcount_aux n f [] = []
 |  mapcount_aux n f (x::xl) = f n x :: (mapcount_aux (n+1) f xl);
in
fun mapcount f l = mapcount_aux 1 f l
end;

(*****************************************************************************)
(* ``s : ty -> ty1#...#tyn``  -->  ``(s1:ty->ty1) <> ... <> (sn:ty->tyn)``   *)
(*****************************************************************************)

fun bus_split tm =
 (let val (name,ty) = dest_var tm
      val (ty1,ty2) = dom_rng ty
      val tyl = strip_prodtype ty2
  in
   if (length tyl = 1)
    then tm
    else
     let val vl1 = mapcount
                    (fn n => fn vty =>
                      bus_split(mk_var((name^Int.toString n),``:^ty1->^vty``)))
                    tyl
         val (v1::vl2) = rev vl1
     in
      foldl (fn (v,vtm) => ``^v <> ^vtm``) v1 vl2
     end
  end)
  handle HOL_ERR _ => raise ERR "bus_split" "not a bus";

(*****************************************************************************)
(*                  |- Cir ===> DEV f                                        *)
(*  ------------------------------------------------------                   *)
(*  |- Cir (load,(inp1<>...<>inpm),done,(out1<>...<>outn))                   *)
(*     ==>                                                                   *)
(*     DEV f (load,(inp1<>...<>inpm),done,(out1<>...<>outn))                 *)
(*****************************************************************************)

fun IN_OUT_SPLIT th =
 let val (tm1,tm2) = dest_dev_imp(concl th)
     val (ty1,ty2) = dom_rng (type_of tm2)
     val [load_ty,inp_ty,done_ty,out_ty] = strip_prodtype ty1
     val args_tm =
          list_mk_pair
           [mk_var("load",load_ty),
            bus_split(mk_var("inp",inp_ty)),
            mk_var("done",done_ty),
            bus_split(mk_var("out",out_ty))]
 in
  SPEC args_tm (CONV_RULE(REWR_CONV DEV_IMP_def)th)
 end;

(*****************************************************************************)
(* User modifiable library of combinational components.                      *)
(*****************************************************************************)

val combinational_components = ref([] : thm list);

fun add_combinational_components thl =
 (combinational_components :=
   thl @ (!combinational_components));

val _ =
 add_combinational_components
  [COMB_NOT,
   COMB_AND,
   COMB_OR];

(*---------------------------------------------------------------------------*)
(* Building netlists                                                         *)
(*---------------------------------------------------------------------------*)

val monitor_netlist_construction = ref false;

fun ptime a f x =
  if !monitor_netlist_construction
   then (print (a^":  "); time f x)
   else f x;

val comb_tm = ``COMB``
val bus_concat_tm = ``BUS_CONCAT``;

fun CIRC_CONV c = RATOR_CONV (RAND_CONV c);
val CIRC_RULE = CONV_RULE o CIRC_CONV;

fun COMB_FN_CONV cnv tm =
  case strip_comb tm
   of (c,[_,_]) =>
        if same_const c comb_tm
         then RATOR_CONV(RAND_CONV cnv) tm
         else raise Conv.UNCHANGED
    | other => raise Conv.UNCHANGED

fun variants V [] = []
  | variants V (h::t) =
     let val h' = variant V h
     in h'::variants (h'::V) t
     end;

val is_prod = Lib.can pairSyntax.dest_prod;

val bus_concat_tm = prim_mk_const{Name="BUS_CONCAT",Thy="compile"};

fun mk_bus_concat(tm1,tm2) =
 let val (ty1,ty2) = dom_rng(type_of tm1)
     val (ty1',ty3) = dom_rng(type_of tm2)
 in
  list_mk_comb(inst[alpha |-> ty1, beta |-> ty2, gamma |-> ty3] bus_concat_tm,
               [tm1,tm2])
 end;

val dest_bus_concat = dest_binop bus_concat_tm (ERR"dest_bus_concat" "");

fun bus_concat_of ty V =
 let open pairSyntax
 in
   if is_prod ty
    then let val (ty1,ty2) = dest_prod ty
             val (l,V') = bus_concat_of ty1 V
             val (r,V'') = bus_concat_of ty2 V'
         in (mk_bus_concat(l,r),V'')
         end
    else (hd V, tl V)
 end;

(*---------------------------------------------------------------------------*)
(* STEP 4                                                                    *)
(*---------------------------------------------------------------------------*)

fun FUN_EXISTS_PROD_CONV tm =
 if is_exists tm andalso
    Lib.can (match_type ``:'a -> 'b#'c``)
            (type_of (bvar (rand tm)))
 then
   let val (forig,body) = dest_exists tm
       val fty = type_of forig
       val f = mk_var("f",fty)
       val P = mk_var("P",fty --> bool)
       val (ty1,ty2) = dom_rng fty
       val ty2list = strip_prod ty2
       val vartys = map (curry op--> ty1) ty2list
       val init_vars = map mk_var
                        (zip (map (strcat "f_" o Int.toString)
                                  (upto 1 (length vartys)))
                             vartys)
       val vars = variants (free_vars tm) init_vars
       val bus_concatenation = fst(bus_concat_of ty2 vars)
       val absgoal = mk_eq(mk_exists(f,mk_comb(P,f)),
             list_mk_exists(vars,mk_comb(P,bus_concatenation)))
       val tac = CONV_TAC (LHS_CONV (TOP_SWEEP_CONV
                                      (HO_REWR_CONV FUN_EXISTS_PROD)))
                    THEN REFL_TAC
       val th = prove(absgoal,tac)
   in
     HO_REWR_CONV th tm
   end
 else raise ERR "FUN_EXISTS_PROD_CONV" "";

val OLD_STEP4a =  (* split buses up *)
 let open Ho_Rewrite
 in
  ptime "\n4a"
   (CONV_RULE (CIRC_CONV
     (GEN_REWRITE_CONV TOP_SWEEP_CONV [FUN_EXISTS_PROD])))
 end;


val STEP4a =  (* split buses up *)
 let open Ho_Rewrite
 in
  ptime "\n4a"
   (CONV_RULE (CIRC_CONV
     (TOP_SWEEP_CONV FUN_EXISTS_PROD_CONV)))
 end;

val STEP4b =  (* build names in COMBs *)
 let open Ho_Rewrite
 in
  ptime "4b"
   (CONV_RULE (CIRC_CONV
     (TOP_SWEEP_CONV (COMB_FN_CONV
       (GEN_REWRITE_CONV TOP_SWEEP_CONV [LAMBDA_PROD] THENC
        GEN_REWRITE_CONV DEPTH_CONV [FST,SND])))))
 end;


val STEP4c =  (* expose f<>g *)
 let open Ho_Rewrite
 in
  ptime "4c"
   (CONV_RULE (CIRC_CONV
     (GEN_REWRITE_CONV TOP_SWEEP_CONV [GSYM BUS_CONCAT_def])))
 end;

val STEP4d =
 let open Ho_Rewrite
 in
  ptime "4d"
   (CONV_RULE (CIRC_CONV
     (GEN_REWRITE_CONV TOP_DEPTH_CONV
           [COMB_CONCAT_FST,COMB_CONCAT_SND,
            COMB_FST,COMB_SND,
(*          COMB_CONSTANT_1,COMB_CONSTANT_2,COMB_CONSTANT_3, *)
            COMB_ID])))
 end;

val STEP4e =
 let open Ho_Rewrite
 in
  ptime "4e"
   (CONV_RULE (CIRC_CONV
     (GEN_REWRITE_CONV TOP_DEPTH_CONV [LATCH_def,POSEDGE_IMP_def])))
 end;

val STEP4f =
 let open Ho_Rewrite
 in
  ptime "4f"
   (CONV_RULE (CIRC_CONV
     (GEN_REWRITE_CONV TOP_DEPTH_CONV
        [ID_CONST, ID_o, o_ID,
         DEL_CONCAT,MUX_CONCAT,DFF_CONCAT,
         BUS_CONCAT_PAIR,BUS_CONCAT_ETA])))
 end;

val STEP4 = STEP4f o STEP4e o STEP4d o STEP4c o STEP4b o STEP4a;

(*---------------------------------------------------------------------------*)
(* STEP 5 applies theorem                                                    *)
(*                                                                           *)
(*  BUS_CONCAT_ELIM = |- (\x1. P1 x1) <> (\x2. P2 x2) = (\x. (P1 x,P2 x))    *)
(*                                                                           *)
(* Contorted code because of efficiency hacks.                               *)
(*---------------------------------------------------------------------------*)

(*
fun CONCAT_CONV c M =
  if is_abs M then ABS_CONV (CONCAT_CONV c) M else
  case strip_comb M
   of (f,[_,_]) => if same_const f bus_concat_tm
         then c M
         else COMB_CONV (CONCAT_CONV c) M
    | otherwise => if is_comb M then COMB_CONV (CONCAT_CONV c) M
                   else ALL_CONV M;

local (* partial evaluation instantiates term-nets once *)
 val SIMPLIFY = RATOR_CONV(RAND_CONV(CONCAT_CONV
      (PURE_REWRITE_CONV [K_INTRO_THM,I_INTRO_THM,BUS_CONCAT_LIFTERS] THENC
       PURE_REWRITE_CONV [BUS_CONCAT_LIFTERS1] THENC
       PURE_REWRITE_CONV [o_DEF,C_THM] THENC
       PURE_ONCE_REWRITE_CONV [GSYM ETA_THM] THENC
       PURE_REWRITE_CONV [K_THM,C_THM,I_THM] THENC DEPTH_CONV BETA_CONV)))
in
fun STEP5a_CONV tm =
  case strip_comb tm
   of (c,[f,x]) =>x
        if same_const c comb_tm andalso
           Lib.can (find_term (same_const bus_concat_tm)) f
         then SIMPLIFY tm
         else raise ERR "STEP5_CONV" ""
    | other => raise ERR "STEP5_CONV" ""
end;

val STEP5_CONV = Ho_Rewrite.REWRITE_CONV
   [BUS_CONCAT_ELIM(*,DFF_IMP_def,POSEDGE_IMP_def,LATCH_def*)]
*)

fun LAMBDA_CONCAT_CONV tm =
 let val (t1,t2) = dest_bus_concat tm
     val _ = assert is_abs t1
     val _ = assert is_abs t2
     val bus_concat_thm = ISPECL [t1,t2] BUS_CONCAT_def
 in
   CONV_RULE (RHS_CONV (ABS_CONV (BINOP_CONV BETA_CONV)))
             bus_concat_thm
 end

fun STEP5_CONV tm =
  case strip_comb tm
   of (c,[f,x]) =>
        if same_const c comb_tm
         then RATOR_CONV(RAND_CONV(DEPTH_CONV LAMBDA_CONCAT_CONV)) tm
         else raise ERR "STEP5_CONV" ""
    | other => raise ERR "STEP5_CONV" "";

(*---------------------------------------------------------------------------*)
(* Translate a DEV into a netlist                                            *)
(*---------------------------------------------------------------------------*)

val MAKE_NETLIST =
 ((ptime "9" (CONV_RULE(RATOR_CONV(RAND_CONV EXISTS_OUT_CONV)))) o
  (ptime "8" (PURE_REWRITE_RULE[DEL_CONCAT,GSYM COMB_NOT,
                     GSYM COMB_AND, GSYM COMB_OR, GSYM COMB_MUX])) o
  (ptime "7" (CONV_RULE(RATOR_CONV(RAND_CONV(REDEPTH_CONV(COMB_SYNTH_CONV)))))) o
  (ptime "6" (PURE_REWRITE_RULE [UNCURRY,FST,SND]))                o
  (ptime "5-6" (REWRITE_RULE [DFF_IMP_def,POSEDGE_IMP_def,LATCH_def]))  o
  (ptime "5" (CONV_RULE (CIRC_CONV (ONCE_DEPTH_CONV STEP5_CONV)))) o
  (ptime "4-5" (DEV_IMP (DEPTH_IMP DFF_IMP_INTRO)))                o
  (ptime "4" STEP4)          o
  (ptime "3" GEN_BETA_RULE)  o
  (ptime "2" IN_OUT_SPLIT)   o
  (ptime "1" (REWRITE_RULE
   [POSEDGE_IMP,CALL,SELECT,FINISH,ATM,SEQ,PAR,ITE,REC,
    ETA_THM,PRECEDE_def,FOLLOW_def,PRECEDE_ID,FOLLOW_ID,
    Let_def,Ite_def,Par_def,Seq_def,o_THM])));


(*----------------ORIGINAL (mostly)----------------------------------
val OLD_STEP4 =
 ptime "4"
   (CONV_RULE (CIRC_CONV(Ho_Rewrite.REWRITE_CONV
     [FUN_EXISTS_PROD,LAMBDA_PROD,COMB_ID,
(*    COMB_CONSTANT_1,COMB_CONSTANT_2,COMB_CONSTANT_3,  *)
      COMB_FST,COMB_SND,GSYM BUS_CONCAT_def,
      BUS_CONCAT_PAIR,BUS_CONCAT_o,
      FST,SND,BUS_CONCAT_ETA,ID_CONST,ID_o,o_ID,
      DEL_CONCAT,DFF_CONCAT,MUX_CONCAT,
      POSEDGE_IMP_def,LATCH_def,
      COMB_CONCAT_FST,COMB_CONCAT_SND,COMB_OUT_SPLIT])));

fun MAKE_NETLIST devth =
 ((ptime "9" (CONV_RULE(RATOR_CONV(RAND_CONV EXISTS_OUT_CONV)))) o
(*  (ptime "8"  (Ho_Rewrite.REWRITE_RULE (!combinational_components))) o *)
  (ptime "8"  (PURE_REWRITE_RULE (!combinational_components))) o
  (ptime "7" (CONV_RULE(RATOR_CONV(RAND_CONV(REDEPTH_CONV(COMB_SYNTH_CONV)))))) o
(*  (ptime "7" (SIMP_RULE std_ss [UNCURRY]))           o *)
  (ptime "6" (REWRITE_RULE [UNCURRY,FST,SND]))           o
(*  (ptime "5" (Ho_Rewrite.REWRITE_RULE [BUS_CONCAT_ELIM])) o *)
  (ptime "5" (CONV_RULE (CIRC_CONV (DEPTH_CONV STEP5_CONV)))) o
  (ptime "4" (Ho_Rewrite.REWRITE_RULE
    [FUN_EXISTS_PROD,LAMBDA_PROD,COMB_ID,
(*   COMB_CONSTANT_1,COMB_CONSTANT_2,COMB_CONSTANT_3, *)
     COMB_FST,COMB_SND,GSYM BUS_CONCAT_def,
     BUS_CONCAT_PAIR,BUS_CONCAT_o,
     FST,SND,BUS_CONCAT_ETA,ID_CONST,ID_o,o_ID,
     DEL_CONCAT,DFF_CONCAT,MUX_CONCAT,
     POSEDGE_IMP_def,LATCH_def,
     COMB_CONCAT_FST,COMB_CONCAT_SND,COMB_OUT_SPLIT]))  o
  (ptime "3" GEN_BETA_RULE)  o
  (ptime "2" IN_OUT_SPLIT)   o
  (ptime "1" (REWRITE_RULE
   [POSEDGE_IMP,CALL,SELECT,FINISH,ATM,SEQ,PAR,ITE,REC,
    ETA_THM,PRECEDE_def,FOLLOW_def,PRECEDE_ID,FOLLOW_ID,
    Ite_def,Par_def,Seq_def,o_THM]))) devth;
 ---------------------------------------------------------------------------*)

(*****************************************************************************)
(* User modifiable list of Melham-style temporal abstraction theorem         *)
(*****************************************************************************)

val temporal_abstractions = ref([] : thm list);

fun add_temporal_abstractions thl =
 (temporal_abstractions :=
   thl @ (!temporal_abstractions));

val _ =
 add_temporal_abstractions
  [UNDISCH DEL_IMP,
   UNDISCH DELT_IMP,
   UNDISCH DELF_IMP,
   COMB_at,
   CONSTANT_at,
   TRUE_at,
   FALSE_at,
   NOT_at,
   AND_at,
   OR_at,
   MUX_at];

(*****************************************************************************)
(* Compile a device implementation into a clocked circuit represented in HOL *)
(*****************************************************************************)
(* Unoptimized *)
fun MAKE_CIRCUIT devth =
 (DISCH_ALL                                                                  o
  LIST_ANTE_EXISTS_INTRO                                                     o
  (I ## AP_ANTE_IMP_TRANS (DEPTH_IMP (IMP_REFINEL(!temporal_abstractions)))) o
  (I ## Ho_Rewrite.REWRITE_RULE[at_CONCAT])                                  o
  at_SPEC_ALL ``clk:num->bool``                                              o
  GEN_ALL                                                                    o
  Ho_Rewrite.REWRITE_RULE[GSYM LEFT_FORALL_IMP_THM,DEL_CONCAT]               o
  CONV_RULE(RATOR_CONV(RAND_CONV EXISTS_OUT_CONV))                           o
  Ho_Rewrite.REWRITE_RULE (!combinational_components)                        o
  CONV_RULE
   (RATOR_CONV(RAND_CONV(REDEPTH_CONV(COMB_SYNTH_CONV))))                    o
  SIMP_RULE std_ss [UNCURRY]                                                 o
  Ho_Rewrite.REWRITE_RULE
   [BUS_CONCAT_ELIM,DFF_IMP_def,POSEDGE_IMP_def,LATCH_def]                   o
  DEV_IMP (DEPTH_IMP DFF_IMP_INTRO)                                          o
  Ho_Rewrite.REWRITE_RULE
    [FUN_EXISTS_PROD,LAMBDA_PROD,COMB_ID,
(*   COMB_CONSTANT_1,COMB_CONSTANT_2,COMB_CONSTANT_3, *)
     COMB_FST,COMB_SND,GSYM BUS_CONCAT_def,
     BUS_CONCAT_PAIR,BUS_CONCAT_o,
     FST,SND,BUS_CONCAT_ETA,ID_CONST,ID_o,o_ID,
     DEL_CONCAT,DFF_CONCAT,MUX_CONCAT,
     DFF_IMP_def,POSEDGE_IMP_def,LATCH_def,
     COMB_CONCAT_FST,COMB_CONCAT_SND,COMB_OUT_SPLIT]                         o
  GEN_BETA_RULE                                                              o
  IN_OUT_SPLIT                                                               o
  REWRITE_RULE
   [POSEDGE_IMP,CALL,SELECT,FINISH,ATM,SEQ,PAR,ITE,REC,
    ETA_THM,PRECEDE_def,FOLLOW_def,PRECEDE_ID,FOLLOW_ID,
    Ite_def,Par_def,Seq_def,Let_def,o_THM]) devth;

(* Only generates DTYPE, CONSTANT, COMB *)
fun MAKE_CIRCUIT devth =
 ((ptime "17" DISCH_ALL)                                                     o
  (ptime "16" LIST_ANTE_EXISTS_INTRO)                                        o
  (ptime "15" (I ## AP_ANTE_IMP_TRANS (DEPTH_IMP (IMP_REFINEL(!temporal_abstractions))))) o
  (ptime "14" (I ## Ho_Rewrite.REWRITE_RULE[at_CONCAT]))                      o
  (ptime "13" (at_SPEC_ALL ``clk:num->bool``))                                o
  (ptime "12" GEN_ALL)                                                       o
  (ptime "11" (Ho_Rewrite.REWRITE_RULE
   [GSYM COMB_NOT, GSYM COMB_AND, GSYM COMB_OR, GSYM COMB_MUX,
    GSYM LEFT_FORALL_IMP_THM,DEL_CONCAT,COMB_COND_CONCAT]))   (* new *)       o
  (ptime "10" (CONV_RULE(RATOR_CONV(RAND_CONV EXISTS_OUT_CONV))))              o
  (ptime "9" (Ho_Rewrite.REWRITE_RULE[BUS_CONCAT_PAIR]))        (* new *)      o
  (ptime "8" (CONV_RULE (TOP_SWEEP_CONV FUN_EXISTS_PROD_CONV))) (* new *)      o
  (ptime "7" (CONV_RULE
     (RATOR_CONV(RAND_CONV(REDEPTH_CONV(COMB_SYNTH_CONV))))))                o
  (ptime "6-1" (SIMP_RULE std_ss [UNCURRY]))                                   o
  (ptime "6" (Ho_Rewrite.REWRITE_RULE
   [BUS_CONCAT_ELIM,DFF_IMP_def,POSEDGE_IMP_def,LATCH_def]))                  o
  (ptime "5" (DEV_IMP (DEPTH_IMP DFF_IMP_INTRO)))                              o
  (ptime "4" (Ho_Rewrite.REWRITE_RULE
    [FUN_EXISTS_PROD,LAMBDA_PROD,COMB_ID,
     COMB_FST,COMB_SND,GSYM BUS_CONCAT_def,
     BUS_CONCAT_PAIR,BUS_CONCAT_o,
     FST,SND,BUS_CONCAT_ETA,ID_CONST,ID_o,o_ID,DEL_CONCAT,DFF_CONCAT,
     MUX_CONCAT,DFF_IMP_def,POSEDGE_IMP_def,LATCH_def,
     COMB_CONCAT_FST,COMB_CONCAT_SND,COMB_OUT_SPLIT]))                        o
  (ptime "3" GEN_BETA_RULE)                                                  o
  (ptime "2" IN_OUT_SPLIT)                                                   o
  (ptime "1" (REWRITE_RULE
   [POSEDGE_IMP,CALL,SELECT,FINISH,ATM,SEQ,PAR,ITE,REC,
    ETA_THM,PRECEDE_def,FOLLOW_def,PRECEDE_ID,FOLLOW_ID,
    Ite_def,Par_def,Seq_def,Let_def,o_THM]))) devth;

(*---------------------------------------------------------------------------*)
(* Optimized                                                                 *)
(*---------------------------------------------------------------------------*)

fun EXISTSL_CONV tm =
  ((LEFT_IMP_EXISTS_CONV THENC QUANT_CONV EXISTSL_CONV) ORELSEC ALL_CONV) tm;

val NEW_MAKE_CIRCUIT =
 (DISCH_ALL o
  (ptime "15" LIST_ANTE_EXISTS_INTRO)                                        o
  (ptime "14" (I ## AP_ANTE_IMP_TRANS
                      (DEPTH_IMP (IMP_REFINEL(!temporal_abstractions)))))    o
  (ptime "13" (I ## REWRITE_RULE[at_CONCAT]))                                o
  (ptime "12" (at_SPEC_ALL ``clk:num->bool``))                               o
  (ptime "11" GEN_ALL)                                                       o
  (ptime "10-11" (CONV_RULE EXISTSL_CONV)) o
  (ptime "10" (PURE_REWRITE_RULE[DEL_CONCAT,GSYM COMB_NOT, GSYM COMB_AND,
               GSYM COMB_OR, GSYM COMB_MUX])) o
  (ptime "9-2" (Ho_Rewrite.REWRITE_RULE
                [GSYM COMB_NOT,GSYM COMB_AND,GSYM COMB_OR,
                 GSYM COMB_MUX,GSYM LEFT_FORALL_IMP_THM,
                 DEL_CONCAT,COMB_COND_CONCAT])) o                   (* new *)
  (ptime "9-1" (CONV_RULE(RATOR_CONV(RAND_CONV EXISTS_OUT_CONV)))) o
  (ptime "8-2" (Ho_Rewrite.REWRITE_RULE[BUS_CONCAT_PAIR])) o        (* new *)
  (ptime "8-1" (CONV_RULE (TOP_SWEEP_CONV FUN_EXISTS_PROD_CONV))) o (* new *)
  (ptime "7" (CONV_RULE(RATOR_CONV(RAND_CONV(REDEPTH_CONV(COMB_SYNTH_CONV)))))) o
  (ptime "6-7" (PURE_REWRITE_RULE [UNCURRY,FST,SND]))                 o
  (ptime "6" (REWRITE_RULE [DFF_IMP_def,POSEDGE_IMP_def,LATCH_def]))  o
  (ptime "5" (CONV_RULE (CIRC_CONV (ONCE_DEPTH_CONV STEP5_CONV))))    o
  (ptime "4-5" (DEV_IMP (DEPTH_IMP DFF_IMP_INTRO)))                   o
  (ptime "4" STEP4)          o
  (ptime "3" GEN_BETA_RULE)  o
  (ptime "2" IN_OUT_SPLIT)   o
  (ptime "1" (REWRITE_RULE
   [POSEDGE_IMP,CALL,SELECT,FINISH,ATM,SEQ,PAR,ITE,REC,
    ETA_THM,PRECEDE_def,FOLLOW_def,PRECEDE_ID,FOLLOW_ID,
    Ite_def,Par_def,Seq_def,Let_def,o_THM])));


val NEW_MAKE_CIRCUIT' =
 (DISCH_ALL o
  (ptime "15" LIST_ANTE_EXISTS_INTRO)                                        o
  (ptime "14" (I ## AP_ANTE_IMP_TRANS
                      (DEPTH_IMP (IMP_REFINEL(!temporal_abstractions)))))    o
  (ptime "13" (I ## REWRITE_RULE[at_CONCAT]))                                o
  (ptime "12" (at_SPEC_ALL ``clk:num->bool``))                               o
  (ptime "11" GEN_ALL)                                                       o
  (ptime "10-11" (CONV_RULE EXISTSL_CONV)) o
  (ptime "10" (PURE_REWRITE_RULE[DEL_CONCAT,GSYM COMB_NOT, GSYM COMB_AND,
               GSYM COMB_OR, GSYM COMB_MUX])) o
  (ptime "9-2" (REWRITE_RULE
                [GSYM COMB_NOT,GSYM COMB_AND,GSYM COMB_OR,
                 GSYM COMB_MUX,GSYM LEFT_FORALL_IMP_THM,
                 DEL_CONCAT,COMB_COND_CONCAT])) o                   (* new *)
  (ptime "9-1" (CONV_RULE(RATOR_CONV(RAND_CONV EXISTS_OUT_CONV)))) o
  (ptime "8-2" (Ho_Rewrite.REWRITE_RULE[BUS_CONCAT_PAIR])) o        (* new *)
  (ptime "8-1" (CONV_RULE (TOP_SWEEP_CONV FUN_EXISTS_PROD_CONV))) o (* new *)
  (ptime "7" (CONV_RULE(RATOR_CONV(RAND_CONV(REDEPTH_CONV(COMB_SYNTH_CONV)))))) o
  (ptime "6-7" (PURE_REWRITE_RULE [UNCURRY,FST,SND]))                 o
  (ptime "6" (REWRITE_RULE [DFF_IMP_def,POSEDGE_IMP_def,LATCH_def]))  o
  (ptime "5" (CONV_RULE (CIRC_CONV (ONCE_DEPTH_CONV STEP5_CONV))))    o
  (ptime "4-5" (DEV_IMP (DEPTH_IMP DFF_IMP_INTRO)))                   o
  (ptime "4" STEP4)          o
  (ptime "3.1" (REWRITE_RULE [])) o
  (ptime "3" GEN_BETA_RULE)  o
  (ptime "2" IN_OUT_SPLIT)   o
  (ptime "1" (REWRITE_RULE
   [POSEDGE_IMP,CALL,SELECT,FINISH,ATM,SEQ,PAR,ITE,REC,
    ETA_THM,PRECEDE_def,FOLLOW_def,PRECEDE_ID,FOLLOW_ID,
    Ite_def,Par_def,Seq_def,Let_def,o_THM])));


val NEW_MAKE_CIRCUIT'' =
 (DISCH_ALL o
  (ptime "15" LIST_ANTE_EXISTS_INTRO)                                        o
  (ptime "14" (I ## AP_ANTE_IMP_TRANS
                      (DEPTH_IMP (IMP_REFINEL(!temporal_abstractions)))))    o
  (ptime "13" (I ## REWRITE_RULE[at_CONCAT]))                                o
  (ptime "12" (at_SPEC_ALL ``clk:num->bool``))                               o
  (ptime "11" GEN_ALL)                                                       o
  (ptime "10-11" (CONV_RULE EXISTSL_CONV)) o
  (ptime "10" (PURE_REWRITE_RULE[DEL_CONCAT,GSYM COMB_NOT, GSYM COMB_AND,
               GSYM COMB_OR, GSYM COMB_MUX])) o
  (ptime "9-2" (REWRITE_RULE
                [GSYM COMB_NOT,GSYM COMB_AND,GSYM COMB_OR,
                 GSYM COMB_MUX,GSYM LEFT_FORALL_IMP_THM,
                 DEL_CONCAT,COMB_COND_CONCAT])) o                   (* new *)
  (ptime "9-1" (CONV_RULE(RATOR_CONV(RAND_CONV EXISTS_OUT_CONV)))) o
  (ptime "8-2" (Ho_Rewrite.REWRITE_RULE[BUS_CONCAT_PAIR])) o        (* new *)
  (ptime "8-1" (CONV_RULE (TOP_SWEEP_CONV FUN_EXISTS_PROD_CONV))) o (* new *)
  (ptime "7" (CONV_RULE(RATOR_CONV(RAND_CONV(REDEPTH_CONV(COMB_SYNTH_CONV)))))) o
  (ptime "6-7" (PURE_REWRITE_RULE [UNCURRY,FST,SND]))                 o
  (ptime "6" (REWRITE_RULE [DFF_IMP_def,POSEDGE_IMP_def,LATCH_def]))  o
  (ptime "5" (CONV_RULE (CIRC_CONV (ONCE_DEPTH_CONV STEP5_CONV))))    o
  (ptime "4-5" (DEV_IMP (DEPTH_IMP DFF_IMP_INTRO)))                   o
  (ptime "4" STEP4)          o
  (ptime "3" ((REWRITE_RULE []) o GEN_BETA_RULE)) o
  (ptime "2"   (IN_OUT_SPLIT)) o
  (ptime "1.2" (REWRITE_RULE [POSEDGE_IMP,CALL,SELECT,FINISH,
                             ATM,SEQ,PAR,ITE,REC,
                             ETA_THM])) o
  (ptime "1.1" ((REWRITE_RULE []) o GEN_BETA_RULE)) o
  (ptime "1" (REWRITE_RULE  [PRECEDE_def,FOLLOW_def,PRECEDE_ID,FOLLOW_ID,
    Ite_def,Par_def,Seq_def,Let_def,o_THM]))) ;


(*****************************************************************************)
(* Expand occurrences of component names into their definitions              *)
(*****************************************************************************)

fun EXPAND_COMPONENTS th = (* Eta expanded to block !hwDefineLib evaluation  *)
 CONV_RULE
  (RATOR_CONV
   (REWRITE_CONV(mapfilter (Convert o #1) (!hwDefineLib))))
 th;

(*****************************************************************************)
(* Invoke hwDefine and then apply MAKE_CIRCUIT, EXPAND_COMPONENTS and        *)
(* REFINE_ALL to the device                                                  *)
(*****************************************************************************)

fun cirDefine qdef =
 let val (def,ind,dev) = hwDefine qdef
 in
  (def, ind, MAKE_CIRCUIT(EXPAND_COMPONENTS(REFINE_ALL dev)))
 end;

fun newcirDefine qdef =
 let val (def,ind,dev) = hwDefine qdef
 in
  (def, ind, NEW_MAKE_CIRCUIT(EXPAND_COMPONENTS(REFINE_ALL dev)))
 end;

(*---------------------------------------------------------------------------*)
(* Don't go all the way to circuits. Instead stop at netlists built from     *)
(* COMB, CONSTANT, DEL and DELT.                                             *)
(*---------------------------------------------------------------------------*)

fun netDefine qdef =
 let val (def,ind,dev) = hwDefine qdef
 in
   (def,ind,MAKE_NETLIST(EXPAND_COMPONENTS(REFINE_ALL dev)))
 end;

end (* struct *)
