
(*****************************************************************************)
(* Very simple compiler, with programs represented as ML list of HOL         *)
(* definitions.                                                              *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)
(******************************************************************************
* Load theories
******************************************************************************)
(*
quietdec := true;
map load  ["composeTheory","compileTheory"];
open arithmeticTheory pairLib pairTheory PairRules combinTheory 
     composeTheory compileTheory;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib compileTheory;

(******************************************************************************
* Open theories
******************************************************************************)
open arithmeticTheory pairLib pairTheory PairRules combinTheory 
     composeTheory compileTheory;

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
fun Convert_CONV f =
 let val (args,t) = 
         dest_pabs f
         handle HOL_ERR _
          => (print_term f; print"\n";
              print "is not an abstraction\n";
              raise ERR "Convert_CONV" "not an abstraction")
  in
  if not(free_vars f = []) 
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
     val (func,args) = 
         dest_comb lt
         handle HOL_ERR _ => 
         (print "lhs not a comb\n"; 
          raise ERR "Convert" "lhs not a comb")
     val _ = if not(is_const func)
              then (print_term func; print " is not a constant\n";
                    raise ERR "Convert" "rator of lhs not a constant")
              else ()
     val _ = if not(subtract (free_vars rt) (free_vars lt) = [])
              then (print "definition rhs has unbound variables: "; 
                    map (fn t => (print_term t; print " "))
                        (rev(subtract (free_vars rt) (free_vars lt))); 
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
     val _ = if not(subtract (free_vars rt) (free_vars lt) = [])
              then (print "definition rhs has unbound variables: "; 
                    map (fn t => (print_term t; print " "))
                        (rev(subtract (free_vars rt) (free_vars lt))); 
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
       val _  = if aconv (concl(SPEC_ALL totalth)) ``TOTAL(^fb,^f1,^f2)``
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
       val th4 = REWRITE_RULE
                  [thb,th1,th2,PALPHA  (fst(dest_imp(concl th3))) ptm]
                  th3
       val th5 = MP th4 (PGEN args defth)
   in
    CONV_RULE
     (RHS_CONV 
      ((RAND_CONV Convert_CONV) 
        THENC (RATOR_CONV(RAND_CONV Convert_CONV))
        THENC (RATOR_CONV(RATOR_CONV(RAND_CONV Convert_CONV)))))
     th5
   end
  else if occurs_in func rt
   then (print "definition of: "; print_term func; 
         print " is not tail recursive"; print "\n";
         raise ERR "RecConvert" "not tail recursive")
   else raise ERR "RecConvert" "this shouldn't happen"
 end;

(*****************************************************************************)
(* CompileExp exp                                                            *)
(* -->                                                                       *)
(* [REC assumption] |- <circuit> ===> DEV exp                                *)
(*****************************************************************************)
fun CompileExp tm =
 if not(fst(dest_type(type_of tm)) = "fun")
  then (print_term tm;print "\n";
        print "is not a function -- can only compile functions";
        raise ERR "CompileExp" "attempt to compile a non-function")
  else if is_comb tm 
          andalso is_const(fst(strip_comb tm))
          andalso mem (fst(dest_const(fst(strip_comb tm)))) ["Seq","Par","Ite","Rec"]
  then
   let val (opr,args) = strip_comb tm
   in
   case fst(dest_const opr) of
      "Seq" => MATCH_MP SEQ_INTRO (LIST_CONJ(map CompileExp args))
    | "Par" => MATCH_MP PAR_INTRO (LIST_CONJ(map CompileExp args))
    | "Ite" => MATCH_MP ITE_INTRO (LIST_CONJ(map CompileExp args))
    | "Rec" => let val thl = map (CompileExp) args
                   val var_list = map (rand o rand o concl o SPEC_ALL) thl
               in
                MATCH_MP
                 (UNDISCH(SPEC_ALL(ISPECL var_list REC_INTRO)))
                 (LIST_CONJ thl)
               end
    | _     => raise ERR "CompileExp" "this shouldn't happen"
   end
  else ISPEC ``DEV ^tm`` DEV_IMP_REFL;

(*****************************************************************************)
(* Compile prog tm --> rewrite tm with prog, then compile result             *)
(*****************************************************************************)
fun Compile prog tm =
 let val expand_th = REWRITE_CONV prog tm
     val compile_th = CompileExp (rhs(concl expand_th))
 in
  REWRITE_RULE [GSYM expand_th] compile_th
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
(* Convert a non-recursive definition to an expression and then compile it.  *)
(*****************************************************************************)
fun ConvertCompile defth =
 let val (l,r) = 
      dest_eq(concl(SPEC_ALL defth))
      handle HOL_ERR _
      => (print "definitions must be equations\n";
          raise ERR "ConvertCompile" "not an equation")
     val (func,args) = 
      dest_comb l 
      handle HOL_ERR _
      => (print "lhs not a combination\n";
          raise ERR "ConvertCompile" "lhs not a combination")
     val _ = if not(is_const func)
              then (print_term func; print " is not a constant\n";
                    raise ERR "ConvertCompile" "rator of lhs not a constant")
              else ()
 in
  Compile [Convert defth] func
 end;

(*****************************************************************************)
(* Convert a recursive definition to an expression and then compile it.      *)
(*****************************************************************************)
fun RecConvertCompile defth totalth =
 let val (l,r) = dest_eq(concl(SPEC_ALL defth))
     val (func,args) = dest_comb l 
 in
  (SIMP_RULE std_ss [UNPAIR_TOTAL totalth] o
  GEN_BETA_RULE o
  SIMP_RULE std_ss [Seq_def,Par_def,Ite_def])
  (DISCH_ALL(Compile [RecConvert defth totalth] func))
 end;


fun mk_measure tm = 
   let open numSyntax
       val measure_tm = prim_mk_const{Name="measure",Thy="prim_rec"}
       val theta = match_type (alpha --> num) (type_of tm)
   in mk_comb(inst theta measure_tm, tm)
   end;

(*---------------------------------------------------------------------------*)
(* For termination prover.                                                   *)
(*---------------------------------------------------------------------------*)

val default_simps =
    [combinTheory.o_DEF,
     combinTheory.I_THM,
     prim_recTheory.measure_def,
     relationTheory.inv_image_def,
     pairTheory.LEX_DEF]

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
(* One can also not mention the measure function, as in Define:              *)
(*                                                                           *)
(*     hwDefine `eqns`                                                       *)
(*                                                                           *)
(* which will accept either non-recursive or recursive specifications. It    *)
(* returns a triple (|- eqns, |- ind, |- dev) where the ind theorem should   *)
(* be ignored (it will be numTheory.INDUCTION.                               *)
(*---------------------------------------------------------------------------*)

fun hwDefine defq =
 let val absyn0 = Parse.Absyn defq
     open Absyn pairSyntax
 in 
   case absyn0
    of APP(_,APP(_,IDENT(loc,"measuring"),def),f) =>
        let val (deftm,names) = Defn.parse_defn def
            val hdeqn = hd (boolSyntax.strip_conj deftm)
            val (l,r) = boolSyntax.dest_eq hdeqn
            val domty = pairSyntax.list_mk_prod 
                          (map type_of (snd (boolSyntax.strip_comb l)))
            val fty = Pretype.fromType (domty --> numSyntax.num)
            val typedf = Parse.absyn_to_term 
                             (Parse.term_grammar())
                             (TYPED(loc,f,fty))
            val defn = Defn.mk_defn (hd names) deftm
            val tac = EXISTS_TAC (mk_measure typedf)
                       THEN TotalDefn.TC_SIMP_TAC [] default_simps
            val (defth,ind) = Defn.tprove(defn, tac)
            val (lt,rt) = boolSyntax.dest_eq(concl defth)
            val (func,args) = dest_comb lt
            val (b,t1,t2) = dest_cond rt
            val fb = mk_pabs(args,b)
            val f1 = mk_pabs(args,t1)
            val f2 = mk_pabs(args,rand t2)
            val totalth = prove
                    (Term`TOTAL(^fb,^f1,^f2)`,
                     RW_TAC std_ss [TOTAL_def]
                      THEN EXISTS_TAC typedf
                      THEN TotalDefn.TC_SIMP_TAC [] default_simps)
            val devth = PURE_REWRITE_RULE [GSYM DEV_IMP_def]
                          (RecConvertCompile defth totalth)
        in
         (defth,ind,devth)
        end
     | otherwise => 
        let val defth = Define defq
            val devth = PURE_REWRITE_RULE[GSYM DEV_IMP_def] 
                          (ConvertCompile defth)
        in (defth,numTheory.INDUCTION,devth)
        end
 end;

(*****************************************************************************)
(* Recognisers, destructors and constructors for harware combinatory         *)
(* expressions.                                                              *)
(*****************************************************************************)

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
(* DEV                                                                       *)
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
(* ATMfn ``DEV f``  =  |- ATM f ===> DEV f : thm                             *)
(*                                                                           *)
(*****************************************************************************)
fun ATMfn tm =
 if not(is_comb tm 
         andalso is_const(rator tm)
         andalso (fst(dest_const(rator tm)) = "DEV"))
  then raise ERR "ATMfn" "argument not a DEV"
  else ISPEC (rand tm) ATM_INTRO;

(*****************************************************************************)
(* Lib                                                                       *)
(*  [|- <circuit> ===> DEV f1,                                               *)
(*   |- <circuit> ===> DEV f2                                                *)
(*   ...                                                                     *)
(*   |- <circuit> ===> DEV fn]                                               *)
(*  ``DEV fi``                                                               *)
(*                                                                           *)
(* returns the first theorem <circuit> ===> DEV fi                           *)
(* that it finds in the supplied list (i.e. library)                         *)
(*****************************************************************************)
fun Lib lib tm =
 if is_DEV tm
  then
   case
     List.find 
      (aconv tm o rand o concl o SPEC_ALL)
      lib
   of SOME th => th
    | NONE    => ISPEC tm DEV_IMP_REFL
  else raise ERR "Lib" "attempt to lookup a non-DEV";

(*****************************************************************************)
(* RefineExp refinefn tm scans through a combinatory expression tm built     *)
(* from ATM, SEQ, PAR, ITE, REC and DEV and applies the refinefn to all      *)
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
(* (if refinefn fails, then no action is taken, i.e. |- tm ===> tm used)     *)
(*****************************************************************************)
fun RefineExp refinefn tm =
 if is_DEV tm
  then (refinefn tm
        handle _ => ISPEC tm DEV_IMP_REFL)
 else if is_ATM tm
  then ISPEC tm DEV_IMP_REFL
 else if is_SEQ tm
  then
   let val (tm1,tm2) = dest_SEQ tm
       val th1 = RefineExp refinefn tm1
       val th2 = RefineExp refinefn tm2 
   in
    MATCH_MP SEQ_DEV_IMP (CONJ th1 th2)
   end
 else if is_PAR tm
  then
   let val (tm1,tm2) = dest_PAR tm
       val th1 = RefineExp refinefn tm1
       val th2 = RefineExp refinefn tm2 
   in
    MATCH_MP PAR_DEV_IMP (CONJ th1 th2)
   end
 else if is_ITE tm
  then
   let val (tm1,tm2,tm3) = dest_ITE tm
       val th1 = RefineExp refinefn tm1
       val th2 = RefineExp refinefn tm2 
       val th3 = RefineExp refinefn tm3 
   in
    MATCH_MP ITE_DEV_IMP (LIST_CONJ[th1,th2,th3])
   end
 else if is_REC tm
  then
   let val (tm1,tm2,tm3) = dest_REC tm
       val th1 = RefineExp refinefn tm1
       val th2 = RefineExp refinefn tm2 
       val th3 = RefineExp refinefn tm3 
   in
    MATCH_MP REC_DEV_IMP (LIST_CONJ[th1,th2,th3])
   end
 else (print_term tm; print"\n";
       raise ERR "RefineExp" "bad argument");

(*****************************************************************************)
(* Refine refinefn (|- <circuit> ===> Dev f) uses RefineExp to generate      *)
(*                                                                           *)
(*  |- <circuit'> ===> <circuit>                                             *)
(*                                                                           *)
(* and then uses transitivity of ===> to deduce                              *)
(*                                                                           *)
(*  |- <circuit'> ===> Dev f                                                 *)
(*****************************************************************************)
fun Refine refinefn th =
 MATCH_MP 
  DEV_IMP_TRANS 
  (CONJ (RefineExp refinefn (rand(rator(concl th)))) th)
 handle _ => raise ERR "Refine" "bad argument";

 
