(*---------------------------------------------------------------------------*)
(* Slightly optimised compiler                                               *)
(*                                                                           *)
(* We apply a peephole optmisation similar to PRECEDE and FOLLOW during the  *)
(* compilation. The compiler tries to reduce the number of SEQs, PARs and    *)
(* and ITEs.                                                                 *)
(*                                                                           *)
(* The difference between this version and the original compiler is that we  *)
(* replace the function calls with their bodies in the function main (inline *)
(* expansion).                                                               *)
(*                                                                           *)
(* This takes advantage of a global view of the structure of the hardware    *)
(* instead of being restricted to the scope of a single function body.       *)
(*                                                                           *)
(* In order to implement the rewriting of the main function,                 *)
(* alternative definitions for hwDefine, compileExp, compileProg and         *)
(* compile are created.                                                      *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* START BOILERPLATE                                                         *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Load theories                                                             *)
(*---------------------------------------------------------------------------*)
(*
quietdec := true;
loadPath :="dff" :: !loadPath;
map load ["compile"];
open compile;
quietdec := false;
*)

(*---------------------------------------------------------------------------*)
(* Boilerplate needed for compilation                                        *)
(*---------------------------------------------------------------------------*)
open HolKernel (* Parse boolLib bossLib compileTheory compile;*)

(*---------------------------------------------------------------------------*)
(* Open theories                                                             *)
(*---------------------------------------------------------------------------*)
open compile;

(*---------------------------------------------------------------------------*)
(* END BOILERPLATE                                                           *)
(*---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*)
(* hwDefine2                                                                 *)
(* Works just like hwDefine, except that it returns:                         *)
(*  (|- eqns, |- ind, |- dev, |- def, |- tot )                               *)
(* where the def is the function defined in terms of Seq, Par, Ite, Rec      *)
(* and tot is the theorem that proves termination for recursive functions    *)
(*                                                                           *)
(* The results of hwDefine2 are stored in an reference hwDefineLib2.         *)
(*---------------------------------------------------------------------------*)
val hwDefineLib2 = ref([] : (thm * thm * thm * thm * thm) list);
val terminationTheorems = ref([]: thm list);

fun addTerminationTheorems th = (terminationTheorems := th::(!terminationTheorems));

val _ = addTerminationTheorems wordsTheory.WORD_PRED_THM;

fun hwDefine2 defq =
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
                              THEN (PROVE_TAC (!terminationTheorems))]
            val (defth,ind) = Defn.tprove(defn, tac)
            val (lt,rt) = boolSyntax.dest_eq(concl defth)
            val (func,args) = dest_comb lt
            val (test,t1,t2) = dest_cond rt
            val fb = mk_pabs(args,test)
            val f1 = mk_pabs(args,t1)
            val f2 = mk_pabs(args,rand t2)
            val totalth = prove
                    (Term`TOTAL(^fb,^f1,^f2)`,
                     RW_TAC std_ss [TOTAL_def,pairTheory.FORALL_PROD]
                      THEN EXISTS_TAC typedf
                      THEN TotalDefn.TC_SIMP_TAC
                      THEN (PROVE_TAC (!terminationTheorems)))
            val devth = PURE_REWRITE_RULE [GSYM DEV_IMP_def]
                                 (RecCompileConvert defth totalth)
        in
         hwDefineLib2 := (defth,ind,devth,RecConvert defth totalth,totalth)
                        :: !hwDefineLib2;
         (defth,ind,devth,RecConvert defth totalth,totalth)
        end
     | otherwise =>
        let val defth = SPEC_ALL(Define defq)
            val _ =
             if occurs_in
                 (fst(strip_comb(lhs(concl defth))))
                 (rhs(concl defth))
              then (print "definition of ";
                    print (fst(dest_const(fst(strip_comb(lhs(concl defth))))));
                    print " is recusive; must have a measure";
                    raise ERR "hwDefine2" "recursive definition without a measure")
              else ()
            val conv = Convert defth
            val devth = PURE_REWRITE_RULE[GSYM DEV_IMP_def] (Compile conv)
        in
         hwDefineLib2 := (defth,boolTheory.TRUTH,devth,conv,boolTheory.TRUTH) ::
                        !hwDefineLib2;
         (defth,boolTheory.TRUTH,devth,conv,boolTheory.TRUTH)
        end
 end;


(*---------------------------------------------------------------------------*)
(* CompileExp2 exp                                                           *)
(* -->                                                                       *)
(* [REC assumption] |- <circuit> ===> DEV exp                                *)
(*---------------------------------------------------------------------------*)
fun CompileExp2 tm =
 let fun is_atm th = term_to_string(rator(rand(rator(snd(dest_thm th)))))="DEV"
     fun get_function th = rand(rand(rator(snd(dest_thm th))))
     val _ = if not(fst(dest_type(type_of tm)) = "fun")
              then (print_term tm; print "\n";
                    print "Devices can only compute functions.\n";
                    raise ERR "CompileExp2" "attempt to compile non-function")
              else ()
     val (opr,args) = dest_exp tm
                      handle HOL_ERR _
                      => raise ERR "CompileExp2" "bad expression"
 in
  if null args orelse is_combinational tm
     then ISPEC ``DEV ^tm`` DEV_IMP_REFL
  else
    case fst(dest_const opr) of
       "Seq" => let val th1 = CompileExp2(hd args)
                    val th2 = CompileExp2(hd(tl args))
                in
                if is_atm th1 andalso is_atm th2 then
                   ISPEC ``DEV (Seq ^ (get_function th1) ^ (get_function th2))``
                   DEV_IMP_REFL
                else if (is_atm th1) andalso not(is_atm th2) then
                   MATCH_MP (ISPEC (get_function th1) PRECEDE_DEV) th2
                else if not(is_atm th1) andalso (is_atm th2) then
                   MATCH_MP (ISPEC (get_function th2) FOLLOW_DEV)  th1
                else
                   MATCH_MP SEQ_INTRO (CONJ th1 th2)
                end
     | "Par" => let val th1 = CompileExp2(hd args)
                    val th2 = CompileExp2(hd(tl args))
                in
                if is_atm th1 andalso is_atm th2 then
                   ISPEC ``DEV (Par ^ (get_function th1) ^ (get_function th2))``
                   DEV_IMP_REFL
                else
                   MATCH_MP PAR_INTRO (CONJ th1 th2)
                end
     | "Ite" => let val th1 = CompileExp2(hd args)
                    val th2 = CompileExp2(hd(tl args))
                    val th3 = CompileExp2(hd(tl(tl args)))
                in
                if is_atm th1 andalso is_atm th2 andalso is_atm th3 then
                   ISPEC ``DEV (Ite ^ (get_function th1) ^ (get_function th2)
                                    ^ (get_function th3))``
                   DEV_IMP_REFL
                else
                   MATCH_MP ITE_INTRO (LIST_CONJ [th1,th2,th3])
                end
     | "Rec" => let val thl = map (CompileExp2) args
                    val var_list = map (rand o rand o concl o SPEC_ALL) thl
                   in
                    MATCH_MP
                     (UNDISCH(SPEC_ALL(ISPECL var_list REC_INTRO)))
                     (LIST_CONJ thl)
                   end
     | "Let" => let val th1 = REWR_CONV Let tm
                    val th2 = CompileExp2(rhs(concl th1))
                in
                 CONV_RULE (RAND_CONV(RAND_CONV(REWR_CONV(SYM th1)))) th2
                end
     | _     => raise ERR "CompileExp2" "this shouldn't happen"
 end;



(*---------------------------------------------------------------------------*)
(* CompileProg2 prog tm --> rewrite tm with prog, then compiles the result   *)
(*---------------------------------------------------------------------------*)
fun CompileProg2 prog tm =
 let val expand_th = REWRITE_CONV prog tm
     val compile_th = CompileExp2 (rhs(concl expand_th))
 in
  CONV_RULE (RAND_CONV(REWRITE_CONV[GSYM expand_th])) compile_th
 end;

(*---------------------------------------------------------------------------*)
(* Compile2 (|- f args = bdy) = CompileProg [|- f args = bdy] ``f``          *)
(*---------------------------------------------------------------------------*)
fun Compile2 th =
 let val (func,_) =
      dest_eq(concl(SPEC_ALL th))
      handle HOL_ERR _ => raise ERR "Compile2" "not an equation"
     val _ = if not(is_const func)
              then raise ERR "Compile" "rator of lhs not a constant"
              else ()
 in
  CompileProg2 [th] func
 end;



(*---------------------------------------------------------------------------*)
(* convertTotal                                                              *)
(* Rewrites the terms in the proof of totality into ones defined in terms    *)
(* Seq, Par, Ite, and Rec followed by inline expansions                      *)
(* See the example at the end of the file.                                   *)
(*---------------------------------------------------------------------------*)
fun convertTotal defths totalth =
    let val (f1,f2f3) = (dest_pair o snd o dest_comb o concl) totalth
        val (f2,f3) = dest_pair f2f3

        val f1th = Convert_CONV f1
        val f2th = Convert_CONV f2
        val f3th = Convert_CONV f3

        fun inline th = let val tm = (snd o dest_eq o snd o dest_thm) th
                        in REWRITE_CONV defths tm handle _ => REFL tm
                        end

        val f1' = (snd o dest_eq o concl) (inline f1th)
        val f2' = (snd o dest_eq o concl) (inline f2th)
        val f3' = (snd o dest_eq o concl) (inline f3th)

   in prove(``^(concl totalth) = TOTAL( ^f1', ^f2' ,^f3')``,
            RW_TAC std_ss (defths @ [f1th,f2th,f3th]))
   end;


(*---------------------------------------------------------------------------*)
(* inlineCompile                                                             *)
(* Performs an inline expansion before compiling                             *)
(*---------------------------------------------------------------------------*)
fun inlineCompile maintm defths totalths =
       let fun findMain th = ((fst o dest_eq o concl) th) = maintm
           val maindef = hd(filter findMain defths)
           val auxdefths = filter (fn th => not(findMain th)) defths
           val mainth = REFINE (DEPTHR ATM_REFINE)
              (Compile2 ((CONV_RULE (REWRITE_CONV (Let::auxdefths))) maindef))
       in prove(concl mainth,
                METIS_TAC ((DISCH_ALL mainth) ::
                           (totalths @ (map (convertTotal (Let::defths)) totalths))))
       end;



(*---------------------------------------------------------------------------
  Example:

  load "vsynth";open vsynth;


  val (MULT_def,_,_,MULT_c,MULT_t) = hwDefine2
      `(MULT(n:num,m:num,acc) = if n=0 then acc else MULT(n-1,m,m+acc))
       measuring FST`;

  val (FACT_def,_,_,FACT_c,FACT_t) = hwDefine2
      `(FACT(n,acc) = if n=0 then acc else FACT(n-1,MULT(n,acc,0)))
       measuring FST`;

   (* Example of convertTotal *)
   convertTotal [MULT_c] FACT_t;

   (* Example of inlineCompile *)
   val FACT_dev = inlineCompile ``FACT`` [FACT_c,MULT_c] [MULT_t,FACT_t];

   val FACT_dev = inlineCompile ``FACT`` [FACT_c] [FACT_t];


  val _ = AddBinop("cSUBT", (``UNCURRY $- : num#num->num`` ,"-"));
  val _ = AddBinop("cEQ",  (``UNCURRY $= : num#num->bool``,"=="));
(*  val _ = AddUnop("cMULT", (``MULT :num#num#num->num``,"*")); *)
  val _ = add_combinational ["MULT"];

   val FACT_cir = NEW_MAKE_CIRCUIT FACT_dev;

---------------------------------------------------------------------------*)




