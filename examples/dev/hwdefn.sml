map load  ["compile"];

quietdec := true;
    open arithmeticTheory pairLib pairTheory PairRules combinTheory
         composeTheory compileTheory compile;
quietdec := false;

(*---------------------------------------------------------------------------*)
(* Tag constant for the measure function. Used infix.                        *)
(*---------------------------------------------------------------------------*)

val _ = new_constant ("measuring", bool --> alpha --> bool);
add_infix ("measuring", 90, NONASSOC);

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
(*     hwDefine lib `(eqns) measuring f`                                     *)
(*                                                                           *)
(* will use f as the measure function and attempt automatic termination      *)
(* proof. If successful, returns (|- eqns, |- ind, |- dev)                   *)
(* NB. the recursion equations must be parenthesized; otherwise, strange     *)
(* parse errors result. Also, the name of the defined function must be       *)
(* alphanumeric.                                                             *)
(*                                                                           *)
(* One can also not mention the measure function, as in Define:              *)
(*                                                                           *)
(*     hwDefine lib `eqns`                                                   *)
(*                                                                           *)
(* which will accept either non-recursive or recursive specifications. It    *)
(* returns a triple (|- eqns, |- ind, |- dev) where the ind theorem should   *)
(* be ignored (it will be numTheory.INDUCTION.                               *)
(*---------------------------------------------------------------------------*)

fun hwDefine lib defq =
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
                          (RecConvertCompile lib defth totalth)
        in
         (defth,ind,devth)
        end
     | otherwise => 
        let val defth = Define defq
            val devth = PURE_REWRITE_RULE[GSYM DEV_IMP_def] 
                          (ConvertCompile lib defth)
        in (defth,numTheory.INDUCTION,devth)
        end
 end;



(*****************************************************************************)
(* Examples                                                                  *)
(*****************************************************************************)

(*****************************************************************************)
(* First build a naive iterative multiplier function (repeated addition)     *)
(*****************************************************************************)

val (MultIter,MultIter_ind,MultIter_dev) =
 hwDefine []
  `(MultIter (m,n,acc) =
      if m = 0 then (0,n,acc) else MultIter(m-1,n,n + acc))
   measuring FST`;


(*****************************************************************************)
(* Verify that MultIter does compute multiplication                          *)
(*****************************************************************************)

val MultIterRecThm =  (* proof adapted from similar one from KXS *)
 save_thm
  ("MultIterRecThm",
   Q.prove
    (`!m n acc. SND(SND(MultIter (m,n,acc))) = (m * n) + acc`,
     recInduct MultIter_ind THEN RW_TAC std_ss []
      THEN RW_TAC arith_ss [Once MultIter]
      THEN Cases_on `m` 
      THEN FULL_SIMP_TAC arith_ss [MULT]));

(*****************************************************************************)
(* Create an implementation of a multiplier from MultIter                    *)
(*****************************************************************************)

val (Mult,_,Mult_dev) =
 hwDefine [MultIter_dev]
  `Mult(m,n) = SND(SND(MultIter(m,n,0)))`;

(*****************************************************************************)
(* Verify Mult is actually multiplication                                    *)
(*****************************************************************************)

val MultThm =
 store_thm
  ("MultThm",
   Term`Mult = UNCURRY $*`,
   RW_TAC arith_ss [FUN_EQ_THM,FORALL_PROD,Mult,MultIterRecThm])

(*****************************************************************************)
(* Implement iterative function as a step to implementing factorial          *)
(* (use Mult to implement multiplication)                                    *)
(*****************************************************************************)

val (FactIter,FactIter_ind,FactIter_dev) =
 hwDefine
  [SUBS [MultThm] Mult_dev]
  `(FactIter (n,acc) =
      if n = 0 then (n,acc) else FactIter (n - 1,n * acc))
   measuring FST`;

(*****************************************************************************)
(* Alternative implementation with multiplication as atomic                  *)
(*****************************************************************************)

val (AltFactIter,AltFactIter_ind,AltFactIter_dev) =
 hwDefine []
  `AltFactIter (n,acc) =
     (if n = 0 then (n,acc) else AltFactIter (n - 1,n * acc))
    measuring FST`;

(*****************************************************************************)
(* Lemma showing how FactIter computes factorial                             *)
(*****************************************************************************)

val FactIterRecThm =  (* proof from KXS *)
 save_thm
  ("FactIterRecThm",
   Q.prove
    (`!n acc. SND(FactIter (n,acc)) = acc * FACT n`,
     recInduct FactIter_ind THEN RW_TAC arith_ss []
      THEN RW_TAC arith_ss [Once FactIter,FACT]
      THEN Cases_on `n` 
      THEN FULL_SIMP_TAC arith_ss [FACT, AC MULT_ASSOC MULT_SYM]));


(*****************************************************************************)
(* Implement a function Fact to compute SND(FactIter (n,1))                  *)
(*****************************************************************************)

val (Fact,_,Fact_dev) =
 hwDefine [FactIter_dev]
  `Fact n = SND(FactIter (n,1))`;

(*****************************************************************************)
(* Verify Fact is indeed the factorial function                              *)
(*****************************************************************************)

val FactThm =
 Q.store_thm
  ("FactThm",
   `Fact = FACT`,
   RW_TAC arith_ss [FUN_EQ_THM,Fact,FactIterRecThm]);

(*****************************************************************************)
(* Create implementation of factorial (HOL's built-in FACT)                  *)
(*****************************************************************************)

val FACT_def =
 save_thm
  ("FACT_dev",
   REWRITE_RULE [FactThm] Fact_dev);
