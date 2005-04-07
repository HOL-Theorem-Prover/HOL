
(*****************************************************************************)
(* High level (TFL) specification and implementation of factorial            *)
(* using ``:word32`` instead of ``:num``                                     *)
(*****************************************************************************)

quietdec := true;
loadPath := "../" :: "word32" :: "../dff/" :: !loadPath;
map load
 ["compileTheory","compile","metisLib","intLib","word32Theory",
  "dffTheory","vsynth","compile32Theory"];
open compile metisLib word32Theory;
open arithmeticTheory intLib pairLib pairTheory PairRules combinTheory
     devTheory composeTheory compileTheory compile vsynth dffTheory
     compile32Theory;
infixr 3 THENR;
infixr 3 ORELSER;
intLib.deprecate_int();

(*****************************************************************************)
(* The definition of hwDefine below is very temporary!                       *)
(*****************************************************************************)
fun CHEAT_TAC(asl,goal) = ([], fn _ => mk_thm(asl,goal));

fun hwDefine defq =
 let val absyn0 = Parse.Absyn defq
 in 
   case absyn0
    of Absyn.APP(_,Absyn.APP(_,Absyn.IDENT(loc,"measuring"),def),f) =>
        let val (deftm,names) = Defn.parse_defn def
            val hdeqn = hd (boolSyntax.strip_conj deftm)
            val (l,r) = boolSyntax.dest_eq hdeqn
            val domty = pairSyntax.list_mk_prod 
                          (map type_of (snd (boolSyntax.strip_comb l)))
            val fty = Pretype.fromType (domty --> numSyntax.num)
(*
            val typedf = Parse.absyn_to_term 
                             (Parse.term_grammar())
                             (Absyn.TYPED(loc,f,fty))
*)
            val defn = Defn.mk_defn (hd names) deftm
(*
            val tac = EXISTS_TAC (mk_measure typedf)
                       THEN TotalDefn.TC_SIMP_TAC [] default_simps
*)
            val tac = CHEAT_TAC
            val (defth,ind) = Defn.tprove(defn, tac)
            val (lt,rt) = boolSyntax.dest_eq(concl defth)
            val (func,args) = dest_comb lt
            val (test,t1,t2) = dest_cond rt
            val fb = mk_pabs(args,test)
            val f1 = mk_pabs(args,t1)
            val f2 = mk_pabs(args,rand t2)
(*
            val totalth = prove
                    (Term`TOTAL(^fb,^f1,^f2)`,
                     RW_TAC std_ss [TOTAL_def,pairTheory.FORALL_PROD]
                      THEN EXISTS_TAC typedf
                      THEN TotalDefn.TC_SIMP_TAC [] default_simps)
*)
            val totalth = prove
                    (Term`TOTAL(^fb,^f1,^f2)`,
                     CHEAT_TAC)
            val devth = PURE_REWRITE_RULE [GSYM DEV_IMP_def]
                          (RecCompileConvert defth totalth)
        in
         (defth,ind,devth)
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
                    raise ERR "hwDefine" "recursive definition without a measure")
              else ()
            val devth = PURE_REWRITE_RULE[GSYM DEV_IMP_def] 
                          (CompileConvert defth)
        in (defth,boolTheory.TRUTH,devth)
        end
 end;

quietdec := false;

add_combinational ["MOD","WL","DIV"];
add_combinational ["word_add","word_sub"];
add_combinational ["BITS","HB","w2n","n2w"];

add_combinational_components
 [COMB_ADD, 
  COMB_SUB, 
  COMB_LESS, 
  COMB_EQ];

add_temporal_abstractions
 [EQ_at, 
  ADD_at, 
  SUB_at, 
  LESS_at];

(*****************************************************************************)
(* Start new theory "Fact32"                                                 *)
(*****************************************************************************)
val _ = new_theory "Fact32";

(*****************************************************************************)
(* We implement multiplication with a naive iterative multiplier function    *)
(* (works by repeated addition)                                              *)
(*****************************************************************************)
val (Mult32Iter,Mult32Iter_ind,Mult32Iter_dev) =
 hwDefine
  `(Mult32Iter (m,n,acc) =
     if m = 0w then (0w,n,acc) else Mult32Iter(m-1w,n,n + acc))
   measuring FST`;

(*****************************************************************************)
(* Create an implementation of a multiplier from Mult32Iter                  *)
(*****************************************************************************)
val (Mult32,_,Mult32_dev) =
 hwDefine
  `Mult32(m,n) = SND(SND(Mult32Iter(m,n,0w)))`;

(*****************************************************************************)
(* Implement iterative function as a step to implementing factorial          *)
(*****************************************************************************)
val (Fact32Iter,Fact32Iter_ind,Fact32Iter_dev) =
 hwDefine
  `(Fact32Iter (n,acc) =
     if n = 0w then (n,acc) else Fact32Iter(n-1w, Mult32(n,acc)))
   measuring FST`;

(*****************************************************************************)
(* Implement a function Fact32 to compute SND(Fact32Iter (n,1))              *)
(*****************************************************************************)
val (Fact32,_,Fact32_dev) =
 hwDefine
  `Fact32 n = SND(Fact32Iter (n,1w))`;

(*****************************************************************************)
(* Derivation using refinement combining combinators                         *)
(*****************************************************************************)
val Fact32Imp_dev =
 REFINE
  (DEPTHR(LIB_REFINE[Fact32Iter_dev])
    THENR DEPTHR(LIB_REFINE[Mult32_dev])
    THENR DEPTHR(LIB_REFINE[Mult32Iter_dev])
    THENR DEPTHR ATM_REFINE)
  Fact32_dev;

val Fact32_net =
 save_thm
  ("Fact32_net",
   time MAKE_NETLIST Fact32Imp_dev);

val Fact32_cir =
 save_thm
  ("Fact32_cir",
   time MAKE_CIRCUIT Fact32Imp_dev);

(*****************************************************************************)
(* This dumps changes to all variables. Set to false to dump just the        *)
(* changes to module Fact32.                                                 *)
(*****************************************************************************)
dump_all_flag := true; 

(*****************************************************************************)
(* Change these variables to select simulator and viewer. Commenting out the *)
(* three assignments below will revert to the defaults: cver/dinotrace.      *)
(*****************************************************************************)
vlogger_path      := "/homes/mjcg/bin/verilog/vlogger/vlogcmd";
verilog_simulator := vlogger;
waveform_viewer   := gtkwave;

(*****************************************************************************)
(* Stop zillions of warning messages that HOL variables of type ``:num``     *)
(* are being converted to Verilog wires or registers of type [31:0].         *)
(*****************************************************************************)
numWarning := true;

SIMULATE Fact32_cir [("inp","4")];

val _ = export_theory();
