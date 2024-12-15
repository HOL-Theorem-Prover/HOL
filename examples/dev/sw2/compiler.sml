structure compiler :> compiler =
struct

(* for interactive use
fun load_path_add x = loadPath := !loadPath @ [concat Globals.HOLDIR x];
val _ = load_path_add "/examples/mc-logic";
val _ = load_path_add "/examples/ARM/v4";
val _ = load_path_add "/tools/mlyacc/mlyacclib";
(* load_path_add "/examples/dev/sw2"; *)

val _ = quietdec := true;
app load ["arm_compilerLib", "Normal", "inline", "closure",
          "regAlloc", "funcCall", "refine"];
val _ = quietdec := false;
*)

open HolKernel Parse boolLib bossLib boolSyntax;
open compilerLib;

val _ = numLib.temp_prefer_num();

(*---------------------------------------------------------------------------*)
(* Interface Functions.                                                      *)
(*---------------------------------------------------------------------------*)

(* val arm_compile = arm_compilerLib.arm_compile; *)

val normalize = Normal.normalize;
val SSA_RULE = Normal.SSA_RULE;
val expand_anonymous = inline.expand_anonymous;
val expand_named = inline.expand_named;
val optimize_norm = inline.optimize_norm;
val close_one_by_one = closure.close_one_by_one;
val close_all = closure.close_all;
val closure_convert = closure.closure_convert;
val parallel_move = regAlloc.parallel_move;
val reg_alloc = regAlloc.reg_alloc;
(*
val printSAL = SALGen.printSAL;
val certified_gen = SALGen.certified_gen;
*)

(*---------------------------------------------------------------------------*)
(* Auxiliary functions.                                                      *)
(*---------------------------------------------------------------------------*)

structure M = Binarymap;

fun resultOf (PASS x) = x;

fun head eqns =
  strip_comb (lhs(snd(strip_forall(hd (strip_conj(concl eqns))))));

(*---------------------------------------------------------------------------*)
(* Compiling a list of functions.                                            *)
(*---------------------------------------------------------------------------*)

fun defname th =
  fst(dest_const(fst(strip_comb(lhs(snd(strip_forall(concl th)))))));

fun compenv comp =
 let fun compile (env,[]) = PASS(rev env)
       | compile (env,h::t) =
          let val name = defname h
          in
            print ("Compiling "^name^" ... ");
            case total comp (env,h)
             of SOME def1 => (print "succeeded.\n"; compile(def1::env,t))
              | NONE => (print "failed.\n"; FAIL(env,h::t))
          end
 in
    compile
 end;

(*---------------------------------------------------------------------------*)
(* Compile a list of definitions, accumulating the environment.              *)
(*---------------------------------------------------------------------------*)

fun complist passes deflist = compenv passes ([],deflist);

(*---------------------------------------------------------------------------*)
(* Conversion 1.                                                             *)
(* Simplify to standard format.                                              *)
(* Basic flattening via CPS and unique names                                 *)
(*---------------------------------------------------------------------------*)

val cond_lift = ref true;

fun convert1 (env,def) =
  let val def1 = Normal.pre_process def
      val def2 = if !cond_lift then refine.lift_cond def1 else def1
  in
      (Normal.SSA_RULE o refine.refine_const o normalize (* o refine.refine_const *)) def2
  end;

(* All previous, plus inlining and optimizations                             *)

fun convert1a (env,def) =
  let val def1 = convert1 def
  in
   Normal.SSA_RULE (inline.optimize_norm env def1)
  end;

(* All previous, and closure conversion.                                     *)

fun convert1b (env,def) =
  let val def1 = convert1a (env,def)
  in case total closure.closure_convert def1
      of SOME thm => Normal.SSA_RULE (inline.optimize_norm env thm)
       | NONE => def1
  end;

(*---------------------------------------------------------------------------*)
(* Conversion 2.                                                             *)
(* All previous, and register allocation.                                    *)
(*---------------------------------------------------------------------------*)

fun convert2 (env,def) =
  let val def1 = convert1 (env,def)
      val def2 = regAlloc.reg_alloc def1
  in
    def2
  end;

(* Different convert2, in which some intermediate steps are skipped.         *)

fun convert2a (env,def) =
  let val def1 = convert1a (env,def)
  in
     regAlloc.reg_alloc def1
  end;

(*---------------------------------------------------------------------------*)
(* Conversion 3.                                                             *)
(* All previous, and refinement.                                             *)
(*---------------------------------------------------------------------------*)

fun convert3 (env,def) =
  let val def1 = convert2 (env,def)
  in
    funcCall.caller_save_call def1
  end

(*---------------------------------------------------------------------------*)
(* Compiling a list of source functions.                                     *)
(*---------------------------------------------------------------------------*)

fun defname th =
  fst(dest_const(fst(strip_comb(lhs(snd(strip_forall(concl th)))))));

fun compenv comp =
 let fun compile (env,[]) = PASS(rev env)
       | compile (env,h::t) =
          let val name = defname h
          in
            print ("Compiling "^name^" ... ");
            case total comp (env,h)
             of SOME def1 => (print "succeeded.\n"; compile(def1::env,t))
              | NONE => (print "failed.\n"; FAIL(env,h::t))
          end
 in
    compile
 end;

(* Compile a list of definitions, accumulating the environment.              *)

fun complist passes deflist = compenv passes ([],deflist);

(*---------------------------------------------------------------------------*)
(* Compilation phases in front end.                                          *)
(*---------------------------------------------------------------------------*)

(* Basic flattening via CPS and unique names                                 *)

val pass1 = complist convert1

(* All previous, and register allocation.                                    *)

val pass2 = complist convert2

(* All previous, and refinement.                                             *)

val pass3 = complist convert3

(* All previous, and the following:                                          *)
(*  1. enforce caller-save-style function calls                              *)
(*  2. tune the normal forms for the back-end                                *)


(*---------------------------------------------------------------------------*)
(* Replace function f with f' when f is called.                              *)
(*---------------------------------------------------------------------------*)

val renamed = (* Format: [function's old name |-> function's new name] *)
ref (M.mkDict regAlloc.tvarOrder)

fun renamed_rules () =
    List.foldl
      (fn ((f,f'),ys) => (f |-> f') :: ys)
      [] (M.listItems (!renamed));

val only_one = ref false;

(*---------------------------------------------------------------------------*)
(* Front end.                                                                *)
(* the flag indicates whether we start all over                              *)
(*---------------------------------------------------------------------------*)

fun f_compile_basic defs flag =
 let
  val _ = if flag then (renamed := M.mkDict regAlloc.tvarOrder) else ()

  fun redefine def =
   let
     val (fname, fbody) = dest_eq (concl def)
     val (args,body) = pairSyntax.dest_pabs fbody
     val def1 = CONV_RULE (RHS_CONV pairLib.GEN_BETA_CONV) (AP_THM def args)

     val (cname, ctype) = dest_const fname
     val new_name = cname ^ "'"
     val cvar = mk_var(new_name, ctype)

     val vtm = subst [fname |-> cvar] (concl def1)
     (* rename the function name in function application *)
     val vtm1 = subst (renamed_rules ()) vtm
     (* val _ = HOL_MESG "redefinition" *)
     val PASS (defn2,tcs) = TotalDefn.std_apiDefine (new_name,vtm1)
     val def2 = LIST_CONJ (Defn.eqns_of defn2)
     val ind = Defn.ind_of defn2
     val (def', ind') =
        let val lem = prove(mk_eq(mk_const(new_name, ctype), fname),
                 REWRITE_TAC [FUN_EQ_THM] THEN
                 SIMP_TAC bool_ss [pairTheory.FORALL_PROD] THEN
                 REWRITE_TAC [Once def1, Once def2])
            val ind2 = case ind of
                   SOME th => ONCE_REWRITE_RULE [lem] th
                 | NONE => TRUTH
        in (def1, ind2) end
        handle _ =>
          let val newc = mk_const(new_name, ctype)
              val _ = renamed := M.insert(!renamed, fname, newc)
          in  (def2, case ind of
                         SOME th => th
                       | NONE => TRUTH)
          end
   in
     (def',ind')
   end;

   val result = pass3 defs
 in
   case result of
        PASS defs' => PASS (List.map redefine defs')
     |  FAIL x => FAIL x
 end

fun f_compile_one def = hd (resultOf (f_compile_basic [def] false));
fun f_compile defs = f_compile_basic defs true;

(*---------------------------------------------------------------------------*)
(* Join the front end with Magnus' backend                                   *)
(*---------------------------------------------------------------------------*)
(*
val style = ref (InLineCode);

fun b_compile_one (def, ind) =
  let
    val (th,strs) = arm_compilerLib.arm_compile (SPEC_ALL def) ind (!style)
    val code = fetch "-" (#1 (dest_const (#1 (head def))) ^ "_code1_def")
  in  (th, code)
  end

fun b_compile norms =
  let val _ = arm_compilerLib.abbrev_code := true
      val _ = arm_compilerLib.reset_compiled()
      val _ = optimise_code := true;
  in
    case norms of
         PASS defs => PASS (List.map b_compile_one defs)
      |  FAIL x => FAIL x
  end

(*---------------------------------------------------------------------------*)
(* End-to-end compiler.                                                      *)
(*---------------------------------------------------------------------------*)

val pp_compile_one = b_compile_one o f_compile_one;
val pp_compile = b_compile o f_compile;
*)

(*---------------------------------------------------------------------------*)

end
