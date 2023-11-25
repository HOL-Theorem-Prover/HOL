structure compilerLib :> compilerLib =
struct

open HolKernel boolLib bossLib Parse;
open decompilerLib;
open codegenLib;
open codegen_x86Lib;
open reg_allocLib;

open prog_armLib prog_ppcLib prog_x86Lib prog_x64Lib;
open wordsTheory wordsLib addressTheory;
open helperLib;
open mc_tailrecLib;
structure Parse = struct
  open Parse
  val (Type,Term) =
      wordsTheory.words_grammars |> parse_from_grammars
end
open Parse


fun AUTO_ALPHA_CONV () = let
  val counter = ref (Arbnum.zero)
  fun inc () = let val v = !counter in (counter := Arbnum.+(v,Arbnum.one); v) end
  fun counter_genvar ty = mk_var("auto_"^ Arbnum.toString (inc()),ty)
  fun doit tm =
    if is_abs tm then
      (ALPHA_CONV (counter_genvar (type_of (fst (dest_abs tm)))) THENC
       ABS_CONV doit) tm
    else if is_comb tm then
      (RATOR_CONV doit THENC RAND_CONV doit) tm
    else ALL_CONV tm
  in doit end

val COMPILER_TAC_LEMMA = prove(
  ``!a b:bool. (a /\ a /\ b <=> a /\ b) /\ (a \/ a \/ b <=> a \/ b)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss []);

val COMPILER_TAC =
    SIMP_TAC bool_ss [LET_DEF,word_div_def,word_mod_def,w2w_CLAUSES]
    THEN SIMP_TAC std_ss [WORD_OR_CLAUSES,GUARD_def]
    THEN REWRITE_TAC [WORD_CMP_NORMALISE]
    THEN REWRITE_TAC [WORD_HIGHER,WORD_GREATER,WORD_HIGHER_EQ,
           WORD_GREATER_EQ,GSYM WORD_NOT_LOWER,GSYM WORD_NOT_LESS]
    THEN SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w,NOT_IF,
           WORD_OR_CLAUSES]
    THEN CONV_TAC (EVAL_ANY_MATCH_CONV word_patterns)
    THEN SIMP_TAC std_ss [WORD_SUB_RZERO, WORD_ADD_0, IF_IF,
                          AC WORD_ADD_COMM WORD_ADD_ASSOC,
                          AC WORD_MULT_COMM WORD_MULT_ASSOC,
                          AC WORD_AND_COMM WORD_AND_ASSOC,
                          AC WORD_OR_COMM WORD_OR_ASSOC,
                          AC WORD_XOR_COMM WORD_XOR_ASSOC,
                          AC CONJ_COMM CONJ_ASSOC,
                          AC DISJ_COMM DISJ_ASSOC,
                          IMP_DISJ_THM, WORD_MULT_CLAUSES]
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC (RAND_CONV (AUTO_ALPHA_CONV ()))
    THEN CONV_TAC ((RATOR_CONV o RAND_CONV) (AUTO_ALPHA_CONV ()))
    THEN SIMP_TAC std_ss [AC CONJ_ASSOC CONJ_COMM, AC DISJ_COMM DISJ_ASSOC,
                          COMPILER_TAC_LEMMA]
    THEN SIMP_TAC std_ss [WORD_SUB_RZERO, WORD_ADD_0, IF_IF,
                          AC WORD_ADD_COMM WORD_ADD_ASSOC,
                          AC WORD_MULT_COMM WORD_MULT_ASSOC,
                          AC WORD_AND_COMM WORD_AND_ASSOC,
                          AC WORD_OR_COMM WORD_OR_ASSOC,
                          AC WORD_XOR_COMM WORD_XOR_ASSOC,
                          AC CONJ_COMM CONJ_ASSOC,
                          AC DISJ_COMM DISJ_ASSOC,
                          IMP_DISJ_THM, WORD_MULT_CLAUSES]
    THEN EQ_TAC
    THEN ONCE_REWRITE_TAC [GSYM DUMMY_EQ_def]
    THEN REWRITE_TAC [FLATTEN_IF]
    THEN REPEAT STRIP_TAC
    THEN ASM_SIMP_TAC std_ss [];

fun basic_compile target tm = let
  val (tools,target,model_name,s) =
    if mem target ["arm","ARM"] then (arm_tools,"arm","ARM_MODEL",[]) else
    if mem target ["x86","i32","386"] then (x86_tools,"x86","X86_MODEL",to_x86_regs ()) else
    if mem target ["x64","X64"] then (x64_tools,"x64","X64_MODEL",[]) else
    if mem target ["ppc","Power","PowerPC"] then (ppc_tools,"ppc","PPC_MODEL",[]) else fail()
  val x = fst (dest_eq tm)
  val name = fst (dest_const (repeat car x)) handle e => fst (dest_var (repeat car x))
  val _ = echo 1 ("\nCompiling " ^ name ^ " into "^ target ^ "...\n")
  val (code,len) = generate_code target model_name true tm
  fun append' [] = "" | append' (x::xs) = x ^ "\n" ^ append' xs
  val qcode = [QUOTE (append' code)] : term quotation
  val in_tm = cdr x
  fun ends (FUN_IF (_,c1,c2)) = ends c1 @ ends c2
    | ends (FUN_LET (_,_,c)) = ends c
    | ends (FUN_COND (_,c)) = ends c
    | ends (FUN_VAL t) = if is_var t orelse pairSyntax.is_pair t then [t] else []
  val out_tm2 = hd (ends (tm2ftree (cdr tm)))
  val (in_tm,out_tm) = (subst s in_tm, subst s out_tm2)
  val function_in_out = SOME (in_tm,out_tm)
  val qcode = ([QUOTE (append' code)]) : term Lib.frag list
  val (th1,th2) = basic_decompile tools name function_in_out qcode
  val _ = print "Proving equivalence, "
  val const = (repeat car o fst o dest_eq o concl o hd o CONJUNCTS) th2
  val tm = subst [ repeat car x |-> const ] tm
  val pre = if is_conj (concl th2) then (last o CONJUNCTS) th2 else TRUTH
  val pre = RW [IF_IF,WORD_TIMES2] pre
  val th3 = auto_prove "compile" (tm,
(*
  set_goal([],tm)
*)
    REPEAT STRIP_TAC
    THEN CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [th2]))
    THEN COMPILER_TAC)
  val _ = add_compiler_assignment out_tm2 (fst (dest_eq tm)) name len model_name
  val _ = print "done.\n"
  in (th1,th3,pre) end;

fun compile target tm = let
  val _ = set_abbreviate_code true
  fun compile_each [] = []
    | compile_each (tm::tms) = let
    val (th,def,pre) = basic_compile target tm
    in (th,def,pre) :: compile_each tms end
  val tms = list_dest dest_conj tm
  val xs = compile_each tms
  val defs = map (fn (x,y,z) => y) xs
  val pres = map (fn (x,y,z) => z) xs
  val def = RW [] (foldr (uncurry CONJ) TRUTH defs)
  val pre = RW [] (foldr (uncurry CONJ) TRUTH pres)
  val (th,_,_) = last xs
  val _ = set_abbreviate_code false
  val th = UNABBREV_CODE_RULE th
  in (th,def,pre) end;

fun compile_all_aux tm = let
  val x = fst (dest_eq tm)
  val name = fst (dest_const (repeat car x)) handle e => fst (dest_var (repeat car x))
  val targets = ["ppc","x86","arm"]
  fun compile_each tm [] = []
    | compile_each tm (target::ts) = let
    val (th,def,_) = basic_compile target tm
    val pre = fetch "-" (name ^ "_pre_def")
    val tm = concl def
    in (target,th,def,pre):: compile_each tm ts end
  val xs = compile_each tm targets
  val (_,_,last_def,last_pre) = last xs
  fun prove_eq (target,th,def,pre) = let
    val f = (repeat car o fst o dest_eq o concl o SPEC_ALL)
    val goal = mk_conj(mk_eq(f def,f last_def),mk_eq(f pre,f last_pre))
    val lemma = auto_prove "compiler prove_eq" (goal,
      TAILREC_TAC THEN REPEAT STRIP_TAC THEN COMPILER_TAC)
    val _ = echo 1 (" " ^ target)
    in (target, ONCE_REWRITE_RULE [lemma] th) end
  val _ = echo 1 "\nJoining definitions:"
  val ys = map prove_eq xs
  val _ = echo 1 ".\n"
  val thms = map snd ys
  val _ = add_compiled thms
  in (ys,last_def,last_pre) end;

fun compile_all tm = let
  val _ = set_abbreviate_code true
  fun compile_each [] = []
    | compile_each (tm::tms) = let
    val x = car (fst (dest_eq tm))
    val (ys,def,pre) = compile_all_aux tm
    val x2 = (car o fst o dest_eq o concl o SPEC_ALL) def
    val tms = map (subst [x |-> x2]) tms
    in (ys,def,pre) :: compile_each tms end
  val tms = list_dest dest_conj tm
  val xs = compile_each tms
  val f = REWRITE_RULE [] o foldr (uncurry CONJ) TRUTH
  val defs = f (map (fn (x,y,z) => y) xs)
  val pres = f (map (fn (x,y,z) => z) xs)
  val (ys,_,_) = last xs
  val _ = set_abbreviate_code false
  val ys = map (fn (n,th) => (n,UNABBREV_CODE_RULE th)) ys
  in (ys,defs,pres) end


(* this compiler maintains a to-do list: a list of functions to be compiled *)

val to_compile = ref ([]:(string * (thm * thm)) list);


(* for each function it generates a precondition, asserting termination etc. *)

fun append_lists [] = []
  | append_lists (y::ys) = y @ append_lists ys

fun list_find x [] = fail()
  | list_find x ((y,z)::zs) = if x = y then z else list_find x zs

fun all_distinct [] = []
  | all_distinct (x::xs) = x :: all_distinct (filter (fn y => not (x = y)) xs)

fun generate_pre fname args tm = let
  val h = fst o dest_eq o concl o SPEC_ALL
  val aux_pre =
      map ((fn (x,y) => (h x,h y)) o snd)
          (filter (fn (_,(_,y)) => cdr (concl y) !~ T) (!to_compile))
  fun mk_ALIGNED b = (fst o dest_eq o concl o SPEC b) addressTheory.ALIGNED_def
  fun word32_read_write tm = let
    val xs1 = find_terms (fn x => is_comb x andalso is_var (car x) andalso
                                  (type_of (car x) = ``:word32 -> word32``)) tm
    val xs1 = map ((fn (x,y) => (fst (dest_var x),y)) o dest_comb) xs1
    val xs2 = find_terms (fn x => is_comb x andalso
                                  combinSyntax.is_update (car x) andalso
                                  (type_of x = ``:word32 -> word32``)) tm
    val xs2 = map (fn x => (fst (combinSyntax.dest_update(car x)),repeat cdr x)) xs2
    val xs2 = map (fn (x,f) => (fst (dest_var f),x)) xs2
    val ys = map (mk_ALIGNED o snd) (xs1 @ xs2)
    val zs = map (fn (n,x) => pred_setSyntax.mk_in(x,mk_var("d"^n,``:word32 set``))) (xs1@xs2)
    in ys @ zs end
  fun aux_fun_pre tm (def,pre) = let
    val xs = find_terms (fn x => can (match_term def) x) tm
    in map (fn x => subst (fst (match_term def x)) pre) xs end
  fun all_aux_fun_pre tm =
      op_mk_set aconv (append_lists (map (aux_fun_pre tm) aux_pre))
  fun get_pre tm = word32_read_write tm @ all_aux_fun_pre tm
  fun cond_pre tm f = let
    val pre = get_pre tm
    in if null pre then f else FUN_COND (list_mk_conj pre, f) end
  val cond_var = mk_var("cond",``:bool``)
  fun get_name tm = fst (dest_var (car tm)) handle HOL_ERR _ =>
                    fst (dest_const (car tm)) handle _ => "    "
  val pre_name = fname ^ "_pre"
  val pre_f = mk_var(pre_name,mk_type ("fun",[type_of args, ``:bool``]))
  fun add_pre (FUN_VAL tm) =
       (if not (get_name tm = fname) then cond_pre tm (FUN_VAL cond_var)
        else cond_pre tm (FUN_VAL (mk_conj(mk_comb(pre_f,cdr tm),cond_var))))
    | add_pre (FUN_IF (tm,t1,t2)) = cond_pre tm (FUN_IF (tm, add_pre t1, add_pre t2))
    | add_pre (FUN_LET (lhs,rhs,t)) = cond_pre rhs (FUN_LET (lhs,rhs, add_pre t))
    | add_pre (FUN_COND (tm,t)) = FUN_COND (tm,add_pre t)
  val pre_tm = subst [cond_var|->T] (ftree2tm (add_pre (tm2ftree (cdr tm))))
  val pre_tm = (snd o dest_eq o concl) (QCONV (REWRITE_CONV []) pre_tm)
  in pre_tm end;


(* mc_define defines a function, generates a precondition and adds these to to-do list *)

fun mc_define q = let
  val absyn = Parse.Absyn q
  val fname = Absyn.dest_ident (fst (Absyn.dest_app (fst (Absyn.dest_eq absyn))))
  val _ = Parse.hide fname
  val tm = Parse.Term q
  val (name,args) = dest_comb (fst (dest_eq tm))
  val pre_tm = generate_pre fname args tm
  val pre_f = mk_var(fname ^ "_pre",mk_type ("fun",[type_of args, ``:bool``]))
  val pre_tm = mk_eq(mk_comb(pre_f,args),pre_tm)
  val pre_option = SOME pre_tm
  val (def,pre) = tailrec_define_with_pre tm pre_tm
  val _ = (to_compile := (fname,(def,pre)) ::
                         filter (fn (n,_) => not (fname = n)) (!to_compile))
  in (def,pre) end;


(* mc_compile performs actual compilation with help of reg_allocLib and compilerLib *)

fun collect_aux_fnames fname = let
  val fconst = car o fst o dest_eq o concl o SPEC_ALL
  val all_fconsts = map (fconst o fst o snd) (!to_compile)
  fun uses def =
    (all_distinct o map (fst o dest_const) o
     filter (fn x => x !~ fconst def) o
     find_terms (fn x => tmem x all_fconsts) o concl) def
  val all_uses =
      map (fn (_,(def,_)) => ((fst o dest_const o fconst) def, uses def))
          (!to_compile)
  fun rec_uses fname =
    fname :: append_lists (map rec_uses (list_find fname all_uses))
  val fnames = all_distinct (rec_uses fname)
  val fnames = filter (fn x => mem x fnames) (map fst (!to_compile))
  in fnames end;

fun mc_compile fname target = let
  val fnames = collect_aux_fnames fname
  val qs = map (fn f => (f,list_find f (!to_compile))) (rev fnames)
  val fun_const = car o fst o dest_eq o concl
  val cs = map (fun_const o fst o snd) qs
  fun make_temp_name s = "__" ^ s
  val s = map (fn c => c |-> mk_var(make_temp_name (fst (dest_const c)),type_of c)) cs
  val tm = subst s (list_mk_conj (map (concl o fst o snd) qs))
  val input_tm = tm
  val n = list_find target [("arm",13),("ppc",31),("x86",1000)]
  val imp = allocate_registers n input_tm
  fun strip_forall tm = strip_forall (snd (dest_forall tm)) handle HOL_ERR _ => tm
  val gs = (map strip_forall o list_dest dest_conj o fst o dest_imp o concl) imp
  val xs = zip (rev fnames) gs
  fun do_all [] thms = thms
    | do_all ((f,tm)::xs) thms = let
        val (x1,x2,x3) = compile target tm
        val x2c = fun_const x2
        val x3c = fun_const x3
        val s = [mk_var(make_temp_name(f),type_of x2c) |-> x2c]
        val xs = map (fn (x,tm) => (x,subst s tm)) xs
        in do_all xs ((x1,x2,x3)::thms) end
  val zs = do_all xs []
  fun prove_equiv [] rws = rws
    | prove_equiv (((_,(x2,x3)),(_,y2,y3))::ts) rws = let
        val goal = mk_conj(mk_eq(fun_const x2,fun_const y2),
                           mk_eq(fun_const x3,fun_const y3))
        val th2 = auto_prove "mc_compile" (goal,
          STRIP_TAC THEN TAILREC_TAC THEN AP_TERM_TAC THEN REWRITE_TAC rws
          THEN SIMP_TAC std_ss [GUARD_def,FUN_EQ_THM] THEN REPEAT STRIP_TAC
          THEN SIMP_TAC std_ss [ALIGNED_INTRO] THEN COMPILER_TAC)
        val rws = th2::rws
        in prove_equiv ts rws end
  val rws = []
  val ts = zip qs (rev zs)
  val rws = prove_equiv ts rws
  val rw = GSYM (RW [GSYM CONJ_ASSOC] (LIST_CONJ rws))
  val (th,_,_) = hd zs
  val th = RW [rw] th
  val temp_cs = map (fst o dest_eq) (list_dest dest_conj (concl rw))
  val _ = map (delete_const o fst o dest_const) temp_cs
  in th end;

fun mc_compile_all fname =
  map (fn target => (target, mc_compile fname target)) ["arm","ppc","x86"]

end;
