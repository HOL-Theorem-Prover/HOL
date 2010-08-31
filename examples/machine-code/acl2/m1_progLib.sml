structure m1_progLib :> m1_progLib =
struct

open HolKernel boolLib bossLib;

open m1_progTheory decompilerLib helperLib sexpTheory pairSyntax;


(* m1_spec produces Hoare triple theorems for M1 instructions *)

fun m1_spec s = let
  val m1_thms = [M1_ICONST,M1_ILOAD,M1_ISTORE,M1_IADD,M1_ISUB,M1_IMUL,M1_GOTO,M1_IFLE];
  val tm = Parse.Term [QUOTE s]  
  fun match_thm th = let
    val (_,_,c,_) = helperLib.dest_spec (concl th)  
    val c = c |> rator |> rand |> rand
    val m = fst (match_term c tm)
    in INST m th end  
  val th = match_thm (first (can match_thm) m1_thms)
  val pc_offset = 
    th |> concl |> rand |> rand |> rand |> rand |> rand
       |> (fn x => numSyntax.int_of_term x handle HOL_ERR _ => 
                   Arbint.toInt(intSyntax.int_of_term x))
  in if can (find_term (fn x => x = ``"IFLE"``)) (concl th) then
       ((th,1,SOME pc_offset),SOME (match_thm M1_IFLE_NOP,1,SOME 1))
     else ((th,1,SOME pc_offset),NONE) end;

val m1_status = TRUTH
val m1_pc = ``PC``;
fun m1_jump (tm1:term) (tm2:term) (jump_length:int) (forward:bool) = ("",0)

val m1_tools = (m1_spec, m1_jump, m1_status, m1_pc)


(* the decompiler is specialised to deal with s-expressions and the M1 model *)

fun dest_tuple tm =
  let val (x,y) = pairSyntax.dest_pair tm in x :: dest_tuple y end handle HOL_ERR e => [tm];

fun fix_pc y th = let
    val format = ``add p (nat n)``
    val fixed_pc = subst [mk_var("n",``:num``)|->numSyntax.term_of_int y] format
    val thi = INST [mk_var("p",``:sexp``)|->fixed_pc] th
    val thi = SIMP_RULE std_ss [add_nat,add_nat_int,add_ASSOC] thi
    in thi end;

val prev = ref (TRUTH,TRUTH);
val (res,def) = !prev
fun sexp_finalise_decompile (res,def) = let
  val _ = (prev := (res,def))
  val _ = echo 2 " - converting to produce sexp\n"
  fun sexp_result output = let
    fun ff [] = (fst o dest_eq o concl) nil_def 
      | ff (v::vs) = mk_comb(mk_comb(``cons``,v),ff vs)
    in mk_pabs(output,ff (dest_tuple output)) end;
  val fhd = hd (CONJUNCTS def)
  val f = last (CONJUNCTS def)
  val (tm1,tm2) = (dest_eq o concl o SPEC_ALL) f
  val input = cdr tm1
  val name = (fst o dest_const o car) tm1
  val name = ("sexp_" ^ name)
  val output = get_output_list f
  val fix = sexp_result output
  fun ff [] = "sexp"
    | ff (x::xs) = "sexp -> " ^ ff xs
  val ty = Parse.Type [QUOTE (":" ^ ff (dest_tuple input))]
  val tm = mk_var(name,ty)
  fun hh tm [] = tm
    | hh tm (x::xs) = hh (mk_comb(tm,x)) xs
  val lhs = hh tm (dest_tuple input)
  val eq_tm = mk_eq (lhs,mk_comb(fix,tm1))
  val def3 = new_definition(name,eq_tm)
  val new_lhs = (fst o dest_eq o concl o SPEC_ALL) def3
  fun rw (FUN_LET (x,y,t)) = FUN_LET (x, y, rw t)
    | rw (FUN_IF (x,t1,t2)) = FUN_IF (x, rw t1, rw t2)
    | rw (FUN_COND (x,t)) = FUN_COND (x, rw t)
    | rw (FUN_VAL tm) =
        if tm = tm1 then FUN_VAL new_lhs
        else FUN_VAL (snd (dest_pabs fix))
  val tm3 = ftree2tm (rw (tm2ftree tm2))
  val goal = mk_eq(new_lhs,tm3)  
  val inferred = prove(goal,  
    REWRITE_TAC [def3]
    THEN CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [f]))
    THEN REPEAT (AUTO_DECONSTRUCT_TAC cdr)
    THEN SIMP_TAC std_ss []
    THEN CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
    THEN SIMP_TAC std_ss []) 
  val def2 = REWRITE_RULE [ite_intro] inferred
  val tm7 = cdr tm1
  fun ff [] = [] | ff (v::vs) = let
    in [``car``] :: map (fn y => y @ [``cdr``]) (ff vs) end
  fun g [] = ``value:sexp``
    | g (x::xs) = mk_comb(x,g xs)
  val tm8 = list_mk_pair (map g (ff (dest_tuple (output))))
  val tm9 = mk_anylet([(``value:sexp``,(fst o dest_eq o concl o SPEC_ALL) def3)],tm8)
  val goal = mk_eq (tm1,tm9)
  val rw_thm = prove(goal,
    SIMP_TAC std_ss [def3,LET_DEF]
    THEN CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
    THEN SIMP_TAC std_ss [car_def,cdr_def])
  val res = REWRITE_RULE [rw_thm] res
  (* flatten let-expressions, leave no ``let ... = (let ... in ..) in ...`` *)
  fun flatten (FUN_IF (x,t1,t2)) = FUN_IF (x, flatten t1, flatten t2)
    | flatten (FUN_COND (x,t)) = FUN_COND (x, flatten t)
    | flatten (FUN_VAL tm) = FUN_VAL tm
    | flatten (FUN_LET (x,y,t)) = let
       val (tm1,tm2) = dest_let y
       val (v,tm1) = dest_abs tm1
       val xs = (v,tm2) :: Lib.zip (dest_tuple x) (dest_tuple tm1)  
       in foldr (fn ((x,y),z) => FUN_LET (x,y,z)) (flatten t) xs end
       handle HOL_ERR _ => FUN_LET (x,y,flatten t)
  val (tm10,tm11) = (dest_eq o concl o SPEC_ALL) def2
  val tm12 = ftree2tm (flatten (tm2ftree tm11))
  val goal = mk_eq(tm10,tm12)
  val def2 = prove(goal,
    CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [def2]))
    THEN SIMP_TAC std_ss [LET_DEF])
  val def2 = REWRITE_RULE [ite_intro] def2
  in (res,def2) end;

val _ = (decompiler_set_pc := fix_pc);
val _ = (decompiler_finalise := sexp_finalise_decompile)

val decompile_m1 = decompile m1_tools


end


