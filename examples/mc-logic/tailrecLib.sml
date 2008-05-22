structure tailrecLib :> tailrecLib =
struct
  
open HolKernel boolLib bossLib Parse;
open tailrecTheory;

val car = fst o dest_comb;
val cdr = snd o dest_comb;

val tailrec_simpset = ref (rewrites [TAILREC_NONREC]);  
val tailrec_top_simpset = ref (rewrites []);  
val tailrec_part_simpset = ref (rewrites [TAILREC_NONREC]);  
val tailrec_reverse_simpset = ref (rewrites []); 
fun tailrec_ss() = !tailrec_simpset; 
fun tailrec_top_ss() = !tailrec_top_simpset; 
fun tailrec_part_ss() = !tailrec_part_simpset; 
fun tailrec_reverse_ss() = !tailrec_reverse_simpset; 

datatype ftree_type = 
    FUN_IF of term * ftree_type * ftree_type 
  | FUN_LET of term * term * ftree_type
  | FUN_VAL of term;

fun tm2ftree tm = let
  val (b,x,y) = dest_cond tm
  in FUN_IF (b,tm2ftree x,tm2ftree y) end handle e => let
  val (x,y) = pairSyntax.dest_anylet tm
  val z = tm2ftree y
  in foldr (fn ((x,y),z) => FUN_LET (x,y,z)) z x end handle e => FUN_VAL tm;

fun ftree2tm (FUN_VAL tm) = tm
  | ftree2tm (FUN_IF (tm,x,y)) = mk_cond(tm, ftree2tm x, ftree2tm y)
  | ftree2tm (FUN_LET (tm,tn,x)) = pairSyntax.mk_anylet([(tm,tn)],ftree2tm x)

fun format_ftree g (FUN_VAL tm) = g (FUN_VAL tm)
  | format_ftree g (FUN_IF (tm,x,y)) = g (FUN_IF (tm, format_ftree g x, format_ftree g y))
  | format_ftree g (FUN_LET (tm,tn,x)) = g (FUN_LET (tm,tn,format_ftree g x))

fun mk_guard is_rec (FUN_VAL tm) = if is_rec tm then FUN_VAL ``T`` else FUN_VAL ``F``
  | mk_guard is_rec (FUN_IF (tm,x,y)) = FUN_IF (tm,x,y)
  | mk_guard is_rec (FUN_LET (tm,tn,x)) = 
      case x of FUN_VAL y => FUN_VAL y | _ => FUN_LET (tm,tn,x)

fun mk_branch is_rec arb g (FUN_VAL tm) = if is_rec tm then FUN_VAL arb else FUN_VAL (g tm)
  | mk_branch is_rec arb g (FUN_IF (tm,x,y)) = FUN_IF (tm,x,y)
  | mk_branch is_rec arb g (FUN_LET (tm,tn,x)) = FUN_LET (tm,tn,x)

fun ftree_is_arb (FUN_VAL tm) = is_arb tm | ftree_is_arb _ = false

fun pull_arb (FUN_VAL tm) = FUN_VAL tm
  | pull_arb (FUN_IF (tm,x,y)) = let
      val x' = pull_arb x
      val y' = pull_arb y
      in if ftree_is_arb x' then y' else if ftree_is_arb y' then x' else FUN_IF (tm,x',y') end
  | pull_arb (FUN_LET (tm,tn,x)) = let
      val x' = pull_arb x
      in if ftree_is_arb x' then x' else FUN_LET (tm,tn,x') end

fun tailrec_define tm side_tm = let
  (* calculate instantations to TAILREC *)
  val (lhs,rhs) = dest_eq tm
  val f = tm2ftree rhs
  fun is_rec tm = (car tm = car lhs) handle e => false
  val input_type = type_of (cdr lhs)  
  val output_type = type_of lhs  
  val name = (fst o dest_var o car) lhs handle e => (fst o dest_const o car) lhs  
  val guard = ftree2tm (format_ftree (mk_guard is_rec) f)
  val guard = (cdr o concl o SIMP_CONV bool_ss []) guard handle e => guard
  val f1 = format_ftree (mk_branch (not o is_rec) (mk_arb input_type) cdr) f
  val f2 = format_ftree (mk_branch (is_rec) (mk_arb output_type) I) f
  (* perform definitions *)
  fun do_define fun_name b = let
    val fv = mk_var(fun_name,mk_type("fun",[type_of (cdr lhs),type_of b]))
    val fv = mk_eq(mk_comb(fv,cdr lhs),b)    
    in Define [ANTIQUOTE fv] end   
  fun do_guard_define fun_name b = 
    if not (b = ``F:bool``) then do_define fun_name b else let
      val fv = mk_var(fun_name,mk_type("fun",[type_of (cdr lhs),type_of b]))
      val fv = mk_eq(fv,mk_abs(mk_var("x",type_of (cdr lhs)),b))    
      in Define [ANTIQUOTE fv] end   
  val step = do_define (name^"_step") (ftree2tm (pull_arb f1))
  val base = do_define (name^"_base") (ftree2tm (pull_arb f2))
  val guard = do_guard_define (name^"_guard") guard
  val side = do_define (name^"_side") side_tm
  val def = ``TAILREC:('a->'a)->('a->'b)->('a->bool)->('a->bool)->'a->'b``
  val def = inst [``:'a``|->input_type,``:'b``|->output_type] def
  val pre_def = ``TAILREC_PRE:('a->'a)->('a->'b)->('a->bool)->('a->bool)->'a->bool``
  val pre_def = inst [``:'a``|->input_type,``:'b``|->output_type] pre_def
  fun select i = (car o cdr o car o concl o SPEC_ALL) i 
                 handle e => (cdr o car o concl o SPEC_ALL) i
  val hh = mk_comb(mk_comb(mk_comb(def,select step),select base),select guard)
  val hh = mk_comb(hh,select side) (*mk_abs(mk_var("x",input_type),``T``))*)
  val hh = mk_eq(mk_var(name,type_of hh),hh)  
  val pre_hh = mk_comb(mk_comb(mk_comb(pre_def,select step),select base),select guard)
  val pre_hh = mk_comb(pre_hh,select side)
  val pre_hh = mk_eq(mk_var(name^"_pre",type_of pre_hh),pre_hh)  
  val pre_f_def = Define [ANTIQUOTE pre_hh]  
  val f_def = Define [ANTIQUOTE hh]  
  (* descriptive theorem *)
  val goal = subst[car lhs |-> (cdr o car o concl o SPEC_ALL) f_def] tm
  val goal = mk_imp(mk_comb((cdr o car o concl o SPEC_ALL) pre_f_def,cdr lhs),goal)
  val th = prove(goal,    
    REWRITE_TAC [pre_f_def] THEN STRIP_TAC    
    THEN CONV_TAC (RATOR_CONV (REWRITE_CONV [f_def]))
    THEN IMP_RES_TAC TAILREC_THM THEN ASM_REWRITE_TAC []
    THEN REPEAT (POP_ASSUM (K ALL_TAC))
    THEN FULL_SIMP_TAC std_ss [base,step,guard,f_def,LET_DEF]
    THEN Cases_on [ANTIQUOTE ((fst o dest_eq o concl o SPEC_ALL) guard)]
    THEN FULL_SIMP_TAC std_ss [base,step,guard,f_def,LET_DEF])
  (* update simpsets *)
  val top = rewrites [f_def,pre_f_def]
  val part = rewrites [step,base,guard,side]
  val reverse = rewrites [GSYM f_def,GSYM pre_f_def]
  val _ = tailrec_simpset := simpLib.merge_ss[!tailrec_simpset,top,part];  
  val _ = tailrec_top_simpset := simpLib.merge_ss[!tailrec_top_simpset,top];  
  val _ = tailrec_part_simpset := simpLib.merge_ss[!tailrec_part_simpset,part];  
  val _ = tailrec_reverse_simpset := simpLib.merge_ss[!tailrec_reverse_simpset,reverse];  
  in th end;

val lemma = simpLib.SIMP_PROVE bool_ss [] ``!x y f g. (x = y) /\ (f = g) ==> (f x = g y)``
val lemma2 = prove(``!x y. ~x ==> y = x \/ y``,Cases_on `x` THEN REWRITE_TAC [])
fun TAILREC_EQ_TAC () = REPEAT (
  REPEAT STRIP_TAC 
  THEN FULL_SIMP_TAC (std_ss++tailrec_ss()) [] 
  THEN REPEAT (REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN STRIP_TAC)
  THEN FULL_SIMP_TAC (std_ss++tailrec_ss()) 
    [lemma2,FUN_EQ_THM,pairTheory.FORALL_PROD,LET_DEF])

(*
       
val tm = ``
  l(x,y) = let y = y + 1 in
           let (x,y) = (x + y - 7,FST (y,x)) in
             (x,y)``

val side_tm = ``x + y < 5``


val tm = ``
  k(x,y) = if x < 5 then x else
             let y = y + 1 in
             let (x,y) = (x + y - 7,FST (y,x)) in
               k(x,y)``

val side_tm = ``T``

val th = tailrec_define tm side_tm

  SIMP_CONV (std_ss++tailrec_ss()) []``l(x,y)``




*)

end;
