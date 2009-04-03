structure tailrecLib :> tailrecLib =
struct
  
open HolKernel boolLib bossLib Parse;
open tailrecTheory;

val car = fst o dest_comb;
val cdr = snd o dest_comb;

val tailrec_simpset         = ref (rewrites []);  
val tailrec_top_simpset     = ref (rewrites []);  
val tailrec_part_simpset    = ref (rewrites []);  
val tailrec_reverse_simpset = ref (rewrites []); 
fun tailrec_ss()         = !tailrec_simpset; 
fun tailrec_top_ss()     = !tailrec_top_simpset; 
fun tailrec_part_ss()    = !tailrec_part_simpset; 
fun tailrec_reverse_ss() = !tailrec_reverse_simpset; 

fun tailrec_add_to_simpsets(f_def,pre_f_def,step,base,guard,side) = let
  val top = rewrites [f_def,pre_f_def]
  val part = rewrites [step,base,guard,side]
  val reverse = rewrites [GSYM f_def,GSYM pre_f_def]
  val _ = tailrec_simpset := simpLib.merge_ss[!tailrec_simpset,top,part];  
  val _ = tailrec_top_simpset := simpLib.merge_ss[!tailrec_top_simpset,top];  
  val _ = tailrec_part_simpset := simpLib.merge_ss[!tailrec_part_simpset,part];  
  val _ = tailrec_reverse_simpset := simpLib.merge_ss[!tailrec_reverse_simpset,reverse];  
  in () end;


datatype ftree_type = 
    FUN_IF of term * ftree_type * ftree_type 
  | FUN_LET of term * term * ftree_type
  | FUN_VAL of term;

fun ftree_type_eq (FUN_IF(t1,aty1,bty1)) (FUN_IF(t2,aty2,bty2)) =
      eq t1 t2 andalso ftree_type_eq aty1 aty2 andalso ftree_type_eq bty1 bty2
  | ftree_type_eq (FUN_LET(at1,bt1,fty1)) (FUN_LET(at2,bt2,fty2)) = 
      eq at1 at2 andalso eq bt1 bt2 andalso ftree_type_eq fty1 fty2
  | ftree_type_eq (FUN_VAL t1) (FUN_VAL t2) = eq t1 t2
  | ftree_type_eq _ _ = false;

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

fun pull_T (FUN_VAL tm) = FUN_VAL tm
  | pull_T (FUN_IF (tm,x,y)) = let
      val x' = pull_T x
      val y' = pull_T y
      val eq = ftree_type_eq
      in if (eq x' (FUN_VAL ``T:bool``)) andalso (eq y' (FUN_VAL ``T:bool``)) orelse (eq x' y') 
         then x' else FUN_IF (tm,x',y') end
  | pull_T (FUN_LET (tm,tn,x)) = let
      val x' = pull_T x
      val vs = free_vars (ftree2tm x')
      val ws = free_vars tm
      in if null (filter (fn v => op_mem eq v ws) vs) then x' else FUN_LET (tm,tn,x') end

val if_expand = prove(``(if x then y else z) = (x /\ y) \/ (~x /\ z)``,
  Cases_on `x` THEN ASM_SIMP_TAC std_ss []);

val implies_expand = prove(``(x:bool ==> y) = ~x \/ y``,
  Cases_on `x` THEN ASM_SIMP_TAC std_ss []);

fun tailrec_define tm side_option = let
  (* remove ``():unit`` constant from lhs *)
  fun apply g NONE = NONE
    | apply g (SOME x) = SOME (g x)
  fun remove_unit tm = let
    val (x,y) = dest_eq tm
    in (mk_eq(subst [``():unit``|->mk_var("()",``:unit``)] x,y)) end
  val (tm,side_option) = (remove_unit tm, apply remove_unit side_option)
  (* calculate instantations to TAILREC *)
  val side_option = (case side_option of NONE => NONE | SOME tm => if is_eq tm then SOME tm else NONE)
  val (lhs,rhs) = dest_eq tm
  val f = tm2ftree rhs
  fun is_rec tm = eq (car tm) (car lhs) handle e => false
  val input_type = type_of (cdr lhs)  
  val output_type = type_of lhs  
  val name = (fst o dest_var o car) lhs handle e => (fst o dest_const o car) lhs  
  val guard_tm = ftree2tm (format_ftree (mk_guard is_rec) f)
  val guard_tm = (cdr o concl o SIMP_CONV bool_ss []) guard_tm handle e => guard_tm
  val f1 = format_ftree (mk_branch (not o is_rec) (mk_arb input_type) cdr) f
  val f2 = format_ftree (mk_branch (is_rec) (mk_arb output_type) I) f
  val guard_tm = if is_arb (ftree2tm (pull_arb f1)) then ``F:bool`` else guard_tm
  (* format side condition *)
  fun replace_base h (FUN_IF (tm,x,y)) = FUN_IF (tm, replace_base h x, replace_base h y)
    | replace_base h (FUN_LET (tm,tn,x)) = FUN_LET (tm, tn, replace_base h x)
    | replace_base h (FUN_VAL tm) = FUN_VAL (h tm)
  fun sim tm2 = subst [(car o cdr o car) tm2 |-> mk_abs(genvar(type_of ((cdr o cdr o car) tm2)),``T``)]
  fun sim' tm = (snd o dest_eq o concl o SIMP_CONV std_ss []) tm handle e => tm
  fun get_side NONE = replace_base (fn x => ``T:bool``) f
    | get_side (SOME tm) = replace_base (sim' o sim tm) (tm2ftree (cdr tm))
  val side_f_tm = ftree2tm (pull_T (get_side side_option))
  (* perform definitions *)
  fun do_define fun_name b = let
    val fv = mk_var(fun_name,mk_type("fun",[type_of (cdr lhs),type_of b]))
    val fv = mk_eq(mk_comb(fv,cdr lhs),b)    
    in Define [ANTIQUOTE fv] end   
  fun do_guard_define fun_name b = 
    if not (eq b ``F:bool``) then do_define fun_name b else let
      val fv = mk_var(fun_name,mk_type("fun",[type_of (cdr lhs),type_of b]))
      val fv = mk_eq(fv,mk_abs(mk_var("x",type_of (cdr lhs)),b))    
      in Define [ANTIQUOTE fv] end   
  val step = do_define (name^"_step") (ftree2tm (pull_arb f1))
  val base = do_define (name^"_base") (ftree2tm (pull_arb f2))
  val guard = do_guard_define (name^"_guard") guard_tm
  val side = do_define (name^"_side") side_f_tm
  val def = ``TAILREC:('a->'a)->('a->'b)->('a->bool)->'a->'b``
  val def = inst [``:'a``|->input_type,``:'b``|->output_type] def
  val pre_def = ``TAILREC_PRE:('a->'a)->('a->bool)->('a->bool)->'a->bool``
  val pre_def = inst [``:'a``|->input_type] pre_def
  fun select i = (car o cdr o car o concl o SPEC_ALL) i 
                 handle e => (cdr o car o concl o SPEC_ALL) i
  val hh = mk_comb(mk_comb(mk_comb(def,select step),select base),select guard)
  val hh = mk_eq(mk_var(name,type_of hh),hh)  
  val pre_hh = mk_comb(mk_comb(mk_comb(pre_def,select step),select guard),select side)
  val pre_hh = mk_eq(mk_var(name^"_pre",type_of pre_hh),pre_hh)  
  val pre_f_def = Define [ANTIQUOTE pre_hh]  
  val f_def = Define [ANTIQUOTE hh]  
  (* descriptive theorem for function *)
  val goal = subst[car lhs |-> (cdr o car o concl o SPEC_ALL) f_def] tm
  val case_split_tac = 
    if eq guard_tm ``F`` then ALL_TAC else Cases_on [ANTIQUOTE ((fst o dest_eq o concl o SPEC_ALL) guard)]
  val main_th = store_thm(name,goal,   
    CONV_TAC (RATOR_CONV (REWRITE_CONV [f_def]))
    THEN ONCE_REWRITE_TAC [TAILREC_THM] 
    THEN case_split_tac
    THEN ASM_SIMP_TAC std_ss [GSYM f_def]
    THEN FULL_SIMP_TAC (std_ss++helperLib.pbeta_ss) [base,step,guard,f_def,LET_DEF,if_expand,implies_expand]
    THEN FULL_SIMP_TAC (std_ss++helperLib.pbeta_ss) [base,step,guard,f_def,LET_DEF,if_expand,implies_expand]
    THEN SRW_TAC [] [])
  (* descriptive theorem for precondition *)
  val pre = mk_comb((cdr o car o concl o SPEC_ALL) pre_f_def,cdr lhs)
  fun get_side NONE = replace_base (fn x => if eq x lhs then pre else ``T:bool``) f
    | get_side (SOME tm) = replace_base (subst [(car o cdr o car) tm |-> car pre]) (tm2ftree (cdr tm))
  val goal = mk_eq (pre,ftree2tm (pull_T (get_side side_option)))
  val side_th = store_thm(name ^ "_pre",goal,   
    CONV_TAC (RATOR_CONV (REWRITE_CONV [pre_f_def]))
    THEN ONCE_REWRITE_TAC [TAILREC_PRE_THM] 
    THEN REWRITE_TAC [pre_f_def]
    THEN case_split_tac
    THEN ASM_SIMP_TAC bool_ss []
    THEN (if eq guard_tm ``F`` then ONCE_REWRITE_TAC [TAILREC_PRE_THM] else REPEAT STRIP_TAC THEN EQ_TAC)
    THEN FULL_SIMP_TAC (std_ss++helperLib.pbeta_ss) [base,step,guard,side,LET_DEF]
    THEN FULL_SIMP_TAC (std_ss++helperLib.pbeta_ss) [base,step,guard,f_def,LET_DEF,if_expand,implies_expand]
    THEN SRW_TAC [] [] THEN METIS_TAC [])
  (* update simpsets *)
  val _ = tailrec_add_to_simpsets(f_def,pre_f_def,step,base,guard,side)
  in (main_th,side_th) end;

val lemma = simpLib.SIMP_PROVE bool_ss [] ``!x y f g. (x = y) /\ (f = g) ==> ((f:'a->'b) x = g y)``
val lemma2 = prove(``!x y. ~x ==> y = x \/ y``,Cases_on `x` THEN REWRITE_TAC [])
fun TAILREC_EQ_TAC () = REPEAT (
  REPEAT STRIP_TAC 
  THEN FULL_SIMP_TAC (std_ss++tailrec_ss()) [] 
  THEN REPEAT (REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN STRIP_TAC)
  THEN FULL_SIMP_TAC (std_ss++tailrec_ss()) 
    [lemma2,FUN_EQ_THM,pairTheory.FORALL_PROD,LET_DEF])

(*

open wordsTheory;

val tm = ``
  test1 (r1:word32,r2:word32,dm:word32 set,m:word32->word32) =
    if r1 = 0w then (r1,r2,dm,m) else
      let r1 = m r1 in
      let r2 = r2 + 1w in
        test1 (r1,r2,dm,m)``

val side_tm = ``
  test1_pre (r1:word32,r2:word32,dm:word32 set,m:word32->word32) =
    if r1 = 0w then T else
      let cond = ALIGNED r1 in
      let r1 = m r1 in
      let r2 = r2 + 1w in
        test1_pre (r1,r2,dm,m) /\ cond``

val side_option = SOME side_tm

*)

end;
