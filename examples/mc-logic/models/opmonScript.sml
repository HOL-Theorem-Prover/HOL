open HolKernel boolLib bossLib Parse;
open optionTheory;

val _ = new_theory "opmon";



(* operations over options *)

val option_orelse_def = Define `
  option_orelse f g x = 
    let m = f x in (if m = NONE then g x else m)`;

val option_then_def = Define `
  option_then f g x =  
    let m = f x in (if m = NONE then NONE else g (THE m))`;

val option_parallel_def = Define `
  option_parallel = option_then`;

val _ = overload_on ("++",Term`$option_orelse`);
val _ = overload_on (">>",Term`$option_then`);
val _ = overload_on (">>|",Term`$option_parallel`);
val _ = add_infix("++", 680,HOLgrammars.LEFT);
val _ = add_infix(">>", 680,HOLgrammars.LEFT);
val _ = add_infix(">>|", 680,HOLgrammars.LEFT);

val option_fail_def = Define `option_fail = \x. NONE`;

val option_do_def = Define `
  (option_do [] = option_fail) /\
  (option_do [t] = t) /\
  (option_do (t1::t2::ts) = t1 >> option_do (t2::ts))`;

val option_try_def = Define `
  (option_try [] = option_fail) /\
  (option_try [t] = t) /\
  (option_try (t1::t2::ts) = t1 ++ option_try (t2::ts))`;


(* monads *)

val LOCAL_def = Define `
  LOCAL (f:(unit#'a)->(unit#'a)option) x = 
    let m = f ((),x) in if m = NONE then NONE else SOME (SND (THE m))`;

val opt_assert_def = Define `opt_assert p x = if p x then SOME x else NONE`;
val opt_push_def   = Define `opt_push f (x,y) = SOME ((f y,x),y)`;
val opt_pop_def    = Define `opt_pop ((v,x),y) = SOME (x,y)`;
val opt_dup_def    = Define `opt_dup ((v,x),y) = SOME ((v,v,x),y)`;
val opt_swap_def   = Define `opt_swap ((v,u,x),y) = SOME ((u,v,x),y)`;
val opt_monop_def  = Define `opt_monop f ((v,x),y) = SOME ((f v,x),y)`;
val opt_binop_def  = Define `opt_binop f ((v,u,x),y) = SOME ((f u v,x),y)`;
val opt_trinop_def = Define `opt_trinop f ((v,u,s,x),y) = SOME ((f s u v,x),y)`;
val opt_quadop_def = Define `opt_quadop f ((v,u,s,t,x),y) = SOME ((f t s u v,x),y)`;
val opt_s_pop_def  = Define `opt_s_pop f ((v,x),y) = SOME (x,f v y)`;
val opt_s_pop2_def = Define `opt_s_pop2 f ((v,u,x),y) = SOME (x,f u v y)`;
val opt_s_push_def = Define `opt_s_push f ((v,x),y) = SOME ((f v y,x),y)`;
val opt_cond_def   = Define `opt_cond f b1 b2 ((x,y),s) = 
                               if f x then b1 (y,s) else b2 (y,s)`;
val opt_do_pop_def = Define `opt_do_pop f ((x,y),z) = f x (y,z)`;
val opt_push_const_def = Define `opt_push_const (x:'a) = opt_push (K x)`;

val opt_try_monop_def = Define `
  opt_try_monop f ((v,x),s) = 
    let m = f v in if m = NONE then NONE else SOME ((THE m,x),s)`;

val opt_try_s_pop_def = Define `
  opt_try_s_pop f ((v,x),s) = 
    let m = f v s in if m = NONE then NONE else SOME (x,THE m)`;

val opt_try_s_pop2_def = Define `
  opt_try_s_pop2 f ((v,u,x),s) = 
    let m = f u v s in if m = NONE then NONE else SOME (x,THE m)`;

val opt_monop_the_def = Define `
  opt_monop_the = opt_assert (\((v,x),s). ~(v = NONE)) >> opt_monop THE`;


(* theorems *)

val option_then_assoc = store_thm("option_then_assoc",
  ``!x y z. (x >> y) >> z = x >> (y >> z)``,
  SIMP_TAC std_ss [FUN_EQ_THM,option_then_def,LET_DEF]  
  THEN REPEAT STRIP_TAC THEN Cases_on `x x'` THEN SRW_TAC [] []);

val option_orelse_assoc = store_thm("option_orelse_assoc",
  ``!x y z. (x ++ y) ++ z = x ++ (y ++ z)``,
  SIMP_TAC std_ss [FUN_EQ_THM,option_orelse_def,LET_DEF]  
  THEN REPEAT STRIP_TAC THEN Cases_on `x x'` THEN SRW_TAC [] []);

val option_then_OVER_orelse = store_thm("option_then_OVER_orelse",
  ``!x:'a -> 'b option y:'b -> 'c option g. 
      ((x >> y) ++ (x >> z) = x >> (y ++ z)) /\ 
      (g ++ (x >> y) ++ (x >> z) = g ++ x >> (y ++ z)) /\ 
      ((x >> y) ++ (x >> z) ++ g = x >> (y ++ z) ++ g) /\ 
      (h ++ (x >> y) ++ (x >> z) ++ g = h ++ x >> (y ++ z) ++ g)``,
  REPEAT STRIP_TAC THEN `x >> y ++ x >> z = x >> (y ++ z)` by 
    (SIMP_TAC std_ss [FUN_EQ_THM,option_orelse_def,option_then_def,LET_DEF]  
     THEN REPEAT STRIP_TAC THEN Cases_on `x x'` THEN SRW_TAC [] [])
  THEN METIS_TAC [option_orelse_assoc]);

val option_orelse_SOME = store_thm("option_orelse_SOME",
  ``!f g h. 
      (f ++ g) >> SOME o k = (f >> SOME o k) ++ (g >> SOME o k)``,
  SIMP_TAC std_ss [FUN_EQ_THM,option_orelse_def,option_then_def,LET_DEF]  
  THEN REPEAT STRIP_TAC THEN Cases_on `f x`
  THEN ASM_SIMP_TAC std_ss []);

val opt_thm = store_thm("opt_thm",  
  ``((opt_push f4 >> p4) (x,y) = p4 ((f4 y,x),y)) /\
    ((opt_dup >> p9) ((u,x),y) = p9 ((u,u,x),y)) /\ 
    ((opt_monop f3 >> p3) ((u,x),y) = p3 ((f3 u,x),y)) /\ 
    ((opt_binop f >> p) ((u,v,x),y) = p ((f v u,x),y)) /\ 
    ((opt_quadop f78 >> p56) ((t1,t2,u,v,x),y) = p56 ((f78 v u t2 t1,x),y)) /\ 
    ((opt_s_push f6 >> p6) ((u,x),y) = p6 ((f6 u y,x),y)) /\  
    ((opt_s_pop f5 >> p5) ((u,x),y) = p5 (x,f5 u y)) /\ 
    ((opt_s_pop2 f2 >> p2) ((u,v,x),y) = p2 (x,f2 v u y)) /\ 
    ((opt_do_pop h9 >> p7) ((ww,x),y) = (h9 ww >> p7) (x,y)) /\ 
    ((opt_swap >> q) ((u,v,x),y) = q ((v,u,x),y)) /\
    ((opt_pop >> q56) ((u,x),y) = q56 (x,y)) /\
    ((opt_cond g r1 r2 >> p10) ((uu,x),y) = 
       if g uu then (r1 >> p10) (x,y) else (r2 >> p10) (x,y)) /\
    ((opt_assert d >> t) h = if d h then t h else NONE)``,
  Cases_on `d h` THEN Cases_on `g uu` 
  THEN ASM_SIMP_TAC std_ss [opt_push_def, opt_binop_def, opt_cond_def,
    opt_monop_def, opt_s_pop_def, opt_s_pop2_def, opt_s_push_def,
    opt_dup_def, opt_assert_def, opt_swap_def, option_then_def,
    opt_do_pop_def, opt_quadop_def, opt_pop_def, LET_DEF]);

val _ = export_theory ();
