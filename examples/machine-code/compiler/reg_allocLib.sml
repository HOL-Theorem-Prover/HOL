structure reg_allocLib :> reg_allocLib =
struct

open HolKernel boolLib bossLib Parse;
open wordsTheory codegen_inputLib helperLib;

local
  val compiler_abbrevs = ref let
    fun kk i = if i < 32 then i::kk(i+1) else []
    val ys = map (numSyntax.mk_numeral o Arbnum.fromInt) (kk 1)
    val ys = map (fn x => ISPECL [mk_var("w",``:word32``),x] WORD_MUL_LSL) ys
    val ys = map (GSYM o (CONV_RULE (RAND_CONV EVAL))) ys
    val ys = map (ONCE_REWRITE_RULE [WORD_MULT_COMM]) ys @ ys
    in ys end      
  in
    fun add_abbrevs thms = (compiler_abbrevs := thms @ (!compiler_abbrevs))
    fun COMPILER_UNABBREV_CONV tm = REWRITE_CONV (!compiler_abbrevs) tm
  end;

val get_temp_name = let
  val n = ref 0
  in (fn () => (n := (!n) + 1; "_" ^ int_to_string (!n))) end
fun mk_temp_var ty = mk_var(get_temp_name(),ty)
fun is_temp_var v = String.isPrefix "_" (fst (dest_var v)) handle HOL_ERR _ => false

val get_t_name = let
  val n = ref 0
  in (fn () => (n := (!n) + 1; "t" ^ int_to_string (!n))) end
fun mk_t_var ty = mk_var(get_t_name(),ty)
fun is_t_var v = String.isPrefix "t" (fst (dest_var v)) handle HOL_ERR _ => false



(* various helpers *)

fun all_distinct [] = []
  | all_distinct (x::xs) = x :: all_distinct (filter (fn y => not (x = y)) xs)

fun append_lists [] = []
  | append_lists (y::ys) = y @ append_lists ys

fun diff xs ys = filter (fn y => not (mem y ys)) xs
fun intersect xs ys = filter (fn y => mem y xs) ys

fun dest_tuple tm =
  let val (x,y) = pairSyntax.dest_pair tm in x :: dest_tuple y end handle HOL_ERR e => [tm];

fun list_find x [] = fail() 
  | list_find x ((y,z)::zs) = if x = y then z else list_find x zs

val EXPAND_LET_CONV = 
  (RATOR_CONV o RATOR_CONV) (ONCE_REWRITE_CONV [LET_DEF]) THENC
   RATOR_CONV BETA_CONV THENC BETA_CONV THENC BETA_CONV

fun mk_tuple [] = ``()``
  | mk_tuple [x] = x
  | mk_tuple (x::xs) = pairSyntax.mk_pair(x,mk_tuple xs)


(* this conversion flattens large expressions into compilable assignments *)

fun BOTTOM_UP_CONV c tm = 
  case dest_term tm of 
    COMB _ => (RAND_CONV (BOTTOM_UP_CONV c) THENC 
               RATOR_CONV (BOTTOM_UP_CONV c) THENC 
               TRY_CONV c) tm
  | LAMB _ => (ABS_CONV (BOTTOM_UP_CONV c) THENC 
               TRY_CONV c) tm
  | _ =>      (TRY_CONV c) tm

fun TOP_DOWN_CONV c tm = 
  (TRY_CONV c THENC (fn tm => 
    case dest_term tm of 
      COMB _ => (RAND_CONV (TOP_DOWN_CONV c) THENC RATOR_CONV (TOP_DOWN_CONV c)) tm
    | LAMB _ => (ABS_CONV (TOP_DOWN_CONV c)) tm
    | _ =>      ALL_CONV tm)) tm

fun FLATTEN_EXPS_CONV tm = let
  fun is_compilable tm = let
    val vs = filter (fn x => type_of x = ``:word32``) (free_vars tm)
    val r0 = mk_var("r0",``:word32``)
    val tm = subst (map (fn x => x |-> r0) vs) tm
    val result = case term2assign ``r1:word32`` tm of
                   ASSIGN_OTHER _ => false | _ => true
                 handle HOL_ERR _ => false | Empty => false
    in result end handle HOL_ERR _ => false
  fun is_c_guard tm = let
    val vs = filter (fn x => type_of x = ``:word32``) (free_vars tm)
    val r0 = mk_var("r0",``:word32``)
    val tm = subst (map (fn x => x |-> r0) vs) tm
    val result = case term2guard tm of
                    GUARD_OTHER _ => false  
                  | GUARD_NOT (GUARD_OTHER _) => false  
                  | _ => true
                 handle HOL_ERR _ => false | Empty => false
    in result end handle HOL_ERR _ => false
  fun one [x] = x | one _ = fail()
  fun divide_aux g (xs,rhs) = if g rhs then (xs,rhs) else let
    val t = find_term (fn x => is_compilable x andalso not (is_var x)) rhs
    val ty = type_of t
    val temp = mk_temp_var ty
    val temp = if ty = ``:word32`` then temp else 
                 find_term (fn v => is_var v andalso (ty = type_of v)) t
                 handle HOL_ERR _ => temp
    in divide_aux g (xs @ [(temp,t)], subst [t |-> temp] rhs) end
    handle HOL_ERR _ => (xs,rhs)
  fun partition p xs = filter p xs @ filter (not o p) xs
  fun divide g (xs,rhs) = let
    val (xs,rhs) = divide_aux g (xs,rhs)
    val xs = partition (fn x => type_of (fst x) = ``:word32``) xs
    in (xs,rhs) end
  fun CONJUNCTS_CONV c tm = 
    if is_conj tm then BINOP_CONV (CONJUNCTS_CONV c) tm else c tm
  fun FORALL_CONV c tm = 
    if is_forall tm then QUANT_CONV (FORALL_CONV c) tm else c tm 
  val FUNC_BODY_CONV = CONJUNCTS_CONV o FORALL_CONV o RAND_CONV  
  fun FLAT_CONV tm = let
    val f = tm2ftree tm
    fun lets ([],y) = y
      | lets ((x1,x2)::xs,y) = FUN_LET (x1,x2,lets (xs,y)) 
    fun ftree_each (FUN_VAL rhs) = let
          val (xs,rhs2) = divide is_compilable ([],rhs)  
          in lets (xs,FUN_VAL rhs2) end
      | ftree_each (FUN_LET (lhs,rhs,t)) = let
          val (xs,rhs2) = divide is_compilable ([],rhs)  
          in lets (xs,FUN_LET (lhs,rhs2,ftree_each t)) end
      | ftree_each (FUN_IF (b,t1,t2)) = let
          val (xs,b2) = divide is_c_guard ([],b)  
          in lets (xs,FUN_IF (b2,ftree_each t1,ftree_each t2)) end
      | ftree_each (FUN_COND (b,t)) = FUN_COND (b,ftree_each t)
    val tm2 = ftree2tm (ftree_each f)
    fun EXPAND_TEMPVARLET_CONV tm = let
      val (v,x) = dest_abs (fst (dest_let tm))
      in if is_temp_var v then EXPAND_LET_CONV tm else NO_CONV tm end 
      handle HOL_ERR _ => NO_CONV tm
    val goal = mk_eq(tm,tm2)
    val result = auto_prove "FLAT_CONV" (goal,
      CONV_TAC (BOTTOM_UP_CONV EXPAND_TEMPVARLET_CONV) THEN REWRITE_TAC [])
    in result end
  val result = FUNC_BODY_CONV FLAT_CONV tm
  in result end;


(* translation into ssa form, at least for word32 variables other than r0,r1... *)

fun not_fixed_reg v = let
  val (name,ty) = dest_var v
  val ii = explode name
  val reg = mem (hd ii) [#"r",#"s"] andalso 
            (filter (fn x => not (mem x [#"0",#"1",#"2",#"3",#"4",#"5",#"6",#"7",#"8",#"9",#"'"])) (tl ii) = [])
  in (ty = ``:word32``) andalso not reg end
  handle HOL_ERR _ => false

val SSA_CONV = let
  fun rename tm = let
    val (v,x) = dest_abs tm
    in if not_fixed_reg v then ALPHA_CONV (mk_t_var(type_of v)) tm 
                          else NO_CONV tm end
  in BOTTOM_UP_CONV rename end

val COMMON_SUBEXP_CONV = let
  fun aux tm = let  
    val (x,y) = dest_let tm
    val (v,x) = dest_abs x
    val _ = dest_var v
    val _ = if not_fixed_reg v then () else fail()
    val _ = find_term (fn x => x = y) x
    val x2 = subst [y|->v] x
    val tm2 = mk_let(mk_abs(v,x2),y)
    val goal = mk_eq(tm,tm2)
    val EXPAND_LET_CONV = 
      (RATOR_CONV o RATOR_CONV) (ONCE_REWRITE_CONV [LET_DEF]) THENC
       RATOR_CONV BETA_CONV THENC BETA_CONV THENC BETA_CONV
    val thi = auto_prove "" (goal,  
      CONV_TAC (BINOP_CONV EXPAND_LET_CONV) THEN REWRITE_TAC [])
    fun DELETE_EXTRA_MOVE_CONV tm = let
      val (x,y) = dest_let tm
      val (v,x) = dest_abs x
      val _ = dest_var v
      val _ = dest_var y
      val _ = if not_fixed_reg v then () else fail()
      in EXPAND_LET_CONV tm end           
    in ((fn tm => thi) THENC BOTTOM_UP_CONV DELETE_EXTRA_MOVE_CONV) tm end
  in TOP_DOWN_CONV aux end


(* restrict register names *)

fun parallel_assign tm2 tm = let (* both tm and tm2 must be tuples of variables *)
  (* make basic parallel assignment *)
  val (m,_) = match_term tm tm2
  val xs = filter (fn x => not (x = subst m x)) (dest_tuple tm)
  val vs = map (fn x => mk_temp_var (type_of x)) xs
  val rs = zip vs xs @ zip (map (subst m) xs) vs
  (* optimise: copy forward *)
  fun forward [] aux = []
    | forward ((x,y)::xs) aux = let
        val y = list_find y aux handle HOL_ERR _ => y
        val aux = filter (fn (lhs,rhs) => not (mem x (free_vars rhs))) aux
        in (x,y) :: forward xs ((x,y)::aux) end
  val rs = forward rs []
  (* optimise: remove unused temporary variables *)  
  fun is_used x [] = not (is_temp_var x)
    | is_used x ((y,z)::xs) = if mem x (free_vars z) then true else is_used x xs
  fun in_tail [] = []
    | in_tail ((x,y)::xs) = if is_used x xs then (x,y)::in_tail xs else in_tail xs
  val rs = in_tail rs
  in rs end;

fun FIX_CALL_RETURN_VALUES_CONV tm = let
  (* find one return value for each function *)
  fun in_out x = let 
    val (lhs,rhs) = dest_eq x
    fun leaves (FUN_COND (_,t)) = leaves t
      | leaves (FUN_LET (_,_,t)) = leaves t
      | leaves (FUN_IF (_,t1,t2)) = leaves t1 @ leaves t2
      | leaves (FUN_VAL tm) = [tm]
    val bases = filter (not o can (match_term lhs)) (leaves (tm2ftree rhs))
    in (car lhs, (cdr lhs, hd bases)) end
  val xs = map (repeat (snd o dest_forall)) (list_dest dest_conj tm)
  val io = map in_out xs
  (* invent new temporaries for each return value *)
  fun invent_new_temps (x,(y,z)) = let
    val f = map (fn z => if is_t_var z then mk_t_var(type_of z) else z) 
    in (x,(y,mk_tuple (f (dest_tuple z)))) end
  val io = map invent_new_temps io
  (* add restrictions on already compiled components *)
  (* ... *)
  (* make sure all function calls/returns respect this io restriction *)  
  fun CONJUNCTS_CONV c tm = 
    if is_conj tm then BINOP_CONV (CONJUNCTS_CONV c) tm else c tm
  fun FORALL_CONV c tm = 
    if is_forall tm then QUANT_CONV (FORALL_CONV c) tm else c tm 
  val FUNC_BODY_CONV = CONJUNCTS_CONV o FORALL_CONV
  fun FLAT_CONV tm = let
    val func_tm = (car o fst o dest_eq) tm
    val f = tm2ftree (cdr tm)
    fun lets [] y = y
      | lets ((x1,x2)::xs) y = FUN_LET (x1,x2,lets xs y) 
    fun ftree_each (FUN_IF (b,t1,t2)) = FUN_IF (b,ftree_each t1,ftree_each t2)
      | ftree_each (FUN_COND (b,t)) = FUN_COND (b,ftree_each t)
      | ftree_each (FUN_VAL rhs) = let
          val call = (car rhs = func_tm) handle HOL_ERR _ => false
          val x = (if call then fst else snd) (list_find func_tm io)
          val rhs2 = if call then cdr rhs else rhs
          val rs1 = parallel_assign x rhs2                   
          val ret = if call then mk_comb(func_tm,x) else x
          in lets rs1 (FUN_VAL ret) end
      | ftree_each (FUN_LET (lhs,rhs,t)) = let
          val (x,y) = list_find (car rhs) io
          val rs1 = parallel_assign x (cdr rhs)                   
          val rs2 = parallel_assign lhs y
          in lets rs1 (FUN_LET (y,mk_comb(car rhs,x),lets rs2 (ftree_each t))) end
          handle HOL_ERR _ => FUN_LET (lhs,rhs,ftree_each t)
    val tm2 = ftree2tm (ftree_each f)
    fun EXPAND_TEMPVARLET_CONV tm = let
      val (v,x) = dest_abs (fst (dest_let tm))
      in if is_temp_var v then EXPAND_LET_CONV tm else NO_CONV tm end 
      handle HOL_ERR _ => NO_CONV tm
    val goal = mk_eq(tm,mk_eq((fst o dest_eq) tm,tm2))
    val result = auto_prove "FLAT_CONV" (goal,SIMP_TAC std_ss [LET_DEF])
    in result end
  val result = FUNC_BODY_CONV FLAT_CONV tm  
  in result end; 


(* clash graph and reg allocation *)

fun ftree_free_vars t = let
  fun vars (FUN_VAL tm) = free_vars tm
    | vars (FUN_COND (tm,t)) = free_vars tm @ vars t
    | vars (FUN_IF (tm,x1,x2)) = all_distinct (free_vars tm @ vars x1 @ vars x2)
    | vars (FUN_LET (lhs,rhs,t)) = all_distinct (free_vars lhs @ free_vars rhs @ vars t)
  in all_distinct (vars t) end;

fun subroutine_internal_vars (tm,t) = let
  val vs = free_vars (cdr tm)
  fun leaves (FUN_COND (_,t)) = leaves t
    | leaves (FUN_LET (_,_,t)) = leaves t
    | leaves (FUN_IF (_,t1,t2)) = leaves t1 @ leaves t2
    | leaves (FUN_VAL tm) = [tm]
  val xs = append_lists (map free_vars (leaves t))
  in diff (ftree_free_vars t) (vs @ xs) end

fun clash_graph ts = let
  fun ok_var x = (type_of x = ``:word32``)
  fun add_live_set ls t = FUN_COND
       (mk_eq(listSyntax.mk_list(all_distinct ls,``:word32``),listSyntax.mk_list([],``:word32``)),t)
  val fs = map (car o fst) ts
  fun get_internal_vars rhs = 
    if not (mem (car rhs) fs) handle HOL_ERR _ => true then [] else
      subroutine_internal_vars (hd (filter (fn (x,_) => x = rhs) ts))
  fun live (FUN_VAL tm) = let
        val ls = filter ok_var (free_vars tm)
        val t = add_live_set ls (FUN_VAL tm)
        in (ls,t) end
    | live (FUN_COND (tm,t)) = fail()
    | live (FUN_IF (tm,x1,x2)) = let
        val (ls1,y1) = live x1
        val (ls2,y2) = live x2
        val ls = (filter ok_var (free_vars tm)) @ ls1 @ ls2
        val t = add_live_set ls (FUN_IF (tm,y1,y2))
        in (ls,t) end
    | live (FUN_LET (lhs,rhs,t)) = let
        val (ls,tt) = live t 
        val vs = (filter ok_var (free_vars lhs))
        val ls = diff ls vs @ (filter ok_var (free_vars rhs))
        val ii = get_internal_vars rhs
        val t = add_live_set (ii @ ls) (FUN_LET (lhs,rhs,tt))
        in (ls,t) end
  fun collect (FUN_VAL tm) = []
    | collect (FUN_COND (tm,t)) = (fst o listSyntax.dest_list o fst o dest_eq) tm :: collect t
    | collect (FUN_IF (tm,x1,x2)) = collect x1 @ collect x2
    | collect (FUN_LET (lhs,rhs,t)) = collect t
  val live_sets = append_lists 
    (map (fn (f,t) => all_distinct (collect (snd (live t)))) ts)  
  fun clash [] y z = false
    | clash (x::xs) y z = (mem y x andalso mem z x) orelse clash xs y z
  val all_vars = all_distinct (append_lists live_sets)
  val graph = map (fn v => (v,filter (clash live_sets v) all_vars)) all_vars
  val graph = map (fn (v,cs) => (v,filter (fn y => not (y = v)) cs)) graph
  in graph end

fun move_assignments ts graph = let
  fun pref (FUN_COND (_,t)) = pref t
    | pref (FUN_IF (_,t1,t2)) = pref t1 @ pref t2
    | pref (FUN_VAL tm) = []
    | pref (FUN_LET (x,y,t)) = 
        if is_var x andalso is_var y then (x,y)::pref t else pref t
  val moves = append_lists (map (pref o snd) ts)
  in moves end;

(* iterated_register_coalescing implements algorithm by George and Appel '96 *)
fun iterated_register_coalescing graph moves freq is_colourable n = let
  val init_graph = graph
  fun kk n = if n < 0 then [] else n::kk(n-1)   
  val regs = map (fn n => mk_var("r" ^ (int_to_string n),``:word32``)) (rev (kk (n-1)))
  val gsort = sort (fn (xz,x) => fn (yz:term,y:term list) => length x <= length y) 
  val r = map fst (filter (fn (x,xs) => mem x regs) graph)   
  val q = filter (fn (x,xs) => not (mem x regs)) graph
  fun move_related [] = []
    | move_related ((x,y)::moves) = x::y::move_related moves
  fun print_graph graph = 
    (map (fn (v,ns) => (print "\n  "; print_term v; print ":";
          map (fn x => (print " "; print_term x)) ns)) graph; print "\n")
  fun join_all joined x = join_all joined (list_find x joined) handle HOL_ERR _ => x
  fun merge_vertexes x y (graph,moves,joined) = let
    val xs = filter (fn v => not (v = x) andalso not (v = y)) (list_find x graph)
    val ys = filter (fn v => not (v = x) andalso not (v = y)) (list_find y graph)
    val graph = filter (fn (v,ns) => not (v = x) andalso not (v = y)) graph
    val graph = map (fn (v,ns) => (v,all_distinct (map (fn n => if n = y then x else n) ns))) graph
    val graph = (x,all_distinct (xs @ ys)) :: graph
    val moves = filter (fn z => not (z = (x,y))) moves
    val moves = map (fn (z1,z2) => (if z1 = y then x else z1,if z2 = y then x else z2)) moves
    val joined = (y,x)::joined
    in (graph,moves,joined) end;
  fun delete_vertex w (graph,moves,joined) = let
    val graph = filter (fn (v,ns) => not (v = w)) graph
    val graph = map (fn (v,ns) => (v,filter (fn n => not (n = w)) ns)) graph
    val moves = filter (fn (x,y) => not (x = w) andalso not (y = w)) moves
    in (graph,moves,joined) end;
  fun busy w = list_find w freq handle HOL_ERR _ => 0
  fun no_print s = print s
  fun build_stack graph moves joined n result =
    (* simplification: ?w. ~(w IN ms) and degree w < n, then remove from graph *) let 
    (* val _ = no_print_graph graph *)
    val ms = move_related moves
    val not_ms_graph = filter (fn (v,neighbours) => not (mem v ms)) graph
    val ws = map fst (filter (fn (v,ns) => length ns < n) not_ms_graph)
    val ws = filter is_colourable ws
    val ws = sort (fn x => fn y => busy x >= busy y) ws   
    val w = first (K true) ws (* select most busy *)
    val (graph,moves,joined) = delete_vertex w (graph,moves,joined)
    val _ = no_print ("!" ^ term_to_string w ^ " ")
    in build_stack graph moves joined n ((w,"r")::result) end handle HOL_ERR _ =>
    (* coalescing: ?x y. (x,y) IN moves and degree (x UNION y) < n, then combine x,y *) let
    fun combined_degree (x,y) = length (all_distinct (list_find x graph @ list_find y graph))
    val moves2 = filter (fn (x,y) => not (mem x (list_find y graph))) moves
    val moves2 = filter (fn (x,y) => combined_degree (x,y) < n) moves2
    val moves2 = sort (fn (x1,x2) => fn (y1,y2) => busy x1 + busy x2 >= busy y1 + busy y2) moves2
    val moves2 = filter (fn (x,y) => is_colourable x orelse is_colourable y) moves2
    val moves2 = filter (fn (x,y) => not (x = y)) moves2
    val (x,y) = first (fn (x,y) => true) moves2
    val (x,y) = if is_colourable y then (x,y) else (y,x) 
    val (graph,moves,joined) = merge_vertexes x y (graph,moves,joined)
    val _ = no_print (term_to_string x ^ "<--" ^ term_to_string y ^ " ")
    in build_stack graph moves joined n result end handle HOL_ERR _ =>
    (* freezing: removing the move property from an edge *) let
    val ((x,y),moves) = if moves = [] then fail () else (hd moves,tl moves)
    val _ = no_print (term_to_string x ^ "-/-" ^ term_to_string y ^ " ")
    in build_stack graph moves joined n result end handle HOL_ERR _ =>
    (* spilling: select a vertex and spill it *) let
    val ws = map fst graph
    val ws = filter is_colourable ws
    val ws = sort (fn x => fn y => busy x <= busy y) ws   
    val w = if ws = [] then fail () else hd ws (* select least busy *)
    val (graph,moves,joined) = delete_vertex w (graph,moves,joined)
    val _ = no_print ("^" ^ term_to_string w ^ " ")
    in build_stack graph moves joined n ((w,"s")::result) end handle HOL_ERR _ =>
    (rev result, joined)
  val (stack,joined) = build_stack graph moves [] n []
  val coalesced = join_all joined
  fun update x y z i = if x = i then y else z i
  fun select_colour x options c = let
    fun score c = foldr (op +) 0 (map (fn (x,y) => if c x = c y then 1 else 0) moves)
    val xs = map (fn p => (p,score (update x p c))) options
    val result = fst (hd (sort (fn (_,x) => fn (_,y) => y <= x) xs))
    in result end handle HOL_ERR _ => hd options 
    handle Empty => failwith "no more registers"
  fun colour [] (c,r) = c
    | colour ((x,ty)::stack) (c,r) = 
        if ty = "r" then let
          val qs = map snd (filter (fn (v,ns) => coalesced v = x) graph)
          val qs = map coalesced (append_lists qs)
          val zs = filter (fn z => mem z r) qs
          val zs = map c zs
          val new_colour = select_colour x (diff regs zs) c
          in colour stack (update x new_colour c, x::r) end 
        else let
          val qs = map snd (filter (fn (v,ns) => coalesced v = x) graph)
          val qs = map coalesced (append_lists qs)
          val zs = filter (fn z => mem z r) qs
          val zs = map c zs
          fun next_stack i = let
            val z = mk_var("s" ^ int_to_string i,``:word32``) 
            in if mem z zs then next_stack (i+1) else z end  
          val z = next_stack 0
          in colour stack (update x z c, x::r) end 
  val colouring = colour stack (I,r) o join_all joined
  (* check validity of colouring *)
  val g = map (fn (v,ns) => (colouring v, map colouring ns)) graph
  val _ = if filter (fn (x,xs) => mem x xs) g = [] then () 
          else (print "\n\nRegister allocator produced invalid result.\n\n"; fail()) 
  in (colouring) end

(* provide a list representing the frequency of use/def of each variable,
   use/defs inside loops are times constant 16 for each loop nesting. *)
fun frequency ts = let
  fun is_rec (FUN_VAL tm) = not (pairSyntax.is_pair tm)
    | is_rec (FUN_COND (tm,t)) = is_rec t
    | is_rec (FUN_IF (tm,x1,x2)) = is_rec x1 orelse is_rec x2
    | is_rec (FUN_LET (lhs,rhs,t)) = is_rec t
  val fs = map (car o fst) ts
  val vs = all_distinct (append_lists (map (ftree_free_vars o snd) ts))
  val vs = diff vs fs
  fun occ v tm s = s + (if mem v (free_vars tm) then 1 else 0)
  fun count v (FUN_VAL tm) s = occ v tm s
    | count v (FUN_COND (tm,t)) s = count v t (occ v tm s)
    | count v (FUN_IF (tm,x1,x2)) s = count v x1 (count v x2 (occ v tm s))
    | count v (FUN_LET (lhs,rhs,t2)) s = let
        val t = (list_find rhs ts handle HOL_ERR _ => FUN_VAL T)
        val inner_s = count v t 0
        val inner_s = if is_rec t then inner_s * 16 else inner_s
        in count v t2 (occ v lhs (occ v rhs (inner_s + s))) end
  val freq = map (fn v => (v,count v (snd (last ts)) 0)) vs
  in freq end;  

fun REMOVE_REFL_LET_CONV tm = let
  val (x,y) = dest_let tm
  val (v,x) = dest_abs x
  in if v = y then EXPAND_LET_CONV tm else NO_CONV tm end
  handle HOL_ERR _ => NO_CONV tm;

fun REG_ALLOC_CONV n tm = let
  val xs = map (repeat (snd o dest_forall)) (list_dest dest_conj tm)
  val ts = map (fn x => ((cdr o car) x, tm2ftree (cdr x))) xs  
  val graph = clash_graph ts
  val moves = move_assignments ts graph
  val freq = frequency ts
  val is_colourable = is_t_var
  val colouring = iterated_register_coalescing graph moves freq is_colourable n
  fun COLOUR_ALPHA_CONV colouring tm = 
    ALPHA_CONV (colouring (fst (dest_abs tm))) tm handle HOL_ERR _ => NO_CONV tm
  val thi = (BOTTOM_UP_CONV (COLOUR_ALPHA_CONV colouring) THENC
             BOTTOM_UP_CONV REMOVE_REFL_LET_CONV) tm
  in thi end;

(*
val input_tm = ``
  (f1 (a,b,c,d:word32) =
    let x = a + b + c + d in
    let y = a + b + 5w in
      (x,y)) /\
  (f2 (a,b,c) = if a <+ b then (a,b,c) else f2 (a,b-4w,c+5w)) /\
  (f3 (a,b) = 
    let (x,y,z) = f2 (b,a,a-b) in
    let (d,c) = f1 (z,x,y,x+5w) in
      if d = c then (d,c) else (a,b))``  

val input_tm = ``
  (f1 (a:word32,b:word32,c:word32,d:word32) =
     let r2 = a in
     let r3 = b in
     let s1 = r2 + r3 in
     let y = s1 + c in
     let x = r2 in
      (x:word32,y:word32))``  

val n = 30
*)

fun initial_clean tm = let
  val tms = list_dest dest_conj tm
  fun function_name tm = repeat car (fst (dest_eq tm))
  val fs = map function_name tms
  fun add_foralls t = list_mk_forall (diff (free_vars t) fs, t)
  val tms2 = map add_foralls tms
  val tm2 = list_mk_conj tms2
  val goal = mk_imp(tm2,tm)
  val imp = auto_prove "initial_clean" (goal,
              ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC bool_ss []
              THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC bool_ss [])
  in imp end;

fun allocate_registers n input_tm = let
  val imp = initial_clean input_tm
  val tm = (fst o dest_imp o concl) imp
  val cc = COMPILER_UNABBREV_CONV
           THENC FLATTEN_EXPS_CONV
           THENC SSA_CONV THENC COMMON_SUBEXP_CONV
           THENC FIX_CALL_RETURN_VALUES_CONV
           THENC REG_ALLOC_CONV n
  (*
  val tm = (snd o dest_eq o concl) (cc tm)
  *)
  in CONV_RULE ((RATOR_CONV o RAND_CONV) cc) imp end



(*
  for x86: 1. split binary ops into two parts
                let x = y ?? z in  --> let x = y in let x = x ?? z in
              this might lead the reg allocator to coalesce x and y,
              alternatively augment 'moves' to have artificial (x,y) edge
              but many of these are commutative, should there be (x,[y,z]) edge?
           2. assume infinite number of regs, make 
                regs 5,6,7,etc. --> stack locations 0,1,2,3,etc.
              reserve one register for loading when two stack locations are 
              used in the same instruction
*)

(*

val n = 3
val pref_list = [4,3,2,1]
val k = length pref_list
fun t_vars n = if n = 0 then [] else mk_t_var(``:word32``)::t_vars (n-1)
val qs = t_vars k
fun cross xs ys = append_lists (map (fn x => map (fn y => (x,y)) ys) xs)
fun rest [] = []
  | rest ((x,y)::xs) = (x,y)::rest (filter (fn z => not (z = (y,x))) xs)
val edges = rest (filter (fn (x,y) => not (x = y)) (cross qs qs))
val max = foldr (op * ) 1 (map (K 2) edges)
val max2 = max * max
val freq = zip qs pref_list
val is_colourable = is_t_var

fun get_graph i = let
  fun n_filter i [] = []
    | n_filter i (x::xs) = 
        if i mod 2 = 0 then n_filter (i div 2) xs 
        else x :: n_filter (i div 2) xs
  fun adj vs edges = map (fn v => (v,map snd (filter (fn x => fst x = v) edges))) vs
  val ts = n_filter i edges
  val ts = ts @ map (fn (x,y) => (y,x)) ts
  val moves = n_filter (i div max) edges
  in (adj qs ts, moves) end;

fun try_inst i = let
  val (graph,moves) = get_graph i  
  val _ = print (int_to_string i)
  val _ = print "/"
  val _ = print (int_to_string max2)
  val _ = print " "
  val ok = (iterated_register_coalescing graph moves freq is_colourable n; true) 
           handle HOL_ERR _ => false  
  val _ = print "\n"
  in if not ok then print ("\n\nFailed at "^int_to_string i^".\n\n") else
     if i < max2 then try_inst (i+1) else print "\n\nDone!\n\n" end;  

val _ = try_inst 0

*)

end;
