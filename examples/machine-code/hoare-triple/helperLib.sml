structure helperLib :> helperLib =
struct

open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory set_sepTheory progTheory wordsTheory;
open pairSyntax;

type decompiler_tools =
  (* ( derive spec, generate branch, status thm, program counter term ) *)
  (string -> (Thm.thm * int * int option) * (Thm.thm * int * int option) option) *
  (term -> term -> int -> bool -> string * int) * Thm.thm * Abbrev.term

infix \\
val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

(* mechanism for printing *)

val echo_level = ref (1:int);  (* 0 - nothing, 1 - brief, 2 - descriptive, 3+ - verbose *)

fun echo level msg =
  if level <= 0 then () else
  if level <= !echo_level then print msg else ();

fun set_echo level = (echo_level := level);

(* attach a cache to a function from strings, e.g. decode *)

fun cache (f:string->'a) = let
  val dd = ref ((Binarymap.mkDict String.compare) : (String.string, 'a) Binarymap.dict)
  in (fn x => let val y = Binarymap.find(!dd,x)
                  val _ = echo 1 " [cache]"
              in y end
      handle e => let val v = f x
                  val _ = dd := Binarymap.insert(!dd,x,v) in v end) end

val to_lower = let
  fun aux c = if 65 <= ord c andalso ord c <= 90 then chr (ord c + 32) else c
  in implode o map aux o explode end;


(* finding and replacing terms *)

fun all_distinct ([]:term list) = []
  | all_distinct (x::xs) =
      x :: all_distinct (filter (fn y => not (eq x y)) xs)

fun replace_terml p tm = let
  fun aux tm = p tm handle e =>
    if is_comb tm
    then let val (x,y) = dest_comb tm in mk_comb(aux x, aux y) end
    else let val (x,y) = dest_abs tm in mk_abs(x, aux y) end
    handle e => tm
  in aux tm end;

fun find_terml p tm = let
  fun aux tm =
    if p tm then [tm] else
      if is_comb tm then
        let val (x,y) = dest_comb tm in aux x @ aux y end
      else aux (snd (dest_abs tm)) handle e => []
  in all_distinct (aux tm) end

fun find_terml_all p tm = let
  fun aux tm acc =
    let val acc = if p tm then acc @ [tm] else acc in
      if is_comb tm then let val (x,y) = dest_comb tm in aux y (aux x acc) end else
      if is_abs tm then let val (x,y) = dest_abs tm in aux y acc end else acc end
  in all_distinct (aux tm []) end

fun collect_term_of_type ty = find_terml (fn tm => type_of tm = ty);


(* making and destroying terms *)

val car = fst o dest_comb;
val cdr = snd o dest_comb;

fun list_mk f ([]:term list) y = y
  | list_mk f [x] y = x
  | list_mk f (x1::x2::xs) y = f (x1, list_mk f (x2::xs) y)

fun list_dest f tm = let val (x,y) = f tm in list_dest f x @ list_dest f y end handle e => [tm];

fun mk_star (tm1,tm2) = (fst o dest_eq o concl o ISPECL [tm1,tm2]) STAR_COMM
            handle e => (snd o dest_eq o concl o ISPECL [tm2,tm1]) STAR_COMM

fun mk_cond_star (tm1,tm2) = (fst o dest_comb o fst o dest_eq o snd o
  dest_comb o concl o ISPEC tm1 o Q.SPEC `s` o ISPEC tm2) cond_STAR

fun mk_sidecond_star (tm1,tm2) = (fst o dest_comb o fst o dest_eq o snd o
  dest_comb o concl o ISPEC tm1 o Q.SPEC `s` o ISPEC tm2 o
  REWRITE_RULE [GSYM sidecond_def]) cond_STAR

fun mk_sep_hide tm =
  (fst o dest_eq o concl o ISPEC tm) SEP_HIDE_def;

fun mk_sep_exists (v,tm) = let
  val t = (fst o dest_eq o concl) SEP_EXISTS
  val t_ty = (hd o snd o dest_type) (type_of t)
  val tm2 = mk_abs(v,tm)
  in mk_comb(inst (match_type t_ty (type_of tm2)) t, tm2) end;

fun list_mk_star xs ty =
  list_mk (fn (x,y) => mk_star (y,x)) (rev xs) (mk_const("emp",ty))

fun dest_star tm = let
  val (x,z) = dest_comb tm
  val (x,y) = dest_comb x
  in if fst (dest_const x) = "STAR" then (y,z) else fail() end

fun dest_sep_disj tm = let
  val (x,z) = dest_comb tm
  val (x,y) = dest_comb x
  in if fst (dest_const x) = "SEP_DISJ" then (y,z) else fail() end

fun mk_one x = (fst o dest_eq o concl o ISPEC x) one_def
fun dest_one tm = if fst (dest_const (car tm)) = "one" then cdr tm else fail()

fun dest_sep_hide tm = let
  val (x,z) = dest_comb tm
  in if fst (dest_const x) = "SEP_HIDE" then z else fail() end

fun dest_sep_exists tm = let
  val (x,z) = dest_comb tm
  in if fst (dest_const x) = "SEP_EXISTS" then dest_abs z else fail() end  
  
fun dest_spec tm = let
  val (tm,q) = dest_comb tm
  val (tm,c) = dest_comb tm
  val (tm,p) = dest_comb tm
  val (tm,m) = dest_comb tm
  in if fst (dest_const tm) = "SPEC" then (m,p,c,q) else fail() end;

fun is_normal_char c = (* test whether c is 0-9 A-Z a-z or _ *)
  let val v = ord c in     (c = #"_") orelse (48 <= v andalso v <=  57)
    orelse (65 <= v andalso v <=  90) orelse (97 <= v andalso v <= 122) end

fun get_sep_domain tm =
  dest_sep_hide tm handle e => fst (dest_comb tm) handle e => tm;

(* simpsets *)

fun conv2ssfrag name conv pattern = simpLib.SSFRAG{name=NONE,
  ac = [], congs = [],
  convs = [{ name  = name, conv = K (K conv), key = SOME([], pattern), trace = 10 }],
  dprocs = [], filter = NONE, rewrs = []};

fun eval_term_ss tm_name tm = simpLib.conv_ss
  { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K EVAL) };

val sw2sw_ss = eval_term_ss "sw2sw" ``(sw2sw:'a word->'b word) (n2w n)``
val w2w_ss = eval_term_ss "w2w" ``(w2w:'a word->'b word) (n2w n)``

val star_ss = simpLib.ac_ss [(STAR_ASSOC,STAR_COMM)]

val cond_ELIM = prove(
  ``!c c' P . (cond c * cond c' = cond (c /\ c'):'a set -> bool) /\
              (P * cond c * cond c' = P * cond (c /\ c'):'a set -> bool)``,
  REWRITE_TAC [GSYM STAR_ASSOC,SEP_CLAUSES]);

val cond_MOVE = prove(
  ``!c P Q. (cond c * P = P * (cond c) :'a set -> bool) /\
            (P * cond c * Q = P * Q * cond c)``,
  SIMP_TAC (bool_ss++star_ss) []);

val SEP_cond_CONV =
  REWRITE_CONV [STAR_ASSOC] THENC
  REPEATC (REWRITE_CONV [cond_ELIM] THENC ONCE_REWRITE_CONV [cond_MOVE]) THENC
  REWRITE_CONV [GSYM CONJ_ASSOC];

val sep_cond_ss = conv2ssfrag "sep_cond_ss" SEP_cond_CONV ``x * (y:'a set -> bool)``;

(* conversions *)

fun MOVE_STAR_CONV tm2 tm1 = prove(mk_eq(tm1,tm2),
  SIMP_TAC (bool_ss++star_ss) [SEP_CLAUSES]);

fun MOVE_STAR_REWRITE_CONV thms tm2 tm1 = prove(mk_eq(tm1,tm2),
  SIMP_TAC (bool_ss++star_ss) (SEP_CLAUSES::thms));

fun MOVE_OUT_CONV target tm = let
  fun take_drop_until p ys [] = fail()
    | take_drop_until p ys (x::xs) =
        if p x then (rev ys,x,xs) else take_drop_until p (x::ys) xs
  val xs = list_dest dest_star tm
  fun is_match x y = eq x (get_sep_domain y)
  val (s1,y,s2) = take_drop_until (is_match target) [] xs
  val result = list_mk_star (s1 @ s2 @ [y]) (type_of tm)
  in prove(mk_eq(tm,result),SIMP_TAC bool_ss [AC STAR_ASSOC STAR_COMM]) end
  handle e => ALL_CONV tm;

fun STAR_REVERSE_CONV tm = let
  val xs = list_dest dest_star tm
  val result = list_mk_star (rev xs) (type_of tm)
  in prove(mk_eq(tm,result),SIMP_TAC bool_ss [AC STAR_ASSOC STAR_COMM]) end
  handle e => ALL_CONV tm;

val PRE_CONV = RATOR_CONV o RATOR_CONV o RAND_CONV
val POST_CONV = RAND_CONV

val FIX_WORD32_ARITH_CONV = DEPTH_CONV (fn tm => let
  val (i,j) = match_term ((fst o dest_eq o concl o SPEC_ALL) word32_add_n2w) tm
  val th1 = INST i (INST_TYPE j (SPEC_ALL word32_add_n2w))
  val th1 = CONV_RULE ((RAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL) th1
  val th1 = CONV_RULE ((RAND_CONV o RAND_CONV o RAND_CONV) EVAL) (REWRITE_RULE [] th1)
  in th1 end handle e => ALL_CONV tm);

fun FORCE_PBETA_CONV tm = let
  val (tm1,tm2) = dest_comb tm
  val vs = fst (dest_pabs tm1)
  fun expand_pair_conv tm = ISPEC tm (GSYM pairTheory.PAIR)
  fun get_conv vs = let
    val (x,y) = dest_pair vs
    in expand_pair_conv THENC (RAND_CONV (get_conv y)) end
    handle e => ALL_CONV
  in (RAND_CONV (get_conv vs) THENC PairRules.PBETA_CONV) tm end;

val pbeta_ss = conv2ssfrag "pbeta_conv" FORCE_PBETA_CONV ``(f:'a # 'b->'c) x``;

fun INST_SPEC spec_th abs_th = let
  val abs_th = SPEC_ALL abs_th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [progTheory.SPEC_MOVE_COND] spec_th
  val tm = (fst o dest_imp o concl) th
  val tx = find_term (can (fn t => match_term t tm)) (concl abs_th)
  val (i,t) = match_term tx tm
  val thi = INST i (INST_TYPE t abs_th)
  val th = MP th (el 1 (CONJUNCTS (UNDISCH thi)))
  val thi = el 2 (CONJUNCTS (UNDISCH thi))
  val th = CONV_RULE (UNBETA_CONV ((fst o dest_eq o concl) thi) THENC RAND_CONV (fn x => thi)) th
  val th = SIMP_RULE std_ss [] th
  val th = REWRITE_RULE [GSYM progTheory.SPEC_MOVE_COND] (DISCH_ALL th)
  in th end;

val EQ_IMP_IMP = prove(``(x = y) ==> x ==> y``,STRIP_TAC THEN ASM_REWRITE_TAC [])
fun parse_in_thm q th = Parse.parse_in_context (free_varsl (concl th::hyp th)) q;
val EXISTS_PRE_LEMMA = MATCH_MP EQ_IMP_IMP (SPEC_ALL progTheory.SPEC_PRE_EXISTS);
fun EXISTS_PRE var th = let
  val v = parse_in_thm var th
  val th = CONV_RULE (PRE_CONV (UNBETA_CONV v)) th
  val th = MATCH_MP EXISTS_PRE_LEMMA (GEN v th)
  val th = CONV_RULE (PRE_CONV (RAND_CONV (ALPHA_CONV v))) th
  in BETA_RULE th end;

val word_patterns = [
  ``(n2w n ?? n2w m):('a word)``,``(n2w n !! n2w m):('a word)``,``(n2w n && n2w m):('a word)``,
  ``(n2w n + n2w m):('a word)``, ``(n2w n - n2w m):('a word)``, ``(n2w n * n2w m):('a word)``,
  ``n2w n < (n2w m):('a word)``, ``n2w n <= (n2w m):('a word)``, ``n2w n > (n2w m):('a word)``, ``n2w n >= (n2w m):('a word)``,
  ``n2w n <+ (n2w m):('a word)``, ``n2w n <=+ (n2w m):('a word)``, ``n2w n >+ (n2w m):('a word)``, ``n2w n >=+ (n2w m):('a word)``,
  ``(n2w n):('a word) << m``, ``(n2w n):('a word) >> m``, ``(n2w n):('a word) >>> m``, ``~(n2w n):('a word)``,
  ``w2n ((n2w n):'a word)``];

fun EVAL_ANY_MATCH_CONV patterns tm = let
  fun aux f [] = []
    | aux f (x::xs) = f x :: aux f xs handle _ => aux f xs
  val x = hd (aux (fn x => find_term (can (match_term x)) tm) patterns)
  in (PURE_REWRITE_CONV [EVAL x] THENC EVAL_ANY_MATCH_CONV patterns) tm end
  handle e => ALL_CONV tm;

fun SEP_EXISTS_AC_CONV tm = let
  val vs = list_dest dest_sep_exists tm
  val (vs,p) = (butlast vs, last vs)
  val ws = sort (fn x => fn y => term_to_string x <= term_to_string y) vs   
  val tm2 = foldr mk_sep_exists p ws
  val goal = mk_eq(tm,tm2)
  fun AUTO_EXISTS_TAC (gs,goal) = EXISTS_TAC (fst (dest_exists goal)) (gs,goal)
  val th = prove(goal,
    REWRITE_TAC [CONV_RULE ((QUANT_CONV o QUANT_CONV o RAND_CONV o RAND_CONV) 
      (ALPHA_CONV (genvar(``:'a``)))) FUN_EQ_THM]
    THEN SIMP_TAC bool_ss [SEP_EXISTS_THM]
    THEN REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
    THEN REPEAT AUTO_EXISTS_TAC THEN ASM_SIMP_TAC std_ss [] 
    THEN (fn x => hd []))
  in th end handle Empty => fail();


(* tree to term and back *)

datatype ftree_type =
    FUN_IF of term * ftree_type * ftree_type
  | FUN_LET of term * term * ftree_type
  | FUN_COND of term * ftree_type
  | FUN_VAL of term;

fun ftree_type_eq (FUN_IF(t1,aty1,bty1)) (FUN_IF(t2,aty2,bty2)) =
      eq t1 t2 andalso ftree_type_eq aty1 aty2 andalso ftree_type_eq bty1 bty2
  | ftree_type_eq (FUN_LET(at1,bt1,fty1)) (FUN_LET(at2,bt2,fty2)) = 
      eq at1 at2 andalso eq bt1 bt2 andalso ftree_type_eq fty1 fty2
  | ftree_type_eq (FUN_VAL t1) (FUN_VAL t2) = eq t1 t2
  | ftree_type_eq (FUN_COND(t1,aty1)) (FUN_COND(t2,aty2)) =
      eq t1 t2 andalso ftree_type_eq aty1 aty2
  | ftree_type_eq _ _ = false;

fun tm2ftree tm = let
  val (b,x,y) = dest_cond tm
  in FUN_IF (b,tm2ftree x,tm2ftree y) end handle e => let
  val (x,y) = dest_anylet tm
  val z = tm2ftree y
  val v = mk_var("cond",``:bool``)
  fun g((x,y),z) = if not (eq x v) then FUN_LET (x,y,z) else
    if (eq (fst(dest_conj(y))) v handle e => false) then FUN_COND (cdr y,z) else FUN_COND (y,z)
  in foldr g z x end handle e => FUN_VAL tm;

fun ftree2tm (FUN_VAL tm) = tm
  | ftree2tm (FUN_IF (tm,x,y)) = mk_cond(tm, ftree2tm x, ftree2tm y)
  | ftree2tm (FUN_LET (tm,tn,x)) = mk_anylet([(tm,tn)],ftree2tm x)
  | ftree2tm (FUN_COND (tm,x)) = let
      val v = mk_var("cond",``:bool``)
      in mk_anylet([(v,mk_conj(v,tm))],ftree2tm x) end


(* instantiate theorem *)

fun MATCH_INST th tm = let
  val vs = butlast (list_dest dest_forall (concl th))
  val thi = SPEC_ALL th
  val tm1 = find_term (fn t => can (match_term t) tm) (concl thi)
  val (i,s) = match_term tm1 tm
  val thi = INST i (INST_TYPE s thi)
  val ws = filter (fn t => eq t (subst i t)) vs
  in GENL ws thi end;


(* rewriting for separation logic *)

fun generic_star_match fixed_vars tm1 tm2 = let
  val xs = list_dest dest_star tm1 
  val ys = list_dest dest_star tm2
  fun list_mk_set [] = empty_varset
    | list_mk_set (x::xs) = HOLset.add(list_mk_set xs,x)
  val match = match_terml [] (list_mk_set fixed_vars)
  fun app [] = [] | app (x::xs) = x @ app xs
  fun find_matches x [] zs = []
    | find_matches x (y::ys) zs =
        if can (match x) y 
        then (y,ys @ zs) :: find_matches x ys (y::zs) 
        else find_matches x ys (y::zs) 
  fun alternatives [] ys = [([],ys)]
    | alternatives (x::xs) ys = let
        val al = find_matches x ys []        
        in app (map (fn (z,zs) => map (fn (r,rs) => ((x,z)::r,rs)) (alternatives xs zs)) al) end       
  fun frame_var tm = is_var tm andalso not (mem tm fixed_vars)
  val ts = alternatives (filter (not o frame_var) xs) ys
  val ts = map (fn (x,y) => (x,list_mk_star y (type_of (fst (hd x))))) ts
  fun terms ([],x) = ((hd (filter frame_var xs),x) handle Empty => (list_mk_star [] (type_of (car tm1)),x))
    | terms (((y,z)::ys),x) = let
        val (y2,z2) = terms (ys,x)
        in (mk_star(y,y2),mk_star(z,z2)) end 
  fun try_each f [] = fail()
    | try_each f (x::xs) = f x handle HOL_ERR _ => try_each f xs
  fun g (x,y) = (x,y,fst (match x y))
  val (x,y,s) = try_each (g o terms) ts
  fun redexes xs = map (fn {redex = x,residue = y} => x) xs  
  val result = s @ map (fn x => x |-> x) (filter (fn y => not (mem y (redexes s))) (free_vars x))
  val rs = redexes result
  val result = result @ map (fn y => y |-> list_mk_star [] (type_of y)) 
                    (filter (fn x => not (mem x rs)) (filter frame_var xs))
  in result end handle Empty => fail();

fun BASIC_SEP_REWRITE_RULE rw th = let
  val (p,q) = dest_eq (concl rw)
  val frame = genvar(type_of p)
  val imp = PURE_ONCE_REWRITE_CONV [rw] (mk_star(frame,p))
  val lhs = fst (dest_eq (concl imp))
  fun foo th = let
    val t = find_term (can (generic_star_match [] lhs)) (concl th)
    val s = generic_star_match [] lhs t
    val lm = (SIMP_CONV (bool_ss++sep_cond_ss) [] THENC 
              SIMP_CONV (bool_ss++star_ss) [SEP_CLAUSES,AC CONJ_ASSOC CONJ_COMM]) 
               (mk_eq(t,subst s lhs))
    val _ = if can (match_term ``x = T``) (concl lm) then () else fail()
    val lm = CONV_RULE (POST_CONV (PURE_ONCE_REWRITE_CONV [rw])) (RW [] lm)
    in foo (RW [STAR_ASSOC] (RW [lm] th)) end handle HOL_ERR _ => th   
  in foo th end;   

fun EXISTS_SEP_REWRITE_RULE rw th = let (* possibly fragile *)
  val (p,q) = dest_eq (concl (SPEC_ALL rw))
  val frame = genvar(type_of p)
  val vs = list_dest dest_sep_exists p
  val lhs = mk_star(last vs,frame)
  val vs = butlast vs
  fun find_exists_match lhs tm = let
    val (v,t) = dest_sep_exists tm
    val vs = list_dest dest_sep_exists tm
    in (butlast vs,last vs,generic_star_match [] lhs (last vs)) end
  fun find_term_and_apply f tm = f (find_term (can f) tm)
  fun foo th = let
    val (ws,tm,s) = find_term_and_apply (find_exists_match lhs) (concl th)
    val (t,t2) = (dest_eq (concl (SPEC_ALL rw)))
    val zs = list_dest dest_sep_exists t
    val (zs,z) = (butlast zs,list_dest dest_star (last zs))
    val xs = list_dest dest_star tm
    val ys = filter (fn y => not (mem y (map (subst s) z))) xs
    val t3 = foldr mk_sep_exists (subst s (list_mk_star z (type_of frame))) (map (subst s) zs)
    val goal = foldr mk_sep_exists (list_mk_star (t3::ys) (type_of frame)) ws
    val goal = mk_eq(foldr mk_sep_exists tm ws,goal)    
    val lemma = prove(goal,
      SIMP_TAC std_ss [GSYM rw]
      THEN SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES]
      THEN CONV_TAC (BINOP_CONV SEP_EXISTS_AC_CONV)
      THEN SIMP_TAC (std_ss++star_ss) [AC CONJ_ASSOC CONJ_COMM])
    val lemma = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [rw] 
                  THENC SIMP_CONV std_ss [SEP_CLAUSES])) lemma
    in foo (RW1 [lemma] th) end handle HOL_ERR _ => th
  in foo th end;


(* introducing SEP_EXISTS into pre and possibly also post *)

val SEP_IMP_EXISTS = prove(
  ``!(p :'a -> 'b set -> bool) x. SEP_IMP (p x) (SEP_EXISTS x. p x)``,
  SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS]
  THEN REPEAT STRIP_TAC THEN Q.EXISTS_TAC `x` THEN ASM_REWRITE_TAC []);

fun SEP_EXISTS_POST_RULE tm th = let
  val (_,_,_,q) = dest_spec (concl th)
  val thj = SPEC tm (ISPEC (mk_abs(tm,q)) SEP_IMP_EXISTS)
  val thj = CONV_RULE ((RAND_CONV o RAND_CONV) (ALPHA_CONV tm)) thj
  val thj = CONV_RULE (DEPTH_CONV BETA_CONV) thj
  val thi = SPEC ((cdr o concl) thj) (MATCH_MP SPEC_WEAKEN th)
  in MP thi thj end;

fun SEP_EXISTS_PRE_RULE tm th = let
  val (_,p,_,q) = dest_spec (concl th)
  val thi = if mem tm (free_vars q) then SEP_EXISTS_POST_RULE tm th else th 
  val thi = CONV_RULE (PRE_CONV (UNBETA_CONV tm)) thi
  val thi = SIMP_RULE bool_ss [SPEC_PRE_EXISTS] (GEN tm thi)
  in thi end;

fun SEP_EXISTS_ELIM_CONV tm = let
  val tm2 = (snd o dest_eq o concl o QCONV (SIMP_CONV bool_ss [SEP_CLAUSES])) tm  
  val _ = dest_sep_exists tm2
  val vs = list_dest dest_sep_exists tm2
  val (v,vs,p) = (hd vs,tl (butlast vs), last vs)
  val xs = filter (fn tm => mem v (free_vars tm)) (list_dest dest_star p)
  val _ = if length xs = 1 then () else fail()
  val x = hd xs
  val (f,x) = dest_comb x
  val _ = if x = v then () else fail()
  val _ = if mem v (free_vars f) then fail() else ()
  val tm3 = subst [hd xs |-> mk_sep_hide f] p
  val tm3 = foldr mk_sep_exists tm3 vs
  val goal = mk_eq(tm2,tm3)
  val thi = CONV_RULE ((RAND_CONV o RAND_CONV) (ALPHA_CONV x)) (ISPEC f SEP_HIDE_def)
  val th = prove(goal,
    SIMP_TAC std_ss [SEP_CLAUSES,thi]
    THEN CONV_TAC (RAND_CONV SEP_EXISTS_AC_CONV)
    THEN CONV_TAC ((RATOR_CONV o RAND_CONV) SEP_EXISTS_AC_CONV)
    THEN ASM_SIMP_TAC std_ss []
    THEN (fn x => hd []))
  in (SIMP_CONV bool_ss [SEP_CLAUSES] THENC (fn _ => th)) tm end 
  handle Empty => fail();
    
fun SEP_EXISTS_ELIM_RULE th = let
  val th = SIMP_RULE bool_ss [SEP_CLAUSES] th
  in CONV_RULE (DEPTH_CONV SEP_EXISTS_ELIM_CONV) th end;


(* hiding variables in SPEC theorems *)

(* expects c to produce SEP_IMP tm tm2 from tm *)
fun SEP_IMP_WEAKEN c tm = let
  val (p,q) = dest_star tm
  in MATCH_MP SEP_IMP_STAR (CONJ (SEP_IMP_WEAKEN c p) (SEP_IMP_WEAKEN c q)) end
  handle HOL_ERR _ => let 
  val (p,q) = dest_sep_disj tm
  in MATCH_MP SEP_IMP_DISJ (CONJ (SEP_IMP_WEAKEN c p) (SEP_IMP_WEAKEN c q)) end
  handle HOL_ERR _ => let 
  val (v,x) = dest_sep_exists tm
  val imp = SEP_IMP_WEAKEN c x
  val imp = GEN v (CONV_RULE (BINOP_CONV (UNBETA_CONV v)) imp)
  in MATCH_MP SEP_IMP_EXISTS_EXISTS imp end
  handle HOL_ERR _ => c tm handle HOL_ERR _ => ISPEC tm SEP_IMP_REFL; 

val LIST_HIDE_POST_LEMMA = 
  (RW [AND_IMP_INTRO] o DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL) SPEC_WEAKEN  
fun LIST_HIDE_POST_RULE tms th = let
  fun HIDE_INTRO format_list tm = let
    val (x,y) = dest_comb tm
    in if mem x format_list 
       then ISPEC y (ISPEC x SEP_IMP_SEP_HIDE) else fail() end
  val (_,_,_,q) = dest_spec (concl th)
  val imp = SEP_IMP_WEAKEN (HIDE_INTRO tms) q
  in MATCH_MP LIST_HIDE_POST_LEMMA (CONJ th imp) end
  
fun HIDE_POST_RULE tm th = LIST_HIDE_POST_RULE [tm] th

val EQ_IMP_IMP = Q.SPECL [`p`,`q`] quotientTheory.EQ_IMPLIES;

val INC_ASSUM = (SPEC (genvar ``:bool``) o prove)(
  ``!t p q. (p ==> q) ==> ((t ==> p) ==> (t ==> q))``,
  REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);

fun DISCH_ALL_AS_SINGLE_IMP th = let
  val th = RW [AND_IMP_INTRO] (DISCH_ALL th)
  in if is_imp (concl th) then th else DISCH ``T`` th end

fun A_MATCH_MP th1 th2 =
  (UNDISCH_ALL o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO,AND_CLAUSES])
  (MATCH_MP (MATCH_MP INC_ASSUM (SPEC_ALL th1)) (DISCH_ALL_AS_SINGLE_IMP th2));

fun SPEC_FRAME_RULE th frame =
  SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)

fun HIDE_PRE_RULE tm th = let
  val (_,p,_,_) = dest_spec (concl th)
  val finder = find_term (fn x => fst (dest_comb x) = tm handle HOL_ERR _ => false)
  in SEP_EXISTS_ELIM_RULE (SEP_EXISTS_PRE_RULE (cdr (finder p)) th) end
      
fun LIST_HIDE_PRE_RULE [] th = th
  | LIST_HIDE_PRE_RULE (x::xs) th = LIST_HIDE_PRE_RULE xs (HIDE_PRE_RULE x th handle HOL_ERR _ => th)

val UNHIDE_PRE1 = (MATCH_MP EQ_IMP_IMP (SPEC_ALL (GSYM SPEC_HIDE_PRE)));
val UNHIDE_PRE2 = (MATCH_MP EQ_IMP_IMP
  (SPEC_ALL (RW [SEP_CLAUSES] (Q.SPECL [`x`,`emp`] (GSYM SPEC_HIDE_PRE)))));

fun UNHIDE_PRE_RULE tm th = let
  val th = CONV_RULE (PRE_CONV (MOVE_OUT_CONV (car tm) THENC REWRITE_CONV [STAR_ASSOC])) th
  val _ = find_term (fn x => x = car tm) (car (concl th))
  val th = (A_MATCH_MP UNHIDE_PRE1 th handle e => A_MATCH_MP UNHIDE_PRE2 th)
  val th = SPEC (cdr tm) th
  in th end;

fun get_model_status_list th = let
  val (x,y) = (dest_eq o concl o SPEC_ALL) th
  in ((map dest_sep_hide o list_dest dest_star) y,x) end handle e => ([],T)

fun HIDE_STATUS_RULE in_post hide_th th = let
  val (xs,s) = get_model_status_list hide_th
  val th = RW [hide_th,STAR_ASSOC] th
  val (_,p,_,_) = dest_spec (concl th)
  val ys = filter (fn x => not (can (find_term (fn y => x = y)) p)) xs
  val ys = if ys = xs then [] else ys 
  val ys = if can (find_term (fn x => s = x)) p then [] else map mk_sep_hide ys
  val th = SPEC_FRAME_RULE th (list_mk_star ys (type_of s))
  val th = SIMP_RULE std_ss [SEP_CLAUSES,STAR_ASSOC] th
  val th = if in_post then LIST_HIDE_POST_RULE xs th else th handle HOL_ERR _ => th 
  val th = LIST_HIDE_PRE_RULE xs th
  val th = BASIC_SEP_REWRITE_RULE (GSYM hide_th) th
  (* check result *)
  val (_,p,_,_) = dest_spec (concl th)
  val ps = (list_dest dest_star o last o list_dest dest_sep_exists) p
  val error = 1 < (length o filter (fn t => t = s)) ps
              orelse not (intersect xs (map get_sep_domain ps) = [])
  val _ = if error then (print "\n\nHIDE_STATUS_RULE failed on theorem:\n\n"; 
                         print_thm th; print "\n\n"; fail()) else ()
  in th end;

fun HIDE_PRE_STATUS_RULE hide_th th = HIDE_STATUS_RULE false hide_th th


(* rules for modifying pre and post *)

fun SPEC_STRENGTHEN_RULE th pre = let
  val th = SPEC pre (MATCH_MP progTheory.SPEC_STRENGTHEN th)
  val goal = (fst o dest_imp o concl) th
  in (th,goal) end;

fun SPEC_WEAKEN_RULE th post = let
  val th = SPEC post (MATCH_MP progTheory.SPEC_WEAKEN th)
  val goal = (fst o dest_imp o concl) th
  in (th,goal) end;

fun SPEC_BOOL_FRAME_RULE th frame = let
  val th = MATCH_MP progTheory.SPEC_FRAME th
  val th = Q.SPEC `cond boolean_variable_name` th
  val th = INST [mk_var("boolean_variable_name",``:bool``) |-> frame] th
  in th end

fun SEP_REWRITE_RULE rws th = let 
  val rws = map (MATCH_MP SEP_REWRITE_THM) rws
  val th = SIMP_RULE std_ss (GSYM STAR_ASSOC::rws) th 
  val th = SIMP_RULE std_ss (STAR_ASSOC::rws) th 
  in th end;

(* a rule for composing a list of SPEC theorems *)

fun remove_primes th = let
  fun last s = substring(s,size s-1,1)
  fun delete_last_prime s = if last s = "'" then substring(s,0,size(s)-1) else fail()
  fun foo [] ys i = i
    | foo (x::xs) ys i = let
      val name = (fst o dest_var) x
      val new_name = repeat delete_last_prime name
      in if name = new_name then foo xs (x::ys) i else let
        val new_var = mk_var(new_name,type_of x)
        in foo xs (new_var::ys) ((x |-> new_var) :: i) end end
  val i = foo (free_varsl (concl th :: hyp th)) [] []
  in INST i th end

fun spec_post_and_pre th1 th2 = let
  val (_,_,_,q) = dest_spec (concl th1)
  val (_,p,_,_) = dest_spec (concl th2)
  in (list_dest dest_star q, list_dest dest_star p, type_of q) end;

fun replace_abbrev_vars tm = let
  fun f v = v |-> mk_var((Substring.string o hd o tl o Substring.tokens (fn x => x = #"@") o
                    Substring.full o fst o dest_var) v, type_of v) handle e => v |-> v
  in subst (map f (free_vars tm)) tm end

fun match_and_partition q p = let
  fun get_match_term tm = replace_abbrev_vars (get_sep_domain tm)
  fun mm x y = get_match_term x = get_match_term y
  fun fetch_match x [] zs = fail()
    | fetch_match x (y::ys) zs =
        if mm x y then (y, rev zs @ ys) else fetch_match x ys (y::zs)
  fun partition [] ys (xs1,xs2,ys1) = (rev xs1, rev xs2, rev ys1, ys)
    | partition (x::xs) ys (xs1,xs2,ys1) =
        let val (y,zs) = fetch_match x ys [] in
          partition xs zs (x::xs1, xs2, y::ys1)
        end handle e =>
          partition xs ys (xs1, x::xs2, ys1)
  in partition q p ([],[],[]) end;  

val AND_CLAUSES2 = CONJ AND_CLAUSES (prove(``(T ==> b) = b``,SIMP_TAC std_ss []))

fun find_composition1 th1 th2 = let
  val (q,p,ty) = spec_post_and_pre th1 th2
  val (xs1,xs2,ys1,ys2) = match_and_partition q p
  val tm1 = mk_star (list_mk_star xs1 ty, list_mk_star xs2 ty)
  val tm2 = mk_star (list_mk_star ys1 ty, list_mk_star ys2 ty)
  val th1 = CONV_RULE (POST_CONV (MOVE_STAR_CONV tm1)) th1
  val th2 = CONV_RULE (PRE_CONV (MOVE_STAR_CONV tm2)) th2
  val th = MATCH_MP SPEC_FRAME_COMPOSE (DISCH_ALL_AS_SINGLE_IMP th2)
  val th = MATCH_MP th (DISCH_ALL_AS_SINGLE_IMP th1)
  val th = UNDISCH_ALL (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO,AND_CLAUSES2] th)
  val th = SIMP_RULE std_ss [pred_setTheory.INSERT_UNION_EQ,pred_setTheory.UNION_EMPTY,
             word_arith_lemma1,word_arith_lemma2,word_arith_lemma3,word_arith_lemma4,
             SEP_CLAUSES,pred_setTheory.UNION_IDEMPOT] th
  in remove_primes th end;

fun find_composition2 th1 th2 = let
  val (q,p,ty) = spec_post_and_pre th1 th2
  val post_not_hidden = map get_sep_domain (filter (not o can dest_sep_hide) q)
  val pre_not_hidden  = map get_sep_domain (filter (not o can dest_sep_hide) p)
  fun f (d:term,(zs,to_be_hidden)) =
    if not (can dest_sep_hide d) then (zs,to_be_hidden) else
      (zs,filter (fn x => get_sep_domain d = x) zs @ to_be_hidden)
  val hide_from_post = snd (foldr f (post_not_hidden,[]) p)
  val hide_from_pre  = snd (foldr f (pre_not_hidden,[]) q)
  val th1 = foldr (uncurry HIDE_POST_RULE) th1 hide_from_post
  val th2 = foldr (uncurry HIDE_PRE_RULE) th2 hide_from_pre
  in find_composition1 th1 th2 end;

(*
  val th1o = th1
  val th2o = th2

  val th1 = th1o
  val th2 = th2o
*)

fun find_composition3 th1 th2 = let
  val (_,_,_,q) = dest_spec (concl th1)
  val (_,p,_,_) = dest_spec (concl th2)
  in if not (can (find_term (can dest_sep_exists)) (mk_star(p,q)))
     then find_composition2 th1 th2 else let
     val f = SIMP_CONV bool_ss [SEP_CLAUSES,SEP_HIDE_def] THENC REWRITE_CONV [STAR_ASSOC]
     val th1 = CONV_RULE (POST_CONV f) th1
     val th2 = CONV_RULE (PRE_CONV f) th2
     val th2 = SPEC_ALL (SIMP_RULE bool_ss [GSYM SPEC_PRE_EXISTS] th2)
     (* first level match *)
     val (_,_,_,q) = dest_spec (concl th1)
     val (_,p,_,_) = dest_spec (concl th2)
     val vs = list_dest dest_sep_exists q
     val (vs,q) = (butlast vs,last vs)    
     val (xs1,xs2,ys1,ys2) = match_and_partition (list_dest dest_star q) (list_dest dest_star p)
     val ty = type_of q
     val (m,i) = match_term (list_mk_star ys1 ty) (list_mk_star xs1 ty)
     val th2 = INST m (INST_TYPE i th2)
     (* second level match *)
     val (_,_,_,q) = dest_spec (concl th1)
     val (_,p,_,_) = dest_spec (concl th2)
     val vs = list_dest dest_sep_exists q
     val (vs,q) = (butlast vs,last vs)    
     val (xs1,xs2,ys1,ys2) = match_and_partition (list_dest dest_star q) (list_dest dest_star p)
     val ty = type_of q
     val (m,i) = match_term (list_mk_star ys1 ty) (list_mk_star xs1 ty)
     val th2 = INST m (INST_TYPE i th2)
     (* do rest *)
     val th2 = SPEC (list_mk_star xs2 ty) (MATCH_MP SPEC_FRAME th2) 
     val th1 = SPEC (subst m (inst i (list_mk_star ys2 ty))) (MATCH_MP SPEC_FRAME th1) 
     val th1 = CONV_RULE (POST_CONV f) th1
     val th2 = CONV_RULE (PRE_CONV f) th2
     val th2 = foldr (uncurry SEP_EXISTS_PRE_RULE) th2 vs     
     val lemma = RW [SEP_CLAUSES] (Q.INST [`q'`|->`emp`,`p'`|->`emp`] (SPEC_ALL SPEC_FRAME_COMPOSE))
     fun g c = DISCH_ALL_AS_SINGLE_IMP o CONV_RULE (c (SIMP_CONV (bool_ss++star_ss) []))
     val thi = MATCH_MP lemma (g PRE_CONV th2)
     val thi = MATCH_MP thi (g POST_CONV th1)
     val thi = UNDISCH_ALL (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO,AND_CLAUSES2] thi)
     val thi = SIMP_RULE std_ss [pred_setTheory.INSERT_UNION_EQ,pred_setTheory.UNION_EMPTY,
             word_arith_lemma1,word_arith_lemma2,word_arith_lemma3,word_arith_lemma4,
             SEP_CLAUSES,pred_setTheory.UNION_IDEMPOT,STAR_ASSOC] thi
     val (_,p,c,q) = dest_spec (concl thi)
     val vs = free_vars c @ free_vars q @ foldr (uncurry append) [] (map free_vars (hyp thi))
     val vs = filter (fn x => not (mem x vs)) (free_vars p)
     val thi = SIMP_RULE bool_ss [SPEC_PRE_EXISTS] (GENL vs thi)
     val thi = SEP_EXISTS_ELIM_RULE thi
     in remove_primes thi end end;

fun SPEC_COMPOSE_RULE [] = fail()
  | SPEC_COMPOSE_RULE [th] = th
  | SPEC_COMPOSE_RULE (th1::th2::thms) =
      SPEC_COMPOSE_RULE ((find_composition3 th1 th2)::thms)


(* tactics *)

fun SPEC_PROVE_TAC thms (hs,goal) = let
  val (m,p,_,q) = dest_spec goal
  val th1 = Q.SPEC `{}` (ISPECL [m,p] SPEC_REFL)
  val th2 = Q.SPEC `{}` (ISPECL [m,q] SPEC_REFL)
  val ts = [th1] @ thms @ [th2]
  fun move_cond th =
    UNDISCH_ALL (SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND] th)
  val th = SPEC_COMPOSE_RULE (map move_cond ts)
  val th = REWRITE_RULE [AND_IMP_INTRO] (DISCH_ALL th)
  val th = REWRITE_RULE [GSYM SPEC_MOVE_COND] th
  val th = MATCH_MP SPEC_STRENGTHEN_WEAKEN th
  in (MATCH_MP_TAC th
      THEN SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_MOVE_COND,SEP_CLAUSES]
      THEN SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL]
      THEN ASM_SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL,SEP_CLAUSES]) (hs,goal) end;

val ALIGNED_TAC = let
  val ALIGNED_CONV =
    ONCE_REWRITE_CONV [ALIGNED_MOD_4] THENC
    SIMP_CONV std_ss [WORD_ADD_0,WORD_SUB_RZERO]
  val ALIGNED_convdata = {name = "ALIGNED_CONV",
    trace = 2, key = SOME ([],``ALIGNED a``),
    conv = K (K ALIGNED_CONV)}:simpfrag.convdata
  val ALIGNED_ss = simpLib.conv_ss ALIGNED_convdata
  in FULL_SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_ADDR32,ALIGNED_n2w]
     THEN FULL_SIMP_TAC (bool_ss++ALIGNED_ss) [ALIGNED_INTRO] end;

val SEP_READ_TAC = let
  fun aux (hs,gs) = let
    val (v,n) = dest_exists gs
    val rhs = cdr n
    val lhs = (cdr o car o car) n
    val xs = filter (fn x => eq (cdr x) rhs handle e => false) hs
    val ys = map (fn x => ((list_dest dest_star o car) x, x)) xs
    val (qs,q) = hd (filter (fn (x,y) => op_mem eq lhs x) ys)
    val zs = filter (fn x => not (eq x lhs)) qs
    val p = list_mk_star zs (type_of lhs)
    in (EXISTS_TAC p THEN PAT_ASSUM q MP_TAC
        THEN SIMP_TAC (std_ss++star_ss) []) (hs,gs) end
  fun dest_pair_one tm = let
    val (x,y) = dest_comb tm
    val _ = if (fst (dest_const x) = "one") then () else fail()
    in dest_pair y end
  fun prepare_tac (hs,gs) = let
    val (x,y) = pred_setSyntax.dest_in gs
    fun extract tm = let
      val (p,f) = dest_comb tm
      val ps = filter (can dest_pair_one) (list_dest dest_star p)
      val z = (snd o hd) (filter (fn (a,b) => eq x a) (map dest_pair_one ps))
      in mk_eq(mk_comb((fst o dest_pair o cdr) f,x),z) end
    val tm = extract (hd (filter (can extract) hs))
    val thi = prove(mk_imp(mk_conj(tm,gs),gs),REPEAT STRIP_TAC)
    in MATCH_MP_TAC thi (hs,gs) end handle e => let
    val (x,y) = dest_comb (fst (dest_eq gs))
    fun extract tm = let
      val (p,f) = dest_comb tm
      val ps = filter (can dest_pair_one) (list_dest dest_star p)
      val z = (snd o hd) (filter (fn (a,b) => eq y a) (map dest_pair_one ps))
      in pred_setSyntax.mk_in(y,cdr (cdr f)) end
    val tm = extract (hd (filter (can extract) hs))
    val thi = prove(mk_imp(mk_conj(gs,tm),gs),REPEAT STRIP_TAC)
    in MATCH_MP_TAC thi (hs,gs) end
  in (REPEAT STRIP_TAC THEN prepare_tac THEN
      MATCH_MP_TAC read_fun2set THEN aux) end handle e => NO_TAC;

fun list_dest_right f tm = let val (x,y) = f tm in x :: list_dest_right f y end handle e => [tm];
fun SEP_WRITE_TAC (hs,gs) = let
  val xs = list_dest_right dest_comb ((fst o dest_pair o cdr o cdr) gs)
  val updates = map (combinSyntax.dest_update) (butlast xs)
  val ys = list_dest dest_star (car gs)
  val zs = map (mk_one o mk_pair) updates
  val qs2 = filter (fn x => not (op_mem eq x zs)) ys
  val tm2 = list_mk_star (qs2 @ rev zs) (type_of (car gs))
  val lemma = prove(mk_eq(car gs,tm2),SIMP_TAC (bool_ss++star_ss) [])
  val tac = ONCE_REWRITE_TAC [lemma]
  val df = mk_pair(last xs, ((snd o dest_pair o cdr o cdr) gs))
  val rhs = mk_comb((car o cdr) gs, df)
  val xs = filter (fn x => eq (cdr x) rhs handle e => false) hs
  val ys = (list_dest dest_star o hd o map car) xs
  fun find_any_match [] name = fail()
    | find_any_match (tm::ws) name = let
        val (v,x) = dest_pair (dest_one tm)
        in if eq v name then x else find_any_match ws name end handle e => find_any_match ws name
  val witnesses = map (find_any_match ys) (map fst updates)
  fun foo (w,tac) =
    MATCH_MP_TAC write_fun2set THEN REWRITE_TAC [STAR_ASSOC] THEN EXISTS_TAC w THEN tac
  fun lift (w,tac) = Q.PAT_ASSUM [ANTIQUOTE w] MP_TAC THEN tac
  val final_tac = foldr lift (SIMP_TAC (bool_ss++star_ss) []) xs
  in (tac THEN foldr foo final_tac witnesses) (hs,gs) end

fun SEP_NEQ_TAC (hs,gs) = let
  val (a1,a2) = dest_eq (dest_neg gs)
  fun dest_one tm = let
    val (x,y) = dest_comb tm
    val _ = if fst (dest_const x) = "one" then () else fail()
    in dest_pair y end
  fun take_apart h = let
    val xs = list_dest dest_star (car h)
    val ys = map dest_one (filter (can dest_one) xs)
    val z1 = (snd o hd o filter (fn (x,y) => eq x a1)) ys
    val z2 = (snd o hd o filter (fn (x,y) => eq x a2)) ys
    fun is_match tm = op_mem (pair_cmp eq eq) (dest_one tm) [(a1,z1),(a2,z2)] handle e => false
    in (z1,z2,list_mk_star (filter (not o is_match) xs) (type_of (car h)),cdr h) end
  val (z1,z2,zs,f) = take_apart (hd (filter (can take_apart) hs))
  val (f,df) = dest_pair (cdr f)
  val thi = ISPECL [a1,a2,z1,z2,f,df,zs] fun2set_NEQ
  in (MATCH_MP_TAC thi THEN FULL_SIMP_TAC (std_ss++star_ss) []) (hs,gs) end

fun dest_update_term tm = 
  if is_comb tm andalso combinSyntax.is_update (car tm) 
  then let val (x,y) = dest_update_term (cdr tm) 
       in (combinSyntax.dest_update (car tm) :: x, y) end else ([],tm)
fun is_update_term f tm = let
  val (xs,y) = dest_update_term tm
  in y = f end;
fun dest_fun2set tm = 
  if not (can (match_term ``(p (fun2set (f:'a->'b,df))):bool``) tm) then fail () else let
    val (f,df) = (dest_pair o cdr o cdr) tm
    in (list_dest dest_star (car tm),f,df) end
fun mk_fun2set (f,df) = (fst o dest_eq o concl o ISPECL [f,df]) fun2set_def
val is_one_pair = can (match_term ``one(x:'a,y:'b)``)
fun dest_one_pair tm = if is_one_pair tm then dest_pair (cdr tm) else fail() 
fun mk_one x = (fst o dest_eq o concl o ISPEC x) one_def

fun STRIP_FORALL_TAC (hs,goal) = 
  if is_forall goal then STRIP_TAC (hs,goal) else NO_TAC (hs,goal);  

fun VERBOSE_TAC (hs,goal) = let
  val tm = hd (filter (fn tm => is_eq tm andalso is_var(cdr tm)) hs)
  in Q.PAT_ASSUM [ANTIQUOTE tm] (fn th => FULL_SIMP_TAC pure_ss [GSYM th]) (hs,goal) end 
  handle Empty => let
  val tm = hd (filter (fn tm => is_eq tm andalso is_var((cdr o car) tm) andalso (free_vars (cdr tm) = [])) hs)
  in Q.PAT_ASSUM [ANTIQUOTE tm] (fn th => FULL_SIMP_TAC pure_ss [th]) (hs,goal) end 
  handle Empty => NO_TAC (hs,goal);

val CLEAN_TAC = REPEAT (Q.PAT_ASSUM `T` (K ALL_TAC))
val EXPAND_TAC = REPEAT VERBOSE_TAC THEN CLEAN_TAC

fun star_match fixed_vars tm1 tm2 = let
  val (xs,f1,df1) = dest_fun2set tm1 
  val (ys,f2,df2) = dest_fun2set tm2
  fun list_mk_set [] = empty_varset
    | list_mk_set (x::xs) = HOLset.add(list_mk_set xs,x)
  val match = match_terml [] (list_mk_set fixed_vars)
  fun app [] = [] | app (x::xs) = x @ app xs
  fun find_matches x [] zs = []
    | find_matches x (y::ys) zs =
        if can (match x) y 
        then (y,ys @ zs) :: find_matches x ys (y::zs) 
        else find_matches x ys (y::zs) 
  fun alternatives [] ys = [([],ys)]
    | alternatives (x::xs) ys = let
        val al = find_matches x ys []        
        in app (map (fn (z,zs) => map (fn (r,rs) => ((x,z)::r,rs)) (alternatives xs zs)) al) end       
  fun frame_var tm = is_var tm andalso not (mem tm fixed_vars)
  val ts = alternatives (filter (not o frame_var) xs) ys
  val ts = map (fn (x,y) => (x,list_mk_star y (type_of (fst (hd x))))) ts
  fun terms ([],x) = ((hd (filter frame_var xs),x) handle Empty => (list_mk_star [] (type_of (car tm1)),x))
    | terms (((y,z)::ys),x) = let
        val (y2,z2) = terms (ys,x)
        in (mk_star(y,y2),mk_star(z,z2)) end 
  fun term_full (tm1,tm2) = (mk_comb(tm1,mk_fun2set(f1,df1)),mk_comb(tm2,mk_fun2set(f2,df2)))
  val (x,y) = (term_full o terms) (hd ts)
  fun redexes xs = map (fn {redex = x,residue = y} => x) xs  
  val s = fst (match x y) 
  val result = s @ map (fn x => x |-> x) (filter (fn y => not (mem y (redexes s))) (free_vars x))
  val rs = redexes result
  val result = result @ map (fn y => y |-> list_mk_star [] (type_of y)) 
                    (filter (fn x => not (mem x rs)) (filter frame_var xs))
  (* verify result *)
  val th = SIMP_CONV (std_ss++star_ss) [SEP_CLAUSES] (mk_eq(subst result tm1,tm2))
  val _ = if cdr (concl th) = T then () else let
    val _ = print "\n\n\nstar_match failed on terms:\n"
    val _ = print "\n  fixed_vars:"
    val _ = map (fn x => (print " "; print_term x)) fixed_vars
    val _ = print "\n\n  tm1: "
    val _ = print_term tm1
    val _ = print "\n\n  tm2: "
    val _ = print_term tm2
    val _ = print "\n\n"
    in fail() end
  in result end handle Empty => fail();

fun SUBST_INST s th = let
  fun redexes xs = map (fn {redex = x,residue = y} => x) xs  
  val xs = butlast (list_dest dest_forall (concl th))
  val tt = map (fn x => (x,genvar (type_of x), mem x (redexes s))) xs
  fun alpha_c [] = ALL_CONV 
    | alpha_c ((x,true)::xs) = RAND_CONV (ALPHA_CONV x THENC ABS_CONV (alpha_c xs))  
    | alpha_c ((x,false)::xs) = RAND_CONV (ABS_CONV (alpha_c xs))  
  val th1 = CONV_RULE (alpha_c (map (fn (x,y,z) => (y,z)) tt)) th
  val g = subst (map (fn (x,y,z) => y |-> x) tt)
  fun aux s vs th = 
    if not (is_forall (concl th)) then GENL vs th else let
      val (v,x) = dest_forall (concl th)
      in aux s (if mem (g v) (redexes s) then vs else vs @ [v]) (SPEC (subst s (g v)) th) end          
  val th2 = aux s [] th1
  in th2 end;

fun SEP_F_TAC (hs,goal) = let
  fun cross [] ys = [] | cross (x::xs) ys = map (fn y => (x,y)) ys @ cross xs ys
  val fss = cross (filter (can dest_forall) hs) (filter (can dest_fun2set) hs)
  fun get_tac (i,fs) = let
    val xs = list_dest dest_forall i
    val (xs,tm) = (butlast xs, last xs)
    val vs = free_vars i
    val qs = (list_dest dest_conj o fst o dest_imp) tm
    val qs = (filter (can (dest_fun2set)) qs)
    fun first_filter [] = fail()
      | first_filter (q::qs) = (q,star_match vs q fs) handle HOL_ERR _ => first_filter qs
    val (q,ss) = first_filter qs
    val goal1 = subst ss q 
    in Q.PAT_ASSUM [ANTIQUOTE i] (MP_TAC o RW1 [GSYM markerTheory.Abbrev_def] o SUBST_INST ss)
       THEN [ANTIQUOTE goal1] by ALL_TAC THEN1
         (Q.PAT_ASSUM [ANTIQUOTE fs] MP_TAC THEN SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES])
       THEN POP_ASSUM (fn th => CONV_TAC (RATOR_CONV (REWRITE_CONV [th])))
       THEN CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [markerTheory.Abbrev_def])) end
  fun filter_map f [] = []
    | filter_map f (x::xs) = ([f x] handle HOL_ERR _ => []) @ filter_map f xs
  in FIRST (filter_map get_tac fss) (hs,goal) end;

fun SEP_I_TAC func_name (hs,goal) = let
  val inds = filter (can dest_forall) hs
  fun finder tm = ((fst o dest_const o car) tm = func_name) handle HOL_ERR _ => false
  val ys = find_terms finder goal
  val tm = hd (sort (fn x => fn y => term_size x >= term_size y) ys)
  fun redexes xs = map (fn {redex = x,residue = y} => x) xs  
  fun get_tac i = let
    val xs = list_dest dest_forall i
    val (xs,t) = (butlast xs, last xs)
    val t1 = find_term (fn t1 => can (match_term t1) tm) t 
    val s = fst (match_term t1 tm)
    val rs = redexes s
    val fs = filter (fn x => not (mem x rs) andalso mem x xs) (free_vars t1)
    val s = s @ map (fn x => x |-> x) fs
    val _ = if filter (fn {redex = x,residue = y} => not (mem x xs)) s = [] then () else fail()
    in Q.PAT_ASSUM [ANTIQUOTE i] (STRIP_ASSUME_TAC o SUBST_INST s) end 
    handle HOL_ERR _ => ALL_TAC 
  in EVERY (map get_tac inds) (hs,goal) end;

fun SEP_W_TAC (hs,goal) = let
  val xs = filter (can dest_fun2set) hs
  fun get_tac x = let   
    val f = (fst o dest_pair o cdr o cdr) x
    val ys = find_terms (is_update_term f) goal 
    val up = hd (sort (fn x => fn y => term_size x >= term_size y) ys)
    val zs = fst (dest_update_term up)
    val (qs,f,df) = dest_fun2set x
    fun replace (z,q) tm = let
      val (x,y) = dest_one_pair tm
      in if x = z then mk_one(mk_pair(x,q)) else fail() end
    fun replace_in_list (x,[]) = fail ()
      | replace_in_list (x,y::ys) = 
          replace x y :: ys handle HOL_ERR _ => y :: replace_in_list (x,ys)
    val goal = list_mk_star (foldr replace_in_list qs zs) (type_of (hd qs))
    val goal = mk_comb(goal,subst [f|->up] (cdr x))
    in ([ANTIQUOTE goal] by ALL_TAC THEN1 SEP_WRITE_TAC) end handle Empty => ALL_TAC 
  in EVERY (map get_tac xs) (hs,goal) end;

fun SEP_R_TAC (hs,goal) = let
  val xs = filter (can dest_fun2set) hs
  val is_one_pair = can (match_term ``one(x:'a,y:'b)``)
  fun app [] = [] | app (x::xs) = x @ app xs
  val xs = app (map (fn x => (map (fn y => (dest_pair(cdr y),dest_pair(cdr (cdr x)))) o 
                              filter is_one_pair o list_dest dest_star o car) x) xs)
  fun get_tac ((a,x),(f,df)) = let
    val goal = mk_conj(mk_eq(mk_comb(f,a),x),pred_setSyntax.mk_in(a,df))
    in [ANTIQUOTE goal] by ALL_TAC THEN1 SEP_READ_TAC
       THEN NTAC 2 (POP_ASSUM (fn th => FULL_SIMP_TAC pure_ss [th])) end
  in EVERY (map get_tac xs) (hs,goal) end;

fun INST_MATCH name th [] = fail()
  | INST_MATCH name th (tm::tms) = let
    fun finder tm = ((fst o dest_const o repeat car) tm = name) handle HOL_ERR _ => false
    val ys = find_terms finder tm
    val tm = hd (sort (fn x => fn y => term_size x >= term_size y) ys) handle Empty => fail()
    val vs = free_vars (concl th)
    fun redexes xs = map (fn {redex = x,residue = y} => x) xs  
    val t1 = find_term (fn t1 => can (match_term t1) tm) (concl (SPEC_ALL th))
    val (s,r) = match_term t1 tm
    val rs = redexes s
    val xs = list_dest dest_forall (concl th)
    val (xs,t) = (butlast xs, last xs)
    val fs = filter (fn x => not (mem x rs) andalso mem x xs) (free_vars t1)
    val s = s @ map (fn x => x |-> x) fs
    val th = INST_TYPE r th
    val xs = list_dest dest_forall (concl th)
    val (xs,t) = (butlast xs, last xs)
    val ys = map (inst r) (redexes s)
    val _ = if filter (fn x => not (mem x xs)) ys = [] then () else fail()
    in SUBST_INST s th end handle HOL_ERR e => INST_MATCH name th tms;

fun INST_FRAME assums th = let
  val fss = filter (can dest_fun2set) assums
  val vs = free_vars (concl th)
  val tm = concl (SPEC_ALL th)
  val qs = (list_dest dest_conj o fst o dest_imp) tm
  val qs = (filter (can (dest_fun2set)) qs)
  fun first_first_filter [] = fail()
    | first_first_filter (fs::fss) = let
      fun first_filter [] = fail()
        | first_filter (q::qs) = (q,fs,star_match vs q fs) handle HOL_ERR _ => first_filter qs
      in first_filter qs end handle HOL_ERR _ => first_first_filter fss
  val (q,fs,ss) = first_first_filter fss
  val thi = prove(mk_eq(subst ss q,fs),SIMP_TAC (bool_ss++star_ss) [])
  in ONCE_REWRITE_RULE [thi] (SUBST_INST ss th) end;

fun SEP_S_TAC names th (hs,goal) = let
  val th = RW [AND_IMP_INTRO] th
  fun LIST_INST_MATCH [] th hs = th
    | LIST_INST_MATCH (x::xs) th hs = LIST_INST_MATCH xs (INST_MATCH x th hs) hs
  val th = LIST_INST_MATCH names th (goal::hs)
  val th = INST_FRAME hs th handle HOL_ERR _ => th
  in MP_TAC th (hs,goal) end;

(* debug prover *)

fun auto_prove proof_name (goal,tac) =
  prove(goal,tac THEN (fn (tms,tm) => let
    val b = !show_types_verbosely
    val _ = print ("\n\n\n  AUTO PROOF FAILED: " ^ proof_name ^ "\n\n")
    val _ = print "-----------------------------------------------\n"
    val _ = print "  Unsolved subgoal:\n\n"
    val _ = print_term (mk_imp(list_mk_conj tms,tm))
    val _ = print "\n\n"
    val _ = print "-----------------------------------------------\n"
    val _ = print "  Initial goal:\n\n"
    val _ = (show_types_verbosely := true)
    val _ = print_term (goal)
    val _ = (show_types_verbosely := b)
    val _ = print "\n\n"
    val _ = print "-----------------------------------------------\n"
    val _ = print ("  The proof failed at " ^ proof_name ^ "\n\n\n")
  in hd [] end)) handle Empty => fail()

end;
