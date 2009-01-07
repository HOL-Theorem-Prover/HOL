structure helperLib :> helperLib =
struct
 
open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory set_sepTheory progTheory;

type decompiler_tools =
  (* ( derive spec, generate branch, status thm, program counter term ) *)
  (string -> (Thm.thm * int * int option) * (Thm.thm * int * int option) option) *
  (term -> term -> int -> bool -> string * int) * Thm.thm * Abbrev.term


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

fun all_distinct ([]:''a list) = []
  | all_distinct (x::xs) = 
      x :: all_distinct (filter (fn y => not (x = y)) xs)

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

fun list_mk_star xs ty = 
  list_mk (fn (x,y) => mk_star (y,x)) (rev xs) (mk_const("emp",ty))

fun dest_star tm = let
  val (x,z) = dest_comb tm
  val (x,y) = dest_comb x
  in if fst (dest_const x) = "STAR" then (y,z) else hd [] end

fun dest_sep_hide tm = let
  val (x,z) = dest_comb tm
  in if fst (dest_const x) = "SEP_HIDE" then z else hd [] end

fun dest_spec tm = let
  val (tm,q) = dest_comb tm
  val (tm,c) = dest_comb tm
  val (tm,p) = dest_comb tm
  val (tm,m) = dest_comb tm
  in if fst (dest_const tm) = "SPEC" then (m,p,c,q) else hd [] end;

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
  fun take_drop_until p ys [] = hd []
    | take_drop_until p ys (x::xs) = 
        if p x then (rev ys,x,xs) else take_drop_until p (x::ys) xs
  val xs = list_dest dest_star tm
  fun is_match x y = (x = get_sep_domain y)
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
  val vs = fst (pairSyntax.dest_pabs tm1)
  fun expand_pair_conv tm = ISPEC tm (GSYM pairTheory.PAIR)
  fun get_conv vs = let
    val (x,y) = pairSyntax.dest_pair vs
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
  ``(n2w n):('a word) << m``, ``(n2w n):('a word) >> m``, ``(n2w n):('a word) >>> m``, ``~(n2w n):('a word)``];

fun EVAL_ANY_MATCH_CONV patterns tm = let
  fun aux f [] = []
    | aux f (x::xs) = f x :: aux f xs handle _ => aux f xs
  val x = hd (aux (fn x => find_term (can (match_term x)) tm) patterns)
  in (PURE_REWRITE_CONV [EVAL x] THENC EVAL_ANY_MATCH_CONV patterns) tm end 
  handle e => ALL_CONV tm;


(* tree to term and back *)

datatype ftree_type = 
    FUN_IF of term * ftree_type * ftree_type 
  | FUN_LET of term * term * ftree_type
  | FUN_COND of term * ftree_type
  | FUN_VAL of term;

fun tm2ftree tm = let
  val (b,x,y) = dest_cond tm
  in FUN_IF (b,tm2ftree x,tm2ftree y) end handle e => let
  val (x,y) = pairSyntax.dest_anylet tm
  val z = tm2ftree y
  val v = mk_var("cond",``:bool``)
  fun g((x,y),z) = if not (x = v) then FUN_LET (x,y,z) else 
    if ((fst(dest_conj(y)) = v) handle e => false) then FUN_COND (cdr y,z) else FUN_COND (y,z)
  in foldr g z x end handle e => FUN_VAL tm;

fun ftree2tm (FUN_VAL tm) = tm
  | ftree2tm (FUN_IF (tm,x,y)) = mk_cond(tm, ftree2tm x, ftree2tm y)
  | ftree2tm (FUN_LET (tm,tn,x)) = pairSyntax.mk_anylet([(tm,tn)],ftree2tm x)
  | ftree2tm (FUN_COND (tm,x)) = let
      val v = mk_var("cond",``:bool``)
      in pairSyntax.mk_anylet([(v,mk_conj(v,tm))],ftree2tm x) end


(* hiding variables in SPEC theorems *)

val EQ_IMP_IMP = Q.SPECL [`p`,`q`] quotientTheory.EQ_IMPLIES;

val INC_ASSUM = prove(
  ``!p q. (p ==> q) ==> ((t ==> p) ==> (t ==> q))``,
  REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);

fun DISCH_ALL_AS_SINGLE_IMP th = let
  val th = RW [AND_IMP_INTRO] (DISCH_ALL th)
  in if is_imp (concl th) then th else DISCH ``T`` th end

fun A_MATCH_MP th1 th2 = 
  (UNDISCH_ALL o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO,AND_CLAUSES]) 
  (MATCH_MP (MATCH_MP INC_ASSUM (SPEC_ALL th1)) (DISCH_ALL_AS_SINGLE_IMP th2));

val HIDE_PRE1 = (MATCH_MP EQ_IMP_IMP (SPEC_ALL SPEC_HIDE_PRE));
val HIDE_PRE2 = (MATCH_MP EQ_IMP_IMP 
  (SPEC_ALL (RW [SEP_CLAUSES] (Q.SPECL [`x`,`emp`] SPEC_HIDE_PRE))));

fun HIDE_PRE_RULE tm th = let
  val th = CONV_RULE (PRE_CONV (MOVE_OUT_CONV tm THENC REWRITE_CONV [STAR_ASSOC])) th  
  val (_,p,_,_) = dest_spec (concl th)
  val v = snd (dest_comb (snd (dest_star p) handle e => p))
  val th = GEN v th 
  in A_MATCH_MP HIDE_PRE1 th handle e => A_MATCH_MP HIDE_PRE2 th end;

val HIDE_POST1 = (SPEC_ALL SPEC_HIDE_POST);
val HIDE_POST2 = (SPEC_ALL 
  (RW [SEP_CLAUSES] (Q.SPECL [`x`,`p`,`c`,`emp`] SPEC_HIDE_POST)));

fun HIDE_POST_RULE tm th = let
  val th = CONV_RULE (POST_CONV (MOVE_OUT_CONV tm THENC REWRITE_CONV [STAR_ASSOC])) th  
  val (_,_,_,q) = dest_spec (concl th)
  val v = fst (dest_comb (snd (dest_star q) handle e => q))
  val _ = if v = tm then v else hd []
  in A_MATCH_MP HIDE_POST1 th handle e => A_MATCH_MP HIDE_POST2 th end;

fun get_model_status_list th = 
  (map dest_sep_hide o list_dest dest_star o snd o dest_eq o concl) th handle e => []

val lemma = prove (``(b = T) ==> b``,SIMP_TAC std_ss [])

fun HIDE_STATUS_RULE in_post hide_th th = let 
  val xs = get_model_status_list hide_th
  val th = RW [hide_th,STAR_ASSOC] th
  fun find_match tm tm2 = find_term (can (match_term tm)) tm2
  fun HIDE_TERM (tm,th) = let
    val th = (if in_post then HIDE_POST_RULE tm th else th) handle e => th
    val th = HIDE_PRE_RULE tm th handle e => th
    in if can (find_match tm) (concl th) then th else
           ISPEC (mk_sep_hide tm) (A_MATCH_MP SPEC_FRAME th) end
  val th = foldl HIDE_TERM th xs
  val (_,p,_,q) = dest_spec (concl th)
  val ps = filter (fn x => not (mem (get_sep_domain x) xs)) (list_dest dest_star p)
  val qs = filter (fn x => not (mem (get_sep_domain x) xs)) (list_dest dest_star q)
  val p = list_mk_star (ps @ [(fst o dest_eq o concl) hide_th]) (type_of p)
  val q = list_mk_star (qs @ [(fst o dest_eq o concl) hide_th]) (type_of q) 
  val (_,pp,_,qq) = dest_spec (concl th)
  val rw = MATCH_MP lemma (SIMP_CONV (bool_ss++star_ss) [hide_th] (mk_eq(pp,p)))
  val th = CONV_RULE (PRE_CONV (ONCE_REWRITE_CONV [rw])) th
  val th = if in_post then let
             val rw = MATCH_MP lemma (SIMP_CONV (bool_ss++star_ss) [hide_th] (mk_eq(qq,q)))
             in CONV_RULE (POST_CONV (ONCE_REWRITE_CONV [rw])) th end
           else th
  in th end handle e => th;

fun HIDE_PRE_STATUS_RULE hide_th th = HIDE_STATUS_RULE false hide_th th


end
