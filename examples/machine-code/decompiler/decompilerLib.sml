structure decompilerLib :> decompilerLib =
struct
  
open HolKernel boolLib bossLib Parse;

open prog_ppcLib prog_x86Lib prog_armLib;

open listTheory wordsTheory pred_setTheory arithmeticTheory wordsLib pairTheory;
open set_sepTheory progTheory helperLib addressTheory tailrecLib;


val decompiler_memory = ref ([]:(string * (thm * int * int option)) list)
val decompiler_finalise = ref (I:(thm * thm -> thm * thm))


fun add_decompiled (name,th,code_len,code_exit) =
  (decompiler_memory := (name,(th,code_len,code_exit)) :: !decompiler_memory);

val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9"];

val _ = set_echo 5;

 
(* ------------------------------------------------------------------------------ *)
(* Various helper functions                                                       *)
(* ------------------------------------------------------------------------------ *)

fun dest_sep_cond tm = 
  if (fst o dest_const o fst o dest_comb) tm = "cond" 
  then snd (dest_comb tm) else hd [];

fun dest_tuple tm = 
  let val (x,y) = pairSyntax.dest_pair tm in x :: dest_tuple y end handle e => [tm];

fun n_times 0 f x = x | n_times n f x = n_times (n-1) f (f x) 

fun replace_char c str = 
  String.translate (fn x => if x = c then str else implode [x]);

fun list_mk_pair xs = pairSyntax.list_mk_pair xs handle e => ``()``
fun list_dest_pair tm = let val (x,y) = pairSyntax.dest_pair tm 
 in list_dest_pair x @ list_dest_pair y end handle e => [tm]

fun list_union [] xs = xs
  | list_union (y::ys) xs = 
      if mem y xs then list_union ys xs else list_union ys (y::xs);

fun REPLACE_CONV th tm = let
  val th = SPEC_ALL th
  val (i,j) = match_term ((fst o dest_eq o concl) th) tm
  in INST i (INST_TYPE j th) end
(* expands pairs ``(x,y,z) = f`` --> (x = FST f) /\ (y = FST (SND f)) /\ (z = ...) *)
fun expand_conv tm = let
  val cc = RAND_CONV (REPLACE_CONV (GSYM pairTheory.PAIR))
  val cc = cc THENC REPLACE_CONV pairTheory.PAIR_EQ
  val th = cc tm
  in CONV_RULE (RAND_CONV (RAND_CONV expand_conv)) th end handle e => REFL tm

fun quote_to_strings q = let (* turns a quote `...` into a list of strings *)
  fun get_QUOTE (QUOTE t) = t | get_QUOTE _ = hd []
  val xs = explode (get_QUOTE (hd q))
  fun strip_comments l [] = []
    | strip_comments l (x::xs) =
        if x = #"(" then strip_comments (l+1) xs else
        if x = #")" then strip_comments (l-1) xs else
        if 0 < l    then strip_comments l xs else x :: strip_comments l xs
  fun strip_space [] = []
    | strip_space (x::xs) = 
        if mem x [#" ",#"\t",#"\n"] then strip_space xs else x::xs
  fun lines [] [] = [] 
    | lines xs [] = [implode (strip_space (rev xs))]
    | lines xs (y::ys) = 
        if mem y [#"\n",#"|"] 
        then implode (strip_space (rev xs)) :: lines [] ys 
        else lines (y::xs) ys   
  val ys = (rev o strip_space o rev o strip_space o strip_comments 0) xs
  in lines [] ys end;  

val quote_to_hex_list: term quotation -> string list = 
  map (replace_char #" " "") o quote_to_strings

fun remove_primes th = let
  fun last s = substring(s,size s-1,1)
  fun delete_last_prime s = if last s = "'" then substring(s,0,size(s)-1) else hd []
  fun foo [] ys i = i
    | foo (x::xs) ys i = let 
      val name = (fst o dest_var) x 
      val new_name = repeat delete_last_prime name
      in if name = new_name then foo xs (x::ys) i else let 
        val new_var = mk_var(new_name,type_of x)
        in foo xs (new_var::ys) ((x |-> new_var) :: i) end end
  val i = foo (free_varsl (concl th :: hyp th)) [] []
  in INST i th end


(* ------------------------------------------------------------------------------ *)
(* Formatting SPEC theorems                                                       *)
(* ------------------------------------------------------------------------------ *)

fun DISCH_ALL_AS_SINGLE_IMP th = let
  val th = RW [AND_IMP_INTRO] (DISCH_ALL th)
  in if is_imp (concl th) then th else DISCH ``T`` th end

fun replace_abbrev_vars tm = let
  fun f v = v |-> mk_var((Substring.string o hd o tl o Substring.tokens (fn x => x = #"@") o 
                    Substring.all o fst o dest_var) v, type_of v) handle e => v |-> v
  in subst (map f (free_vars tm)) tm end

fun name_for_abbrev tm = 
  if is_const (cdr (car tm)) andalso is_const(car (car tm)) handle e => false then 
    (to_lower o fst o dest_const o cdr o car) tm
  else if can (match_term ``(f ((n2w n):'a word) (x:'c)):'d``) tm then
    "r" ^ ((int_to_string o numSyntax.int_of_term o cdr o cdr o car) tm)  
  else fst (dest_var (repeat cdr tm)) handle e =>
       fst (dest_var (find_term is_var tm)) handle e =>
       fst (dest_const (repeat car (get_sep_domain tm)));

fun abbreviate (var_name,tm) th = let
  val y = snd (dest_comb tm)
  val y = mk_eq(mk_var(var_name,type_of y),y)
  val cc = UNBETA_CONV tm THENC (RAND_CONV o RAND_CONV) (fn t => GSYM (ASSUME y)) THENC BETA_CONV
  val th = CONV_RULE cc th
  in th end;

fun ABBREV_POSTS dont_abbrev_list prefix th = let
  fun dont_abbrev tm = mem tm dont_abbrev_list 
  val (th,b) = let
    val (_,_,_,q) = dest_spec (concl th)
    val xs = list_dest dest_star q
    fun next_abbrev [] = hd [] 
      | next_abbrev (tm::xs) = 
      if (is_var (cdr tm) andalso (name_for_abbrev tm = fst (dest_var (cdr tm))))
         handle e => false then next_abbrev xs else 
      if (prefix ^ (name_for_abbrev tm) = fst (dest_var (cdr tm))) 
         handle e => false then next_abbrev xs else 
      if can dest_sep_hide tm then next_abbrev xs else 
      if dont_abbrev (car tm) then next_abbrev xs else
        (prefix ^ name_for_abbrev tm,tm)
    val th = abbreviate (next_abbrev xs) th     
    in (th,true) end handle e => (th,false)
  in if b then ABBREV_POSTS dont_abbrev_list prefix th else th end;

fun ABBREV_PRECOND prefix th = let
  val th = RW [SPEC_MOVE_COND] (SIMP_RULE (bool_ss++sep_cond_ss) [] th)
  val tm = (fst o dest_imp o concl) th
  val v = mk_var(prefix^"cond",``:bool``)
  val thx = SYM (BETA_CONV (mk_comb(mk_abs(v,v),tm)))
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (fn tm => thx)) th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] (RW [precond_def] (UNDISCH th))
  in th end handle e => th;

fun ABBREV_ALL dont_abbrev_list prefix = 
  ABBREV_PRECOND prefix o ABBREV_POSTS dont_abbrev_list prefix;

fun ABBREV_CALL prefix th = let
  val (_,_,_,q) = (dest_spec o concl) th
  val (x,tm) = pairSyntax.dest_anylet q
  val (x,y) = hd x
  val ys = map (fn v => mk_var(prefix^(fst (dest_var v)),type_of v)) (dest_tuple x)
  val thi = ASSUME (mk_eq(pairSyntax.list_mk_pair ys, y))
  val cc = UNBETA_CONV y THENC RAND_CONV (fn tm => GSYM thi)
  val th = CONV_RULE (RAND_CONV cc) th
  val th = RW [FST,SND] (PairRules.PBETA_RULE (RW [LET_DEF] th))
  in ABBREV_PRECOND prefix th end handle e => ABBREV_PRECOND prefix th;

fun UNABBREV_ALL th = let
  fun remove_abbrev th = let
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) expand_conv) th
    val th = RW [GSYM AND_IMP_INTRO] th
    val (x,y) = (dest_eq o fst o dest_imp o concl) th
    in MP (INST [x|->y] th) (REFL y) end 
    handle e => UNDISCH (CONV_RULE ((RATOR_CONV o RAND_CONV) BETA_CONV) th)
    handle e => UNDISCH th
  in repeat remove_abbrev (DISCH_ALL th) end;


(* ------------------------------------------------------------------------------ *)
(* Deriving SPEC theorems                                                         *)
(* ------------------------------------------------------------------------------ *)

fun pair_apply f ((th1,x1:int,x2:int option),NONE) = ((f th1,x1,x2),NONE)
  | pair_apply f ((th1,x1,x2),SOME (th2,y1:int,y2:int option)) = 
      ((f th1,x1,x2),SOME (f th2,y1,y2))

fun jump_apply f NONE = NONE | jump_apply f (SOME x) = SOME (f x);

fun pair_jump_apply (f:int->int) ((th1,x1:int,x2:int option),NONE) = ((th1,x1,jump_apply f x2),NONE)
  | pair_jump_apply f ((th1:thm,x1,x2),SOME (th2:thm,y1:int,y2:int option)) = 
      ((th1,x1,jump_apply f x2),SOME (th2,y1,jump_apply f y2))

fun parse_renamer instruction = let
  val xs = Substring.tokens (fn x => x = #"/") (Substring.all instruction)
  in if length xs < 2 then (instruction,fn x => x) else (Substring.string (hd xs),fn th => let
    val vs = free_vars (concl th) 
    val vs = filter (fn v => mem (fst (dest_var v)) ["f","df"]) vs
    fun make_new_name v = ((implode o rev o tl o rev o explode o fst o dest_var) v) ^ Substring.string (hd (tl xs))
    val s = map (fn v => v |-> mk_var(make_new_name v,type_of v)) vs
    in INST s th end) end

fun derive_individual_specs tools (code:string list) = let
  val (f,_,hide_th,pc) = tools
  fun get_model_status_list th = 
    (map dest_sep_hide o list_dest dest_star o snd o dest_eq o concl) th handle e => []
  val dont_abbrev_list = pc :: get_model_status_list hide_th  
  fun get_specs (instruction,(n,ys)) = 
    if (substring(instruction,0,7) = "insert:" handle e => false) then let
      val name = substring(instruction,7,length (explode instruction) - 7)
      val (name,(th,i,j)) = hd (filter (fn (x,y) => x = name) (!decompiler_memory))
      val th = RW [sidecond_def,hide_th,STAR_ASSOC] th
      val th = ABBREV_CALL ("s"^(int_to_string n)^"@") th
      val _ = echo 1 "  (insert command)\n"
      in (n+1,(ys @ [(n,(th,i,j),NONE)])) end
    else let
      val (instruction, renamer) = parse_renamer instruction
      val _ = echo 1 ("  "^instruction^":")
      val i = int_to_string n
      val g = RW [precond_def] o ABBREV_ALL dont_abbrev_list ("s"^i^"@") o renamer
      val (x,y) = pair_apply g (f instruction)
      val _ = echo 1 ".\n"
      in (n+1,(ys @ [(n,x,y)])) end
  val _ = echo 1 "\nDeriving specifications for individual instructions.\n"
  val res = snd (foldl get_specs (1,[]) code)

  fun calc_addresses i [] = []
    | calc_addresses i ((n:int,(th1:thm,l1,j1),y)::xs)  = let
    val (x,y) = pair_jump_apply (fn j => i+j) ((th1,l1,j1),y)
    in (i,x,y) :: calc_addresses (i+l1) xs end
  val res = calc_addresses 0 res
  val _ = echo 1 "\n"
  in res end;

(* 

val (instruction,n,ys) = (hd (tl code),0,[]) 

*)


(* ------------------------------------------------------------------------------ *)
(* Composing two specifications                                                   *)
(* ------------------------------------------------------------------------------ *)

fun spec_pre th = let
  val (_,p,_,_) = dest_spec (concl th) in (list_dest dest_star p, type_of p) end;
fun spec_post th = let
  val (_,_,_,q) = dest_spec (concl th) in (list_dest dest_star q, type_of q) end;

fun spec_post_and_pre th1 th2 = let
  val (_,_,_,q) = dest_spec (concl th1)
  val (_,p,_,_) = dest_spec (concl th2)
  in (list_dest dest_star q, list_dest dest_star p, type_of q) end;

fun find_composition1 th1 th2 = let
  val (q,p,ty) = spec_post_and_pre th1 th2
  fun get_match_term tm = replace_abbrev_vars (get_sep_domain tm)
  fun mm x y = get_match_term x = get_match_term y
  fun fetch_match x [] zs = hd []
    | fetch_match x (y::ys) zs = 
        if mm x y then (y, rev zs @ ys) else fetch_match x ys (y::zs)
  fun partition [] ys (xs1,xs2,ys1) = (rev xs1, rev xs2, rev ys1, ys)
    | partition (x::xs) ys (xs1,xs2,ys1) =
        let val (y,zs) = fetch_match x ys [] in
          partition xs zs (x::xs1, xs2, y::ys1)
        end handle e =>
          partition xs ys (xs1, x::xs2, ys1)
  val (xs1,xs2,ys1,ys2) = partition q p ([],[],[])
  val tm1 = mk_star (list_mk_star xs1 ty, list_mk_star xs2 ty)
  val tm2 = mk_star (list_mk_star ys1 ty, list_mk_star ys2 ty)
  val th1 = CONV_RULE (POST_CONV (MOVE_STAR_CONV tm1)) th1    
  val th2 = CONV_RULE (PRE_CONV (MOVE_STAR_CONV tm2)) th2 
  val th = MATCH_MP SPEC_FRAME_COMPOSE (DISCH_ALL_AS_SINGLE_IMP th2)   
  val th = MATCH_MP th (DISCH_ALL_AS_SINGLE_IMP th1)   
  val th = UNDISCH_ALL (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO,AND_CLAUSES] th)
  val th = SIMP_RULE std_ss [INSERT_UNION_EQ,UNION_EMPTY,word_arith_lemma1,
             word_arith_lemma2,word_arith_lemma3,word_arith_lemma4,SEP_CLAUSES] th
  in th end;

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

val SPEC_COMPOSE = find_composition2;    


(* ------------------------------------------------------------------------------ *)
(* Constructing specifications for paths throught the code                        *)
(* ------------------------------------------------------------------------------ *)

datatype mc_tree = 
    LEAF of thm * int
  | SEQ of term list * mc_tree 
  | BRANCH of term * mc_tree * mc_tree;

fun basic_find_composition th1 (th2,l2,j2) = let
  val th = remove_primes (SPEC_COMPOSE th1 th2)
  val th = RW [WORD_CMP_NORMALISE] th
  val th = RW [GSYM WORD_NOT_LOWER, GSYM WORD_NOT_LESS] th
  fun h x = (fst o dest_eq) x handle e => (fst o dest_abs o car) x
  fun f [] ys = ys | f (x::xs) ys = f xs (h x :: ys handle e => ys) 
  val th2_hyps = f (hyp th2) []
  fun g tm = mem (h tm) th2_hyps handle e => false
  val lets = filter g (hyp th) 
  in ((th,l2,j2),lets) end

fun find_cond_composition th1 NONE = hd [] 
  | find_cond_composition th1 (SOME (th2,l2,j2)) = let
  val th = RW [SPEC_MOVE_COND] th2
  val th = if concl th = T then hd [] else th
  val th = if not (is_imp (concl th)) then th else
             CONV_RULE ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM CONTAINER_def])) th
  val th = RW [GSYM SPEC_MOVE_COND] th
  val ((th,l,j),lets) = basic_find_composition th1 (th,l2,j2)
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [SEP_CLAUSES] th
  val th = RW [SPEC_MOVE_COND,GSYM AND_IMP_INTRO] th
  fun imps tm xs = let val (x,y) = dest_imp tm in imps y (x::xs) end handle e => xs
  fun is_CONTAINER tm = (fst o dest_const o car) tm = "CONTAINER" handle e => false
  val xs = filter is_CONTAINER (imps (concl th) [])
  val th = RW [GSYM SPEC_MOVE_COND,CONTAINER_def] th
  in let val cond = snd (dest_comb (hd xs)) in 
     let val cond = dest_neg cond in (cond,(th,l,j)) end 
     handle e => (mk_neg cond,(th,l,j)) end 
     handle e => (``F:bool``,(th,l,j)) end;

fun negate tm = dest_neg tm handle e => mk_neg tm
fun the (SOME x) = x | the NONE = hd []

fun tree_composition (th,i:int,thms,entry,exit,conds,firstTime) =
  if i = entry andalso not firstTime then LEAF (th,i) else
  if i = exit then LEAF (th,i) else let
    val (_,thi1,thi2) = hd (filter (fn (x,y,z) => x = i) thms)
    in let (* try composing second branch *)
       val (cond,(th2,_,i2)) = find_cond_composition th thi2
       in if mem (negate cond) conds 
          then (* case: only second branch possible *)
               tree_composition (th2,the i2,thms,entry,exit,conds,false)
          else if mem cond conds then hd [] 
          else (* case: both branches possible *) let
            val ((th1,_,i1),lets) = basic_find_composition th thi1
            val t1 = tree_composition (th1,the i1,thms,entry,exit,cond::conds,false)
            val t2 = tree_composition (th2,the i2,thms,entry,exit,negate cond::conds,false)
            val t1 = if length lets = 0 then t1 else SEQ (lets,t1)
            in BRANCH (cond,t1,t2) end end
       handle e => (* case: only first branch possible *) let 
       val ((th,_,i),lets) = basic_find_composition th thi1
       val result = tree_composition (th,the i,thms,entry,exit,conds,false)
       in if length lets = 0 then result else SEQ (lets,result) end end

fun map_spectree f (LEAF (thm,i)) = LEAF (f thm,i)
  | map_spectree f (SEQ (x,t)) = SEQ(x, map_spectree f t)
  | map_spectree f (BRANCH (j,t1,t2)) = BRANCH (j, map_spectree f t1, map_spectree f t2)

fun generate_spectree tools inst_thms (entry,exit) = let 
  val (_,_,hide_th,_) = tools
  fun apply_to_th f (i,(th,k,l),NONE) = (i,(f th,k,l),NONE)
    | apply_to_th f (i,(th,k,l),SOME (th2,k2,l2)) = (i,(f th,k,l),SOME (f th2,k2,l2))
  val inst_thms = map (apply_to_th (RW [hide_th])) inst_thms
  val (i,(th,_,_),_) = hd inst_thms
  val (m,_,_,_) = dest_spec (concl th)
  val (th,i,conds,firstTime) = (Q.SPECL [`emp`,`{}`] (ISPEC m SPEC_REFL),entry,[]:term list,true)
  val _ = echo 1 "Forward simulation,"
  val t = tree_composition (th,i,inst_thms,entry,exit,conds,firstTime)
  val _ = echo 1 " done.\n"
  val t = map_spectree (HIDE_STATUS_RULE true hide_th) t
  in t end;

fun spectree2thms (LEAF thm) thms = thm :: thms
  | spectree2thms (SEQ (_,t)) thms = spectree2thms t thms
  | spectree2thms (BRANCH (_,t1,t2)) thms = spectree2thms t1 (spectree2thms t2 thms)


(* ------------------------------------------------------------------------------ *)
(* Extract a HOL function from a "spectree"                                       *)
(* ------------------------------------------------------------------------------ *)

fun get_resvar_name v = let
  val n = (fst o dest_var) v
  fun g [] = n | g (c::cs) = if c = #"@" then implode cs else g cs
  in g (explode n) end

fun get_resvar v = mk_var(get_resvar_name v,type_of v);

fun resvar_subst xs tm = let
  fun find_subst [] v = v |-> v
    | find_subst (x::xs) v = if v = get_resvar x then v |-> x else find_subst xs v
  in subst (map (find_subst xs) (free_vars tm)) tm end;

fun spectree2fun exit (LEAF (th,i)) (result,call) s =
      FUN_VAL (resvar_subst s (if i = exit then result else call))
  | spectree2fun exit (BRANCH (cond,t1,t2)) k s =
      FUN_IF (cond,spectree2fun exit t1 k s,spectree2fun exit t2 k s)
  | spectree2fun exit (SEQ ([],t)) k s = spectree2fun exit t k s
  | spectree2fun exit (SEQ (x::xs,t)) k s = let
      val (x,y) = dest_eq(x) 
      in FUN_LET (x,y,spectree2fun exit (SEQ (xs,t)) k (list_dest_pair x @ s)) end 
      handle e => FUN_COND (cdr x,spectree2fun exit (SEQ (xs,t)) k s)

fun simplify_names ftree = let
  fun aux (FUN_VAL tm)      = tm
    | aux (FUN_COND (c,t))  = ftree2tm (FUN_COND (c,FUN_VAL (aux t)))
    | aux (FUN_IF (a,b,c))  = ftree2tm (FUN_IF (a,FUN_VAL (aux b),FUN_VAL (aux c)))
    | aux (FUN_LET (v,x,t)) = let
       val tm = aux t
       val names = map (fn x => (get_resvar_name x,x)) (list_dest_pair v)
       val xs = free_vars tm
       fun h v = if not (mem v xs) then hd [] else mk_var((fst o dest_var) v ^ "'",type_of v)
       fun new_name (n,x) = repeat h (mk_var(n,type_of x))
       val new_name_list = map (fn (n,x) => (x,new_name (n,x))) names
       val subst_list = map (fn (x,y) => x |-> y) new_name_list
       val tm = subst subst_list tm
       val vars = list_mk_pair (map snd new_name_list) 
       in ftree2tm (FUN_LET (vars,x,FUN_VAL tm)) end
  in tm2ftree (aux ftree) end

fun tree2modified_vars (LEAF th) xs = xs
  | tree2modified_vars (BRANCH (cond,t1,t2)) xs = 
      tree2modified_vars t1 (tree2modified_vars t2 xs)
  | tree2modified_vars (SEQ ([],t)) xs = tree2modified_vars t xs
  | tree2modified_vars (SEQ (x::xs,t)) ys = let
      fun f v = mk_var(get_resvar_name v,type_of v)
      val vs = (map f o list_dest_pair o fst o dest_eq) x
      in tree2modified_vars (SEQ (xs,t)) (list_union vs ys) end 
      handle e => tree2modified_vars (SEQ (xs,t)) ys;

fun thms2resources [] xs = xs
  | thms2resources (th::thms) xs = let
  val (_,p,_,_) = dest_spec (concl th) 
  val p = list_dest dest_star p
  fun f (tm,tms) = let val v = (snd o dest_comb) tm in 
    if is_var v andalso not (mem v tms) then v::tms else tms end handle e => tms
  in thms2resources thms (foldr f xs p) end

fun string_split c str = let
  fun f [] ys = hd []
    | f (x::xs) ys = if x = c then (implode (rev ys),implode xs) else f xs (x::ys)
  in f (explode str) [] end

fun sort_SEQ_in_tree keep_status (SEQ (xs,t)) = let
  fun sort_SEQ [] (xs,ys,zs) = rev xs @ rev ys @ rev zs
    | sort_SEQ (q::qs) (xs,ys,zs) =
      if (is_abs o car) q handle e => false then sort_SEQ qs (q::xs,ys,zs) 
      else if (hd o explode o snd o string_split #"@" o fst o dest_var o cdr o car) q = #"r" handle e => false 
      then sort_SEQ qs (xs,ys,q::zs) else sort_SEQ qs (xs,q::ys,zs)
  fun f x = keep_status orelse not (mem ((fst o dest_var o fst o dest_eq) x) ["sN","sZ","sC","sV"]) handle e => true
  in SEQ (filter f (sort_SEQ xs ([],[],[])),sort_SEQ_in_tree keep_status t) end
  | sort_SEQ_in_tree keep_status (BRANCH(c,t1,t2)) = let
     val t1 = sort_SEQ_in_tree keep_status t1
     val t2 = sort_SEQ_in_tree keep_status t2
     in if is_neg c then BRANCH(dest_neg c,t2,t1) else BRANCH (c,t1,t2) end
  | sort_SEQ_in_tree keep_status t = t

val var_sorter = let (* sorts in alphabetical order except for r1,r2,r3 which will come first *)
  fun dest_reg_var s = let
    val xs = explode s
    in if hd xs = #"r" then string_to_int (implode (tl xs)) else hd [] end
  val is_reg_var = can dest_reg_var
  fun name_of_var tm = let
    val s = fst (dest_var tm)
    in if s = "eax" then "r0" else    
       if s = "ecx" then "r1" else    
       if s = "edx" then "r2" else    
       if s = "ebx" then "r3" else    
       if s = "esp" then "r4" else    
       if s = "ebp" then "r5" else    
       if s = "esi" then "r6" else    
       if s = "edi" then "r7" else s end  
  fun cmp tm1 tm2 = let
    val s1 = name_of_var tm1
    val s2 = name_of_var tm2
    in if is_reg_var s1 = is_reg_var s2 
       then (dest_reg_var s1 < dest_reg_var s2 handle e => s1 < s2)
       else is_reg_var s1 end
  in sort cmp end

fun erase_conds (FUN_VAL tm) = FUN_VAL tm
  | erase_conds (FUN_COND (c,t)) = erase_conds t
  | erase_conds (FUN_IF (a,b,c)) = FUN_IF (a,erase_conds b,erase_conds c)
  | erase_conds (FUN_LET (x,y,t)) = FUN_LET (x,y,erase_conds t)



fun extract_function name inst_thms tools (entry,exit) function_in_out = let
  (* generate spectree *)
  val t = generate_spectree tools inst_thms (entry,exit)
  val t = sort_SEQ_in_tree false t  
  val thms = spectree2thms t []
  (* determine output *)
  val res_out = tree2modified_vars t []
  val modified = map (fst o dest_var) res_out
  val res_out = var_sorter res_out 
  val output = list_mk_pair res_out
  (* determine input *)
  val f = mk_var(name,mk_type("fun",[type_of ``()``,type_of output]))
  val c = mk_var("cond",``:bool``)
  val ftree = spectree2fun exit t (output,mk_comb(f,``()``)) []
  val vars = free_vars (ftree2tm ftree)
  val res_in = var_sorter vars
  val res_in = filter (fn x => not (mem x [f,c])) res_in
  val input = list_mk_pair res_in
  val res_out = var_sorter (list_union res_in res_out)
  val output = list_mk_pair res_out
  (* over-ride input/output *)
  val (input,output) = (case function_in_out of SOME x => x | NONE => (input,output))
  (* create data function *)
  val f1 = mk_comb(mk_var(name,mk_type("fun",[type_of input,type_of output])),input)
  val ftree = spectree2fun exit t (output,f1) []
  val tm1 = ftree2tm (simplify_names (erase_conds ftree))
  (* create precondition function *)
  val f2 = mk_comb(mk_var(name^"_pre",mk_type("fun",[type_of input,``:bool``])),input)
  val ftree = spectree2fun exit t (mk_var("cond",``:bool``),mk_conj(f2,mk_var("cond",``:bool``))) []
  val tm2 = ftree2tm (simplify_names ftree)
  val tm2 = subst [mk_var("cond",``:bool``)|->``T:bool``] tm2
  val tm2 = (cdr o concl o REWRITE_CONV []) tm2 handle e => tm2
  val tm1 = mk_eq(f1,tm1) 
  val tm2 = mk_eq(f2,tm2) 
  in (tm1,tm2,thms) end;


(* ------------------------------------------------------------------------------ *)
(* Select subcomponent of code based on simple control-flow heuristic             *)
(* ------------------------------------------------------------------------------ *)

fun find_segments thms = let
  (* find list of jumps *)
  fun get_jumps [] = []
    | get_jumps ((x,(_,_,NONE),NONE)::xs) = get_jumps xs
    | get_jumps ((x,(_,_,SOME j),NONE)::xs) = (x,j) :: get_jumps xs
    | get_jumps ((x,(_,_,NONE),SOME (_,_,NONE))::xs) = get_jumps xs
    | get_jumps ((x,(_,_,NONE),SOME (_,_,SOME j))::xs) = (x,j) :: get_jumps xs
    | get_jumps ((x,(_,_,SOME i),SOME (_,_,NONE))::xs) = (x,i) :: get_jumps xs
    | get_jumps ((x,(_,_,SOME i),SOME (_,_,SOME j))::xs) = (x,i) :: (x,j) :: get_jumps xs
  val jumps = get_jumps thms
  val max = hd (sort (fn x => fn y => (y <= (x:int))) (map fst jumps))
  val loops = filter (fn (x,y) => y < x) jumps @ [(max,0)]
  fun in_range (x,y) z = x <= z andalso z <= y
  fun find_entry (y,x) = (snd o hd) 
    (filter (fn (x1,x2) => in_range(x,y)x2 andalso not (in_range(x,y)x1)) jumps @ [(y,x)])
  fun find_exit (y,x) = (snd o hd) 
    (filter (fn (x1,x2) => in_range(x,y)x1 andalso not (in_range(x,y)x2)) jumps @ [(y,x)])
  val segments = map (fn x => (find_entry x, find_exit x)) loops
  in segments end;     
  

(* ------------------------------------------------------------------------------ *)
(* Prove that code executes a HOL function                                        *)
(* ------------------------------------------------------------------------------ *)

fun unhide_pre_elements thms tools = let
  val (_,_,hide_th,_) = tools 
  val sts = (fst o dest_eq o concl o SPEC_ALL) hide_th
  fun show_pre_for_thm (th,loop) = let 
    val (_,p,_) = spec_post_and_pre th th
    val xs = filter (fn tm => can dest_sep_hide tm andalso (not (tm = sts))) p 
    fun show_pre (tm,th) = let
      val th = CONV_RULE (PRE_CONV (MOVE_OUT_CONV tm)) th
      val th = RW [GSYM SPEC_HIDE_PRE] th
      val (_,p,_) = spec_post_and_pre (SPEC_ALL th) (SPEC_ALL th)
      val v = mk_var(name_for_abbrev (last p),(type_of o fst o dest_forall o concl) th)
      val th = SPEC v th
      in th end handle HOL_ERR e => th
    val th = foldr show_pre th (map dest_sep_hide xs)
    in (th,loop) end
  val thms = map show_pre_for_thm thms
  in thms end;

fun sort_code c = let
  val c = (cdr o concl o REWRITE_CONV [INSERT_UNION_EQ,UNION_EMPTY]) c handle e => c 
  val xs = list_dest pred_setSyntax.dest_insert c
  fun measure tm = (numSyntax.int_of_term o cdr o cdr o fst o dest_pair) tm handle e => 0
  val xs = sort (fn x => fn y => measure x < measure y) xs
  fun all_distinct [] = []
    | all_distinct (x::xs) = x :: all_distinct (filter (fn y => not (x = y)) xs)
  val xs = all_distinct xs
  val xs = filter (not o pred_setSyntax.is_empty) xs
  val c = foldr pred_setSyntax.mk_insert (pred_setSyntax.mk_empty(type_of (hd xs))) xs
  in c end

fun fill_preconditions thms = let
  (* extract list of pre elements from each theorem *)
  val pres = map (fst o spec_pre o fst) thms
  (* make a list of all elements that occur in preconditions *)    
  val pre_elements = foldr (uncurry list_union) [] pres
  (* filter out "cond" *)
  val pres = filter (not o can dest_sep_cond) pre_elements
  (* insert missing elements into specs *)
  fun insert_pres (th,loop) = let    
    val zs = (map get_sep_domain o fst o spec_pre) th
    val new = filter (fn x => not (mem (get_sep_domain x) zs)) pres
    in if new = [] then (th,loop) else let
    val frame = list_mk_star new (snd (spec_pre th))
    val th = RW [STAR_ASSOC] (SPEC frame (MATCH_MP SPEC_FRAME th))     
    in (th,loop) end end
  val thms = map insert_pres thms
  (* collect code *)
  fun select_code (m,p,c,q) = c
  val cs = map (select_code o dest_spec o concl o fst) thms  
  val c = foldr pred_setSyntax.mk_union (hd cs) (tl cs)
  val cc = sort_code c
  fun fix_code (th,loop) = let
    val th = SPEC cc (MATCH_MP SPEC_SUBSET_CODE th)
    val tm = (fst o dest_imp o concl) th
    val lemma = prove(tm,REWRITE_TAC [INSERT_SUBSET,IN_INSERT,NOT_IN_EMPTY,EMPTY_SUBSET])
    in (MP th lemma,loop) end
  val thms = map fix_code thms
  in thms end;

fun get_input_list def = 
  (cdr o cdr o car o snd o dest_conj o concl o SPEC_ALL) def handle e => ``()``;

fun get_output_list def = let
  val tm = (concl o last o CONJUNCTS o SPEC_ALL) def
  val (fm,tm) = dest_eq tm
  val t = (tm2ftree) tm 
  fun ftree2res (FUN_VAL tm) = [tm]
    | ftree2res (FUN_IF (tm,x,y)) = ftree2res x @ ftree2res y
    | ftree2res (FUN_LET (tm,tn,x)) = ftree2res x 
    | ftree2res (FUN_COND (tm,x)) = ftree2res x
  val res = filter (fn x => not (x = fm)) (ftree2res t)
  val result = dest_tuple (hd res)
  fun deprime x = mk_var(replace_char #"'" "" (fst (dest_var x)), type_of x) handle e => x
  in pairSyntax.list_mk_pair(map deprime result) end;

fun hide_pre_post_elements thms def tools = let
  val (_,_,_,pc) = tools
  val f = map (replace_char #"'" "") o map (fst o dest_var) 
  val in_list = (f o free_vars o get_input_list) def
  val out_list = (f o free_vars o get_output_list) def
  fun hide (f:term->thm->thm) (tm,th) = if tm = pc then th else f tm th
  val get_name = fst o dest_var o hd o free_vars o replace_abbrev_vars o cdr
  fun hide_elements (th,loop) = let
    val (q,p,ty) = spec_post_and_pre th th
    val q = filter (not o can dest_sep_hide) q   
    val p = filter (not o can dest_sep_hide) p   
    val post_list = if loop then in_list else out_list
    val p2 = filter (fn tm => not (mem (get_name tm) in_list)) p
    val q2 = filter (fn tm => not (mem (get_name tm) post_list)) q
    fun not_pc_and_not_cond tm = 
      not (car tm = pc) andalso not (can dest_sep_cond tm) handle e => true
    val p2 = filter not_pc_and_not_cond p2
    val q2 = filter not_pc_and_not_cond q2
    val th = foldr (hide HIDE_POST_RULE) th (map car q2)
    val th = foldr (hide HIDE_PRE_RULE) th (map car p2)
    in (th,loop) end handle e => (th,loop)
  val thms = map hide_elements thms
  in thms end;      

fun sort_sep_elements thms = let
  val f = term_to_string o replace_abbrev_vars o get_sep_domain
  val sorter = sort (curry (fn (tm1,tm2) => f tm1 < f tm2))
  fun fix (th,loop) = let
    val th = (UNDISCH_ALL o RW [SPEC_MOVE_COND] o SIMP_RULE (bool_ss++sep_cond_ss) []) th
    val (m,p,c,q) = dest_spec (concl th)
    val p' = list_mk_star (sorter (list_dest dest_star p)) (type_of p)
    val q' = list_mk_star (sorter (list_dest dest_star q)) (type_of q)
    val p_th = prove(mk_eq(p,p'),SIMP_TAC (bool_ss++star_ss) [])
    val q_th = prove(mk_eq(q,q'),SIMP_TAC (bool_ss++star_ss) [])
    val th = CONV_RULE (RATOR_CONV (ONCE_REWRITE_CONV [p_th])) th
    val th = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [q_th])) th
    in (th,loop) end
  val thms = map fix thms
  in thms end

fun get_pre_post_terms tools thms def = let
  val (_,_,_,pc) = tools
  val th = (fst o hd o filter (not o snd)) thms
  val (q,p,ty) = spec_post_and_pre th th
  val p = filter (not o can dest_sep_cond) p
  val q = map replace_abbrev_vars q
  val pre_tm = pairSyntax.list_mk_pabs([get_input_list def],list_mk_star p ty)
  val post_tm = pairSyntax.list_mk_pabs([get_output_list def],list_mk_star q ty)
  in (pre_tm,post_tm) end;

fun introduce_post_let th = let
  val (x,y) = (dest_comb o cdr o concl) th
  val (x,z) = pairSyntax.dest_pabs x
  val tm = pairSyntax.mk_anylet([(x,y)],z)
  val th1 = GSYM (SIMP_CONV std_ss [LET_DEF] tm)
  in CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [th1])) 
       (SIMP_RULE std_ss [] th) end handle e => th;

fun rename_th def = let
  val x = (cdr o cdr o car o fst o dest_conj o concl) def
  val p = mk_var("P",mk_type("fun",[type_of x,``:bool``]))
  val v = mk_var("x",type_of x)
  val th = SIMP_CONV std_ss [FORALL_PROD] (mk_forall(v,mk_comb(p,v)))
  val vs = list_dest_pair x 
  fun rename [] = ALL_CONV
    | rename (v::vs) = RAND_CONV (ABS_CONV (rename vs) THENC ALPHA_CONV v)
  in CONV_RULE (RAND_CONV (rename vs)) th end handle e => FORALL_PROD;

fun pull_pre_post pre_tm post_tm (th,loop) = let
  val post = if loop then pre_tm else post_tm
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
  val (x,y) = (pairSyntax.dest_pabs) post
  val (_,_,_,q) = dest_spec (concl th)
  val (i,j) = match_term y q
  val new_post = mk_comb(post,subst i x)
  val thi = GSYM (SIMP_CONV std_ss [] new_post)
  val new_pre = mk_comb(pre_tm,fst (pairSyntax.dest_pabs pre_tm))
  val thj = GSYM (SIMP_CONV std_ss [] new_pre)
  val th = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [thi])) th
  val th = CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [thj])) th
  in (th,loop) end;

fun pull_pre_post pre_tm post_tm (th,loop) = let
  val post = if loop then pre_tm else post_tm
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
  val th = UNDISCH_ALL (REWRITE_RULE [SPEC_MOVE_COND] th)
  val (x,y) = (pairSyntax.dest_pabs) post
  val (_,_,_,q) = dest_spec (concl th)
  val (i,j) = match_term y q
  val new_post = mk_comb(post,subst i x)
  val thi = GSYM (SIMP_CONV std_ss [] new_post)
  val new_pre = mk_comb(pre_tm,fst (pairSyntax.dest_pabs pre_tm))
  val thj = GSYM (SIMP_CONV std_ss [] new_pre)
  val th = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [thi])) th
  val th = CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [thj])) th
  in (th,loop) end;

fun GEN_ALL_EXCEPT vs th = let
  val ws = filter (fn x => not (mem x vs)) (free_vars (concl th))    
  in foldr (fn (tm,th) => GEN tm th) th ws end

fun prove_correspondence tools def thms = let
  (* unhide all preconditions except status bits *)
  val thms = unhide_pre_elements thms tools 
  (* make sure all preconditions mention the same resources *)
  val _ = echo 2 " - sorting code\n"
  val thms = fill_preconditions thms
  (* hide irrelevant pre and post elements *)  
  val thms = hide_pre_post_elements thms def tools
  (* sort theorems *)  
  val thms = sort_sep_elements thms 
  (* generate pre- and postconditions *)
  val _ = echo 2 " - generating specification\n"
  val (pre_tm,post_tm) = get_pre_post_terms tools thms def
  (* construct the spec *)
  val conv = SIMP_CONV (bool_ss++tailrec_top_ss()) []
  val temp = (snd o dest_eq o concl o conv o cdr o car o fst o dest_conj o concl) def
  val temp2 = (snd o dest_eq o concl o conv o cdr o car o snd o dest_conj o concl) def
  val xs = list_dest dest_comb temp   
  val ys = list_dest dest_comb temp2   
  val th = ISPEC (el 3 ys) (ISPEC (el 2 ys) SPEC_TAILREC)
  val th = SPECL [el 3 xs, el 4 xs] th
  val th = ISPECL [pre_tm,post_tm] th
  val th = SIMP_RULE (pure_ss++tailrec_reverse_ss()) [] th
  val (m,_,c,_) = (dest_spec o concl o fst o hd) thms  
  val th = ISPEC c th
  val th = ISPEC m th
  (* prove the spec *)
  val thms = map (pull_pre_post pre_tm post_tm) thms handle e => thms
  val goal = concl (UNDISCH th)
  val vs = free_vars goal  
  val rw = map (GEN_ALL_EXCEPT vs o DISCH_ALL o UNABBREV_ALL o fst) thms
  val _ = echo 2 " - proving specification\n"
  val result = prove(goal,
(*
  set_goal([],goal)
*)
    MATCH_MP_TAC th
    THEN EVERY (map ASSUME_TAC rw)
    THEN REPEAT (POP_ASSUM MP_TAC)
    THEN SPEC_TAC (pre_tm,genvar(type_of pre_tm)) THEN STRIP_TAC
    THEN SPEC_TAC (post_tm,genvar(type_of post_tm)) THEN STRIP_TAC
    THEN SPEC_TAC (c,genvar(type_of c)) THEN STRIP_TAC
    THEN SIMP_TAC std_ss [LET_DEF] 
    THEN REWRITE_TAC [AND_IMP_INTRO] THEN STRIP_TAC
    THEN SIMP_TAC bool_ss [rename_th def]
    THEN SIMP_TAC (std_ss++tailrec_top_ss()) [LET_DEF]
    THEN ONCE_REWRITE_TAC [tailrecTheory.TAILREC_PRE_THM]
    THEN SIMP_TAC std_ss []
    THEN SIMP_TAC (std_ss++tailrec_part_ss()) [LET_DEF]
    THEN REPEAT STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC)
    THEN CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
    THEN SIMP_TAC std_ss [LET_DEF,FST,SND]
    THEN METIS_TAC []) 
  val result = SPEC ((cdr o cdr o car o fst o dest_conj o concl) def) result
  val result = RW [GSYM SPEC_MOVE_COND] result
  val result = introduce_post_let result  
  val result = SIMP_RULE std_ss [] result
  in result end


(* ------------------------------------------------------------------------------ *)
(* The decompiler                                                                 *)
(* ------------------------------------------------------------------------------ *)

fun decompile_part tools name inst_thms (entry,exit) function_in_out = let
  val (tm1,tm2,thms) = extract_function name inst_thms tools (entry,exit) function_in_out
 (* val thms = map (fn (th,x) => (HIDE_STATUS_RULE true hide (RW [STAR_ASSOC] th),x)) thms *)
  val _ = echo 1 "\nDefining tail-recursion\n\n"
  val _ = echo 2 (term_to_string tm1)
  val _ = echo 2 "\n\nwith side condition\n\n"
  val _ = echo 2 (term_to_string tm2)
  val _ = echo 2 "\n\n"
  val (tm,side_option) = (tm1, SOME tm2) 
  val (def,pre) = tailrec_define tm side_option 
  val def = CONJ pre def
  val thms = map (fn (th,i) => (RW [WORD_ADD_0] th, i = entry)) thms 
  val _ = echo 1 "Proving theorem relating code with function.\n"
  val res = prove_correspondence tools def thms
  val res = if not ((cdr o concl o SPEC_ALL) pre = ``T``) then res else
    RW [pre,SEP_CLAUSES] res

  val (res,def) = (!decompiler_finalise) (res,def)
  in (def,res) end;

fun prepare_for_reuse n (th,i,j) = let
  val prefix = ("s"^(int_to_string n)^"@") 
  in (n,(ABBREV_CALL prefix th,i,j),NONE) end;

fun decompile (tools :decompiler_tools) name (qcode :term quotation) = let
  val code = filter (fn x => not (x = "")) (quote_to_hex_list qcode)
  val inst_thms = derive_individual_specs tools code
  val segments = find_segments inst_thms
  val defs = TRUTH
  fun decompile_all_parts inst_thms defs [] prev = prev
    | decompile_all_parts inst_thms defs ((entry,exit)::segments) prev = let
      val part_name = if length segments = 0 then name else (name ^ int_to_string (length segments))
      val function_in_out = (NONE: (term * term) option)
      val (def,result) = decompile_part tools part_name inst_thms (entry,exit) function_in_out 
      val defs = REWRITE_RULE [GSYM CONJ_ASSOC] (CONJ def defs)
      val inst_thms = prepare_for_reuse entry (result,0,SOME exit) :: inst_thms
      in decompile_all_parts inst_thms defs segments (defs,result) end
  val (defs,result) = decompile_all_parts inst_thms defs segments (TRUTH,TRUTH)
  val i = snd (last segments)
  val _ = add_decompiled (name,result,i,SOME i)
  in (result,defs) end;

(*
val ((entry,exit)::segments) = segments
*)

val decompile_arm = decompile arm_tools
val decompile_ppc = decompile ppc_tools
val decompile_x86 = decompile x86_tools

fun basic_decompile (tools :decompiler_tools) name function_in_out (qcode :term quotation) = let
  val code = filter (fn x => not (x = "")) (quote_to_hex_list qcode)
  val inst_thms = derive_individual_specs tools code
  val (entry,exit) = last (find_segments inst_thms)
  val (defs,result) = decompile_part tools name inst_thms (entry,exit) function_in_out
  val _ = add_decompiled (name,result,exit,SOME exit)
  in (result,defs) end;

val basic_decompile_arm = basic_decompile arm_tools
val basic_decompile_ppc = basic_decompile ppc_tools
val basic_decompile_x86 = basic_decompile x86_tools

end;
