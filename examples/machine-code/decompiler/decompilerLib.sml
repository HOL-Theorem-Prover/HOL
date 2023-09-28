structure decompilerLib :> decompilerLib =
struct

open HolKernel boolLib bossLib Parse;

open listTheory wordsTheory pred_setTheory arithmeticTheory wordsLib pairTheory;
open set_sepTheory progTheory helperLib addressTheory;

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars addressTheory.address_grammars
end

val new_definition = Definition.new_definition (* not boolSyntax! *)

(* -------------------------------------------------------------------------- *)
(* Decompilation stages:                                                      *)
(*   1. derive SPEC theorem for each machine instruction, abbreviate code     *)
(*   2. extract control flow graph                                            *)
(*   3. for each code segment:                                                *)
(*        a. compose SPEC theorems for one-pass through the code              *)
(*        b. merge one-pass theorems into one theorem                         *)
(*        c. extract the function describing the code                         *)
(*   4. store and return result of decompilation                              *)
(* -------------------------------------------------------------------------- *)

(* decompiler's memory *)

val decompiler_memory = ref ([]:(string * (thm * int * int option)) list)
val decompiler_finalise = ref (I:(thm * thm -> thm * thm))
val code_abbreviations = ref ([]:thm list);
val abbreviate_code = ref false;
val user_defined_modifier = ref (fn (name:string) => fn (th:thm) => th);
val decompile_as_single_function = ref false;

val decompiler_set_pc = ref ((fn y => fn th => fail()) :int -> thm -> thm);

fun add_decompiled (name,th,code_len,code_exit) =
  (decompiler_memory := (name,(th,code_len,code_exit)) :: !decompiler_memory);

fun get_decompiled name =
  snd (hd (filter (fn (x,y) => x = name) (!decompiler_memory)))
  handle _ => fail();

fun add_code_abbrev thms = (code_abbreviations := thms @ !code_abbreviations);
fun set_abbreviate_code b = (abbreviate_code := b);
fun get_abbreviate_code () = !abbreviate_code;

fun add_modifier name f = let
  val current = !user_defined_modifier
  in user_defined_modifier := (fn x => if x = name then f else current x) end;
fun remove_all_modifiers () =
  user_defined_modifier := (fn (name:string) => fn (th:thm) => th);
fun modifier name th = (!user_defined_modifier) name th;


(* general set-up *)

val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9",
                        "r10","r11","r12","r13","r14","r15"];
val _ = set_echo 5;


(* -------------------------------------------------------------------------- *)
(* Various helper functions                                                   *)
(* -------------------------------------------------------------------------- *)

fun take n [] = []
  | take n (x::xs) = if n = 0 then [] else x :: take (n-1) xs

fun drop n [] = []
  | drop n (x::xs) = if n = 0 then x::xs else drop (n-1) xs

fun take_until p [] = []
  | take_until p (x::xs) = if p x then [] else x:: take_until p xs

fun diff xs ys = filter (fn x => not (mem x ys)) xs
fun subset xs ys = (diff xs ys = [])
fun same_set xs ys = subset xs ys andalso subset ys xs
fun disjoint xs ys = diff xs ys = xs

fun negate tm = dest_neg tm handle HOL_ERR e => mk_neg tm
fun the (SOME x) = x | the NONE = fail()

fun is_new_var v =
  (String.isPrefix "new@" o fst o dest_var) v handle HOL_ERR _ => false
fun dest_new_var tm = if not (is_new_var tm) then fail() else let
  val (s,ty) = dest_var tm
  in mk_var(implode (drop 4 (explode s)), ty) end

fun dest_tuple tm =
  let val (x,y) = pairSyntax.dest_pair tm in x :: dest_tuple y end
  handle HOL_ERR e => [tm];

fun mk_tuple_abs (v,tm) =
  if v ~~ ``()`` then
    (subst [mk_var("x",type_of tm) |-> tm]
       (inst [``:'a``|->type_of tm] ``\():unit.x:'a``))
 else pairSyntax.list_mk_pabs([v],tm)

fun dest_sep_cond tm =
  if (fst o dest_const o fst o dest_comb) tm = "cond"
  then snd (dest_comb tm) else fail();

fun n_times 0 f x = x | n_times n f x = n_times (n-1) f (f x)

fun replace_char c str =
  String.translate (fn x => if x = c then str else implode [x]);

fun REPLACE_CONV th tm = let
  val th = SPEC_ALL th
  val (i,j) = match_term ((fst o dest_eq o concl) th) tm
  in INST i (INST_TYPE j th) end

(* expands pairs
     ``(x,y,z) = f`` --> (x = FST f) /\ (y = FST (SND f)) /\ (z = ...) *)
fun expand_conv tm = let
  val cc = RAND_CONV (REPLACE_CONV (GSYM pairTheory.PAIR))
  val cc = cc THENC REPLACE_CONV pairTheory.PAIR_EQ
  val th = cc tm
  in CONV_RULE (RAND_CONV (RAND_CONV expand_conv)) th end
  handle HOL_ERR e => REFL tm

fun list_mk_pair xs = pairSyntax.list_mk_pair xs handle HOL_ERR e => ``()``
fun list_dest_pair tm = let val (x,y) = pairSyntax.dest_pair tm
 in list_dest_pair x @ list_dest_pair y end handle HOL_ERR e => [tm]

fun list_union [] xs = xs
  | list_union (y::ys) xs =
      if mem y xs then list_union ys xs else list_union ys (y::xs);

fun append_lists [] = [] | append_lists (x::xs) = x @ append_lists xs

val (no_tools:decompiler_tools) = let
  val no_jump = fn x => fail()
  val no_spec = fn x => fail()
  in (no_spec, no_jump, TRUTH, T) end

val curr_tools = ref no_tools;

fun set_tools tools = (curr_tools := tools);
fun get_tools () = !curr_tools

fun get_pc () = let val (_,_,_,x) = get_tools () in x end;
fun get_status () = let val (_,_,x,_) = get_tools () in x end;

fun get_output_list def = let
  val tm = (concl o last o CONJUNCTS o SPEC_ALL) def
  val (fm,tm) = dest_eq tm
  val t = (tm2ftree) tm
  fun ftree2res (FUN_VAL tm) = [tm]
    | ftree2res (FUN_IF (tm,x,y)) = ftree2res x @ ftree2res y
    | ftree2res (FUN_LET (tm,tn,x)) = ftree2res x
    | ftree2res (FUN_COND (tm,x)) = ftree2res x
  val res = filter (fn x => x !~ fm) (ftree2res t)
  val result = dest_tuple (hd res)
  fun deprime x = mk_var(replace_char #"'" "" (fst (dest_var x)), type_of x)
                  handle HOL_ERR e => x
  in pairSyntax.list_mk_pair(map deprime result) end;

val GUARD_THM =
  prove(``!m n x. GUARD n x = GUARD m x``, REWRITE_TAC [GUARD_def]);


(* -------------------------------------------------------------------------- *)
(* Implementation of STAGE 1                                                  *)
(* -------------------------------------------------------------------------- *)

(* formatting *)

val stack_terms = ([]):term list;

fun DISCH_ALL_AS_SINGLE_IMP th = let
  val th = RW [AND_IMP_INTRO] (DISCH_ALL th)
  in if is_imp (concl th) then th else DISCH ``T`` th end

fun replace_abbrev_vars tm = let
  fun f v = v |-> mk_var((Substring.string o hd o tl o
                          Substring.tokens (fn x => x = #"@") o
                          Substring.full o fst o dest_var) v, type_of v)
            handle HOL_ERR e => v |-> v
  in subst (map f (free_vars tm)) tm end

fun name_for_abbrev p tm = let
  val x = get_sep_domain tm
  in first (fn t => rator t ~~ x) p |> rand |> dest_var |> fst end
  handle HOL_ERR _ =>
  "v" ^ (int_to_string (Arbnum.toInt(numSyntax.dest_numeral(cdr (car tm)))))
  handle HOL_ERR e =>
  if (fst (dest_const (car tm)) = "tT") handle HOL_ERR e => false then "k" else
  if is_const (cdr (car tm)) andalso is_const(car (car tm))
     handle HOL_ERR e => false then
    (to_lower o fst o dest_const o cdr o car) tm
  else if can (match_term ``(f ((n2w n):'a word) (x:'c)):'d``) tm then
    "r" ^ ((int_to_string o numSyntax.int_of_term o cdr o cdr o car) tm)
  else
    fst (dest_var (repeat cdr tm)) handle HOL_ERR e =>
    fst (dest_var (find_term is_var tm)) handle HOL_ERR e =>
    fst (dest_const (repeat car (get_sep_domain tm)));

fun raw_abbreviate2 (var_name,y,tm) th = let
  val y = mk_eq(mk_var(var_name,type_of y),y)
  val cc = UNBETA_CONV tm
           THENC (RAND_CONV) (fn t => GSYM (ASSUME y))
           THENC BETA_CONV
  val th = CONV_RULE (RAND_CONV cc) th
  in th end;

fun raw_abbreviate (var_name,y,tm) th = let
  val y = mk_eq(mk_var(var_name,type_of y),y)
  val cc = UNBETA_CONV tm
           THENC (RAND_CONV o RAND_CONV) (fn t => GSYM (ASSUME y))
           THENC BETA_CONV
  val th = CONV_RULE (RAND_CONV cc) th
  in th end;

fun abbreviate (var_name,tm) th = raw_abbreviate (var_name,cdr tm,tm) th

fun ABBREV_POSTS dont_abbrev_list prefix th = let
  fun dont_abbrev tm = tmem tm (dont_abbrev_list @ stack_terms)
  fun next_abbrev p [] = fail()
    | next_abbrev p (tm::xs) =
    if (is_var (cdr tm) andalso
       (name_for_abbrev p tm = fst (dest_var (cdr tm))))
       handle HOL_ERR e => false then next_abbrev p xs else
    if (prefix ^ (name_for_abbrev p tm) = fst (dest_var (cdr tm)))
       handle HOL_ERR e => false then next_abbrev p xs else
    if can dest_sep_hide tm then next_abbrev p xs else
    if dont_abbrev (car tm) then next_abbrev p xs else
      (prefix ^ name_for_abbrev p tm,tm)
  val (th,b) = let
    val (_,p,_,q) = dest_spec (concl th)
    val p = list_dest dest_star p
            |> filter (fn tm => (is_var o rand) tm handle HOL_ERR _ => false)
    val xs = list_dest dest_star q
    val th = abbreviate (next_abbrev p xs) th
    in (th,true) end handle HOL_ERR e => (th,false) handle Empty => (th,false)
  in if b then ABBREV_POSTS dont_abbrev_list prefix th else th end;

fun ABBREV_PRECOND prefix th = let
  val th = RW [SPEC_MOVE_COND] (SIMP_RULE (bool_ss++sep_cond_ss) [] th)
  val tm = (fst o dest_imp o concl) th
  val v = mk_var(prefix^"cond",``:bool``)
  val thx = SYM (BETA_CONV (mk_comb(mk_abs(v,v),tm)))
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (fn tm => thx)) th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] (RW [precond_def] (UNDISCH th))
  in th end handle HOL_ERR e => th handle Empty => th;

fun ABBREV_STACK prefix th = let
  val (_,p,_,q) = dest_spec (concl th)
  val f = find_term (fn tm => tmem (car tm) stack_terms
                              handle HOL_ERR _ => false)
  val s_pre = f p
  val s_post = f q
  val xs = map (fn {redex=x1, residue=x2} => (x1,x2))
               (fst (match_term s_pre s_post))
  val th1 = CONV_RULE (UNBETA_CONV s_post) th
  val ys = map (fn (x1,x2) =>
                  mk_eq(mk_var(prefix ^ fst (dest_var x1), type_of x1),x2)) xs
  val rw = map (GSYM o ASSUME) ys
  val cs = map (fn th => fn tm =>
                  if tm ~~ fst (dest_eq (concl th)) then th else NO_CONV tm) rw
  fun each [] = ALL_CONV | each (c::cs) = c ORELSEC each cs
  val th1 = CONV_RULE (RAND_CONV (DEPTH_CONV (each cs)) THENC BETA_CONV) th1
  in th1 end handle HOL_ERR _ => th

fun ABBREV_ALL dont_abbrev_list prefix th = let
  val th = ABBREV_POSTS dont_abbrev_list prefix th
  val th = ABBREV_STACK prefix th
  val th = ABBREV_PRECOND prefix th
  in th end;

fun ABBREV_CALL prefix th = let
  val (_,_,_,q) = (dest_spec o concl) th
  val (x,tm) = pairSyntax.dest_anylet q
  val (x,y) = hd x
  val ys = map (fn v => mk_var(prefix^(fst (dest_var v)),type_of v))
               (dest_tuple x)
  val thi = ASSUME (mk_eq(pairSyntax.list_mk_pair ys, y))
  val thj = RW1 [LET_DEF] (GSYM thi)
  val th = CONV_RULE (RAND_CONV (RAND_CONV (fn tm => thj))) (RW [LET_DEF] th)
  val th = RW [FST,SND] (PairRules.PBETA_RULE (RW [LET_DEF] th))
  in ABBREV_PRECOND prefix th end
  handle HOL_ERR e => ABBREV_PRECOND prefix th
  handle Empty => ABBREV_PRECOND prefix th;

fun UNABBREV_ALL th = let
  fun remove_abbrev th = let
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) expand_conv) th
    val th = RW [GSYM AND_IMP_INTRO] th
    val (x,y) = (dest_eq o fst o dest_imp o concl) th
    in MP (INST [x|->y] th) (REFL y) end
    handle HOL_ERR e =>
       UNDISCH (CONV_RULE ((RATOR_CONV o RAND_CONV) BETA_CONV) th)
       handle HOL_ERR e => UNDISCH th
  in repeat remove_abbrev (DISCH_ALL th) end;


(* derive SPEC theorems *)

fun pair_apply f ((th1,x1:int,x2:int option),NONE) = ((f th1,x1,x2),NONE)
  | pair_apply f ((th1,x1,x2),SOME (th2,y1:int,y2:int option)) =
      ((f th1,x1,x2),SOME (f th2,y1,y2))

fun jump_apply f NONE = NONE | jump_apply f (SOME x) = SOME (f x);

fun pair_jump_apply (f:int->int) ((th1,x1:int,x2:int option),NONE) =
      ((th1,x1,jump_apply f x2),NONE)
  | pair_jump_apply f ((th1:thm,x1,x2),SOME (th2:thm,y1:int,y2:int option)) =
      ((th1,x1,jump_apply f x2),SOME (th2,y1,jump_apply f y2));

fun introduce_guards thms = let
  val pattern = (fst o dest_eq o concl o SPEC_ALL) cond_def
(*
  val (n,(th1,i1,j1),SOME (th2,i2,j2)) = el 8 res
*)
  fun intro (n,(th1,i1,j1),NONE) = (n,(th1,i1,j1),NONE)
    | intro (n,(th1,i1,j1),SOME (th2,i2,j2)) = let
    val t1 = cdr (find_term (can (match_term pattern)) (concl th1))
    val t2 = cdr (find_term (can (match_term pattern)) (concl th2))
    val h = RW [SPEC_MOVE_COND] o SIMP_RULE (bool_ss++sep_cond_ss) []
    val (th1,th2) = (h th1,h th2)
    val tm1 = (mk_neg o fst o dest_imp o concl) th1
    val tm2 = (fst o dest_imp o concl) th2
    val lemma =
       auto_prove "introduce_guards" (mk_eq(tm2,tm1),SIMP_TAC std_ss [])
    val th2 =
       CONV_RULE ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [lemma])) th2
    val rw = SPEC (numSyntax.term_of_int n) GUARD_def
    val f1 =
       CONV_RULE ((RATOR_CONV o RAND_CONV) (PURE_ONCE_REWRITE_CONV [GSYM rw]))
    val f2 = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
                           (PURE_ONCE_REWRITE_CONV [GSYM rw]))
    val (th1,th2) = if is_neg t1 then (f2 th1,f1 th2) else (f1 th1, f2 th2)
    val h2 = RW [GSYM SPEC_MOVE_COND]
    val (th1,th2) = (h2 th1,h2 th2)
    in (n,(th1,i1,j1),SOME (th2,i2,j2)) end
  val thms = map intro thms
  in thms end

fun derive_individual_specs tools (code:string list) = let
  val (f,_,hide_th,pc) = tools
  fun get_model_status_list th =
    (map dest_sep_hide o list_dest dest_star o snd o dest_eq o concl) th
    handle HOL_ERR e => []
  val dont_abbrev_list = pc :: get_model_status_list hide_th
  val delete_spaces = (implode o filter (fn x => not(x = #" ")) o explode)
  fun list_find name [] = fail ()
    | list_find name ((x,y)::xs) = if name = x then y else list_find name xs
  fun get_specs (instruction,(n,ys)) =
    if String.isPrefix "insert:" (delete_spaces instruction) then let
      val name = delete_spaces instruction
      val name = substring(name,7,length (explode name) - 7)
      val (th,i,j) = list_find name (!decompiler_memory)
      val th = RW [sidecond_def,hide_th,STAR_ASSOC] th
      val th = ABBREV_CALL ("new@") th
      val _ = echo 1 "  (insert command)\n"
      in (n+1,(ys @ [(n,(th,i,j),NONE)])) end
    else let
      val _ = echo 1 ("  "^instruction^":")
      val i = int_to_string n
      val g = RW [precond_def] o ABBREV_ALL dont_abbrev_list ("new@")
      val (x,y) = pair_apply g (f instruction)
      val _ = echo 1 ".\n"
      in (n+1,(ys @ [(n,x,y)])) end
  val _ = echo 1 "\nDeriving theorems for individual instructions.\n"
(*
  val instruction = el 1 code
  val ((th,_,_),_) = f instruction
  val th = renamer th
  val prefix = "foo@"
*)
  val res = snd (foldl get_specs (1,[]) code)
  val res = introduce_guards res
  fun calc_addresses i [] = []
    | calc_addresses i ((n:int,(th1:thm,l1,j1),y)::xs)  = let
    val (x,y) = pair_jump_apply (fn j => i+j) ((th1,l1,j1),y)
    in (i,x,y) :: calc_addresses (i+l1) xs end
  val res = calc_addresses 0 res
  val _ = echo 1 "\n"
  in res end;

fun inst_pc_var tools thms = let
  fun triple_apply f (y,(th1,x1:int,x2:int option),NONE) =
        (y,(f y th1,x1,x2),NONE)
    | triple_apply f (y,(th1,x1,x2),SOME (th2,y1:int,y2:int option)) =
        (y,(f y th1,x1,x2),SOME (f y th2,y1,y2))
  val i = [mk_var("pc",``:word32``) |-> mk_var("p",``:word32``),
           mk_var("pc",``:word64``) |-> mk_var("p",``:word64``),
           mk_var("eip",``:word32``) |-> mk_var("p",``:word32``),
           mk_var("rip",``:word64``) |-> mk_var("p",``:word64``)]
  val (_,_,_,pc) = tools
  val ty = (hd o snd o dest_type o type_of) pc
  fun f y th = (!decompiler_set_pc) y th handle HOL_ERR _ => let
    val aa = (hd o tl o snd o dest_type) ty
    val th = INST i th
    val (_,p,_,_) = dest_spec (concl th)
    val pattern = inst [``:'a``|->aa] ``(p:'a word) + n2w n``
    val new_p =
       subst [mk_var("n",``:num``)|-> numSyntax.mk_numeral (Arbnum.fromInt y)]
         pattern
    val th = INST [mk_var("p",type_of new_p)|->new_p] th
    val (_,_,_,q) = dest_spec (concl th)
    val tm = find_term (fn tm => car tm ~~ pc handle HOL_ERR e => false) q
    val cc =
       SIMP_CONV std_ss [word_arith_lemma1,word_arith_lemma3,word_arith_lemma4]
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) cc) th
    val thi = QCONV cc tm
    in PURE_REWRITE_RULE [thi,WORD_ADD_0] th end;
  in map (triple_apply f) thms end

fun UNABBREV_CODE_RULE th = let
  val rw = (!code_abbreviations)
  val c = REWRITE_CONV rw THENC
          SIMP_CONV std_ss [word_arith_lemma1] THENC
          REWRITE_CONV [INSERT_UNION_EQ,UNION_EMPTY]
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) c) th
  in th end;

val ABBBREV_CODE_LEMMA = prove(
  ``!a (x :('a, 'b, 'c) processor) p c q.
      (a ==> SPEC x p c q) ==> !d. c SUBSET d ==> a ==> SPEC x p d q``,
  REPEAT STRIP_TAC THEN RES_TAC THEN IMP_RES_TAC SPEC_SUBSET_CODE);

fun abbreviate_code name thms = let
  fun extract_code (_,(th,_,_),_) =
     let val (_,_,c,_) = dest_spec (concl th) in c end
  val cs = map extract_code thms
  val ty = (hd o snd o dest_type o type_of o hd) cs
  val tm = foldr pred_setSyntax.mk_union (pred_setSyntax.mk_empty ty) cs
  val cth = QCONV (PURE_REWRITE_CONV [INSERT_UNION_EQ,UNION_EMPTY]) tm
  val c = (cdr o concl) cth
  val (_,(th,_,_),_) = hd thms
  val (m,_,_,_) = dest_spec (concl th)
  val model_name = (to_lower o implode o take_until (fn x => x = #"_") o
                    explode o fst o dest_const) m
  val x = list_mk_pair (free_vars c)
  val def_name = name ^ "_" ^ model_name
  val v = mk_var(def_name,type_of(mk_pabs(x,c)))
  val code_def = new_definition(def_name ^ "_def",mk_eq(mk_comb(v,x),c))
  val _ = add_code_abbrev [code_def]
  fun triple_apply f (y,(th1,x1:int,x2:int option),NONE) =
        (y,(f th1,x1,x2),NONE)
    | triple_apply f (y,(th1,x1,x2),SOME (th2,y1:int,y2:int option)) =
        (y,(f th1,x1,x2),SOME (f th2,y1,y2))
  val code_thm = CONV_RULE (RAND_CONV (fn _ => GSYM cth)) (SPEC_ALL code_def)
  fun foo th = let
    val thi = MATCH_MP ABBBREV_CODE_LEMMA (DISCH_ALL_AS_SINGLE_IMP th)
    val thi = SPEC ((fst o dest_eq o concl o SPEC_ALL) code_def) thi
    val goal = (fst o dest_imp o concl) thi
    val lemma = auto_prove "abbreviate_code" (goal,
        REPEAT (REWRITE_TAC [code_thm,SUBSET_DEF,IN_UNION] THEN REPEAT STRIP_TAC
                THEN ASM_REWRITE_TAC [] THEN (fn _ => fail()))
        THEN REWRITE_TAC [EMPTY_SUBSET]
        THEN REWRITE_TAC [SUBSET_DEF,IN_INSERT,IN_UNION,NOT_IN_EMPTY,code_def]
        THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [])
    val thi =
       UNDISCH_ALL (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] (MP thi lemma))
    in thi end
  val thms = map (triple_apply foo) thms
  in thms end

fun stage_1 name tools code =
  let
     val thms = derive_individual_specs tools code
     val thms = inst_pc_var tools thms
     val thms = abbreviate_code name thms
  in
     thms
  end;


(* -------------------------------------------------------------------------- *)
(* Implementation of STAGE 2                                                  *)
(* -------------------------------------------------------------------------- *)

fun extract_graph thms = let
  fun extract_jumps (i,(_,_,j),NONE) = [(i,j)]
    | extract_jumps (i,(_,_,j),SOME (_,_,k)) = [(i,j),(i,k)]
  val jumps = append_lists (map extract_jumps thms)
  in jumps end;

fun all_distinct [] = []
  | all_distinct (x::xs) = x :: all_distinct (filter (fn z => not (x = z)) xs)

fun drop_until P [] = []
  | drop_until P (x::xs) = if P x then x::xs else drop_until P xs

fun jumps2edges jumps = let
  fun h (i,NONE) = []
    | h (i,SOME j) = [(i,j)]
  in append_lists (map h jumps) end;

fun extract_loops jumps = let
  (* find all possible paths *)
  val edges = jumps2edges jumps
  fun all_paths_from edges i prefix = let
    fun f [] = []
      | f ((k,j)::xs) = if i = k then j :: f xs else f xs
    val next = all_distinct (f edges)
    val prefix = prefix @ [i]
    val xs = map (fn x => if mem x prefix then [prefix @ [x]] else
                          all_paths_from edges x prefix) next
    val xs = if xs = [] then [[prefix]] else xs
    in append_lists xs end
  val paths = all_paths_from edges 0 []
  (* get looping points *)
  fun is_loop xs = mem (last xs) (butlast xs)
  val loops = all_distinct (map last (filter is_loop paths))
  (* find loop bodies and tails *)
  fun loop_body_tail i = let
    val bodies = filter (fn xs => last xs = i) paths
    val bodies = filter is_loop bodies
    val bodies = map (drop_until (fn x => x = i) o butlast) bodies
    val bodies = all_distinct (append_lists bodies)
    val tails = filter (fn xs => mem i xs andalso not (last xs = i)) paths
    val tails = map (drop_until (fn x => x = i)) tails
    in (i,bodies,tails) end
  val summaries = map loop_body_tail loops
  (* clean loop tails *)
  fun clean_tails (i,xs,tails) = let
    val tails = map (drop_until (fn x => not (mem x xs))) tails
    val tails = filter (fn xs => not (xs = [])) tails
    in (i,xs,tails) end
  val zs = map clean_tails summaries
  (* merge combined loops *)
  val zs = map (fn (x,y,z) => ([x],y,z)) zs
  fun find_and_merge zs = let
    val ls = append_lists (map (fn (x,y,z) => x) zs)
    val qs = map (fn (x,y,z) => (x,y,map hd z)) zs
    fun f ys = filter (fn x => mem x ls andalso (not (mem x ys)))
    val qs = map (fn (x,y,z) => (x,all_distinct (f x y @ f x z))) qs
    fun cross [] ys = []
      | cross (x::xs) ys = map (fn y => (x,y)) ys @ cross xs ys
    val edges = append_lists (map (fn (x,y) => cross x y) qs)
    val paths = map (fn i => all_paths_from edges i []) ls
    val goals = map (fn (x,y) => (y,x)) edges
    fun sat_goal ((i,j),path) = (hd path = i) andalso (mem j (tl path))
    val (i,j) = fst (hd (filter sat_goal (cross goals (append_lists paths))))
    val (p1,q1,x1) = hd (filter (fn (x,y,z) => mem i x) zs)
    val (p2,q2,x2) = hd (filter (fn (x,y,z) => mem j x) zs)
    val (p,q,x) = (p1 @ p2, all_distinct (q1 @ q2), x1 @ x2)
    val zs =
       (p,q,x) :: filter (fn (x,y,z) => not (mem i x) andalso not (mem j x)) zs
    val zs = map clean_tails zs
    in zs end
  val zs = repeat find_and_merge zs
  (* attempt to find common exit point *)
  fun mem_all x [] = true
    | mem_all x (xs::xss) = mem x xs andalso mem_all x xss
  fun find_exit_points (x,y,z) = let
    val q = hd (filter (fn x => mem_all x (tl z)) (hd z))
    in (x,[q]) end handle Empty => (x,all_distinct (map hd z))
  val zs = map find_exit_points zs
  (* finalise *)
  val exit = (all_distinct o map last o filter (not o is_loop)) paths
  val zero = ([0],exit)
  val zs = if filter (fn (x,y) => mem 0 x andalso subset exit y) zs = []
              then zs @ [zero]
           else zs
  fun list_before x y [] = true
    | list_before x y (z::zs) = if z = y then false else
                                if z = x then true else list_before x y zs
  fun compare (xs,_) (ys,_) = let
    val x = hd xs
    val y = hd ys
    val p = hd (filter (fn xs => mem x xs andalso mem y xs) paths)
    in not (list_before x y p) end handle Empty => false
  val loops = sort compare zs
  (* sort internal  *)
  val int_sort = sort (fn x => fn (y:int) => x <= y)
  val loops = map (fn (xs,ys) => (int_sort xs, int_sort ys)) loops
  (* deal with option to return result as a single function *)
  val loops = if not (!decompile_as_single_function) then loops else let
    val entry = all_distinct (append_lists (map fst loops))
    val exit = diff (all_distinct (append_lists (map snd loops))) entry
    in [(sort (fn x => fn y => (x <= y)) entry,exit)] end
  (* TODO: final states should still be optimised... *)
  in loops end;

fun stage_12 name tools code =
   let
      val thms = stage_1 name tools code
      val jumps = extract_graph thms
      val loops = extract_loops jumps
   in
      (thms, loops)
   end;


(* -------------------------------------------------------------------------- *)
(* Implementation of STAGE 3                                                  *)
(* -------------------------------------------------------------------------- *)

(* STAGE 3, part a ---------------------------------------------------------- *)

local val varname_counter = ref 1 in
  fun varname_reset () = (varname_counter := 1);
  fun varname_next () = let
    val v = !varname_counter
    val _ = (varname_counter := v+1)
    in v end
end;

(* functions for composing SPEC theorems *)

fun replace_new_vars v th = let
  fun mk_new_var prefix v = let
    val (n,ty) = dest_var v
    val _ = if String.isPrefix "new@" n then () else fail()
    in mk_var (prefix ^ "@" ^ (implode o drop 4 o explode) n, ty) end
  fun rename_new tm =
    if is_comb tm
       then (RATOR_CONV rename_new THENC RAND_CONV rename_new) tm
    else if not (is_abs tm)
       then ALL_CONV tm
    else let
      val (x,y) = dest_abs tm
      val conv = ALPHA_CONV (mk_new_var v x) handle HOL_ERR e => ALL_CONV
      in (conv THENC ABS_CONV rename_new) tm end
  val th = GEN_ALL (DISCH_ALL th)
  val th = CONV_RULE rename_new th
  val th = UNDISCH_ALL (SPEC_ALL th)
  in th end;

fun SPEC_COMPOSE th1 th2 = let
  (* replace "new@..." variables with fresh numbered variables *)
  val th2a = replace_new_vars ("s" ^ int_to_string (varname_next ())) th2
  in SPEC_COMPOSE_RULE [th1,th2a] end;

fun number_GUARD (x,y,z) = let
  val rw = SPEC (numSyntax.term_of_int (varname_next ())) GUARD_THM
  fun f (th1,y1,y2) = (RW1[rw]th1,y1,y2)
  fun apply_option g NONE = NONE
    | apply_option g (SOME x) = SOME (g x)
  in (x,f y,apply_option f z) end;

(* multi-entry/exit preformatting *)

fun format_for_multi_entry entry thms = let
  val _ = if length entry = 1 then fail() else ()
  val pc_tm = get_pc()
  val pos = mk_var("pos",``:num``)
  val mk_num = numSyntax.mk_numeral o Arbnum.fromInt
  fun mk_pos i =
     subst [mk_var("n",``:num``) |-> mk_num i] ``p + (n2w n):word32``
  fun foo [] n = [] | foo (y::ys) n = n :: foo ys (n+1)
  val xs = zip (map mk_num (foo entry 0)) (map mk_pos entry)
  fun mk [] = fail()
    | mk [(x,y)] = y
    | mk ((x,y)::xs) = mk_cond(mk_eq(pos,x),y,mk xs)
  val tm = mk xs
  val case_list = map (fn (x,y) => mk_eq(pos,x)) xs
  val format =
    mk_imp(``GUARD 0 (pos = k:num)``,
           mk_eq(mk_comb(pc_tm,mk_var("t1",``:word32``)),
                 mk_comb(pc_tm,mk_var("t2",``:word32``))))
  val format = subst [``t2:word32``|->tm] format
  fun mk_sub (x,y) = subst [``k:num``|->x, ``t1:word32``|->y] format
  fun mk_goals [] rest = fail()
    | mk_goals [(x,y)] rest =
       [mk_conj(mk_imp(rest,snd (dest_imp (mk_sub (x,y)))),mk_sub (x,y))]
    | mk_goals ((x,y)::xs) rest = let
       val xy = mk_sub (x,y)
       val r = mk_neg((cdr o car) xy)
       in mk_conj(mk_imp(rest,xy),xy) :: mk_goals xs (mk_conj(rest,r)) end
  val goals = mk_goals xs T
  fun two_conj th = let
    val xs = CONJUNCTS th
    in if length xs = 1 then (hd xs, hd xs) else (el 1 xs, el 2 xs) end
  val ys =
     map (fn goal => (two_conj o RW[AND_IMP_INTRO,GSYM CONJ_ASSOC,WORD_ADD_0])
                       (prove(goal,SIMP_TAC std_ss [GUARD_def]))) goals
  val posts = map snd ys
  val pres = map fst ys
  val posts =
     map (RW [GUARD_def] o INST [pos|->mk_var("s10000@pos",type_of pos)]) posts
  fun RW_CONV [] tm = NO_CONV tm
    | RW_CONV (th::xs) tm =
       if fst (dest_eq (concl th)) ~~ tm then th else RW_CONV xs tm
       handle HOL_ERR _ => NO_CONV tm
  fun process th = let
    val th = CONV_RULE (PRE_CONV (DEPTH_CONV (RW_CONV (map UNDISCH pres)))) th
    val th = CONV_RULE (POST_CONV (DEPTH_CONV (RW_CONV (map UNDISCH posts)))) th
    val th = UNDISCH (DISCH_ALL_AS_SINGLE_IMP th)
    in th end
  fun apply f (k,(th1,i1,j1),NONE) = (k,(f th1,i1,j1),NONE)
    | apply f (k,(th1,i1,j1),SOME (th2,i2,j2)) =
        (k,(f th1,i1,j1),SOME (f th2,i2,j2))
  val thms = map (apply process) thms
  in (case_list,thms) end handle HOL_ERR _ => ([],thms);

(* functions for deriving one-pass theorems *)

datatype mc_tree =
    LEAF of thm * int
  | SEQ of term list * mc_tree
  | BRANCH of term * mc_tree * mc_tree;

fun basic_find_composition th1 (th2,l2,j2) = let
  val th1 = modifier "pre" th1
  val th2 = modifier "pre" th2
  val th = remove_primes (SPEC_COMPOSE th1 th2) handle HOL_ERR e =>
           remove_primes (SPEC_COMPOSE th1 (UNABBREV_ALL th2))
  val th = modifier "post" th
  val th = RW [WORD_CMP_NORMALISE] th
  val th = RW [GSYM WORD_NOT_LOWER, GSYM WORD_NOT_LESS] th
  fun h x = (fst o dest_eq) x handle e => (fst o dest_abs o car) x
  fun f [] ys = ys | f (x::xs) ys = f xs (h x :: ys handle e => ys)
  val th2_hyps = f (hyp th2) []
  fun g tm = tmem (h tm) th2_hyps handle e => false
  val lets = filter g (hyp th)
  in ((th,l2,j2),lets) end

fun find_cond_composition th1 NONE = fail()
  | find_cond_composition th1 (SOME (th2,l2,j2)) = let
  val th = RW [SPEC_MOVE_COND] th2
  val th = if Teq (concl th) then fail() else th
  val th = if not (is_imp (concl th)) then th else
             CONV_RULE
                ((RATOR_CONV o RAND_CONV)
                    (ONCE_REWRITE_CONV [GSYM CONTAINER_def])) th
  val th = RW [GSYM SPEC_MOVE_COND] th
  val ((th,l,j),lets) = basic_find_composition th1 (th,l2,j2)
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [SEP_CLAUSES] th
  val th =
     SIMP_RULE std_ss [SPEC_MOVE_COND,GSYM AND_IMP_INTRO,SEP_EXISTS_COND] th
  fun imps tm xs =
     let val (x,y) = dest_imp tm in imps y (x::xs) end handle e => xs
  fun is_CONTAINER tm =
     (fst o dest_const o car) tm = "CONTAINER" handle e => false
  val xs = filter is_CONTAINER (imps (concl th) [])
  val th = RW [GSYM SPEC_MOVE_COND,CONTAINER_def] th
  in let val cond = snd (dest_comb (hd xs)) in
     let val cond = dest_neg cond in (cond,(th,l,j)) end
     handle e => (mk_neg cond,(th,l,j)) end
     handle e => (``F:bool``,(th,l,j)) end;

fun remove_guard tm =
  (cdr o concl o REWRITE_CONV [GUARD_def]) tm handle UNCHANGED => tm;

fun find_first i [] = fail()
  | find_first i ((x,y,z)::xs) = if i = x then (x,y,z) else find_first i xs

fun tree_composition (th,i:int,thms,entry,exit,conds,firstTime) =
  if mem i entry andalso not firstTime then LEAF (th,i) else
  if mem i exit then LEAF (th,i) else let
    val (_,thi1,thi2) = number_GUARD (find_first i thms)
    in let (* try composing second branch *)
       val (cond,(th2,_,i2)) = find_cond_composition th thi2
       val cond' = remove_guard cond
       in if tmem (negate cond') conds
          then (* case: only second branch possible *)
               tree_composition (th2,the i2,thms,entry,exit,conds,false)
          else if tmem cond' conds then fail()
          else (* case: both branches possible *) let
            val ((th1,_,i1),lets) = basic_find_composition th thi1
            val t1 = tree_composition
                       (th1,the i1,thms,entry,exit,cond'::conds,false)
            val t2 = tree_composition
                       (th2,the i2,thms,entry,exit,negate cond'::conds,false)
            val t1 = if length lets = 0 then t1 else SEQ (lets,t1)
            in BRANCH (cond,t1,t2) end end
       handle e => (* case: only first branch possible *) let
       val ((th,_,i),lets) = basic_find_composition th thi1
       val result = tree_composition (th,the i,thms,entry,exit,conds,false)
       in if length lets = 0 then result else SEQ (lets,result) end end

fun map_spectree f (LEAF (thm,i)) = LEAF (f thm,i)
  | map_spectree f (SEQ (x,t)) = SEQ(x, map_spectree f t)
  | map_spectree f (BRANCH (j,t1,t2)) =
      BRANCH (j, map_spectree f t1, map_spectree f t2)

fun merge_entry_points [] ts = hd ts
  | merge_entry_points [x] ts = hd ts
  | merge_entry_points (x::xs) ts = let
      val t1 = merge_entry_points xs (tl ts)
      in BRANCH (mk_comb(``GUARD 0``,x), hd ts, t1) end

fun generate_spectree thms (entry,exit) = let
  val _ = varname_reset ()
  val (_,(th,_,_),_) = hd thms
  val hide_th = get_status()
  fun apply_to_th f (i,(th,k,l),NONE) = (i,(f th,k,l),NONE)
    | apply_to_th f (i,(th,k,l),SOME (th2,k2,l2)) =
        (i,(f th,k,l),SOME (f th2,k2,l2))
  val thms = map (apply_to_th (RW [hide_th])) thms
  val (case_list,thms) = format_for_multi_entry entry thms
  val (_,(th,_,_),_) = hd thms
  val (m,_,_,_) = dest_spec (concl th)
  val (default_th,is,conds,firstTime) =
     (Q.SPECL [`emp`,`{}`] (ISPEC m SPEC_REFL),entry,[]:term list,true)
  val i = hd is
  val _ = echo 1 "Composing,"
  val ts = map (fn i => let
             val th = modifier ("shape " ^ int_to_string i) default_th
             val t = tree_composition (th,i,thms,entry,exit,conds,firstTime)
             in (i,t) end) is
  val t = merge_entry_points case_list (map snd ts)
  val t = if not (is_eq (concl (SPEC_ALL hide_th))) then t
          else map_spectree (HIDE_STATUS_RULE true hide_th) t
  val t = map_spectree (modifier "spec") t
  in t end;

(*
val in_post = true
fun spectree_leaves (LEAF (thm,i)) = [thm]
  | spectree_leaves (SEQ (x,t)) = spectree_leaves t
  | spectree_leaves (BRANCH (j,t1,t2)) = spectree_leaves t1 @ spectree_leaves t2
val th = el 2 (spectree_leaves t)
*)


(* STAGE 3, part b ---------------------------------------------------------- *)

(* merge spectree theorems *)

fun strip_tag v = let
  val vs = (drop_until (fn x => x = #"@") o explode o fst o dest_var) v
  in if vs = [] then (fst o dest_var) v else implode (tl vs) end

fun read_tag v = let
  val xs = (explode o fst o dest_var) v
  val vs = take_until (fn x => x = #"@") xs
  in if length vs = length xs then "" else implode vs end

fun ABBREV_NEW th = let
  val pc = get_pc ()
  val ty = (hd o snd o dest_type o type_of) pc
  val tm =
    find_term (can (match_term (mk_comb(pc,genvar(ty))))) (cdr (concl th))
  val th = abbreviate ("new@p",tm) th
  val ws = (filter (not o is_new_var) o free_vars o cdr o concl) th
  fun one(v,th) = raw_abbreviate2 ("new@" ^ strip_tag v,v,v) th
  val th = foldr one th ws
  val th =
    UNDISCH (RW [SPEC_MOVE_COND,AND_IMP_INTRO,GSYM CONJ_ASSOC] (DISCH_ALL th))
  in th end

fun remove_tags tm =
  subst (map (fn v => v |-> mk_var(strip_tag v,type_of v)) (free_vars tm)) tm

fun list_dest_sep_exists tm = let
  val vs = list_dest dest_sep_exists tm
  in (butlast vs, last vs) end;

fun prepare_sep_disj_posts th1 th2 = let
  val (_,_,_,q1) = dest_spec (concl th1)
  val (_,_,_,q2) = dest_spec (concl th2)
  in if can dest_sep_disj q1 orelse can dest_sep_disj q2 then let
       val th1 = if can dest_sep_disj q2 then
                   SPEC (snd (dest_sep_disj q2)) (MATCH_MP SPEC_ADD_DISJ th1)
                 else th1
       val th2 = if can dest_sep_disj q1 then
                   SPEC (snd (dest_sep_disj q1)) (MATCH_MP SPEC_ADD_DISJ th2)
                 else th2
       val f =
          RW [SEP_CLAUSES] o
          CONV_RULE ((RAND_CONV o RAND_CONV)
                     (SIMP_CONV std_ss [AC SEP_DISJ_ASSOC SEP_DISJ_COMM])) o
          RW [SEP_DISJ_ASSOC]
       val th1 = f th1
       val th2 = f th2
       in (th1,th2) end
     else (th1,th2) end;

val merge_mem = ref (T,TRUTH,TRUTH);
(*
val (guard,th1,th2) = (!merge_mem);
*)

fun MERGE guard th1 th2 = let
  (* fill in preconditions *)
  val th1 = remove_primes th1
  val th2 = remove_primes th2
  val p = get_pc ()
  val (_,p1,_,q1) = dest_spec (concl th1)
  val (_,p2,_,q2) = dest_spec (concl th2)
  val (qs1,q1) = list_dest_sep_exists q1
  val (qs2,q2) = list_dest_sep_exists q2
  fun fst_sep_disj tm = fst (dest_sep_disj tm) handle HOL_ERR _ => tm
  val xs1 = filter (fn x => p !~ get_sep_domain x)
                   (list_dest dest_star (fst_sep_disj q1))
  val xs2 = filter (fn x => p !~ get_sep_domain x)
                   (list_dest dest_star (fst_sep_disj q2))
  val xs1 = map remove_tags xs1
  val xs2 = map remove_tags xs2
  val zs1 = map get_sep_domain xs1
  val zs2 = map get_sep_domain xs2
  val ys1 = filter (fn x => not (tmem (get_sep_domain x) zs1)) xs2
  val ys2 = filter (fn x => not (tmem (get_sep_domain x) zs2)) xs1
  val th1 = SPEC (list_mk_star ys1 (type_of p1)) (MATCH_MP SPEC_FRAME th1)
  val th2 = SPEC (list_mk_star ys2 (type_of p2)) (MATCH_MP SPEC_FRAME th2)
  val th1 = SIMP_RULE std_ss [SEP_CLAUSES,STAR_ASSOC] th1
  val th2 = SIMP_RULE std_ss [SEP_CLAUSES,STAR_ASSOC] th2
  (* unhide relevant preconditions *)
  val (_,p1,_,q1) = dest_spec (concl th1)
  val (_,p2,_,q2) = dest_spec (concl th2)
  val (ps1,p1) = list_dest_sep_exists p1
  val (ps2,p2) = list_dest_sep_exists p2
  val xs1 = filter (fn x => p !~ get_sep_domain x) (list_dest dest_star p1)
  val xs2 = filter (fn x => p !~ get_sep_domain x) (list_dest dest_star p2)
  val ys1 = map dest_sep_hide (filter (can dest_sep_hide) xs1)
  val ys2 = map dest_sep_hide (filter (can dest_sep_hide) xs2)
  val zs1 = (filter (not o can dest_sep_hide) xs1)
  val zs2 = (filter (not o can dest_sep_hide) xs2)
  val qs1 = filter (fn x => tmem (car x) ys1 handle HOL_ERR _ => false) zs2
  val qs2 = filter (fn x => tmem (car x) ys2 handle HOL_ERR _ => false) zs1
  val th1 = foldr (uncurry UNHIDE_PRE_RULE) th1 qs1
  val th2 = foldr (uncurry UNHIDE_PRE_RULE) th2 qs2
  (* hide relevant postconditions *)
  val (_,p1,_,q1) = dest_spec (concl th1)
  val (_,p2,_,q2) = dest_spec (concl th2)
  val (qs1,q1) = list_dest_sep_exists q1
  val (qs2,q2) = list_dest_sep_exists q2
  val xs1 = filter (fn x => p !~ get_sep_domain x)
                   (list_dest dest_star (fst_sep_disj q1))
  val xs2 = filter (fn x => p !~ get_sep_domain x)
                   (list_dest dest_star (fst_sep_disj q2))
  val ys1 = map dest_sep_hide (filter (can dest_sep_hide) xs1)
  val ys2 = map dest_sep_hide (filter (can dest_sep_hide) xs2)
  fun safe_car tm = car tm handle HOL_ERR _ => tm
  val zs1 = map safe_car (filter (not o can dest_sep_hide) xs1)
  val zs2 = map safe_car (filter (not o can dest_sep_hide) xs2)
  val qs1 = filter (fn x => tmem x ys1) zs2
  val qs2 = filter (fn x => tmem x ys2) zs1
  val th1 = foldr (uncurry HIDE_POST_RULE) th1 qs2
  val th2 = foldr (uncurry HIDE_POST_RULE) th2 qs1
  (* abbreviate posts *)
  val f = CONV_RULE (PRE_CONV (SIMP_CONV (bool_ss++star_ss) []) THENC
                     POST_CONV (SIMP_CONV (bool_ss++star_ss) []) THENC
                     REWRITE_CONV [STAR_ASSOC])
  val th1 = f (ABBREV_NEW th1)
  val th2 = f (ABBREV_NEW th2)
  (* do the merge *)
  fun g x = PURE_REWRITE_RULE [AND_IMP_INTRO] o DISCH x o DISCH_ALL
  val (th1,th2) = prepare_sep_disj_posts th1 th2
  val th = MATCH_MP SPEC_COMBINE (g guard th1)
  val th = MATCH_MP th (g (mk_neg guard) th2)
  val th = UNDISCH (RW [UNION_IDEMPOT] th)
  val th = remove_primes th
  in th end handle HOL_ERR e => let
    val _ = (merge_mem := (guard,th1,th2))
    val th1 = DISCH_ALL th1
    val th2 = DISCH_ALL th2
    val _ = print ("\n\nval guard = ``"^ term_to_string guard ^"``;\n\n")
    val _ = print ("\n\nval th1 = mk_thm([],``"^ term_to_string (concl th1) ^
                   "``);\n\n")
    val _ = print ("\n\nval th2 = mk_thm([],``"^ term_to_string (concl th2) ^
                   "``);\n\n")
    in raise HOL_ERR e end;

fun merge_spectree_thm (LEAF (th,i)) = let
      val th = SIMP_RULE (bool_ss++sep_cond_ss) [SEP_EXISTS_COND] th
      val th = UNDISCH (RW [SPEC_MOVE_COND,AND_IMP_INTRO] (DISCH_ALL th))
      in (th,LEAF (TRUTH,i)) end
  | merge_spectree_thm (SEQ (tms,t)) = let
      val (th,t) = merge_spectree_thm t
      in (th,SEQ (tms,t)) end
  | merge_spectree_thm (BRANCH (guard,t1,t2)) = let
      val (th1,t1') = merge_spectree_thm t1
      val (th2,t2') = merge_spectree_thm t2
      val th = MERGE guard th1 th2
      in (th,BRANCH (guard,t1',t2')) end

fun merge_spectree name t = let
  val _ = echo 1 " merging cases,"
  val (th,_) = merge_spectree_thm t
  val th = MERGE ``T`` th th
  val th = UNDISCH_ALL (remove_primes (DISCH_ALL th))
  in th end


(* STAGE 3, part c ---------------------------------------------------------- *)

(* clean the theorem *)

fun tagged_var_to_num v = let
  fun drop_until p [] = []
    | drop_until p (x::xs) = if p x then x::xs else drop_until p xs
  val xs = (take_until (fn x => x = #"@") o explode o fst o dest_var) v
  val xs =
     drop_until
        (fn x => mem x [#"0",#"1",#"2",#"3",#"4",#"5",#"6",#"7",#"8",#"9"]) xs
  val s = implode xs
  val s = if s = "" then "100000" else s
  in string_to_int s end

val GUARD_T = prove(``!x. x = (x = GUARD 0 T)``,REWRITE_TAC [GUARD_def])
val GUARD_F = prove(``!x. ~x = (x = GUARD 0 F)``,REWRITE_TAC [GUARD_def])

fun init_clean th = let
  fun side2guard_conv tm =
    if not (can (match_term ``(\x.x:bool) y``) tm)
    then NO_CONV tm else let
      val v =
        (numSyntax.term_of_int o tagged_var_to_num o fst o dest_abs o car) tm
      in (BETA_CONV THENC ONCE_REWRITE_CONV [GSYM (SPEC v GUARD_def)]) tm end
  val th = RW [PUSH_IF_LEMMA,GSYM CONJ_ASSOC] (DISCH_ALL th)
  val th = CONV_RULE (DEPTH_CONV side2guard_conv) (DISCH_ALL th)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                     (SIMP_CONV bool_ss [GSYM CONJ_ASSOC,NOT_IF])) th
  val th = remove_primes th
  fun bool_var_assign_conv tm =
    if is_conj tm then BINOP_CONV bool_var_assign_conv tm else
    if is_cond tm then BINOP_CONV bool_var_assign_conv tm else
    if is_var tm andalso type_of tm = ``:bool`` then SPEC tm GUARD_T else
    if is_neg tm andalso is_var (cdr tm ) then SPEC (cdr tm) GUARD_F
    else ALL_CONV tm
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) bool_var_assign_conv) th
  in th end;

fun guard_to_num tm = (numSyntax.int_of_term o cdr o car) tm
fun assum_to_num tm =
  if is_var tm then tagged_var_to_num tm else
  if is_neg tm andalso is_var (cdr tm) then tagged_var_to_num (cdr tm) else
  if is_cond tm then 100000 else
  if can (match_term ``GUARD b x``) tm then guard_to_num tm else
  if can (match_term ``~(GUARD b x)``) tm then guard_to_num (cdr tm) else
    (hd o map tagged_var_to_num o free_vars o fst o dest_eq) tm

fun push_if_inwards th = let
  fun drop_until p [] = []
    | drop_until p (x::xs) = if p x then x::xs else drop_until p xs
  fun strip_names v = let
    val vs = (drop_until (fn x => x = #"@") o explode o fst o dest_var) v
    in if vs = [] then (fst o dest_var) v else implode vs end
  fun sort_seq tms = let
    val xs = all_distinct (map assum_to_num tms)
    val xs = sort (fn x => fn y => x <= y) xs
    val xs = map (fn x => filter (fn tm => x = assum_to_num tm) tms) xs
    fun internal_sort ys = let
      val zs = filter (fn tm => can (match_term ``GUARD b x``) tm orelse
                                can (match_term ``~(GUARD b x)``) tm) ys
      val ys = op_set_diff aconv ys zs
      fun comp tm1 tm2 = let
        val (defs,_) = dest_eq tm1
        val (_,refs) = dest_eq tm2
        in disjoint (map strip_names (free_vars defs))
                    (map strip_names (free_vars refs)) end
      fun f [] = []
        | f [x] = [x]
        | f (x::y::ys) = if comp x y then x :: f (y::ys) else y :: f (x::ys)
      in zs @ f ys end
    in append_lists (map internal_sort xs) end
  fun PUSH_IF_TERM tm = let
    val (b,t1,t2) = dest_cond tm
    val t1 = PUSH_IF_TERM t1
    val t2 = PUSH_IF_TERM t2
    val xs1 = list_dest dest_conj t1
    val xs2 = list_dest dest_conj t2
    val i = guard_to_num b
    val ys1 = filter (fn x => assum_to_num x < i) xs1
    val ys2 = filter (fn x => assum_to_num x < i) xs2
    val _ = if HOLset.equal(listset ys1, listset ys2) then () else hd []
    val zs1 = sort_seq (op_set_diff aconv xs1 ys1)
    val zs2 = sort_seq (op_set_diff aconv xs2 ys2)
    val q = mk_cond(b,list_mk_conj zs1,list_mk_conj zs2)
    val goal = list_mk_conj(sort_seq ys1 @ [q])
    in goal end handle HOL_ERR _ =>
    list_mk_conj(sort_seq (list_dest dest_conj tm))
  val th = RW [NOT_IF] (DISCH_ALL th)
  val tm = (fst o dest_imp o concl) th
  val goal = mk_imp(PUSH_IF_TERM tm,tm)
  val simp = SIMP_CONV pure_ss [AC CONJ_ASSOC CONJ_COMM]
  val lemma = auto_prove "push_if_inwards" (goal,
    REWRITE_TAC [PUSH_IF_LEMMA]
    THEN CONV_TAC (RAND_CONV simp THENC (RATOR_CONV o RAND_CONV) simp)
    THEN REWRITE_TAC [])
  val th = DISCH_ALL (MP th (UNDISCH lemma))
  val th =
    CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV bool_ss [GUARD_EQ_ZERO])) th
  in th end;

fun list_dest_exists tm ys = let
  val (v,y) = dest_exists tm
  in list_dest_exists y (v::ys) end handle e => (rev ys, tm)

(* val tm = ``?x. (x = y + 5) /\ x < z /\ t < x`` *)
(* val tm = ``?z. (z = x + 5)`` *)

fun INST_EXISTS_CONV tm = let
  val (v,rest) = dest_exists tm
  val (x,rest) = dest_conj rest
  val (x,y) = dest_eq x
  val th = ISPECL [mk_abs(v,rest),y] UNWIND_THM2
  val th = CONV_RULE (RAND_CONV BETA_CONV) th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
             (ALPHA_CONV v THENC ABS_CONV (RAND_CONV BETA_CONV))) th
  in if x ~~ v then th else NO_CONV tm end handle HOL_ERR _ => let
  val (v,rest) = dest_exists tm
  val (x,y) = dest_eq rest
  val th = GEN_ALL (SIMP_CONV std_ss [] ``?x:'a. x = a``)
  val th = ISPEC y th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
             (ALPHA_CONV v)) th
  in if x ~~ v then th else NO_CONV tm end

(* val tm = ``!x. foo (FST x, SND (SND x)) = FST (SND x)`` *)

val EXPAND_FORALL_CONV = let
  fun EXPAND_FORALL_ONCE_CONV tm =
    ((QUANT_CONV (UNBETA_CONV (fst (dest_forall tm))) THENC
      ONCE_REWRITE_CONV [FORALL_PROD] THENC
      (QUANT_CONV o QUANT_CONV) BETA_CONV)) tm
    handle HOL_ERR _ => ALL_CONV tm;
  in (REPEATC (DEPTH_CONV EXPAND_FORALL_ONCE_CONV)) end

(* val tm = ``?z:num. y + x + 5 < 7`` *)

fun PUSH_EXISTS_CONST_CONV tm = let
  val PUSH_EXISTS_CONST_LEMMA = auto_prove "PUSH_EXISTS_CONST_CONV"
   (``!p. (?x:'a. p) = p:bool``,
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC (genvar(``:'a``)) THEN ASM_SIMP_TAC std_ss []);
  val (v,n) = dest_exists tm
  val _ = if free_in v n then hd [] else 1
  val th = SPEC n (INST_TYPE [``:'a``|->type_of v] PUSH_EXISTS_CONST_LEMMA)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) (ALPHA_CONV v)) th
  in th end handle e => NO_CONV tm handle e => NO_CONV tm;

(* val tm = ``?x. let (y,z,q) = foo t in y + x + z + 5 = 8 - q`` *)

fun PUSH_EXISTS_LET_CONV tm = let
  val (v,n) = dest_exists tm
  val (x,rest) = pairSyntax.dest_anylet n
  val tm2 = pairSyntax.mk_anylet(x,mk_exists(v,rest))
  val goal = mk_eq(tm,tm2)
  val c = (RATOR_CONV o RATOR_CONV) (REWRITE_CONV [LET_DEF])
  val thi = auto_prove "PUSH_EXISTS_LET_CONV" (goal,
    SPEC_TAC (snd (hd x),genvar(type_of (snd (hd x))))
    THEN CONV_TAC EXPAND_FORALL_CONV THEN REPEAT STRIP_TAC
    THEN CONV_TAC ((RAND_CONV) c)
    THEN CONV_TAC ((RATOR_CONV o RAND_CONV o QUANT_CONV) c)
    THEN NTAC ((length o dest_tuple o fst o hd) x + 1)
      (CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
       THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
       THEN REWRITE_TAC [UNCURRY_DEF]))
  in thi end handle e => NO_CONV tm
             handle e => NO_CONV tm;

(* val tm = ``?x y z. if (q = 4) then (x + 1 = 6) else (y - 8 = z)`` *)

fun PUSH_EXISTS_COND_CONV tm = let
  val (vs,n) = list_dest_exists tm []
  val _ = if null vs then hd [] else ()
  val (b,x1,x2) = dest_cond n
  val tm2 = mk_cond(b,list_mk_exists(vs,x1),list_mk_exists(vs,x2))
  val thi = auto_prove "PUSH_EXISTS_COND_CONV"
            (mk_eq(tm,tm2),Cases_on [ANTIQUOTE b] THEN ASM_REWRITE_TAC [])
  in thi end handle e => NO_CONV tm handle e => NO_CONV tm;

(* val tm = ``?x y z. (q = 4) /\ (x + 1 = 6)`` *)

fun PUSH_EXISTS_CONJ_CONV tm = let
  val (vs,n) = list_dest_exists tm []
  val xs = (list_dest dest_conj n)
  val _ = if HOLset.isEmpty (FVs (hd xs) Isct listset vs) then () else hd []
  val tm2 = mk_conj(hd xs,list_mk_exists(vs,list_mk_conj(tl xs)))
  fun PULL_EXISTS_CONV tm = let
    val (x,y) = dest_conj tm
    val (v,y) = dest_exists y
    val th = ISPEC (mk_abs(v,y)) (SPEC x (GSYM RIGHT_EXISTS_AND_THM))
    val th = CONV_RULE (RAND_CONV (
        RAND_CONV (ALPHA_CONV v) THENC
        QUANT_CONV (RAND_CONV BETA_CONV)) THENC
      (RATOR_CONV o RAND_CONV) (
        RAND_CONV (RAND_CONV (ALPHA_CONV v) THENC
                   QUANT_CONV BETA_CONV))) th
    in th end handle HOL_ERR _ => NO_CONV tm
  val thi = GSYM (REPEATC (ONCE_DEPTH_CONV PULL_EXISTS_CONV) tm2)
  in thi end handle e => NO_CONV tm handle e => NO_CONV tm;

(* val tm = ``?x y z. 5 = 6 + tg`` *)

fun PUSH_EXISTS_EMPTY_CONV tm = let
  fun DELETE_EXISTS_CONV tm = let
    val (v,rest) = dest_exists tm
    val _ = if free_in v rest then hd [] else ()
    val w = genvar(``:bool``)
    val th = INST_TYPE [``:'a``|->type_of v] (SPEC w boolTheory.EXISTS_SIMP)
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) (ALPHA_CONV v)) th
    in INST [w |-> rest] th end handle e => NO_CONV tm
  val th = DEPTH_CONV DELETE_EXISTS_CONV tm
  in if (is_exists o cdr o concl) th then NO_CONV tm else th end

fun DEPTH_EXISTS_CONV c tm =
  if is_exists tm then (c THENC DEPTH_EXISTS_CONV c) tm else
  if can (match_term ``GUARD n x``) tm then ALL_CONV tm else
  if is_comb tm then (RATOR_CONV (DEPTH_EXISTS_CONV c) THENC
                      RAND_CONV (DEPTH_EXISTS_CONV c)) tm else
  if is_abs tm then ABS_CONV (DEPTH_EXISTS_CONV c) tm else ALL_CONV tm;

fun EXPAND_BASIC_LET_CONV tm = let
  val (xs,x) = pairSyntax.dest_anylet tm
  val (lhs,rhs) = hd xs
  val ys = dest_tuple lhs
  val zs = dest_tuple rhs
  val _ = if length zs = length ys then () else hd []
  fun every p [] = true
    | every p (x::xs) = if p x then every p xs else hd []
  val _ = every (fn x => every is_var (list_dest dest_conj x)) zs
  in (((RATOR_CONV o RATOR_CONV) (REWRITE_CONV [LET_DEF]))
      THENC DEPTH_CONV PairRules.PBETA_CONV) tm end
  handle e => NO_CONV tm;

fun STRIP_FORALL_TAC (hs,tm) =
  if is_forall tm then STRIP_TAC (hs,tm) else NO_TAC (hs,tm)

fun SPEC_AND_CASES_TAC x =
  SPEC_TAC (x,genvar(type_of x)) THEN Cases THEN REWRITE_TAC []

fun GENSPEC_TAC [] = SIMP_TAC pure_ss [FORALL_PROD]
  | GENSPEC_TAC (x::xs) = SPEC_TAC (x,genvar(type_of x)) THEN GENSPEC_TAC xs;

val EXPAND_BASIC_LET_TAC =
  CONV_TAC (DEPTH_CONV EXPAND_BASIC_LET_CONV)
  THEN REPEAT STRIP_FORALL_TAC

fun AUTO_DECONSTRUCT_TAC finder (hs,goal) = let
  val tm = finder goal
  in if is_cond tm then let
       val (b,_,_) = dest_cond tm
       in SPEC_AND_CASES_TAC b (hs,goal) end
     else if is_let tm then let
       val (v,c) = (hd o fst o pairSyntax.dest_anylet) tm
       val c = if not (type_of c = ``:bool``) then c else
         (find_term (can (match_term ``GUARD x b``)) c handle e => c)
       val cs = dest_tuple c
       in (GENSPEC_TAC cs THEN EXPAND_BASIC_LET_TAC) (hs,goal) end
     else (REWRITE_TAC [] THEN NO_TAC) (hs,goal) end

(* val v = ``v:num``
   val c = ``c:num``
   val tm =
      ``?x y v z. (x = 5) /\ (y = x + 6) /\ (v = c) /\ (z = v) /\ (n = v:num)``
*)

fun FAST_EXISTS_INST_CONV v c tm = let
  val (x,y) = dest_exists tm
  in if x !~ v then QUANT_CONV (FAST_EXISTS_INST_CONV v c) tm else let
  val imp = SPEC (mk_abs(v,y)) (ISPEC c EXISTS_EQ_LEMMA)
  val thi = MP (CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV bool_ss [])) imp) TRUTH
  val thi = CONV_RULE (RAND_CONV BETA_CONV THENC
                       (RATOR_CONV o RAND_CONV o RAND_CONV) (ALPHA_CONV v) THENC
                       (RATOR_CONV o RAND_CONV o QUANT_CONV) BETA_CONV) thi
  in thi end end;

fun SUBST_EXISTS_CONV_AUX [] cs = ALL_CONV
  | SUBST_EXISTS_CONV_AUX vs [] = ALL_CONV
  | SUBST_EXISTS_CONV_AUX (v::vs) (c::cs) =
      FAST_EXISTS_INST_CONV v c THENC SUBST_EXISTS_CONV_AUX vs cs;

fun SUBST_EXISTS_CONV vs cs =
  PURE_REWRITE_CONV [PAIR_EQ,GSYM CONJ_ASSOC]
  THENC SUBST_EXISTS_CONV_AUX vs cs
  THENC REWRITE_CONV [];

(*
fun PRINT_GOAL_TAC s (hs,goal) = let
  val _ = print "\n\n"
  val _ = print s
  val _ = print ":\n\n"
  val _ = print_term goal
  val _ = print "\n\n"
  in ALL_TAC (hs,goal) end;
*)

fun GUIDED_INST_EXISTS_TAC finder1 cc2 (hs,goal) = let
  val tm = finder1 goal
  val (xs,x) = pairSyntax.dest_anylet tm
  val (lhs,rhs) = hd xs
  val ys = dest_tuple lhs
  val zs = dest_tuple rhs
  val _ = if length zs = length ys then () else hd []
  val cond_var = mk_var("cond",``:bool``)
  in (if tml_eq ys [cond_var] then ALL_TAC (hs,goal)
      else CONV_TAC (cc2 (SUBST_EXISTS_CONV ys zs)) (hs,goal)) end
  handle e => let
    val _ = print "\n\nGUIDED_INST_EXISTS_TAC should not fail.\n\nGoal:\n\n"
    val _ = print_term goal
    val _ = print "\n\n"
    in raise e end;

fun AUTO_DECONSTRUCT_EXISTS_TAC finder1 (cc1,cc2) (hs,goal) = let
  val tm = finder1 goal
  in if is_cond tm then let
       val (b,_,_) = dest_cond tm
       in SPEC_AND_CASES_TAC b (hs,goal) end
     else if is_let tm then let
       val cond_var = mk_var("cond",``:bool``)
       val (v,c) = (hd o fst o pairSyntax.dest_anylet) tm
       val c = if v !~ cond_var then c
               else (find_term (can (match_term ``GUARD x b``)) c
                     handle e => ``GUARD 1000 F`` (* unlikely term *))
       val cs = dest_tuple c
       in (GENSPEC_TAC cs
           THEN REPEAT STRIP_TAC
           THEN REWRITE_TAC []
           THEN GUIDED_INST_EXISTS_TAC finder1 cc2
           THEN CONV_TAC (cc1 EXPAND_BASIC_LET_CONV)
           THEN REWRITE_TAC []) (hs,goal) end
     else (REWRITE_TAC [] THEN NO_TAC) (hs,goal) end;

fun one_step_let_intro th = let
  val tm = fst (dest_imp (concl th))
  val g = last (list_dest boolSyntax.dest_exists tm)
  fun let_term tm = let
    val (g,x,y) = dest_cond tm
    in FUN_IF (g,let_term x,let_term y) end handle e => let
    val (x,y) = dest_conj tm
    in if can (match_term ``GUARD n y``) x
       then FUN_COND (x,let_term y)
       else let
         val (x1,x2) = dest_eq x
         val xs1 = dest_tuple x1
         in if is_new_var x1
               then FUN_VAL (mk_conj(tm,mk_var("cond",``:bool``)))
            else FUN_LET (x1,x2,let_term y)
         end end
  val let_tm =
     subst [mk_var("cond",``:bool``)|->``T:bool``] (ftree2tm (let_term g))
  val goal = mk_eq(tm,let_tm)
(*
set_goal([],goal)
*)
  val thi = RW [GSYM CONJ_ASSOC] (auto_prove "one_step_let_intro" (goal,
    REWRITE_TAC []
    THEN REPEAT (AUTO_DECONSTRUCT_EXISTS_TAC cdr
                   (RAND_CONV, RATOR_CONV o RAND_CONV))
    THEN SIMP_TAC pure_ss [AC CONJ_ASSOC CONJ_COMM] THEN REWRITE_TAC []
    THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []))
  val th = RW1 [thi] th
  in th end;

fun remove_constant_new_assigment avoid_vars th = let
  val vs = filter is_new_var (free_vars (concl th))
  fun is_real_assign tm = let
    val (x,y) = dest_eq tm
    in dest_new_var x !~ y end handle HOL_ERR _ => false
  val ws = map (fst o dest_eq) (find_terms is_real_assign (concl th))
  val ws = op_set_diff aconv vs ws
  val th1 = RW [] (INST (map (fn x => x |-> dest_new_var x) ws) th)
  val ts = (free_vars o fst o dest_imp o concl) th1
  fun mk_new_var v = let val (n,t) = dest_var v in mk_var("new@"^n,t) end
  val ws = op_set_diff aconv (map dest_new_var ws) (ts @ avoid_vars)
  val th = RW [] (INST (map (fn x => mk_new_var x |-> x) ws) th)
  in th end;

fun introduce_lets th = let
  val th = init_clean th
  val th = push_if_inwards th
  val (lhs,rhs) = (dest_imp o concl) th
  val vs = op_set_diff aconv (free_vars lhs) (free_vars rhs)
  val vs = filter (fn v => not (read_tag v = "new")) vs
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                         (ONCE_REWRITE_CONV [GSYM CONTAINER_def])) th
  val th = SIMP_RULE bool_ss [LEFT_FORALL_IMP_THM] (GENL vs th)
  val th = RW1 [CONTAINER_def] th
  val th = one_step_let_intro th
  in th end;

fun raw_tm2ftree tm = let
  val (x,y) = dest_conj tm
  val _ = if can (match_term ``GUARD b x``) x then () else fail()
  in FUN_COND (x,raw_tm2ftree y) end handle e => let
  val (b,x,y) = dest_cond tm
  in FUN_IF (b,raw_tm2ftree x,raw_tm2ftree y) end handle e => let
  val (x,y) = pairSyntax.dest_anylet tm
  val z = raw_tm2ftree y
  fun g((x,y),z) = FUN_LET (x,y,z)
  in foldr g z x end handle e => FUN_VAL tm;

(* sorts in alphabetical order except for r1,r2,r3 which will come first *)
val var_sorter = let
  fun dest_reg_var s = let
    val xs = explode s
    in if hd xs = #"r" then string_to_int (implode (tl xs)) else fail() end
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

fun leaves (FUN_VAL tm)      f = FUN_VAL (f tm)
  | leaves (FUN_COND (c,t))  f = FUN_COND (c, leaves t f)
  | leaves (FUN_IF (a,b,c))  f = FUN_IF (a, leaves b f, leaves c f)
  | leaves (FUN_LET (v,y,t)) f = FUN_LET (v, y, leaves t f)

fun erase_conds (FUN_VAL tm) = FUN_VAL tm
  | erase_conds (FUN_COND (c,t)) = erase_conds t
  | erase_conds (FUN_IF (a,b,c)) = FUN_IF (a,erase_conds b,erase_conds c)
  | erase_conds (FUN_LET (x,y,t)) = FUN_LET (x,y,erase_conds t)

val REMOVE_TAGS_CONV = let
  val alpha_lemma = prove(``!b:bool. (b = T) ==> b``,Cases THEN REWRITE_TAC []);
  fun REMOVE_TAG_CONV tm = let
    val (v,x) = dest_abs tm
    val xs = free_vars x
    fun d [] = fail()
      | d (x::xs) = if x = #"@" then implode xs else d xs
    fun strip_tag v = mk_var((d o explode o fst o dest_var) v, type_of v)
    fun add_prime v = mk_var(fst (dest_var v) ^ "'", type_of v)
    fun is_ok v = not (tmem v xs)
    fun UNTIL g f x = if g x then x else UNTIL g f (f x)
    val w = UNTIL is_ok add_prime (strip_tag v)
    val thi =
       SIMP_CONV std_ss [FUN_EQ_THM] (mk_eq(tm,mk_abs(w,subst [v|->w] x)))
    in MATCH_MP alpha_lemma thi end handle e => NO_CONV tm
  in (DEPTH_CONV REMOVE_TAG_CONV THENC REWRITE_CONV [GUARD_def]) end;

fun simplify_and_define name x_in rhs = let (*  *)
  val ty = mk_type("fun",[type_of x_in, type_of rhs])
  val rw = REMOVE_TAGS_CONV rhs handle HOL_ERR _ => REFL rhs
  val tm = mk_eq(mk_comb(mk_var(name,ty),x_in),cdr (concl rw))
  val def = SPEC_ALL (new_definition(name ^ "_def", tm)) handle e =>
            (print ("\n\nERROR: Cannot define " ^ name ^ "_def as,\n\n");
             print_term tm; print "\n\n"; raise e)
  in CONV_RULE (RAND_CONV (fn tm => GSYM rw)) def end;

fun pull_T (FUN_VAL tm) = FUN_VAL tm
  | pull_T (FUN_COND tm) = FUN_COND tm
  | pull_T (FUN_IF (tm,x,y)) = let
      val x' = pull_T x
      val y' = pull_T y
      in if (ftree_type_cmp(x', FUN_VAL ``T:bool``) = EQUAL andalso
             ftree_type_cmp(y', FUN_VAL ``T:bool``) = EQUAL) orelse
            ftree_type_cmp(x',y') = EQUAL
         then x' else FUN_IF (tm,x',y') end
  | pull_T (FUN_LET (tm,tn,x)) = let
      val x' = pull_T x
      val vs = free_vars (ftree2tm x')
      val ws = free_vars tm
      in if null (filter (fn v => tmem v ws) vs)then x' else FUN_LET (tm,tn,x')
      end

fun simplify_pre pre th = let
  val ft = pull_T (tm2ftree ((cdr o concl o SPEC_ALL) pre))
  val goal = mk_comb((car o concl o SPEC_ALL) pre, ftree2tm ft)
  in if not (ftree_type_cmp(ft,FUN_VAL ``T``) = EQUAL) then (th,pre) else let
    val new_pre = (auto_prove "simplify_pre" (goal,
      REWRITE_TAC []
      THEN ONCE_REWRITE_TAC [pre]
      THEN REPEAT (AUTO_DECONSTRUCT_TAC I)))
    val th = RW [new_pre,SEP_CLAUSES] th
    in (th,new_pre) end end

fun introduce_post_let th = let
  val (x,y) = (dest_comb o cdr o concl) th
  val (x,z) = pairSyntax.dest_pabs x
  val tm = pairSyntax.mk_anylet([(x,y)],z)
  val th1 = GSYM (SIMP_CONV std_ss [LET_DEF] tm)
  in CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [th1]))
       (SIMP_RULE std_ss [] th) end handle e => th;

fun REMOVE_VARS_FROM_THM vs th = let
  fun REMOVE_FROM_LHS (v,th) = let
    val th = SIMP_RULE pure_ss [LEFT_FORALL_IMP_THM] (GEN v th)
    val c = DEPTH_EXISTS_CONV (PUSH_EXISTS_COND_CONV ORELSEC
                               PUSH_EXISTS_LET_CONV ORELSEC
                               PUSH_EXISTS_CONJ_CONV ORELSEC
                               INST_EXISTS_CONV ORELSEC
                               PUSH_EXISTS_CONST_CONV)
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) c) th
    in th end
  in foldr REMOVE_FROM_LHS th vs end

fun HIDE_POST_VARS vs th = let
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                         (ONCE_REWRITE_CONV [GSYM CONTAINER_def])) th
  val th = foldr (uncurry SEP_EXISTS_POST_RULE) (UNDISCH_ALL th) vs
  val th = SEP_EXISTS_ELIM_RULE th
  val th = RW [CONTAINER_def] (DISCH_ALL th)
  val th = REMOVE_VARS_FROM_THM vs th
  in th end;

fun HIDE_PRE_VARS vs th1 = let
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                         (ONCE_REWRITE_CONV [GSYM CONTAINER_def])) th1
  val th = foldr (uncurry SEP_EXISTS_PRE_RULE) (UNDISCH_ALL th) vs
  val th = SEP_EXISTS_ELIM_RULE th
  val th = RW [CONTAINER_def] (DISCH_ALL th)
  in th end;

fun SORT_SEP_CONV tm = let
  fun remove_tags tm =
    subst (map (fn v => v |-> mk_var(strip_tag v,type_of v)) (free_vars tm)) tm
  val xs = list_dest dest_star tm
  fun compare tm1 tm2 = let
    val s1 = term_to_string (remove_tags (get_sep_domain tm1))
    val s2 = term_to_string (remove_tags (get_sep_domain tm2))
    in if size s2 < size s1 then 1 < 2 else
       if size s1 < size s2 then 2 < 1 else
       if not (s1 = s2) then s1 < s2 else
         term_to_string (remove_tags tm1) < term_to_string (remove_tags tm2) end
  val tm2 = list_mk_star (sort compare xs) (type_of tm)
  val thi =
     auto_prove "SORT_SEP_CONV" (mk_eq(tm,tm2),SIMP_TAC (bool_ss++star_ss) [])
  in thi end;

fun LET_EXPAND_POS_CONV tm = let
  val x = (fst o dest_abs o fst o dest_let) tm
  in if x !~ mk_var("pos",``:num``) then fail () else
     ((RATOR_CONV o RATOR_CONV) (ONCE_REWRITE_CONV [LET_DEF])
      THENC RATOR_CONV BETA_CONV THENC BETA_CONV THENC BETA_CONV) tm end
  handle HOL_ERR _ => NO_CONV tm;

fun DEST_NEW_VAR_CONV tm =
  ALPHA_CONV (dest_new_var (fst (dest_abs tm))) tm
  handle HOL_ERR _ => NO_CONV tm;

fun SEP_EXISTS_CONV c tm =
  if can dest_sep_exists tm
  then RAND_CONV (ABS_CONV (SEP_EXISTS_CONV c)) tm else ALL_CONV tm;
       (* is this right? shouldn't it be: c tm *)

fun SEP_DISJ_CONV c tm =
  if can dest_sep_disj tm
  then ((RATOR_CONV o RAND_CONV) c) tm else c tm;

val GEN_TUPLE_LEMMA = GSYM (CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
   (ALPHA_CONV (mk_var("_",``:'a # 'b``)))) FORALL_PROD)
fun GEN_TUPLE tm th =
  if not (pairSyntax.is_pair tm) then GEN tm th else let
    val (w,tm2) = pairSyntax.dest_pair tm
    val th = GEN_TUPLE tm2 th
    val v = fst (dest_forall (concl th))
    val th = CONV_RULE (UNBETA_CONV (pairSyntax.mk_pair(w,v))) (SPEC v th)
    val x = genvar(type_of tm)
    val th =
       GEN x (CONV_RULE BETA_CONV
              (SPEC x (PURE_REWRITE_RULE [GEN_TUPLE_LEMMA] (GEN w (GEN v th)))))
    in th end;

fun extract_function name th entry exit function_in_out = let
  val _ = echo 1 " extracting function,"
  val output = (filter (not o is_new_var) o free_vars o cdr o concl) th
  fun drop_until p [] = []
    | drop_until p (x::xs) = if p x then x::xs else drop_until p xs
  fun strip_names v = let
    val vs = (tl o drop_until (fn x => x = #"@") o explode o fst o dest_var) v
    in if vs = [] then (fst o dest_var) v else implode vs end
    handle e => (fst o dest_var) v
  fun new_abbrev (v,th) = let
    val th = RW [GSYM SPEC_MOVE_COND] (DISCH_ALL th)
    val n = "new@" ^ strip_names v
    val th = raw_abbreviate2 (n,v,v) th
    val th = RW [SPEC_MOVE_COND,AND_IMP_INTRO] (DISCH_ALL th)
    val th = RW [PUSH_IF_LEMMA] th
    in th end
  val th = foldr new_abbrev th output
  val th = introduce_lets th
  val avoid_vars =
     case function_in_out of NONE => [] | SOME (p,q) => free_vars q
  val th = remove_constant_new_assigment avoid_vars th
  val pc = get_pc()
  val pc_type = (hd o snd o dest_type o type_of) pc
  val th = INST [mk_var("new@p",pc_type) |-> mk_var("set@p",pc_type)] th
  val t = tm2ftree ((cdr o car o concl o RW [WORD_ADD_0]) th)
  (* extract: step function and input, output tuples *)
  fun gen_pc n = if n = 0 then mk_var("p",pc_type) else
    (ASSUME (mk_eq(mk_var("_",pc_type),mk_var("p",pc_type))))
            |> (!decompiler_set_pc) n |> concl |> cdr
    handle HOL_ERR _ => subst [mk_var("n",``:num``) |-> numSyntax.term_of_int n]
      (inst [``:'a``|->(hd o tl o snd o dest_type) pc_type]
            ``(p:'a word) + n2w n``)
  val exit_tm = gen_pc (hd exit)
  val entry_tm = (snd o dest_eq o find_term (fn tm => let
                   val (x,y) = dest_eq tm
                   in fst (dest_var x) = "set@p" andalso y !~ exit_tm end
                   handle HOL_ERR _ => false) o concl) th
                 handle HOL_ERR _ => gen_pc (hd entry)
  val final_node = mk_eq(mk_var("set@p",pc_type),exit_tm)
  fun is_terminal_node tm = can (find_term (fn x => x ~~ final_node)) tm
  val output = (filter is_new_var o free_vars o cdr o cdr o concl) th
  fun strip_tag v =
     mk_var((implode o drop 4 o explode o fst o dest_var) v, type_of v)
  val output = var_sorter (map strip_tag output)
  fun rm_pc tm = let
    val xs = find_terms (fn x => fst (dest_eq x) ~~ mk_var("set@p",pc_type)
                                 handle HOL_ERR _ => false) tm
    in subst (map (fn x => x |-> T) xs) tm end
  val iii = (list_mk_pair o var_sorter o filter (not o is_new_var) o
               free_vars o rm_pc o ftree2tm o leaves t)
            (fn x => if is_terminal_node x then x else ``T:bool``)
  val input = (var_sorter o filter (not o is_new_var) o
               filter (fn v => v !~ mk_var("cond",``:bool``)) o
               free_vars o rm_pc o ftree2tm o leaves t)
           (fn x => if is_terminal_node x then x else mk_eq(iii,iii))
  val input = if null input then [mk_var("()",``:unit``)] else input
  fun set_input_output NONE = (input,output)
    | set_input_output (SOME (ix,ox)) = (dest_tuple ix, dest_tuple ox)
  val (input,output) = set_input_output function_in_out
  val pos_subst = mk_var("pos",``:num``) |-> mk_var("s10000@pos",``:num``)
  val new_pos_subst =
     mk_var("s10000@pos",``:num``) |-> mk_var("new@pos",``:num``)
  fun new_into_subst tm = let
    val vs = list_dest dest_conj tm
    val vs = filter is_eq vs
    in subst
         (pos_subst ::
          map (fn x => let val (x,y) = dest_eq x in (strip_tag x) |-> y end) vs)
    end
  val x_in = list_mk_pair input
  val x_out = list_mk_pair output
  fun add_new_tag v = mk_var("new@" ^ fst (dest_var v), type_of v)
  val new_output = list_mk_pair (map add_new_tag output)
  val new_input = list_mk_pair (map add_new_tag input)
  val cond_var = mk_var("cond",``:bool``)
  fun mk_exit tm = pairSyntax.mk_pair(tm,cond_var)
  val step_fun =
      mk_pabs(x_in,ftree2tm (leaves t (fn x =>
                if is_terminal_node x
                then mk_exit(sumSyntax.mk_inr
                               (new_into_subst x x_out,type_of x_in))
                else mk_exit(sumSyntax.mk_inl
                               (new_into_subst x x_in,type_of x_out)))))
  val step_fun =
     (snd o dest_eq o concl o QCONV (REWRITE_CONV [GSYM CONJ_ASSOC]))
        (subst [cond_var |-> T] step_fun)
  (* define functions *)
  val func_name = name
  val tm_option = NONE
  val (main_thm,main_def,pre_thm,pre_def) =
         tailrecLib.tailrec_define_from_step func_name step_fun tm_option
  val finalise =
     CONV_RULE (REMOVE_TAGS_CONV THENC DEPTH_CONV (LET_EXPAND_POS_CONV))
  val main_thm = finalise main_thm
  val pre_thm = finalise pre_thm
  (* define temporary abbreviation *)
  val silly_string = Theory.temp_binding "((step))"
  val step_def =
     new_definition
        (silly_string,mk_eq(mk_var(silly_string,type_of step_fun),step_fun))
  val main_def = RW [GSYM step_def] main_def
  val pre_def = RW [GSYM step_def] pre_def
  val step_const = (fst o dest_eq o concl) step_def
(*
  (* try automatically proving pre = T, i.e. termination *)
  val pre_thm = let
    val tt = (fst o dest_eq o concl o SPEC_ALL o RW1 [FUN_EQ_THM]) pre_def
    val goal = mk_forall(cdr tt,mk_eq(tt,``T:bool``))
    val dummy_name = "no_name"
    val c = (repeat car o fst o dest_eq o concl o SPEC_ALL) main_thm
    val v = mk_var(dummy_name,type_of c)
    val fake_eq = subst [c|->v] ((concl o SPEC_ALL) main_thm)
    val defn = Hol_defn dummy_name [ANTIQUOTE fake_eq]
    val gs = TotalDefn.guessR defn
    fun case_tac x =
      TotalDefn.WF_REL_TAC [ANTIQUOTE x]
      THEN SRW_TAC [] [] THEN SIMP_TAC std_ss [GSYM word_sub_def]
      THEN REPEAT (POP_ASSUM MP_TAC)
      THEN SIMP_TAC std_ss (!termination_simps) THEN NO_TAC
    val AUX_TAC = FIRST (map case_tac gs)
    (* set_goal([],goal) *)
    val tac =
      PURE_REWRITE_TAC [pre_def,tailrecTheory.SHORT_TAILREC_PRE_def]
      THEN MATCH_MP_TAC tailrecTheory.TAILREC_PRE_IMP
      THEN Tactical.REVERSE STRIP_TAC
      THEN1 (SIMP_TAC std_ss [pairTheory.FORALL_PROD]
             THEN SRW_TAC [] [step_def,LET_DEF])
      THEN SIMP_TAC std_ss [step_def,LET_DEF,pairTheory.FORALL_PROD,GUARD_def]
      THEN AUX_TAC
    val pre_thm = (snd o tac) ([],goal) []
    val _ = echo 1 " (termination automatically proved),"
    in pre_thm end handle HOL_ERR _ => pre_thm
*)
  (* prove lemmas for final proof *)
  val _ = echo 1 " proving certificate,"
  val (th1,th2) = (th,th)
  val finder = cdr o el 2 o list_dest dest_conj o fst o dest_imp
  val tac2 = SIMP_TAC std_ss [step_def]
             THEN REPEAT (AUTO_DECONSTRUCT_TAC finder)
             THEN SIMP_TAC std_ss [sumTheory.OUTL,sumTheory.OUTR,
                                   sumTheory.ISR,sumTheory.ISL]
  val thi = ISPEC step_const SPEC_SHORT_TAILREC
  val thi = RW [GSYM main_def, GSYM pre_def] thi
  val lemma1 = let
    val th1 = INST [mk_var("set@p",pc_type) |-> exit_tm] th1
    val th1 = DISCH_ALL_AS_SINGLE_IMP (RW [] th1)
    val post = (free_vars o cdr o snd o dest_imp o concl) th1
    val top = (free_vars o fst o dest_imp o concl) th1
    val new_top = filter is_new_var top
    val vs = op_set_diff aconv new_top (dest_tuple new_output @ output)
    val th1 = remove_primes (HIDE_POST_VARS vs th1)
    val pre = (free_vars o cdr o car o car o snd o dest_imp o concl) th1
    val ws = op_set_diff aconv pre (mk_var("p",pc_type)::input)
    val tm = (fst o dest_imp o concl o DISCH_ALL) th1
    val ts = (list_dest dest_forall o snd o dest_conj o fst o dest_imp o
              concl o SPEC_ALL) thi
    val goal = (fst o dest_imp o last) ts
    val goal = subst [el 1 ts |-> x_in, el 2 ts |-> new_output] goal
    val goal = mk_imp(goal,tm)
    val lemma = UNDISCH (auto_prove "lemma1" (goal,tac2))
    val lemma1 = DISCH_ALL (MP th1 lemma)
    val (_,_,_,q) = dest_spec (concl (UNDISCH th1))
    val ws = op_set_diff aconv ws (free_vars q)
    val lemma1 = HIDE_PRE_VARS ws lemma1
    in RW [GSYM step_def] lemma1 end
    handle e => (print "\n\nDecompiler failed to prove 'lemma 1'.\n\n"; raise e)
  val lemma2 = let
    val e_tm = subst [new_pos_subst] entry_tm
    val th2 = INST [mk_var("set@p",pc_type) |-> e_tm] th2
    val th2 = RW [WORD_ADD_0] th2
    val post = (free_vars o cdr o snd o dest_imp o concl) th1
    val top = (free_vars o fst o dest_imp o concl) th1
    val new_top = filter is_new_var top
    val vs = op_set_diff aconv new_top (dest_tuple new_input)
    val th2 = remove_primes (HIDE_POST_VARS vs th2)
    val pre = (free_vars o cdr o car o car o snd o dest_imp o concl) th2
    val vs = op_set_diff aconv pre (mk_var("p",pc_type)::input)
    val tm = (fst o dest_imp o concl o DISCH_ALL) th2
    val ts = (list_dest dest_forall o fst o dest_conj o fst o dest_imp o
              concl o SPEC_ALL) thi
    val goal = (fst o dest_imp o last) ts
    val goal = subst [el 1 ts |-> x_in, el 2 ts |-> new_input] goal
    val goal = mk_imp(goal,tm)
    val lemma = UNDISCH (auto_prove "lemma2" (goal,tac2))
    val lemma2 = DISCH_ALL (MP th2 lemma)
    val (_,_,_,q) = dest_spec (concl (UNDISCH th2))
    val ws = op_set_diff aconv vs (free_vars q)
    val lemma2 = HIDE_PRE_VARS ws lemma2
    in RW [GSYM step_def] lemma2 end
    handle e => (print "\n\nDecompiler failed to prove 'lemma 2'.\n\n"; raise e)
  val sort_conv = PRE_CONV (SEP_EXISTS_CONV SORT_SEP_CONV) THENC
                  POST_CONV (SEP_EXISTS_CONV (SEP_DISJ_CONV SORT_SEP_CONV))
  val lemma1 = CONV_RULE (RAND_CONV sort_conv) lemma1
  val lemma2 = CONV_RULE (RAND_CONV sort_conv) lemma2
  (* simplification for cases of non-recursive functions *)
  val simp_lemma = let
    val (x,y) = dest_eq (concl (SPEC_ALL main_thm))
    val _ = if can (find_term (fn tm => car x ~~ tm)) y then fail () else ()
    val goal = mk_eq((fst o dest_imp o concl o
      ISPEC (pairSyntax.mk_fst(mk_comb(step_fun,x_in)))) sumTheory.INL,F)
    val simp_lemma = auto_prove "simp_lemma" (goal,SIMP_TAC std_ss []
      THEN REPEAT (AUTO_DECONSTRUCT_TAC (cdr o cdr))
      THEN SIMP_TAC std_ss [])
    val simp_lemma = Q.SPEC `x` (GEN_TUPLE x_in simp_lemma)
    val simp_lemma = PURE_REWRITE_RULE [GSYM step_def] simp_lemma
    in GEN_ALL simp_lemma end handle HOL_ERR _ => TRUTH
  (* deal with SEP_DISJ in post -- move to pre *)
  val lemma1 = DISCH_ALL (MATCH_MP SPEC_PRE_DISJ_INTRO (UNDISCH lemma1))
               handle HOL_ERR _ => lemma1
  val lemma2 = DISCH_ALL (MATCH_MP SPEC_PRE_DISJ_INTRO (UNDISCH lemma2))
               handle HOL_ERR _ => lemma2
  (* certificate theorem *)
  fun remove_new_tags tm = let
    val vs = filter is_new_var (free_vars tm)
    in subst (map (fn v => v |-> strip_tag v) vs) tm end
  val (m,p,c,q) = (dest_spec o concl o UNDISCH_ALL) lemma1
  val thi = ISPEC (mk_pabs(x_in,p)) thi
  val thi = ISPEC (mk_pabs(x_out,remove_new_tags q)) thi
  val thi = ISPEC c thi
  val thi = ISPEC m thi
  val xi = GSYM (SIMP_CONV std_ss [] (mk_comb(mk_pabs(x_in,p),x_in)))
  val xin = GSYM (SIMP_CONV std_ss [] (mk_comb(mk_pabs(x_in,p),new_input)))
  val xon = GSYM (SIMP_CONV std_ss []
                    (mk_comb(mk_pabs(x_out,remove_new_tags q),new_output)))
  fun fix_star rw =
    SIMP_CONV (bool_ss++star_ss) []
    THENC ONCE_REWRITE_CONV
            [CONV_RULE (RATOR_CONV (SIMP_CONV (bool_ss++star_ss) [])) rw]
  val l1 = CONV_RULE (RAND_CONV (PRE_CONV (fix_star xi) THENC
                                 POST_CONV (fix_star xon))) lemma1
  val l2 = CONV_RULE (RAND_CONV (PRE_CONV (fix_star xi) THENC
                                 POST_CONV (fix_star xin))) lemma2
  val l1 = GEN_TUPLE x_in (GEN_TUPLE new_output l1)
  val l2 = GEN_TUPLE x_in (GEN_TUPLE new_input l2) handle HOL_ERR _ => l2
  val goal = (fst o dest_imp o concl) thi
  val th = auto_prove "decompiler certificate" (goal,
    STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [simp_lemma] THEN REWRITE_TAC [] THEN
           REPEAT STRIP_TAC THEN MATCH_MP_TAC l2 THEN FULL_SIMP_TAC std_ss [])
    THEN1 (REPEAT STRIP_TAC THEN MATCH_MP_TAC l1 THEN FULL_SIMP_TAC std_ss []))
  val th = MP thi th
  val th = SPEC x_in th
  val th = RW [GSYM SPEC_MOVE_COND] th
  val th = introduce_post_let th
  val th = INST [mk_var("()",``:unit``) |-> ``():unit``] th
  val th =
     th |> RW [SPEC_MOVE_COND] |> UNDISCH |> SIMP_RULE std_ss [SPEC_PRE_DISJ]
        |> CONJUNCTS |> hd |> DISCH_ALL |> RW [GSYM SPEC_MOVE_COND]
  val th = SPEC_ALL (SIMP_RULE bool_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th)
  val th = CONV_RULE (DEPTH_CONV DEST_NEW_VAR_CONV) th
  (* clean up and save function definitions *)
  val _ = delete_const (fst (dest_const step_const))
  val _ = echo 1 " done.\n"
  val _ = save_thm(name ^ "_def",main_thm)
  val _ = save_thm(name ^ "_pre_def",pre_thm)
  in (th,main_thm,pre_thm) end;


(* -------------------------------------------------------------------------- *)
(* Implementation of STAGE 4                                                  *)
(* -------------------------------------------------------------------------- *)

fun prepare_for_reuse [] (th,i,j) k = []
  | prepare_for_reuse (n::ns) (th,i,j) k = let
  val prefix = "new@"
  val th = ABBREV_CALL prefix th
  val mk_num = numSyntax.mk_numeral o Arbnum.fromInt
  val th = SIMP_RULE std_ss [] (INST [mk_var("pos",``:num``) |-> mk_num k] th)
  in (n,(th,i,j),NONE) :: prepare_for_reuse ns (th,i,j) (k+1) end;

fun decompile_part name thms (entry,exit)
      (function_in_out: (term * term) option) = let
  val t = generate_spectree thms (entry,exit)
  val th = merge_spectree name t
  val (th,def,pre) = extract_function name th entry exit function_in_out
  val (th,pre) = simplify_pre pre th
  val (th,def) = (!decompiler_finalise) (th,def)
  val def = modifier "func" def
  in (def,pre,th) end;

val fio = (NONE: (term * term) option)

fun decompile_io_with q (tools :decompiler_tools) name fio code =
let
  val _ = set_tools tools
  val (thms,loops) = stage_12 name tools (q code)
  fun decompile_all thms (defs,pres) [] prev =
         (LIST_CONJ defs,LIST_CONJ pres,prev)
    | decompile_all thms (defs,pres) ((entry,exit)::loops) prev = let
(*
  val (entry,exit)::loops = loops
*)
      val function_in_out = (NONE: (term * term) option)
      val suff = int_to_string (length loops)
      val (part_name,function_in_out) = if length loops = 0 then (name,fio)
                                        else (name ^ suff,function_in_out)
      val (def,pre,result) =
         decompile_part part_name thms (entry,exit) function_in_out
      val thms = prepare_for_reuse entry (result,0,SOME (hd exit)) 0 @ thms
      in decompile_all thms (def::defs,pre::pres) loops result end
  val (def,pre,result) = decompile_all thms ([],[]) loops TRUTH
  val exit = snd (last loops)
  val _ = add_decompiled (name,result,hd exit,SOME (hd exit))
  val result = if (get_abbreviate_code()) then result
               else UNABBREV_CODE_RULE result
  val func = RW [GSYM CONJ_ASSOC] (CONJ def pre)
  in (result,func) end;

fun decompile_with q tools name code = decompile_io_with q tools name NONE code;

val decompile_io =
   decompile_io_with (helperLib.quote_to_strings: term quotation -> string list)

val decompile =
   decompile_with (helperLib.quote_to_strings: string quotation -> string list)

val decompile_io_strings = decompile_io_with I
val decompile_strings = decompile_with I

fun basic_decompile_with q (tools :decompiler_tools) name function_in_out code =
let
  val _ = set_tools tools
  val (thms,loops) = stage_12 name tools (q code)
  val (entry,exit) = (fn (x,y) => (hd x, hd y)) (last loops)
  val (entry,exit) = ([entry],[exit])
  val (def,pre,result) = decompile_part name thms (entry,exit) function_in_out
  val _ = add_decompiled (name,result,hd exit,SOME (hd exit))
  val result =
     if (get_abbreviate_code()) then result else UNABBREV_CODE_RULE result
  in (result,CONJ def pre) end;

val basic_decompile =
   basic_decompile_with
      (helperLib.quote_to_strings: term quotation -> string list)

val basic_decompile_strings = basic_decompile_with I

end
