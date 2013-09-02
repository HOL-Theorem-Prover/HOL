structure rel_decompilerLib =
struct

local

open HolKernel Parse boolLib bossLib Lib;
open armTheory armLib arm_stepTheory pred_setTheory pairTheory optionTheory;
open arithmeticTheory wordsTheory wordsLib addressTheory combinTheory pairSyntax;
open sumTheory whileTheory;

open arm_relTheory arm_relLib;


(* ========================================================================== *

  The decompiler as three phases:
   1. derive specs for each instruction
   2. calcuate CFG and split into separate 'decompilation rounds'
   3. for each round: compose specs together to produce function

 * ========================================================================== *)

val code_abbrevs = ref ([]:thm list);
fun add_code_abbrev th = (code_abbrevs := th::(!code_abbrevs));

val decomp_mem = ref ([]:(string * thm * int) list);
fun add_decomp name th len = (decomp_mem := ((name,th,len)::(!decomp_mem)));

(* PHASE 1 -- evaluate model *)

fun strip_string s = let
  fun strip_space [] = []
    | strip_space (x::xs) =
        if mem x [#" ",#"\t",#"\n"] then strip_space xs else x::xs
  in (implode o rev o strip_space o rev o strip_space o explode) s end;

fun quote_to_strings (q: term quotation) = let (* turns a quote `...` into a list of strings *)
  fun get_QUOTE (QUOTE t) = t | get_QUOTE _ = fail()
  val xs = explode (get_QUOTE (hd q))
  fun strip_comments l [] = []
    | strip_comments l [x] = if 0 < l then [] else [x]
    | strip_comments l (x::y::xs) =
        if x = #"(" andalso y = #"*" then strip_comments (l+1) xs else
        if x = #"*" andalso y = #")" then strip_comments (l-1) xs else
        if 0 < l    then strip_comments l (y::xs) else x :: strip_comments l (y::xs)
  fun lines [] [] = []
    | lines xs [] = [implode (rev xs)]
    | lines xs (y::ys) =
        if mem y [#"\n",#"|"]
        then implode (rev xs) :: lines [] ys
        else lines (y::xs) ys
  val zs = lines [] (strip_comments 0 xs)
  val qs = filter (fn z => not (z = "")) (map strip_string zs)
  in qs end;

fun derive_specs code = let
  fun option_add k NONE = NONE
    | option_add k (SOME n) = SOME (k+n)
  val p = mk_var("r15",``:word32``)
  fun set_pc n (th,l,j) = let
    val p' = ``^p + n2w ^(numSyntax.term_of_int n)``
    val th = INST [p|->p'] th
             |> SIMP_RULE std_ss [word_arith_lemma1,word_arith_lemma2]
             |> SIMP_RULE std_ss [word_arith_lemma3,word_arith_lemma4]
    in (th,l,option_add n j) end
  fun option_apply f NONE = NONE
    | option_apply f (SOME x) = SOME (f x)
  fun foo hex n =
    if String.isPrefix "insert:" hex then let
      val name = String.substring(hex,size("insert:"),size(hex)-size("insert:"))
                 |> strip_string
      val (_,th,len) = first (fn (n,_,_) => n = name) (!decomp_mem)
      in (n+len,set_pc n (th |> UNDISCH_ALL,len,SOME len),NONE) end
    else let
      val ((x,l,j),y) = l3_triple hex
      in (n+l, set_pc n (x,l,j), option_apply (set_pc n) y) end
  val l = length code
  fun derive n [] aux l = rev aux
    | derive n (x::xs) aux l = let
        val _ = helperLib.echo 1 (" " ^ (int_to_string l))
        val (n',x,y) = foo x n
        in derive n' xs ((n,x,y)::aux) (l-1) end
  in derive 0 code [] l end

fun model tm = tm |> rator |> rator |> rator |> rand

fun abbreviate_code name thms = let
  fun extract_code (_,(th,_,_),_) = th |> concl |> rator |> rand
  val cs = map extract_code thms
  val ty = (hd o snd o dest_type o type_of o hd) cs
  val tm = foldr pred_setSyntax.mk_union (pred_setSyntax.mk_empty ty) cs
  val cth = QCONV (PURE_REWRITE_CONV [INSERT_UNION_EQ,UNION_EMPTY]) tm
  val c = (rand o concl) cth
  val (_,(th,_,_),_) = hd thms
  val m = model (th |> concl)
  val model_name = (helperLib.to_lower o fst o dest_const) m
  val x = list_mk_pair (free_vars c)
  val def_name = name ^ "_" ^ model_name
  val v = mk_var(def_name,type_of(mk_pabs(x,c)))
  val code_def = new_definition(def_name ^ "_def",mk_eq(mk_comb(v,x),c))
  val _ = add_code_abbrev code_def
  fun triple_apply f (y,(th1,x1:int,x2:int option),NONE) = (y,(f th1,x1,x2),NONE)
    | triple_apply f (y,(th1,x1,x2),SOME (th2,y1:int,y2:int option)) =
        (y,(f th1,x1,x2),SOME (f th2,y1,y2))
  val code_thm = CONV_RULE (RAND_CONV (fn _ => GSYM cth)) (SPEC_ALL code_def)
  fun foo th = let
    val th1 = MATCH_MP TRIPLE_EXTEND th
    val th1 = SPEC ((fst o dest_eq o concl o SPEC_ALL) code_def) th1
    val goal = (fst o dest_imp o concl) th1
    val lemma = helperLib.auto_prove "abbreviate_code" (goal,
        REPEAT (REWRITE_TAC [code_thm,SUBSET_DEF,IN_UNION] THEN REPEAT STRIP_TAC
                THEN ASM_REWRITE_TAC [] THEN (fn _ => fail()))
        THEN REWRITE_TAC [EMPTY_SUBSET]
        THEN REWRITE_TAC [SUBSET_DEF,IN_INSERT,IN_UNION,NOT_IN_EMPTY,code_def]
        THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [])
    val th1 = MP th1 lemma
    in th1 end
  val thms = map (triple_apply foo) thms
  in thms end

fun stage_1 name qcode = let
  val code = quote_to_strings qcode
  val thms = derive_specs code

  val thms = abbreviate_code name thms
  in thms end;


(* PHASE 2 -- compute CFG *)

fun extract_graph thms = let
  fun extract_jumps (i,(_,_,j),NONE) = [(i,j)]
    | extract_jumps (i,(_,_,j),SOME (_,_,k)) = [(i,j),(i,k)]
  val jumps = foldl (fn (x,y) => extract_jumps x @ y) [] thms
  in jumps end;

fun all_distinct [] = []
  | all_distinct (x::xs) =
      if mem x xs then all_distinct xs else x :: all_distinct xs

fun drop_until P [] = []
  | drop_until P (x::xs) = if P x then x::xs else drop_until P xs

fun jumps2edges jumps = let
  fun h (i,NONE) = []
    | h (i,SOME j) = [(i,j)]
  in foldl (fn (x,y) => h x @ y) [] jumps end;

fun subset [] ys = true
  | subset (x::xs) ys = mem x ys andalso subset xs ys

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
    in Lib.flatten xs end
  val paths = all_paths_from edges 0 []
  (* get looping points *)
  fun is_loop xs = mem (last xs) (butlast xs)
  val loops = all_distinct (map last (filter is_loop paths))
  (* find loop bodies and tails *)
  fun loop_body_tail i = let
    val bodies = filter (fn xs => last xs = i) paths
    val bodies = filter is_loop bodies
    val bodies = map (drop_until (fn x => x = i) o butlast) bodies
    val bodies = all_distinct (Lib.flatten bodies)
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
    val ls = Lib.flatten (map (fn (x,y,z) => x) zs)
    val qs = map (fn (x,y,z) => (x,y,map hd z)) zs
    fun f ys = filter (fn x => mem x ls andalso (not (mem x ys)))
    val qs = map (fn (x,y,z) => (x,all_distinct (f x y @ f x z))) qs
    fun cross [] ys = []
      | cross (x::xs) ys = map (fn y => (x,y)) ys @ cross xs ys
    val edges = Lib.flatten (map (fn (x,y) => cross x y) qs)
    val paths = map (fn i => all_paths_from edges i []) ls
    val goals = map (fn (x,y) => (y,x)) edges
    fun sat_goal ((i,j),path) = (hd path = i) andalso (mem j (tl path))
    val (i,j) = fst (hd (filter sat_goal (cross goals (Lib.flatten paths))))
    val (p1,q1,x1) = hd (filter (fn (x,y,z) => mem i x) zs)
    val (p2,q2,x2) = hd (filter (fn (x,y,z) => mem j x) zs)
    val (p,q,x) = (p1 @ p2, all_distinct (q1 @ q2), x1 @ x2)
    val zs = (p,q,x) :: filter (fn (x,y,z) => not (mem i x) andalso not (mem j x)) zs
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
  val zs = if filter (fn (x,y) => mem 0 x andalso subset exit y) zs = [] then zs @ [zero] else zs
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
  in loops end;

fun forks [] = []
  | forks ((x1,y1)::xs) =
  if can (first (fn (x2,_) => x1 = x2)) xs then
    x1 :: (forks (filter (fn (x2,_) => x2 <> x1) xs))
  else forks xs

fun stage_12 name qcode = let
  val thms = stage_1 name qcode
  val jumps = extract_graph thms
  val loops = extract_loops jumps
  val loops =
    case loops of
      [([0],[n])] => let
        val fs = forks jumps |> sort (fn x => fn y => x >= y)
        in map (fn f => ([f],[n])) fs @ [([0],[n])] end
    | other => other
  in (thms,loops) end;


(* PHASE 3 -- compose and extract *)

datatype compose_tree =
    End of int
  | Repeat of int
  | Cons of thm * compose_tree
  | Merge of term * compose_tree * compose_tree
  | ConsMerge of term * thm * thm * compose_tree

fun is_rec (Repeat _) = true
  | is_rec (End _) = false
  | is_rec (Cons (_,t)) = is_rec t
  | is_rec (Merge (_,t1,t2)) = is_rec t1 orelse is_rec t2
  | is_rec (ConsMerge (_,_,_,t)) = is_rec t

fun build_compose_tree (b,e) thms = let
  fun find_next i = first (fn (n,_,_) => n = i) thms
  fun sub init NONE = failwith("cannot handle bad exists")
    | sub init (SOME i) =
      if mem i e then End i else
      if not init andalso mem i b then Repeat i else
        case find_next i of
          (_,(th1,l1,x1),NONE) => Cons (th1,sub false x1)
        | (_,(th1,l1,x1),SOME (th2,l2,x2)) =>
          if x1 = x2 then let
            val t1 = sub false x1
            val tm = find_term (can (match_term ``Abbrev b``)) (hd (hyp th1)) handle Empty =>
                     find_term (can (match_term ``Abbrev b``)) (concl th1)
            in ConsMerge (rand tm,th1,th2,t1) end
          else let
            val t1 = Cons (th1,sub false x1)
            val t2 = Cons (th2,sub false x2)
            val tm = find_term (can (match_term ``Abbrev b``)) (hd (hyp th1)) handle Empty =>
                     find_term (can (match_term ``Abbrev b``)) (concl th1)
            in Merge (rand tm,t1,t2) end
  val t = sub true (SOME (hd b))
  in t end;

val l1 = ref TRUTH;
val l2 = ref TRUTH;
val l3 = ref T;

fun VALUE_CONV c = RAND_CONV (RAND_CONV c)

fun compose th1 th2 = let
  val th3 = MATCH_MP (MATCH_MP TRIPLE_COMPOSE_ALT th2) th1
  in if length (hyp th3) = 0 then th3 else let
    val tm = hd (hyp th3)
    val lemma = SYM (ASSUME tm)
    val (lhs,rhs) = dest_eq tm
    val th4 = th3 |> CONV_RULE (VALUE_CONV (PairRules.UNPBETA_CONV rhs
                                THENC REWR_CONV (SYM (SPEC_ALL LET_THM))
                                THENC (RAND_CONV (fn _ => lemma))))
    fun ii lhs rhs = let
      val (x,y) = dest_pair rhs
      val x1 = pairSyntax.mk_fst lhs
      val y1 = pairSyntax.mk_snd lhs
      in (x |-> x1) :: ii y1 y end handle HOL_ERR _ => [rhs |-> lhs]
    val th5 = INST (ii lhs rhs) (DISCH_ALL th4)
              |> CONV_RULE ((RATOR_CONV o RAND_CONV) (PURE_REWRITE_CONV [PAIR]))
              |> (fn th => MP th (REFL lhs))
    in th5 end end
  handle HOL_ERR e => (l1 := th1; l2 := th2; raise HOL_ERR e)

(*
val th1 = !l1
val th2 = !l2
val tm = !l3
*)

fun merge tm th1 th2 = let
  val th1 = DISCH tm (th1 |> REWRITE_RULE [markerTheory.Abbrev_def,CONTAINER_def])
  val th2 = DISCH (mk_neg tm) (th2 |> REWRITE_RULE [markerTheory.Abbrev_def,CONTAINER_def])
  val th3 = MATCH_MP COND_MERGE (CONJ th1 th2)
  val th3 = th3 |> CONV_RULE ((RAND_CONV o RAND_CONV) (SIMP_CONV bool_ss []))
  in th3 end
  handle HOL_ERR e => (l1 := th1; l2 := th2; l3 := tm; raise HOL_ERR e)

(*
  fun fan (End i) = 1
    | fan (Repeat i) = 1
    | fan (Cons (th,t)) = fan t
    | fan (Merge (tm,t1,t2)) = fan t1 + fan t2
    | fan (ConsMerge (tm,th1,th2,t)) = fan t + fan t

  fan t
*)

fun round name (b,e) thms = let
  val _ = print "Building composition tree, "
  val t = build_compose_tree (b,e) thms
  val loop = is_rec t
  val (_,(th,_,_),_) = first (fn (n,_,_) => (n = 0)) thms
  val m = model (concl th)
  val code = (concl th) |> rator |> rand
  val p = mk_var("r15",``:word32``)
  val pre = th |> REWRITE_RULE [WORD_ADD_0] |> concl |> rator |> rator |> rand
  val affected_vars = pre |> free_vars |> filter (fn v => not (v = p))
  val input = pairSyntax.list_mk_pair affected_vars
  fun inst_pc n = let
    val p' = ``^p + n2w ^(numSyntax.term_of_int n)``
    in subst [p|->p'] end
  fun get_assert i = (mk_pabs(input,inst_pc i pre))
  val pre = get_assert (hd b)
  val post = get_assert (hd e)
  val exit_th = if loop then
                  ISPEC m TRIPLE_REFL |> SPEC code
                  |> SPEC ``my_sum_case ^pre ^post (INR ^(input))``
                  |> CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [my_sum_case_def]))
                else ISPEC m TRIPLE_REFL |> SPEC code |> SPEC (mk_comb(post,input))
                  |> CONV_RULE (RATOR_CONV (SIMP_CONV std_ss []))
  val enter_post = if loop then ``my_sum_case ^pre ^post (INL ^(input))`` else T
  val enter_th = if loop then ISPEC m TRIPLE_REFL |> SPEC code |> SPEC enter_post
                              |> CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [my_sum_case_def])) else TRUTH
  val _ = print "done.\n"
  (* perform composition *)
  val _ = print "Perform composition, "
  fun comp (End i) = exit_th
    | comp (Repeat i) = enter_th
    | comp (Cons (th,t)) = compose th (comp t)
    | comp (Merge (tm,t1,t2)) = merge tm (comp t1) (comp t2)
    | comp (ConsMerge (tm,th1,th2,t)) = let
        val res = comp t
        in merge tm (compose th1 res) (compose th2 res) end
  val th = comp t
  val _ = print "done.\n"
  val th = th |> CONV_RULE ((RAND_CONV o RAND_CONV) (PairRules.UNPBETA_CONV input))
  val th = if loop then let
    val _ = print "Apply loop rule, "
    (* apply loop rule *)
    val lemma = (mk_comb(pre,input)) |> SIMP_CONV std_ss [my_sum_case_def]
    val th = th |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV) (fn _ => GSYM lemma))
    val x = mk_var("x",type_of input)
    val tm = mk_forall(x,concl th |> subst [input |-> x])
    val lemma = prove(tm,
      FULL_SIMP_TAC pure_ss [FORALL_PROD] THEN REPEAT STRIP_TAC
      THEN MATCH_MP_TAC (DISCH T th) THEN FULL_SIMP_TAC std_ss [])
    val th = MATCH_MP SHORT_TERM_TAILREC lemma
             |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL THENC SIMP_CONV std_ss [])
             |> SPEC input |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV) (PairRules.PBETA_CONV))
    val _ = print "done.\n"
    in th end else th
  val _ = print "Define extracted function, "
  val ff = th |> concl |> rand |> rand |> rator
  val def = new_definition(name ^ "_def",mk_eq(mk_var(name,type_of ff),ff))
  val th = th |> CONV_RULE ((RAND_CONV o RAND_CONV o RATOR_CONV) (fn _ => GSYM def))
  (* clean up result *)
  val lemma = mk_eq(mk_comb(concl def |> dest_eq |> fst,input),swap_primes input) |> ASSUME
  val result = th |> CONV_RULE ((RAND_CONV o RAND_CONV) (fn _ => lemma)
                                THENC RAND_CONV PairRules.PBETA_CONV) |> DISCH_ALL
  val _ = print "done.\n"
  in (def,result) end;

in

fun fast_decompile name qcode = let
  val (thms,loops) = time (stage_12 name) qcode
  fun rounds loops thms defs = let
    val (b,e) = hd loops
    val loops = tl loops
    val n = length loops
    val part_name = (if n = 0 then name
                     else name ^ "_part" ^ (int_to_string n))
    val (def,result) = round part_name (b,e) thms
    val thms = (hd b,(UNDISCH_ALL result,0,SOME (hd e)),NONE)::thms
    in if n = 0 then (result,rev (def::defs)) else rounds loops thms (def::defs) end
  val (res,defs) = time (rounds loops thms) []
  val _ = add_decomp name res (loops |> last |> snd |> hd)
  in (res,LIST_CONJ defs) end

end

end
