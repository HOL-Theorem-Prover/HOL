structure core_decompilerLib :> core_decompilerLib =
struct

open HolKernel Parse boolLib bossLib
open helperLib tripleTheory tripleSyntax

val ERR = Feedback.mk_HOL_ERR "core_decompilerLib"

(* ========================================================================== *

  The decompiler as three phases:
   1. derive specs for each instruction
   2. calcuate CFG and split into separate 'decompilation rounds'
   3. for each round: compose specs together to produce function

 * ========================================================================== *)

(* Hooks for ISA specific tools.  *)

val get_triple =
   ref (fn _: string =>
          (raise ERR "get_triple" "uninitialised"): helperLib.instruction)
val initialise = ref (Lib.I: unit -> unit)
val pc = ref boolSyntax.F
val pc_size = ref 0
val at_pc_conv = ref (Lib.I: conv -> conv)
val swap_primes = ref (Lib.I: term -> term)
val code_parser = ref (NONE: (string quotation -> string list) option)

fun add_prime v = Term.mk_var (fst (Term.dest_var v) ^ "'", Term.type_of v)

fun configure
   {triple_fn = f,
    init_fn = i,
    pc_tm = p,
    pc_conv = c,
    component_vars = vs
    } =
   ( get_triple := f
     ; initialise := i
     ; pc := p
     ; at_pc_conv := c
     ; pc_size := Arbnum.toInt (wordsSyntax.size_of p)
     ; swap_primes :=
         Term.subst
            (List.concat
               (List.map
                  (fn v =>
                     let val pv = add_prime v in [v |-> pv, pv |-> v] end) vs))
   )

val code_abbrevs = ref ([]:thm list);
fun add_code_abbrev th = (code_abbrevs := th::(!code_abbrevs));

val decomp_mem = ref ([]:(string * thm * int) list);
fun add_decomp name th len = (decomp_mem := ((name,th,len)::(!decomp_mem)));

(* PHASE 1 -- evaluate model *)

fun add_to_pc n =
   [!pc |-> wordsSyntax.mk_word_add (!pc, wordsSyntax.mk_wordii (n, !pc_size))]

local
   (* vt100 escape string *)
   val ESC = String.str (Char.chr 0x1B)
in
   val inPlaceEcho =
      if !Globals.interactive
         then fn s => helperLib.echo 1 ("\n" ^ s)
      else fn s => helperLib.echo 1 (ESC ^ "[1K" ^ "\n" ^ ESC ^ "[A" ^ s)
end

local
   val POST_ASSERT = RAND_CONV o RAND_CONV
   val PRE_ASSERT = RATOR_CONV o RATOR_CONV o POST_ASSERT
   val ARITH_SUB_CONV = wordsLib.WORD_ARITH_CONV THENC wordsLib.WORD_SUB_CONV
   fun is_reducible tm =
      case Lib.total wordsSyntax.dest_word_add tm of
         SOME (v, _) => not (Term.is_var v)
       | _ => not (boolSyntax.is_cond tm)
   fun PC_CONV tm =
      if is_reducible tm then (!at_pc_conv) ARITH_SUB_CONV tm else ALL_CONV tm
   val PC_RULE = Conv.CONV_RULE (PRE_ASSERT PC_CONV THENC POST_ASSERT PC_CONV)
   fun set_pc n (th, l, j) =
      (PC_RULE (Thm.INST (add_to_pc n) th), l, Option.map (fn i => n + i) j)
   fun derive1 hex n =
      if String.isPrefix "insert:" hex
         then let
                 val name =
                    helperLib.remove_whitespace
                       (String.extract (hex, size ("insert:"), NONE))
                 val (_, th, l) = first (fn (n, _, _) => n = name) (!decomp_mem)
              in
                 (n + l, (set_pc n (UNDISCH_ALL th, l, SOME l), NONE))
              end
      else let
              val (x as (_, l, _), y) = (!get_triple) hex
           in
              (n + l, (set_pc n x, Option.map (set_pc n) y))
           end
   fun derive n [] aux l = rev aux
     | derive n (x::xs) aux l =
         let
            val () = inPlaceEcho (" " ^ Int.toString l)
            val (n', (x, y)) = derive1 x n
         in
            derive n' xs ((n, (x, y)) :: aux) (l - 1)
         end
in
   fun derive_specs name code =
      let
         val l = length code
         val s = if l = 1 then "" else "s"
      in
         echo 1 ("\nDeriving instruction spec" ^ s ^ " for " ^
                 Lib.quote name ^ "...\n\n")
         ; derive 0 code [] l before
           inPlaceEcho
              (" Finished " ^ Int.toString l ^ " instruction" ^ s ^ ".\n\n")
      end
end

local
   val tac =
      SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF, pred_setTheory.UNION_DEF]
   val IN_DEFN = Q.prove(`(c = b) ==> a IN b ==> a IN c`, tac)
   val SUBSET_DEFN = Q.prove(`(c = b) ==> a SUBSET b ==> a SUBSET c`, tac)
   val IN_LEFT_DEFN = Q.prove(`(c = b UNION d) ==> a IN b ==> a IN c`, tac)
   val IN_RIGHT_DEFN =
      Q.prove(`(c = b UNION d) ==> a SUBSET d ==> a SUBSET c`, tac)
   val SUBSET_REST = Q.prove(`a SUBSET b ==> a SUBSET (b UNION d)`, tac)
   val SUBSET_UNION2 = Thm.CONJUNCT2 pred_setTheory.SUBSET_UNION
   fun subset_conv rwts =
      Conv.LAND_CONV
        (PURE_REWRITE_CONV ([boolTheory.AND_CLAUSES,
                             pred_setTheory.EMPTY_SUBSET,
                             pred_setTheory.INSERT_SUBSET,
                             pred_setTheory.UNION_SUBSET] @ rwts))
      THENC PURE_REWRITE_CONV [boolTheory.IMP_CLAUSES]
   val list_mk_union =
      HolKernel.list_mk_lbinop (Lib.curry pred_setSyntax.mk_union)
   val strip_union = HolKernel.strip_binop (Lib.total pred_setSyntax.dest_union)
   val get_model_name =
      helperLib.to_lower o fst o Term.dest_const o tripleSyntax.dest_model o
      Thm.concl
   fun extract_code (_, ((th, _, _), _)) = tripleSyntax.dest_code (Thm.concl th)
   val get_code =
      (((Lib.mk_set o List.concat o List.map pred_setSyntax.strip_set) ##
        Lib.mk_set) o
       List.partition pred_setSyntax.is_insert o
       List.concat o List.map (strip_union o extract_code)):
       (int * helperLib.instruction) list -> term list * term list
   val (CONJ1_CONV, CONJ2_CONV) =
      case Drule.CONJUNCTS (Drule.SPEC_ALL boolTheory.OR_CLAUSES) of
         c1 :: c2 :: _ => (Conv.REWR_CONV c1, Conv.REWR_CONV c2)
       | _ => fail()
in
   fun abbreviate_code _ [] = raise ERR "abbreviate_code" "no code"
     | abbreviate_code name (thms as (_: int, ((th, _, _), _)) :: _) =
      let
         val (newcode, acode) = get_code thms
         val (cs, l, r) =
            if List.null acode
               then let
                       val l = pred_setSyntax.mk_set newcode
                    in
                       (l, l, boolSyntax.F)
                    end
            else if List.null newcode
               then let
                       val r = list_mk_union acode
                    in
                       (r, boolSyntax.F, r)
                    end
            else let
                     val l = pred_setSyntax.mk_set newcode
                     val r = list_mk_union acode
                 in
                     (pred_setSyntax.mk_union (l, r), l, r)
                 end
         val def_name = name ^ "_" ^ get_model_name th
         val x = pairSyntax.list_mk_pair (Term.free_vars cs)
         val v =
            Term.mk_var (def_name, Term.type_of (pairSyntax.mk_pabs (x, cs)))
         val code_def =
            Definition.new_definition
               (def_name ^ "_def", boolSyntax.mk_eq (Term.mk_comb (v, x), cs))
         val () = add_code_abbrev code_def
         val spec_code_def = Drule.SPEC_ALL code_def
         val tm = boolSyntax.lhs (Thm.concl spec_code_def)
         val sty = Term.type_of cs
         val ty = pred_setSyntax.dest_set_type sty
         val inst_ty = Thm.INST_TYPE [Type.alpha |-> ty]
         fun f thm = MATCH_MP thm spec_code_def
         val (in_left, in_right) =
            if List.null newcode
               then (TRUTH, f SUBSET_DEFN)
            else if List.null acode
               then (f IN_DEFN, TRUTH)
            else (f IN_LEFT_DEFN, f IN_RIGHT_DEFN)
         val rwts1 =
            if List.null newcode
               then []
            else let
                    val a = Term.mk_var ("a", ty)
                    val refl_cnv =
                       Conv.REWR_CONV (inst_ty boolTheory.REFL_CLAUSE)
                    val in_cnv =
                       Conv.REWR_CONV (inst_ty pred_setTheory.IN_INSERT)
                    fun expand_in n tm =
                       if n <= 0
                          then (in_cnv
                                THENC Conv.LAND_CONV refl_cnv
                                THENC CONJ1_CONV) tm
                       else (in_cnv
                             THENC Conv.RAND_CONV (expand_in (n - 1))
                             THENC CONJ2_CONV) tm
                    fun cnv i = EQT_ELIM o expand_in i
                 in
                    Lib.mapi
                       (fn i => fn c =>
                           MP (Thm.INST [a |-> c] in_left)
                              (cnv i (pred_setSyntax.mk_in (c, l)))) newcode
                 end
         val rwts2 =
            if List.null acode
               then []
            else let
                    val a = Term.mk_var ("a", sty)
                    val n = List.length acode - 1
                    val tac1 = MATCH_MP_TAC (inst_ty SUBSET_REST)
                    val tac2 =
                       REWRITE_TAC
                         [inst_ty SUBSET_UNION2, pred_setTheory.SUBSET_REFL]
                 in
                     Lib.mapi
                        (fn i => fn c =>
                            MP (Thm.INST [a |-> c] in_right)
                            (Tactical.prove
                               (pred_setSyntax.mk_subset (c, r),
                                NTAC (n - i) tac1 THEN tac2))) acode
                 end
         val rule = CONV_RULE (subset_conv (rwts1 @ rwts2)) o
                    Thm.SPEC tm o MATCH_MP TRIPLE_EXTEND
      in
         List.map (fn (i, x) => (i, helperLib.instruction_apply rule x)) thms
      end
end

fun stage_1 name qcode =
   let
      val p = Option.getOpt (!code_parser, helperLib.quote_to_strings)
   in
      (!initialise) ()
    ; abbreviate_code name (derive_specs name (p qcode))
   end

(* Testing
val name = "test"
val qcode = `e59f322c  00012f94
             e59f222c  00012f80
             edd37a00`
val (_, ((th, _, _), _)) = hd thms
*)


(* PHASE 2 -- compute CFG *)

val extract_graph =
   List.concat o
   List.map (fn (i, ((_, _, j), NONE): helperLib.instruction) => [(i: int, j)]
              | (i, ((_, _, j), SOME (_, _, k))) => [(i, j), (i, k)])

val jumps2edges =
    List.concat o
    List.map (fn (i, NONE) => []: (int * int) list
               | (i, SOME j) => [(i, j)])

val all_distinct = Lib.mk_set

fun drop_until P [] = []
  | drop_until P (x :: xs) = if P x then x :: xs else drop_until P xs

fun subset [] ys = true
  | subset (x :: xs) ys = mem x ys andalso subset xs ys

local
   fun all_paths_from edges i prefix =
      let
         fun f [] = []
           | f ((k, j) :: xs) = if i = k then j :: f xs else f xs
        val next = all_distinct (f edges)
        val prefix = prefix @ [i]
        val xs = map (fn x => if mem x prefix
                                 then [prefix @ [x]]
                              else all_paths_from edges x prefix) next
        val xs = if xs = [] then [[prefix]] else xs
      in
         Lib.flatten xs
      end

   fun is_loop xs = Lib.mem (List.last xs) (Lib.butlast xs)

   (* clean loop tails *)
   fun clean_tails (i, xs, tails) =
      (i, xs,
       List.mapPartial
          (fn t => let
                      val l = drop_until (fn x => not (mem x xs)) t
                   in
                      if List.null l then NONE else SOME l
                   end) tails)

   fun cross [] ys = []
     | cross (x :: xs) ys = map (fn y => (x, y)) ys @ cross xs ys

   fun sat_goal ((i, j), path) = hd path = i andalso mem j (tl path)

   fun find_and_merge zs =
      let
         val ls = Lib.flatten (map (fn (x, y, z) => x) zs)
         val qs = map (fn (x, y, z) => (x, y, map hd z)) zs
         fun f ys = filter (fn x => mem x ls andalso (not (mem x ys)))
         val qs = map (fn (x, y, z) => (x, all_distinct (f x y @ f x z))) qs
         val edges = Lib.flatten (map (fn (x,y) => cross x y) qs)
         val paths = map (fn i => all_paths_from edges i []) ls
         val goals = map (fn (x,y) => (y,x)) edges
         val (i, j) =
            fst (hd (filter sat_goal (cross goals (Lib.flatten paths))))
         val (p1, q1, x1) = hd (filter (fn (x,y,z) => mem i x) zs)
         val (p2, q2, x2) = hd (filter (fn (x,y,z) => mem j x) zs)
         val (p, q, x) = (p1 @ p2, all_distinct (q1 @ q2), x1 @ x2)
         val zs =
            (p,q,x) ::
            filter (fn (x, y, z) => not (mem i x) andalso not (mem j x)) zs
         val zs = map clean_tails zs
      in
         zs
      end

   fun mem_all x = List.all (Lib.mem x)

   fun find_exit_points (x, y, z) =
      let
         val q = hd (filter (fn x => mem_all x (tl z)) (hd z))
      in
         (x, [q])
      end
      handle Empty => (x, all_distinct (map hd z))

   fun list_before x y [] = true
     | list_before x y (z :: zs) =
           z <> y andalso (z = x orelse list_before x y zs)

   val int_sort = Lib.sort (Lib.curry (op Int.<=))
in
   fun extract_loops jumps =
      let
         (* find all possible paths *)
         val edges = jumps2edges jumps
         val paths = all_paths_from edges 0 []
         (* get looping points *)
         val loops = all_distinct (map last (filter is_loop paths))
         (* find loop bodies and tails *)
         fun loop_body_tail i =
            let
               val bodies = filter (fn xs => last xs = i) paths
               val bodies = filter is_loop bodies
               val bodies = map (drop_until (fn x => x = i) o butlast) bodies
               val bodies = all_distinct (Lib.flatten bodies)
               val tails =
                  filter (fn xs => mem i xs andalso not (last xs = i)) paths
               val tails = map (drop_until (fn x => x = i)) tails
            in
               (fn (x, y, z) => ([x], y, z)) (clean_tails (i, bodies, tails))
            end
         val zs = map loop_body_tail loops
         (* merge combined loops *)
         val zs = repeat find_and_merge zs
         (* attempt to find common exit point *)
         val zs = map find_exit_points zs
         (* finalise *)
         val exit = (all_distinct o map last o filter (not o is_loop)) paths
         val zero = ([0], exit)
         val zs =
            if List.null
                 (filter (fn (x, y) => mem 0 x andalso subset exit y) zs)
               then zs @ [zero]
            else zs
         fun compare (xs, _) (ys, _) =
            let
               val x = hd xs
               val y = hd ys
               val p = hd (filter (fn xs => mem x xs andalso mem y xs) paths)
            in
               not (list_before x y p)
            end
            handle Empty => false
         val loops = sort compare zs
         (* sort internal  *)
         val loops = map (int_sort ## int_sort) loops
      in
         loops
      end
end

local
   fun forks_acc a =
     fn [] => List.rev a
      | (x1, _) :: xs =>
          if List.exists (fn (x2, _) => x2 = x1) xs
             then forks_acc (x1 :: a) (filter (fn (x2, _) => x2 <> x1) xs)
          else forks_acc a xs
in
   val forks = forks_acc []
end

fun stage_12 name qcode =
   let
      val thms = stage_1 name qcode
      val jumps = extract_graph thms
      val loops = extract_loops jumps
      val loops =
         case loops of
            [([0], [n])] =>
               let
                  val fs = Lib.sort (Lib.curry (op >=)) (forks jumps)
               in
                  map (fn f => ([f], [n])) fs @ [([0], [n])]
               end
          | other => other
   in
      (thms, loops)
   end


(* PHASE 3 -- compose and extract *)

datatype compose_tree =
    End of int
  | Repeat of int
  | Cons of thm * compose_tree
  | Merge of term * compose_tree * compose_tree
  | ConsMerge of term * thm * thm * compose_tree

fun is_rec (Repeat _) = true
  | is_rec (End _) = false
  | is_rec (Cons (_, t)) = is_rec t
  | is_rec (Merge (_, t1, t2)) = is_rec t1 orelse is_rec t2
  | is_rec (ConsMerge (_, _, _, t)) = is_rec t

local
   val (_, _, _, is_abbrev) = HolKernel.syntax_fns1 "marker" "Abbrev"
   fun get_Abbrev th =
      case Thm.hyp th of
         [h] => Lib.with_exn (Term.rand o HolKernel.find_term is_abbrev) h
                   (ERR "get_Abbrev" "Abbrev not found")
       | _ => raise ERR "get_Abbrev" "not a single hyp"
in
   fun build_compose_tree (b, e) thms =
      let
         fun find_next i = first (fn (n, _:helperLib.instruction) => n = i) thms
         fun sub init NONE =
               raise ERR "build_compose_tree" "cannot handle bad exists"
           | sub init (SOME i) =
             if mem i e
                then End i
             else if not init andalso mem i b
                then Repeat i
             else case find_next i of
                     (_, ((th1, l1, x1), NONE)) => Cons (th1, sub false x1)
                   | (_, ((th1, l1, x1), SOME (th2, l2, x2))) =>
                     if x1 = x2
                        then ConsMerge (get_Abbrev th1, th1, th2, sub false x1)
                     else let
                             val t1 = Cons (th1, sub false x1)
                             val t2 = Cons (th2, sub false x2)
                          in
                             Merge (get_Abbrev th1, t1, t2)
                          end
      in
         sub true (SOME (hd b))
      end
end

val l1 = ref TRUTH
val l2 = ref TRUTH
val l3 = ref T;

local
   fun VALUE_RULE c = CONV_RULE (RAND_CONV (RAND_CONV c))
   val PAIR_RULE =
      CONV_RULE ((RATOR_CONV o RAND_CONV) (PURE_REWRITE_CONV [pairTheory.PAIR]))
   fun ii lhs rhs =
      let
         val (x, y) = pairSyntax.dest_pair rhs
         val x1 = pairSyntax.mk_fst lhs
         val y1 = pairSyntax.mk_snd lhs
      in
         (x |-> x1) :: ii y1 y
      end
      handle HOL_ERR _ => [rhs |-> lhs]
in
   fun compose th1 th2 =
      let
         val th3 = MATCH_MP (MATCH_MP TRIPLE_COMPOSE_ALT th2) th1
      in
         case Thm.hyp th3 of
            [] => th3
          | tm :: _ =>
              let
                 val lemma = SYM (ASSUME tm)
                 val (lhs, rhs) = dest_eq tm
                 val th4 = VALUE_RULE
                              (PairRules.UNPBETA_CONV rhs
                               THENC REWR_CONV (SYM (SPEC_ALL LET_THM))
                               THENC RAND_CONV (fn _ => lemma)) th3
              in
                 MP (PAIR_RULE (INST (ii lhs rhs) (DISCH_ALL th4))) (REFL lhs)
              end
      end
      handle HOL_ERR e => (l1 := th1; l2 := th2; raise HOL_ERR e)
end

(*
val th1 = !l1
val th2 = !l2
val tm = !l3
*)

local
   val rule1 =
      REWRITE_RULE [markerTheory.Abbrev_def, addressTheory.CONTAINER_def]
   val rule2 = CONV_RULE ((RAND_CONV o RAND_CONV) (SIMP_CONV bool_ss []))
in
   fun merge tm th1 th2 =
      let
         val th1 = DISCH tm (rule1 th1)
         val th2 = DISCH (mk_neg tm) (rule1 th2)
      in
         rule2 (MATCH_MP COND_MERGE (CONJ th1 th2))
      end
      handle HOL_ERR e => (l1 := th1; l2 := th2; l3 := tm; raise HOL_ERR e)
end

(*
  fun fan (End i) = 1
    | fan (Repeat i) = 1
    | fan (Cons (th,t)) = fan t
    | fan (Merge (tm,t1,t2)) = fan t1 + fan t2
    | fan (ConsMerge (tm,th1,th2,t)) = fan t + fan t

  fan t
*)

val case_sum_conv =
   SIMP_CONV (std_ss++simpLib.rewrites [tripleTheory.case_sum_def]) []
val case_sum_rule = Conv.CONV_RULE (Conv.RATOR_CONV case_sum_conv)
val beta_fst_rule =
   CONV_RULE ((RATOR_CONV o RAND_CONV)
                (DEPTH_CONV PairedLambda.GEN_BETA_CONV
                 THENC REWRITE_CONV [pairTheory.FST])
              THENC REWRITE_CONV [boolTheory.IMP_CLAUSES])
val forall_prod_ss = pure_ss++simpLib.rewrites [pairTheory.FORALL_PROD]

fun round (input, get_assert, triple_refl) =
   fn name => fn (b, e) => fn thms =>
   let
      val () = inPlaceEcho (name ^ ": ")
      val () = echo 1 "."
      val t = build_compose_tree (b, e) thms
      val loop = is_rec t
      val pre = get_assert (hd b)
      val post = get_assert (hd e)
      val (enter_th, exit_th) =
         if loop
            then let
                    fun refl_sum f =
                       triple_refl
                          (tripleSyntax.mk_case_sum
                             (pre, post, f (input, Term.type_of input)))
                 in
                    (refl_sum sumSyntax.mk_inl, refl_sum sumSyntax.mk_inr)
                 end
         else (boolTheory.TRUTH, triple_refl (Term.mk_comb (post, input)))
      (* perform composition *)
      val () = echo 1 "."
      fun comp (End i) = exit_th
        | comp (Repeat i) = enter_th
        | comp (Cons (th, t)) = compose th (comp t)
        | comp (Merge (tm, t1, t2)) = merge tm (comp t1) (comp t2)
        | comp (ConsMerge (tm, th1, th2, t)) =
            let
               val res = comp t
            in
               merge tm (compose th1 res) (compose th2 res)
            end
      val th =
         CONV_RULE ((RAND_CONV o RAND_CONV) (PairRules.UNPBETA_CONV input))
            (comp t)
      val th =
         if loop
            then let
                    val () = echo 1 "."
                    (* apply loop rule *)
                    val lemma = case_sum_conv (mk_comb (pre, input))
                    val th = CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                                           (fn _ => GSYM lemma)) th
                    val x = Term.mk_var ("x", Term.type_of input)
                    val tm = mk_forall (x, subst [input |-> x] (Thm.concl th))
                    val lemma =
                       prove
                         (tm,
                          FULL_SIMP_TAC forall_prod_ss []
                          THEN REPEAT STRIP_TAC
                          THEN MATCH_MP_TAC (DISCH T th)
                          THEN FULL_SIMP_TAC std_ss [])
                    val th =
                       MATCH_MP SHORT_TERM_TAILREC lemma
                       |> beta_fst_rule
                       |> SPEC input
                       |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                                         PairRules.PBETA_CONV)
                 in
                    th
                 end
         else th
      val () = echo 1 "."
      val ff = th |> concl |> rand |> rand |> rator
      val def =
         new_definition (name ^ "_def", mk_eq (mk_var (name, type_of ff), ff))
      val th = th |> CONV_RULE
                       ((RAND_CONV o RAND_CONV o RATOR_CONV) (fn _ => GSYM def))
      (* clean up result *)
      val lemma = mk_eq(mk_comb (boolSyntax.lhs (concl def), input),
                        (!swap_primes) input)
                  |> ASSUME
      val result =
         th |> CONV_RULE ((RAND_CONV o RAND_CONV) (fn _ => lemma)
                          THENC RAND_CONV PairRules.PBETA_CONV)
            |> DISCH_ALL
      val () = echo 1 "."
   in
      (def, result)
   end

fun core_decompile name qcode =
   let
      val (thms, loops) = time (stage_12 name) qcode
      val (_, ((th, _, _), _)) = Lib.first (fn (x, _) => x = 0) thms
      val (model, pre, code, _) = tripleSyntax.dest_triple (Thm.concl th)
      val (cnd, asrt) = pairSyntax.dest_pair pre
      val affected_vars = asrt |> Term.free_vars |> filter (fn v => v <> !pc)
      val inp = pairSyntax.list_mk_pair (cnd :: affected_vars)
      fun get_assert i = pairSyntax.mk_pabs (inp, Term.subst (add_to_pc i) pre)
      val refl = Thm.SPEC code (Drule.ISPEC model tripleTheory.TRIPLE_REFL)
      fun triple_refl t = case_sum_rule (Thm.SPEC t refl)
      val round = round (inp, get_assert, triple_refl)
      fun rounds loops thms defs =
         let
            val (b, e) = hd loops
            val loops = tl loops
            val n = length loops
            val part_name = if n = 0 then name
                            else name ^ "_part" ^ (int_to_string n)
            val (def, result) = round part_name (b, e) thms
            val thms =
               (hd b, ((UNDISCH_ALL result, 0, SOME (hd e)), NONE)) :: thms
         in
            if n = 0
               then (result, rev (def :: defs))
            else rounds loops thms (def :: defs)
         end
      val () = echo 1 "\nProcessing...\n\n"
      val (res, defs) =
         time (fn () => rounds loops thms [] before inPlaceEcho "Finished.\n\n")
              ()
      val () = add_decomp name res (loops |> last |> snd |> hd)
   in
      (res, LIST_CONJ defs)
   end

end
