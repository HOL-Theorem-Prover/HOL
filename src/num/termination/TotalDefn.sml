(*---------------------------------------------------------------------------
       Proving that definitions terminate.
 ---------------------------------------------------------------------------*)

structure TotalDefn :> TotalDefn =
struct

open HolKernel Parse boolLib pairLib basicSize DefnBase numSyntax
     relationTheory combinTheory prim_recTheory arithmeticTheory
     basicSizeTheory pairTheory

open simpLib infix ++;

local open numSimps in end

structure Parse = struct
  open Parse
  val SOME arithmetic_grammars = grammarDB {thyname="arithmetic"}
  val (Type,Term) = parse_from_grammars arithmetic_grammars
end

open Parse

(*---------------------------------------------------------------------------*)
(* Set up standard errors, warnings, etc                                     *)
(*---------------------------------------------------------------------------*)

val ERR    = mk_HOL_ERR "TotalDefn";
val ERRloc = mk_HOL_ERRloc "TotalDefn";
val WARN   = HOL_WARNING "TotalDefn";

(*---------------------------------------------------------------------------*)
(* Set up traces                                                             *)
(*---------------------------------------------------------------------------*)

val {get = monitoring, flag = termination_candidates, ...} =
    HOLFlags.create_trace ({group = "Definition",
                            name = "termination_candidates"},
                           {initial = 0, max = 4})
local
in
fun lztrace(i,title,msgf) =
  if i <= monitoring() then
     Lib.say $ String.concat ["\n", title, msgf()]
  else ()
end

val {get = get_allow_schema_definition, flag = allow_schema_definition, ...} =
    HOLFlags.create_btrace ({group = "Definition",
                             name = "allow_schema_definition"}, false)

val {get = get_auto_tgoal, flag = auto_tgoal, ...} =
    HOLFlags.create_btrace ({group = "Definition",
                             name = "auto_tgoal"}, true)

val {get = deleting_support, flag = delete_support_defs, ...} =
    HOLFlags.create_btrace ({group = "Definition",
                             name = "delete_support_defs"}, true)

fun delete_support defn s2 s1 =
   if deleting_support() then
      DefnBase.delete_support defn s2 s1
   else ()

(*---------------------------------------------------------------------------*)
(* Misc. stuff that should be in Lib probably                                *)
(*---------------------------------------------------------------------------*)

fun max [] m = m
  | max (h::t) m = max t (if h>m then h else m);

fun take 0 L = []
  | take n (h::t) = h::take (n-1) t
  | take n [] = raise ERR "take" "not enough elements";

fun copies x =
  let fun repl 0 = []
        | repl n = x::repl (n-1)
  in repl
  end;

fun trylist f [] = raise ERR "trylist" "all attempts failed"
  | trylist f (h::t) = (h, f h) handle HOL_ERR _ => trylist f t

fun index_of P =
 let fun index i [] = raise ERR "index_of" "not found"
       | index i (h::t) = if P(h) then i else index (i+1) t
 in index 0
 end

(*---------------------------------------------------------------------------*)
(* perms delivers all permutations of a list. By Peter Sestoft.              *)
(* Pinched from MoscowML distribution (examples/small/perms.sml).            *)
(*---------------------------------------------------------------------------*)

local
    fun accuperms []      tail res = tail :: res
      | accuperms (x::xr) tail res = cycle [] x xr tail res
    and cycle left mid [] tail res = accuperms left (mid::tail) res
      | cycle left mid (right as r::rr) tail res =
        cycle (mid::left) r rr tail (accuperms (left @ right) (mid::tail) res)
in
  fun perms xs = accuperms xs [] []
  fun permsn n = perms (List.tabulate(n, fn x => x+1))
end;

(*---------------------------------------------------------------------------*)
(* Remove duplicates in a set of terms, while keeping original order         *)
(*---------------------------------------------------------------------------*)

fun rm x [] = []
  | rm x (h::t) = if aconv x h then rm x t else h::rm x t;

fun mk_term_set [] = []
  | mk_term_set (h::t) = h::mk_term_set (rm h t);

fun imk_var(i,ty) = mk_var("v"^Int.toString i,ty);

(*---------------------------------------------------------------------------*)
(* Basic syntax for WF relations                                             *)
(*---------------------------------------------------------------------------*)

val inv_image_tm = prim_mk_const{Thy="relation",Name="inv_image"};

fun mk_inv_image(R,f) =
  let val ty1 = fst(dom_rng(type_of R))
      val ty2 = fst(dom_rng(type_of f))
  in
    list_mk_comb(inst[beta |-> ty1, alpha |-> ty2] inv_image_tm,[R,f])
  end;

val WF_tm = prim_mk_const{Name = "WF", Thy="relation"};

val isWFR = same_const WF_tm o fst o strip_comb;

fun get_WF tmlist =
   pluck isWFR tmlist
    handle HOL_ERR _ => raise ERR "get_WF" "unexpected termination condition";

fun K0 ty = mk_abs(mk_var("v",ty), numSyntax.zero_tm);

(*---------------------------------------------------------------------------*)
(* Takes [v1,...,vn] [i_j,...,i_m], where  1 <= i_j <= i_m <= n and returns  *)
(*                                                                           *)
(*    inv_image ($< LEX ... LEX $<)                                          *)
(*              (\(v1:ty1,...,vn:tyn).                                       *)
(*                  (size_of(tyi)(vi), ..., size_of(tym)(vm)))               *)
(*---------------------------------------------------------------------------*)

fun list_mk_lex []  = raise ERR "list_mk_lex" "empty list"
  | list_mk_lex [x] = x
  | list_mk_lex L   = end_itlist (curry pairSyntax.mk_lex) L;

val nless_lex = list_mk_lex o copies numSyntax.less_tm;

fun mk_lex_reln argvars sizedlist arrangement =
  let val lex_comb = nless_lex (length sizedlist)
      val pargvars = list_mk_pair argvars
  in
     mk_inv_image (lex_comb, mk_pabs(pargvars,list_mk_pair arrangement))
  end;


(*---------------------------------------------------------------------------*)
(* proper_subterm t1 t2 iff t1 is a proper subterm of t2. A record projn     *)
(* x.fld is a proper subterm of x.                                           *)
(*---------------------------------------------------------------------------*)

fun is_recd_proj tm1 tm2 =
  let val (proj,a) = dest_comb tm1
      val aty = type_of a
      val projlist = mapfilter
         (fst o dest_comb o boolSyntax.lhs o snd o strip_forall o concl)
         (TypeBase.accessors_of aty)
  in TypeBase.is_record_type aty andalso op_mem aconv proj projlist
  end
  handle HOL_ERR _ => false;

fun proper_subterm tm1 tm2 =
   not(aconv tm1 tm2)
   andalso (Lib.can (find_term (aconv tm1)) tm2
            orelse
            is_recd_proj tm1 tm2);


(*---------------------------------------------------------------------------*)
(* termination_simps is an adjustable set of rewrites for doing termination  *)
(* proofs. It is created by the call to "create_simple_dictionary"           *)
(*---------------------------------------------------------------------------*)

val initial_termination_simps =
  [("DIV_LT_X", DIV_LT_X),
   ("X_LT_DIV", X_LT_DIV),
   ("SUB_LESS", SUB_LESS),
   ("DIV_LESS", DIV_LESS),
   ("MOD_LESS", MOD_LESS)]

val {exclude = exclude_termsimp, temp_exclude = temp_exclude_termsimp,
     export = export_termsimp,   temp_export = temp_export_termsimp,
     getDB = termination_simpdb, temp_setDB = termination_tempsetDB,
     get_thms = termination_simps, ...} =
    ThmSetData.export_simple_dictionary {settype = "tfl_termsimp",
                                         initial = initial_termination_simps}
val _ =
    List.app temp_export_termsimp
        ["combin.o_DEF", "combin.I_THM",
         "prim_rec.measure_def", "relation.inv_image_def",
         "basicSize.sum_size_def", "basicSize.min_pair_size_def",
         "pair.LEX_DEF", "pair.RPROD_DEF",
         "arithmetic.DIV2_def"]

fun with_termsimps ths =
    ThmSetData.sdict_withflag_thms
      ({getDB = termination_simpdb, temp_setDB = termination_tempsetDB}, ths)

(*---------------------------------------------------------------------------*)
(* Adjustable set of WF theorems for doing WF proofs.                        *)
(*---------------------------------------------------------------------------*)

val {getDB = WF_thms, export = export_WF_thm, ...} =
    ThmSetData.export_list {
      settype = "tfl_WF",
      initial = let
        open relationTheory prim_recTheory pairTheory
      in
        [WF_inv_image, WF_measure, WF_LESS,
         WF_EMPTY_REL, WF_PRED, WF_RPROD, WF_LEX, WF_TC]
      end
    }

(*---------------------------------------------------------------------------*)
(* Basic simplification set. We perform any (paired) beta-reductions, eg.    *)
(* expand "(\(x,y). M x y) N" to "M (FST N) (SND N)", and apply common       *)
(* arithmetic simplification.                                                *)
(*---------------------------------------------------------------------------*)

val base_ss =
 boolSimps.bool_ss
    ++ pairSimps.PAIR_ss
    ++ pairSimps.paired_forall_ss
    ++ pairSimps.paired_exists_ss
    ++ pairSimps.gen_beta_ss
    ++ rewrites [pairTheory.FORALL_PROD]
    ++ numSimps.REDUCE_ss
    ++ numSimps.ARITH_RWTS_ss;

(*---------------------------------------------------------------------------*)
(* Destruct R (x1,...,xn) (y1,...ym) into [(x1,y1), ... , (xn,yn)],          *)
(* where n and m need not be equal.                                          *)
(*---------------------------------------------------------------------------*)

fun pair_up [] _  = raise ERR "pair_up" "empty arg."
  | pair_up _ []  = raise ERR "pair_up" "empty arg."
  | pair_up [x] Y = [(x,pairSyntax.list_mk_pair Y)]
  | pair_up X [y] = [(pairSyntax.list_mk_pair X, y)]
  | pair_up (x::rst) (y::rst1) = (x,y)::pair_up rst rst1;

(*---------------------------------------------------------------------------*)
(* The two values a termination condition compares: the argument of the      *)
(* recursive call, and the argument the call was made from.                  *)
(*---------------------------------------------------------------------------*)

fun dest_tc tm =
  let val Ryx = (snd o strip_imp o snd o strip_forall) tm
      val (Ry, x) = dest_comb Ryx
  in
     (rand Ry, x)
  end;

fun dest tm =
  let val (y,x) = dest_tc tm
      open pairSyntax
  in
     pair_up (spine_pair y) (spine_pair x)
  end;

(*---------------------------------------------------------------------------*)
(* Is a list-of-lists rectangular, filling in with false on short rows       *)
(*---------------------------------------------------------------------------*)

fun fill n [] = copies false n
  | fill n (h::t) = h::fill (n-1) t;

fun rectangular L =
 let val lens = map length L
 in case Lib.mk_set lens
     of []  => raise ERR "rectangular" "impossible"
      | [x] => L
      |  _  => map (fill (max lens 0)) L
 end;

(*---------------------------------------------------------------------------*)
(* For each column, return true if every element is true.                    *)
(*---------------------------------------------------------------------------*)

fun apply_pred_to_cols P L =
 if all null L then []
 else P (map (Lib.trye hd) L)::apply_pred_to_cols P (map (Lib.trye tl) L);

(*---------------------------------------------------------------------------*)
(* For each column, return true if every element is true.                    *)
(* For each column, if any entry in the column is true, then return true.    *)
(*---------------------------------------------------------------------------*)

val all_true_in_cols = apply_pred_to_cols (all I);
val some_true_in_cols = apply_pred_to_cols (exists I);

(*---------------------------------------------------------------------------*)
(* After first true in a list, turn everything false.                        *)
(*---------------------------------------------------------------------------*)

fun fix [] = []
  | fix (true::t)  = true::map (K false) t
  | fix (false::t) = false::fix t;

(*---------------------------------------------------------------------------*)
(* Make L0 rectangular then try to find and mark first column where          *)
(* predicate holds. If there is such, mark all later cols false. Otherwise,  *)
(* collect all columns where predicate holds at least once.                  *)
(*---------------------------------------------------------------------------*)

fun projects L0 =
  let val L = rectangular L0
      val col_trues = all_true_in_cols L
  in
    if exists I col_trues then fix col_trues else some_true_in_cols L
  end;

(*---------------------------------------------------------------------------*)
(* Collect all columns where some change happens.                            *)
(*---------------------------------------------------------------------------*)

fun column_summaries L = some_true_in_cols (rectangular L);

(*---------------------------------------------------------------------------*)
(* Identify columns where P holds                                            *)
(*---------------------------------------------------------------------------*)

fun nth P [] _ N = rev N
  | nth P (h::t) n N = nth P t (n+1) (if P h then n::N else N);

(*---------------------------------------------------------------------------*)
(* Take apart a product type with respect to a list of terms                 *)
(*---------------------------------------------------------------------------*)

fun strip_prod_ty [] _ = raise ERR "strip_prod_ty" ""
  | strip_prod_ty [x] ty = [(x,ty)]
  | strip_prod_ty (h::t) ty =
     let val (x,y) = with_exn pairSyntax.dest_prod ty
                          (ERR "strip_prod_ty" "expected a product type")
     in  (h,x)::strip_prod_ty t y
     end

fun list_mk_prod_tyl L =
 let val (front,(b,last)) = front_last L
     val tysize = TypeBasePure.type_size (TypeBase.theTypeBase())
     val last' = (if b then tysize else K0) last
                 handle e => raise wrap_exn "TotalDefn" "last'" e
  in
  itlist (fn (b,ty1) => fn M =>
     let val x = mk_var("x",ty1)
         val y = mk_var("y",fst(dom_rng (type_of M)))
         val blagga = (if b then tysize else K0) ty1
     in
       mk_pabs(mk_pair(x,y),
               numSyntax.mk_plus(mk_comb(blagga,x),mk_comb(M,y)))
     end) front last'
 end
 handle e => raise wrap_exn "TotalDefn" "list_mk_prod" e;

(*---------------------------------------------------------------------------*)
(* Construct all lex combos corresponding to permutations of list            *)
(*---------------------------------------------------------------------------*)

fun mk_sized_subsets argvars sizedlist =
 let val permutations =
         if length sizedlist > 4
         then (WARN "mk_sized_subsets"
                 "too many permutations (more than 24): chopping some";
               perms (take 4 sizedlist))
         else perms sizedlist
 in
  map (mk_lex_reln argvars sizedlist) permutations
  handle HOL_ERR _ => []
 end;

(*---------------------------------------------------------------------------*)
(* Simplify guessed relations                                                *)
(*---------------------------------------------------------------------------*)

val simplifyR =
 let open prim_recTheory basicSizeTheory reduceLib simpLib
     val expand = QCONV (SIMP_CONV base_ss
                    [measure_def,pair_size_def,bool_size_def,one_size_def])
 in
  rhs o concl o expand
 end;

(*---------------------------------------------------------------------------*)
(* Build a type size, not counting outer sum or pair constructors,           *)
(* which are likely to be created by mutual recursion.                       *)
(*---------------------------------------------------------------------------*)

fun flat_type_size ty =
  let open basicSizeSyntax in
  case (total sumSyntax.dest_sum ty, total pairSyntax.dest_prod ty)
   of (SOME (lty, rty), _) =>
         mk_sum_size2(flat_type_size lty,flat_type_size rty)
    | (NONE, SOME (lty, rty)) =>
         mk_min_pair_size2(flat_type_size lty,flat_type_size rty)
    | _ => TypeBasePure.type_size (TypeBase.theTypeBase()) ty end

(*---------------------------------------------------------------------------*)
(* A mutual recursion's domain is a sum, with one leaf per function.  Give   *)
(* each leaf a measure of its own and add them up, without counting the sum  *)
(* constructors that brought the functions into one domain: those say which  *)
(* function a call is to, not how big its argument is.                       *)
(*                                                                           *)
(* A leaf is measured the way a flat domain is -- a column that never        *)
(* shrinks weighs nothing -- so an argument a function merely carries, an    *)
(* accumulator say, need not shrink for the call to.  A leaf's columns are   *)
(* read off the conditions with both sides at that leaf, and failing those,  *)
(* off the conditions that reach it from another leaf.                       *)
(*---------------------------------------------------------------------------*)

fun sum_leaves ty =
  case total sumSyntax.dest_sum ty
   of NONE => [ty]
    | SOME (lty,rty) => sum_leaves lty @ sum_leaves rty;

(*---------------------------------------------------------------------------*)
(* The leaf a value was injected at, and the value injected.                 *)
(*---------------------------------------------------------------------------*)

fun leaf_of ty tm =
  case total sumSyntax.dest_sum ty
   of NONE => (0,tm)
    | SOME (lty,rty) =>
      case total sumSyntax.dest_inl tm
       of SOME (t,_) => leaf_of lty t
        | NONE =>
          case total sumSyntax.dest_inr tm
           of SOME (t,_) =>
                let val (i,u) = leaf_of rty t
                in (length (sum_leaves lty) + i, u)
                end
            | NONE => raise ERR "leaf_of" "not an injection";

fun leaf_measures domty tcs =
 let val tysize = TypeBasePure.type_size (TypeBase.theTypeBase())
     val sided = mapfilter (fn tc =>
            let val (y,x) = dest_tc tc
            in (leaf_of domty x, leaf_of domty y)
            end) tcs
     fun rows i =
       List.mapPartial
         (fn ((ix,px),(iy,py)) =>
             if ix = i andalso iy = i then
               total (pair_up (pairSyntax.spine_pair py))
                     (pairSyntax.spine_pair px)
             else NONE)
         sided
     (* A leaf no condition compares with itself is still reached from
        the others.  A column a call descended into is a proper subterm
        of a column of the argument the call was made from; which column
        that was does not matter, and need not even exist, because the
        leaves need not take their parameters the same way. *)
     fun reached i =
       List.mapPartial
         (fn ((ix,px),(iy,py)) =>
             if iy = i andalso ix <> i then
               let val src = pairSyntax.spine_pair px
               in SOME (map (fn c => List.exists (proper_subterm c) src)
                            (pairSyntax.spine_pair py))
               end
             else NONE)
         sided
     fun from_rows [] = NONE
       | from_rows rws =
           let val chf = projects rws
           in if exists I chf then SOME chf else NONE
           end
     fun mask i = from_rows (map (map (uncurry proper_subterm)) (rows i))
     val leaves = sum_leaves domty
     val indices = Lib.upto 0 (length leaves - 1)
     val masks = map mask indices
     val reaching = map (from_rows o reached) indices
     val known = List.mapPartial I masks
     fun sized chf ty = list_mk_prod_tyl (strip_prod_ty chf ty)
     fun By chf ty = (sized chf ty handle HOL_ERR _ => tysize ty)
     fun whole _ ty = tysize ty
     fun own i ty =
       case List.nth(masks,i)
        of SOME chf => By chf ty
         | NONE => tysize ty
     fun reach i ty =
       case List.nth(masks,i)
        of SOME chf => By chf ty
         | NONE =>
           case List.nth(reaching,i)
            of SOME chf => By chf ty
             | NONE => tysize ty
     (* a leaf no condition compares with itself still shares the other
        functions' parameters, so borrow a mask that fits it *)
     fun shared i ty =
       case List.nth(masks,i)
        of SOME _ => own i ty
         | NONE =>
           case List.find (fn chf => Lib.can (sized chf) ty) known
            of SOME chf => sized chf ty
             | NONE => tysize ty
     fun build leafm ty i =
       case total sumSyntax.dest_sum ty
        of NONE => (leafm i ty, i+1)
         | SOME (lty,rty) =>
             let val (ml,i1) = build leafm lty i
                 val (mr,i2) = build leafm rty i1
             in (basicSizeSyntax.mk_sum_size2(ml,mr), i2)
             end
 in
   if Lib.can sumSyntax.dest_sum domty
   then mapfilter (fn lm => fst (build lm domty 0)) [reach, own, shared, whole]
   else []
 end
 handle HOL_ERR _ => [];

(*---------------------------------------------------------------------------*)
(* Among the termination_simps() are theorems of the form                    *)
(*                                                                           *)
(*   constraints ==> f t1 < f t2                                             *)
(*                                                                           *)
(* which are used to finalize termination proofs. These are also used to     *)
(* determine if an argument position should be included in the synthesized   *)
(* termination relation. An example is                                       *)
(*                                                                           *)
(*  ⊢ ∀m. m ≠ 0w ⇒ w2n (m − 1w) < w2n m                                      *)
(*                                                                           *)
(* When the type of t1 and t2 are :num, there need be no "measure function"  *)
(* f present. The following theorem is an example.                           *)
(*                                                                           *)
(*  ⊢ ∀m n. 0 < n ⇒ m MOD n < n                                              *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun is_relevant tsimps = let
  fun rec_call_pat th = let
      fun dest_order x = dest_less x handle HOL_ERR _ => dest_leq x
      fun is_measureFn_app (l,r) =
          aconv (rator l) (rator r) handle HOL_ERR _ => false
      val (l,r) = concl th |> strip_forall |> snd |>
                  strip_imp |> snd |> dest_order
  in if is_measureFn_app (l,r) then
        rand l else
     if is_var r then
        l
     else raise ERR "is_relevant" ""
  end
  val pats = mapfilter rec_call_pat tsimps
 in
   fn (tm,_:term) => 0 < length (mapfilter (C match_term tm) pats)
 end;

(*---------------------------------------------------------------------------*)
(* "guessR" guesses a list of termination measures. Quite ad hoc.            *)
(* First guess covers recursions on proper subterms, e.g. prim. recs. Next   *)
(* guess measure sum of sizes of all arguments. Next guess generates         *)
(* lex-combos for Ackermann-style iterated prim. rec. defs. Finally,         *)
(* generate all lex combinations of arguments that get changed by known      *)
(* functions, i.e., ones that have corresponding theorems in ref variable    *)
(* "termination_simps".                                                      *)
(* Finally, all generated termination relations are simplified and           *)
(* duplicates are weeded out.                                                *)
(*---------------------------------------------------------------------------*)

fun report_num_tcs n =
    lztrace(1,"Termination conditions: ",
            fn () => Int.toString n)
fun report_num_guesses n =
    lztrace(1,"Candidate termination relations generated: ",
            fn () => Int.toString n)

fun guessR defn =
 let open Defn numSyntax simpLib boolSimps
   fun tysize ty = TypeBasePure.type_size (TypeBase.theTypeBase()) ty
   fun size_app v = mk_comb(tysize (type_of v),v)
   val relevant = is_relevant (termination_simps())
 in
 if null (tcs_of defn) then []
  else
  case reln_of defn
   of NONE => []
    | SOME R =>
       let val domty = fst(dom_rng(type_of R))
           val (_,tcs0) = Lib.pluck isWFR (tcs_of defn)
           val tcs = map (rhs o concl o QCONV (SIMP_CONV bool_ss [])) tcs0
           val tcs = filter (not o aconv T) tcs
           val () = report_num_tcs (length tcs)
           val matrix  = map dest tcs
           val check1  = map (map (uncurry proper_subterm)) matrix
           val chf1    = projects check1
           val domtyl_1 = strip_prod_ty chf1 domty
           val domty0  = list_mk_prod_tyl domtyl_1
           (* deal with possible iterated prim_rec *)
           val indices_1 = Lib.upto 1 (length domtyl_1)
           val (argvars_1,subset_1) =
             itlist2 (fn i => fn (b,ty) => fn (alist,slist) =>
                        let val v = imk_var(i,ty)
                        in (v::alist, if b then size_app v::slist else slist)
                        end) indices_1 domtyl_1 ([],[])
           val it_prim_rec = [mk_lex_reln argvars_1 subset_1 subset_1]
                              handle HOL_ERR _ => []
           (* deal with other lex. combos *)
           val check2 = map (map relevant) matrix
           val chf2   = column_summaries check2
           val domtyl_2 = strip_prod_ty chf2 domty
           val indices = Lib.upto 1 (length domtyl_2)
           val (argvars,subset) =
             itlist2 (fn i => fn (b,ty) => fn (alist,slist) =>
                        let val v = imk_var(i,ty)
                        in (v::alist, if b then size_app v::slist else slist)
                        end) indices domtyl_2 ([],[])
           val lex_combs = mk_sized_subsets argvars subset
           val allrels = [mk_cmeasure domty0, mk_cmeasure (tysize domty),
                          mk_cmeasure (flat_type_size domty)]
                         @ map mk_cmeasure (leaf_measures domty tcs)
                         @ it_prim_rec @ lex_combs
           val allrels' = mk_term_set (map simplifyR allrels)
           val () = report_num_guesses(length allrels')
       in
         allrels'
       end
 end
 handle e => raise wrap_exn "TotalDefn" "guessR" e;

(*---------------------------------------------------------------------------*)
(* Wellfoundedness and termination provers (parameterized by theorems).      *)
(* The default TC simplifier and prover is terribly terribly naive, but      *)
(* still useful. It knows all about the sizes of types.                      *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Wellfoundedness prover for combinations of wellfounded relations.         *)
(*---------------------------------------------------------------------------*)

fun BC_TAC th =
  if is_imp (#2 (strip_forall (concl th)))
  then MATCH_ACCEPT_TAC th ORELSE MATCH_MP_TAC th
    else MATCH_ACCEPT_TAC th;

fun PRIM_WF_TAC thl = REPEAT (MAP_FIRST BC_TAC thl ORELSE CONJ_TAC);
fun WF_TAC g = PRIM_WF_TAC (WF_thms()) g;

(*--------------------------------------------------------------------------*)
(* Basic simplification and proof for remaining termination conditions.     *)
(*--------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Convert a tactic to a conv                                                *)
(*---------------------------------------------------------------------------*)

fun TAC_CONV tac tm = TAC_PROOF (([],tm),REWRITE_TAC [] THEN tac) |> EQT_INTRO

val solve_conjs = EVERY_CONJ_CONV o TRY_CONV o TAC_CONV

fun ACHIEVES_CONV P cnv t =
  let val th = cnv t
  in if P (dest_eq (concl th)) then th else NO_CONV t
  end

val SOLVES_CONV = ACHIEVES_CONV (aconv boolSyntax.T o snd)

fun SOLVES tac g ctxt =
  let val result as (subgoals, vfn) = tac g ctxt
  in if null subgoals then result else NO_TAC g ctxt
  end

(*---------------------------------------------------------------------------*)
(* There are two entrypoints to termination proofs. One---TC_SIMP_TAC---is  *)
(* intended to be an automatic prover acting as a backend to prove one of a  *)
(* set of generated guesses. Thus it needs to be reasonably fast and yet     *)
(* still go "as deep as possible" in order to prove a guess if it is true.   *)
(* So it's an "all or nothing" tactic.                                       *)
(*                                                                           *)
(* The other entrypoint---WF_REL_TAC---takes a user-supplied relation "R"    *)
(* and does one of two things: it either proves the termination conditions   *)
(* completely or, if unable to do that, leaves an understandable termination *)
(* goal. By this we mean that the goal hasn't been so transformed that it is *)
(* hard to see the connection with the original recursive equations.         *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Extra rewrites, used only if they would solve a termination conjunct.     *)
(*---------------------------------------------------------------------------*)

val {getDB = termination_solve_simps, export = export_termsolve_simp, ...} =
    ThmSetData.export_list {settype = "tfl_termsolve", initial = []}

(*---------------------------------------------------------------------------*)
(* Create TC simplifiers and provers. WF(-) formulas not handled             *)
(*---------------------------------------------------------------------------*)

fun termination_ss() =
  let open boolTheory
      fun get_orig (TypeBasePure.ORIG th) = th
        | get_orig _ = raise ERR "get_orig" "not the original"
      val term_simps = [PULL_EXISTS] @ termination_simps()
      val elts = TypeBase.elts()
      val size_defs =
          mapfilter (get_orig o #2 o valOf o TypeBasePure.size_of0) elts
      val case_defs = mapfilter TypeBasePure.case_def_of elts
  in
   base_ss ++ rewrites term_simps
           ++ rewrites size_defs
           ++ rewrites case_defs
           ++ numSimps.ARITH_DP_ss  (* important that this is last! *)
  end

(* simplify then case split and simplify from asms *)
fun TC_SIMP_TAC ss thl =
    let val ss' = ss ++ rewrites (termination_solve_simps() @ thl)
    in
      CONV_TAC (simpLib.SIMP_CONV ss' []) THEN
      BasicProvers.PRIM_STP_TAC ss' NO_TAC
    end

(*---------------------------------------------------------------------------*)
(* Instantiate the termination relation with q, then try to prove            *)
(* wellfoundedness, then simplify and try to prove the TCs. Any remaining    *)
(* unproved TCs should be in reduced form.                                   *)
(*---------------------------------------------------------------------------*)

fun TERM_TAC tctac = CONJ_TAC THENL [WF_TAC,tctac]

fun WF_REL_TAC q =
  let val ss = termination_ss()
      val simplifier = simpLib.SIMP_CONV ss []
      val prover = SOLVES (TC_SIMP_TAC ss [])
      val conjunct_conv = TAC_CONV(prover) ORELSEC simplifier
  in
    Q.EXISTS_TAC q THEN
    TERM_TAC (CONV_TAC (EVERY_CONJ_CONV conjunct_conv))
  end

fun mk_term_tac() =
    let val ss = termination_ss() ++ boolSimps.ETA_ss
    in TERM_TAC (SOLVES (TC_SIMP_TAC ss [])) end

(*---------------------------------------------------------------------------
       Definition principles that automatically attempt
       to prove termination. If the termination proof
       fails, the definition attempt fails.
 ---------------------------------------------------------------------------*)

fun reln_is_not_set defn =
  case Defn.reln_of defn
   of NONE => false
    | SOME R => is_var R;

fun proveTotal tac defn =
  let val (WFR,rest) = get_WF (Defn.tcs_of defn)
      val form = list_mk_conj(WFR::rest)
      val thm = Tactical.default_prover(form,tac)
  in
    (Defn.elim_tcs defn (CONJUNCTS thm), SOME thm)
  end;

fun complain_about_rhsfvs srcfn V =
  raise ERR srcfn
      (String.concat
       ["The following variables are free in the \n",
        "right hand side of the proposed definition: ",
        String.concatWith "," $ map (Lib.quote o #1 o dest_var) V])

local open Defn
  fun should_try_to_prove_termination defn rhs_frees =
      let val tcs = tcs_of defn
      in not(null tcs) andalso
         null (op_intersect aconv (free_varsl tcs) rhs_frees)
      end
  fun fvs_on_rhs V =
      if get_allow_schema_definition() then ()
      else complain_about_rhsfvs "defnDefine" V

  fun msg1 defName thm_src_loc =
    let open DB_dtype
        val locstring =
          case thm_src_loc of
            Unknown => "unknown location"
          | Located {scriptpath,linenum,exact} =>
            String.concat
              [String.toString scriptpath, ":",
               Int.toString linenum,
               if not exact then " (approx)" else ""]
     in String.concat
        ["\nUnable to automatically prove termination for\n\n  ",
         defName, " at\n  ", locstring, "\n"]
     end

  fun msg2 defName goalstring = String.concat
    ["\nThe termination goal for ", defName,"\n\n  ",
     goalstring, "\n\n",
     "has been created in the proof manager. Solve the goal\n",
     "(try e.g. p(), WF_REL_TAC) and add the tactic to the\n",
     "Termination block for the Definition, i.e.\n\n",
     "  Definition ", defName, ":\n",
     "    <eqns>\n",
     "  Termination\n",
     "    <tactic>\n",
     "  End\n\n"]

  fun termination_proof_failed loc defn =
     let val defName = Defn.name_of defn
         val _ = Defn.tgoal defn
         val goalstring =  (* grab this in any case *)
             PP.pp_to_string (!Globals.linewidth)
                 proofManagerLib.std_goal_pp (proofManagerLib.top_goal())
         val _ = if not (get_auto_tgoal()) then
                    ignore $ proofManagerLib.drop ()
                 else ()
     in
       if not (!Globals.interactive) then
          raise ERR "defnDefine" (msg1 defName loc ^ "\n" ^ goalstring ^ "\n")
       else
          raise ERR "defnDefine" (msg1 defName loc ^ msg2 defName goalstring)
     end
  fun report_successful_candidate tm candidates =
      let val i = index_of (aconv tm) candidates
          val mesg = String.concat
              ["Termination proof successful with candidate ",
               Int.toString i, ":\n  "]
      in
         lztrace(1, mesg, fn () => term_to_string tm ^ "\n\n")
      end
  fun report_failure_of_candidates() =
      lztrace(1, "All candidates failed.\n", fn () => "\n")
 in
  fun located_defnDefine loc defn =
   let val V = params_of defn
       val _ = if not (null V) then fvs_on_rhs V else ()  (* can fail *)
       val (defn',opt) =
           if not (should_try_to_prove_termination defn V) then
             (defn,NONE)
           else
           let val tprover = proveTotal (mk_term_tac())
               fun try_proof Rcand = tprover (set_reln defn Rcand)
           in
             (if reln_is_not_set defn then  (* look for suitable term. reln *)
                 let val candidates = guessR defn
                     val (cand,result) = trylist try_proof candidates
                     val () = report_successful_candidate cand candidates
                 in result end
              else (* one is already installed, try to prove TCs *)
                 tprover defn
             ) handle HOL_ERR _ =>
                  (report_failure_of_candidates();
                   termination_proof_failed loc defn)
           end
   in
       save_defn_at loc defn'
     ; (LIST_CONJ (map GEN_ALL (eqns_of defn')),
        ind_of defn', opt)
   end
  val defnDefine = located_defnDefine DB.Unknown
end

fun located_primDefine loc = located_defnDefine loc

val primDefine = located_primDefine DB.Unknown

(*---------------------------------------------------------------------------*)
(* Make a definition, giving the name to store things under. Try to          *)
(* automatically prove termination, if needed.                                *)
(*---------------------------------------------------------------------------*)

fun def_n_ind (def, indopt, NONE) = (def, NONE)
  | def_n_ind (def,indopt, SOME _) = (def, indopt)

fun located_xDefine loc stem q =
  let fun thunk() =
      let val snap1 = thy_consts (current_theory())
          val defn = Defn.Hol_defn stem q
          val result = def_n_ind (located_primDefine loc defn)
          val snap2 = thy_consts (current_theory())
      in delete_support defn snap2 snap1 ;
         result
      end
  in Parse.try_grammar_extension thunk () end
  handle e => render_exn (wrap_exn "TotalDefn" "xDefine" e);

val xDefine = located_xDefine DB.Unknown

(*---------------------------------------------------------------------------
     Define
 ---------------------------------------------------------------------------*)

local
   fun msg alist invoc =
      String.concat
        ["Definition failed! Can't make name for storing definition\n",
         "because there is no alphanumeric identifier in: \n\n   ",
         wfrecUtils.list_to_string Lib.quote "," alist,
         ".\n\nTry \"",invoc, "\" instead.\n\n"]
   fun mk_bindstem exn invoc alist =
      Lib.first Lexis.ok_identifier alist
      handle HOL_ERR _ => (Lib.say (msg alist invoc); raise exn)
in
fun quotation_to_stem q =
    let
      val absyn0 = Parse.Absyn q
      val locn = Absyn.locn_of_absyn absyn0
      val (_,names) = Defn.parse_absyn absyn0
    in
      mk_bindstem (ERRloc "Define" locn "") "Define <quotation>" names
    end

end

(*---------------------------------------------------------------------------*)
(* Definitions with an explicit termination proof.                           *)
(*                                                                           *)
(* Such a definition is pending from its preparation until its termination   *)
(* proof is complete: its support constants stay, and storing its equations  *)
(* and induction theorem, its attributes and its registrations wait.  If the *)
(* proof suspends goals (markerLib.suspend), the definition waits under its  *)
(* equations' name among the suspended theorems, for Resume, and finalising  *)
(* that name completes it.  Pending definitions live in the context, so a    *)
(* heap saved part-way through carries them; a theory with one pending      *)
(* cannot be exported.                                                       *)
(*---------------------------------------------------------------------------*)

(* The settings a definition is made and stored under: their values when
   it is prepared *)
type scope = {def_suffix : string, ind_suffix : string,
              bflags : (HOLFlags.bflag * bool) list}

fun in_scope ({def_suffix, ind_suffix, bflags} : scope) f =
    HOLFlags.with_bflags bflags
      (with_flag (Defn.def_suffix, def_suffix)
         (with_flag (Defn.ind_suffix, ind_suffix) f))

fun current_scope () : scope =
    {def_suffix = !Defn.def_suffix, ind_suffix = !Defn.ind_suffix,
     bflags = map (fn f => (f, HOLFlags.get_bflag f))
                  [computeLib.auto_import_definitions, allow_schema_definition,
                   Theory.allow_rebinds, delete_support_defs]}

type pending = {loc : DB.thm_src_location, goal : goal,
                validate : thm -> thm, finish : thm -> thm * thm option}

(* The current theory's definitions whose termination is not yet proved,
   by their equations' name *)
val pending_slot : (string * pending) list Context.Data.slot =
    Context.Data.new {name = "TotalDefn.pending_definitions", empty = [],
                      pp = String.concatWith ", " o map #1}

fun pending_definition name =
    Option.map #2 (List.find (fn (n, _) => n = name)
                     (Context.Data.get pending_slot (Context.snapshot ())))

fun set_pending0 name p =
    let val entry = case p of NONE => [] | SOME p => [(name, p)]
    in
      Context.Data.modify pending_slot
        (fn ps => entry @ List.filter (fn (n, _) => n <> name) ps)
    end

val _ = Theory.register_hook
  ("TotalDefn.pending_definitions",
   fn TheoryDelta.NewTheory _ => Context.Data.write pending_slot []
    | _ => ())

(* A pending definition reserves its name with markerLib, which keeps
   Resume and Finalise of it in the current theory and the theory from
   being exported *)
fun set_pending name p =
    (set_pending0 name p;
     markerLib.set_finaliser name
       (Option.map (fn _ => fn _ =>
                       raise ERR "Finalise" ("The termination of " ^
                                             Lib.quote name ^
                                             " is not proved")) p))

fun is_suspended name =
    case markerLib.lookup_suspension name of
        SOME (thy, _) => thy = current_theory ()
      | NONE => false

(* th proves w, the goal of name's termination or what proving it gives,
   from the goal's assumptions asl and suspended goals only *)
fun check_proof fname name asl w th =
    aconv (concl th) w andalso
    List.all (fn h => tmem h asl orelse
                      Option.isSome (boolLib.dest_suspended h)) (hyp th)
    andalso Theory.uptodate_thm th orelse
    raise ERR fname ("Theorem does not prove the termination goal of " ^
                     Lib.quote name)

fun list_conj_gen th = th |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ

datatype prepared = Made of thm * thm option
                  | Goal of {bind : string, name : string, goal : goal}

fun delete_consts cs =
    if deleting_support () then
      List.app (fn c => if uptodate_term c then
                          Theory.delete_const (fst (dest_const c))
                          handle HOL_ERR _ => ()
                        else ()) cs
    else ()

(* Makes the definition, in scope; post runs after it is stored, outside *)
fun prepare loc stem q scope post =
  let open Defn
      val bind = stem ^ !Defn.def_suffix
      val _ = not (Option.isSome (pending_definition bind) orelse
                   is_suspended bind) orelse
              raise ERR "prepare" ("Definition " ^ Lib.quote bind ^
                                   " is already pending")
      val snap1 = thy_consts (current_theory())
      val defn = Hol_defn stem q
      val ps = params_of defn
      val _ = null ps orelse get_allow_schema_definition() orelse
              complain_about_rhsfvs "tDefine" ps
  in
    if triv_defn defn then
      let val def = fetch_eqns defn
          val _ = HOL_MESG "Termination argument ignored (term. proved \
                           \automatically)"
      in been_stored (bind,def);
         Theory.upd_binding bind (DB_dtype.updsrcloc (K loc));
         Made (def, NONE)
      end
    else
      let val (name, (goal, validate)) = tc_obligation defn
          val support =
              DefnBase.support_consts defn (thy_consts (current_theory())) snap1
          fun store th =
              let val def = list_conj_gen (CONJUNCT1 th)
                  val ind = CONJUNCT2 th
              in
                delete_consts support;
                store_at loc (stem,def,ind);
                (def, SOME ind)
              end
          fun finish th = let val r = in_scope scope store th
                          in post r; r end
      in
        set_pending bind (SOME {loc = loc, goal = goal, validate = validate,
                                finish = finish});
        Goal {bind = bind, name = name, goal = goal}
      end
  end

(* The pending definition name, and th, a proof of its goal, validated *)
fun checked fname name th =
    case pending_definition name of
        NONE => raise ERR fname ("No pending definition " ^ Lib.quote name)
      | SOME (p as {goal = (asl, w), validate, ...}) =>
        (check_proof fname name asl w th; (p, validate th))

(* Completes the pending definition name from th, a validated proof of its
   goal.  If th has suspended goals, the definition is suspended under
   name, and finalising it (markerLib.finalise_suspended_thm) completes
   it. *)
fun complete name ({loc, goal = (asl, _), finish, ...} : pending) th =
    let
      fun finalise th' = (check_proof "Finalise" name asl (concl th) th';
                          #1 (finish th'))
    in
      if boolLib.has_suspended_subgoals th then
        (boolLib.save_thm_attrs loc
           ({thmname = name, attrs = [], reserved = [], unknown = []}, th);
         set_pending0 name NONE;
         markerLib.set_finaliser name (SOME finalise);
         (list_conj_gen (CONJUNCT1 th), NONE))
      else
        finish th before set_pending name NONE
    end

fun define_with_tactic loc stem q tac scope post =
  let fun thunk () =
        case in_scope scope (fn () => prepare loc stem q scope post) () of
            Made r => (post r; r)
          | Goal {bind, name, goal} =>
            let
              val (p, th) =
                  checked "tDefine" bind
                    (in_scope scope
                       (fn g => boolLib.prove_named (Context.snapshot ()) g)
                       {name = name, goal = goal, tac = tac})
                  handle e => (set_pending bind NONE; raise e)
            in
              complete bind p th
            end
  in
    Parse.try_grammar_extension thunk ()
    handle e => render_exn (wrap_exn "TotalDefn" "tDefine" e)
  end

fun located_tDefine loc stem q tac =
    define_with_tactic loc stem q tac (current_scope ()) ignore

val tDefine = located_tDefine DB.Unknown

fun complete_definition name th =
    #1 (Lib.uncurry (complete name) (checked "complete_definition" name th))

(* ----------------------------------------------------------------------
    version of Define that allows control of options with "attributes"
    attached to the name, and provides an optional termination tactic
   ---------------------------------------------------------------------- *)
fun test_remove n kvl =
    let val (ns, rest) = Lib.partition (fn (k,_) => k = n) kvl
    in
      (not (null ns), rest)
    end

fun find_indoption kvl =
    case Lib.partition (fn (k,_) => k = "induction") kvl of
        ([], _) => (NONE, kvl)
      | ([(k,[v])], rest) => (SOME v, rest)
      | _ => raise ERR "Definition" "multiple induction attribute-values"

fun tailrecDefine loc nm q =
    let
      val (t, _) = Defn.parse_absyn (Parse.Absyn q)
      val th = tailrecLib.gen_tailrec_define {name = nm, def = t, loc = loc}
    in
      Defn.add_defs_to_EVAL [(nm,th)];
      th
    end

val _ = List.app ThmAttribute.reserve_word
                 ["nocompute", "schematic", "tailrecursive"]

(* The name, the scope its attributes give, and what they do once the
   definition is stored *)
fun definition_options stem =
    let
      val {thmname=corename, attrs=attrs,reserved=R,unknown} =
          ThmAttribute.extract_attributes stem
      val (nocomp, R) = test_remove "nocompute" R
      val (svarsok, R) = test_remove "schematic" R
      val (notuserdef, R) = test_remove "notuserdef" R
      val (rebindok, R) = test_remove "allow_rebind" R
      val (tailrecp, R) = test_remove "tailrecursive" R
      val (indopt, R) = find_indoption R
      val _ = null unknown orelse
              raise ERR "Definition"
                    ("Unknown attributes: " ^
                     String.concatWith ", " (map #1 unknown))
      val flag = HOLFlags.get_bflag
      val auto_import = computeLib.auto_import_definitions
      val scope =
          {def_suffix = "",
           ind_suffix = case indopt of NONE => "" | SOME s => " " ^ s,
           bflags = [(auto_import, not nocomp andalso flag auto_import),
                     (allow_schema_definition,
                      svarsok orelse flag allow_schema_definition),
                     (Theory.allow_rebinds,
                      rebindok orelse flag Theory.allow_rebinds),
                     (delete_support_defs, flag delete_support_defs)]}
      fun post (thm, indopt) =
        let
          fun proc_attr (k,vs) =
              ThmAttribute.store_at_attribute{name = corename, attrname = k,
                                              args = vs, thm = thm}
          val attrs = if notuserdef then attrs else ("userdef",[]) :: attrs
          val gen_ind =
              if tailrecp then (fn th => raise ERR "Unseen" "")
              else Prim_rec.gen_indthm {lookup_ind = TypeBase.induction_of}
        in
          List.app proc_attr attrs;
          if notuserdef then ()
          else
            case indopt of
                NONE => (case total gen_ind thm of
                             NONE => ()
                           | SOME p => DefnBase.register_indn p)
              | SOME ith =>
                DefnBase.register_indn (ith, DefnBase.constants_of_defn thm)
        end
    in
      {corename = corename, scope = scope, post = post, tailrecp = tailrecp}
    end

(* The context is the channel the expansion supplies; the quote and the
   termination proof are handled by the Defn machinery below, which does
   not take one yet. *)
fun located_qDefine loc stem q tacopt (_ : Context.t) =
    let
      val {corename, scope, post, tailrecp} = definition_options stem
      fun stored r = (post r; #1 r)
    in
      case (tailrecp, tacopt) of
          (true, NONE) =>
          stored (in_scope scope (tailrecDefine loc corename) q, NONE)
        | (true, SOME _) =>
          raise ERR "qDefine"
                "Termination tactic for tail-recursive definition makes \
                \no sense"
        | (false, NONE) =>
          stored (in_scope scope (located_xDefine loc corename) q)
        | (false, SOME tac) =>
          #1 (define_with_tactic loc corename q tac scope post)
    end

fun prepare_qDefine stem q =
    let
      val {corename, scope, post, tailrecp} = definition_options stem
      val _ = not tailrecp orelse
              raise ERR "prepare_qDefine"
                    "Tail-recursive definitions have no termination proof"
      fun prep () = prepare DB.Unknown corename q scope post
      fun thunk () =
          case in_scope scope prep () of
              Made r => (post r; NONE)
            | Goal {goal, ...} => SOME goal
    in
      Parse.try_grammar_extension thunk ()
      handle e => render_exn (wrap_exn "TotalDefn" "prepare_qDefine" e)
    end

fun qDefine stem q tacopt =
    located_qDefine DB.Unknown stem q tacopt (Context.snapshot())

fun Define q =
    let
      val stem = quotation_to_stem q
    in
      qDefine (stem ^ !Defn.def_suffix) q NONE
    end

(*---------------------------------------------------------------------------*)
(* Version of Define that supports multiple definitions, failing if any do.  *)
(*---------------------------------------------------------------------------*)

fun multidefine q = List.map (#1 o primDefine) (Defn.Hol_multi_defns q)

fun multiDefine q =
  Parse.try_grammar_extension (Theory.try_theory_extension multidefine) q
  handle e => render_exn (wrap_exn "TotalDefn" "multiDefine" e);

(*---------------------------------------------------------------------------*)
(* API for Define                                                            *)
(*---------------------------------------------------------------------------*)

datatype phase
  = PARSE of term quotation
  | BUILD of term
  | TERMINATION of defn;

type apidefn = (defn * thm option, phase * exn) Lib.verdict


(*---------------------------------------------------------------------------*)
(* Turn off printing of messages by the HOL system for the duration of the   *)
(* invocation of f.                                                          *)
(*---------------------------------------------------------------------------*)

fun silent f =
  Lib.with_flag(Lib.saying,false)
   (Lib.with_flag(Feedback.emit_WARNING,false)
     (Lib.with_flag(Feedback.emit_MESG,false) f));

(*---------------------------------------------------------------------------*)
(* Instantiate the termination conditions of a defn with a relation and      *)
(* attempt to prove termination. Note that this includes having to prove     *)
(* that the supplied relation is well-founded.                               *)
(*---------------------------------------------------------------------------*)

fun tryR tac defn = proveTotal tac o Defn.set_reln defn;

(*---------------------------------------------------------------------------*)
(* Given a guesser of termination relations and a prover for termination     *)
(* conditions, try the guesses until the prover succeeds. Return the proved  *)
(* termination conditions as a theorem, along with the tc-free defn.         *)
(*---------------------------------------------------------------------------*)

fun elimTCs guessR tac defn =
 case guessR defn
   of [] => (defn,NONE)   (* prim. rec. or non-rec. defn *)
    | guesses => Lib.tryfind (tryR tac defn) guesses;

(*---------------------------------------------------------------------------*)
(* Sequence the phases of definition, starting from a stem and a term        *)
(*---------------------------------------------------------------------------*)

fun apiDefine guessR tprover (stem,tm) =
  PASS tm ?> verdict (Defn.mk_defn stem) BUILD
          ?> verdict (elimTCs guessR (tprover())) TERMINATION;

(*---------------------------------------------------------------------------*)
(* Sequence the phases of definition, starting from a quotation              *)
(*---------------------------------------------------------------------------*)

fun stem eqn = (fst (dest_const (fst (strip_comb (lhs eqn)))),eqn)

fun apiDefineq guessR tprover q =
   PASS q ?> verdict (silent (stem o hd o Defn.parse_quote)) PARSE
          ?> apiDefine guessR tprover;

(*---------------------------------------------------------------------------*)
(* Instantiate to the current guesser and terminator                         *)
(*---------------------------------------------------------------------------*)

val std_apiDefine = apiDefine guessR mk_term_tac;
val std_apiDefineq = apiDefineq guessR mk_term_tac;

(*---------------------------------------------------------------------------
    Special entrypoints for defining schemas
 ---------------------------------------------------------------------------*)

fun xDefineSchema stem =
   HOLFlags.with_bflags [(allow_schema_definition,true)] (xDefine stem);

val DefineSchema =
   HOLFlags.with_bflags [(allow_schema_definition,true)] Define;

end
