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

fun render_exn srcfn e =
    if !Globals.interactive then
      (Feedback.output_ERR (Feedback.exn_to_string e);
       raise ERR srcfn "Exception raised")
    else
      raise e

(*---------------------------------------------------------------------------*)
(* Set up trace stuff                                                        *)
(*---------------------------------------------------------------------------*)

local
  val monitoring = ref 0
  val _ = register_trace
             ("Definition.termination candidates", monitoring, 4)
in
fun lztrace(i,title,msgf) =
  if i <= !monitoring then
     Lib.say $ String.concat ["\n", title, msgf()]
  else ()
end

val allow_schema_definition = ref false
val _ = Feedback.register_btrace
         ("Definition.allow_schema_definition", allow_schema_definition)

val auto_tgoal = ref true
val _ = Feedback.register_btrace("Definition.auto Defn.tgoal", auto_tgoal)

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

local
fun foo [] _  = raise ERR "foo" "empty arg."
  | foo _ []  = raise ERR "foo" "empty arg."
  | foo [x] Y = [(x,pairSyntax.list_mk_pair Y)]
  | foo X [y] = [(pairSyntax.list_mk_pair X, y)]
  | foo (x::rst) (y::rst1) = (x,y)::foo rst rst1
in
fun dest tm =
  let val Ryx = (snd o strip_imp o snd o strip_forall) tm
      val (Ry, x) = dest_comb Ryx
      val y = rand Ry
      open pairSyntax
  in
     foo (spine_pair y) (spine_pair x)
  end
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
                 handle e => render_exn "last'" e
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

fun flat_type_size ty = case
        (total sumSyntax.dest_sum ty, total pairSyntax.dest_prod ty) of
    (SOME (lty, rty), _) => list_mk_icomb (basicSizeSyntax.sum_size_tm,
        map flat_type_size [lty, rty])
  | (NONE, SOME (lty, rty)) => list_mk_icomb (basicSizeSyntax.min_pair_size_tm,
        map flat_type_size [lty, rty])
  | _ => TypeBasePure.type_size (TypeBase.theTypeBase()) ty

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

fun SOLVES tac g =
  let val result as (subgoals, vfn) = tac g
  in if null subgoals then result else NO_TAC g
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

val termination_solve_simps = ref ([] : thm list);

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
    let val ss' = ss ++ rewrites (!termination_solve_simps @ thl)
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

fun proveTotal tac defn =  let val (WFR,rest) = get_WF (Defn.tcs_of defn)
      val form = list_mk_conj(WFR::rest)
      val thm = Tactical.default_prover(form,tac)
  in
    (Defn.elim_tcs defn (CONJUNCTS thm), SOME thm)
  end;

fun complain_about_rhsfvs srcfn V =
    let
      val Vstr =
          String.concat (Lib.commafy (map (Lib.quote o #1 o dest_var) V))
    in
      raise ERR srcfn
            ("The following variables are free in the \nright hand side of\
             \ the proposed definition: " ^ Vstr)
    end

local open Defn
  fun should_try_to_prove_termination defn rhs_frees =
     let
        val tcs = tcs_of defn
     in
        not(null tcs) andalso
        null (op_intersect aconv (free_varsl tcs) rhs_frees)
     end
  fun fvs_on_rhs V =
      if !allow_schema_definition then ()
      else complain_about_rhsfvs "defnDefine" V
  val msg1 = "\nUnable to prove termination!\n\n\
              \Try using \"TotalDefn.tDefine <name> <quotation> <tac>\".\n"
  val msg2 = "\nThe termination goal has been set up using Defn.tgoal <defn>.\n\
              \Solve the current proof goal (try e.g. p(), WF_REL_TAC).\n"
  fun termination_proof_failed defn =
     let
        val s =
           if !auto_tgoal
              then (Defn.tgoal defn
                    ; PP.prettyPrint
                        (TextIO.print, !Globals.linewidth)
                        (proofManagerLib.pp_proof (proofManagerLib.p()))
                    ; if !Globals.interactive then msg2 else "")
           else ""
     in
        raise ERR "defnDefine" (msg1 ^ s)
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
    let
       val V = params_of defn
       val _ = if not (null V) then fvs_on_rhs V else ()  (* can fail *)
       val tprover = proveTotal (mk_term_tac())
       fun try_proof defn Rcand = tprover (set_reln defn Rcand)
       val (defn',opt) =
          if should_try_to_prove_termination defn V
           then
            ((if reln_is_not_set defn then  (* look for suitable term. reln *)
                 let val candidates = guessR defn
                     val (cand,result) = trylist (try_proof defn) candidates
                     val () = report_successful_candidate cand candidates
                 in result end
              else (* one is already installed, try to prove TCs *)
                 tprover defn
             ) handle HOL_ERR _ =>
                 (report_failure_of_candidates();
                  termination_proof_failed defn))
          else
            (defn,NONE)
    in
       save_defn_at loc defn'
       ; (LIST_CONJ (map GEN_ALL (eqns_of defn')), ind_of defn', opt)
    end
  val defnDefine = located_defnDefine DB.Unknown
end

fun located_primDefine loc = located_defnDefine loc

val primDefine = located_primDefine DB.Unknown

(*---------------------------------------------------------------------------*)
(* Make a definition, giving the name to store things under. If anything     *)
(* fails in the process, remove any constants introduced by the definition.  *)
(*---------------------------------------------------------------------------*)

fun def_n_ind (def, indopt, NONE) = (def, NONE)
  | def_n_ind (def,indopt, SOME _) = (def, indopt)

fun located_xDefine loc stem q =
 Parse.try_grammar_extension
   (Theory.try_theory_extension
       (def_n_ind o located_primDefine loc o Defn.Hol_defn stem)) q
  handle e => render_exn "xDefine" e;

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
(* Version of Define where the termination tactic is explicitly supplied.    *)
(*---------------------------------------------------------------------------*)

fun located_tDefine loc stem q tac =
 let open Defn
     fun thunk() =
       let val defn = Hol_defn stem q
           val ps = params_of defn
           val _ = null ps orelse !allow_schema_definition orelse
                   complain_about_rhsfvs "tDefine" ps
       in
        if triv_defn defn then
          let val def = fetch_eqns defn
              val bind = stem ^ !Defn.def_suffix
              val _ = HOL_MESG "Termination argument ignored (term. proved \
                               \automatically)"
          in been_stored (bind,def);
             Theory.upd_binding bind (DB_dtype.updsrcloc (K loc));
             (def, NONE)
          end
        else let val (def,ind) = with_flag (proofManagerLib.chatting,false)
                                           Defn.tprove0(defn,tac)
                 val def = def |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ
             in Defn.store_at loc (stem,def,ind) ;
                (def, SOME ind)
             end
       end
 in
  Parse.try_grammar_extension
    (Theory.try_theory_extension thunk) ()
  handle e => render_exn "tDefine" e
 end

val tDefine = located_tDefine DB.Unknown

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

fun located_qDefine loc stem q tacopt =
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
      fun fmod f =
          f |> (if nocomp then trace ("computeLib.auto_import_definitions", 0)
                else (fn f => f))
            |> (if svarsok then trace ("Definition.allow_schema_definition", 1)
                else (fn f => f))
            |> with_flag(Defn.def_suffix, "")
            |> (case indopt of NONE => with_flag(Defn.ind_suffix, "")
                             | SOME s => with_flag(Defn.ind_suffix, " " ^ s))
            |> (if rebindok then trace ("Theory.allow_rebinds", 1)
                else (fn f => f))
      val (thm,indopt) =
          case (tailrecp, tacopt) of
              (true, NONE) => (fmod (tailrecDefine loc corename) q, NONE)
            | (true, SOME _) =>
              raise ERR "qDefine"
                    "Termination tactic for tail-recursive definition makes \
                    \no sense"
            | (false, NONE) => fmod (located_xDefine loc corename) q
            | (false, SOME tac) => fmod (located_tDefine loc corename q) tac
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
            DefnBase.register_indn (ith, DefnBase.constants_of_defn thm);
      thm
    end

val qDefine = located_qDefine DB.Unknown

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
  handle e => render_exn "multiDefine" e;

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
   with_flag(allow_schema_definition,true) (xDefine stem);

val DefineSchema =
   with_flag(allow_schema_definition,true) Define;

end
