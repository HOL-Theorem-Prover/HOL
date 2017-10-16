(*---------------------------------------------------------------------------
       Proving that definitions terminate.
 ---------------------------------------------------------------------------*)

structure TotalDefn :> TotalDefn =
struct

open HolKernel Parse boolLib pairLib basicSize DefnBase numSyntax
     arithmeticTheory;

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
end
open Parse

val ERR    = mk_HOL_ERR "TotalDefn";
val ERRloc = mk_HOL_ERRloc "TotalDefn";
val WARN   = HOL_WARNING "TotalDefn";

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
(* Adjustable set of rewrites for doing termination proof.                   *)
(*---------------------------------------------------------------------------*)

val DIV_LESS_I = prove
(``!n d. 0n < n /\ 1 < d ==> I(n DIV d) < I(n)``,
 REWRITE_TAC[DIV_LESS,combinTheory.I_THM]);

val MOD_LESS_I = prove
(``!m n. 0n < n ==> I(m MOD n) < I(n)``,
 REWRITE_TAC [MOD_LESS,combinTheory.I_THM]);

val SUB_LESS_I = prove
(``!m n. 0n < n /\ n <= m ==> I(m - n) < I(m)``,
 REWRITE_TAC[SUB_LESS,combinTheory.I_THM]);

val termination_simps =
     ref [combinTheory.o_DEF,
          combinTheory.I_THM,
          prim_recTheory.measure_def,
          relationTheory.inv_image_def,
          pairTheory.LEX_DEF,
          pairTheory.RPROD_DEF,
          SUB_LESS_I,DIV_LESS_I,MOD_LESS_I];

(*---------------------------------------------------------------------------*)
(* Adjustable set of WF theorems for doing WF proofs.                        *)
(*---------------------------------------------------------------------------*)

val WF_thms =
 let open relationTheory prim_recTheory pairTheory
 in
   ref [WF_inv_image, WF_measure, WF_LESS,
        WF_EMPTY_REL, WF_PRED, WF_RPROD, WF_LEX, WF_TC]
 end;


(*---------------------------------------------------------------------------*)
(* Same as pairSimps.PAIR_ss, except more eager to force paired              *)
(* beta-reductions. For example, should reduce "(\(x,y). M x y) N" to        *)
(* "M (FST N) (SND N)"                                                       *)
(*---------------------------------------------------------------------------*)

val term_ss =
 let open simpLib infix ++
 in boolSimps.bool_ss
    ++ pairSimps.PAIR_ss
    ++ pairSimps.paired_forall_ss
    ++ pairSimps.paired_exists_ss
    ++ pairSimps.gen_beta_ss
    ++ rewrites [pairTheory.FORALL_PROD]
    ++ numSimps.REDUCE_ss
    ++ numSimps.ARITH_RWTS_ss
 end;

val term_dp_ss =
 let open simpLib infix ++
 in term_ss ++ numSimps.ARITH_DP_ss
 end;


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
                 handle e => Raise (wrap_exn "TotalDefn" "last'" e)
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
     val expand = QCONV (SIMP_CONV term_ss
                    [measure_def,pair_size_def,bool_size_def,one_size_def])
 in
  rhs o concl o expand
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

fun known_fun tm =
 let fun dest_order x = dest_less x handle HOL_ERR _ => dest_leq x
     fun get_lhs th =
            rand (fst(dest_order(snd(strip_imp
                  (snd(strip_forall(concl th)))))))
     val pats = mapfilter get_lhs (!termination_simps)
 in
    0 < length (mapfilter (C match_term tm) pats)
 end;

fun relevant (tm,_) = known_fun tm;

fun guessR defn =
 let open Defn numSyntax simpLib boolSimps
   fun tysize ty = TypeBasePure.type_size (TypeBase.theTypeBase()) ty
   fun size_app v = mk_comb(tysize (type_of v),v)
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
           val allrels = [mk_cmeasure domty0, mk_cmeasure (tysize domty)]
                         @ it_prim_rec @ lex_combs
           val allrels' = mk_term_set (map simplifyR allrels)
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
fun WF_TAC g = PRIM_WF_TAC (!WF_thms) g;

(*--------------------------------------------------------------------------*)
(* Basic simplification and proof for remaining termination conditions.     *)
(*--------------------------------------------------------------------------*)

fun get_orig (TypeBasePure.ORIG th) = th
  | get_orig _ = raise ERR "get_orig" "not the original"

fun PRIM_TC_SIMP_CONV simps =
 let val els = TypeBasePure.listItems (TypeBase.theTypeBase())
     val size_defs =
         mapfilter (get_orig o #2 o valOf o TypeBasePure.size_of0) els
     val case_defs = mapfilter TypeBasePure.case_def_of els
 in
  simpLib.SIMP_CONV term_ss (simps@size_defs@case_defs)
 end;

fun TC_SIMP_CONV tm = PRIM_TC_SIMP_CONV (!termination_simps) tm;

val ASM_ARITH_TAC =
 REPEAT STRIP_TAC
    THEN REPEAT (POP_ASSUM
         (fn th => if numSimps.is_arith (concl th)
                   then MP_TAC th else ALL_TAC))
    THEN CONV_TAC Arith.ARITH_CONV;

fun PRIM_TC_SIMP_TAC thl =
  CONV_TAC (PRIM_TC_SIMP_CONV thl) THEN TRY ASM_ARITH_TAC;

fun TC_SIMP_TAC g = PRIM_TC_SIMP_TAC (!termination_simps) g;

fun PRIM_TERM_TAC wftac tctac = CONJ_TAC THENL [wftac,tctac]

val STD_TERM_TAC = PRIM_TERM_TAC WF_TAC TC_SIMP_TAC;

local
  fun mesg tac (g as (_,tm)) =
    (if !Defn.monitoring then
      print(String.concat["\nCalling ARITH on\n",term_to_string tm,"\n"])
      else () ;
     tac g)
in
fun PROVE_TERM_TAC g =
 let open combinTheory simpLib
     val simps = map (PURE_REWRITE_RULE [I_THM]) (!termination_simps)
     val ss = term_dp_ss ++ rewrites simps
 in
   PRIM_TERM_TAC WF_TAC
      (CONV_TAC TC_SIMP_CONV THEN BasicProvers.PRIM_STP_TAC ss NO_TAC)
 end g
end;


(*---------------------------------------------------------------------------*)
(* Instantiate the termination relation with q and then try to prove         *)
(* wellfoundedness and remaining termination conditions.                     *)
(*---------------------------------------------------------------------------*)

fun PRIM_WF_REL_TAC q WFthms simps g =
  (Q.EXISTS_TAC q THEN CONJ_TAC THENL
   [PRIM_WF_TAC WFthms, PRIM_TC_SIMP_TAC simps]) g;

fun WF_REL_TAC q = Q.EXISTS_TAC q THEN STD_TERM_TAC;


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

local open Defn
  val auto_tgoal = ref true
  val () = Feedback.register_btrace("auto Defn.tgoal", auto_tgoal)

  fun should_try_to_prove_termination defn rhs_frees =
     let
        val tcs = tcs_of defn
     in
        not(null tcs) andalso
        null (op_intersect aconv (free_varsl tcs) rhs_frees)
     end
  fun fvs_on_rhs V =
     let
        val Vstr =
           String.concat (Lib.commafy (map (Lib.quote o #1 o dest_var) V))
     in
        if !allow_schema_definition
           then ()
        else raise ERR "defnDefine"
         ("  The following variables are free in the \n right hand side of\
          \ the proposed definition: " ^ Vstr)
     end
  val msg1 = "\nUnable to prove termination!\n\n\
              \Try using \"TotalDefn.tDefine <name> <quotation> <tac>\".\n"
  val msg2 = "\nThe termination goal has been set up using Defn.tgoal <defn>.\n"
  fun termination_proof_failed defn =
     let
        val s =
           if !auto_tgoal
              then (Defn.tgoal defn
                    ; Portable.pprint
                         proofManagerLib.pp_proof (proofManagerLib.p())
                    ; if !Globals.interactive then msg2 else "")
           else ""
     in
        raise ERR "defnDefine" (msg1 ^ s)
     end
in
  fun defnDefine term_tac defn =
    let
       val V = params_of defn
       val _ = if not (null V) then fvs_on_rhs V else ()  (* can fail *)
       val tprover = proveTotal term_tac
       fun try_proof defn Rcand = tprover (set_reln defn Rcand)
       val (defn',opt) =
          if should_try_to_prove_termination defn V
            then ((if reln_is_not_set defn
                      then Lib.tryfind (try_proof defn) (guessR defn)
                   else tprover defn)
                  handle HOL_ERR _ => termination_proof_failed defn)
            else (defn,NONE)
    in
       save_defn defn'
       ; (LIST_CONJ (map GEN_ALL (eqns_of defn')), ind_of defn', opt)
    end
end

val primDefine = defnDefine PROVE_TERM_TAC;

(*---------------------------------------------------------------------------*)
(* Make a definition, giving the name to store things under. If anything     *)
(* fails in the process, remove any constants introduced by the definition.  *)
(*---------------------------------------------------------------------------*)

fun xDefine stem q =
 Parse.try_grammar_extension
   (Theory.try_theory_extension
       (#1 o primDefine o Defn.Hol_defn stem)) q
  handle e => Raise (wrap_exn "TotalDefn" "xDefine" e);

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
   fun define q =
      let
         val absyn0 = Parse.Absyn q
         val locn = Absyn.locn_of_absyn absyn0
         val (tm,names) = Defn.parse_absyn absyn0
         val bindstem =
            mk_bindstem (ERRloc "Define" locn "") "Define <quotation>" names
      in
         #1 (primDefine (Defn.mk_defn bindstem tm))
         handle e => raise (wrap_exn_loc "TotalDefn" "Define" locn e)
      end

   (* Use of Raise means that typecheck error exceptions will get printed
      anyway; no need to also have the code in Preterm etc print them out
      as well. *)

   fun Define q =
      trace ("show_typecheck_errors", 0)
            (Parse.try_grammar_extension (Theory.try_theory_extension define))
            q
      handle e => Raise e
end

(*---------------------------------------------------------------------------*)
(* Version of Define where the termination tactic is explicitly supplied.    *)
(*---------------------------------------------------------------------------*)

fun tDefine stem q tac =
 let open Defn
     fun thunk() =
       let val defn = Hol_defn stem q
       in
        if triv_defn defn
        then let val def = fetch_eqns defn
                 val bind = stem ^ !Defn.def_suffix
             in been_stored (bind,def); def
             end
        else let val (def,ind) = with_flag (proofManagerLib.chatting,false)
                                         Defn.tprove0(defn,tac)
                 val def = def |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ
             in Defn.store(stem,def,ind) ; def
             end
       end
 in
  Parse.try_grammar_extension
    (Theory.try_theory_extension thunk) ()
  handle e => Raise (wrap_exn "TotalDefn" "tDefine" e)
 end;

(*---------------------------------------------------------------------------*)
(* Version of Define that supports multiple definitions, failing if any do.  *)
(*---------------------------------------------------------------------------*)

fun multidefine q = List.map (#1 o primDefine) (Defn.Hol_multi_defns q)

fun multiDefine q =
  Parse.try_grammar_extension (Theory.try_theory_extension multidefine) q
  handle e => Raise e;

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
          ?> verdict (elimTCs guessR tprover) TERMINATION;

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

val std_apiDefine = apiDefine guessR PROVE_TERM_TAC;
val std_apiDefineq = apiDefineq guessR PROVE_TERM_TAC;

(*---------------------------------------------------------------------------
    Special entrypoints for defining schemas
 ---------------------------------------------------------------------------*)

fun xDefineSchema stem =
   with_flag(allow_schema_definition,true) (xDefine stem);

val DefineSchema =
   with_flag(allow_schema_definition,true) Define;

end
