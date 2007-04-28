(*---------------------------------------------------------------------------
       Proving that definitions terminate.
 ---------------------------------------------------------------------------*)

structure TotalDefn :> TotalDefn =
struct

open HolKernel Parse boolLib pairLib basicSize DefnBase;

val ERR    = mk_HOL_ERR "TotalDefn";
val ERRloc = mk_HOL_ERRloc "TotalDefn";
val WARN   = HOL_WARNING "TotalDefn";

(*---------------------------------------------------------------------------*)
(* proper_subterm t1 t2 iff t1 is a proper subterm of t2                     *)
(*---------------------------------------------------------------------------*)

fun proper_subterm tm1 tm2 =
  not(aconv tm1 tm2) andalso Lib.can (find_term (aconv tm1)) tm2;

fun isWFR tm =
 (case dest_thy_const (fst (strip_comb tm))
   of {Name="WF", Thy="relation",...} => true
    | otherwise => false)
  handle HOL_ERR _ => false;

fun foo [] _  = raise ERR "foo" "empty arg."
  | foo _ []  = raise ERR "foo" "empty arg."
  | foo [x] Y = [(x,pairSyntax.list_mk_pair Y)]
  | foo X [y] = [(pairSyntax.list_mk_pair X, y)]
  | foo (x::rst) (y::rst1) = (x,y)::foo rst rst1;

fun dest tm =
  let val Ryx = (snd o strip_imp o snd o strip_forall) tm
      val (Ry, x) = dest_comb Ryx
      val y = rand Ry
      open pairSyntax
  in
     foo (spine_pair y) (spine_pair x)
  end;

fun max [] m = m
  | max (h::t) m = max t (if h>m then h else m);

fun copies x =
  let fun repl 0 = []
        | repl n = x::repl (n-1)
  in repl
  end;

fun fill n [] = copies false n
  | fill n (h::t) = h::fill (n-1) t;

fun rectangular L =
 let val lens = map length L
 in case mk_set lens
     of []  => raise ERR "rectangular" "impossible"
      | [x] => L
      |  _  => map (fill (max lens 0)) L
 end;

fun true_col L =
 if all null L then []
 else all I (map (Lib.trye hd) L)::true_col (map (Lib.trye tl) L);

fun fix [] = []
  | fix (true::t)  = true::map (fn x => false) t
  | fix (false::t) = false::fix t;

fun transp L =
      if (all null L) then []
      else exists I (map (Lib.trye hd) L)::transp (map (Lib.trye tl) L);

fun projects L0 =
  let val L = rectangular L0
      val trues = true_col L
  in
    if exists I trues then fix trues else transp L
  end;

fun nth P [] _ N = rev N
  | nth P (h::t) n N = nth P t (n+1) (if P h then n::N else N);

fun strip_prod_ty [] _ = raise ERR "strip_prod_ty" ""
  | strip_prod_ty [x] ty = [(x,ty)]
  | strip_prod_ty (h::t) ty =
     let val (x,y) = with_exn pairSyntax.dest_prod ty
                          (ERR "strip_prod_ty" "expected a product type")
     in  (h,x)::strip_prod_ty t y
     end

fun K0 ty = mk_abs(mk_var("v",ty), numSyntax.zero_tm);

fun list_mk_prod_tyl L =
 let val (front,(b,last)) = front_last L
     val tysize = TypeBasePure.type_size (TypeBase.theTypeBase())
     val last' = (if b then tysize else K0) last
     handle e => Raise (wrap_exn "TotalDefn" "last'" e);
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

val inv_image_tm = prim_mk_const{Thy="relation",Name="inv_image"};

fun mk_inv_image(R,f) = 
  let val ty1 = fst(dom_rng(type_of R))
      val ty2 = fst(dom_rng(type_of f))
  in
    list_mk_comb(inst[beta |-> ty1, alpha |-> ty2] inv_image_tm,[R,f])
  end;

fun list_mk_lex []  = raise ERR "list_mk_lex" "empty list"
  | list_mk_lex [x] = x
  | list_mk_lex L   = end_itlist (curry pairSyntax.mk_lex) L;

val nless_lex = list_mk_lex o copies numSyntax.less_tm;

val strip_lex = strip_binop (total pairSyntax.dest_lex);

(*---------------------------------------------------------------------------*)
(* Takes [v1,...,vn] [i_j,...,i_m], where  1 <= i_j <= i_m <= n and returns  *)
(*                                                                           *)
(*    inv_image ($< LEX ... LEX $<)                                          *)
(*              (\(v1:ty1,...,vn:tyn).                                       *)
(*                  (size_of(tyi)(vi), ..., size_of(tym)(vm)))               *)
(*---------------------------------------------------------------------------*)

fun mk_lex_reln argvars sizedlist arrangement = 
  let val lex_comb = nless_lex (length sizedlist)
      val pargvars = list_mk_pair argvars
  in
     mk_inv_image (lex_comb, mk_pabs(pargvars,list_mk_pair arrangement))
  end;

fun take 0 L = []
  | take n [] = raise ERR "take" "not enough elements"
  | take n (h::t) = h::take (n-1) t;

fun mk_sized_subsets argvars sizedlist = 
 let val permutations = 
         if length sizedlist > 4
         then (WARN "mk_sized_subsets" 
                 "too many permutations (more than 24): chopping some";
               perms (take 4 sizedlist))
         else perms sizedlist
 in 
  map (mk_lex_reln argvars sizedlist) permutations
 end;

fun imk_var(i,ty) = mk_var("v"^Int.toString i,ty);

fun simplifyR tm = 
 let open prim_recTheory basicSizeTheory reduceLib
     val expand = QCONV (REWRITE_CONV 
                    [measure_def,pair_size_def,bool_size_def,one_size_def])
     val zero_elim = 
        QCONV (REWRITE_CONV 
          [EQT_ELIM (Arith.ARITH_CONV 
                 ``!x:num. (x + 0 = x) /\ (0 + x = x)``)])
 in
  rhs (concl 
   ((expand THENC DEPTH_CONV BETA_CONV THENC zero_elim) tm))
 end;

(* Remove duplicates, while maintaining left-to-right order *)

fun rm x [] = []
  | rm x (h::t) = if aconv x h then rm x t else h::rm x t;

fun mk_set [] = []
  | mk_set (h::t) = h::mk_set (rm h t);

(*---------------------------------------------------------------------------*
 * The general idea behind this is to try 2 termination measures. The first  *
 * measure takes the size of all subterms meeting the following criteria:    *
 * argument i in a recursive call must be a proper subterm of argument i     *
 * in the head call. For i, if at least one TC meets this criteria, then     *
 * position i will be measured. This measure should catch all primitive      *
 * recursions, and primitive recursive tail recursions. Because of           *
 * various syntactic limitations to the form of primitive recursions in HOL  *
 * e.g. not allowing varstructs, this should be useful. Also, this step      *
 * catches some non-prim.rec tail recursions, see the examples.              *
 *                                                                           *
 * The second measure is just the total size of the arguments.               *
 *---------------------------------------------------------------------------*)

local open Defn numSyntax
(* fun is_word ty = 
    case total mk_thy_type{Tyop = "cart",Thy="fcp",Args=[bool,alpha]}
     of SOME pty => Lib.can (match_type pty) ty
      | NONE => false
 fun tysize ty = 
    if is_word ty 
      then fst(TypeBase.size_of ty)
      else TypeBasePure.type_size (TypeBase.theTypeBase()) ty
*)
 fun tysize ty = TypeBasePure.type_size (TypeBase.theTypeBase()) ty
 fun size_app v = mk_comb(tysize (type_of v),v)
in
fun guessR defn =
 if null (tcs_of defn) then []
  else
  case reln_of defn
   of NONE => []
    | SOME R =>
       let val domty  = fst(dom_rng(type_of R))
           val (_,tcs) = Lib.pluck isWFR (tcs_of defn)
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
           val check2  = map (map (not o uncurry aconv)) matrix
           val chf2    = projects check2
           val domtyl_2 = strip_prod_ty chf2 domty
           val indices = Lib.upto 1 (length domtyl_2)
           val (argvars,subset) = 
             itlist2 (fn i => fn (b,ty) => fn (alist,slist) =>
                        let val v = imk_var(i,ty)
                        in (v::alist, if b then size_app v::slist else slist)
                        end) indices domtyl_2 ([],[])
           val lex_combs = mk_sized_subsets argvars subset
           val allrels = [mk_cmeasure domty0,mk_cmeasure (tysize domty)]
                         @ it_prim_rec @ lex_combs
           val allrels' = mk_set (map simplifyR allrels)
       in
         allrels'
       end
end;

(*---------------------------------------------------------------------------*)
(* Wellfoundedness and termination provers (parameterized by theorems).      *)
(* The default TC simplifier and prover is terribly terribly naive, but      *)
(* still useful. It knows all about the sizes of types.                      *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Wellfoundedness prover for combinations of wellfounded relations.         *)
(*---------------------------------------------------------------------------*)

val default_WF_thms = 
 let open relationTheory prim_recTheory pairTheory
 in
   ref [WF_inv_image, WF_measure, WF_LESS, 
        WF_EMPTY_REL, WF_PRED, WF_RPROD, WF_LEX, WF_TC]
 end;

fun BC_TAC th =
  if is_imp (#2 (strip_forall (concl th)))
  then MATCH_ACCEPT_TAC th ORELSE MATCH_MP_TAC th
    else MATCH_ACCEPT_TAC th;

fun PRIM_WF_TAC thl = REPEAT (MAP_FIRST BC_TAC thl ORELSE CONJ_TAC);
fun WF_TAC g = PRIM_WF_TAC (!default_WF_thms) g;

(*--------------------------------------------------------------------------*)
(* Basic simplification and proof for remaining termination conditions.     *)
(*--------------------------------------------------------------------------*)

val default_termination_simps =
     ref [combinTheory.o_DEF,
          combinTheory.I_THM,
          prim_recTheory.measure_def,
          relationTheory.inv_image_def,
          pairTheory.LEX_DEF];

val ASM_ARITH_TAC =
 REPEAT STRIP_TAC
    THEN REPEAT (POP_ASSUM
         (fn th => if numSimps.is_arith (concl th)
                   then MP_TAC th else ALL_TAC))
    THEN CONV_TAC Arith.ARITH_CONV;

fun get_orig (TypeBasePure.ORIG th) = th
  | get_orig _ = raise ERR "get_orig" "not the original"

val term_ss = 
 let open simpLib infix ++
 in boolSimps.bool_ss 
    ++ pairSimps.PAIR_ss 
    ++ numSimps.REDUCE_ss 
    ++ numSimps.ARITH_RWTS_ss
 end; 

fun PRIM_TC_SIMP_CONV simps tm =
 let open arithmeticTheory 
     val els = TypeBasePure.listItems (TypeBase.theTypeBase())
     val size_defs = 
        mapfilter (get_orig o #2 o valOf o TypeBasePure.size_of0) els
     val case_defs = mapfilter TypeBasePure.case_def_of els
 in
  simpLib.SIMP_CONV term_ss (simps@size_defs@case_defs)
 end tm;

fun PRIM_TC_SIMP_TAC thl = 
  CONV_TAC (PRIM_TC_SIMP_CONV thl) THEN TRY ASM_ARITH_TAC;

fun TC_SIMP_CONV tm = PRIM_TC_SIMP_CONV (!default_termination_simps) tm;
fun TC_SIMP_TAC g = PRIM_TC_SIMP_TAC (!default_termination_simps) g;

local 
 fun mesg tac (g as (_,tm)) =
  let in 
    if !Defn.monitoring then 
      print(String.concat["\nCalling ARITH on\n",term_to_string tm,"\n"])
      else ()
   ; tac g
 end
in
fun PRIM_TERM_TAC wftac tctac = CONJ_TAC THENL [wftac,tctac]
val STD_TERM_TAC = PRIM_TERM_TAC WF_TAC TC_SIMP_TAC;
val PROVE_TERM_TAC = 
   PRIM_TERM_TAC WF_TAC 
       (CONV_TAC TC_SIMP_CONV THEN mesg ASM_ARITH_TAC)
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
 
val WF_tm = prim_mk_const{Name="WF",Thy="relation"};

fun get_WF tmlist = 
 pluck (same_const WF_tm o rator) tmlist
 handle HOL_ERR _ => raise ERR "get_WF" "unexpected termination condition";

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
  fun should_try_to_prove_termination defn rhs_frees =
     let val tcs = tcs_of defn
     in not(null tcs) andalso
        null(intersect (free_varsl tcs) rhs_frees)
     end
  fun fvs_on_rhs V = 
     let val Vstr = String.concat (Lib.commafy
                       (map (Lib.quote o #1 o dest_var) V))
     in if !allow_schema_definition 
        then HOL_MESG (String.concat
            ["Definition is schematic in the following variables:\n    ",
             Vstr])
        else raise ERR "defnDefine"
         ("  The following variables are free in the \n right hand side of\
          \ the proposed definition: " ^ Vstr)
     end
  fun termination_proof_failed () = 
     raise ERR "defnDefine" (String.concat
         ["Unable to prove totality!\nUse \"Defn.Hol_defn\" to make ",
          "the definition,\nand \"Defn.tgoal <defn>\" to set up the ",
          "termination proof.\n"])
in
fun defnDefine term_tac defn =
 let val V = params_of defn
     val _ = if not(null V) then fvs_on_rhs V else ()  (* can fail *)
     val tprover = proveTotal term_tac
     fun try_proof defn Rcand = tprover (set_reln defn Rcand)
     val (defn',opt) =
       if should_try_to_prove_termination defn V
         then ((if reln_is_not_set defn
                 then Lib.tryfind (try_proof defn) (guessR defn)
                 else tprover defn)
              handle HOL_ERR _ => termination_proof_failed())
         else (defn,NONE)
 in
    save_defn defn'
  ; (LIST_CONJ (eqns_of defn'), ind_of defn', opt)
 end
end;

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

local fun msg alist invoc = String.concat
          ["Definition failed! Can't make name for storing definition\n",
           "because there is no alphanumeric identifier in: \n\n   ",
           wfrecUtils.list_to_string Lib.quote "," alist,
           ".\n\nTry \"",invoc, "\" instead.\n\n"]
       fun mk_bindstem exn invoc alist =
            Lib.first Lexis.ok_identifier alist
            handle HOL_ERR _ => (Lib.say (msg alist invoc); raise exn)
in
fun define q =
 let val absyn0 = Parse.Absyn q
     val locn = Absyn.locn_of_absyn absyn0
     val (tm,names) = Defn.parse_defn absyn0
     val bindstem = mk_bindstem (ERRloc "Define" locn "")
                   "Define <alphanumeric-stem> <eqns-quotation>" names
 in
    #1 (primDefine (Defn.mk_defn bindstem tm))
    handle e => raise (wrap_exn_loc "TotalDefn" "Define" locn e)
 end

fun Define q = 
 Parse.try_grammar_extension
    (Theory.try_theory_extension define) q
 handle e => Raise e
end;

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
        else let val (def,ind) = with_flag (goalstackLib.chatting,false)
                                         Defn.tprove0(defn,tac)
             in Defn.store(stem,def,ind) ; def
             end
       end
 in
  Parse.try_grammar_extension
    (Theory.try_theory_extension thunk) ()
  handle e => Raise (wrap_exn "TotalDefn" "tDefine" e)
 end;

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
(* Parse a quotation. Fail if parsing or type inference or overload          *)
(* resolution (etc) fail. Also fail if a usable name for the definition      *)
(* can't be found in the names of the function(s) under definition.          *)
(*---------------------------------------------------------------------------*)

local 
 fun mesg slist = 
   String.concat ("No alphanumeric identifiers in :" 
                  :: Lib.commafy (map Lib.quote slist))
in
fun parse_defn_quote q =
  let val (tm,names) = Defn.parse_defn (Parse.Absyn q)
      val stem = Lib.first Lexis.ok_identifier names 
                  handle HOL_ERR _ => 
                  raise ERR "parse_quote" (mesg names)
  in (stem,tm)
  end
end;

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

fun apiDefineq guessR tprover q = 
   PASS q ?> verdict (silent parse_defn_quote) PARSE
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

(*---------------------------------------------------------------------------*)
(* Moving SUC out of patterns on lhs                                         *)
(*---------------------------------------------------------------------------*)


val SUC_TO_NUMERAL_DEFN_CONV = let
  fun UBLIST [] = ALL_CONV
    | UBLIST (h::t) = UNBETA_CONV h THENC RATOR_CONV (UBLIST t)
  fun basic_elim t = let
    (* t of form !n. ..SUC n.. = .. n .. SUC n .. *)
    val (v, body) = dest_forall t
    val sv = numSyntax.mk_suc v
  in
    BINDER_CONV (LAND_CONV (UNBETA_CONV sv) THENC
                 RAND_CONV (UBLIST [sv, v])) THENC
    REWR_CONV arithmeticTheory.SUC_ELIM_NUMERALS THENC
    BINOP_CONV (BINDER_CONV (BINOP_CONV LIST_BETA_CONV) THENC
                RAND_CONV (ALPHA_CONV v))
  end t

  fun push_down t =
      if is_forall (#2 (dest_forall t)) then
        (SWAP_VARS_CONV THENC BINDER_CONV push_down) t
      else ALL_CONV t
  fun push_nth_down n t =
      if n > 0 then BINDER_CONV (push_nth_down (n - 1)) t
      else push_down t
  fun pull_up t =
      if is_forall (#2 (dest_forall t)) then
        (BINDER_CONV pull_up THENC SWAP_VARS_CONV) t
      else ALL_CONV t
  fun pull_upto_nth n t =
      if n > 0 then BINDER_CONV (pull_upto_nth (n - 1)) t
      else pull_up t
  fun push_over_conjs t =
      if is_forall t then
        (BINDER_CONV push_over_conjs THENC FORALL_AND_CONV) t
      else ALL_CONV t

  fun unsuc_conjn c = let
    val (vs, body) = strip_forall c
    val (l, r) = dest_eq body
    val suc_terms = find_terms numSyntax.is_suc l
    fun elim_one_suc st t = let
      val v = numSyntax.dest_suc st
    in
      if is_var v then
        case Lib.total (index (equal v)) vs of
          NONE => ALL_CONV t
        | SOME i => (push_nth_down i THENC
                     LAST_FORALL_CONV basic_elim THENC
                     push_over_conjs THENC
                     BINOP_CONV (pull_upto_nth i)) t
      else
        ALL_CONV t
    end
  in
    EVERY_CONV (map (EVERY_CONJ_CONV o elim_one_suc) suc_terms) c
  end
  fun reassociate_toplevel_conjns t =
      if is_conj t then
        ((REWR_CONV (GSYM CONJ_ASSOC) THENC
          reassociate_toplevel_conjns) ORELSEC
         RAND_CONV reassociate_toplevel_conjns) t
      else ALL_CONV t
in
  EVERY_CONJ_CONV unsuc_conjn THENC reassociate_toplevel_conjns
end

val _ = Defn.SUC_TO_NUMERAL_DEFN_CONV_hook := SUC_TO_NUMERAL_DEFN_CONV;

end
