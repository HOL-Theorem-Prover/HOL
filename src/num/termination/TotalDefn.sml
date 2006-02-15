(*---------------------------------------------------------------------------
       Proving that definitions terminate.
 ---------------------------------------------------------------------------*)

structure TotalDefn :> TotalDefn =
struct

open HolKernel Parse boolLib pairLib NonRecSize DefnBase;

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
end

val inv_image_tm = prim_mk_const{Thy="relation",Name="inv_image"};

fun mk_inv_image(R,f) = 
  let val ty1 = fst(dom_rng(type_of R))
      val ty2 = fst(dom_rng(type_of f))
  in
    list_mk_comb(inst[beta |-> ty1, alpha |-> ty2] inv_image_tm,[R,f])
  end;

val list_mk_lex = end_itlist (curry pairSyntax.mk_lex);
val nless_lex = list_mk_lex o copies numSyntax.less_tm;

val strip_lex = strip_binop (total pairSyntax.dest_lex);

(*---------------------------------------------------------------------------*)
(* Takes [v1,...,vn] [i_j,...,i_m], where  1 <= i_j <= i_m <= n and returns  *)
(*                                                                           *)
(*    inv_image ($< LEX ... LEX $<)                                          *)
(*              (\(v1:ty1,...,vn:tyn).                                       *)
(*                  (size_of(tyi)(vi), ..., size_of(tym)(vm)))               *)
(*---------------------------------------------------------------------------*)

fun mk_sized_subsets argvars sizedlist =
  let val lex_comb = nless_lex (length sizedlist)
      val pargvars = list_mk_pair argvars
      fun mk_reln arrangement = 
          mk_inv_image (lex_comb, mk_pabs(pargvars,list_mk_pair arrangement))
  in 
     map mk_reln (perms sizedlist)
  end;

fun imk_var(i,ty) = mk_var("v"^Int.toString i,ty);
               
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
in
fun guessR defn =
 if null (tcs_of defn) then []
  else
  case reln_of defn
   of NONE => []
    | SOME R =>
       let val domty   = fst(dom_rng(type_of R))
           val tysize = TypeBasePure.type_size (TypeBase.theTypeBase())
           fun size_app v = mk_comb(tysize (type_of v),v)
           val (_,tcs) = Lib.pluck isWFR (tcs_of defn)
           val matrix  = map dest tcs
           val check1  = map (map (uncurry proper_subterm)) matrix
           val chf1     = projects check1
           val domtyl_1  = strip_prod_ty chf1 domty
           val domty0  = list_mk_prod_tyl domtyl_1
           val check2  = map (map (not o uncurry aconv)) matrix
           val chf2    = projects check2
           val domtyl_2  = strip_prod_ty chf2 domty
           val indices = Lib.upto 1 (length domtyl_2)
           val (argvars,subset) = 
             itlist2 (fn i => fn (b,ty) => fn (alist,slist) =>
                        let val v = imk_var(i,ty)
                        in (v::alist, if b then size_app v::slist else slist)
                        end) indices domtyl_2 ([],[])
           val lex_combs = mk_sized_subsets argvars subset
       in
          [mk_cmeasure domty0,
           mk_cmeasure (TypeBasePure.type_size
                         (TypeBase.theTypeBase()) domty)]
          @ lex_combs
       end
end;


fun proveTotal tac defn =
  let val thm = Tactical.default_prover
                  (list_mk_conj (Defn.tcs_of defn), tac)
  in
    (Defn.elim_tcs defn (CONJUNCTS thm), thm)
  end;

(*---------------------------------------------------------------------------
      Default TC simplifier and prover. Terribly terribly naive, but
      still useful. It knows all about the sizes of types.
 ---------------------------------------------------------------------------*)

fun get_orig (TypeBasePure.ORIG th) = th
  | get_orig _ = raise ERR "get_orig" "not the original"

val default_simps =
         [combinTheory.o_DEF,
          combinTheory.I_THM,
          prim_recTheory.measure_def,
          relationTheory.inv_image_def,
          pairTheory.LEX_DEF];


fun TC_SIMP_CONV simps tm =
 (REPEATC
   (CHANGED_CONV
     (Rewrite.REWRITE_CONV
        (simps @ default_simps @ mapfilter TypeBasePure.case_def_of
               (TypeBasePure.listItems (TypeBase.theTypeBase())))
       THENC REDEPTH_CONV GEN_BETA_CONV))
  THENC Rewrite.REWRITE_CONV
          (pairTheory.pair_rws @
           mapfilter (get_orig o #2 o valOf o TypeBasePure.size_of0)
               (TypeBasePure.listItems (TypeBase.theTypeBase())))
  THENC REDEPTH_CONV BETA_CONV
  THENC Rewrite.REWRITE_CONV [arithmeticTheory.ADD_CLAUSES]) tm;


(*---------------------------------------------------------------------------
 * Trivial wellfoundedness prover for combinations of wellfounded relations.
 *--------------------------------------------------------------------------*)

local fun BC_TAC th =
        if (is_imp (#2 (strip_forall (concl th))))
        then MATCH_ACCEPT_TAC th ORELSE MATCH_MP_TAC th
        else MATCH_ACCEPT_TAC th;
      open relationTheory prim_recTheory pairTheory
      val WFthms = [WF_inv_image, WF_measure, WF_LESS, WF_EMPTY_REL,
                    WF_PRED, WF_RPROD, WF_LEX, WF_TC]
in
fun WF_TAC thms = REPEAT (MAP_FIRST BC_TAC (thms@WFthms) ORELSE CONJ_TAC)
end;

val ARITH_TAC = CONV_TAC Arith.ARITH_CONV;

val ASM_ARITH_TAC =
 REPEAT STRIP_TAC
    THEN REPEAT (POP_ASSUM
         (fn th => if numSimps.is_arith (concl th)
                   then MP_TAC th else ALL_TAC))
    THEN ARITH_TAC;

fun TC_SIMP_TAC WFthl thl =
   WF_TAC WFthl THEN
   CONV_TAC (TC_SIMP_CONV thl) THEN
   TRY ASM_ARITH_TAC;


(*---------------------------------------------------------------------------
    Rquote is a quotation denoting the termination relation.
 ---------------------------------------------------------------------------*)

fun PRIM_WF_REL_TAC Rquote WFthms simps g =
  (Q.EXISTS_TAC Rquote THEN TC_SIMP_TAC WFthms simps) g;


fun WF_REL_TAC Rquote = PRIM_WF_REL_TAC Rquote [] default_simps;


(*---------------------------------------------------------------------------
       Definition principles that automatically attempt
       to prove termination. If the termination proof
       fails, the definition attempt fails.
 ---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
      The default prover is invoked on goals involving measure
      functions, so the wellfoundedness proofs for the guessed
      termination relations (which are measure functions) are
      trivial and can be blown away with rewriting.
 ---------------------------------------------------------------------------*)

local fun mesg tac (g as (_,tm)) =
        (if !Defn.monitoring
           then print(String.concat
                   ["\nCalling ARITH on\n",term_to_string tm,"\n"])
           else ();
         tac g)
in
fun default_prover g =
 let open prim_recTheory relationTheory
 in (CONV_TAC (TC_SIMP_CONV (WF_measure::WF_LESS::WF_EMPTY_REL::default_simps))
     THEN mesg ASM_ARITH_TAC) g
 end
end;

local open Defn
      val term_prover = proveTotal default_prover
      fun try_proof defn Rcand = term_prover (set_reln defn Rcand)
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
           else raise ERR "primDefine"
            ("  The following variables are free in the \n right hand side of\
             \ the proposed definition: " ^ Vstr)
        end
      fun termination_proof_failed () = 
        raise ERR "primDefine" (String.concat
            ["Unable to prove totality!\nUse \"Defn.Hol_defn\" to make ",
             "the definition,\nand \"Defn.tgoal <defn>\" to set up the ",
             "termination proof.\n"])
in
fun primDefine defn =
 let val V = params_of defn
     val _ = if not(null V) then fvs_on_rhs V else ()  (* can fail *)
     val (defn',th) =
       if should_try_to_prove_termination defn V
         then Lib.tryfind (try_proof defn) (guessR defn)
               handle HOL_ERR _ => termination_proof_failed()
         else (defn,TRUTH)
 in
    save_defn defn'
  ; (LIST_CONJ (eqns_of defn'), ind_of defn', 
     if (concl th) = T then NONE else SOME th)
 end
end;


fun xDefine stem = Lib.try (#1 o primDefine o Defn.Hol_defn stem);


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
            "xDefine <alphanumeric-stem> <eqns-quotation>" names
   in
       #1 (primDefine (Defn.mk_defn bindstem tm))
       handle e => raise (wrap_exn_loc "TotalDefn" "Define" locn e)
   end
val Define = Lib.try define
end;

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
