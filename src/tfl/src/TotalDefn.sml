(*---------------------------------------------------------------------------
       Proving that definitions terminate.
 ---------------------------------------------------------------------------*)

structure TotalDefn :> TotalDefn =
struct

open HolKernel Parse basicHol90Lib arithLib Let_conv NonRecSize DefnBase;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

type thm    = Thm.thm;
type conv   = Abbrev.conv
type tactic = Abbrev.tactic;
type proofs = GoalstackPure.proofs
type defn   = DefnBase.defn;
type 'a quotation = 'a Portable.frag list

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars

fun ERR f m =
  HOL_ERR{origin_structure="TotalDefn", origin_function=f, message=m};



fun proper_subterm tm1 tm2 =
  not(aconv tm1 tm2) andalso Lib.can (find_term (aconv tm1)) tm2;

fun isWFR tm =
  (#Name(dest_const(fst(strip_comb tm))) = "WF")
  handle HOL_ERR _ => false;

fun foo [] _  = raise ERR "foo" "empty arg."
  | foo _ []  = raise ERR "foo" "empty arg."
  | foo [x] Y = [(x,list_mk_pair Y)]
  | foo X [y] = [(list_mk_pair X, y)]
  | foo (x::rst) (y::rst1) = (x,y)::foo rst rst1;

fun dest tm =
  let val Ryx = (snd o strip_imp o snd o strip_forall) tm
      val {Rator=Ry, Rand=x} = dest_comb Ryx
      val y = rand Ry
  in
     foo (strip_pair y) (strip_pair x)
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
      if (all null L) then []
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
     if is_vartype ty then raise ERR "strip_prod_ty" "expected a product type"
     else case dest_type ty
           of {Tyop="prod", Args=[x,y]} => (h,x)::strip_prod_ty t y
            | _ => raise ERR "strip_prod_ty" "expected a product type"

val numty = mk_type{Tyop="num", Args=[]};
val Zero = Term`0n`;
val Plus = mk_const{Name="+", Ty=Type`:num -> num -> num`};
fun mk_plus x y = list_mk_comb(Plus,[x,y]);
fun K0 ty = mk_abs{Bvar=mk_var{Name="v",Ty=ty}, Body=Zero};

fun list_mk_prod_tyl L =
 let val (front,(b,last)) = front_last L
     val tysize = TypeBase.type_size (TypeBase.theTypeBase())
     val last' = (if b then tysize else K0) last
  in
  itlist (fn (b,ty1) => fn M =>
     let val x = mk_var{Name="x",Ty=ty1}
         val y = mk_var{Name="y",Ty=fst(dom_rng (type_of M))}
     in
       mk_pabs {varstruct=mk_pair{fst=x,snd=y},
                 body = mk_plus (mk_comb{Rator=(if b then tysize else K0) ty1,
                                         Rand=x})
                                (mk_comb{Rator=M,Rand=y})}
     end) front last'
 end;


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

local open Defn
in
fun guessR defn =
 if null (tcs_of defn) then []
  else
  case reln_of defn
   of NONE => []
    | SOME R =>
       let val domty = fst(dom_rng(type_of R))
           val (_,tcs) = Lib.pluck isWFR (tcs_of defn)
           val matrix = map dest tcs
           val check1 = map (map (uncurry proper_subterm)) matrix
           val chf = projects check1
           val domtyl = strip_prod_ty chf domty
           val domty0 = list_mk_prod_tyl domtyl
       in
          [Term`measure ^domty0`,
           Term`measure ^(TypeBase.type_size (TypeBase.theTypeBase()) domty)`]
       end
end;


fun proveTotal tac defn = 
  Defn.elim_tcs defn (CONJUNCTS (prove(list_mk_conj (Defn.tcs_of defn), tac)))

(*---------------------------------------------------------------------------
      Default TC simplifier and prover. Terribly terribly naive, but 
      still useful. It knows all about the sizes of types.
 ---------------------------------------------------------------------------*)

fun get_orig (TypeBase.ORIG th) = th
  | get_orig _ = raise ERR "get_orig" "not the original"

fun TC_SIMP_CONV simps tm =
 (REPEATC
   (CHANGED_CONV
     (Rewrite.REWRITE_CONV 
        (simps @ mapfilter TypeBase.case_def_of
               (TypeBase.listItems (TypeBase.theTypeBase())))
       THENC REDEPTH_CONV Let_conv.GEN_BETA_CONV))
  THENC Rewrite.REWRITE_CONV
          (pairTheory.pair_rws @
           mapfilter (get_orig o #2 o valOf o TypeBase.size_of0)
               (TypeBase.listItems (TypeBase.theTypeBase())))
  THENC REDEPTH_CONV BETA_CONV
  THENC Rewrite.REWRITE_CONV [arithmeticTheory.ADD_CLAUSES]) tm;


(*---------------------------------------------------------------------------
 * Trivial wellfoundedness prover for combinations of wellfounded relations.
 *--------------------------------------------------------------------------*)

local fun BC_TAC th = 
        if (is_imp (#2 (Dsyntax.strip_forall (concl th))))
        then MATCH_ACCEPT_TAC th ORELSE MATCH_MP_TAC th
        else MATCH_ACCEPT_TAC th;
      open relationTheory prim_recTheory pairTheory
      val WFthms =  [WF_inv_image, WF_measure, WF_LESS, WF_Empty,
                     WF_PRED, WF_RPROD, WF_LEX, WF_TC]
in
fun WF_TAC thms = REPEAT (MAP_FIRST BC_TAC (thms@WFthms) ORELSE CONJ_TAC)
end;

val default_simps =
         [combinTheory.o_DEF,
          combinTheory.I_THM,
          prim_recTheory.measure_def, 
          relationTheory.inv_image_def, 
          pairTheory.LEX_DEF];

val ASM_ARITH_TAC = 
      REPEAT STRIP_TAC
        THEN REPEAT (POP_ASSUM 
               (fn th => if arithSimps.is_arith (concl th) 
                         then MP_TAC th else ALL_TAC))
        THEN numLib.ARITH_TAC;

fun TC_SIMP_TAC WFthl thl = 
   WF_TAC WFthl THEN 
   CONV_TAC (TC_SIMP_CONV (thl@default_simps)) THEN 
   TRY ASM_ARITH_TAC;


(*---------------------------------------------------------------------------
    Rquote is a quotation denoting the termination relation. 
 ---------------------------------------------------------------------------*)

fun PRIM_WF_REL_TAC defn Rquote WFthms simps g =
  (Defn.TC_INTRO_TAC defn 
    THEN Q.EXISTS_TAC Rquote
    THEN TC_SIMP_TAC WFthms simps) g;


fun WF_REL_TAC defn Rquote = PRIM_WF_REL_TAC defn Rquote [] default_simps;


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

local open prim_recTheory relationTheory
in
fun default_prover g =
 (CONV_TAC (TC_SIMP_CONV (WF_measure::WF_LESS::WF_Empty::default_simps))
   THEN ASM_ARITH_TAC) g
end;


local val term_prover = proveTotal default_prover
      open Defn
      fun try_proof defn Rcand = term_prover (set_reln defn Rcand)
      fun should_try_to_prove_termination defn = 
            not(null(tcs_of defn)) andalso null(params_of defn)
in
fun primDefine defn =
 let val defn' = 
       if should_try_to_prove_termination defn 
         then Lib.tryfind (try_proof defn) (guessR defn)
               handle HOL_ERR _ => (Lib.say (String.concat
               ["Unable to prove totality!\nUse \"Defn.Hol_defn\" to make ",
               "the definition,\nand \"Defn.tgoal <defn>\" to set up the ",
               "termination proof.\n"]);
             raise ERR "primDefine" "Unable to prove termination")
         else defn
 in 
    save_defn defn'; 
    eqns_of defn'
 end
end;


fun xDefine stem q = primDefine (Defn.Hol_defn stem q);


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
fun Define q =
   let val (tm,names) = Defn.parse_defn q
       val bindstem = mk_bindstem (ERR "Define" "") 
            "xDefine <alphanumeric-stem> <eqns-quotation>" names 
   in 
       primDefine (Defn.mk_defn bindstem tm)
   end               
end;

end;
