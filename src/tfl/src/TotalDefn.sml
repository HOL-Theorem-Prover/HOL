structure TotalDefn :> TotalDefn =
struct

open HolKernel Parse basicHol90Lib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
fun -- q x = Term q
fun == q x = Type q

open arithLib Let_conv NonRecSize;

type thm    = Thm.thm;
type conv   = Abbrev.conv
type tactic = Abbrev.tactic;
type proofs   = GoalstackPure.proofs
type defn   = Defn.defn;
type 'a quotation = 'a Portable.frag list

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
      |  _  => let val m = max lens 0
               in map (fill m) L
               end
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
val Zero = Term`0`;
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

local open Defn
in
fun try_proof def tac r =
   let val def' = set_reln def r
       val tcs = tcs_of def'
       val thm = prove(list_mk_conj tcs, tac)
       val thml = CONJUNCTS thm
    in
       elim_tcs def' thml
    end
fun proveTotal0 tac def =
  case guessR def
    of [] => def
     | cands => Lib.tryfind (try_proof def tac) cands
end;

(*---------------------------------------------------------------------------
      TC prover. Terribly terribly naive, but it still gets a lot.
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

val default_simps =
  [combinTheory.o_DEF,combinTheory.I_THM,prim_recTheory.measure_def, 
   relationTheory.inv_image_def, pairTheory.LEX_DEF];


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
  THEN REPEAT STRIP_TAC
  THEN REPEAT (POP_ASSUM (fn th =>
       if arithSimps.is_arith (concl th)
       then MP_TAC th else ALL_TAC))
  THEN CONV_TAC arithLib.ARITH_CONV) g
end;

val proveTotal = proveTotal0 default_prover;

val TC_SIMP_TAC = CONV_TAC (TC_SIMP_CONV []);

(*---------------------------------------------------------------------------
        Support for interactive termination proofs. Brought over
        from Defn.
 ---------------------------------------------------------------------------*)

val tgoal = Defn.tgoal
val tprove = Defn.tprove
val TC_INTRO_TAC = Defn.TC_INTRO_TAC


 (*---------------------------------------------------------------------------
  * Trivial wellfoundedness prover for combinations of wellfounded relations.
  *--------------------------------------------------------------------------*)

local fun BC_TAC th = 
        if (is_imp (#2 (Dsyntax.strip_forall (concl th))))
        then MATCH_ACCEPT_TAC th ORELSE MATCH_MP_TAC th
        else MATCH_ACCEPT_TAC th;
      open relationTheory prim_recTheory pairTheory listTheory
      val WFthms =  [WF_inv_image, WF_measure, WF_LESS, WF_Empty,
                     WF_PRED, WF_LIST_PRED, WF_RPROD, WF_LEX, WF_TC]
in
fun WF_TAC thms = REPEAT (MAP_FIRST BC_TAC (thms@WFthms) ORELSE CONJ_TAC)
end;

(*---------------------------------------------------------------------------
    Rquote is a quotation denoting the termination relation. 
 ---------------------------------------------------------------------------*)

fun PRIM_WF_REL_TAC defn Rquote WFthms simps g =
  (TC_INTRO_TAC defn 
    THEN Q.EXISTS_TAC Rquote
    THEN WF_TAC WFthms
    THEN CONV_TAC (TC_SIMP_CONV simps)) g;


fun WF_REL_TAC defn Rquote = PRIM_WF_REL_TAC defn Rquote [] default_simps;


(*---------------------------------------------------------------------------
       Definition principles that automatically attempt
       to prove termination. If the termination proof
       fails, the definition attempt fails.
 ---------------------------------------------------------------------------*)

val ind_suffix = ref "ind";
val def_suffix = ref "def";

fun atom_name tm = #Name(dest_var tm handle HOL_ERR _ => dest_const tm);


fun const_of th =
  let val hd_eqn = 
       snd(strip_imp(snd(strip_forall(hd(strip_conj(concl th))))))
  in
    fst(strip_comb(#lhs(dest_eq hd_eqn)))
  end;

fun constants_of defn =
  let val eqns = Defn.eqns_of defn
      val nest_eqns = case Defn.aux_defn defn
                       of NONE => [] 
                        | SOME nest => [Defn.eqns_of nest]
      val mut_eqns = case Defn.union_defn defn
                      of NONE => [] 
                       | SOME mut => 
                           Defn.eqns_of mut 
                            ::(case Defn.aux_defn mut
                                of NONE => []
                                 | SOME nest => [Defn.eqns_of nest])
      val alleqns = eqns::(nest_eqns@mut_eqns)
      val consts = map const_of alleqns
  in 
      consts
  end;


(*---------------------------------------------------------------------------
    xDefine bindstem ` ... ` operates as follows:

        1. It makes the definition, using Hol_fun.
        2. If the definition is not recursive or is
           primitive recursive, the defining equations are 
           stored under bindstem_def (and returned).
        3. Otherwise, we check to see if the definition
           is schematic. If so, the induction theorem is stored
           under bindstem_ind and the recursion equations are stored
           under bindstem_def.
        4. Otherwise, an attempt is made to prove termination. If this fails, 
           then xDefine fails (and cleans up after itself).
        5. Otherwise, the termination conditions are eliminated, and
           the induction theorem is stored under bindstem_ind and
           the recursion equations are stored under bindstem_def, before
           the recursion equations are returned.
 ---------------------------------------------------------------------------*)

fun xDefine bindstem qtm =
 let val defname = bindstem^"_"^ !def_suffix
     val indname = bindstem^"_"^ !ind_suffix
     val defn = Defn.Hol_defn bindstem qtm
                 handle e => (Lib.say "Unable to define function!\n"; raise e)
 in
   if Defn.abbrev defn orelse Defn.primrec defn 
   then (Theory.set_MLname bindstem defname;
         Lib.say ("Definition stored under "^Lib.quote defname^".\n");
         Defn.eqns_of defn)
   else
   if not(null(Defn.parameters defn)) 
   then let val ind = Option.valOf (Defn.ind_of defn)
        in
          Lib.say (String.concat
           ["Schematic definition.\nEquations stored under ",
            Lib.quote defname, ".\nInduction stored under ",
            Lib.quote indname, ".\n"]);
          save_thm(indname, ind);
          save_thm(defname, Defn.eqns_of defn)
        end
   else 
    let val defn' = proveTotal defn handle HOL_ERR _ => defn
    in 
       if null(Defn.tcs_of defn')
       then let val ind = Option.valOf (Defn.ind_of defn')
            in
               Lib.say (String.concat
                ["Equations stored under ",    Lib.quote defname,
                 ".\nInduction stored under ", Lib.quote indname, ".\n"]);
               save_thm(indname, ind);
               save_thm(defname, Defn.eqns_of defn')
            end
       else (Lib.say (String.concat
               ["Unable to prove totality!\nUse \"Defn.Hol_defn\" to make ",
               "the definition,\nand \"Defn.tgoal <defn>\" to set up the ",
               "termination proof.\n"]);
             mapfilter delete_const (map atom_name (constants_of defn));
             Theory.scrub();
             raise ERR "xDefine" "Unable to prove termination")
    end
 end;


(*---------------------------------------------------------------------------
    Define ` ... ` creates a bindstem for the definition to be made, 
    then calls xDefine. In the case of a single-recursive function
    with an alphanumeric name, everything is simple. If the name
    is symbolic, then the bindstem is generated from "symbol_". If 
    the definition is mutually recursive, then the name is generated
    from "mutrec" in a bizarre fashion.
 ---------------------------------------------------------------------------*)

local val mut_namesl = ref []:string list list ref
      val sort = Lib.sort (curry (op= :string*string->bool))
      fun index_of x [] i = NONE
        | index_of x (y::rst) i = if x=y then SOME i else index_of x rst (i+1)
      fun inc_mutl names =
        let val names' = sort names
        in case index_of names' (!mut_namesl) 0
            of NONE => (mut_namesl := !mut_namesl@[names']; 
                        Option.valOf(index_of names' (!mut_namesl) 0))
             | SOME i => i
        end
      val symbr = ref 0
      fun gen_symbolic_name() = 
         let val s = "symbol_"^Lib.int_to_string (!symbr)
         in Portable.inc symbr; s
         end
in
fun Define ql =
 let val qtm = Defn.norm_quote ql
     val names = Defn.preview qtm
     val bindstem =
        case names
         of []  => raise ERR "Define" "Can't find name of function"
          | [x] => if Lexis.ok_identifier x then x
                   else let val name = gen_symbolic_name()
                        in
                          Lib.say (String.concat
                             ["Non-alphanumeric being defined.\n",
                              "Invented stem for binding(s): ", 
                              Lib.quote name,".\n"]);
                          name
                        end
          |  _  =>
             let val name = "mutrec"^Lib.int_to_string(inc_mutl names)
             in 
               Lib.say (String.concat
                  ["Mutually recursive definition.\n",
                   "Invented stem for bindings is ", 
                   Lib.quote name,".\n"]);
               name
             end
 in 
    xDefine bindstem qtm
 end               
end;

end;
