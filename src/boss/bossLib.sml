(*---------------------------------------------------------------------------*
 * The "boss" library. This provides a collection of proof routines.         *
 * They provide                                                              *
 *                                                                           *
 *    1. Automatic maintenance of the usual products of a datatype           *
 *       definition.                                                         *
 *                                                                           *
 *    2. Some tools that work using that information.                        *
 *                                                                           *
 *    3. Some basic automation support.                                      *
 *                                                                           *
 *---------------------------------------------------------------------------*)

structure bossLib :> bossLib =
struct

open HolKernel Parse basicHol90Lib;

  type term = Term.term
  type fixity = Parse.fixity
  type thm = Thm.thm
  type tactic = Abbrev.tactic
  type simpset = simpLib.simpset
  type 'a quotation = 'a Portable_General.frag list

infix THEN THENL ORELSE |->;
infixr -->;

fun BOSS_ERR func mesg =
     HOL_ERR{origin_structure = "bossLib",
             origin_function = func,
             message = mesg};

(*---------------------------------------------------------------------------*
 * Datatype definition.                                                      *
 *---------------------------------------------------------------------------*)

fun type_rws tyn = TypeBase.simpls_of (valOf (TypeBase.read tyn));

val Hol_datatype = Datatype.Hol_datatype;


(*---------------------------------------------------------------------------*
 * Non-datatype congruence rules need to be installed by hand. Congruence    *
 * rules derived from datatype definitions get handled automatically.        *
 *---------------------------------------------------------------------------*)

val _ = Context.write_context [Thms.LET_CONG, Thms.COND_CONG];


(*---------------------------------------------------------------------------*
 * Mildly altered STRUCT_CASES_TAC, so that it does a SUBST_ALL_TAC instead  *
 * of a SUBST1_TAC.                                                          *
 *---------------------------------------------------------------------------*)
val VAR_INTRO_TAC = REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC;
val TERM_INTRO_TAC =
 REPEAT_TCL STRIP_THM_THEN
     (fn th => TRY (SUBST_ALL_TAC th) THEN ASSUME_TAC th);


fun FREEUP [] g = ALL_TAC g
  | FREEUP W (g as (_,w)) =
  let val (V,_) = strip_forall w
      val others = set_diff V W
  in
    (REPEAT GEN_TAC THEN MAP_EVERY ID_SPEC_TAC (rev others)) g
  end;

(*---------------------------------------------------------------------------*
 * Do case analysis on given term. The quotation is parsed into a term M that*
 * must match a subterm in the body (or the assumptions). If M is a variable,*
 * then the match of the names must be exact. Once the term to split over is *
 * known, its type and the associated facts are obtained and used to do the  *
 * split with. If M is a variable, it might be quantified in the goal. If so,*
 * we try to unquantify it so that the case split has meaning.               *
 *                                                                           *
 * It can happen that the given term is not found anywhere in the goal. If   *
 * the term is boolean, we do a case-split on whether it is true or false.   *
 *---------------------------------------------------------------------------*)
datatype category = Free of term
                  | Bound of term list * term
                  | Alien of term

fun cat_tyof (Free M)      = type_of M
  | cat_tyof (Bound (_,M)) = type_of M
  | cat_tyof (Alien M)     = type_of M

fun name_eq s M = ((s = #Name(dest_var M)) handle HOL_ERR _ => false)
fun tm_free_eq M N P =
   (aconv N P andalso free_in N M) orelse raise BOSS_ERR"" ""

fun find_subterm tm (asl,w) =
   if (is_var tm)
   then let val name = #Name(dest_var tm)
        in
          Free (Lib.first(name_eq name) (free_varsl (w::asl)))
          handle HOL_ERR _
          => Bound(let val (V,_) = strip_forall w
                       val v = Lib.first (name_eq name) V
                   in
                     ([v], v)
                   end)
        end
   else Free (tryfind(fn x => find_term (can(tm_free_eq x tm)) x) (w::asl))
        handle HOL_ERR _
        => Bound(let val (V,body) = strip_forall w
                     val M = find_term (can (tm_free_eq body tm)) body
                 in
                    (intersect (free_vars M) V, M)
                 end)
                 handle HOL_ERR _ => Alien tm;

fun Cases_on qtm g =
 let val tm = Lib.with_flag
                 (Globals.notify_on_tyvar_guess,false) Parse.Term qtm
     val st = find_subterm tm g
     val {Tyop, ...} = Type.dest_type(cat_tyof st)
 in case TypeBase.read Tyop
    of SOME facts =>
        let val thm = TypeBase.nchotomy_of facts
        in case st
           of Free M =>
               if (is_var M) then VAR_INTRO_TAC (ISPEC M thm) g else
               if (Tyop="bool") then ASM_CASES_TAC M g
               else TERM_INTRO_TAC (ISPEC M thm) g
            | Bound(V,M) => (FREEUP V THEN VAR_INTRO_TAC (ISPEC M thm)) g
            | Alien M    => if (Tyop="bool") then ASM_CASES_TAC M g
                            else TERM_INTRO_TAC (ISPEC M thm) g
        end
     | NONE => raise BOSS_ERR "Cases_on"
                         ("No cases theorem found for type: "^Lib.quote Tyop)
 end
 handle e as HOL_ERR _ => Exception.Raise e;


fun primInduct st ind_tac (g as (asl,c)) =
 let fun ind_non_var V M =
       let val Mfrees = free_vars M
           fun has_vars tm = not(null_intersection (free_vars tm) Mfrees)
           val tms = filter has_vars asl
           val newvar = variant (free_varsl (c::asl))
                                (mk_var{Name="v",Ty=type_of M})
           val tm = mk_exists{Bvar=newvar, Body=mk_eq{lhs=newvar, rhs=M}}
           val th = EXISTS(tm,M) (REFL M)
        in
          FREEUP V
            THEN MAP_EVERY UNDISCH_TAC tms
            THEN CHOOSE_THEN MP_TAC th
            THEN MAP_EVERY ID_SPEC_TAC Mfrees
            THEN ID_SPEC_TAC newvar
            THEN ind_tac
        end
 in case st
     of Free M =>
         if is_var M
         then let val tms = filter (free_in M) asl
              in (MAP_EVERY UNDISCH_TAC tms THEN ID_SPEC_TAC M THEN ind_tac) g
              end
         else ind_non_var [] M g
      | Bound(V,M) =>
         if is_var M then (FREEUP V THEN ID_SPEC_TAC M THEN ind_tac) g
         else ind_non_var V M g
      | Alien M =>
         if is_var M then raise BOSS_ERR "primInduct" "Alien variable"
         else ind_non_var (free_vars M) M g
 end
 handle e as HOL_ERR _ => Exception.Raise e;


fun Induct_on qtm g =
 let val tm = Lib.with_flag
                 (Globals.notify_on_tyvar_guess,false) Parse.Term qtm
     val st = find_subterm tm g
     val {Tyop, ...} = Type.dest_type(cat_tyof st)
       handle HOL_ERR _ =>
         raise BOSS_ERR "Induct_on"
           "No induction theorems available for variable types"
 in case TypeBase.read Tyop
     of SOME facts =>
        let val thm = TypeBase.induction_of facts
            val ind_tac = INDUCT_THEN thm ASSUME_TAC
        in primInduct st ind_tac g
        end
      | NONE => raise BOSS_ERR "Induct_on"
                    ("No induction theorem found for type: "^Lib.quote Tyop)
 end;

fun completeInduct_on qtm g =
 let val tm = Lib.with_flag
                 (Globals.notify_on_tyvar_guess,false) Parse.Term qtm
     val st = find_subterm tm g
     val ind_tac = INDUCT_THEN arithmeticTheory.COMPLETE_INDUCTION ASSUME_TAC
 in
     primInduct st ind_tac g
 end;

(*---------------------------------------------------------------------------
    Invoked e.g. measureInduct_on `LENGTH L` or
                 measureInduct_on `(\(x,w). x+w) (M,N)`
 ---------------------------------------------------------------------------*)

local open WFTheory primWFTheory
      val mvar = mk_var{Name="m", Ty=Type`:'a -> num`}
      val measure_m = mk_comb{Rator= #const(const_decl"measure"),Rand=mvar}
      val ind_thm0 = GEN mvar
          (BETA_RULE
             (REWRITE_RULE[WF_measure,measure_def,inv_image_def]
                 (MATCH_MP (SPEC measure_m WF_INDUCTION_THM)
                         (SPEC_ALL WF_measure))))
in
fun measureInduct_on q g =
 let val tm = Lib.with_flag
                 (Globals.notify_on_tyvar_guess,false) Parse.Term q
     val {Rator=meas, Rand=arg} = dest_comb tm
     val (d,r) = dom_rng (type_of meas)  (* r should be num *)
     val st = find_subterm arg g
     val st_type = cat_tyof st
     val meas' = inst (match_type d st_type) meas
     val ind_thm1 = INST_TYPE [Type`:'a` |-> st_type] ind_thm0
     val ind_thm2 = CONV_RULE (DEPTH_CONV Let_conv.GEN_BETA_CONV)
                              (SPEC meas' ind_thm1)
     val ind_tac = INDUCT_THEN ind_thm2 ASSUME_TAC
 in
     primInduct st ind_tac g
 end
end;



fun Cases (g as (_,w)) =
  let val {Bvar,...} = dest_forall w handle HOL_ERR _
                       => raise BOSS_ERR "Cases" "not a forall"
      val {Name,...} = dest_var Bvar
  in
    Cases_on [QUOTE Name] g
  end;


fun Induct (g as (_,w)) =
 let val {Bvar, ...} = Dsyntax.dest_forall w handle HOL_ERR _
                       => raise BOSS_ERR "Induct" "not a forall"
      val {Name,...} = dest_var Bvar
 in
   Induct_on [QUOTE Name] g
 end;

(*---------------------------------------------------------------------------*
 * Defining functions.                                                       *
 *---------------------------------------------------------------------------*)

fun func_of_cond_eqn tm =
    #1(strip_comb(#lhs(dest_eq(#2 (strip_forall(#2(strip_imp tm)))))));

val prod_tyl =
  end_itlist(fn ty1 => fn ty2 => mk_type{Tyop="prod",Args=[ty1,ty2]});

fun variants FV vlist = rev(fst
  (rev_itlist (fn v => fn (V,W) => let val v' = variant W v
                                   in (v'::V, v'::W)
                                   end) vlist ([],FV)));

fun drop [] x = x
  | drop (_::t) (_::rst) = drop t rst
  | drop _ _ = raise BOSS_ERR "drop" "";

(*---------------------------------------------------------------------------
 * On entry to this, we know that f is curried, i.e., of type
 *
 *    f : ty1 -> ... -> tyn -> rangety
 *
 *---------------------------------------------------------------------------*)

fun pairf (f,argtys,range_ty,eqs0) =
 let val unc_argty = prod_tyl argtys
     val fname = #Name (dest_var f handle HOL_ERR _ => dest_const f)
     val f' = Lib.with_flag (Globals.priming, SOME"")
              mk_primed_var
                {Name=if Lexis.ok_identifier fname
                      then "tupled_"^fname else "tupled",
                 Ty = unc_argty --> range_ty}
     fun rebuild tm =
      case (dest_term tm)
      of COMB _ =>
         let val (g,args) = strip_comb tm
             val args' = map rebuild args
         in if (g=f)
            then if (length args < length argtys)  (* partial application *)
                 then let val newvars = map (fn ty => mk_var{Name="a", Ty=ty})
                                            (drop args argtys)
                          val newvars' = variants (free_varsl args') newvars
                      in list_mk_abs(newvars',
                          mk_comb{Rator=f',Rand=list_mk_pair(args' @newvars')})
                      end
                 else mk_comb{Rator=f', Rand=list_mk_pair args'}
            else list_mk_comb(g,args')
         end
       | LAMB{Bvar,Body} => mk_abs{Bvar=Bvar, Body=rebuild Body}
       | _ => tm
   in
     rebuild eqs0
   end;

fun function name eqs0 =
 let val eqslist      = strip_conj eqs0
     val lhs1         = #lhs(dest_eq(hd eqslist))
     val (forig,args) = strip_comb lhs1
     val argtys       = map type_of args
     val unc_argty    = prod_tyl argtys
     val range_ty     = type_of lhs1
     val curried      = not(length args = 1)
     val unc_eqs      = if not curried then eqs0
                        else pairf(forig,argtys,range_ty,eqs0)
     val unc_name     = if not curried then name else ("tupled_"^name)
     val R            = map (#rhs o dest_eq) eqslist
     val recursive    = exists (can (find_term (aconv forig))) R
     val facts        = TypeBase.theTypeBase()
     val {rules,R,full_pats_TCs,...} = Tfl.lazyR_def facts unc_name unc_eqs
     val f = func_of_cond_eqn
                (concl(CONJUNCT1 rules handle HOL_ERR _ => rules))
     val newvars' = variants [forig]
                     (map (fn ty => mk_var{Name="x", Ty=ty}) argtys)
     (* Pass back the definition and the new rules. If the original wasn't
        curried, do nothing -- just pass back a pair of unchanged rules. *)
     fun def () =
        if curried then
           let val def = new_definition
                   (name,
                    mk_eq{lhs=list_mk_comb (forig, newvars'),
                          rhs=list_mk_comb(f, [list_mk_pair newvars'])})
           in
             (def,Rewrite.PURE_REWRITE_RULE[GSYM def] rules)
           end
        else (rules,rules)
in
  if recursive  (* then add induction scheme *)
  then let val induction = Tfl.mk_induction facts f R full_pats_TCs
       in if not curried
          then CONJ (snd (def())) induction
         else let val (def,rules') = def()
                  val P = #Bvar(dest_forall(concl induction))
                  val Qty = itlist (curry Type.-->) argtys Type.bool
                  val Q = mk_primed_var{Name = "P", Ty = Qty}
                  val tm = mk_pabs{varstruct=list_mk_pair newvars',
                                   body=list_mk_comb(Q,newvars')}
                  val ind1 = SPEC tm
                      (Rewrite.PURE_REWRITE_RULE [GSYM def] induction)
                 val ind2 = CONV_RULE(DEPTH_CONV Let_conv.GEN_BETA_CONV) ind1
              in
               CONJ rules' (GEN Q ind2)
              end
       end
   else snd(def())
 end


(*---------------------------------------------------------------------------*
 * A preliminary attempt to have a single entrypoint for definitions. It     *
 * tries to make a basic definition or a prim. rec. definition. If those     *
 * fail, it tries a TFL definition. It will try to solve trivial termination *
 * conditions, but non-trivial ones get put on the assumptions for the user  *
 * to solve. Nested recursions are not yet handled.                          *
 *---------------------------------------------------------------------------*)

fun string_variant slist =
   let fun pass str = if (mem str slist) then pass (str^"'") else str
   in pass
   end;

fun is_constructor tm = not (is_var tm orelse is_pair tm);

local fun basic_defn (fname,tm) =
        let fun D fix = new_gen_definition(fname, tm, fix)
        in D end
      fun dest_atom ac = dest_const ac handle _ => dest_var ac
in
fun primDefine eqs0 fixity name =
 let val eqs = strip_conj eqs0
     val (f,args) = strip_comb(#lhs(dest_eq(#2 (strip_forall(hd eqs)))))
     val nm = #Name(dest_atom f)
 in
   (if Lib.exists is_constructor args
    then case (TypeBase.read (#Tyop(Type.dest_type
                  (type_of(first is_constructor args)))))
          of NONE => raise BOSS_ERR "define"
                      "unexpected lhs in proposed definition"
           | SOME facts => new_recursive_definition
                                {name=name,def=eqs0,fixity=fixity,
                                 rec_axiom = TypeBase.axiom_of facts}
    else basic_defn (name,eqs0) fixity)
    handle HOL_ERR _
    =>  (* resort to TFL *)
      let val thm = function name eqs0
                    handle e as HOL_ERR _
                    => (Lib.say"Definition failed.\n"; raise e)
          val thm' = case (hyp thm)
               of [WF_R] =>   (* non-recursive defn *)
                  (case (strip_comb WF_R)
                    of (WF,[R]) =>
                      let val Rty = type_of R
                          val theta = [Type.alpha |-> hd(#Args(dest_type Rty))]
                          val Empty_thm = INST_TYPE theta primWFTheory.WF_Empty
                      in MATCH_MP (DISCH_ALL thm) Empty_thm
                      end
                    | _ => raise BOSS_ERR"primDefine" "Unexpected hyp. term")
               | [] => raise BOSS_ERR"primDefine" "Empty hyp. after use of TFL"
               | _  => Halts.halts Halts.prover thm
                        handle HOL_ERR _ => (Lib.mesg true (Lib.quote nm
                         ^" defined: side-conditions remain in hypotheses");
                         thm)
          val _ = set_fixity nm fixity
             (* val away = map fst (theorems()@definitions()@axioms())
             val save_name = string_variant away (name^"_thm") *)
          val save_name = name^"_thm"
      in
         save_thm(save_name,thm')
      end
 end
end;


(*---------------------------------------------------------------------------*
 * Find the name of a to-be-defined constant from a quotation. Or at         *
 * least try to.                                                             *
 *---------------------------------------------------------------------------*)

fun alphabetic c   = Lexis.in_class(Lexis.alphabet,      Char.ord c);
fun alphanumeric c = Lexis.in_class(Lexis.alphanumerics, Char.ord c);
fun symbolic c     = Lexis.in_class(Lexis.hol_symbols,   Char.ord c);
fun starts_ident c = alphanumeric c orelse symbolic c ;

fun grab_first_ident s =
 let val ss0 = Substring.dropl (not o starts_ident) (Substring.all s)
     val ident_ss =
       case Substring.getc ss0
        of NONE => raise BOSS_ERR "grab_first_ident" "can't find an ident"
         | SOME(c,_) =>
             if (symbolic c)
             then Substring.takel symbolic ss0
             else if (alphabetic c)
                  then Substring.takel alphanumeric ss0
                  else raise BOSS_ERR "grab_first_ident"
                                      "can't find an ident.1"
 in
   Substring.string ident_ss
 end;

fun head tm =
  let val a = fst(strip_comb(lhs
                 (snd(strip_forall(Lib.trye hd (strip_conj tm))))))
  in
    #Name(dest_var a handle HOL_ERR _ => dest_const a)
  end;


(*---------------------------------------------------------------------------*
 * What to use when making defn.                                             *
 *---------------------------------------------------------------------------*)
val Define_suffix = ref (fn s => s^"_def");

(*---------------------------------------------------------------------------*
 * Attempt to find and hide the constant being defined before calling        *
 * primDefine.                                                               *
 *---------------------------------------------------------------------------*)
fun Define qtm =
 let fun def (qtm as [QUOTE s]) =
           let val nm = grab_first_ident s
               val dnm = "$"^nm
               val _ = List.app Parse.hide [nm,dnm]
               val eqs0 = Parse.Term qtm
               val _ = List.app Parse.reveal [nm,dnm]
           in
             primDefine eqs0 Prefix (!Define_suffix nm)
           end
       | def qtm =
           let val tm = Parse.Term qtm
           in
             primDefine tm Prefix (!Define_suffix (head tm))
           end
 in
   Lib.try def qtm
 end


(*---------------------------------------------------------------------------
 * Naughty! I am overwriting the record for pairs, so that the TFL rewriter
 * will use "pair_case" as a case construct, rather than UNCURRY_DEF. This
 * (apparently) solves a deeply buried problem in TC extraction involving
 * paired beta-reduction. I don't recall the details, but there must be
 * some sort of critical pair. In the end, it was easier to invent a
 * new constant.
 *
 * Here we also finally fill in the "size" entries in theTypeBase for
 * some types that get built before numbers.
 *---------------------------------------------------------------------------*)

local
  val prod_info =
         TypeBase.gen_tyinfo
             {ax = pairTheory.pair_Axiom,
              case_def = pairTheory.pair_case_thm,
              distinct = NONE,
              one_one = SOME pairTheory.CLOSED_PAIR_EQ}
  val prod_size_info =
       (Parse.Term`\f g. UNCURRY(\(x:'a) (y:'b). f x + g y)`,
        pairTheory.UNCURRY_DEF)
  val prod_info' = TypeBase.put_size prod_size_info prod_info

  val bool_info = Option.valOf(TypeBase.read "bool")
  val bool_case_rw = prove(Term`!x y. bool_case x x y = (x:'a)`,
    REPEAT GEN_TAC
      THEN BOOL_CASES_TAC (Term`y:bool`)
     THEN Rewrite.ASM_REWRITE_TAC[boolTheory.bool_case_DEF]);
  val bool_size_info = (Term`bool_case 0 0`, bool_case_rw)
  val bool_info' = TypeBase.put_size bool_size_info bool_info

  val option_info = Option.valOf(TypeBase.read "option")
  val option_size_info =
       (Parse.Term`\f. option_case 0 (\x:'a. SUC (f x))`,
        optionTheory.option_case_def)
  val option_info' = TypeBase.put_size option_size_info option_info

in
   val _ = TypeBase.write bool_info'
   val _ = TypeBase.write prod_info'
   val _ = TypeBase.write option_info'
end


(*---------------------------------------------------------------------------
                               Proof
 ---------------------------------------------------------------------------*)

fun PROVE thl tm = Tactical.prove (Parse.Term tm, mesonLib.MESON_TAC thl);
val PROVE_TAC    = mesonLib.ASM_MESON_TAC;

val DECIDE     = decisionLib.DECIDE o Parse.Term
val DECIDE_TAC = decisionLib.DECIDE_TAC

infix 4  &&;
fun (ss && thl) = simpLib.++(ss,simpLib.rewrites thl);

val empty_ss = simpLib.empty_ss;

val bool_ss  = (simpLib.++
                 (simpLib.++(simpLib.++(boolSimps.bool_ss,boolSimps.NOT_ss),
                             pairSimps.PAIR_ss), UnwindSimps.UNWIND_ss))
               && let open optionTheory
                  in [option_case_def,THE_DEF, option_APPLY_DEF,
                      SOME_11, NOT_NONE_SOME, NOT_SOME_NONE] end;

val arith_ss = simpLib.++(bool_ss, arithSimps.ARITH_ss)

val list_ss  = simpLib.++(arith_ss, listSimps.list_ss)

(*---------------------------------------------------------------------------*
 * When invoked, we know that th is an equality, at least one side of which  *
 * is a variable.                                                            *
 *---------------------------------------------------------------------------*)
fun orient th =
  let val c = concl th
      val {lhs,rhs} = dest_eq c
  in if (is_var lhs)
     then if (is_var rhs)
          then if term_lt lhs rhs (* both vars, rewrite to textually smaller *)
               then SYM th
               else th
          else th
     else SYM th
  end;

fun VSUBST_TAC tm = UNDISCH_TAC tm THEN DISCH_THEN (SUBST_ALL_TAC o orient);

fun var_eq tm =
   let val {lhs,rhs} = dest_eq tm
   in
       aconv lhs rhs
     orelse
       (is_var lhs andalso not (mem lhs (free_vars rhs)))
     orelse
       (is_var rhs andalso not (mem rhs (free_vars lhs)))
   end
   handle _ => false;


fun grab P f v =
  let fun grb [] = v
        | grb (h::t) = if (P h) then f h else grb t
  in grb
  end;

fun ASSUM_TAC f P = W (fn (asl,_) => grab P f NO_TAC asl)

fun ASSUMS_TAC f P = W (fn (asl,_) =>
  case filter P asl
    of []     => NO_TAC
     | assums => MAP_EVERY f assums);

fun CONCL_TAC f P = W (fn (_,c) => if (P c) then f else NO_TAC);

fun constructed constr_set tm =
  let val {lhs,rhs} = dest_eq tm
  in
  (aconv lhs rhs)
     orelse
   let val maybe1 = #Name(dest_const(fst(strip_comb lhs)))
       val maybe2 = #Name(dest_const(fst(strip_comb rhs)))
   in Binaryset.member(constr_set,maybe1)
         andalso
      Binaryset.member(constr_set,maybe2)
   end
  end
  handle _ => false;

fun LIFT_SIMP ss tm =
   UNDISCH_TAC tm THEN
   DISCH_THEN (STRIP_ASSUME_TAC o simpLib.SIMP_RULE ss []);


local
fun DTHEN (ttac:Abbrev.thm_tactic) :tactic = fn (asl,w) =>
     if (is_neg w) then raise BOSS_ERR "DTHEN" "negation"
     else let val {ant,conseq} = Dsyntax.dest_imp w
              val (gl,prf) = ttac (Thm.ASSUME ant) (asl,conseq)
          in (gl, Thm.DISCH ant o prf)
          end
in
 val BOSS_STRIP_TAC = Tactical.FIRST [GEN_TAC,CONJ_TAC, DTHEN STRIP_ASSUME_TAC]
end;

fun add_constr tyinfo set =
   let open TypeBase
       val C = constructors_of tyinfo
   in Binaryset.addList (set, map (#Name o dest_const) C)
   end;

fun add_simpls tyinfo ss = ss && TypeBase.simpls_of tyinfo;

local val constr_set0 = Binaryset.empty String.compare
in
fun STP_TAC ss finisher =
  let open TypeBase
      val tyl = listItems (theTypeBase())
      val constr_set = rev_itlist add_constr tyl constr_set0
      val has_constr_eqn = Lib.can (find_term (constructed constr_set))
      val ss' = rev_itlist add_simpls tyl ss
      val ASM_SIMP = simpLib.ASM_SIMP_TAC ss' []
  in
    REPEAT (GEN_TAC ORELSE CONJ_TAC)
     THEN REPEAT (ASSUM_TAC VSUBST_TAC var_eq)
     THEN ASM_SIMP
     THEN TRY (COND_CASES_TAC THEN REPEAT COND_CASES_TAC THEN ASM_SIMP)
     THEN REPEAT BOSS_STRIP_TAC
     THEN REPEAT (CHANGED_TAC
            (ASSUM_TAC VSUBST_TAC var_eq
               ORELSE ASSUMS_TAC (LIFT_SIMP ss') has_constr_eqn
               ORELSE CONCL_TAC ASM_SIMP has_constr_eqn))
     THEN TRY finisher
  end
end;

fun RW_TAC ss thl = STP_TAC (ss && thl) NO_TAC
fun ZAP_TAC ss thl =
   STP_TAC ss (tautLib.TAUT_TAC ORELSE DECIDE_TAC
               ORELSE mesonLib.GEN_MESON_TAC 0 12 1 thl);

(*---------------------------------------------------------------------------*
 * A simple aid to reasoning by contradiction.                               *
 *---------------------------------------------------------------------------*)

fun SPOSE_NOT_THEN ttac =
  CCONTR_TAC THEN POP_ASSUM (fn th => ttac (simpLib.SIMP_RULE bool_ss [] th));

(*---------------------------------------------------------------------------
     Assertional style reasoning
 ---------------------------------------------------------------------------*)

(* First we need a variant on THEN. *)
fun mapshape [] _ _ =  []
  | mapshape (n::nums) (f::funcs) all_args =
     let val (fargs,rst) = split_after n all_args
     in
      f fargs :: mapshape nums funcs rst
     end
  | mapshape _ _ _ = raise BOSS_ERR "mapshape" "irregular lists";

fun THENF (tac1:tactic,tac2:tactic,tac3:tactic) g =
 case (tac1 g)
  of (h::rst, p) =>
      let val (gl0,p0) = tac2 h
          val (gln,pn) = unzip (map tac3 rst)
          val gll = gl0 @ flatten gln
      in
        (gll, p o mapshape (length gl0::map length gln) (p0::pn))
      end
   | x => x;

infix 8 by;

fun (q by tac) =
  THENF (SUBGOAL_THEN (Term q) STRIP_ASSUME_TAC, tac, ALL_TAC)
  handle e as HOL_ERR _ => raise BOSS_ERR "by" "";

end;
