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
  type defn = Defn.defn
  type 'a quotation = 'a Portable.frag list

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


(*---------------------------------------------------------------------------
      Function definitions.
 ---------------------------------------------------------------------------*)

         
(*---------------------------------------------------------------------------*
 * Try to find the names of to-be-defined constants from a quotation.        *
 * First, parse into type "parse_term", then look for names on the lhs       *
 * of the definition.                                                        *
 *---------------------------------------------------------------------------*)

local open parse_term
in
fun dest_binop str =
  let fun dest (COMB(COMB(VAR s, l),r)) 
           = if s=str then (l,r) 
             else raise BOSS_ERR "dest_binop" ("Expected a "^Lib.quote str)
        | dest  _ = raise BOSS_ERR "dest_binop"  ""
  in dest end
fun dest_binder str =
  let fun dest (COMB(VAR s, ABS p)) 
           = if s=str then p
             else raise BOSS_ERR "dest_binder" ("Expected a "^Lib.quote str)
        | dest  _ = raise BOSS_ERR "dest_binder"  ""
  in dest end
fun ptm_dest_conj ptm   = dest_binop  "/\\" ptm
fun ptm_dest_eq ptm     = dest_binop  "=" ptm
fun ptm_dest_forall ptm = dest_binder "!" ptm

fun ptm_dest_var(VAR s) = s
  | ptm_dest_var _ =  raise BOSS_ERR "ptm_dest_comb" "Expected a VAR"

fun ptm_dest_comb (COMB(l,r)) = (l,r)
  | ptm_dest_comb   _ = raise BOSS_ERR "ptm_dest_comb" "Expected a COMB"
end;

fun ptm_is_eq tm = Lib.can ptm_dest_eq tm;


fun ptm_strip dest =
  let fun strip ptm =
       let val (l,r) = dest ptm 
       in l::strip r
       end handle HOL_ERR _ => [ptm];
  in strip
  end;

fun ptm_strip_conj ptm = ptm_strip ptm_dest_conj ptm;

fun ptm_strip_comb ptm =
   let fun strip ptm A =
         let val (l,r) = ptm_dest_comb ptm 
         in strip l (r::A)
         end handle HOL_ERR _ => (ptm,A)
  in strip ptm []
  end;


fun ptm_strip_binder dest =
  let fun strip ptm =
       let val (l,r) = dest ptm 
           val (L,M) = strip r
       in (l::L,M)
       end handle HOL_ERR _ => ([],ptm)
  in strip
  end;
fun ptm_strip_forall ptm = ptm_strip_binder ptm_dest_forall ptm;


fun dollar s = "$"^s;
fun drop_dollar s =
   (if String.sub(s,0) = #"$"
    then String.substring(s,1,String.size s)
    else s)
  handle _ => raise BOSS_ERR "drop_dollar" "unexpected string"

fun dest_atom tm =
  #Name(dest_var tm handle HOL_ERR _ => dest_const tm);

fun preview qthing =
 let fun preev (q as [QUOTE _]) =
         let val ptm = Parse.parse_preTerm q
             val eqs = ptm_strip_conj ptm
             val L = map (fst o ptm_dest_eq o snd o ptm_strip_forall) eqs
         in
           map (ptm_dest_var o fst o ptm_strip_comb) L
         end
       | preev qtm =
          let val tm = Parse.Term qtm
              val eqs = strip_conj tm
              open Psyntax
              val L = map (fst o dest_eq o snd o strip_forall) eqs
          in
            map (dest_atom o fst o strip_comb) L
          end
 in 
    mk_set (map drop_dollar (preev qthing))
     handle HOL_ERR _ 
     => raise BOSS_ERR "preview" 
             "unable to find name of function(s) to be defined"
end;


fun Hol_fun bindstem (qtm as [QUOTE _]) =
     let val names = preview qtm
         val allnames = map dollar names @ names
         val _ = List.app Parse.hide allnames
         val eqs = Parse.Term qtm 
                    handle e => (List.app Parse.reveal allnames; raise e)
         val _ = List.app Parse.reveal allnames
         val defn = Defn.define bindstem eqs
     in 
        Halts.proveTotal defn
     end 
  | Hol_fun bindstem qtm = 
      Halts.proveTotal (Defn.define bindstem (Parse.Term qtm));


(*---------------------------------------------------------------------------
    Define ` ... ` operates as follows:

        1. It creates a bindstem for the definition to be made.
        2. It makes the definition, using Hol_fun.
        3. It attempts to prove termination. If this fails, then
           Define fails.
        4. Otherwise, if the definition is not recursive or is
           primitive recursive, the defining equations alone are returned.
        5. Else, the definition is not a trivial recursion, and the
           following steps are made:

                 5a. The induction theorem is stored under bindname_ind
                 5b. The recursion equations are stored under bindname

           Then the recursion equations are returned to the user.
 ---------------------------------------------------------------------------*)

fun Define qtm = 
 let val bindstem =
       case preview qtm
        of []    => raise BOSS_ERR "Define" "Can't find name of function"
         | [x]   => if Lexis.ok_identifier x then x 
                    else #Name(dest_var
                            (Lib.with_flag(Globals.priming,SOME"")
                                mk_primed_var{Name=x,Ty=bool}))
         | names => #Name(dest_var
                      (Lib.with_flag(Globals.priming,SOME"")
                                mk_primed_var{Name="mutual",Ty=bool}))
     val defn = Hol_fun bindstem qtm
 in
   case Defn.tcs_of defn
    of [] => if (Defn.nonrec defn orelse Defn.primrec defn)
             then Defn.eqns_of defn
             else let val ind = Option.valOf (Defn.ind_of defn)
                  in 
                     save_thm(bindstem^"_ind", ind); 
                     save_thm(bindstem^"_eqns", Defn.eqns_of defn)
                  end
     | _  => raise BOSS_ERR "Define" "Unable to prove termination"
 end;




(*---------------------------------------------------------------------------
         High level interactive operations
 ---------------------------------------------------------------------------*)

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

local open relationTheory prim_recTheory
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
     val ind_thm1 = INST_TYPE [Type.alpha |-> st_type] ind_thm0
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




(*---------------------------------------------------------------------------
                          Proof Automation
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
  in if is_var lhs
     then if is_var rhs
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


local fun DTHEN (ttac:Abbrev.thm_tactic) :tactic = fn (asl,w) =>
        if (is_neg w) then raise BOSS_ERR "DTHEN" "negation"
        else let val {ant,conseq} = Dsyntax.dest_imp w
                 val (gl,prf) = ttac (Thm.ASSUME ant) (asl,conseq)
             in (gl, Thm.DISCH ant o prf)
             end
in
val BOSS_STRIP_TAC = 
      Tactical.FIRST [GEN_TAC,CONJ_TAC, DTHEN STRIP_ASSUME_TAC]
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

infix 8 by;

fun (q by tac) = 
  Tactic.via(Term q,tac)
  handle e as HOL_ERR _ => raise BOSS_ERR "by" "";

end;
