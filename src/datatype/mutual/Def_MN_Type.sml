(*========================================================================*)
(* FILE          : Def_MN_Type.sml (originally define_mutual_types.sml)   *)
(* DESCRIPTION   : Defines nested mutually recursive types, conveniently. *)
(*                                                                        *)
(* AUTHOR        : Peter Vincent Homeier, Univ. of Pennsylvania           *)
(* DATE          : April 23, 1998                                         *)
(*                                                                        *)
(* ADAPTED       : for Hol98                                              *)
(* ADAPTOR       : Konrad Slind, Cambridge University                     *)
(* DATE          : December 12, 1998                                      *)
(*========================================================================*)

structure Def_MN_Type :> Def_MN_Type =
struct

(* ---------------------------------------------------------------------*)
(* Functor DefNestTypesFunc:                                       *)
(*                                                                      *)
(* construct a set of nested mutually recursive user-specified concrete *)
(* recursive type and derive abstract characterizations of them.        *)
(*                                                                      *)
(* DefineMutualTypesFunc takes an input structure with signature        *)
(*                                                                      *)
(*      signature DefineMutualTypesInputSig =                           *)
(*          sig                                                         *)
(*              val name : string                                       *)
(*              val recursor_thms : Thm.thm list                        *)
(*              val types_spec : Term.term Portable.frag list           *)
(*          end;                                                        *)
(*                                                                      *)
(* E.g.                                                                 *)
(*                                                                      *)
(* structure tys =                                                      *)
(*      DefineMutualTypesFunc(val name = "tys"                          *)
(*                            val recursor_thms = [list_Axiom]          *)
(*                            val types_spec =                          *)
(*                            `ty1 = C1 of 'a                           *)
(*                                 | C2 of ty1 => 'a                    *)
(*                                 | C3 of 'a => ty2 list ;             *)
(*                             ty2 = C4 of ty1 list                     *)
(*                                 | C5 of 'a => ty2 `);                *)
(*                                                                      *)
(* defines:                                                             *)
(*      1) type operators ('a)ty1                                       *)
(*                        ('a)ty2                                       *)
(*      2) constants C1: 'a -> 'a ty1,                                  *)
(*                   C2: 'a ty1 -> 'a -> 'a ty1,                        *)
(*                   C3: 'a -> 'a ty2 list -> 'a ty1,                   *)
(*                   C4: 'a ty1 list -> 'a ty2                          *)
(*                   C5: 'a -> 'a ty2 ->'a ty2                          *)
(*                                                                      *)
(* and proves that ty1 and ty2 have the following properties:           *)
(*                                                                      *)
(*      1) Existence                                                    *)
(*      2) Induction                                                    *)
(*      3) Uniqueness                                                   *)
(*      4) Distinctness of Constructors                                 *)
(*      5) One-to-one-ness of Constructors                              *)
(*      6) Cases of Construction                                        *)
(*                                                                      *)
(* These theorems are stored in the current theory and added to the     *)
(* SML session, with names (respectively)                               *)
(*                                                                      *)
(*      1) tys_exists                                                   *)
(*      2) tys_induct                                                   *)
(*      3) tys_unique                                                   *)
(*      4) tys_distinct                                                 *)
(*      5) tys_one_one                                                  *)
(*      6) tys_cases                                                    *)
(*                                                                      *)
(* These theorems are also returned in the structure tys that is        *)
(* created by the functor.  This structure has signature                *)
(*                                                                      *)
(*      signature MutualTypeSig =                                       *)
(*          sig                                                         *)
(*            type thm                                                  *)
(*              val New_Ty_Axiom_Thm :thm                               *)
(*              val New_Ty_Induct_Thm :thm                              *)
(*              val New_Ty_Uniqueness_Thm :thm                          *)
(*              val New_Ty_Existence_Thm :thm                           *)
(*              val Constructors_Distinct_Thm : thm                     *)
(*              val Constructors_One_One_Thm : thm                      *)
(*              val Cases_Thm : thm                                     *)
(*          end;                                                        *)
(*                                                                      *)
(* There is a corresponding functor StringDefineMutualTypesFunc which   *)
(* takes a string as the specification of the types, instead of the     *)
(* term frag list that DefineMutualTypesFunc accepts.                   *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

open HolKernel Parse basicHol90Lib;
infix THENC THEN;

type 'a quotation = 'a frag list
type hol_type = Type.hol_type
type thm = Thm.thm

fun ERR func mesg =
 Exception.HOL_ERR
    {origin_structure = "DefNestType",
     origin_function = func,
     message = mesg};

val (Type,Term) = parse_from_grammars boolTheory.bool_grammars
fun -- q x = Term q
fun == q x = Type q

val OR  = --`$\/`--;
val AND = --`$/\`--;


(* ---------------------------------------------------------------------*)
(* mkvars : generate sensible variable names for the arguments to the   *)
(* constructors of a newly-defined type.  A call to mkvars takes the    *)
(* form:                                                                *)
(*                                                                      *)
(*     mkvars [t1;...;tn]                                               *)
(*                                                                      *)
(* where t1,...,tn are the types required for the variables.            *)
(* ---------------------------------------------------------------------*)

local
fun fch ty = (hd o explode o #Tyop o dest_type) ty handle _ => #"x"
fun suff f c l =
   if (f c = "")
   then if (exists (fn x => fch x = c) l)
        then ("0", fn ch => (if (ch=c) then "0" else f ch))
        else ("",f)
   else let val n = int_to_string(string_to_int(f c) + 1)
        in (n, fn ch => if (ch=c) then n else f ch)
        end
fun mkvs f rvs [] = []
  | mkvs f rvs (h::t) =
      let val c = fch h
          val (s,f') = suff f c t
(*           val v = variant rvs (mk_primed_var{Name = c^s, Ty = h}) *)
          val v = variant rvs (mk_var{Name = String.str c^s, Ty = h})
      in
      v::(mkvs f' (v::rvs) t)
      end
in
fun mkvars l = mkvs (fn x => "") [] l
end;

(* ---------------------------------------------------------------------*)
(* mkfuns : generate sensible function names for the functions being    *)
(* applied to instances of a newly-defined type.  A call to mkfuns      *)
(* takes the form:                                                      *)
(*                                                                      *)
(*     mkfuns [t1;...;tn]                                               *)
(*                                                                      *)
(* where t1,...,tn are the function types required for the variables.   *)
(* The names will begin with "fn", continue with a single character     *)
(* depending on the name of the type of the first argument, and be      *)
(* followed by a numeric suffix starting with 0, unless there is only   *)
(* one name of that character.                                          *)
(* ---------------------------------------------------------------------*)

local
fun fch ty = (hd o explode o #Tyop o dest_type o hd o #Args o dest_type) ty
             handle _ => #"x"
fun suff f c l =
   if (f c = "")
   then if (exists (fn x => fch x = c) l)
        then ("0", fn ch => (if (ch=c) then "0" else f ch))
        else ("",f)
   else let val n = int_to_string(string_to_int(f c) + 1)
        in (n, fn ch => if (ch=c) then n else f ch)
        end
fun mkfs f rvs [] = []
  | mkfs f rvs (h::t) =
      let val c = fch h
          val (s,f') = suff f c t
(*           val v = variant rvs (mk_primed_var{Name = "fn"^c^s, Ty = h}) *)
          val v = variant rvs (mk_var{Name = "fn"^String.str c^s,
                                      Ty = h})
      in
      v::(mkfs f' (v::rvs) t)
      end
in
fun mkfuns l = mkfs (fn x => "") [] l
end;

(* ---------------------------------------------------------------------*)
(* UNDER_FORALL_CONV : apply a given conversion under a sequence of     *)
(* universal quantifications                                            *)
(*                                                                      *)
(* UNDER_FORALL_CONV conv `!x1 x2 ... xn. t` applies conv to t, and     *)
(* then universal quantification from the results.                      *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

fun UNDER_FORALL_CONV conv tm =
   let val _ = dest_forall tm
       val {Rator,Rand} = dest_comb tm
       val {Bvar,Body} = dest_abs Rand
   in AP_TERM Rator (ABS Bvar (UNDER_FORALL_CONV conv Body))
   end
   handle _ => conv tm;

(* ---------------------------------------------------------------------*)
(* UNDER_EXISTS_CONV : apply a given conversion under a sequence of     *)
(* existential quantifications                                          *)
(*                                                                      *)
(* UNDER_EXISTS_CONV conv `!x1 x2 ... xn. t` applies conv to t, and     *)
(* then existential quantification from the results.                    *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

fun UNDER_EXISTS_CONV conv tm =
   let val _ = dest_exists tm
       val {Rator,Rand} = dest_comb tm
       val {Bvar,Body} = dest_abs Rand
   in AP_TERM Rator (ABS Bvar (UNDER_EXISTS_CONV conv Body))
   end
   handle _ => conv tm;

(* ---------------------------------------------------------------------*)
(* QUANTS_ALPHA_CONV : apply alpha conversions to a sequence of         *)
(* quantified variables, either forall or exists.                       *)
(*                                                                      *)
(* QUANTS_ALPHA_CONV [`x1`, ..., `xn`] `!y1 ... yn. t` returns the      *)
(* theorem                                                              *)
(*                                                                      *)
(*    |- (!y1 ... yn. t) = (!x1' ... xn'. t[x1',...,xn'/y1,...,yn])     *)
(*                                                                      *)
(* where the variables xi' are primed variants of xi chosen so as not   *)
(* to be free in !y1 y2 ... yn. t.                                      *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

fun QUANTS_ALPHA_CONV [] = ALL_CONV
  | QUANTS_ALPHA_CONV (x::xs) =
    RAND_CONV (ALPHA_CONV x THENC ABS_CONV (QUANTS_ALPHA_CONV xs));

(* ---------------------------------------------------------------------*)
(* CONJS_CONV : apply a given conversion to a sequence of conjuncts     *)
(*                                                                      *)
(* CONJS_CONV conv `t1 /\ t2 /\ ... /\ tn` applies conv to each of the  *)
(* n conjuncts t1,t2,...,tn and then rebuilds the conjunction from the  *)
(* results.                                                             *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

fun CONJS_CONV conv tm =
   let val {conj1,conj2} = dest_conj tm
   in MK_COMB(AP_TERM AND (conv conj1), CONJS_CONV conv conj2)
   end
   handle _ => conv tm

(* ---------------------------------------------------------------------*)
(* DISJS_CONV : apply a given conversion to a sequence of conjuncts     *)
(*                                                                      *)
(* DISJS_CONV conv `t1 \/ t2 \/ ... \/ tn` applies conv to each of the  *)
(* n disjuncts t1,t2,...,tn and then rebuilds the disjunction from the  *)
(* results.                                                             *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)


fun DISJS_CONV conv tm =
   let val {disj1,disj2} = dest_disj tm
   in MK_COMB(AP_TERM OR (conv disj1), DISJS_CONV conv disj2)
   end
   handle _ => conv tm


(* ---------------------------------------------------------------------*)
(* RENAME_FORALL_VARS_CONV : rename the variables used in a sequence of *)
(* universal quantifications to reasonable function names.              *)
(* ---------------------------------------------------------------------*)

fun RENAME_FORALL_VARS_CONV tm =
    let val (vrs, body) = strip_forall tm
    in
    QUANTS_ALPHA_CONV (mkvars (map (#Ty o dest_var) vrs)) tm
    end;

(* ---------------------------------------------------------------------*)
(* RENAME_FORALL_11_CONV : rename the variables used in a sequence of   *)
(* universal quantifications to reasonable function names.              *)
(* ---------------------------------------------------------------------*)

fun RENAME_FORALL_11_VARS_CONV tm =
    let val (vrs, body) = strip_forall tm
        val n = length vrs div 2
        val (vrs1,_) = split_after n vrs
        val vrs1 = mkvars (map (#Ty o dest_var) vrs1)
        val vrs2 = map (fn v => let val {Name,Ty} = dest_var v
                                in mk_var{Name=Name^"'",Ty=Ty}
                                end)
                       vrs1
    in
    QUANTS_ALPHA_CONV (vrs1 @ vrs2) tm
    end;

(* ---------------------------------------------------------------------*)
(* RENAME_EXISTS_VARS_CONV : rename the variables used in a sequence of *)
(* universal quantifications to reasonable function names.              *)
(* ---------------------------------------------------------------------*)

fun RENAME_EXISTS_VARS_CONV tm =
    let val (vrs, body) = strip_exists tm
    in
    QUANTS_ALPHA_CONV (mkvars (map (#Ty o dest_var) vrs)) tm
    end;

(* ---------------------------------------------------------------------*)
(* RENAME_EXISTS_FUNS_CONV : rename the variables used in a sequence of *)
(* existential quantifications to reasonable function names.            *)
(* ---------------------------------------------------------------------*)

fun RENAME_EXISTS_FUNS_CONV tm =
    let val (vrs, body) = strip_exists tm
    in
    QUANTS_ALPHA_CONV (mkfuns (map (#Ty o dest_var) vrs)) tm
    end;

(* ---------------------------------------------------------------------*)
(* Internal function:                                                   *)
(*                                                                      *)
(* MOVEQS tys : returns a conversion that, when applied to a term with  *)
(*              universal quantifications, moves the quantifications    *)
(*              of variables of types in tys outward, and the others    *)
(*              inward towards the body; otherwise, order is preserved. *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

fun MOVEQS tys tm =
   if not (is_forall tm) then raise ERR "MOVEQS" "not a forall"
   else
   let val (Bvars,Body) = strip_forall tm
       val (vars1,vars2) = partition (fn v => mem (type_of v) tys) Bvars
       val tm1 = list_mk_forall (vars1 @ vars2, Body)
       val eq_thm =
       Tactical.prove (Rsyntax.mk_eq{lhs=tm, rhs=tm1},
                       EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[])
   in
       itlist (fn v =>
               CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV FORALL_IMP_CONV)))
              vars2 eq_thm
   end;

(* ---------------------------------------------------------------------*)
(* RENAME_EXISTS_THM : rename the variables used in the existence       *)
(* theorem generated by the nested recursion library to reasonable      *)
(* names.                                                               *)
(* ---------------------------------------------------------------------*)

val RENAME_EXISTS_THM =
    CONV_RULE (UNDER_FORALL_CONV
                (RENAME_EXISTS_FUNS_CONV THENC
                 UNDER_EXISTS_CONV
                  (CONJS_CONV RENAME_FORALL_VARS_CONV))
               THENC REWRITE_CONV[ETA_AX]);

(* ---------------------------------------------------------------------*)
(* RENAME_INDUCT_THM : rename the variables used in the induction       *)
(* theorem generated by the nested recursion library to reasonable      *)
(* names.                                                               *)
(* ---------------------------------------------------------------------*)

fun RENAME_INDUCT_THM th =
    let val (Bvars,Body) = strip_forall(concl th)
        val {ant = hy, conseq = cns} = dest_imp Body
        val tys = map (type_of o #Bvar o dest_forall) (strip_conj cns)
    in
    (CONV_RULE (UNDER_FORALL_CONV
                 (RATOR_CONV (RAND_CONV (CONJS_CONV RENAME_FORALL_VARS_CONV)
                                         THENC ONCE_DEPTH_CONV (MOVEQS tys))
                  THENC RAND_CONV (CONJS_CONV RENAME_FORALL_VARS_CONV)))
     o REWRITE_RULE[AND_IMP_INTRO,GSYM CONJ_ASSOC]) th
    end;

(* ---------------------------------------------------------------------*)
(* RENAME_UNIQUE_THM : rename the variables used in the uniqueness      *)
(* theorem generated by the nested recursion library to reasonable      *)
(* names.                                                               *)
(* ---------------------------------------------------------------------*)

val RENAME_UNIQUE_THM =
    (CONV_RULE (UNDER_FORALL_CONV
                 (RATOR_CONV (RAND_CONV (CONJS_CONV RENAME_FORALL_VARS_CONV))))
     o REWRITE_RULE[AND_IMP_INTRO,GSYM CONJ_ASSOC])

(* ---------------------------------------------------------------------*)
(* RENAME_DISTINCT_THM : rename the variables used in the               *)
(* distinctiveness of constructors theorem generated by the nested      *)
(* recursion library to reasonable names.                               *)
(* ---------------------------------------------------------------------*)

val RENAME_DISTINCT_THM =
    CONV_RULE (CONJS_CONV (CONJS_CONV RENAME_FORALL_VARS_CONV)
               THENC REWRITE_CONV[ETA_AX]);

(* ---------------------------------------------------------------------*)
(* RENAME_ONE_ONE_THM : rename the variables used in the                *)
(* one-to-one-ness of constructors theorem generated by the nested      *)
(* recursion library to reasonable names.                               *)
(* ---------------------------------------------------------------------*)

val RENAME_ONE_ONE_THM =
    CONV_RULE (CONJS_CONV (CONJS_CONV RENAME_FORALL_11_VARS_CONV)
               THENC REWRITE_CONV[ETA_AX]);

(* ---------------------------------------------------------------------*)
(* RENAME_CASES_THM : rename the variables used in the cases theorem    *)
(* generated by the nested recursion library to reasonable names.       *)
(* ---------------------------------------------------------------------*)

val RENAME_CASES_THM =
    CONV_RULE (CONJS_CONV (RENAME_FORALL_VARS_CONV THENC
                           UNDER_FORALL_CONV
                            (DISJS_CONV RENAME_EXISTS_VARS_CONV)));


fun prim_define_type desc axioms =
 let val {New_Ty_Existence_Thm=th1,
          New_Ty_Induct_Thm=th2,
          New_Ty_Uniqueness_Thm=th3,
          Constructors_Distinct_Thm=th4,
          Constructors_One_One_Thm=th5,
          Cases_Thm=th6}
         = nested_recLib.define_type desc axioms
 in
   {New_Ty_Existence_Thm      = RENAME_EXISTS_THM th1,
    New_Ty_Induct_Thm         = RENAME_INDUCT_THM th2,
    New_Ty_Uniqueness_Thm     = RENAME_UNIQUE_THM th3,
    Constructors_Distinct_Thm = RENAME_DISTINCT_THM th4,
    Constructors_One_One_Thm  = RENAME_ONE_ONE_THM th5,
    Cases_Thm                 = RENAME_CASES_THM th6}
 end;


(*---------------------------------------------------------------------------
    Parsing of type specifications
 ---------------------------------------------------------------------------*)

local
  open DefTypeInfo ParseDatatype
  fun dexl [] A = SOME(rev A) (* all in list were existing *)
    | dexl (existing ty::t) A = dexl t (ty::A)
    | dexl _ _ = NONE
in
  fun make_type_clause tynames (constructor, args) = let
    fun munge (dVartype s) = existing(mk_vartype s)
      | munge (dAQ ty) = existing ty
      | munge (dTyop(gr, [])) = let
          val name = gr
        in
          if mem name tynames then being_defined name
          else existing(mk_type{Tyop=name, Args=[]})
        end
      | munge (dTyop(gr,A)) = let
          val name = gr
          val A1 = map munge A
        in
          case dexl A1 [] of
            SOME A2 => existing(mk_type{Tyop=name, Args = A2})
          | NONE    => type_op{Tyop=name, Args = A1}
        end
  in
    {name=constructor, arg_info = map munge args}
  end
end;

fun transAST tynames (tyn,dtform) =
  case dtform of
    ParseDatatype.Constructors cargs =>
      {type_name = tyn, constructors = map (make_type_clause tynames) cargs}
  | ParseDatatype.Record _ =>
      raise ERR "transAST"
        "Can't handle record forms in middle of mutual and/or nested type defn"


fun prepare_quote q =
     let val astl = ParseDatatype.parse q
         val tynames = map #1 astl
     in
       map (transAST tynames) astl
     end;


fun define_type axioms q = prim_define_type (prepare_quote q) axioms;

fun string_define_type axioms s = define_type axioms [QUOTE s];


(*---------------------------------------------------------------------------
        Examples.

time (define_type [listTheory.list_Axiom])
    `vexp = ANUM   of num
          | AVAR   of ind (* was string *)
          | ASUC   of vexp
          | APLUS  of vexp => vexp
          | AMINUS of vexp => vexp
          | AMULT  of vexp => vexp
          | ACONDV of aexp => vexp => vexp
          | ACALL  of ind => vexp list ;

     aexp = ATRUE
          | AFALSE
          | AEQ    of vexp => vexp
          | ALESS  of vexp => vexp
          | ALLESS of vexp list => vexp list
          | AAND   of aexp => aexp
          | AOR    of aexp => aexp
          | ANOT   of aexp
          | AIMP   of aexp => aexp
          | AEQB   of aexp => aexp
          | ACOND  of aexp => aexp => aexp
          | AFORALL of ind => aexp
          | AEXISTS of ind => aexp`;


time (string_define_type [listTheory.list_Axiom])
        "vexp = ANUM of num  \
\             | AVAR of string  \
\             | ASUC of vexp  \
\             | APLUS of vexp => vexp  \
\             | AMINUS of vexp => vexp  \
\             | AMULT of vexp => vexp  \
\             | ACONDV of aexp => vexp => vexp  \
\             | ACALL of string => vexp list ;  \
\        aexp = ATRUE  \
\             | AFALSE  \
\             | AEQ of vexp => vexp  \
\             | ALESS of vexp => vexp  \
\             | ALLESS of vexp list => vexp list  \
\             | AAND of aexp => aexp  \
\             | AOR of aexp => aexp  \
\             | ANOT of aexp  \
\             | AIMP of aexp => aexp  \
\             | AEQB of aexp => aexp  \
\             | ACOND of aexp => aexp => aexp  \
\             | AFORALL of string => aexp  \
\             | AEXISTS of string => aexp";


define_type [listTheory.list_Axiom]
       `ty1 = C1 of 'a
            | C2 of ty1 => 'a
            | C3 of 'a => ty2 list ;
        ty2 = C4 of ty1 list
            | C5 of 'a => ty2 `;
*)

end;
