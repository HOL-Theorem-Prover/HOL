(* ===================================================================== *)
(* FILE          : define_mutual_types.sml                               *)
(* DESCRIPTION   : Defines nested mutually recursive types, conveniently.*)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier, Univ. of Pennsylvania          *)
(* DATE          : April 23, 1998                                        *)
(* ===================================================================== *)


(*
val _ = app use ["mutrec.yak.sig","mutrec.yak.sml","mutrec.lex.sml"];
*)

structure Parse_mutual_types : Parse_mutual_types_sig =
struct
structure Parse_support = Parse_support

structure PD_Tokens = MutrecLrValsFun(LrParser.Token);
structure Lex = HolLex(structure Tokens = PD_Tokens.Tokens
                       structure Parse_support = Parse_support);
structure P = JoinWithArg(structure ParserData = PD_Tokens.ParserData
                          structure Lex = Lex
                          structure LrParser = LrParser);

datatype frag = datatype Portable.frag;

fun DEFINE_MUTUAL_TYPES_ERR{func,mesg} = 
 Exception.HOL_ERR{origin_structure = "Parse_mutual_types",
              origin_function = func,
              message = mesg};

fun error (s,_,_) = raise DEFINE_MUTUAL_TYPES_ERR{func="Parsing error", mesg=s};

fun format [] ol ml = (ol, rev ml) 
  | format (ANTIQUOTE  x::rst) ol ml = format rst (ol^"^") (x::ml)
  | format (QUOTE s::rst) ol ml = format rst (ol^s) ml;


fun parse0 tyvars s aqs =
   let val strm = Portable.open_string s
       val lexer = P.makeLexer(fn _ => Portable.input_line strm) (ref aqs)
   in Lib.fst(P.parse(0,lexer,error,tyvars))
   end;

fun pstring tyvars = Lib.C (parse0 tyvars) [];

fun pquote tyvars ol_frag_list =
   let val (s,antiq_list) = format ol_frag_list "" []
   in parse0 tyvars s antiq_list
   end; 

val dummy_tyvars = Type.fresh_tyvar_stream()
val ty_quote = pquote dummy_tyvars
val ty_string = pstring dummy_tyvars;


(*---------------------------------------------------------------------------
 * Parsing of type specifications
 *---------------------------------------------------------------------------*)
fun colon s = ":"^s;

fun try f x = f x handle e => Exception.Raise e;

fun mutual_types_spec_parser (QUOTE s :: rst) =
     (Globals.in_type_spec := SOME "";
      (try ty_quote (QUOTE(colon s)::rst)))
  | mutual_types_spec_parser _ = raise DEFINE_MUTUAL_TYPES_ERR{
                                         func = "mutual_types_spec_parser",
                                         mesg = "Badly formed quotation."};

fun string_to_mutual_types_spec s =
  (Globals.in_type_spec := SOME "";
   (ty_string (colon s)));

end; (* Parse_mutual_types *)


(* ---------------------------------------------------------------------*)
(* Functor DefineMutualTypesFunc:                                       *)
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

signature AltNestedRecTypeInputSig =
    sig
        val name : string
        val recursor_thms : Thm.thm list
        val def_type_spec :
            {type_name : string,
             constructors : {name : string,
                             arg_info : DefTypeInfo.type_info list} list} list

    end;

structure Rename_mutual_types_thms : Rename_mutual_types_thms_sig =
struct
open Rsyntax;

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
fun fch ty = (hd o explode o #Tyop o dest_type) ty
             handle _ => Portable.Char.chr 120 (* "x" *)
fun suff f c l =
   if (f c = "")
   then if (Portable.List.exists (fn x => fch x = c) l)
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
          val v = variant rvs (mk_var{Name = Portable.String.str c^s, Ty = h})
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
             handle _ => Portable.Char.chr 120 (* "x" *)
fun suff f c l =
   if (f c = "")
   then if (Portable.List.exists (fn x => fch x = c) l)
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
          val v = variant rvs (mk_var{Name = "fn"^Portable.String.str c^s,
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

local
val AND = --`/\`--
in
fun CONJS_CONV conv tm =
   let val {conj1,conj2} = dest_conj tm
   in MK_COMB(AP_TERM AND (conv conj1), CONJS_CONV conv conj2)
   end
   handle _ => conv tm
end;

(* ---------------------------------------------------------------------*)
(* DISJS_CONV : apply a given conversion to a sequence of conjuncts     *)
(*                                                                      *)
(* DISJS_CONV conv `t1 \/ t2 \/ ... \/ tn` applies conv to each of the  *)
(* n disjuncts t1,t2,...,tn and then rebuilds the disjunction from the  *)
(* results.                                                             *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

local
val OR = --`\/`--
in
fun DISJS_CONV conv tm =
   let val {disj1,disj2} = dest_disj tm
   in MK_COMB(AP_TERM OR (conv disj1), DISJS_CONV conv disj2)
   end
   handle _ => conv tm
end;

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
   if not (is_forall tm) then
         raise Parse_mutual_types.DEFINE_MUTUAL_TYPES_ERR
                        {func = "MOVEQS", mesg = "not a forall"}
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

end; (* structure Rename_mutual_types_thms *)


functor AltNestedRecTypeFunc(NestedRecTypeInput : AltNestedRecTypeInputSig) =
let

    structure DefType = DefTypeFunc (NestedRecTypeInput)

    open Rename_mutual_types_thms;

    val save_thm = Theory.save_thm

    fun add_thm (name,thm) = add_to_sml[(name,save_thm(name,thm))]

    val new_ty_existence_thm =
            RENAME_EXISTS_THM DefType.New_Ty_Existence_Thm

    val new_ty_induct_thm =
            RENAME_INDUCT_THM DefType.New_Ty_Induct_Thm

    val new_ty_uniqueness_thm =
            RENAME_UNIQUE_THM DefType.New_Ty_Uniqueness_Thm

    val constructors_distinct_thm =
            RENAME_DISTINCT_THM DefType.Constructors_Distinct_Thm

    val constructors_one_one_thm =
            RENAME_ONE_ONE_THM DefType.Constructors_One_One_Thm

    val cases_thm = RENAME_CASES_THM DefType.Cases_Thm

    val _ = add_thm(NestedRecTypeInput.name ^ "_exists",
                    new_ty_existence_thm)

    val _ = add_thm(NestedRecTypeInput.name ^ "_induct",
                    new_ty_induct_thm)

    val _ = add_thm(NestedRecTypeInput.name ^ "_unique",
                    new_ty_uniqueness_thm)

    val _ = add_thm(NestedRecTypeInput.name ^ "_distinct",
                    constructors_distinct_thm)

    val _ = add_thm(NestedRecTypeInput.name ^ "_one_one",
                    constructors_one_one_thm)

    val _ = add_thm(NestedRecTypeInput.name ^ "_cases",
                    cases_thm)

    structure MutualType : DefTypeSig =
        struct
            type thm = CoreHol.Thm.thm
            val New_Ty_Existence_Thm = new_ty_existence_thm
            val New_Ty_Induct_Thm = new_ty_induct_thm
            val New_Ty_Uniqueness_Thm = new_ty_uniqueness_thm
            val Constructors_Distinct_Thm = constructors_distinct_thm
            val Constructors_One_One_Thm = constructors_one_one_thm
            val Cases_Thm = cases_thm
        end
in
    MutualType
end


functor DefineMutualTypesFunc
              (val name : string
               and recursor_thms : Thm.thm list
               and types_spec : Term.term Portable.frag list) =
let
    val def_type_spec = Parse_mutual_types.mutual_types_spec_parser types_spec
               handle HOL_ERR{origin_structure,origin_function,message}
               => raise Parse_mutual_types.DEFINE_MUTUAL_TYPES_ERR{
                        func = "DefineMutualTypeFunc",
                      mesg = origin_structure^"."^origin_function^": "^message}
    
    structure NestedRecTypeInput  : AltNestedRecTypeInputSig =
          struct
             val name = name
             val def_type_spec = def_type_spec
             val recursor_thms = recursor_thms
          end (* struct *)
in
    AltNestedRecTypeFunc (NestedRecTypeInput)
end


functor StringDefineMutualTypesFunc
              (val name : string
               and recursor_thms : Thm.thm list
               and types_spec : string) =
let
    val def_type_spec= Parse_mutual_types.string_to_mutual_types_spec types_spec
               handle HOL_ERR{origin_structure,origin_function,message}
               => raise Parse_mutual_types.DEFINE_MUTUAL_TYPES_ERR{
                        func = "StringDefineMutualTypeFunc",
                      mesg = origin_structure^"."^origin_function^": "^message}
    
    structure NestedRecTypeInput  : AltNestedRecTypeInputSig =
          struct
             val name = name
             val def_type_spec = def_type_spec
             val recursor_thms = recursor_thms
          end (* struct *)
in
    AltNestedRecTypeFunc (NestedRecTypeInput)
end

(* Examples.

structure avexp =
   DefineMutualTypesFunc
      (val name = "avexp"
       val recursor_thms = [list_Axiom]
       val type_spec =
        ` vexp = ANUM of num
               | AVAR of string
               | ASUC of vexp
               | APLUS of vexp => vexp
               | AMINUS of vexp => vexp
               | AMULT of vexp => vexp
               | ACONDV of aexp => vexp => vexp
               | ACALL of string => vexp list ;
          aexp = ATRUE
               | AFALSE
               | AEQ of vexp => vexp
               | ALESS of vexp => vexp
               | ALLESS of vexp list => vexp list
               | AAND of aexp => aexp
               | AOR of aexp => aexp
               | ANOT of aexp
               | AIMP of aexp => aexp
               | AEQB of aexp => aexp
               | ACOND of aexp => aexp => aexp
               | AFORALL of string => aexp
               | AEXISTS of string => aexp ` );

structure avexp =
   StringDefineMutualTypesFunc
      (val name = "avexp"
       val recursor_thms = [list_Axiom]
       val type_spec =
        " vexp = ANUM of num  \
\              | AVAR of string  \
\              | ASUC of vexp  \
\              | APLUS of vexp => vexp  \
\              | AMINUS of vexp => vexp  \
\              | AMULT of vexp => vexp  \
\              | ACONDV of aexp => vexp => vexp  \
\              | ACALL of string => vexp list ;  \
\         aexp = ATRUE  \
\              | AFALSE  \
\              | AEQ of vexp => vexp  \
\              | ALESS of vexp => vexp  \
\              | ALLESS of vexp list => vexp list  \
\              | AAND of aexp => aexp  \
\              | AOR of aexp => aexp  \
\              | ANOT of aexp  \
\              | AIMP of aexp => aexp  \
\              | AEQB of aexp => aexp  \
\              | ACOND of aexp => aexp => aexp  \
\              | AFORALL of string => aexp  \
\              | AEXISTS of string => aexp " );


structure tys =
     DefineMutualTypesFunc(val name = "tys"
                           val recursor_thms = [list_Axiom]
                           val types_spec =
                           `ty1 = C1 of 'a
                                | C2 of ty1 => 'a
                                | C3 of 'a => ty2 list ;
                            ty2 = C4 of ty1 list
                                | C5 of 'a => ty2 `);
*)

