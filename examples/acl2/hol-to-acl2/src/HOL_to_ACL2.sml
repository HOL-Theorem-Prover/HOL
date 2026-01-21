(*---------------------------------------------------------------------------*)
(* Copyright (C) 2025, Konrad Slind                                          *)
(* Written by Konrad Slind                                                   *)
(* License: A 3-clause BSD license;                                          *)
(*          See the LICENSE file distributed with ACL2.                      *)
(*---------------------------------------------------------------------------*)

structure HOL_to_ACL2 :> HOL_to_ACL2 =
struct
open HolKernel boolLib bossLib
     pairTheory listTheory hol_to_acl2Theory;

open HOLsexp List;

val ERR = mk_HOL_ERR  "HOL_to_ACL2";

(*---------------------------------------------------------------------------*)
(* Basic definitions underpinning examples                                   *)
(*---------------------------------------------------------------------------*)

val basis_defs =
  [cond_thm, COMMA_def, FST, SND, suc_thm, leq_thm, HD, null_thm]

(*---------------------------------------------------------------------------*)
(* Tags on elements to be translated                                         *)
(*---------------------------------------------------------------------------*)

val THM_const  = prim_mk_const{Thy="hol_to_acl2",Name="THM"}
val GOAL_const = prim_mk_const{Thy="hol_to_acl2",Name="GOAL"}
val SPEC_const = prim_mk_const{Thy="hol_to_acl2",Name="SPEC"};

(*---------------------------------------------------------------------------*)
(* Types                                                                     *)
(*---------------------------------------------------------------------------*)

fun tyvar_name tyv =
 let val s = dest_vartype tyv
 in String.substring(s,1,String.size s - 1)
 end

fun tyop_dict s =
  case s
   of "fun" => ":arrow*"
    | "prod" => ":hash"
    | otherwise => ":"^s

(*---------------------------------------------------------------------------*)
(* A HOL type is essentially a first order term: either a variable or a      *)
(* type operator applied to a list of types.                                 *)
(*---------------------------------------------------------------------------*)

fun ty_sexp ty =
 if is_vartype ty then
   Symbol (tyvar_name ty)
 else
  case dest_type ty
   of (s,[]) => Symbol (tyop_dict s)
    | ("fun",_) =>
        let val tylist = (op@ o (I ## single) o strip_fun) ty
        in Cons(Symbol(tyop_dict "fun"),List (map ty_sexp tylist))
        end
    | (s,args) => Cons(Symbol(tyop_dict s),List (map ty_sexp args))
;

(*---------------------------------------------------------------------------*)
(* example type s-expressions                                                *)
(*---------------------------------------------------------------------------*)

(*
map ty_sexp [bool, alpha --> beta, bool --> alpha --> beta, ``:num list``];
*)

(*---------------------------------------------------------------------------*)
(* Terms                                                                     *)
(*---------------------------------------------------------------------------*)

fun bvar_sexp v =
 let val (s,ty) = dest_var v
 in List[Symbol s,ty_sexp ty]
 end

fun strip_cond tm =
  if not (is_cond tm) then
    ([],tm)
  else
    let val (t1,t2,t3) = dest_cond tm
        val (pairs,tn) = strip_cond t3
    in ((t1,t2)::pairs,tn)
    end

(*---------------------------------------------------------------------------*)
(* Current rule for mapping a name to a constant: look to see if the name is *)
(* that of a built-in. If it is then no need to do a hap*. If it isn't then  *)
(* do a (hap* (name (ty <ty>)) a1 ... an)                                    *)
(*---------------------------------------------------------------------------*)

val builtin_const_map =
  [(“(=)”, "hp="),
   (“(,)”, "hp-comma"),
   (“NIL”, "hp-nil"),
   (“CONS”, "hp-cons"),
   (“NONE”, "hp-none"),
   (“SOME”, "hp-some"),
   (“T”, "hp-true"),
   (“F”, "hp-false"),
   (“(~):bool->bool”, "hp-not"),
   (“(/\)”, "hp-and"),
   (“(\/)”, "hp-or"),
   (“(==>)”, "hp-implies"),
   (“(!)”, "hp-forall"),
   (“(?)”, "hp-exists"),
   (“(+):num->num->num”, "hp+"),
   (“$* :num->num->num”, "hp*"),
   (“(<):num->num->bool”, "hp<")
  ];

fun lookup_const_name c = total (op_assoc same_const c) builtin_const_map;

fun mk_typ ty = Cons(Symbol "typ", List [ty_sexp ty])

(*---------------------------------------------------------------------------*)
(* Nullary polymorphic constructors need special treatment to find the type  *)
(* argument.                                                                 *)
(*---------------------------------------------------------------------------*)

fun const_sexp c =
  let val {Name,Ty,Thy} = dest_thy_const c
      val generic_const = prim_mk_const{Name=Name,Thy=Thy}
      val is_ground = null o type_vars_in_term
  in case lookup_const_name c
      of NONE => Cons(Symbol Name, List [mk_typ Ty])
       | SOME acl2_name =>
           let val tylist =
               if is_ground generic_const then
                  [] else
               if same_const c listSyntax.nil_tm then
                  [mk_typ (listSyntax.dest_list_type Ty)] else
               if same_const c optionSyntax.none_tm then
                  [mk_typ (optionSyntax.dest_option Ty)]
               else [mk_typ Ty]
           in
              Cons(Symbol acl2_name, List tylist)
           end
  end

(*---------------------------------------------------------------------------*)
(* NB: 0 is a constant but needs to be treated as a literal, so the          *)
(* "is_numeral" check has to come before the "is_const" check.               *)
(*---------------------------------------------------------------------------*)

fun tm_sexp t =
  if is_var t then
     Symbol (fst(dest_var t)) else
  if numSyntax.is_numeral t then
     let open numSyntax
         val n = dest_numeral t
         val ns = Arbnum.toString n
     in List [Symbol "hp-num", Symbol ns]
     end else
  if is_const t then
     const_sexp t else
  let val (f,args) = strip_comb t
  in if is_abs f then String "<!!lambda abstraction!!>"
     else
     (* args are non-null at this point *)
     if is_var f then
        Cons(Symbol "hap*", List (map tm_sexp (f::args))) else
     if is_const f then
        let val {Name,Thy,Ty} = dest_thy_const f
        in case lookup_const_name f
            of NONE => Cons(Symbol "hap*", List (map tm_sexp (f::args)))
             | SOME acl2_name => Cons(Symbol acl2_name, List (map tm_sexp args))
        end
     else
     String "<!unexpected term structure!>"
  end

(* TODO
 if is_cond t then
    let val (pairs,last_tm) = strip_cond t
        val pair_sexps = map (fn (t1,t2) => List [tm_sexp t1, tm_sexp t2]) pairs
        val last_pair = List[Symbol"T", tm_sexp last_tm]
    in Cons (Symbol"cond",List (pair_sexps @ [last_pair]))
    end else
*)

fun fns_entry c =
   let val {Name,Thy,Ty} = dest_thy_const c
   in List [Symbol Name, ty_sexp Ty]
   end

fun list_mk_forall_sexp vs sexp =
  if null vs then
     sexp
  else Cons(Symbol":forall", List [List (map bvar_sexp vs), sexp])

fun list_mk_forall_term vs = list_mk_forall_sexp vs o tm_sexp

(*---------------------------------------------------------------------------*)
(* Theorems come with a name                                                 *)
(*---------------------------------------------------------------------------*)

fun mk_named_thm name thm =
 let val v = mk_var(name,bool)
 in
   THM_def |> SPEC v |> SPEC (concl thm) |> GSYM |> C EQ_MP TRUTH
 end

fun dest_named_thm thm =
 let val (c,[v,th]) = strip_comb $ concl thm
 in if same_const THM_const c then
       (fst $ dest_var v,th)
    else failwith ""
 end
 handle _ => failwith "dest_named_thm";

fun thm_sexp thm =
 let val (name,tm) = dest_named_thm thm
     val (vs,body) = strip_forall tm
 in (name,
     Cons (Symbol "defhol",
           List [Cons(Symbol ":name", Symbol name),
                 Cons(Symbol ":thm",  list_mk_forall_term vs body)]))
 end

(*---------------------------------------------------------------------------*)
(* Goals are just like theorems, except they have a ":goal" slot in place of *)
(* the ":thm" slot.                                                          *)
(*---------------------------------------------------------------------------*)

fun mk_named_goal name tm =
 let val v = mk_var(name,bool)
 in
   GOAL_def |> SPEC v |> SPEC tm |> SYM |> C EQ_MP TRUTH
 end

fun dest_named_goal thm =
 let val (c,[v,tm]) = strip_comb $ concl thm
 in if same_const GOAL_const c then
       (fst $ dest_var v,tm)
    else failwith ""
 end
 handle _ => failwith "dest_named_goal";

fun goal_sexp thm =
 let val (name,tm) = dest_named_goal thm
     val (vs,body) = strip_forall tm
 in (name,
     Cons (Symbol "defhol",
           List [Cons(Symbol ":name", Symbol name),
                 Cons(Symbol ":goal",  list_mk_forall_term vs body)]))
 end

(*---------------------------------------------------------------------------*)
(* Constant specifications require the defined constants to be supplied      *)
(*---------------------------------------------------------------------------*)

fun mk_spec clist thm =
 let val tys = map type_of clist
     val consts_var = mk_var("consts", list_mk_fun(tys,bool))
     val consts_comb = list_mk_comb(consts_var, clist)
 in
   SPEC_def |> ISPEC consts_comb |> SPEC (concl thm) |> GSYM |> C EQ_MP TRUTH
 end

fun dest_spec thm =
 let val (c,[consts,tm]) = strip_comb $ concl thm
 in if same_const SPEC_const c then
       (snd $ strip_comb consts,tm)
    else failwith ""
 end
 handle _ => failwith "dest_spec";

fun spec_sexp thm =
 let val (fns,tm) = dest_spec thm
     val {Name,...} = dest_thy_const(hd fns)
     val (vs,(left,right)) = (I##dest_eq) $ strip_forall tm
     val bare_def = Cons(Symbol"equal", List (map tm_sexp[left,right]))
 in
   (Name,
    Cons (Symbol "defhol",
          List [Cons(Symbol ":fns", List (map fns_entry fns)),
                Cons(Symbol ":defs",List [list_mk_forall_sexp vs bare_def])]))
 end

(*---------------------------------------------------------------------------*)
(* Definitions. A definition is a list of equations (clauses). A definition  *)
(* can also be a mutual recursion, introducing a list of constants.          *)
(* So a definition renders down into a list of constants paired with a list  *)
(* of clauses.                                                               *)
(*---------------------------------------------------------------------------*)

fun dest_clause_body tm = (strip_comb##I) (dest_eq tm)
fun dest_clause t = ((I ## dest_clause_body) o strip_forall) t

fun cls_qvars (vs,((c,args),r)) = vs
fun cls_lhs   (vs,((c,args),r)) = (c,args)
fun cls_rhs   (vs,((c,args),r)) = r
fun cls_const cls = fst(cls_lhs cls)

fun dest_def th =
 let open boolSyntax
     val eqns = strip_conj (concl th)
     val clauses = map dest_clause eqns
 in
   {fns = op_mk_set Term.aconv (map cls_const clauses),
    defs = clauses}
 end

(*---------------------------------------------------------------------------*)
(* Clause in a definition looks like "!vs. f a1 ... ak = rhs"                *)
(*---------------------------------------------------------------------------*)

fun clause_sexp (vs,((chd,args),r)) =
 let val {Name,Thy,Ty} = dest_thy_const chd
     val cty_sexp = Cons(Symbol"typ", List[ty_sexp Ty])
     val chd_sexp = List [Symbol Name, cty_sexp]
     val lhs_sexp = Cons(Symbol"hap*", List (chd_sexp::map tm_sexp args))
     val bare_def = Cons(Symbol"equal", List [lhs_sexp, tm_sexp r])
  in
    list_mk_forall_sexp vs bare_def
  end

fun def_sexp th =
 let val {fns,defs} = dest_def th
     val {Name,...} = dest_thy_const(hd fns)
 in (Name,
     Cons (Symbol "defhol",
           List [Cons(Symbol ":fns",   List (map fns_entry fns)),
                 Cons(Symbol ":defs",  List (map clause_sexp defs))]))
 end
 handle _ => raise ERR "def_sexp" "";

(*---------------------------------------------------------------------------*)
(* Decide between the kinds of declaration being made.                       *)
(*---------------------------------------------------------------------------*)

fun hol_sexp thm =
  def_sexp thm handle HOL_ERR _ =>
  thm_sexp thm handle HOL_ERR _ =>
  spec_sexp thm handle HOL_ERR _ =>
  goal_sexp thm handle HOL_ERR _ =>
  ("ERROR", Symbol "!<unknown construct> in hol_sexp!");

(*---------------------------------------------------------------------------*)
(* Prettyprinting for ACL2 defhol form. Adapted from                         *)
(*                                                                           *)
(*   <holdir>/portableML/HOL_sexp.sml                                        *)
(*---------------------------------------------------------------------------*)

fun break_sexp_list s =
  let fun recurse A (Cons(s1,s2)) = recurse (s1::A) s2
        | recurse A s = (List.rev A, s)
  in
    recurse [] s
  end

val translate_symbol = String.translate (String.str o Char.toLower);

fun pp_sexp t =
 let open HOLPP HOLsexp_dtype
 in
   case t
    of Symbol s => add_string (translate_symbol s)
     | String s => add_string (Portable.mlquote s)
     | Integer i => add_string (if i < 0 then "-" ^ Int.toString (~i) else Int.toString i)
     | Cons _ =>
        let val (els, last) = break_sexp_list t
        in block INCONSISTENT 1 (
             add_string "(" ::
             pr_list pp_sexp [add_break(1,0)] els @
             (case last
               of Symbol "nil" => [add_string ")"]
                | t => [add_string " .", add_break(1,0), pp_sexp t, add_string ")"])
           )
        end
 end

(*---------------------------------------------------------------------------*)
(* This taking apart of sexps and adding a little bit more formatting is     *)
(* only for presentation purposes and could be dropped.                      *)
(*---------------------------------------------------------------------------*)

fun pp_defhol s =
  let open HOLPP HOLsexp_dtype
      fun dest_def_sexp s =
          let val Cons(Symbol"defhol", Cons(fns_elt, Cons(defs_elt, Symbol"nil"))) = s
              val Cons(Symbol":fns", fns) = fns_elt
              val Cons(Symbol":defs", defs) = defs_elt
          in (fns,defs)
          end
      fun dest_named_thm_sexp s =
          let val Cons(Symbol"defhol", Cons(name_elt, Cons(thm_elt, Symbol"nil"))) = s
              val Cons(Symbol":name", Symbol n) = name_elt
              val Cons(Symbol":thm", thm) = thm_elt
          in (n,thm)
          end
      fun dest_named_goal_sexp s =
          let val Cons(Symbol"defhol", Cons(name_elt, Cons(goal_elt, Symbol"nil"))) = s
              val Cons(Symbol":name", Symbol n) = name_elt
              val Cons(Symbol":goal", goal) = goal_elt
          in (n,goal)
          end
  in case total dest_def_sexp s
      of SOME(fns,defs) =>
          block CONSISTENT 3 (
              [add_string "(defhol", add_newline,
               add_string ":fns ", block CONSISTENT 1 [pp_sexp fns], add_newline,
               add_string ":defs ", block CONSISTENT 1 [pp_sexp defs], add_string ")"])
       | NONE =>
     case total dest_named_thm_sexp s
       of SOME(name,thm) =>
          block CONSISTENT 3 (
              [add_string "(defhol", add_newline,
               add_string ":name ", block CONSISTENT 1 [pp_sexp (Symbol name)], add_newline,
               add_string ":thm ", block CONSISTENT 1 [pp_sexp thm], add_string ")"])
        | NONE =>
     case total dest_named_goal_sexp s
       of SOME(name,thm) =>
          block CONSISTENT 3 (
              [add_string "(defhol", add_newline,
               add_string ":name ", block CONSISTENT 1 [pp_sexp (Symbol name)], add_newline,
               add_string ":goal ", block CONSISTENT 1 [pp_sexp thm], add_string ")"])
        | NONE => pp_sexp s
  end

(*---------------------------------------------------------------------------*)
(* install pp_defhol in REPL                                                   *)
(*---------------------------------------------------------------------------*)

val _ =
  let fun pp depth _ (s : HOLsexp.t) = pp_defhol s
  in PolyML.addPrettyPrinter pp
  end;

(*---------------------------------------------------------------------------*)
(* For defhol files, print out each source object as a Common Lisp comment   *)
(* just above the translation of the object.                                 *)
(*---------------------------------------------------------------------------*)

fun pp_thm_as_defhol th =
    let open HOLPP
    in block CONSISTENT 0
             [add_string "#|", NL,
              add_string"   ", block CONSISTENT 3 [pp_thm th], NL,
              add_string "|#",NL,NL,
              pp_defhol (snd (hol_sexp th))]
    end

(* Following code includes time of file generation ... not sure this helps
   in establishing connection between the HOL objects and the objects that
   appear in ACL2. Maybe a GIT commit number is better.
      val timestamp = Date.toString(Date.fromTimeUniv(Time.now()))
      val pp = block CONSISTENT 0
               [add_string "; Time of generation (UTC): ",
                add_string timestamp, NL,NL,
                block CONSISTENT 0 (pr_list pp_thm_as_defhol [NL,NL] ths)]
*)

fun print_defhols ostrm ths =
  let open HOLPP
      fun outfn s = TextIO.output(ostrm,s)
      val pp = block CONSISTENT 0 (pr_list pp_thm_as_defhol [NL,NL] ths)
  in
    HOLPP.prettyPrint(outfn,78) pp
  end

val print_defhols_to_stdout = print_defhols TextIO.stdOut;

fun print_defhols_to_file fname ths =
  let val ostrm = TextIO.openOut fname
  in print_defhols ostrm ths
  end
  handle e => raise wrap_exn "HOL_to_ACL2" "print_defhols_to_file" e

end