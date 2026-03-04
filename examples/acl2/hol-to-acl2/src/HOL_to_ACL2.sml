structure HOL_to_ACL2 :> HOL_to_ACL2 =
struct

open HolKernel boolLib bossLib Elim_Lambda
     pairTheory listTheory hol_to_acl2Theory

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
 handle _ => raise ERR "dest_named_thm" "";

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
 handle _ => raise ERR "dest_named_goal" "";

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
 handle _ => raise ERR "dest_spec" "";

(*---------------------------------------------------------------------------*)
(* Get rid of lambdas in a term/theorem by creating definitions for them.    *)
(* Also known as "lambda lifting".                                           *)
(*---------------------------------------------------------------------------*)

fun unlambda_term t =
  case Elim_Lambda.lift_lambdas t
    of NONE => ([],REFL t)
     | SOME (equiv,defs) => (defs, equiv)

fun unlambda thm =
  case Elim_Lambda.lift_lambdas (concl thm)
    of NONE => ([],thm)
     | SOME (equiv,defs) => (defs, EQ_MP equiv thm)

(*---------------------------------------------------------------------------*)
(* Top-level universal quantifiers shouldn't be unlambda'ed. A special case  *)
(* is conjunctions of the form                                               *)
(*                                                                           *)
(*   (!x1 ... xn. P1 x1 .. xn) /\ ... /\ (!y1 ... yk. Pj y1 ... yk)          *)
(*                                                                           *)
(* Taken naively, all the universals would get unlambda'ed, but the handling *)
(* on the ACL2(zfc) side treats each conjunct separately, and the top-level  *)
(* universals for each conjunct get added to a variable context (I think)    *)
(* so unlambda should not be done.                                           *)
(*---------------------------------------------------------------------------*)

fun unlambda_conj thm =
  case CONJUNCTS thm
    of [] => raise ERR "unlambda_conj" "empty conjuncts (error!)"
     | conjs =>
       let val unconjs = map unlambda conjs
           val (locals,unlambs) = unzip unconjs
       in (List.concat locals, LIST_CONJ unlambs) end

(*---------------------------------------------------------------------------*)
(* Lambda-lifting means that entities destined for translation to defhol     *)
(* format aren't single objects anymore, but bundles of auxiliary            *)
(* definitions plus the lifted entity (when lifting is needed). There is     *)
(* also an extra complication arising from lifting recursive definitions.    *)
(*                                                                           *)
(* Elimination of lambda expressions from a definition happens after the     *)
(* definition is made. The new lambda-eliminator definitions can introduce   *)
(* what look to be mutual recursions. Consider                               *)
(*                                                                           *)
(*   fact n = case n of 0 => 1 | _ => n * fact (n - 1)                       *)
(*                                                                           *)
(* The surface syntax conceals a RHS that is actually                        *)
(*                                                                           *)
(*   num_CASE n 1 (\v1. n * fact (n-1))                                      *)
(*                                                                           *)
(* Lambda lifting creates the auxiliary definition                           *)
(*                                                                           *)
(*   Lam_31 n v1 = n * fact (n − 1)                                          *)
(*                                                                           *)
(* and the lifted version of the original:                                   *)
(*                                                                           *)
(*   fact n = num_CASE n 1 (Lam_31 n)                                        *)
(*                                                                           *)
(* It seems that we have created a mutual recursion between "fact" and       *)
(* "Lam_31"! Should we be worried? I don't think so. This relationship has   *)
(* been created post-definition and shouldn't be taken as being part of the  *)
(* recursion equations to be solved.                                         *)
(*                                                                           *)
(* On the ACL2(zfc) side, the attitude (I think) is that the HOL-side        *)
(* definition event has introduced some constants and asserted some axioms,  *)
(* and only those steps have to be replicated on the ACL2(zfc) side.         *)
(*                                                                           *)
(* But how exactly? This is currently to be discussed with Matt, but two     *)
(* possibilities come to mind. (1) combine the auxiliary definition(s) and   *)
(* the lifted original into one defhol form or (2) create one defhol per     *)
(* definition (so one for "Lam_31" and one for "fact") and add extra         *)
(* signature information on the first defhol, ie, if "Lam_31" is defined     *)
(* first, its :fns field will hold both the "Lam_31" constant and the "fact" *)
(* constant.                                                                 *)
(*                                                                           *)
(* For now I am going with possibility 1.                                    *)
(*---------------------------------------------------------------------------*)

datatype bundle
  = THM  of string * thm * (thm list * thm) option
  | GOAL of string * term * (thm list * term) option
  | DEF  of thm * (thm list * thm list * thm) option
  | SPEC of term list * thm * (thm list * thm list * thm) option

val head = fst o strip_comb
fun dest_atom t = dest_var t handle _ => dest_const t
val eqn_head = head o lhs o snd o strip_forall
fun conj_heads conj = op_mk_set aconv (map eqn_head (strip_conj conj))

(*---------------------------------------------------------------------------*)
(* Normalize possibly mutually recursive equations. Most of the code in      *)
(* sort_defs builds to a call to Defn.sort_eqns, followed by a phase of      *)
(* figuring out which, if any, auxiliary eqns have been dragged into a       *)
(* clique with the lifted original.                                          *)
(*---------------------------------------------------------------------------*)

fun sort_defs (aux,lifted) =
 let val aux_eqns = map concl aux
     val aux_conjs = List.concat (map strip_conj aux_eqns)
     val bare_aux_conjs = map (snd o strip_forall) aux_conjs
     val lifted_eqns = concl lifted
     val bare_lifted_conjs = map (snd o strip_forall) (strip_conj lifted_eqns)
     val aux_consts = map eqn_head bare_aux_conjs
     val lifted_consts = op_mk_set aconv (map eqn_head bare_lifted_conjs)
     val aux_vars = map (mk_var o dest_const) aux_consts
     val lifted_vars = map (mk_var o dest_const) lifted_consts
     val theta = map2 (curry op |->) (aux_consts @ lifted_consts) (aux_vars @ lifted_vars)
     val all_veqns = map (subst theta) (bare_aux_conjs @ bare_lifted_conjs)
     val sorted = Defn.sort_eqns (list_mk_conj all_veqns)
     val sorted_heads = map conj_heads sorted
     val lifted_vars' = first (op_mem aconv (hd lifted_vars)) sorted_heads
     val aux_vars' = op_set_diff aconv aux_vars lifted_vars'
     val aux_vars'_names = map (fst o dest_var) aux_vars'
     fun is_aux' th = mem (fst $ dest_atom $ eqn_head $ concl th) aux_vars'_names
     val (aux',aux'') = partition is_aux' aux
 in
   (aux', aux'')
 end handle e => raise wrap_exn "HOL_to_ACL2" "sort_defs" e;

fun thm_bundle name thm =
    let val (aux,th') = unlambda_conj thm
        val opt = if null aux then NONE else SOME(aux,th')
    in THM (name, thm, opt) end

(* TODO: think about whether the equiv theorem should be stored *)
fun goal_bundle name tm =
    let val (aux,equiv) = unlambda_term tm
        val opt = if null aux then NONE else SOME(aux,rhs(concl equiv))
    in GOAL (name, tm, opt) end

fun def_bundle thm =
    let val (aux,def') = unlambda_conj thm
    in if null aux then
          DEF (thm, NONE)
       else
        let val (aux', aux'') = sort_defs (aux,def')
        in DEF (thm, SOME(aux', aux'', def')) end
    end

fun spec_bundle consts thm =
    let val (aux,thm') = unlambda_conj thm
    in if null aux then
          SPEC(consts,thm,NONE)
       else
        let val (aux', aux'') = sort_defs (aux,thm')
        in SPEC (consts, thm, SOME(aux', aux'', thm')) end
    end

fun pp_const c =
    let open HOLPP
        val (n,ty) = dest_const c
    in block CONSISTENT 0
          [add_string n, add_string " ", pp_type ty] end

fun pp_bundle (THM(name,orig,NONE)) =
    let open HOLPP
    in block CONSISTENT 0
         [add_string "#|", NL,
          add_string ("Theorem: "^name), NL, NL,
          add_string"   ", block CONSISTENT 3 [pp_thm orig], NL,
          add_string "|#",NL] end
  | pp_bundle (THM(name,orig,SOME(aux,final))) =
    let open HOLPP
    in block CONSISTENT 0
         [add_string "#|", NL,
          add_string ("Theorem: "^name), NL, NL,
          add_string"   ", block CONSISTENT 3 [pp_thm orig], NL,NL,
          add_string "Auxiliary definitions:", NL, NL,
          add_string"   ",
          block CONSISTENT 3 (pr_list pp_thm [NL] aux), NL,NL,
          add_string "Lifted theorem:", NL,NL,
          add_string"   ",block CONSISTENT 3 [pp_thm final], NL,
          add_string "|#",NL] end
  | pp_bundle (GOAL(name,orig,NONE)) =
    let open HOLPP
    in block CONSISTENT 0
         [add_string "#|", NL,
          add_string ("Goal: "^name), NL, NL,
          add_string"   ", block CONSISTENT 3 [pp_term orig], NL,
          add_string "|#",NL] end
  | pp_bundle (GOAL(name,orig,SOME(defs,final))) =
    let open HOLPP
    in block CONSISTENT 0
         [add_string "#|", NL,
          add_string ("Goal: "^name), NL, NL,
          add_string"   ", block CONSISTENT 3 [pp_term orig], NL,NL,
          add_string "Auxiliary definitions:", NL, NL,
          add_string"   ",
          block CONSISTENT 0 (pr_list pp_thm [NL] defs), NL,NL,
          add_string "Lifted goal:", NL,NL,
          add_string"   ", block CONSISTENT 3 [pp_term final], NL,
          add_string "|#",NL] end
  | pp_bundle (DEF(orig,NONE)) =
    let open HOLPP
    in block CONSISTENT 0
         [add_string "#|", NL,
          add_string "Definition:", NL,NL,
          add_string"   ",
          block CONSISTENT 3 [pp_thm orig], NL,
          add_string "|#",NL] end
  | pp_bundle (DEF(orig,SOME(aux,aux',final))) =
    let open HOLPP
    in block CONSISTENT 0
        ([add_string "#|", NL,
          add_string "Original definition:", NL, NL,
          add_string"   ",
          block CONSISTENT 3 [pp_thm orig], NL, NL]
          @
          (if not $ null aux then
              [add_string "Auxiliary definitions:", NL, NL,
               add_string"   ",
               block CONSISTENT 3 (pr_list pp_thm [NL] aux), NL,NL]
           else [])
          @
          (if not $ null aux' then
              [add_string "Auxiliary definitions (pseudo recursive):", NL, NL,
               add_string"   ",
               block CONSISTENT 3 (pr_list pp_thm [NL] aux'), NL,NL]
           else [])
          @
          [add_string "Lifted definition:", NL,NL,
           add_string"   ", block CONSISTENT 3 [pp_thm final],NL,
           add_string "|#",NL]
         )
    end
  | pp_bundle (SPEC(consts,orig,NONE)) =
    let open HOLPP
    in block CONSISTENT 0
         [add_string "#|", NL,
          add_string "Constant specification:", NL, NL,
          add_string"   ",
          block CONSISTENT 3 (pr_list pp_const [NL] consts), NL,NL,
          add_string"   ", block CONSISTENT 3 [pp_thm orig], NL,
          add_string "|#",NL] end
  | pp_bundle (SPEC(consts,orig,SOME(aux,aux',final))) =
    let open HOLPP
    in block CONSISTENT 0
         ([add_string "#|", NL,
           add_string "Original constant specification:", NL, NL,
           add_string"   ",
           block CONSISTENT 3 (pr_list pp_const [NL] consts), NL,NL,
           add_string"   ", block CONSISTENT 3 [pp_thm orig], NL,NL]
          @
          (if not $ null aux then
              [add_string "Auxiliary definitions:", NL, NL,
               add_string"   ",
               block CONSISTENT 3 (pr_list pp_thm [NL] aux), NL,NL]
           else [])
          @
          (if not $ null aux' then
              [add_string "Auxiliary definitions (pseudo recursive):", NL, NL,
               add_string"   ",
               block CONSISTENT 3 (pr_list pp_thm [NL] aux'), NL,NL]
           else [])
          @
          [add_string "Lifted specification:", NL,NL,
           add_string"   ", block CONSISTENT 3 [pp_thm final],NL,
           add_string "|#",NL]
         ) end

val _ =
  let fun pp depth _ (b : bundle) = pp_bundle b
  in PolyML.addPrettyPrinter pp
  end;

(*---------------------------------------------------------------------------*)
(* Types                                                                     *)
(*---------------------------------------------------------------------------*)

fun tyvar_name tyv =
  let val s = dest_vartype tyv
  in String.substring(s,1,String.size s - 1) end

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

fun strip_cond tm =
  if not (is_cond tm) then
    ([],tm)
  else
    let val (t1,t2,t3) = dest_cond tm
        val (pairs,tn) = strip_cond t3
    in ((t1,t2)::pairs,tn)
    end

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
(* Prettyprinting for sexps. Adapted from <holdir>/portableML/HOL_sexp.sml   *)
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
(* Prettyprint defhol sexp                                                   *)
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

fun bundle_to_sexps (THM(name,orig,NONE)) =
      [thm_sexp (mk_named_thm name orig)]
  | bundle_to_sexps (THM(name,orig,SOME(aux,lifted))) =
      map def_sexp aux @ [thm_sexp (mk_named_thm name lifted)]
  | bundle_to_sexps (GOAL(name,orig,NONE)) =
      [goal_sexp (mk_named_goal name orig)]
  | bundle_to_sexps (GOAL(name,orig,SOME(aux,lifted))) =
      map def_sexp aux @ [goal_sexp (mk_named_goal name lifted)]
  | bundle_to_sexps (DEF(orig,NONE)) =
      [def_sexp orig]
  | bundle_to_sexps (DEF(orig,SOME(aux,pseuds,lifted))) =
      let val def = LIST_CONJ (pseuds @ CONJUNCTS lifted)
      in map def_sexp aux @ [def_sexp def] end
  | bundle_to_sexps (SPEC(consts,orig,NONE)) =
      [spec_sexp (mk_spec consts orig)]
  | bundle_to_sexps (SPEC(consts,orig,SOME(aux,pseuds,lifted))) =
      let val spec = LIST_CONJ (pseuds @ CONJUNCTS lifted)
          val pconsts = map (eqn_head o concl) pseuds
          val allconsts = consts @ pconsts
      in map def_sexp aux @ [spec_sexp (mk_spec allconsts spec)] end

(*---------------------------------------------------------------------------*)
(* install pp_defhol in REPL                                                 *)
(*---------------------------------------------------------------------------*)

val _ =
  let fun pp depth _ (s : HOLsexp.t) = pp_defhol s
  in PolyML.addPrettyPrinter pp
  end;

(*---------------------------------------------------------------------------*)
(* For defhol files, print out each source object as a Common Lisp comment   *)
(* just above the translation of the object.                                 *)
(*---------------------------------------------------------------------------*)

fun pp_bundle_as_defhols bundle =
    let open HOLPP
        val header = pp_bundle bundle
        val sexps = map snd (bundle_to_sexps bundle)
        val defhols = pr_list pp_defhol [NL,NL] sexps
    in block CONSISTENT 0 (header :: NL :: defhols)
    end

(*---------------------------------------------------------------------------*)
(* Output bundles                                                            *)
(*---------------------------------------------------------------------------*)

fun print_bundles ostrm bs =
  let open HOLPP
      fun outfn s = TextIO.output(ostrm,s)
      val pp = block CONSISTENT 0 (pr_list pp_bundle_as_defhols [NL,NL] bs)
  in
    HOLPP.prettyPrint(outfn,78) pp
  end

val print_bundles_to_stdout = print_bundles TextIO.stdOut;

fun print_bundles_to_file fname bundles =
  let val ostrm = TextIO.openOut fname
  in print_bundles ostrm bundles
  end
  handle e => raise wrap_exn "HOL_to_ACL2" "print_bundles_to_file" e

(* Following code includes time of file generation ... not sure this helps
   in establishing connection between the HOL objects and the objects that
   appear in ACL2. Maybe a GIT commit number is better.
      val timestamp = Date.toString(Date.fromTimeUniv(Time.now()))
      val pp = block CONSISTENT 0
               [add_string "; Time of generation (UTC): ",
                add_string timestamp, NL,NL,
                block CONSISTENT 0 (pr_list pp_thm_as_defhol [NL,NL] ths)]
*)

end
