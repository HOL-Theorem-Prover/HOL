structure Parse_support :> Parse_support =
struct

type pretype = Pretype.pretype
type preterm = Preterm.preterm
type term    = Term.term
type overload_info = term_grammar.overload_info

open HolKernel GrammarSpecials;

val ERROR = mk_HOL_ERR "Parse_support";
val ERRORloc = mk_HOL_ERRloc "Parse_support";

(*---------------------------------------------------------------------------
       Parsing environments
 ---------------------------------------------------------------------------*)

open Parse_supportENV

fun lookup_fvar(s,({free,...}:env)) = assoc s free;
fun lookup_bvar(s,({scope,...}:env)) = assoc s scope;
fun add_free(b,{scope,free,uscore_cnt,ptyE}) =
    {scope=scope, free=b::free, uscore_cnt = uscore_cnt, ptyE = ptyE}
fun add_scope(b,{scope,free,uscore_cnt,ptyE}) =
  {scope=b::scope, free=free, uscore_cnt = uscore_cnt, ptyE = ptyE};
fun new_uscore {scope,free,uscore_cnt,ptyE} =
    {scope = scope, free = free, uscore_cnt = uscore_cnt + 1, ptyE = ptyE}

type preterm_in_env = env -> Preterm.preterm * env

(*---------------------------------------------------------------------------*
 * Denotes a binding occurrence of a variable. These are treated as          *
 * functions from preterm (the body) to preterm (the abstraction).           *
 *---------------------------------------------------------------------------*)

type bvar_in_env = env -> (Preterm.preterm -> Preterm.preterm) * env

(*---------------------------------------------------------------------------*
 * Denotes a variable bound by a binder ("\\" or a constant, e.g.,           *
 * "!", "?", "@"). Hence, it takes a binder and returns a function from      *
 * the body to a preterm (plus of course, any changes to the env).           *
 *---------------------------------------------------------------------------*)

type binder_in_env = string -> bvar_in_env


(*---------------------------------------------------------------------------*
 * Top level parse terms                                                     *
 *---------------------------------------------------------------------------*)

fun make_preterm (tm_in_e : preterm_in_env) =
  fn e => let
    val (pt, env:env) = tm_in_e (fupd_ptyE (K e) empty_env)
  in
    errormonad.Some(#ptyE env, pt)
  end

(*---------------------------------------------------------------------------*
 *       Antiquotes                                                          *
 *---------------------------------------------------------------------------*)

fun make_aq l tm (e:env) =
  let
    open errormonad
    fun traverse localbvs t e =
      case dest_term t of
          VAR(nm, ty) =>
          if HOLset.member(localbvs, t) then e
          else
            let
              val pty = Pretype.fromType ty
            in
              case assoc1 nm (#scope e) of
                  NONE =>
                  (case assoc1 nm (#free e) of
                       NONE => fupd_free (cons (nm,pty)) e
                     | SOME (_, pty') =>
                       case Pretype.unify pty pty' (#ptyE e) of
                           Some(ptyE', ()) => fupd_ptyE (K ptyE') e
                         | Error e => raise AQincompat{
                                       nm = nm, aqty = ty, loc = l, fv = true,
                                       unify_error = e })
               | SOME (_, pty') =>
                 (case Pretype.unify pty pty' (#ptyE e) of
                      Some(ptyE', ()) => fupd_ptyE (K ptyE') e
                    | Error e => raise AQincompat {
                                  nm = nm, aqty = ty, loc = l, fv = false,
                                  unify_error = e })
            end
        | CONST _ => e
        | COMB(f,x) => traverse localbvs x (traverse localbvs f e)
        | LAMB(bv, bod) => traverse (HOLset.add(localbvs,bv)) bod e
  in
    (Preterm.Antiq{Tm = tm, Locn = l}, traverse empty_tmset tm e)
  end

(*---------------------------------------------------------------------------*
 * Generating fresh constant instances                                       *
 *---------------------------------------------------------------------------*)

fun ptylift (m : 'a Pretype.in_env) (e : env) : 'a * env =
  let
    open errormonad
    val {scope,free,uscore_cnt,ptyE} = e
  in
    case m ptyE of
      Error e => raise typecheck_error.mkExn e
    | Some (e', a) => (a, {scope=scope,free=free,uscore_cnt=uscore_cnt,ptyE=e'})
  end


fun gen_thy_const l (thy,s) E = let
  open Term
  val c = prim_mk_const{Name=s, Thy=thy}
  val ptym = type_of c |> Pretype.fromType |> Pretype.rename_typevars []
  val (pty,E') = ptylift ptym E
in
  (Preterm.Const {Name=s, Thy=thy, Locn=l, Ty=pty}, E')
end

(*---------------------------------------------------------------------------
 * Binding occurrences of variables
 *---------------------------------------------------------------------------*)

fun make_binding_occ lAbs lVar s E = let
  open Preterm
  val (ntv,E') = ptylift Pretype.new_uvar E
  val E'' = add_scope((s,ntv),E')
in
  ((fn b => Abs{Bvar=Var{Name=s, Ty=ntv, Locn=lVar},Body=b,
                Locn=locn.near lAbs}), E'')
end

fun make_aq_binding_occ lAbs lVar aq E = let
  val (v as (Name,Ty)) = Term.dest_var aq
  val pty = Pretype.fromType Ty
  val v' = {Name=Name, Ty=Pretype.fromType Ty, Locn=lVar}
  val E' = add_scope ((Name,pty),E)
  open Preterm
in
  ((fn b => Abs{Bvar=Var v', Body=b, Locn=lAbs}), E')
end


(*---------------------------------------------------------------------------
 * Free occurrences of variables.
 *---------------------------------------------------------------------------*)

fun all_uscores s = let
  fun check i = i < 0 orelse (String.sub(s,i) = #"_" andalso check (i - 1))
in
  check (size s - 1)
end

fun make_free_var l (s,E) = let
  open Preterm
  fun fresh (s,E) = let
    val (tyv, E') = ptylift Pretype.new_uvar E
  in
    (Var{Name = s, Ty = tyv, Locn = l}, add_free((s,tyv), E'))
  end
in
  if all_uscores s then fresh ("_"^Int.toString (#uscore_cnt E), new_uscore E)
  else (Var{Name=s, Ty=lookup_fvar(s,E), Locn=l}, E)
       handle HOL_ERR _ => fresh(s,E)
end

(*---------------------------------------------------------------------------
 * Bound occurrences of variables.
 *---------------------------------------------------------------------------*)

fun make_bvar l (s,E) = (Preterm.Var{Name=s, Ty=lookup_bvar(s,E), Locn=l}, E);

(* ----------------------------------------------------------------------
     Treatment of overloaded identifiers
 ---------------------------------------------------------------------- *)

fun gen_overloaded_const oinfo l s E =
 let
   open Overload Pretype
   val opinfo = valOf (info_for_name oinfo s)
         handle Option => raise Fail "gen_overloaded_const: invariant failure"
 in
  case #actual_ops opinfo of
    [t] =>
      if is_const t then let
          val {Name,Thy,Ty} = dest_thy_const t
          val (pty, E') = ptylift (rename_typevars [] (fromType Ty)) E
        in
          (Preterm.Const{Name=Name, Thy=Thy, Locn=l, Ty = pty}, E')
        end
      else let
          val fvs = free_vars t
          val tyfvs = List.foldl (fn (t, acc) => Lib.union (type_vars_in_term t)
                                                           acc)
                                 []
                                 fvs
          val (ptm, E') =
              ptylift (Preterm.term_to_preterm (map dest_vartype tyfvs) t) E
        in
          (Preterm.Pattern{Ptm = ptm, Locn = l}, E')
        end
  | otherwise => let
      val base_pretype0 = fromType (#base_type opinfo)
      val (new_pretype, E') = ptylift (rename_typevars [] base_pretype0) E
    in
      (Preterm.Overloaded{Name = s, Ty = new_pretype, Info = opinfo, Locn = l},
       E')
    end
 end


(*---------------------------------------------------------------------------
 * Identifiers work as follows: look for the string in the scope;
 * if it's there, put the bound var.
 * Failing that, check to see if the string is a known constant.
 *
 * If so, it will have an "overloading" entry.  Look this up and proceed.
 *
 * If not, it might be trying to be a record selection; these are
 * necessarily constants (and overloaded) so we can complain at this point.
 *
 * Otherwise, it might be a string literal.  Try and make one, if this
 * fails because stringTheory is not loaded, fail.
 *
 * If none of the above, then it's a free variable.
 *
 * Free vars are placed in the "free" part of the environment; this is a
 * set. Bound vars are placed at the front of the "scope". When we come out
 * of an Abs, we return the scope in effect when entering the Abs, but the
 * "free"s include new ones found in the body of the Abs.
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
    Making preterm string literals.
 ---------------------------------------------------------------------------*)

local
  fun mk_chr ctm tm = mk_comb(ctm, tm)
  fun mk_string stm (tm1,tm2) = list_mk_comb(stm, [tm1, tm2])
  fun mk_numeral n =
      Literal.gen_mk_numeral
        {mk_comb = mk_comb,
         ZERO = prim_mk_const{Name = "0", Thy = "num"},
         ALT_ZERO = prim_mk_const{Name = "ZERO", Thy = "arithmetic"},
         NUMERAL = prim_mk_const {Name="NUMERAL",Thy="arithmetic"},
         BIT1 = prim_mk_const {Name="BIT1", Thy="arithmetic"},
         BIT2 = prim_mk_const {Name="BIT2", Thy="arithmetic"}} n
  fun fromMLC ctm c = mk_chr ctm (mk_numeral (Arbnum.fromInt (Char.ord c)))
in
fun make_string_literal l s =
    if not (mem "string" (ancestry "-")) andalso
       current_theory() <> "string"
    then
      Raise (ERRORloc "make_string_literal" l
                      ("String literals not allowed - "^
                       "load \"stringTheory\" first."))
    else let
        val char_ty = mk_thy_type {Tyop = "char", Thy = "string", Args = []}
        val str_ty = mk_thy_type {Tyop = "list", Thy = "list", Args = [char_ty]}
        val stm = mk_thy_const {Name = "CONS", Thy = "list",
                                Ty = char_ty --> str_ty --> str_ty}
        val ctm = prim_mk_const {Name = "CHR", Thy = "string"}
        val etm = mk_thy_const{Name = "NIL", Thy = "list",
                               Ty = str_ty}
      in
        Preterm.Antiq {Locn = l,
                       Tm = Literal.mk_string_lit
                              {mk_string = mk_string stm,
                               emptystring = etm,
                               fromMLchar = fromMLC ctm}
                              (String.substring(s,1,String.size s - 2))}
      end
fun make_char_literal l s =
    if not (mem "string" (ancestry "-")) andalso
       current_theory() <> "string"
    then
      raise (ERRORloc "make_char_literal" l
                      "Char literals not allowed - \
                      \load \"stringTheory\" first.")
    else let
        val ctm = prim_mk_const {Name = "CHR", Thy = "string"}
        val n_t = mk_numeral (Arbnum.fromInt (Char.ord (String.sub(s,2))))
      in
        Preterm.Antiq{Locn = l, Tm = mk_chr ctm n_t}
      end
end (* local *)

(*---------------------------------------------------------------------------
    "make_qconst" ignores overloading and visibility information. The
    idea is that if we ask to make a long identifier, it should be
    treated as visible.
 ---------------------------------------------------------------------------*)

fun make_qconst l (p as (thy,s)) = gen_thy_const l p

fun make_atom oinfo l s E =
 make_bvar l (s,E) handle HOL_ERR _
  =>
  if Overload.is_overloaded oinfo s then gen_overloaded_const oinfo l s E
  else
    case List.find (fn rfn => String.isPrefix rfn s)
                   [recsel_special, recupd_special, recfupd_special] of
      NONE => if Lexis.is_string_literal s then (make_string_literal l s, E)
              else if Lexis.is_char_literal s then (make_char_literal l s, E)
              else make_free_var l (s, E)
    | SOME rfn =>
        raise ERRORloc "make_atom" l
                       ("Record field "^String.extract(s, size rfn, NONE)^
                        " not registered")

(*---------------------------------------------------------------------------
 * Combs
 *---------------------------------------------------------------------------*)

fun list_make_comb l (tm1::(rst as (_::_))) E =
     rev_itlist (fn tm => fn (trm,e) =>
        let val (tm',e') = tm e
        in (Preterm.Comb{Rator = trm, Rand = tm', Locn=l}, e') end)     rst (tm1 E)
  | list_make_comb l _ _ = raise ERRORloc "list_make_comb" l "insufficient args";

(*---------------------------------------------------------------------------
 * Constraints
 *---------------------------------------------------------------------------*)

fun make_constrained l tm ty E = let
  val (tm',E') = tm E
in
  (Preterm.Constrained{Ptm = tm', Ty = ty, Locn = l}, E')
end;


(*---------------------------------------------------------------------------

  Abstractions, qualified abstractions, and vstructs.

  The thing to know about parsing abstractions is that an abstraction is
  a function from the string identifying the binder to an env to a
  pair. The first member of the pair is a function that will take the
  body of the abstraction and produce a lambda term, essentially by
  clapping on whatever variables, or applying whatever constants
  necessary. The second member of the pair is the environment previous
  to entering the abstraction plus whatever new free variables were
  found in the body of the abstraction.

  We could just return (F tm', E), except that we may add free variables
  found in tm to E.
 ----------------------------------------------------------------------------*)

fun bind_term _ alist tm (E as {scope=scope0,...}:env) : (preterm*env) = let
  fun itthis a (e,f) = let
    val (g,e') = a e
  in
    (e', f o g)
  end
  val (E',F) = rev_itlist itthis alist (E,I)
  val (tm',({free=free1,uscore_cnt=uc',ptyE,...}:env)) = tm E'
in
  (F tm', {scope=scope0,free=free1,uscore_cnt=uc',ptyE=ptyE})
end


(*---------------------------------------------------------------------------
 * For restricted binders. Adding a pair "(B,R)" to this list, if "B" is the
 * name of a binder and "R" is the name of a constant, will enable parsing
 * of terms with the form
 *
 *     B <varstruct list>::<restr>. M
 *---------------------------------------------------------------------------*)

local val restricted_binders = ref ([] : (string * string) list)
in
fun binder_restrictions() = !restricted_binders
fun associate_restriction l (p as (binder_str,const_name)) =
  case (Lib.assoc1 binder_str (!restricted_binders)) of
    NONE => restricted_binders := p :: !restricted_binders
  | SOME _ =>
      raise ERRORloc "restrict_binder" l
        ("Binder "^Lib.quote binder_str^" is already restricted")

fun delete_restriction l binder =
 restricted_binders :=
  Lib.set_diff (!restricted_binders)
         [(binder,Lib.assoc binder(!restricted_binders))]
  handle HOL_ERR _
   => raise ERRORloc "delete_restriction" l (Lib.quote binder^" is not restricted")
end;

fun restr_binder l s =
   assoc s (binder_restrictions()) handle HOL_ERR _
   => raise ERRORloc "restr_binder" l
                      ("no restriction associated with "^Lib.quote s)

fun split ty =
  case ty of
    Pretype.Tyop{Thy="pair",Tyop = "prod",Args} => Args
  | _ => raise ERROR "split" "not a product";


local open Preterm
in
fun cdom M [] = M
  | cdom (Abs{Bvar,Body,Locn}) (ty::rst) =
       Abs{Bvar = Constrained{Ptm=Bvar,Ty=ty,Locn=Locn}, Body = cdom Body rst, Locn = Locn}
  | cdom (Comb{Rator as Const{Name="UNCURRY",...},Rand,Locn}) (ty::rst) =
       Comb{Rator=Rator, Rand=cdom Rand (split ty@rst), Locn=Locn}
  | cdom x y = raise ERRORloc "cdom" (Preterm.locn x) "missing case"
end;

fun cdomf (f,e) ty = ((fn tm => cdom (f tm) [ty]), e)

fun make_vstruct oinfo l bvl tyo E = let
  open Preterm
  fun loop ([v],E) = v E
    | loop ((v::rst),E) = let
        val (f,e) = v E
        val (F,E') = loop(rst,e)
        val (uc_t, E'') = gen_overloaded_const oinfo l "UNCURRY" E'
      in
        ((fn b => Comb{Rator=uc_t, Rand=f(F b),Locn=l}), E'')
      end
    | loop _ = raise ERRORloc "make_vstruct" l "impl. error, empty vstruct"
in
  case tyo of
    NONE    => loop(bvl,E)
  | SOME ty => cdomf (hd bvl E) ty
end


(*---------------------------------------------------------------------------
 * Let bindings
 *---------------------------------------------------------------------------*)
fun make_let oinfo l bindings tm (env:env) = let
  open Preterm
  fun itthis (bvs, arg) {body_bvars,args,E} = let
    val (b,rst) = (hd bvs,tl bvs)
    val (arg',E') =
        case rst of [] => arg E | L => bind_term l L arg E
  in
    {body_bvars = b::body_bvars, args=arg'::args, E=E'}
  end
  val {body_bvars, args, E} =
      itlist itthis bindings {body_bvars=[], args=[], E=env}
  val (core,E') = bind_term l body_bvars tm E
  fun rev_itthis arg (core, E) =
    let
      val (let_t, E') = gen_overloaded_const oinfo l "LET" E
    in
      (Comb{Rator= Comb{Rator=let_t, Rand=core,Locn=l},Rand=arg,Locn=l},
       E')
    end
in
  rev_itlist rev_itthis args (core, E')
end
    handle HOL_ERR _ => raise ERRORloc "make_let" l "bad let structure";

fun make_set_const oinfo l fname s E =
 gen_overloaded_const oinfo l s E
  handle HOL_ERR _
    => raise ERRORloc fname l ("The theory "^Lib.quote "pred_set"^" is not loaded");


(*---------------------------------------------------------------------------
 * Set abstractions {tm1 | tm2}. The complicated rigamarole at the front is
 * so that new type variables only get made once per free var, although we
 * compute the free vars for tm1 and tm2 separately.
 *
 * You can't make a set unless the theory of sets is an ancestor.
 * The calls to make_set_const ensure this.
 *
 * Warning: apt not to work if you want to "antiquote in" free variables that
 * will subsequently get bound in the set abstraction.
 *---------------------------------------------------------------------------*)
fun update_ptyE (old:env) = fupd_ptyE (K (#ptyE old))

fun make_set_abs oinfo l (tm1,tm2) (E as {scope=scope0,...}:env) = let
  val (_,(e1:env)) = tm1 (update_ptyE E empty_env)
                     (* used to find names of free vars in tm1, but is also
                        the basis for calculating the bound vars in the final
                        preterm so we need its pty-env to be accurate *)
  val (_,(e2:env)) = tm2 empty_env (* only used to get 2nd set of free vars *)
  val (_,(e3:env)) = tm2 e1 (* link types and get complete set of free vars *)
  val tm1_fv_names = map fst (#free e1)
  val tm2_fv_names = map fst (#free e2)
  val fv_names = if null tm1_fv_names then tm2_fv_names else
                 if null tm2_fv_names then tm1_fv_names else
                 intersect tm1_fv_names tm2_fv_names
  val init_fv = #free e3 (* candidate bound names *)
in
  case filter (fn (name,_) => mem name fv_names) init_fv of
    [] => raise ERRORloc "make_set_abs" l "no free variables in set abstraction"
  | quants =>
    let
      open Preterm
      val quants' = map
                      (fn (bnd as (Name,Ty)) =>
                          fn E =>
                             ((fn b => Abs{Bvar=Var{Name=Name,Ty=Ty,Locn=l},
                                           Body=b, Locn=l}),
                              add_scope(bnd,E)))
                      (rev quants) (* make_vstruct expects reverse occ. order *)
      fun comma E = gen_overloaded_const oinfo l "," E
    in
      list_make_comb l
                     [(make_set_const oinfo l "make_set_abs" "GSPEC"),
                      (bind_term l
                                 [make_vstruct oinfo l quants' NONE]
                                 (list_make_comb l [comma,tm1,tm2]))]
                     (update_ptyE e3 E)
    end
end

(* ----------------------------------------------------------------------
    case arrow

    Free variables in the first should bind in the second
   ---------------------------------------------------------------------- *)

fun make_case_arrow oinfo loc tm1 tm2 (E : env) = let
  val (ptm1, e1 : env) = tm1 (fupd_ptyE (K (#ptyE E)) empty_env)
  val (arr, E') =
      make_qconst loc
                  ("bool", GrammarSpecials.case_arrow_special)
                  (fupd_ptyE (K (#ptyE e1)) E)
  fun mk_bvar (bv as (n,ty)) E = ((fn t => t), add_scope(bv,E))
  val qs = map mk_bvar (#free e1)
  val (ptm2, E'') = bind_term loc qs tm2 E'
in
  (Preterm.Comb{Rator = Preterm.Comb{Locn=loc,Rator = arr, Rand = ptm1},
                Rand = ptm2,
                Locn = loc}, E'')
end


(*---------------------------------------------------------------------------
 * Sequence abstractions [| tm1 | tm2 |].
 *
 * You can't make a llist unless llistTheory is an ancestor.
 * The call to make_seq_comp_const ensure this.
 *---------------------------------------------------------------------------*)
(*
fun make_seqComp_const l fname s E =
 (gen_const l s, E)
  handle HOL_ERR _
    => raise ERRORloc fname l ("The theory "^Lib.quote "llist"^" is not loaded");

fun make_seq_abs l (tm1,tm2) (E as {scope=scope0,...}:env) =
   let val (_,(e1:env)) = tm1 empty_env
       val (_,(e2:env)) = tm2 empty_env
       val (_,(e3:env)) = tm2 e1
       val tm1_fv_names = map fst (#free e1)
       val tm2_fv_names = map fst (#free e2)
       val fv_names = if null tm1_fv_names then tm2_fv_names else
                      if null tm2_fv_names then tm1_fv_names else
                      intersect tm1_fv_names tm2_fv_names
       val init_fv = #free e3
   in
   case filter (fn (name,_) => mem name fv_names) init_fv
     of [] => raise ERRORloc "make_seq_abs" l "no free variables in set abstraction"
      | quants =>
         let val quants' = map
                (fn (bnd as (Name,Ty)) =>
                     (fn (s:string) => fn E =>
                       ((fn b => Preterm.Abs{Bvar=Preterm.Var{Name=Name,Ty=Ty,Locn=l(*ugh*)},
                                             Body=b, Locn=l}),
                                add_scope(bnd,E))))
               (rev quants) (* make_vstruct expects reverse occ. order *)
         in list_make_comb l
               [(make_seqComp_const l "make_seq_abs" "SeqComp"),
                (bind_term l "\\" [make_vstruct l quants' NONE]
                          (list_make_comb l [make_const l ",",tm1,tm2]))] E
         end
   end;
*)

end; (* Parse_support *)
