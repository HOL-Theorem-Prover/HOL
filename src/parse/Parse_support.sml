structure Parse_support :> Parse_support =
struct

type pretype = Pretype.pretype
type preterm = Preterm.preterm
type term    = Term.term

open HolKernel GrammarSpecials;

val ERROR = mk_HOL_ERR "Parse_support";

(*---------------------------------------------------------------------------
       Parsing environments
 ---------------------------------------------------------------------------*)

type env = {scope : (string * pretype) list,
            free  : (string * pretype) list};

fun lookup_fvar(s,({free,...}:env)) = assoc s free;
fun lookup_bvar(s,({scope,...}:env)) = assoc s scope;
fun add_free(b,{scope,free}) = {scope=scope, free=b::free}
fun add_scope(b,{scope,free}) = {scope=b::scope, free=free};

val empty_env = {scope=[], free=[]};

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

fun make_preterm tm_in_e = fst(tm_in_e empty_env)

(*---------------------------------------------------------------------------*
 *       Antiquotes                                                          *
 *---------------------------------------------------------------------------*)

fun make_aq tm {scope,free} = let
  open Term Preterm
  fun from ltm (E as (lscope,scope,free)) =
    case ltm of
      VAR (v as (Name,Ty)) =>
       let val pty = Pretype.fromType Ty
           val v' = {Name=Name, Ty=pty}
       in if mem v' lscope then (Var v', E)
          else
          case assoc1 Name scope
           of SOME(_,ntv) => (Constrained(Var{Name=Name,Ty=ntv}, pty), E)
            | NONE => let in
               case assoc1 Name free
                of NONE => (Var v', (lscope,scope, (Name,pty)::free))
                 | SOME(_,ntv) => (Constrained(Var{Name=Name,Ty=ntv},pty), E)
               end
       end
    | CONST{Name,Thy,Ty} => (Const{Name=Name,Thy=Thy,Ty=Pretype.fromType Ty},E)
    | COMB(Rator,Rand)   =>
       let val (ptm1,E1) = from (dest_term Rator) E
           val (ptm2,E2) = from (dest_term Rand) E1
       in (Comb{Rator=ptm1, Rand=ptm2}, E2)
       end
    | LAMB(Bvar,Body) =>
       let val (s,ty) = dest_var Bvar
           val v' = {Name=s, Ty = Pretype.fromType ty}
           val (Body',(_,_,free')) = from (dest_term Body)
                                          (v'::lscope, scope, free)
       in (Abs{Bvar=Var v', Body=Body'}, (lscope,scope,free'))
       end
  val (ptm, (_,_,free)) = from (dest_term tm) ([],scope,free)
in
  (ptm, {scope=scope,free=free})
end;


(*---------------------------------------------------------------------------*
 * Generating fresh constant instances                                       *
 *---------------------------------------------------------------------------*)

fun gen_thy_const (thy,s) =
  let val c = Term.prim_mk_const{Name=s, Thy=thy}
  in Preterm.Const {Name=s, Thy=thy,
        Ty=Pretype.rename_typevars
                 (Pretype.fromType (Term.type_of c))}
  end

fun gen_const s =
 case Term.decls s
  of [] => raise ERROR "gen_const" ("unable to find constant "^Lib.quote s)
   | h::_ => let val {Name,Thy,Ty} = Term.dest_thy_const h
             in Preterm.Const
                  {Name=Name, Thy=Thy,
                   Ty=Pretype.rename_typevars (Pretype.fromType Ty)}
             end



(*---------------------------------------------------------------------------
 * Binding occurrences of variables
 *---------------------------------------------------------------------------*)

fun make_binding_occ s binder E =
 let open Preterm
     val _ =
       Lexis.ok_identifier s orelse
       Lexis.ok_symbolic s orelse
       raise ERROR "make_binding_occ"
         (s ^ " is not lexically permissible as a binding variable")
     val ntv = Pretype.new_uvar()
     val E' = add_scope((s,ntv),E)
 in
  case binder
   of "\\" => ((fn b => Abs{Bvar=Var{Name=s, Ty=ntv},Body=b}), E')
    |  _   => ((fn b => Comb{Rator=gen_const binder,
                             Rand=Abs{Bvar=Var{Name=s,Ty=ntv}, Body=b}}), E')
 end;


fun make_aq_binding_occ aq binder E = let
  val (v as (Name,Ty)) = Term.dest_var aq
  val pty = Pretype.fromType Ty
  val v' = {Name=Name, Ty=Pretype.fromType Ty}
  val E' = add_scope ((Name,pty),E)
  open Preterm
in
  case binder of
    "\\"   => ((fn b => Abs{Bvar=Var v', Body=b}), E')
  | binder => ((fn b => Comb{Rator=gen_const binder,
                             Rand=Abs{Bvar=Var v', Body=b}}),  E')
end


(*---------------------------------------------------------------------------
 * Free occurrences of variables.
 *---------------------------------------------------------------------------*)

fun make_free_var (s,E) =
 let open Preterm
 in (Var{Name=s, Ty=lookup_fvar(s,E)}, E)
     handle HOL_ERR _ =>
       let val tyv = Pretype.new_uvar()
       in (Var{Name=s, Ty=tyv}, add_free((s,tyv), E))
       end
 end

(*---------------------------------------------------------------------------
 * Bound occurrences of variables.
 *---------------------------------------------------------------------------*)

fun make_bvar (s,E) = (Preterm.Var{Name=s, Ty=lookup_bvar(s,E)}, E);

(* ----------------------------------------------------------------------
     Treatment of overloaded identifiers
 ---------------------------------------------------------------------- *)

fun gen_overloaded_const oinfo s = 
 let open Overload
     val opinfo = valOf (info_for_name oinfo s)
         handle Option => raise Fail "gen_overloaded_const: invariant failure"
 in
  case #actual_ops opinfo 
   of [{Ty,Name,Thy}] =>
         Preterm.Const{Name=Name, Thy=Thy,
                   Ty=Pretype.rename_typevars (Pretype.fromType Ty)}
  | otherwise => 
     let val base_pretype0 = Pretype.fromType (#base_type opinfo)
         val new_pretype = Pretype.rename_typevars base_pretype0
     in Preterm.Overloaded{Name = s, Ty = new_pretype, Info = opinfo}
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

fun make_const s E = (gen_const s, E)

(*---------------------------------------------------------------------------
    Making preterm string literals. 
 ---------------------------------------------------------------------------*)

local val num_ty = Pretype.Tyop("num",[])
      val char_ty = Pretype.Tyop("char",[])
      val string_ty = Pretype.Tyop("string",[])
      fun funty ty1 ty2 = Pretype.Tyop("fun",[ty1,ty2])
      fun mk_comb(ptm1,ptm2) = Preterm.Comb{Rator=ptm1,Rand=ptm2}
      val CHR = Preterm.Const
                   {Name="CHR",Thy="string",Ty=funty num_ty char_ty}
      val STRING = Preterm.Const {Name="STRING",Thy="string",
                      Ty=funty char_ty (funty string_ty string_ty)}
      val EMPTY = Preterm.Const
                      {Name="EMPTYSTRING",Thy="string",Ty=string_ty}
      fun mk_chr ptm = Preterm.Comb{Rator=CHR,Rand=ptm}
      fun mk_string (ptm1,ptm2) = 
          Preterm.Comb{Rator=Preterm.Comb{Rator=STRING,Rand=ptm1},Rand=ptm2}
      val mk_numeral = Literal.gen_mk_numeral
          {mk_comb = mk_comb,
          ZERO = Preterm.Const {Name="0",Thy="num",Ty=num_ty},
          ALT_ZERO = Preterm.Const{Name="ALT_ZERO",Thy="arithmetic",Ty=num_ty},
          NUMERAL = Preterm.Const 
                     {Name="NUMERAL",Thy="arithmetic",Ty=funty num_ty num_ty},
          BIT1 = Preterm.Const {Name="NUMERAL_BIT1",
                                Thy="arithmetic",Ty=funty num_ty num_ty},
          BIT2 = Preterm.Const {Name="NUMERAL_BIT2",
                                Thy="arithmetic",Ty=funty num_ty num_ty}}
in
fun make_string_literal s =
 Literal.mk_string_lit
     {mk_string = mk_string,
      emptystring = EMPTY,
      fromMLchar = fn ch => mk_chr(mk_numeral(Arbnum.fromInt (Char.ord ch)))}
  (String.substring(s,1,String.size s - 2))
end;

(*---------------------------------------------------------------------------
    "make_qconst" ignores overloading and visibility information. The
    idea is that if we ask to make a long identifier, it should be
    treated as visible.
 ---------------------------------------------------------------------------*)

fun make_qconst _ (p as (thy,s)) E = (gen_thy_const p, E);

fun make_atom oinfo s E =
 make_bvar(s,E) handle HOL_ERR _
  =>
  if Overload.is_overloaded oinfo s then
    (gen_overloaded_const oinfo s, E)
  else
  case List.find (fn rfn => String.isPrefix rfn s)
                 [recsel_special, recupd_special, recfupd_special]
   of NONE =>
       if Lexis.is_string_literal s
       then (make_string_literal s, E) handle HOL_ERR _
             => raise ERROR "make_atom"
                       ("Unable to make the string literal: "^s)
       else make_free_var (s, E)
    | SOME rfn =>
        raise ERROR "make_atom"
               ("Record field "^String.extract(s, size rfn, NONE)^
                " not registered")

(*---------------------------------------------------------------------------
 * Combs
 *---------------------------------------------------------------------------*)

fun list_make_comb (tm1::(rst as (_::_))) E =
     rev_itlist (fn tm => fn (trm,e) =>
        let val (tm',e') = tm e
        in (Preterm.Comb{Rator = trm, Rand = tm'}, e') end)     rst (tm1 E)
  | list_make_comb _ _ = raise ERROR "list_make_comb" "insufficient args";

(*---------------------------------------------------------------------------
 * Constraints
 *---------------------------------------------------------------------------*)

fun make_constrained tm ty E = let
  val (tm',E') = tm E
in
  (Preterm.Constrained(tm', ty), E')
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

fun bind_term binder alist tm (E as {scope=scope0,...}:env) =
   let val (E',F) = rev_itlist (fn a => fn (e,f) =>
             let val (g,e') = a binder e in (e', f o g) end) alist (E,I)
       val (tm',({free=free1,...}:env)) = tm E'
   in (F tm', {scope=scope0,free=free1})
   end;


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
fun associate_restriction(p as (binder_str,const_name)) =
  case (Lib.assoc1 binder_str (!restricted_binders)) of
    NONE => restricted_binders := p :: !restricted_binders
  | SOME _ =>
      raise ERROR "restrict_binder"
        ("Binder "^Lib.quote binder_str^" is already restricted")

fun delete_restriction binder =
 restricted_binders :=
  Lib.set_diff (!restricted_binders)
         [(binder,Lib.assoc binder(!restricted_binders))]
  handle HOL_ERR _
   => raise ERROR"delete_restriction" (Lib.quote binder^" is not restricted")
end;

fun restr_binder s =
   assoc s (binder_restrictions()) handle HOL_ERR _
   => raise ERROR "restr_binder"
                      ("no restriction associated with "^Lib.quote s)

fun bind_restr_term binder vlist restr tm (E as {scope=scope0,...}:env)=
   let fun replicate_rbinder e =
            (gen_const (restr_binder binder),e)
             handle HOL_ERR _ => raise ERROR "bind_restr_term"
              ("Can't find constant associated with "^Lib.quote binder)
       val (E',F) =
          rev_itlist (fn v => fn (e,f)
             => let val (prefix,e') = list_make_comb[replicate_rbinder,restr] e
                    val (g,e'') = v "\\" e'
                    fun make_cmb ptm = Preterm.Comb{Rator=prefix,Rand=ptm}
                in (e'', f o make_cmb o g) end)         vlist (E,I)
       val (tm',({free=free1,...}:env)) = tm E'
   in
   (F tm', {scope=scope0,free=free1})
   end;

fun split ty =
  case ty of
    Pretype.Tyop("prod",Args) => Args
  | _ => raise ERROR "split" "not a product";


local open Preterm
in
fun cdom M [] = M
  | cdom (Abs{Bvar,Body}) (ty::rst) =
       Abs{Bvar = Constrained(Bvar,ty), Body = cdom Body rst}
  | cdom (Comb{Rator as Const{Name="UNCURRY",...},Rand}) (ty::rst) =
       Comb{Rator=Rator, Rand=cdom Rand (split ty@rst)}
  | cdom x y = raise ERROR"cdom" "missing case"
end;

fun cdomf (f,e) ty = ((fn tm => cdom (f tm) [ty]), e)

fun make_vstruct bvl tyo binder E = let
  open Preterm
  fun loop ([v],E) = v "\\" E
    | loop ((v::rst),E) = let
        val (f,e) = v "\\" E
        val (F,E') = loop(rst,e)
      in
        ((fn b => Comb{Rator=gen_const "UNCURRY",Rand=f(F b)}), E')
      end
    | loop _ = raise ERROR"make_vstruct" "impl. error, empty vstruct"
  val (F,E') =
    case tyo of
      NONE    => loop(bvl,E)
    | SOME ty => cdomf (hd bvl "\\" E) ty
in
  case binder of
    "\\" => (F,E')
  | _ => ((fn b => Comb{Rator=gen_const binder,Rand=F b}), E')
end;


(*---------------------------------------------------------------------------
 * Let bindings
 *---------------------------------------------------------------------------*)
fun make_let bindings tm env =
   let open Preterm
       val {body_bvars, args, E} =
          itlist (fn (bvs,arg) => fn {body_bvars,args,E} =>
                    let val (b,rst) = (hd bvs,tl bvs)
                        val (arg',E') =
                          case rst of [] => arg E | L => bind_term "\\" L arg E
                    in {body_bvars = b::body_bvars, args=arg'::args, E=E'}
                    end) bindings {body_bvars=[], args=[], E=env}
       val (core,E') = bind_term "\\" body_bvars tm E
   in
     ( rev_itlist (fn arg => fn core =>
            Comb{Rator=Comb{Rator=gen_const "LET",Rand=core},Rand=arg})
           args core, E')
   end
   handle HOL_ERR _ => raise ERROR "make_let" "bad let structure";

fun make_set_const fname s E =
 (gen_const s, E)
  handle HOL_ERR _
    => raise ERROR fname ("The theory "^Lib.quote "set"^" is not loaded");


(*---------------------------------------------------------------------------
 * Set abstractions {tm1 | tm2}. The complicated rigamarole at the front is
 * so that new type variables only get made once per free var, although we
 * compute the free vars for tm1 and tm2 separately.
 *
 * You can't make a set unless the theory of sets is an ancestor.
 *  The calls to make_set_const ensure this.
 *
 * Warning: apt not to work if you want to "antiquote in" free variables that
 * will subsequently get bound in the set abstraction.
 *---------------------------------------------------------------------------*)

fun make_set_abs (tm1,tm2) (E as {scope=scope0,...}:env) =
   let val (_,(e1:env)) = tm1 empty_env
       val (_,(e2:env)) = tm2 empty_env
       val (_,(e3:env)) = tm2 e1
       val tm1_fv_names = map fst (#free e1)
       val tm2_fv_names = map fst (#free e2)
       val fv_names = intersect tm1_fv_names tm2_fv_names
       val init_fv = #free e3
   in
   case (gather (fn (name,_) => mem name fv_names) init_fv)
     of [] => raise ERROR "make_set_abs" "no free variables in set abstraction"
      | quants =>
         let val quants' = map
                (fn (bnd as (Name,Ty)) =>
                     (fn (s:string) => fn E =>
                       ((fn b => Preterm.Abs{Bvar=Preterm.Var{Name=Name,Ty=Ty},
                                             Body=b}),
                                add_scope(bnd,E))))
               (rev quants) (* make_vstruct expects reverse occ. order *)
         in list_make_comb
               [(make_set_const "make_set_abs" "GSPEC"),
                (bind_term "\\" [make_vstruct quants' NONE]
                          (list_make_comb[make_const ",",tm1,tm2]))] E
         end
   end;

end; (* Parse_support *)
