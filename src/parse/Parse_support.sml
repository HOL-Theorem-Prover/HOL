structure Parse_support :> Parse_support =
struct

type hol_type = Type.hol_type;
type pretype = TCPretype.pretype;

open Exception Lib;

fun ERROR function message =
 Exception.HOL_ERR{origin_structure = "Parse_support",
                   origin_function = function,
                   message = message};


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
      VAR (v as {Name,Ty}) => let
        val pty = TCPretype.fromType Ty
        val v' = {Name=Name, Ty=pty}
      in
        if mem v' lscope then (Var v', E)
        else
          case assoc1 Name scope of
            SOME(_,ntv) => (Constrained(Var{Name=Name,Ty=ntv}, pty), E)
          | NONE => let
            in
              case assoc1 Name free of
                NONE => (Var v', (lscope,scope, (Name,pty)::free))
              | SOME(_,ntv) => (Constrained(Var{Name=Name,Ty=ntv},pty), E)
            end
      end
    | CONST {Name, Ty} => (Const{Name=Name, Ty = TCPretype.fromType Ty}, E)
    | COMB{Rator,Rand} => let
        val (ptm1,E1) = from (dest_term Rator) E
        val (ptm2,E2) = from (dest_term Rand) E1
      in
        (Comb{Rator=ptm1, Rand=ptm2}, E2)
      end
    | LAMB{Bvar,Body} => let
        val v = dest_var Bvar
        val v' = {Name= #Name v, Ty = TCPretype.fromType (#Ty v)}
        val (Body',(_,_,free')) =
          from (dest_term Body) (v'::lscope, scope, free)
      in
        (Abs{Bvar=Var v', Body=Body'}, (lscope,scope,free'))
      end
  val (ptm, (_,_,free)) = from (dest_term tm) ([],scope,free)
in
  (ptm, {scope=scope,free=free})
end;


(*---------------------------------------------------------------------------
 * Getting constants from the symbol table
 *---------------------------------------------------------------------------*)
fun gen_const s = let
  val {Name,Ty} = Term.dest_const(#const(Term.const_decl s))
  val pty = TCPretype.fromType Ty
in
  Preterm.Const {Name = Name, Ty = TCPretype.rename_typevars pty}
end;



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
     val ntv = TCPretype.new_uvar()
     val E' = add_scope((s,ntv),E)
 in
  case binder
   of "\\" => ((fn b => Abs{Bvar=Var{Name=s, Ty=ntv},Body=b}), E')
    |  _   => ((fn b => Comb{Rator=gen_const binder,
                             Rand=Abs{Bvar=Var{Name=s,Ty=ntv}, Body=b}}), E')
 end;


fun make_aq_binding_occ aq binder E = let
  val (v as {Name,Ty}) = Term.dest_var aq
  val pty = TCPretype.fromType Ty
  val v' = {Name = Name, Ty = TCPretype.fromType Ty}
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

fun make_free_var (s,E) = let
  open Preterm
in
  (Var{Name=s, Ty=lookup_fvar(s,E)}, E)
  handle HOL_ERR _ => let
    val tyv = TCPretype.new_uvar()
  in
    (Var{Name=s, Ty = tyv}, add_free((s,tyv), E))
  end
end

(*---------------------------------------------------------------------------
 * Bound occurrences of variables.
 *---------------------------------------------------------------------------*)

fun make_bvar (s,E) = (Preterm.Var{Name=s, Ty=lookup_bvar(s,E)}, E);

(*---------------------------------------------------------------------------
   Setting the visibility of identifiers.
 ---------------------------------------------------------------------------*)
local val the_hidden = ref [] : string list ref
in
 fun hide s   = (the_hidden := insert s (!the_hidden))
 fun reveal s = (the_hidden := set_diff (!the_hidden) [s])
 fun hidden s = mem s (!the_hidden)
end;

(* ----------------------------------------------------------------------
     Treatment of overloaded identifiers
 ---------------------------------------------------------------------- *)

fun gen_overloaded_const oinfo s = let
  open Overload
  val opinfo = valOf (info_for_name oinfo s)
in
  case #actual_ops opinfo of
    [(ty, s)] => Preterm.Const{Name = s, Ty = TCPretype.fromType ty}
  | _ => let
      val base_pretype0 = TCPretype.fromType (#base_type opinfo)
      val new_pretype = TCPretype.rename_typevars base_pretype0
    in
      Preterm.Overloaded{Name = s, Ty = new_pretype, Info = opinfo}
    end
end


(*---------------------------------------------------------------------------
 * Identifiers work as follows: look for the string in the scope;
 * if it's there, put the var. Otherwise, the string might be a constant that
 * we intend to parse as a free var. Otherwise, the string might be a constant;
 * look in the symbol table. If it's there, rename any type variables in
 * its binding and make a Const out of it. Otherwise, it's not in the scope
 * and not in the symtab, hence is a free variable. Generate a new type
 * variable and bind the term variable to it in E; also we return a var
 * that has the new type variable as its type.
 *
 * Free vars are placed in the "free" part of the environment; this is a
 * set. Bound vars are placed at the front of the "scope". When we come out
 * of an Abs, we return the scope in effect when entering the Abs, but the
 * "free"s include new ones found in the body of the Abs.
 *
 * Note: this code should maybe check whether the prospective identifier is a
 * reserved word or not.
 *---------------------------------------------------------------------------*)

fun make_const s E = (gen_const s, E)

fun make_atom oinfo s E = make_bvar(s,E)
  handle HOL_ERR _ =>
    if (hidden s) then
      make_free_var (s,E)
    else
      if Overload.is_overloaded oinfo s then
        (gen_overloaded_const oinfo s, E)
      else
        (gen_const s, E)
        handle HOL_ERR _ =>
          if (Lexis.is_string_literal s) then
            raise ERROR "make_atom"
              "string literals not lexically OK until stringTheory loaded"
          else make_free_var (s,E);

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
    TCPretype.Tyop("prod",Args) => Args
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
                    let val (b::rst) = bvs
                        val (arg',E') =
                          case rst of [] => arg E | L => bind_term "\\" L arg E
                    in {body_bvars = b::body_bvars, args = arg'::args, E = E'}
                    end) bindings {body_bvars = [], args = [], E = env}
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
     of [] => raise ERROR"make_set_abs"
                                "no free variables in set abstraction"
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
