structure Parse_support :> Parse_support =
struct

type hol_type = Type.hol_type;

open Exception Lib;

fun PARSE_SUPPORT_ERR function message = 
 Exception.HOL_ERR{origin_structure = "Parse_support",
                   origin_function = function,
                   message = message};

(*---------------------------------------------------------------------------
 * For defining recursive concrete types.
 *---------------------------------------------------------------------------*)
datatype arg = Rec_occ | Hty of hol_type;

(*---------------------------------------------------------------------------
 * The three kinds of objects parsable by the hol.yak file: preterms, types,
 * and datatype declarations.
 *---------------------------------------------------------------------------*)
datatype parse = 
     PTM of Preterm.preterm
   | TY of hol_type
   | TY_SPEC of {ty_name: string,
                 clauses: {constructor:string, args:arg list} list}



type env = {scope : (string * hol_type) list, 
            free  : (string * hol_type) list};

fun lookup_fvar(s,({free,...}:env)) = assoc s free;
fun lookup_bvar(s,({scope,...}:env)) = assoc s scope;
fun add_free(b,{scope,free}) = {scope=scope, free=b::free}
fun add_scope(b,{scope,free}) = {scope=b::scope, free=free};

val empty_env = {scope = [], free = []};

type preterm_in_env = env -> Preterm.preterm * env

(*---------------------------------------------------------------------------
 * Denotes a lambda-bound variable. These are treated as functions from
 * preterm (the body) to preterm (the abstraction).
 *---------------------------------------------------------------------------*)
type bvar_in_env = env -> (Preterm.preterm -> Preterm.preterm) * env

(*---------------------------------------------------------------------------
 * Denotes a variable bound by a binder ("\\" or a constant, e.g., 
 * "!", "?", "@"). Hence, it takes a binder and returns a function from 
 * the body to a preterm (plus of course, any changes to the env).
 *---------------------------------------------------------------------------*)
type binder_in_env = string -> bvar_in_env



(*---------------------------------------------------------------------------
 * Top level parse terms 
 *---------------------------------------------------------------------------*)
fun make_preterm tm_in_e = fst(tm_in_e empty_env)


(*---------------------------------------------------------------------------
 * Antiquotes 
 *---------------------------------------------------------------------------*)
fun make_aq tm E = (Preterm.Antiq tm, E)


(*---------------------------------------------------------------------------
 * Getting constants from the symbol table
 *---------------------------------------------------------------------------*)
local val ren_ref = ref (fn _:(int,hol_type)Lib.istream =>
                         fn _:Type.hol_type => Type.DIFF(Type.mk_vartype"'x"))
      val _ = Type.Ps_init ren_ref
      val rename_tv = !ren_ref
in
fun gen_const tyvars s = 
   let val {Name,Ty} = Term.dest_const(#const(Term.const_decl s))
   in Preterm.Const 
        (case (rename_tv tyvars Ty)
           of Type.SAME     => {Name=Name, Ty=Ty}
            | Type.DIFF ty' => {Name=Name, Ty=ty'})
   end
end;



(*---------------------------------------------------------------------------
 * Binding occurrences of variables
 *---------------------------------------------------------------------------*)
fun make_binding_occ tyvars s "\\" E = 
     let val ntv = Lib.state(Lib.next tyvars)
     in ((fn b => Preterm.Abs{Bvar = Preterm.Var{Name = s, Ty = ntv}, 
                              Body = b}),
         add_scope((s,ntv),E))
     end
  | make_binding_occ tyvars s binder E =
     let val ntv = Lib.state(Lib.next tyvars)
     in ((fn b => Preterm.Comb{Rator=gen_const tyvars binder,
                             Rand=Preterm.Abs{Bvar=Preterm.Var{Name=s,Ty=ntv},
                                              Body = b}}),
         add_scope((s,ntv),E))
     end;

fun make_aq_binding_occ _ aq "\\" E = 
     ((fn b => Preterm.Abs{Bvar=Preterm.Antiq aq,Body=b}), E)
  | make_aq_binding_occ tyvars aq binder E = 
        ((fn b => Preterm.Comb{Rator = gen_const tyvars binder,
                               Rand = Preterm.Abs{Bvar = Preterm.Antiq aq,
                                                  Body = b}}),  E);

(*---------------------------------------------------------------------------
 * Free occurrences of variables in the body
 *---------------------------------------------------------------------------*)
fun make_free_var tyvars (s,E) =
   (Preterm.Var{Name = s, Ty = lookup_fvar(s,E)}, E)
   handle HOL_ERR _
   => let val tyv = Lib.state(Lib.next tyvars)
      in (Preterm.Var{Name = s, Ty = tyv}, add_free((s,tyv),E))
      end;

(*---------------------------------------------------------------------------
 * Bound occurrences in the body
 *---------------------------------------------------------------------------*)
fun make_bvar (s,E) = (Preterm.Var{Name = s, Ty = lookup_bvar(s,E)},E);


(*---------------------------------------------------------------------------
 * Constants not in the symbol table: numeric and string literals.
 *---------------------------------------------------------------------------*)

fun int2numeral tyvars nstr =
  Term.prim_mk_numeral {mkCOMB = Preterm.Comb,
                        mkNUM_CONST = gen_const tyvars,
                        mkNUM2_CONST = gen_const tyvars}
  (arbnum.fromString nstr)

fun make_num_literal tyvars (s,E) =
  if Globals.nums_defined()
  then (int2numeral tyvars s, E)
  else make_free_var tyvars (s,E);

(*---------------------------------------------------------------------------
 * Makes the assumption that s is already quoted (except for emptystring).
 *---------------------------------------------------------------------------*)
fun make_string s E = 
   let val atom = {Name=s, Ty=Type.mk_type{Tyop="string",Args=[]}}
       val tag = if Globals.strings_defined()
                 then Preterm.Const else Preterm.Var
   in (tag atom, E)
   end;


(* Atoms *)
local val the_hidden = ref [] : string list ref
in 
 fun hidden s = mem s (!the_hidden)
 fun hide s = (the_hidden := insert s (!the_hidden))
 fun reveal s = (the_hidden := set_diff (!the_hidden) [s])
end;

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
 * reserved word  or not.
 *---------------------------------------------------------------------------*)
fun make_atom tyvars s E =
   make_bvar(s,E)
   handle HOL_ERR _
   => if (hidden s)
      then make_free_var tyvars (s,E)
      else (gen_const tyvars s, E)
           handle HOL_ERR _ 
             => if (Lexis.is_num_literal s)
                then make_num_literal tyvars (s,E)
                else make_free_var tyvars (s,E);


(*---------------------------------------------------------------------------
 * Combs 
 *---------------------------------------------------------------------------*)
fun list_make_comb (tm1::(rst as (_::_))) E =
   rev_itlist (fn tm => fn (trm,e) => 
      let val (tm',e') = tm e
      in (Preterm.Comb{Rator = trm, Rand = tm'}, e') end)     rst (tm1 E) ;

(*---------------------------------------------------------------------------
 * Constraints 
 *---------------------------------------------------------------------------*)
fun make_constrained tm ty E =
   let val (tm',E') = tm E
   in (Preterm.Constrained(tm', ty), E')
   end;


(*---------------------------------------------------------------------------
 * Abstractions, qualified abstractions, and vstructs.
 * The thing to know about parsing abstractions is that an abstraction is 
 * a function from the string identifying the binder to an env to a 
 * pair. The first member of the pair is a function that will take the body
 * of the abstraction and produce a lambda term, essentially by clapping 
 * on whatever variables, or applying whatever constants necessary. The second
 * member of the pair is the environment previous to entering the abstraction
 * plus whatever new free variables were found in the body of the abstraction.
 *
 * We could just return (F tm', E), except that we may add free variables
 * found in tm to E.
 *---------------------------------------------------------------------------*)

fun bind_term binder alist tm (E as {scope=scope0,...}:env) =
   let val (E',F) = rev_itlist (fn a => fn (e,f) => 
             let val (g,e') = a binder e in (e', f o g) end) alist (E,I)
       val (tm',({free=free1,...}:env)) = tm E'
   in (F tm', {scope=scope0,free=free1})
   end;

fun restr_binder s = 
   assoc s (Dsyntax.binder_restrictions()) handle HOL_ERR _
   => raise PARSE_SUPPORT_ERR "restr_binder"
                      ("no restriction associated with "^Lib.quote s)

fun bind_restr_term tyvars binder vlist restr tm (E as {scope=scope0,...}:env)=
   let fun replicate_rbinder e = 
            (gen_const tyvars (restr_binder binder),e)
             handle HOL_ERR _ => raise PARSE_SUPPORT_ERR "bind_restr_term"
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
  case (Type.dest_type ty) 
   of {Tyop="prod",Args} => Args
    | _ => raise PARSE_SUPPORT_ERR "split" "not a product";



fun cdom M [] = M
  | cdom (Preterm.Abs{Bvar,Body}) (ty::rst) = 
       Preterm.Abs{Bvar = Preterm.Constrained(Bvar,ty), 
                   Body = cdom Body rst}
  | cdom (Preterm.Comb{Rator as Preterm.Const{Name="UNCURRY",...},Rand}) 
         (ty::rst) = 
       Preterm.Comb{Rator=Rator, Rand=cdom Rand (split ty@rst)} 
  | cdom x y = raise PARSE_SUPPORT_ERR"cdom" "missing case"


fun cdomf (f,e) ty = ((fn tm => cdom (f tm) [ty]), e)

fun make_vstruct tyvars bvl tyo binder E = 
 let fun loop ([v],E) = v "\\" E
       | loop ((v::rst),E) = 
           let val (f,e) = v "\\" E
               val (F,E') = loop(rst,e)
           in ((fn b => Preterm.Comb{Rator = gen_const tyvars "UNCURRY",
                                     Rand = f(F b)}), E') end
       | loop _ = raise PARSE_SUPPORT_ERR"make_vstruct"
                                         "impl. error, empty vstruct"
     val (F,E') = case tyo 
                  of NONE    => loop(bvl,E) 
                   | SOME ty => cdomf (hd bvl "\\" E) ty
   in
   case binder 
   of "\\" => (F,E')
    | _ => ((fn b => Preterm.Comb{Rator=gen_const tyvars binder,Rand=F b}), E')
   end;


(*---------------------------------------------------------------------------
 * Let bindings 
 *---------------------------------------------------------------------------*)
fun make_let tyvars bindings tm env =
   let val {body_bvars, args, E} =
          itlist (fn (bvs,arg) => fn {body_bvars,args,E} =>
                    let val (b::rst) = bvs
                        val (arg',E') = 
                          case rst of [] => arg E | L => bind_term "\\" L arg E
                    in {body_bvars = b::body_bvars, args = arg'::args, E = E'}
                    end) bindings {body_bvars = [], args = [], E = env}
       val (core,E') = bind_term "\\" body_bvars tm E
   in
   ( rev_itlist (fn arg => fn core => 
       Preterm.Comb{Rator=Preterm.Comb{Rator=gen_const tyvars"LET",Rand=core},
                    Rand = arg}) args core,
     E')  end
   handle HOL_ERR _ => raise PARSE_SUPPORT_ERR "make_let" "bad let structure";


(*---------------------------------------------------------------------------
 * Enumerated lists and sets (nearly identical treatment)
 *
 * This is a bit tricky in the case that alist = [], for we still do a
 * make_atom "CONS". But we know that "CONS" is already in the symtab, hence
 * make_atom "CONS" E = (Const{Name = "CONS", Ty = ...},E') and E = E'.
 * So nothing new can get added to the environment. When it builds the 
 * environment, it goes right-to-left in the list, so maybe error messages
 * will be puzzling.
 *---------------------------------------------------------------------------*)
fun make_list tyvars alist E =
 let val (cons,E') = make_atom tyvars "CONS" E   
 in itlist (fn h => fn (L,E) =>
     let val (h',E') = h E
     in (Preterm.Comb{Rator=Preterm.Comb{Rator=cons,Rand=h'}, Rand=L}, E') end)
   alist (make_atom tyvars "NIL" E')
 end;

fun make_set_const tyvars fname s E = 
 (gen_const tyvars s, E) handle HOL_ERR _
  => raise PARSE_SUPPORT_ERR fname 
       ("The theory "^Lib.quote "set"^" is not loaded");

(*---------------------------------------------------------------------------
 * You can't make a set unless the theory of sets is an ancestor. 
 *  The calls to make_set_const ensure this.
 *---------------------------------------------------------------------------*)
fun make_set tyvars [] E = make_set_const tyvars "make_set" "EMPTY" E
  | make_set tyvars alist E =
      let val (insert,_) = make_set_const tyvars "make_set" "INSERT" []
          val empty_in_env = make_set_const tyvars "make_set" "EMPTY" E
      in itlist(fn h => fn (L,E) =>
           let val (h',E') = h E
           in (Preterm.Comb{Rator = Preterm.Comb{Rator = insert,Rand = h'},
                            Rand = L}, E') end)        alist empty_in_env
      end;


(*---------------------------------------------------------------------------
 * Set abstractions {tm1 | tm2}. The complicated rigamarole at the front is 
 * so that new type variables only get made once per free var, although we 
 * compute the free vars for tm1 and tm2 separately.
 *
 * Warning: apt not to work if you want to "antiquote in" free variables that
 * will subsequently get bound in the set abstraction.
 *---------------------------------------------------------------------------*)
fun make_set_abs tyvars (tm1,tm2) (E as {scope=scope0,...}:env) = 
   let val (_,(e1:env)) = tm1 empty_env
       val (_,(e2:env)) = tm2 empty_env
       val (_,(e3:env)) = tm2 e1
       val tm1_fv_names = map fst (#free e1)
       val tm2_fv_names = map fst (#free e2)
       val fv_names = intersect tm1_fv_names tm2_fv_names
       val init_fv = #free e3
   in
   case (gather (fn (name,_) => mem name fv_names) init_fv)
     of [] => raise PARSE_SUPPORT_ERR"make_set_abs"
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
               [(make_set_const tyvars "make_set_abs" "GSPEC"),
                (bind_term "\\" [make_vstruct tyvars quants' NONE]
                          (list_make_comb[make_atom tyvars ",",tm1,tm2]))] E
         end
   end;


(*---------------------------------------------------------------------------*
 * Types                                                                     *
 *---------------------------------------------------------------------------*)
val rec_occ = Type.dummy

fun make_atomic_type (ident,NONE) = Type.mk_type{Tyop=ident, Args=[]}
  | make_atomic_type (ident,SOME s) = 
     if (ident = s) then rec_occ
     else make_atomic_type(ident,NONE);


fun make_type_app (s,tylist) = Type.mk_type{Tyop=s, Args=tylist}

(*---------------------------------------------------------------------------
 * Clauses in type specifications
 *
 * Recursive occurrences of the defined type are marked with Type.dummy, a 
 * nonsense type variable, in order to stay within the the type of 
 * hol_types (this saves on creating a new type built from Rec_occs and 
 * normal hol_types).
 *---------------------------------------------------------------------------*)
fun make_type_clause {constructor, args} =
 let fun check ty =
       if (ty=rec_occ)
       then raise PARSE_SUPPORT_ERR"make_type_clause.check"
                                "recursive occurrence of defined type \
                                        \is deeper than the first level"
       else if (Type.is_vartype ty) then ()
            else case Type.dest_type ty
                  of {Args=[],Tyop}   => ()
                   | {Args,Tyop} => (map check Args; ())

     fun munge ty = 
       if (ty = rec_occ) then Rec_occ else 
       if (Type.is_vartype ty) then Hty ty
       else case Type.dest_type ty
            of {Args=[],Tyop} => Hty ty
             | {Args,Tyop}    => (map check Args; Hty ty)
 in 
    {constructor=constructor, args = map munge args}
 end;


(*---------------------------------------------------------------------------*
 * Sorting out precedence between infixes.                                   *
 *---------------------------------------------------------------------------*)

val dummy_least_infix = Preterm.Const{Name = "", Ty = Type.dummy}

fun prec (tm as Preterm.Const{Name, ...}) =
        if (tm = dummy_least_infix) then ~1 else Theory.precedence Name
  | prec (Preterm.Constrained(tm,_)) = prec tm;

fun is_infix_term (Preterm.Const{Name,...}) = Theory.is_infix Name
  | is_infix_term (Preterm.Constrained(tm,_)) = is_infix_term tm
  | is_infix_term _ = false

fun is_neg(Preterm.Const{Name = "~",...}) = true
  | is_neg(Preterm.Constrained(tm,_)) = is_neg tm
  | is_neg _ = false

fun list_make_list tmlist E =
  let val (L,E') = rev_itlist(fn tm => fn (L,E) =>
        let val (tm',E') = tm E in ((tm'::L),E') end) tmlist ([],E)
   in (rev L, E')
   end;

fun G [] (f,arg) = [(f,arg)]
  | G (stk as ((g,tm)::stk')) (f,arg) = 
        if (prec g >= prec f)
        then let val tm' = Preterm.Comb{Rator = Preterm.Comb{Rator=g,Rand=arg},
                                        Rand = tm}
             in G stk' (f,tm') end
        else ((f,arg)::stk);

local fun lc [] tm = tm
        | lc (a::rst) tm = lc rst (Preterm.Comb{Rator = tm, Rand = a})
      fun list_comb (a::L) = lc L a
        | list_comb [] = raise PARSE_SUPPORT_ERR"prec_parse"
                                 "an infix is being used as a prefix"
      fun make_neg tm [] = tm
        | make_neg tm L = Preterm.Comb{Rator = tm, Rand = list_comb L}
in
fun prec_parse [f] E = f E
  | prec_parse cl_list E =
   let val (tm_list,E') = list_make_list cl_list E
       fun pass tm (L,stk) =
           if (is_infix_term tm)
           then ([], G stk (tm, list_comb L))
           else if (is_neg tm) then ([make_neg tm L], stk)
                                else (tm::L, stk)
       val (L,stk) = itlist pass tm_list ([],[])
       val [(_,tm)] = G stk (dummy_least_infix,list_comb L)
   in (tm,E') end
end;



(*---------------------------------------------------------------------------
 * Used in hol.lex. Could possibly be done through make_atom.
 *---------------------------------------------------------------------------*)
val is_binder = Theory.is_binder;

end; (* parse_support *)
