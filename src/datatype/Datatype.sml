(*---------------------------------------------------------------------------*
 * Define a HOL datatype and derive a bunch of theorems from it. Return      *
 * these encapsulated in an element of the TypeBase.tyinfo type.             *
 *                                                                           *
 * Examples of use:                                                          *
 *                                                                           *
 *   local open Datatype                                                     *
 *   in                                                                      *
 *   val term_ty_def =                                                       *
 *       Hol_datatype `term = Var of 'a                                      *
 *                          | Const of 'a                                    *
 *                          | App of term => term`                           *
 *                                                                           *
 *   val subst_ty_def =                                                      *
 *       Hol_datatype  `subst = Fail | Subst of ('a#'a term) list`           *
 *   end;                                                                    *
 *                                                                           *
 *                                                                           *
 * Returns a great deal of information about the datatype: theorems,         *
 * definition of case-constant, induction tactics, etc.                      *
 *                                                                           *
 * Side-effects: it adds the definition of the type and the definition       *
 * of the case-construct to the current theory.                              *
 *                                                                           *
 * Notice that, at least using the current mechanism for defining types,     *
 * a great many theories get loaded in: numbers, lists, trees, etc. when     *
 * this module is loaded. If your formalization doesn't want to have these   *
 * as parents, then TypeBase.mk_tyinfo can be used directly.                 *
 *---------------------------------------------------------------------------*)

structure Datatype :> Datatype =
struct

open HolKernel Parse Drule Tactical Tactic Conv Prim_rec ;

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
fun -- q x = Term q
fun == q x = Type q

infix ## |-> THEN THENC THENL;
infixr -->;

type term = Term.term
type hol_type = Type.hol_type
type tyinfo = TypeBase.tyinfo
type typeBase = TypeBase.typeBase;
type 'a quotation = 'a Portable.frag list;


fun ERR func mesg =
    HOL_ERR{origin_structure = "Datatype",
            origin_function = func,
            message = mesg};

val defn_const =
  #1 o strip_comb o lhs o #2 o strip_forall o hd o strip_conj o concl;

(*---------------------------------------------------------------------------*
 * Term size, as a function of types. Types not registered in gamma are      *
 * translated into the constant function that returns 0. The function theta  *
 * maps a type variables (say 'a) to a term variable "f" of type 'a -> num.  *
 * The function gamma maps type operator "ty" to term "ty_size".             *
 *                                                                           *
 * When actually building a measure function, the behaviour of theta is      *
 * changed to be such that it maps type variables to the constant function   *
 * that returns 0.                                                           *
 *---------------------------------------------------------------------------*)

val Zero  = Term`0n`
val One   = Term`1n`
val numty = mk_type{Tyop="num", Args=[]};
val Plus  = mk_const{Name="+", Ty=Type`:num -> num -> num`};
fun mk_plus x y = list_mk_comb(Plus,[x,y]);

local fun num_variant vlist v =
        let val counter = ref 1
            val {Name,Ty} = dest_var v
            fun pass str list =
              if (mem str list)
              then ( counter := !counter + 1;
                     pass (Name^Lib.int_to_string(!counter)) list)
              else str
        in
          mk_var{Name=pass Name (map (#Name o dest_var) vlist),  Ty=Ty}
        end
in
fun mk_ty_fun vty (V,away) =
    let val fty = vty --> numty
        val v = num_variant away (mk_var{Name="f", Ty=fty})
    in
       (v::V, v::away)
    end
end;


local open arithmeticTheory
      val zero_rws = [Rewrite.ONCE_REWRITE_RULE [ADD_SYM] ADD_0, ADD_0]
in
fun define_size ax tysize_env =
 let val exu = snd(strip_forall(concl ax))
     val {Rator,Rand} = dest_comb exu
     val {Name = "?!",...} = dest_const Rator
     val {Bvar,Body} = dest_abs Rand
     val (dty,rty) = Type.dom_rng (type_of Bvar)
     val {Tyop,Args} = dest_type dty
     val clist = map (rand o lhs o #2 o strip_forall) (strip_conj Body)
     val arglist = rev(fst(rev_itlist mk_ty_fun Args ([],free_varsl clist)))
     val v = mk_var{Name = Tyop^"_size",
                    Ty = itlist (curry op-->) (map type_of arglist)
                                (dty --> numty)}
     val preamble = list_mk_comb(v,arglist)
     val f0 = zip Args arglist
     fun theta tyv = case (assoc1 tyv f0) of SOME(_,x) => SOME x | _ => NONE
     fun gamma str = if str=Tyop then SOME v else tysize_env str
     val sizer = TypeBase.tysize(theta,gamma)
     fun mk_app x = mk_comb{Rator=sizer (type_of x), Rand=x}
     fun capp2rhs capp =
          case snd(strip_comb capp)
           of [] => Zero
            | L  => end_itlist mk_plus (One::map mk_app L)
     fun clause c = mk_eq{lhs=mk_comb{Rator=preamble,Rand=c},rhs=capp2rhs c}
     val defn = list_mk_conj (map clause clist)
     val red_defn = #rhs(dest_eq(concl   (* remove zero additions *)
                       ((DEPTH_CONV BETA_CONV
                           THENC Rewrite.PURE_REWRITE_CONV zero_rws) defn)))
 in
    new_recursive_definition
        {name=Tyop^"_size_def", fixity=Prefix, rec_axiom=ax,
         def = red_defn}
 end
 handle HOL_ERR _ => raise ERR "define_size" "failed"
end;


(*---------------------------------------------------------------------------
     Generate and install a prettyprinter for importing a previously
     declared datatype from an external theory.
 ---------------------------------------------------------------------------*)

fun adjoin {ax,case_def,case_cong,induction,nchotomy,size,one_one,distinct}
  = adjoin_to_theory
    {sig_ps = NONE,
     struct_ps = SOME (fn ppstrm =>
       let val S = PP.add_string ppstrm
           fun NL() = PP.add_newline ppstrm
           fun do_size(c,s) =
              let open Globals
                  val strc = with_flag(show_types,true) term_to_string c
                  val line = String.concat ["SOME(Parse.Term`", strc, "`,"]
              in
                 S ("      size="^line);
                 NL();
                 S ("                "^s^"),")
              end
       in
           S "val _ = TypeBase.write";            NL();
           S "  (TypeBase.mk_tyinfo";             NL();
           S ("     {ax="^ax^",");                NL();
           S ("      case_def="^case_def^",");    NL();
           S ("      case_cong="^case_cong^",");  NL();
           S ("      induction="^induction^",");  NL();
           S ("      nchotomy="^nchotomy^",");    NL();
           do_size size;                          NL();
           S ("      one_one="^one_one^",");  NL();
           S ("      distinct="^distinct^"});")
       end)};


fun join f g x =
  case (g x)
   of NONE => NONE
    | SOME y => (case (f y)
                  of NONE => NONE
                   | SOME(x,_) => SOME x);

fun tysize_env db = join TypeBase.size_of (TypeBase.get db);

(*---------------------------------------------------------------------------

    For a datatype named "ty", primHol_datatype stores the following
    theorems in the current theory, and in TypeBase.theTypeBase. (Some
    other definitions and theorems used in defining the datatype are
    also stored in the current theory, but we will ignore them.)

        1. ty               (* datatype characterization theorem *)
        2. ty_case_def      (* case_expression defn *)
        3. ty_case_cong     (* congruence theorem for case expression *)
        4. ty_induction     (* induction thm for datatype *)
        5. ty_nchotomy      (* case completeness *)
        6. ty_size_def      (* size of type defn *)
        7. one_one          (* one-one-ness of the constructors *)
        8. distinct         (* distinctness of the constructors *)

   We also adjoin some ML to the current theory so that if the theory
   gets exported and loaded in a later session, these "datatype"
   theorems are loaded automatically into theTypeBase.

 ---------------------------------------------------------------------------*)

fun primHol_datatype db q =
  let open Define_type
      val {ty_name, clauses} = Define_type.parse_tyspec q
      fun prefix{constructor,args} =
          {constructor=constructor, args=args, fixity=Prefix}
      fun name s = (ty_name^s)
      val axname = name "_Axiom"
      val ax = dtype{clauses=map prefix clauses,
                     save_name=axname,ty_name=ty_name}
      val tyinfo =
        TypeBase.gen_tyinfo {ax=ax,
                             case_def = Prim_rec.define_case_constant ax}
      val one_one = TypeBase.one_one_of tyinfo
      val distinct = TypeBase.distinct_of tyinfo
      val size_def = define_size (TypeBase.axiom_of tyinfo) (tysize_env db)
      val tyinfo'  = TypeBase.put_size (defn_const size_def,size_def) tyinfo
      val _ = save_thm (name"_case_cong",TypeBase.case_cong_of tyinfo')
      val _ = save_thm (name"_induction",TypeBase.induction_of tyinfo')
      val _ = save_thm (name"_nchotomy",TypeBase.nchotomy_of tyinfo')
      val _ =
        case one_one of
          NONE => ()
        | SOME th => (save_thm(name "_11", th); ())
      val _ =
        case distinct of
          NONE => ()
        | SOME th => (save_thm(name "_distinct", th); ())
  in
     adjoin{ax=axname,case_def=name"_case_def",
            case_cong=name "_case_cong",
            induction=name "_induction",
            nchotomy=name "_nchotomy",
            size=(#const(const_decl(name "_size")),name "_size_def"),
            one_one=case one_one
                     of NONE => "NONE"
                      | _ => ("SOME "^name"_11"),
            distinct=case distinct
                     of NONE => "NONE"
                      | _ => ("SOME "^name"_distinct")};
     tyinfo'
  end
  handle e as HOL_ERR _ => Raise e;


fun Hol_datatype q =
  TypeBase.write (primHol_datatype (TypeBase.theTypeBase()) q);

end;
