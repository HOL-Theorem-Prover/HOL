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

type tyspec = (hol_type * (string * hol_type list) list) list

(* a list of type specifications; one for each type.  The first
   component is a type variable whose name (less the leading quote) is
   the name of the new type.  Each such is accompanied by a list of
   constructor specifications.  Such a spec. is a string (the
   constructor name) and a list of types that are the arguments of
   that constructor.  Recursive occurrences of the types are marked by
   occurrences of the corresponding type variables. *)

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


local
  open arithmeticTheory
  val zero_rws = [Rewrite.ONCE_REWRITE_RULE [ADD_SYM] ADD_0, ADD_0]
in
  fun define_size ax tysize_env = let
    val (_, abody) = strip_forall(concl ax)
    val (exvs, ebody) = strip_exists abody

(*
     val {Rator,Rand} = dest_comb exu
     val {Name = "?!",...} = dest_const Rator
     val {Bvar,Body} = dest_abs Rand
     val (dty,rty) = Type.dom_rng (type_of Bvar)
     val {Tyop,Args} = dest_type dty
*)
    val dtys = new_types ax
    val Args = Lib.U (map (#Args o dest_type) dtys)

    (* list of all constructors with arguments *)
    val clist = map (rand o lhs o #2 o strip_forall) (strip_conj ebody)

    (* functions which will generate sizes for type variables *)
    val arglist = rev(fst(rev_itlist mk_ty_fun Args ([],free_varsl clist)))
    fun construct_sizefn_term ty = let
      val {Tyop = name, ...} = dest_type ty
    in
      (name,
       (ty,
        mk_var{Name = name ^ "_size",
              Ty = itlist (curry op-->) (map type_of arglist) (ty --> numty)}))
    end
    val vs = map construct_sizefn_term dtys
    val preambles = map (fn (_,(ty,v)) => (ty, list_mk_comb(v,arglist))) vs
    val f0 = zip Args arglist
    fun theta tyv = case (assoc1 tyv f0) of SOME(_,x) => SOME x | _ => NONE
    fun gamma str =
      case (assoc1 str vs) of
        SOME(_,(_, v)) => SOME v
      | _ => tysize_env str
    val sizer = TypeBase.tysize(theta,gamma)
    fun mk_app x = mk_comb{Rator=sizer (type_of x), Rand=x}
    fun capp2rhs capp =
      case snd(strip_comb capp) of
        [] => Zero
      | L  => end_itlist mk_plus (One::map mk_app L)
    fun clause c =
      case assoc1 (type_of c) preambles of
        SOME (_, p) =>
          SOME (mk_eq{lhs=mk_comb{Rator=p, Rand=c},rhs=capp2rhs c})
      | NONE => NONE
     val defn = list_mk_conj (List.mapPartial clause clist)
     val red_defn = #rhs(dest_eq(concl   (* remove zero additions *)
                       ((DEPTH_CONV BETA_CONV
                           THENC Rewrite.PURE_REWRITE_CONV zero_rws) defn)))
 in
    new_recursive_definition
        {name= #1 (hd vs)^"_size_def", rec_axiom = ax, def = red_defn}
 end
 handle HOL_ERR _ => raise ERR "define_size" "failed"
end;


(*---------------------------------------------------------------------------
     Generate and install a prettyprinter for importing a previously
     declared datatype from an external theory.
 ---------------------------------------------------------------------------*)

fun adjoin base_names extras = let
  val {ax,case_def,case_cong,induction,nchotomy,size,one_one,distinct} =
    base_names
in
  adjoin_to_theory
    {sig_ps = NONE,
     struct_ps = SOME
     (fn ppstrm => let
       val S = PP.add_string ppstrm
       fun NL() = PP.add_newline ppstrm
       fun do_size(c,s) = let
         open Globals
         val strc = "(" ^ term_to_string c ^ ") "^type_to_string (type_of c)
         val line = String.concat ["SOME(Parse.Term`", strc, "`,"]
       in
         S ("      size="^line);
         NL();
         S ("                "^s^"),")
       end
       fun do_simpls () = (S "["; app S (Lib.commafy extras); S "]")
     in
       S "val _ =";                           NL();
       S "   let val tyinfo0 = ";             NL();
       S "     TypeBase.mk_tyinfo";           NL();
       S ("     {ax="^ax^",");                NL();
       S ("      case_def="^case_def^",");    NL();
       S ("      case_cong="^case_cong^",");  NL();
       S ("      induction="^induction^",");  NL();
       S ("      nchotomy="^nchotomy^",");    NL();
       do_size size;                          NL();
       S ("      one_one="^one_one^",");      NL();
       S ("      distinct="^distinct^"}");    NL();
       S "   in";                             NL();
       S "    TypeBase.write ";               NL();
       if (not (null extras)) then
         (S "    (TypeBase.put_simpls (";
          do_simpls();
          S " @ TypeBase.simpls_of tyinfo0) tyinfo0)")
       else
         (S "    tyinfo0");
       NL();
       S "   end;";                           NL()
     end)}
end


fun join f g x =
  case (g x)
   of NONE => NONE
    | SOME y => (case (f y)
                  of NONE => NONE
                   | SOME(x,_) => SOME x);

fun tysize_env db = join TypeBase.size_of (TypeBase.get db);

(* ----------------------------------------------------------------------
   Primitive function for defining a type, based on the form of the
   datatypeAST returned from parsing a quotation
   ---------------------------------------------------------------------- *)

local
  open ParseDatatype

in

  fun raw_define_type tyspec = let
    val (ind, recth) = ind_types.define_type tyspec
  in
    {induction = ind, recursion = recth}
  end

  fun translate_out_record dast =
    case dast of
      (tyname, WithConstructors cs) => ((tyname, cs), NONE)
    | (rtyname, RecordType fldtypes) => let
        val (flds, types) = ListPair.unzip fldtypes
      in
        ((rtyname, [(rtyname, types)]), SOME flds)
      end

  fun translate_parse dastl = let
    val dasts_with_record_info = map translate_out_record dastl
    val (dasts, record_infos) = ListPair.unzip dasts_with_record_info
    val new_type_names = map #1 dasts
    fun translate_newtyname n = mk_vartype ("'" ^ n)
    fun translate_pty pty =
      case pty of
        dVartype s => mk_vartype s
      | dTyop(s, args) => let
        in
          if Lib.mem s new_type_names then
            if (null args) then translate_newtyname s
            else
              raise ERR "deftype_from_parse"
                "Can't apply new types as operators - leave them nullary"
          else
            mk_type{Tyop = s, Args = map translate_pty args}
        end
      | dAQ ty => ty
    fun translate_constructor (cname, ptys) =
      (cname, map translate_pty ptys)
    fun translate_1_typedef (n, cs) =
      (translate_newtyname n, map translate_constructor cs)
  in
    (map translate_1_typedef dasts, record_infos)
  end

  fun deftype_from_parse dtastl =
    case dtastl of
      [] => raise ERR "deftype_from_parse" "No type forms specificed"
    | _ => let
        val (tydef_input, record_infos) = translate_parse dtastl
        val {induction,recursion} = raw_define_type tydef_input
        val case_defs = Prim_rec.define_case_constant recursion
        val tyinfos =
          TypeBase.gen_tyinfo {ax = recursion, ind = induction,
                               case_defs = case_defs}
        fun recordise x =
          case x of
            (tyinfo, NONE) => (tyinfo, [])
          | (tyinfo, SOME flds) =>
              RecordType.prove_recordtype_thms (tyinfo, flds)
      in
        ListPair.map recordise (tyinfos, record_infos)
      end

  val define_type_from_parse = deftype_from_parse

end (* local *)


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

fun make_tyinfo_persist (tyinfo, extras) = let
  fun name s = TypeBase.ty_name_of tyinfo ^ s
  val one_one = TypeBase.one_one_of tyinfo
  val distinct = TypeBase.distinct_of tyinfo
  val _ = save_thm (name"_case_cong",TypeBase.case_cong_of tyinfo)
  val _ = save_thm (name"_induction",TypeBase.induction_of tyinfo)
  val _ = save_thm (name"_nchotomy",TypeBase.nchotomy_of tyinfo)
  val _ = save_thm (name"_Axiom", TypeBase.axiom_of tyinfo)
  val one_one_name =
    case one_one of
      NONE => "NONE"
    | SOME th => (save_thm(name "_11", th); "SOME "^name "_11")
  val distinct_name =
    case distinct of
      NONE => "NONE"
    | SOME th => (save_thm(name "_distinct", th); "SOME "^name "_distinct")
in
  adjoin{ax= name"_Axiom",
         case_def= name"_case_def",
         case_cong= name "_case_cong",
         induction= name "_induction",
         nchotomy= name "_nchotomy",
         size=(#const(const_decl(name "_size")),name "_size_def"),
         one_one= one_one_name,
         distinct= distinct_name}
  extras
end

fun primHol_datatype db q = let
  val parse_result = ParseDatatype.parse q
  val tyinfo_extras = deftype_from_parse parse_result
  val ax = TypeBase.axiom_of (#1 (hd tyinfo_extras))
  val size_defn_thm = define_size ax (tysize_env db)
  val conjs = CONJUNCTS size_defn_thm
  (* given an equivalence relation R, partition a list into a list of lists
     such that everything in each list is related to each other *)
  (* preserves the order of the elements within each partition with
     respect to the order they were given in the original list *)
  fun partition R l = let
    fun partition0 parts [] = parts
      | partition0 parts (x::xs) = let
          fun srch_parts [] = [[x]]
            | srch_parts (p::ps) = if R x (hd p) then (x::p)::ps
                                   else p::(srch_parts ps)
        in
          partition0 (srch_parts parts) xs
        end
  in
    map List.rev (partition0 [] l)
  end
  val head = rator o lhs o #2 o strip_forall o concl
  fun same_head thm1 thm2 = head thm1 = head thm2
  val partitioned_conjs = partition same_head conjs
  val oktypes = Prim_rec.new_types ax
  val ok_types_only =
    List.filter (fn thml =>
                 mem (#1 (dom_rng (type_of (head (hd (thml)))))) oktypes)
    partitioned_conjs
  val conjed_up = map LIST_CONJ ok_types_only
in
  ListPair.map (fn ((tyi, ex), sz_def) =>
                (TypeBase.put_size (defn_const sz_def, sz_def) tyi, ex))
  (tyinfo_extras, conjed_up)
end
handle e as HOL_ERR _ => Raise e;


fun Hol_datatype q = let
  val tyinfos_extras = primHol_datatype (TypeBase.theTypeBase()) q
  fun do_side_effects (x as (tyinfo, _)) = let
  in
    TypeBase.write tyinfo;
    make_tyinfo_persist x
  end
in
  app do_side_effects tyinfos_extras
end

end (* struct *)