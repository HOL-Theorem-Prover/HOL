(*---------------------------------------------------------------------------*
 * Define a HOL datatype and derive a bunch of theorems from it. Return      *
 * these encapsulated in an element of the TypeBasePure.tyinfo type.         *
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
 * as parents, then TypeBasePure.mk_tyinfo can be used directly.             *
 *---------------------------------------------------------------------------*)

(* Interactive:

    app load ["ind_types", "ParseDatatype", "RecordType"];
    open Rsyntax ParseDatatype;
*)

structure Datatype :> Datatype =
struct

open HolKernel Parse boolLib Prim_rec ParseDatatype;

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars

infix ## |-> THEN THENC THENL;
infixr -->;

type hol_type     = Type.hol_type
type thm          = Thm.thm
type tyinfo       = TypeBasePure.tyinfo
type typeBase     = TypeBasePure.typeBase
type 'a quotation = 'a Portable.frag list
type AST          = ParseDatatype.AST;

type field_name   = string
type field_names  = string list
type constructor  = string * hol_type list
type tyspec       = hol_type * constructor list
type record_rw_names = string list

(*---------------------------------------------------------------------------
   A tyspec is a type specification.  The first component is a type
   variable whose name (less the leading quote) is the name of the new
   type.  Each such is accompanied by a list of constructor specifications.
   Such a spec. is a string (the constructor name) and a list of types that
   are the arguments of that constructor.  Recursive occurrences of the
   types are marked by occurrences of the corresponding type variables.
 ---------------------------------------------------------------------------*)

val ERR = mk_HOL_ERR "Datatype";
val num = numSyntax.num

val defn_const =
  #1 o strip_comb o lhs o #2 o strip_forall o hd o strip_conj o concl;

val head = Lib.repeat rator;

local open Portable
      fun num_variant vlist v =
        let val counter = ref 0
            val names = map (fst o dest_var) vlist
            val (Name,Ty) = dest_var v
            fun pass str =
               if mem str names
               then (inc counter; pass (Name^Lib.int_to_string(!counter)))
               else str
        in mk_var(pass Name,  Ty)
        end
in
fun mk_tyvar_size vty (V,away) =
  let val fty = vty --> num
      val v = num_variant away (mk_var("f", fty))
  in (v::V, v::away)
  end
end;

fun tysize_env db = 
     Option.map fst o 
     Option.composePartial (TypeBasePure.size_of, TypeBasePure.get db)


(*---------------------------------------------------------------------------*
 * Term size, as a function of types. The function gamma maps type           *
 * operator "ty" to term "ty_size". Types not registered in gamma are        *
 * translated into the constant function that returns 0. The function theta  *
 * maps a type variables (say 'a) to a term variable "f" of type 'a -> num.  *
 *                                                                           *
 * When actually building a measure function, the behaviour of theta is      *
 * changed to be such that it maps type variables to the constant function   *
 * that returns 0.                                                           *
 *---------------------------------------------------------------------------*)

local fun drop [] ty = fst(dom_rng ty)
        | drop (_::t) ty = drop t (snd(dom_rng ty));
      fun Kzero ty = mk_abs(mk_var("v",ty), numSyntax.zero_tm)
      fun OK f ty M =
         let val (Rator,Rand) = dest_comb M
         in (Rator=f) andalso is_var Rand andalso (type_of Rand = ty)
         end
in
fun tysize (theta,omega,gamma) clause ty =
 case theta ty
  of SOME fvar => fvar
   | NONE =>
      case omega ty
       of SOME (_,[]) => raise ERR "tysize" "bug: no assoc for nested"
        | SOME (_,[(f,szfn)]) => szfn
        | SOME (_,alist) => snd
             (first (fn (f,sz) => Lib.can (find_term(OK f ty)) (rhs clause))
                  alist)
        | NONE =>
           let val (Tyop,Args) = dest_type ty
           in case gamma Tyop
               of SOME f =>
                   let val vty = drop Args (type_of f)
                       val sigma = Type.match_type vty ty
                    in list_mk_comb(inst sigma f,
                                map (tysize (theta,omega,gamma) clause) Args)
                    end
                | NONE => Kzero ty
             end

fun type_size db ty =
  let fun theta ty = if is_vartype ty then SOME (Kzero ty) else NONE
      fun omega ty = NONE
  in
    tysize (theta,omega,tysize_env db) ty
  end
end;

fun dupls [] (C,D) = (rev C, rev D)
  | dupls (h::t) (C,D) = dupls t (if mem h t then (C,h::D) else (h::C,D));

fun crunch [] = []
  | crunch ((x,y)::t) =
    let val key = #1(dom_rng(type_of x))
        val (yes,no) = partition (fn(x,_) => (#1(dom_rng(type_of x))=key)) t
    in (key, (x,y)::yes)::crunch no
    end;

local open arithmeticTheory
      val zero_rws = [Rewrite.ONCE_REWRITE_RULE [ADD_SYM] ADD_0, ADD_0]
      val Zero  = numSyntax.zero_tm
      val One   = Term `1n`
in
fun define_size ax db =
 let val dtys = Prim_rec.doms_of_tyaxiom ax  (* primary types in axiom *)
     val tyvars = Lib.U (map (snd o dest_type) dtys)
     val (_, abody) = strip_forall(concl ax)
     val (exvs, ebody) = strip_exists abody
     (* list of all constructors with arguments *)
     val conjl = strip_conj ebody
     val bare_conjl = map (snd o strip_forall) conjl
     val capplist = map (rand o lhs) bare_conjl
     val def_name = fst(dest_type(type_of(hd capplist)))
     (* 'a -> num variables : size functions for type variables *)
     val fparams = rev(fst(rev_itlist mk_tyvar_size tyvars
                             ([],free_varsl capplist)))
     val fparams_tyl = map type_of fparams
     fun proto_const n ty =
         mk_var(n, itlist (curry op-->) fparams_tyl (ty --> num))
     fun tyop_binding ty =
       let val root_tyop = fst(dest_type ty)
       in (root_tyop, (ty, proto_const(root_tyop^"_size") ty))
       end
     val tyvar_map = zip tyvars fparams
     val tyop_map = map tyop_binding dtys
     fun theta tyv =
          case assoc1 tyv tyvar_map
           of SOME(_,f) => SOME f
            | NONE => NONE
     val type_size_env = tysize_env db
     fun gamma str =
          case assoc1 str tyop_map
           of NONE  => type_size_env str
            | SOME(_,(_, v)) => SOME v
     (* now the ugly nested map *)
     val head_of_clause = head o lhs o snd o strip_forall
     fun is_dty M = mem(#1(dom_rng(type_of(head_of_clause M)))) dtys
     val (dty_clauses,non_dty_clauses) = partition is_dty bare_conjl
     val dty_fns = fst(dupls (map head_of_clause dty_clauses) ([],[]))
     fun dty_size ty =
        let val (d,r) = dom_rng ty
        in list_mk_comb(proto_const(fst(dest_type d)^"_size") d,fparams)
        end
     val dty_map = zip dty_fns (map (dty_size o type_of) dty_fns)
     val non_dty_fns = fst(dupls (map head_of_clause non_dty_clauses) ([],[]))
     fun nested_binding (n,f) =
        let val name = String.concat[def_name,Lib.int_to_string n,"_size"]
            val (d,r) = dom_rng (type_of f)
            val proto_const = proto_const name d
        in (f, list_mk_comb (proto_const,fparams))
       end
     val nested_map0 = map nested_binding (enumerate 1 non_dty_fns)
     val nested_map1 = crunch nested_map0
     fun omega ty = assoc1 ty nested_map1
     val sizer = tysize(theta,omega,gamma)
     fun mk_app cl v = mk_comb(sizer cl (type_of v), v)
     val fn_i_map = dty_map @ nested_map0
     fun clause cl =
         let val (fn_i, capp) = dest_comb (lhs cl)
         in
         mk_eq(mk_comb(assoc fn_i fn_i_map, capp),
               case snd(strip_comb capp)
                of [] => Zero
                 | L  => end_itlist (curry numSyntax.mk_plus)
                                    (One::map (mk_app cl) L))
         end
     val pre_defn0 = list_mk_conj (map clause bare_conjl)
     val pre_defn1 = rhs(concl   (* remove zero additions *)
                      ((DEPTH_CONV BETA_CONV THENC
                        Rewrite.PURE_REWRITE_CONV zero_rws) pre_defn0))
     val defn = new_recursive_definition
                 {name=def_name^"_size_def",
                  rec_axiom=ax, def=pre_defn1}
     val cty = (I##(type_of o last)) o strip_comb o lhs o snd o strip_forall
     val ctyl = Lib.mk_set (map cty (strip_conj (concl defn)))
     val const_tyl = gather (fn (c,ty) => mem ty dtys) ctyl
     val const_tyopl = map (fn (c,ty) => (c,fst(dest_type ty))) const_tyl
 in
    SOME {def=defn,const_tyopl=const_tyopl}
 end
 handle HOL_ERR _ => NONE
end;

(*---------------------------------------------------------------------------
           Basic datatype definition support
 ---------------------------------------------------------------------------*)

val define_type = ind_types.define_type;


(*---------------------------------------------------------------------------
      Support for quoted input
 ---------------------------------------------------------------------------*)
       
local fun find_dup [] = NONE
        | find_dup [x] = NONE
        | find_dup (x::y::xs) = if x=y then SOME x else find_dup (y::xs)
in
val duplicate_names = find_dup o Listsort.sort String.compare
end;

local fun tyname_as_tyvar n = mk_vartype ("'" ^ n)
      fun stage1 (s,Constructors l) = (s,l)
        | stage1 (s,Record fields)  = (s,[(s,map snd fields)])
      fun check_fields (s,Record fields) =
          (case duplicate_names (map fst fields)
           of NONE => ()
            | SOME n => raise ERR "check_fields" ("Duplicate field name: "^n))
        | check_fields _ = ()
      fun cnames (s,Record _) A = s::A
        | cnames (_,Constructors l) A = map fst l @ A
      fun check_constrs asts =
            case duplicate_names (itlist cnames asts [])
             of NONE => ()
              | SOME n => raise ERR "check_constrs"
                       ("Duplicate constructor name: "^n)
in
fun to_tyspecs ASTs =
 let val _ = List.app check_fields ASTs
     val _ = check_constrs ASTs
     val asts = map stage1 ASTs
     val new_type_names = map #1 asts
     fun mk_hol_type (dAQ ty) = ty
       | mk_hol_type (dVartype s) = mk_vartype s
       | mk_hol_type (dTyop{Tyop = s, Args, Thy}) =
            if Lib.mem s new_type_names
            then if null Args then tyname_as_tyvar s
                 else raise ERR "to_tyspecs"
                     "Can't use new types as operators - leave them nullary"
            else
              case Thy of
                NONE => mk_type(s, map mk_hol_type Args)
              | SOME t => mk_thy_type {Tyop = s, Thy = t,
                                       Args = map mk_hol_type Args}
     val mk_hol_type0 = mk_hol_type
     fun mk_hol_type pty = let
       val ty = mk_hol_type0 pty
     in
       if Theory.uptodate_type ty then ty
       else let val tyname = #1 (dest_type ty)
            in raise ERR "to_tyspecs" (tyname^" not up-to-date")
            end
     end

     fun constructor (cname, ptys) = (cname, map mk_hol_type ptys)
  in
     map (tyname_as_tyvar##map constructor) asts
  end
end;

val new_asts_datatype  = define_type o to_tyspecs;
fun new_datatype q     = new_asts_datatype (ParseDatatype.parse q);


(* ----------------------------------------------------------------------
    Determine if a parsed type spec is calling for an enumerated type
   ---------------------------------------------------------------------- *)

(* returns false if there is more than one type called for.  Really, *)
(* if there is more than one type, but they are all for enumerated types *)
(* we should be able to disentangle them and call type definition for each *)
(* of them independently *)

fun is_enum_type_spec astl =
    case astl of
      [(ty,Constructors constrs)] => List.all (null o #2) constrs
    (* recall that constrs is a list of constr-name - type arguments pairs *)
    | _ => false


(* ----------------------------------------------------------------------
    Build a tyinfo list for an enumerated type.
   ---------------------------------------------------------------------- *)

fun build_enum_tyinfo (tyname, ast) =
 let open EnumType
 in case ast
     of Constructors clist => (enum_type_to_tyinfo (tyname, map #1 clist))
      | otherwise => raise ERR "build_enum_tyinfo" "Should never happen"
 end

fun build_enum_tyinfos astl = map build_enum_tyinfo astl



(*---------------------------------------------------------------------------
    Returns a list of tyinfo thingies
 ---------------------------------------------------------------------------*)

fun build_tyinfos db {induction,recursion} =
 let val case_defs = Prim_rec.define_case_constant recursion
     val tyinfol = TypeBasePure.gen_tyinfo
                      {ax=recursion, ind=induction, case_defs=case_defs}
 in case define_size recursion db
     of NONE => (HOL_MESG "Couldn't define size function"; tyinfol)
      | SOME {def,const_tyopl} =>
        (case tyinfol
         of [] => raise ERR "build_tyinfos" "empty tyinfo list"
          | tyinfo::rst =>
             let val first_tyname = TypeBasePure.ty_name_of tyinfo
                 fun insert_size info size_eqs =
                    let val tyname = TypeBasePure.ty_name_of info
                    in case assoc2 tyname const_tyopl
                       of SOME(c,tyop) =>
                            TypeBasePure.put_size(c,size_eqs) info
                        | NONE => (HOL_MESG
                                     ("Can't find size constant for"^tyname);
                                    raise ERR "build_tyinfos" "")
                    end
             in insert_size tyinfo (TypeBasePure.ORIG def)
                :: map(C insert_size (TypeBasePure.COPY(first_tyname,def))) rst
             end
             handle HOL_ERR _ => tyinfol)
 end;

local fun add_record_facts (tyinfo, NONE) = (tyinfo, [])
        | add_record_facts (tyinfo, SOME fields) =
               RecordType.prove_recordtype_thms (tyinfo, fields);
      fun field_names_of (_,Record l) = SOME (map fst l)
        | field_names_of _ = NONE
in
fun primHol_datatype db q =
 let val astl = ParseDatatype.parse q
 in
    if is_enum_type_spec astl
      then build_enum_tyinfos astl
      else map add_record_facts
                 (zip (build_tyinfos db (new_asts_datatype astl))
                      (map field_names_of astl))
 end
end (* local *)



(*---------------------------------------------------------------------------

    For a datatype named "ty", Hol_datatype stores the following
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

fun adjoin {ax,case_def,case_cong,induction,nchotomy,
            one_one,distinct,boolify,size} record_rw_names 
  =
 adjoin_to_theory
   {sig_ps = NONE,
    struct_ps = SOME
     (fn ppstrm =>
      let val S = PP.add_string ppstrm
          fun NL() = PP.add_newline ppstrm
          fun do_size NONE = (S "         size = NONE,"; NL())
            | do_size (SOME (c,s)) =
               let val strc = String.concat
                     ["(", term_to_string c, ") ",type_to_string (type_of c)]
                   val line = String.concat ["SOME(Parse.Term`", strc, "`,"]
               in S ("         size="^line); NL();
                  S ("                   "^s^"),")
               end
          fun do_boolify NONE = (S "         boolify = NONE,"; NL())
            | do_boolify (SOME (c,s)) =
               let val strc = String.concat
                     ["(", term_to_string c, ") ",type_to_string (type_of c)]
                   val line = String.concat ["SOME(Parse.Term`", strc, "`,"]
               in S ("         boolify="^line); NL();
                  S ("                   "^s^"),")
               end
          fun do_simpls() = (S "["; app S (Lib.commafy record_rw_names); S "]")
          fun do_field_rws() =
            if null record_rw_names then (S " tyinfo0;")
            else (NL();S "       (TypeBasePure.put_simpls ("; do_simpls();
                  S " @ TypeBasePure.simpls_of tyinfo0) tyinfo0);")
      in
        S "val _ =";                                      NL();
        S "   let open TypeBasePure ";                    NL();
        S "       val tyinfo0 = mk_tyinfo";               NL();
        S ("        {ax="^ax^",");                        NL();
        S ("         case_def="^case_def^",");            NL();
        S ("         case_cong="^case_cong^",");          NL();
        S ("         induction="^induction^",");          NL();
        S ("         nchotomy="^nchotomy^",");            NL();
        do_size size;                                     NL();
        do_boolify boolify;                               NL();
        S ("         one_one="^one_one^",");              NL();
        S ("         distinct="^distinct^"}");            NL();
        S "   in";                                        NL();
        S "    TypeBase.write "; do_field_rws();          NL();
        S "    computeLib.write_datatype_info tyinfo0";   NL();
        S "   end;";                                      NL()
      end)};

fun write_tyinfo (tyinfo, record_rw_names) =
 let open TypeBasePure
     fun name s = ty_name_of tyinfo ^ s
     val one_one_name =
       case one_one_of tyinfo
        of NONE => "NONE"
         | SOME th =>
            let val nm = name"_11" in save_thm(nm, th); "SOME "^nm end
     val distinct_name =
       case distinct_of tyinfo
        of NONE => "NONE"
         | SOME th =>
            let val nm = name"_distinct" in save_thm(nm,th); "SOME "^nm end
     val case_cong_name =
        let val ccname = name"_case_cong"
        in save_thm (ccname,case_cong_of tyinfo);
           ccname
        end
     val nchotomy_name =
       let val nchname = name"_nchotomy"
       in save_thm (nchname,nchotomy_of tyinfo);
          nchname
       end
     val axiom_name =
        let val axname = name"_Axiom"
        in
        case axiom_of0 tyinfo
         of ORIG th => (save_thm (axname, th); "ORIG "^axname)
          | COPY (s,th) => "COPY ("^Lib.quote s^","^s^"_Axiom)"
        end
     val induction_name =
        let val indname = name"_induction"
        in
        case induction_of0 tyinfo
         of ORIG th => (save_thm (indname, th); "ORIG "^indname)
          | COPY (s,th) => "COPY ("^Lib.quote s^","^s^"_induction)"
        end
     val size_info =
       let val sd_name = name"_size_def"
       in
       case size_of0 tyinfo
        of NONE => NONE
         | SOME (tm, ORIG def) => SOME (tm, "ORIG "^sd_name)
         | SOME (tm, COPY(s,def))
            => SOME (tm, "COPY ("^Lib.quote s^","^s^"_size_def)")
       end
     val boolify_info =
       let val sd_name = name"_to_bool_def"
       in
       case boolify_of0 tyinfo
        of NONE => NONE
         | SOME (tm, ORIG def) => SOME (tm, "ORIG "^sd_name)
         | SOME (tm, COPY(s,def))
            => SOME (tm, "COPY ("^Lib.quote s^","^s^"_to_bool_def)")
       end
 in
  adjoin{ax        = axiom_name,
         induction = induction_name,
         case_def  = name"_case_def",
         case_cong = case_cong_name,
         nchotomy  = nchotomy_name,
         size      = size_info,
         boolify   = boolify_info,
         one_one   = one_one_name,
         distinct  = distinct_name}
     record_rw_names
 end;



fun persistent_tyinfo (x as (tyinfo,_)) =
   (TypeBase.write tyinfo;
    computeLib.write_datatype_info tyinfo;
    write_tyinfo x)

fun Hol_datatype q = let
  val tyinfos_etc = primHol_datatype (TypeBase.theTypeBase()) q
  val tynames = map (Lib.quote o TypeBasePure.ty_name_of o #1) tyinfos_etc
  val message = "Defined "^(if length tynames > 1 then "types" else "type")^
                ": "^String.concat (Lib.commafy tynames)
in
  List.app persistent_tyinfo tyinfos_etc;
  HOL_MESG message
end handle ? => Raise (wrap_exn "Datatype" "Hol_datatype" ?);



end (* struct *)
