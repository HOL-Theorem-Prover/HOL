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
 * as parents, then TypeBasePure.mk_datatype_info can be used directly.      *
 *---------------------------------------------------------------------------*)

(* Interactive:

    app load ["ind_types", "ParseDatatype", "RecordType"];
    open Rsyntax ParseDatatype;
*)

structure Datatype :> Datatype =
struct

open HolKernel Parse boolLib Prim_rec ParseDatatype DataSize
local open ind_typeTheory in end;

type hol_type     = Type.hol_type
type thm          = Thm.thm
type tyinfo       = TypeBasePure.tyinfo
type typeBase     = TypeBasePure.typeBase
type 'a quotation = 'a Portable.frag list
type AST          = ParseDatatype.AST;

type record_rw_names = string list

type field_name   = string
type field_names  = string list
type constructor  = string * hol_type list

(*---------------------------------------------------------------------------
   A tyspec is a type specification.  The first component is a type
   variable whose name (less the leading quote) is the name of the new
   type.  Each such is accompanied by a list of constructor specifications.
   Such a spec. is a string (the constructor name) and a list of types that
   are the arguments of that constructor.  Recursive occurrences of the
   types are marked by occurrences of the corresponding type variables.
 ---------------------------------------------------------------------------*)

type tyspec = hol_type * constructor list


(* Fix the grammar used by this file *)
val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars arithmeticTheory.arithmetic_grammars;

val ERR = mk_HOL_ERR "Datatype";

val empty_stringset = HOLset.empty String.compare

(*---------------------------------------------------------------------------
           Basic datatype definition support
 ---------------------------------------------------------------------------*)

val define_type = ind_types.define_type;

(*---------------------------------------------------------------------------*)
(* Generate a string that, when evaluated as ML, will create the given type. *)
(* Copied from TheoryPP.sml. Parameterized by strings representing code that *)
(* builds type variables or compound types.                                  *)
(*---------------------------------------------------------------------------*)

val extern_type = TheoryPP.pp_type

fun with_parens pfn x =
  let open Portable PP
  in block CONSISTENT 1 [add_string "(", pfn x, add_string ")"]
  end

fun pp_fields fields =
 let open Portable PP
     fun pp_field (s,ty) =
       block CONSISTENT 0 [
         add_string ("("^Lib.quote s),
         add_string ",",
         extern_type "U" "T" ty,
         add_string ")"
       ]
 in
  block CONSISTENT 0 [
    add_string "let fun T s t A = mk_thy_type{Thy=t,Tyop=s,Args=A}", NL,
    add_string "    val U = mk_vartype", NL,
    add_string "in", NL,
    block CONSISTENT 1 [
      add_string "[",
      block INCONSISTENT 0 (
        pr_list pp_field [add_string ",", add_break (1,0)] fields
      ),
      add_string "]"
    ],
    add_string "end"
  ]
 end


(*---------------------------------------------------------------------------
      Support for quoted input
 ---------------------------------------------------------------------------*)

local fun find_dup [] = NONE
        | find_dup [x] = NONE
        | find_dup (x::y::xs) = if x=y then SOME x else find_dup (y::xs)
in
val duplicate_names = find_dup o Listsort.sort String.compare
end;

fun prim_mk_type (Thy, Tyop) = let
  val arity = valOf (Type.op_arity {Thy = Thy, Tyop = Tyop})
in
  Type.mk_thy_type {Thy = Thy, Tyop = Tyop,
                    Args = List.tabulate (arity, fn n => Type.alpha)}
end

val mk_recordtype_constructor = TypeBasePure.mk_recordtype_constructor

fun check_constrs_unique_in_theory asts = let
  fun cnames (s, Record _) = [(s,mk_recordtype_constructor s)]
    | cnames (s, Constructors l) = map (fn s' => (s, #1 s')) l
  val newtypes = map #1 asts
  val constrs = List.concat (map cnames asts)
  val current_types = set_diff (map fst (types "-")) newtypes
  fun current_constructors (tyname, fm) = let
    val tys_cons =
        TypeBase.constructors_of (prim_mk_type (current_theory(), tyname))
        handle HOL_ERR _ => []
    fun foldthis (c,fm) =
        if uptodate_term c then
          Binarymap.insert(fm, #Name (dest_thy_const c), tyname)
        else fm
  in
    foldl foldthis fm tys_cons
  end
  val current_constructors =
      List.foldl current_constructors (Binarymap.mkDict String.compare)
                 current_types
  fun calculate_intersection ((tyname, conname), acc) =
      case Binarymap.peek(current_constructors, conname) of
        NONE => acc
      | SOME ty' => (tyname, conname, ty') :: acc
  val common = List.rev (foldl calculate_intersection [] constrs)

  fun warn (newty, conname, oldty) =
      HOL_WARNING "Datatype" "Hol_datatype"
      ("Constructor \""^conname^"\" in new type \""^newty^"\"\n\
       \               duplicates constructor in type \""^oldty^"\", \
       \which will be\n\
       \               invalidated by this definition")
in
  app warn common
end

fun ast_tyvar_strings (dAQ ty) = map dest_vartype $ type_vars ty
  | ast_tyvar_strings (dVartype s) = [s]
  | ast_tyvar_strings (dTyop {Args, ...}) =
      List.concat (map ast_tyvar_strings Args)

val typecheck_listener : (string Symtab.table * pretype * hol_type) Listener.t =
    Listener.new_listener()

local
  fun strvariant avoids s = if mem s avoids then strvariant avoids (s ^ "a")
                            else s
  fun tyname_as_tyvar n = mk_vartype ("'" ^ n)
  fun stage1 (s,Constructors l) = (s,l)
    | stage1 (s,Record fields)  = (s,[(mk_recordtype_constructor s,
                                       map snd fields)])
  fun check_fields (s,Record fields) =
      (case duplicate_names (map fst fields) of
           NONE => ()
         | SOME n => raise ERR "check_fields" ("Duplicate field name: "^n))
    | check_fields _ = ()
  fun cnames (s,Record _) A = s::A
    | cnames (_,Constructors l) A = map fst l @ A
  fun check_constrs asts =
      case duplicate_names (itlist cnames asts []) of
          NONE => ()
        | SOME n => raise ERR "check_constrs"
                          ("Duplicate constructor name: "^n)
in
fun to_tyspecs ASTs =
 let val _ = List.app check_fields ASTs
     val _ = check_constrs ASTs
     val _ = check_constrs_unique_in_theory ASTs
     val asts = map stage1 ASTs
     val new_type_names = map #1 asts

     fun mk_hol_ty d (dAQ ty) = ty
       | mk_hol_ty d (dVartype s) = mk_vartype (valOf $ Symtab.lookup d s)
       | mk_hol_ty d (dTyop{Tyop=s, Args, Thy}) =
            if Lib.mem s new_type_names andalso
               (Thy = NONE orelse Thy = SOME (current_theory()))
            then if null Args then tyname_as_tyvar s
                 else raise ERR "to_tyspecs"
                     ("Omit arguments to new type:"^Lib.quote s)
            else
              case Thy of
                NONE => mk_type(s, map (mk_hol_ty d) Args)
              | SOME t => mk_thy_type {Tyop = s, Thy = t,
                                       Args = map (mk_hol_ty d) Args}
     fun mk_hol_type d pty = let
       val ty = mk_hol_ty d pty
       val _ = Listener.call_listener typecheck_listener (d, pty, ty)
     in
       if Theory.uptodate_type ty then ty
       else let val tyname = #1 (dest_type ty)
            in raise ERR "to_tyspecs" (tyname^" not up-to-date")
            end
     end
     val allvars = let
       fun perc ((cnm, ptys), A) =
           List.foldl
             (fn (pt,A) => HOLset.addList(A,ast_tyvar_strings pt)) A ptys
       fun perty ((nm, cs), A) = List.foldl perc A cs
     in
       HOLset.listItems (List.foldl perty (HOLset.empty String.compare) asts)
     end
     val (dict,_) = List.foldl
                  (fn (nm, (d,avds)) =>
                      let val nm' = strvariant avds nm
                      in
                        (Symtab.update(nm,nm') d, nm'::avds)
                      end)
                  (Symtab.empty, map (fn (s,_) => "'" ^ s) asts)
                  allvars
     fun constructor (cname, ptys) = (cname, map (mk_hol_type dict) ptys)
  in
    map (tyname_as_tyvar ## map constructor) asts
  end
end;

fun tyspecs_of tyg q = to_tyspecs (ParseDatatype.parse tyg q);

val new_asts_datatype = define_type o to_tyspecs;
fun new_datatype q =
  new_asts_datatype (ParseDatatype.parse (type_grammar()) q);


(*---------------------------------------------------------------------------*)
(* Determine if a parsed type spec is calling for an enumerated type.        *)
(* Returns false if there is more than one type called for, because an       *)
(* earlier sorting process will ensure that enumerated types are presented   *)
(* singly.                                                                   *)
(*---------------------------------------------------------------------------*)

fun is_enum_type_spec astl =
    case astl of
      [(ty,Constructors constrs)] => List.all (null o #2) constrs
    (* recall that constrs is a list of constr-name - type arguments pairs *)
    | _ => false


(*---------------------------------------------------------------------------*)
(*  Build a tyinfo list for an enumerated type.                              *)
(*---------------------------------------------------------------------------*)

fun build_enum_tyinfo (tyname, ast) =
 let open EnumType
 in case ast
    of Constructors clist =>
       let val constructors = map #1 clist
       in case duplicate_names constructors
          of NONE => (enum_type_to_tyinfo (tyname, constructors))
           | SOME s => raise ERR "build_enum"("Duplicate constructor name: "^s)
       end
    | otherwise => raise ERR "build_enum_tyinfo" "Should never happen"
end

fun build_enum_tyinfos astl = let
  val _ = check_constrs_unique_in_theory astl
in
  map build_enum_tyinfo astl
end


(*---------------------------------------------------------------------------
    Returns a list of tyinfo thingies
 ---------------------------------------------------------------------------*)

local
  fun insert_size {def, const_tyopl} tyinfol =
   case tyinfol
    of [] => raise ERR "build_tyinfos" "empty tyinfo list"
     | tyinfo::rst =>
       let val first_tyname = TypeBasePure.ty_name_of tyinfo
           fun insert_size info size_eqs =
            let val tyname = TypeBasePure.ty_name_of info
            in case assoc2 tyname const_tyopl
                of SOME(c,tyop) => TypeBasePure.put_size(c,size_eqs) info
                 | NONE => (HOL_MESG
                              ("Can't find size constant for"^(snd tyname))
                             ; raise ERR "build_tyinfos" "")
            end
       in
         insert_size tyinfo (TypeBasePure.ORIG def)
         :: map (C insert_size (TypeBasePure.COPY (first_tyname,def))) rst
       end
       handle HOL_ERR _ => tyinfol
in

fun build_tyinfos db {induction,recursion} =
 let val case_defs = Prim_rec.define_case_constant recursion
     val tyinfol = TypeBasePure.gen_datatype_info
                    {ax=recursion, ind=induction, case_defs=case_defs}
 in
   case define_size {induction = induction, recursion = recursion} db
    of NONE => (HOL_MESG "Couldn't define size function"; tyinfol)
     | SOME s => insert_size s tyinfol
    end
end;

(* ----------------------------------------------------------------------
    Topological sort of datatype declarations so that the system can
    automatically separate out those types that aren't recursively linked
   ---------------------------------------------------------------------- *)

fun pretype_ops acc ptysl =
    (* find all of the operator names in a list of pretype lists *)
    case ptysl of
      [] => acc
    | (ptys :: rest) => let
      in
        case ptys of
          [] => pretype_ops acc rest
        | (pty :: more_ptys) => let
          in
            case pty of
              dTyop {Args, Thy, Tyop} =>
              pretype_ops (HOLset.add(acc, Tyop)) (Args :: more_ptys :: rest)
            | _ => pretype_ops acc (more_ptys :: rest)
          end
      end

fun build_reference_matrix astl = let
  (* turns a astl into an adjacency matrix, position (n,m) is true if
     ast n refers to ast m. *)
  val newnames = map #1 astl
  val n = length newnames
  exception NoDex
  fun dex s [] = raise NoDex
    | dex s (h::t) = if s = h then 0 else 1 + dex s t
  val array = Array2.array(n,n,false)
  fun refers_to ast =
      case ast of
        Record flds => let
          fun foldthis ((_, pty), acc) = pretype_ops acc [[pty]]
        in
          foldl foldthis (HOLset.empty String.compare) flds
        end
      | Constructors cs => let
          fun foldthis ((_, ptys), acc) = pretype_ops acc [ptys]
        in
          foldl foldthis (HOLset.empty String.compare) cs
        end
  fun record_refs (tyname, ast) = let
    val i = dex tyname newnames
    fun appthis s = Array2.update(array, i, dex s newnames, true)
                    handle NoDex => ()
  in
    HOLset.app appthis (refers_to ast)
  end
in
  app record_refs astl ;
  array
end

fun calculate_transitive_closure a = let
  (* updates a 2D array so that it represents the transitive closure of the
     relation it used to represent  O(n^3) *)
  open Array2
  nonfix via
  val n = nCols a
  fun check i =
      modifyi RowMajor
              (fn (j,k,v) => v orelse (sub(a,j,i) andalso sub(a,i,k)))
              { base = a, row = 0, col = 0, nrows = NONE, ncols = NONE}
  fun via i =
      if i = n then ()
      else (check i ; via (i + 1))
in
  via 0
end

fun topo_sort a = let
  (* return the elements of the graph in a topological order,
     treating elements in loops as equivalent.  Function returns a list of
     lists of integers, where the integers index the nodes.  Lists are
     never empty.  If not singleton, this represents a loop *)
  open Array2
  val n = nRows a
  fun findloops () = let
    (* return a list of lists,  not sorted topologically, but which
       encompasses loop structure *)
    val done = Array.array(n, false)
    fun check_row i = let
      fun findothers acc j =
          if j = n then List.rev acc
          else if sub(a, i, j) andalso sub(a, j, i) andalso i <> j then
            (Array.update(done, j, true);
             findothers (j::acc) (j + 1))
          else findothers acc (j + 1)
    in
      findothers [i] 0
    end
    fun check_rows i =
        if i = n then []
        else if Array.sub(done, i) then check_rows (i + 1)
        else (check_row i :: check_rows (i + 1))
  in
    check_rows 0
  end
  val blocks = findloops()
  fun zero_column j =
      modifyi ColMajor (fn _ => false)
              {base = a, col = j, row = 0, nrows = NONE, ncols = SOME 1}
  fun pull_out_next bs =
      case bs of
        [] => raise Fail "Can't happen"
      | [b] => (List.app zero_column b; (b, []))
      | b :: rest => let
          val i = hd b
          fun check j =
              (* j and later indices are ok iff : *)
              j = n orelse
              ((not (sub(a, i, j)) orelse mem j b) andalso
               check (j + 1))
        in
          if check 0 then (List.app zero_column b; (b, rest))
          else let
              val (best, rest') = pull_out_next rest
            in
              (best, (b :: rest'))
            end
        end
  fun pull_out_oks blist =
      case blist of
        [] => []
      | _ => let
          val (b, rest) = pull_out_next blist
        in
          b :: pull_out_oks rest
        end
in
  pull_out_oks blocks
end

fun sort_astl astl = let
  val adjs = build_reference_matrix astl
  val _ = calculate_transitive_closure adjs
  val sorted = topo_sort adjs
  fun dex_to_astl i = List.nth(astl, i)
in
  map (map dex_to_astl) sorted
end


(*---------------------------------------------------------------------------*)
(*   Do the hard work of type definition                                     *)
(*                                                                           *)
(* [tyis] is a list of tyinfos coupled with strings representing how to      *)
(*   recreate them (strings which when eval-ed will be a function of type    *)
(*   tyinfo -> tyinfo; these functions will be applied to the basic tyinfo   *)
(*   created for the record type).                                           *)
(*                                                                           *)
(* [thminfo_list] is of type                                                 *)
(*        (string * (string * thm) list * (string * hol_type) list) list,    *)
(*                                                                           *)
(*   basically an association list from type names to extra stuff.           *)
(*   The second component of each triple is theorems which need to be        *)
(*   added to the corresponding tyinfos, and they are accompanied by         *)
(*   the names under which they have been stored in the theory               *)
(*   segment.  The third component is field information for that type.       *)
(*                                                                           *)
(* [persistp] is true iff we need to adjoin stuff to make the change         *)
(*    persistent.                                                            *)
(*---------------------------------------------------------------------------*)

val tyi_compare =
   inv_img_cmp TypeBasePure.ty_name_of
               (Lib.pair_compare(String.compare,String.compare))

fun alist_comp ((s1,_,_), (s2,_,_)) = String.compare(s1,s2);

fun augment_tyinfos tyis thminfo_list = let
  val tyis = Listsort.sort tyi_compare tyis
  val thminfo_list = Listsort.sort alist_comp thminfo_list
  type thmdata = (string * thm) list
  type flddata = (string * TypeBase.rcd_fieldinfo) list * thm list * thm list
  fun merge acc tyis (thmi_list : (string * thmdata * flddata) list) =
      case (tyis, thmi_list) of
        ([], _ :: _ ) => raise Fail "Datatype.sml: invariant failure 101"
      | ([],[]) => acc
      | (_, []) => tyis @ acc
      | (tyi::tyi_rest, (th_s, thms, flds)::thmi_rest) => let
        in
          case String.compare (snd(TypeBasePure.ty_name_of tyi), th_s) of
            LESS => merge (tyi::acc) tyi_rest thmi_list
          | GREATER => raise Fail "Datatype.sml: invariant failure 102"
          | EQUAL => let
              val tyi' = RecordType.update_tyinfo (SOME flds) (map #2 thms) tyi
            in
              merge (tyi' :: acc) tyi_rest thmi_rest
            end
        end
in
  merge [] tyis thminfo_list
end


local
  fun add_record_facts (tyinfo, NONE) = tyinfo
    | add_record_facts (tyinfo, SOME fields) =
      RecordType.prove_recordtype_thms (tyinfo, fields)
  fun field_names_of (_,Record l) = SOME (map fst l)
    | field_names_of _ = NONE
  fun astpty_map f ast = let
    open ParseDatatype
  in
    case ast of
      Constructors clist =>
        Constructors (map (fn (s, ptys) => (s, map f ptys)) clist)
    | Record flds => Record (map (fn (s, pty) => (s, f pty)) flds)
  end
  fun reform_tyops prevtypes pty = let
    open ParseDatatype
  in
    case pty of
      dTyop{Tyop, Thy, Args} => let
      in
        case (Lib.assoc1 Tyop prevtypes, Args) of
          (SOME (_, strset), []) => let
            val thytyop =
                case Thy of
                  NONE => hd (Type.decls Tyop)
                | SOME s => {Thy = s, Tyop = Tyop}
            val arity = valOf (Type.op_arity thytyop)
            val _ = arity = HOLset.numItems strset orelse
                    raise ERR "reform_tyops" (Tyop ^ " has unexpected arity")
          in
            dTyop{Tyop = Tyop, Thy = Thy,
                  Args = map dVartype (HOLset.listItems strset)}
          end
        | _ => dTyop{Tyop = Tyop, Thy = Thy,
                     Args = map (reform_tyops prevtypes) Args}
      end
    | _ => pty
  end

  fun insert_tyarguments prevtypes astl =
      map (fn (s, dt) => (s, astpty_map (reform_tyops prevtypes) dt)) astl

  fun getfldinfo bigrecinfo = let
      fun mapthis (s, l) = (s, map (I ## ParseDatatype.pretypeToType) l)
  in
      map mapthis bigrecinfo
  end
  fun merge_alists alist1 alist2 = let
      fun recurse acc alist1 alist2 =
          case (alist1, alist2) of
              ([], []) => List.rev acc
            | (_, []) => List.rev acc @ map (fn (s,d) => (s, d, ([],[],[]))) alist1
            | ([], _) => List.rev acc @ map (fn (s,d) => (s, [],(d,[],[]))) alist2
            | ((a1k, a1d)::a1s, (a2k, a2d)::a2s) =>
              case String.compare (a1k, a2k) of
                  LESS => recurse ((a1k,a1d,([],[],[])) :: acc) a1s alist2
                | EQUAL => recurse ((a1k,a1d,(a2d,[],[])) :: acc) a1s a2s
                | GREATER => recurse ((a2k,[],(a2d,[],[])) :: acc) alist1 a2s
      fun alistcomp ((s1, d1), (s2, d2)) = String.compare(s1, s2)
  in
      recurse [] (Listsort.sort alistcomp alist1) (Listsort.sort alistcomp alist2)
  end

in
(*---------------------------------------------------------------------------*)
(* precondition: astl has been sorted, so that, for example,  those          *)
(* ast elements not referring to any others will be present only as          *)
(*     singleton lists                                                       *)
(*---------------------------------------------------------------------------*)

fun prim_define_type_from_astl prevtypes f db astl0 = let
  val astl = insert_tyarguments prevtypes astl0
in
  if is_enum_type_spec astl then (db, build_enum_tyinfos astl)
  else (db,
        map add_record_facts
            (zip (build_tyinfos db (new_asts_datatype astl))
                 (map field_names_of astl)))
end (* let *)
end (* local *)


fun find_vartypes (pty, acc) =
 let open ParseDatatype
 in
  case pty of
    dVartype s => HOLset.add(acc, s)
  | dAQ ty => List.foldl (fn (ty, acc) => HOLset.add(acc, dest_vartype ty))
                         acc (Type.type_vars ty)
  | dTyop {Args, ...} => List.foldl find_vartypes acc Args
 end

fun dtForm_vartypes (dtf, acc) =
    case dtf of
      Constructors clist => List.foldl (fn ((s, ptyl), acc) =>
                                           List.foldl find_vartypes acc ptyl)
                                       acc clist
    | Record fldlist => List.foldl
                          (fn ((s, pty), acc) => find_vartypes (pty, acc))
                          acc fldlist


(*---------------------------------------------------------------------------*)
(* prevtypes below is an association list mapping the names of types         *)
(* previously defined in this "session" to the list of type variables that   *)
(* occurred on the RHS of the type definitions.                              *)
(*---------------------------------------------------------------------------*)

fun define_type_from_astl prevtypes db astl = let
  val sorted_astll = sort_astl astl
  val f = define_type_from_astl
  fun handle_astl (astl, (prevtypes, db, tyinfo_acc)) = let
    val (db, new_tyinfos) = prim_define_type_from_astl prevtypes f db astl
    fun addtyi (tyi, db) = TypeBasePure.insert db tyi
    val alltyvars =
        List.foldl (fn ((_, dtf), acc) => dtForm_vartypes(dtf, acc))
                   empty_stringset
                   astl
  in
    (prevtypes @ map (fn (s, dtf) => (s, alltyvars)) astl,
     List.foldl addtyi db new_tyinfos,
     tyinfo_acc @ new_tyinfos)
  end
  val (_,db,tyinfos) = List.foldl handle_astl (prevtypes, db, []) sorted_astll
in
  (db, tyinfos)
end


fun primHol_datatype db astl = define_type_from_astl [] db astl;

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
        7. ty_to_bool_def   (* encoder for the type *)
        8. lift             (* lifter (ML -> HOL) for the type  *)
        9. one_one          (* one-one-ness of the constructors *)
        10. distinct        (* distinctness of the constructors *)
        11. fields          (* fields, if it is a record type *)
        12. accessors       (* accessors, if it is a record type *)
        13. updates         (* update fns, if it is a record type *)

   We also adjoin some ML to the current theory so that if the theory
   gets exported and loaded in a later session, these "datatype"
   theorems are loaded automatically into theTypeBase.

 ---------------------------------------------------------------------------*)

fun persistent_tyinfo tyinfos =
  let
      fun ovl tyi = Parse.overload_on ("case", TypeBasePure.case_const_of tyi)
      fun save_thms tyi =
        let
          open TypeBasePure
          val tname = snd (ty_name_of tyi)
          fun name s = tname ^ s
          fun optsave nm thopt =
            case thopt of NONE => () | SOME th => ignore (save_thm(name nm, th))
        in
          optsave "_11" (one_one_of tyi);
          optsave "_distinct" (distinct_of tyi);
          save_thm(name "_nchotomy", nchotomy_of tyi);
          save_thm(name "_Axiom", axiom_of tyi);
          save_thm(name "_induction", induction_of tyi);
          save_thm(name "_case_cong", case_cong_of tyi);
          save_thm(name "_case_eq", case_eq_of tyi);
          ()
        end
  in
    TypeBase.export tyinfos;
    app save_thms tyinfos;
    app ovl tyinfos;
    app computeLib.write_datatype_info tyinfos
  end;

(*---------------------------------------------------------------------------*)
(* Construct trivial theorem from which structure of original datatype can   *)
(* be recovered.                                                             *)
(*---------------------------------------------------------------------------*)

fun mk_datatype_presentation thy tyspecl =
  let open ParseDatatype
      fun mkc n = prim_mk_const{Name=n,Thy=thy}
      fun type_dec (tyname,Constructors dforms) =
          let val constrs = map (mkc o #1) dforms
              val tyn_var = mk_var(tyname,list_mk_fun(map type_of constrs,bool))
          in
            list_mk_comb(tyn_var,constrs)
          end
        | type_dec (tyname,Record fields) =
          let
            fun pmc f =
                mkc (TypeBasePure.mk_recordtype_fieldsel
                       {tyname = tyname, fieldname = f})
            val hdc = pmc (#1 (hd fields))
            fun fieldvar (n, _) = let
              val c = pmc n
              val (_, ty) = dom_rng (type_of c)
            in
              mk_var(n, ty)
            end
            val fvars = map fieldvar fields
            val tyn_var = mk_var(tyname,hdc |> type_of |> dom_rng |> #1)
            val record_var =
                mk_var("record",
                       list_mk_fun(type_of tyn_var::map type_of fvars,bool))
          in
            list_mk_comb(record_var,tyn_var::fvars)
          end
  in
   (fst(hd tyspecl),list_mk_conj (map type_dec tyspecl))
  end

fun datatype_thm (n,M) = save_thm
  ("datatype_"^n,
   EQT_ELIM (ISPEC M DATATYPE_TAG_THM));

fun astHol_datatype astl =
 let
  val (_,tyinfos) = primHol_datatype (TypeBase.theTypeBase()) astl
  val _ = Theory.scrub()
  val _ = datatype_thm (mk_datatype_presentation (current_theory()) astl)
  val tynames = map TypeBasePure.ty_name_of tyinfos
  val tynames = map (Lib.quote o snd) tynames
  val message = "Defined type"^(if length tynames > 1 then "s" else "")^
                ": "^String.concat (Lib.commafy tynames)
 in
  persistent_tyinfo tyinfos;
  HOL_MESG message
 end handle e as HOL_ERR _ => Raise (wrap_exn "Datatype" "Hol_datatype" e);

fun Hol_datatype q = astHol_datatype (ParseDatatype.parse (type_grammar()) q)
fun Datatype q = astHol_datatype (ParseDatatype.hparse (type_grammar()) q)

val _ = Parse.temp_set_grammars ambient_grammars

end
