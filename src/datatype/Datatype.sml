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

fun extern_type mk_vartype_str mk_thy_type_str ppstrm ty =
 let open Portable
     val {add_break,add_newline,
          add_string,begin_block,end_block,...} = with_ppstream ppstrm
     val extern = extern_type mk_vartype_str mk_thy_type_str ppstrm

 in
  if is_vartype ty
  then case dest_vartype ty
        of "'a" => add_string "alpha"
         | "'b" => add_string "beta"
         | "'c" => add_string "gamma"
         | "'d" => add_string "delta"
         |   s  => add_string (mk_vartype_str^quote s)
  else
  case dest_thy_type ty
   of {Tyop="bool",Thy="min", Args=[]} => add_string "bool"
    | {Tyop="ind", Thy="min", Args=[]} => add_string "ind"
    | {Tyop="fun", Thy="min", Args=[d,r]}
       => (add_string "(";
           begin_block INCONSISTENT 0;
             extern d;
             add_break (1,0);
             add_string "-->";
             add_break (1,0);
             extern r;
           end_block ();
           add_string ")")
   | {Tyop,Thy,Args}
      => let in
           add_string mk_thy_type_str;
           begin_block INCONSISTENT 0;
           add_string (quote Thy);
           add_break (1,0);
           add_string (quote Tyop);
           add_break (1,0);
           add_string "[";
           begin_block INCONSISTENT 0;
           pr_list extern (fn () => add_string ",")
                          (fn () => add_break (1,0)) Args;
           end_block (); add_string "]";
           end_block ()
         end
 end

fun with_parens pfn ppstrm x =
  let open Portable
  in add_string ppstrm "("; pfn ppstrm x; add_string ppstrm ")"
  end

fun pp_fields ppstrm fields =
 let open Portable
     val {add_break,add_newline,
          add_string,begin_block,end_block,...} = with_ppstream ppstrm
     fun pp_field (s,ty) =
        (begin_block CONSISTENT 0;
         add_string ("("^Lib.quote s);
         add_string ",";
         extern_type "U" "T" ppstrm ty;
         add_string ")";
         end_block())
 in
  begin_block CONSISTENT 0;
  add_string "let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}"; add_newline();
  add_string "    val U = mk_vartype"; add_newline();
  add_string "in"; add_newline();
  begin_block CONSISTENT 0;
   add_string "[";
   begin_block INCONSISTENT 0;
   pr_list pp_field (fn () => add_string ",")
                    (fn () => add_break (1,0)) fields;
   end_block (); add_string "] end";
   end_block ()
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

fun check_constrs_unique_in_theory asts = let
  fun cnames (s, Record _) = [(s,s)]
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
     val _ = check_constrs_unique_in_theory ASTs
     val asts = map stage1 ASTs
     val new_type_names = map #1 asts
     fun mk_hol_ty (dAQ ty) = ty
       | mk_hol_ty (dVartype s) = mk_vartype s
       | mk_hol_ty (dTyop{Tyop=s, Args, Thy}) =
            if Lib.mem s new_type_names
            then if null Args then tyname_as_tyvar s
                 else raise ERR "to_tyspecs"
                     ("Omit arguments to new type:"^Lib.quote s)
            else
              case Thy of
                NONE => mk_type(s, map mk_hol_ty Args)
              | SOME t => mk_thy_type {Tyop = s, Thy = t,
                                       Args = map mk_hol_ty Args}
     fun mk_hol_type pty = let
       val ty = mk_hol_ty pty
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

fun tyspecs_of q = to_tyspecs (ParseDatatype.parse q);

val new_asts_datatype = define_type o to_tyspecs;
fun new_datatype q    = new_asts_datatype (ParseDatatype.parse q);


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
   case define_size recursion db
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

(* ----------------------------------------------------------------------
    Handle big record type declarations
   ---------------------------------------------------------------------- *)

val bigrec_subdivider_string = GrammarSpecials.bigrec_subdivider_string

val big_record_size = ref 20 (* arbitrary choice *)

(* these functions generate the "magic" names used to represent big records
   as two level trees of smaller records.  There is a coupling between the
   choices made here, and the choice of names for functions in the
   RecordType code, and also in the examination made of these names in the
   term pretty-printer.  In other words, if you change something in the next
   two functions, you may need to change code in term_pp.sml and
   RecordType.sml as well.  I can't see an easy and nice way to fix this
   problem, so I'm letting it rest for the moment. *)
fun subrecord_tyname tyn n =
    (* the name of the type that inhabits the top level record *)
    tyn ^ "_" ^ bigrec_subdivider_string ^ Int.toString n
fun subrecord_fldname tyn n =
    (* the name of the field in the top level record *)
    bigrec_subdivider_string ^ "sf" ^Int.toString n
fun leaf_fldname tyn fld = fld

(* generates the sub-record number to look in, given the number of the
   original field.  Needs to know the total number of fields too. *)
fun subfld_num max = let
  fun builddexlist base m =
      if m <= 2 * !big_record_size then
        [base, base + m div 2]
      else
        base :: builddexlist (base + !big_record_size) (m - !big_record_size)
  val dexlist = builddexlist 0 max
  fun finddex n i dexlist =
      case dexlist of
        [] => i - 1
      | h::t => if n >= h then finddex n (i + 1) t
                else i - 1
in
  (fn n => finddex n 0 dexlist)
end

fun really_handle_big_record (tyname, fields) = let
  (* return a fresh list of datatype declarations that splits the list
     fields over multiple record types, that are then in turn included
     in one top-level record of the given name.  Just reformulates;
     definition work done elsewhere. *)
  open ParseDatatype
  fun split_fields fldlist = let
    val len = length fldlist
  in
    if len <= 2 * !big_record_size then let
        val (l1, l2) = split_after (len div 2) fldlist
      in
        [l1, l2]
      end
    else let
        val (pfx, sfx) = split_after (!big_record_size) fldlist
      in
        pfx :: split_fields sfx
      end
  end
  val splitflds = split_fields fields
  fun generate_newtyspec (fldlist, (n, acc)) = let
    val newtyname = subrecord_tyname tyname n
    val newfldlist =
        map (fn (s, ty) => (leaf_fldname tyname s, ty)) fldlist
  in
    (n + 1, (newtyname, Record newfldlist) :: acc)
  end
  fun gen_top_record_fld n = let
    val fldname = subrecord_fldname tyname n
    val fldtyname = subrecord_tyname tyname n
  in
    (fldname, dTyop{Tyop = fldtyname, Thy = NONE, Args = []})
  end
  val (n, subrecords) = List.foldl generate_newtyspec (0, []) splitflds
  val toprecord_spec = (tyname, Record (List.tabulate(n, gen_top_record_fld)))
in
  toprecord_spec :: subrecords
end

fun handle_big_record ast =
    (* ast is a type declaration of the form
           tyname = <foo>
       where <foo> might be a record or a standard algebraic type with
       constructors
       This code looks at ast, and does nothing unless the <foo> is a big record.
       If so, it translates
         rcdty = <| fld1 : ty1 ; fld2 : ty2 ; ... fldmax : tymax |>
       into
         rcdty = <| subrec_fld1 : subrec1_ty ; subrec_fld2 : subrec2_ty ... |> ;
         subrec1_ty = <| fld1 : ty1 ; fld2 : ty2 ; ... |> ;
         subrec2_ty = <| fld11 : ty11 ; fld12 : ty12 ; ... |> ;
         ...
       Return a pair.  The first is the new list of type declarations.
                       The second is the list of old type declarations for just
                       those record types that were too big.
       (The actual calculation of subrec_ty etc is done by really_handle_big_record.)
    *)
    case ast of
      (tyname, Constructors _) => ([ast], [])
    | (tyname, Record fields) =>
      if length fields >= !big_record_size then
        (really_handle_big_record (tyname, fields), [(tyname, fields)])
      else ([ast], [])


fun pairconcat [] = ([], [])
  | pairconcat ((x, y) :: rest) = let
      val (xs, ys) = pairconcat rest
    in
      (x @ xs, y @ ys)
    end

fun reformulate_record_types astl = pairconcat (map handle_big_record astl)

val includes_big_record = let
  open ParseDatatype
  fun is_big_record (_, Constructors _) = false
    | is_big_record (tyn, Record fldl) =
        not (is_substring bigrec_subdivider_string tyn) andalso
        length fldl >= !big_record_size
in
  fn astl => List.exists is_big_record astl
end

fun define_bigrec_functions (tyname, fldlist) = let
  (* given a type-name and the list of fields (names + pretypes),
     define the accessor and update functions for this type, knowing
     that this is a big record and that its fields have been
     distributed across various sub-record types *)
  open ParseDatatype
  val subn = subfld_num (length fldlist)
  fun define_functions n (fld, _) acc = let
    val subn = subn n
    fun defn_hd th = #1 (strip_comb (lhs (#2 (strip_forall (concl th)))))

    (* accessor *)
    val subrec_accname = tyname ^ "_" ^ subrecord_fldname tyname subn
    val subrec_accessor = prim_mk_const { Name = subrec_accname,
                                          Thy = current_theory()}
    val (toprec_ty, subrec_ty) = dom_rng (type_of subrec_accessor)
    val leaf_accname = subrecord_tyname tyname subn ^ "_" ^ fld
    val leaf_accessor = prim_mk_const {Name = leaf_accname,
                                       Thy = current_theory()}
    val field_ty = #2 (dom_rng (type_of leaf_accessor))
    val acc_const_name = tyname ^ "_" ^ fld
    val acc_const = mk_var(acc_const_name, toprec_ty --> field_ty)
    val rvar = mk_var("r", toprec_ty)
    val acc_defn = mk_eq(mk_comb(acc_const, rvar),
                     mk_comb(leaf_accessor,
                             mk_comb(subrec_accessor, rvar)))
    val acc_defn_th = new_definition(acc_const_name, acc_defn)
    val acc_defn_const = defn_hd acc_defn_th
    val _ = add_record_field (fld, acc_defn_const)
    (* fupdate function *)
    val subrec_fupdname =
        tyname ^ "_" ^ subrecord_fldname tyname subn ^ "_fupd"
    val subrec_fupd = prim_mk_const {Name = subrec_fupdname,
                                     Thy = current_theory()}
    val leaf_fupdname = leaf_accname ^ "_fupd"
    val leaf_fupd = prim_mk_const{Name = leaf_fupdname, Thy = current_theory()}
    val fupd_const_name = acc_const_name ^ "_fupd"
    val fupd_const = mk_var(fupd_const_name, (field_ty --> field_ty) -->
                                             (toprec_ty --> toprec_ty))
    val field_fvar = mk_var("f", field_ty --> field_ty)
    val fupd_defn =
        mk_eq(list_mk_comb(fupd_const, [field_fvar, rvar]),
              list_mk_comb(subrec_fupd,
                           [mk_comb(leaf_fupd, field_fvar), rvar]))
    val fupd_defn_th = new_definition(fupd_const_name, fupd_defn)
    val fupd_defn_const = defn_hd fupd_defn_th
    val _ = add_record_fupdate(fld, fupd_defn_const)
  in
    (acc_const_name, acc_defn_th) :: (fupd_const_name, fupd_defn_th) :: acc
  end
  fun foldthis (fld, (n, sthlist)) =
      (n + 1, define_functions n fld sthlist)
in
  (tyname, #2 (List.foldl foldthis (0, []) fldlist))
end

fun prove_bigrec_theorems tyinfos ss (tyname, fldlist) = let
  (* prove versions of component_equality, FORALL, EXISTS and literal_equality
     theorems that are not in terms of brss sub-records, but leaf field
     names instead. *)
  (* those theorems that need to be put into the TypeBase's tyinfo are
     returned for further processing.  The others are stored in the
     current segment, and nothing else needs to be done with them. *)
  (* final WARNING: these theorems are deliberately duplicating some of the
     theorems generated by RecordType.sml; meaning that there is a further
     ickily tight coupling between that file and this.  For example, the
     names of the theorems below need to be the same as the theorems
     generated there. *)
  open TypeBasePure
  val tyinfos = map #1 (tyinfos : (tyinfo * string) list)
  fun tyinfo_for ty = let
    val {Thy,Tyop,...} = dest_thy_type ty
  in
    List.find (fn tyi => ty_name_of tyi = (Thy,Tyop)) tyinfos
  end

  fun mk_accessor fldname = let
    val accname = tyname ^ "_" ^ fldname
  in
    prim_mk_const {Name = accname, Thy = current_theory()}
  end
  val accessors = map (mk_accessor o fst) fldlist
  val (toprec_ty, _) = dom_rng (type_of (hd accessors))
  fun mk_fupdate fldname = let
    val updname = tyname ^ "_" ^ fldname ^ "_fupd"
  in
    prim_mk_const {Name = updname, Thy = current_theory()}
  end
  val fupdates = map (mk_fupdate o fst) fldlist
  val fld_tys = map (#2 o dom_rng o type_of) accessors
  fun foldthis (ty, (n,acc)) = (n + 1, mk_var("v" ^ Int.toString n, ty) :: acc)
  val fld_vars = List.rev (#2 (foldl foldthis (1, []) fld_tys))
  fun mk_literal base values = let
    fun foldthis (upd, value, acc) = let
      val ty = type_of value
      val K = Term.inst [alpha |-> ty, beta |-> ty] combinSyntax.K_tm
    in
      list_mk_comb(upd, [mk_comb(K, value), acc])
    end
  in
    ListPair.foldr foldthis base (fupdates, values)
  end
  val arb = mk_arb toprec_ty
  val stdliteral = mk_literal arb fld_vars

  fun mk_literal' base values =
      rhs (concl (simpLib.SIMP_CONV ss [] (mk_literal base values)))
  val stdliteral' = mk_literal' arb fld_vars

  val x = mk_var("x", toprec_ty)
  val y = mk_var("y", toprec_ty)
  (* component equality theorem *)
  fun mk_rhs t = mk_eq(mk_comb(t, x), mk_comb(t, y))
  val goal = list_mk_forall([x,y],
                            mk_eq(mk_eq(x, y),
                                  list_mk_conj(map mk_rhs accessors)))
  val comp_eq_name = tyname ^ "_component_equality"
  val old_comp_eq_th = theorem comp_eq_name
  val tybrss = tyname ^ "_" ^ bigrec_subdivider_string
  val subtype_names =
      Listsort.sort String.compare
                    (filter (String.isPrefix tybrss) (map #1 (types "-")))
  val subtype_comp_eqs =
      map (theorem o (fn s => s ^ "_component_equality")) subtype_names
  open simpLib
  val component_equality =
      store_thm(comp_eq_name, goal,
                SIMP_TAC ss [] THEN
                SIMP_TAC ss (GSYM CONJ_ASSOC :: old_comp_eq_th ::
                             subtype_comp_eqs))
  (* literal nchotomy theorem *)
  val nchoto_name = tyname ^ "_literal_nchotomy"
  val old_nchoto = nchotomy_of (valOf (tyinfo_for toprec_ty))
  val base_nchoto = SPEC x old_nchoto
  val arb_nchoto = SPEC arb old_nchoto

  val subvars = let
    fun foldthis (v, (acc, n)) =
        (mk_var("x" ^ Int.toString n, type_of v) :: acc, n + 1)
    val vars0 = #1 (strip_exists (concl base_nchoto))
  in
    List.rev (#1 (List.foldl foldthis ([], 1) vars0))
  end
  val subvars' = map (mk_var o (prime ## I) o dest_var) subvars
  fun gen_cases v = let
    val (_, ty) = dest_var v
    val cases = nchotomy_of (valOf (tyinfo_for ty))
  in
    SPEC v cases
  end
  val subcases = map gen_cases (subvars @ subvars')
  val fn_updates = theorem (tyname ^ "_fn_updates")
  val sub_fn_updates =
      map (theorem o (fn s => s ^ "_fn_updates")) subtype_names

  val literal_nchotomy =
      store_thm(nchoto_name,
                mk_forall(x, list_mk_exists(fld_vars, mk_eq(x, stdliteral'))),
                GEN_TAC THEN
                EVERY_TCL (map X_CHOOSE_THEN subvars)
                          SUBST_ALL_TAC base_nchoto THEN
                EVERY_TCL (map X_CHOOSE_THEN subvars')
                          SUBST_ALL_TAC arb_nchoto THEN
                MAP_EVERY (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                          subcases THEN
                REWRITE_TAC (fn_updates :: combinTheory.o_THM ::
                             combinTheory.K_THM :: sub_fn_updates) THEN
                SIMP_TAC ss [])

  (* literal equality *)
  val liteq_name = tyname ^ "_updates_eq_literal"
  val literal_equality =
      store_thm(liteq_name,
                mk_forall(x, mk_eq(mk_literal' x fld_vars, stdliteral')),
                GEN_TAC THEN
                EVERY_TCL (map X_CHOOSE_THEN subvars)
                          SUBST_ALL_TAC base_nchoto THEN
                EVERY_TCL (map X_CHOOSE_THEN subvars')
                          SUBST_ALL_TAC arb_nchoto THEN
                MAP_EVERY (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                          subcases THEN
                SIMP_TAC ss [] THEN SIMP_TAC ss [fn_updates])
  (* literal 1-1 *)
  val fld_vars' = map (mk_var o (prime ## I) o dest_var) fld_vars
  val lit11_name = tyname ^ "_literal_11"
  val literal_11 =
      save_thm(lit11_name,
               SIMP_RULE ss [] (SPECL [stdliteral', mk_literal' arb fld_vars']
                                      component_equality))
  (* forall and exists *)
  val P = mk_var("P", toprec_ty --> bool)
  val forall =
      store_thm("FORALL_" ^ tyname,
                mk_forall(P,
                          mk_eq(mk_forall(x, mk_comb(P, x)),
                                list_mk_forall(fld_vars,
                                               mk_comb(P, stdliteral')))),
                GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
                GEN_TAC THEN
                STRUCT_CASES_TAC (SPEC x literal_nchotomy) THEN
                ASM_REWRITE_TAC [])
  val exists =
      store_thm("EXISTS_" ^ tyname,
                mk_forall(P,
                          mk_eq(mk_exists(x, mk_comb(P, x)),
                                list_mk_exists(fld_vars,
                                               mk_comb(P, stdliteral')))),
                GEN_TAC THEN EQ_TAC THENL [
                  DISCH_THEN (X_CHOOSE_THEN x ASSUME_TAC) THEN
                  EVERY_TCL (map X_CHOOSE_THEN fld_vars)
                            SUBST_ALL_TAC (SPEC x literal_nchotomy) THEN
                  MAP_EVERY EXISTS_TAC fld_vars THEN ASM_REWRITE_TAC [],
                  DISCH_THEN (EVERY_TCL (map X_CHOOSE_THEN fld_vars)
                                        ASSUME_TAC) THEN
                  EXISTS_TAC stdliteral' THEN ASM_REWRITE_TAC []
                ])
in
  (tyname, [(liteq_name, literal_equality), (lit11_name, literal_11)])
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

fun tyi_compare((ty1, _), (ty2, _)) =
   Lib.pair_compare(String.compare,String.compare)
        (TypeBasePure.ty_name_of ty1,
         TypeBasePure.ty_name_of ty2);

fun alist_comp ((s1,_,_), (s2,_,_)) = String.compare(s1,s2);

fun augment_tyinfos persistp tyis thminfo_list = let
  val tyis = Listsort.sort tyi_compare tyis
  val thminfo_list = Listsort.sort alist_comp thminfo_list
  type thmdata = (string * thm) list
  type flddata = (string * hol_type) list * thm list * thm list
  fun merge acc tyis (thmi_list : (string * thmdata * flddata) list) =
      case (tyis, thmi_list) of
        ([], _ :: _ ) => raise Fail "Datatype.sml: invariant failure 101"
      | ([],[]) => acc
      | (_, []) => tyis @ acc
      | ((tyi_s as (tyi, ty_s))::tyi_rest, (th_s, thms, flds)::thmi_rest) => let
        in
          case String.compare
                   (snd(TypeBasePure.ty_name_of tyi), th_s) of
            LESS => merge (tyi_s::acc) tyi_rest thmi_list
          | GREATER => raise Fail "Datatype.sml: invariant failure 102"
          | EQUAL => let
              val tyi' = RecordType.update_tyinfo (SOME flds) (map #2 thms) tyi
              val ty_s' = if persistp then
                            "(RecordType.update_tyinfo NONE [" ^
                            String.concat (Lib.commafy (map #1 thms)) ^
                            "] o " ^ ty_s ^ ")"
                          else ty_s
            in
              merge ((tyi', ty_s') :: acc) tyi_rest thmi_rest
            end
        end
in
  merge [] tyis thminfo_list
end


local
  fun add_record_facts (tyinfo, NONE) = (tyinfo, "")
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
  if includes_big_record astl then let
      val (newastls, bigrecords) = reformulate_record_types astl
      val (db, tyinfos) = f prevtypes db newastls
      val function_defns = map define_bigrec_functions bigrecords
      val fldinfo = getfldinfo bigrecords (* list of (string * (string*type) list)
                                             recording user's desired fields for
                                             each big record type *)
      val merged_alists = merge_alists function_defns fldinfo
      val tyinfos = augment_tyinfos true tyinfos merged_alists
      val ss = let
        open simpLib boolSimps
        fun foldthis (tyi, ss) =
            ss ++ rewrites (#rewrs (TypeBasePure.simpls_of (fst tyi)))
      in
        foldl foldthis (bool_ss ++ combinSimps.COMBIN_ss) tyinfos
      end
      val newtheorems = map (prove_bigrec_theorems tyinfos ss) bigrecords
     (* don't need to make this stuff persist because what's adjoined already
        will mention the theorems that should be in the typebase.  What we've
        done here is made the theorems look right.
      *)
      val tyinfos = augment_tyinfos false tyinfos merged_alists
    in
      (db, tyinfos)
    end
  else if is_enum_type_spec astl then (db, build_enum_tyinfos astl)
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
    fun addtyi ((tyi, _), db) = TypeBasePure.insert db tyi
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

val (type_to_string, term_to_string) = let
  val (pty, ptm) = print_from_grammars boolTheory.bool_grammars
  fun sanitise f =
      f |> Lib.with_flag (Parse.current_backend, PPBackEnd.raw_terminal)
        |> trace ("Unicode", 0)
in
  (sanitise (fn ty => ":" ^ PP.pp_to_string 70 pty ty),
   sanitise (PP.pp_to_string 70 ptm))
end;

fun adjoin [] = raise ERR "Hol_datatype" "no tyinfos"
  | adjoin (string_etc0 :: strings_etc) =
    adjoin_to_theory
    {sig_ps = NONE,
     struct_ps = SOME
     (fn ppstrm =>
      let val S = PP.add_string ppstrm
          fun NL() = PP.add_newline ppstrm
          fun do_size NONE = (S "         size = NONE,"; NL())
            | do_size (SOME (c,s)) =
               let val strc = String.concat
                     ["(", term_to_string c, ") ", type_to_string (type_of c)]
                   val line = String.concat ["SOME(Parse.Term`", strc, "`,"]
               in S ("         size="^line); NL();
                  S ("                   "^s^"),")
               end
          fun do_encode NONE = S "         encode = NONE,"
            | do_encode (SOME (c,s)) =
               let val strc = String.concat
                     ["(", term_to_string c, ") ",type_to_string (type_of c)]
                   val line = String.concat ["SOME(Parse.Term`", strc, "`,"]
               in S ("         encode="^line); NL();
                  S ("                   "^s^"),")
               end
          fun do_extras extra_string =
              (S ("      val tyinfo0 = " ^ extra_string ^ "tyinfo0"); NL())
          fun do_string_etc
             ({ax,case_def,case_cong,induction,nchotomy,
               one_one,distinct,encode,lift,size,fields,accessors,updates,
               recognizers,destructors},
              extra_simpls_string) =
            (S "    let";                                               NL();
             S "      open TypeBasePure";                               NL();
             S "      val tyinfo0 = mk_datatype_info";                  NL();
             S("        {ax="^ax^",");                                  NL();
             S("         case_def="^case_def^",");                      NL();
             S("         case_cong="^case_cong^",");                    NL();
             S("         induction="^induction^",");                    NL();
             S("         nchotomy="^nchotomy^",");                      NL();
             do_size size;                                              NL();
             do_encode encode;                                          NL();
             S("         lift=NONE,");                                  NL();
             S("         one_one="^one_one^",");                        NL();
             S("         distinct="^distinct^",");                      NL();
             S("         fields="^fields^",");                          NL();
             S("         accessors="^accessors^",");                    NL();
             S("         updates="^updates^",");                        NL();
             S("         recognizers="^recognizers^",");                NL();
             S("         destructors="^destructors^"}");                NL();
             do_extras extra_simpls_string;
             S "      val () = computeLib.write_datatype_info tyinfo0"; NL();
             S "    in";                                                NL();
             S "      tyinfo0";                                         NL();
             S "    end")
      in
        S "val _ =";                                                    NL();
        S "  TypeBase.write [";                                         NL();
        do_string_etc string_etc0;
        app (fn se => (S ","; NL(); do_string_etc se)) strings_etc;     NL();
        S "  ];";                                                       NL()
      end)};

fun string_pair(s1,s2) = "("^Lib.quote s1^","^Lib.quote s2^")";

fun write_tyinfo tyinfo =
 let open TypeBasePure
     val tname = snd(ty_name_of tyinfo)
     fun name s = tname ^ s
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
          | COPY (sp,th) => "COPY ("^string_pair sp^","^snd(sp)^"_Axiom)"
        end
     val induction_name =
        let val indname = name"_induction"
        in
        case induction_of0 tyinfo
         of ORIG th => (save_thm (indname, th); "ORIG "^indname)
          | COPY (sp,th) => "COPY ("^string_pair sp^","^snd(sp)^"_induction)"
        end
     val size_info =
       let val sd_name = name"_size_def"
       in
       case size_of0 tyinfo
        of NONE => NONE
         | SOME (tm, ORIG def) => SOME (tm, "ORIG "^sd_name)
         | SOME (tm, COPY(sp,def))
            => SOME (tm, "COPY ("^string_pair sp^","^snd(sp)^"_size_def)")
       end
     val encode_info =
       let val sd_name = "encode_"^name"_def"
       in
       case encode_of0 tyinfo
        of NONE => NONE
         | SOME (tm, ORIG def) => SOME (tm, "ORIG "^sd_name)
         | SOME (tm, COPY(sp,def))
            => SOME (tm, "COPY ("^string_pair sp^",encode_"^snd(sp)^"_def)")
       end
     val lift_info = NONE
     val accessors_list =
       let val acc_name = name"_accessors"
       in case accessors_of tyinfo
           of [] => "[]"
            | other => "Drule.CONJUNCTS "^acc_name
       end
     val updates_list =
       let val upd_name = name"_fn_updates"
       in case updates_of tyinfo
           of [] => "[]"
            | other => "Drule.CONJUNCTS "^upd_name
       end
     val destructors_list =
       let val dest_name = name"_destructors"
       in case destructors_of tyinfo
           of [] => "[]"
            | other => "Drule.CONJUNCTS "^dest_name
       end
     val recognizers_list =
       let val rec_name = name"_recognizers"
       in case recognizers_of tyinfo
           of [] => "[]"
            | other => "Drule.CONJUNCTS "^rec_name
       end

 in
   {ax        = axiom_name,
    induction = induction_name,
    case_def  = case_constant_defn_name {type_name = tname},
    case_cong = case_cong_name,
    nchotomy  = nchotomy_name,
    size      = size_info,
    encode    = encode_info,
    lift      = lift_info,
    one_one   = one_one_name,
    fields    = Portable.pp_to_string 60 pp_fields (fields_of tyinfo),
    accessors = accessors_list,
    updates   = updates_list,
    recognizers = recognizers_list,
    destructors = destructors_list,
    distinct  = distinct_name}
 end;

val write_tyinfos = adjoin o map (write_tyinfo ## I);

fun persistent_tyinfo tyinfos_etc =
  let val (tyinfos, etc) = unzip tyinfos_etc
      val tyinfos = TypeBase.write tyinfos
      val () = app computeLib.write_datatype_info tyinfos
  in
    write_tyinfos tyinfos_etc
  end;

(*---------------------------------------------------------------------------*)
(* Construct trivial theorem from which structure of original datatype can   *)
(* be recovered.                                                             *)
(*---------------------------------------------------------------------------*)

fun mk_datatype_presentation thy tyspecl =
  let open ParseDatatype
      fun mkc (n,_) = prim_mk_const{Name=n,Thy=thy}
      fun type_dec (tyname,Constructors dforms) =
          let val constrs = map mkc dforms
              val tyn_var = mk_var(tyname,list_mk_fun(map type_of constrs,bool))
          in
            list_mk_comb(tyn_var,constrs)
          end
        | type_dec (tyname,Record fields) = let
            fun fieldvar (n, _) = let
              val c = prim_mk_const{Name = tyname ^ "_" ^ n, Thy = thy}
              val (_, ty) = dom_rng (type_of c)
            in
              mk_var(n, ty)
            end
            val fvars = map fieldvar fields
            val tyn_var = mk_var(tyname,ind)
            val record_var = mk_var("record",
                                    list_mk_fun(ind::map type_of fvars,bool))
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
  val (_,tyinfos_etc) = primHol_datatype (TypeBase.theTypeBase()) astl
  val _ = Theory.scrub()
  val _ = datatype_thm (mk_datatype_presentation (current_theory()) astl)
  val tynames = map (TypeBasePure.ty_name_of o #1) tyinfos_etc
  val tynames = filter (not o is_substring bigrec_subdivider_string o snd) tynames
  val tynames = map (Lib.quote o snd) tynames
  val message = "Defined type"^(if length tynames > 1 then "s" else "")^
                ": "^String.concat (Lib.commafy tynames)
 in
  persistent_tyinfo tyinfos_etc;
  HOL_MESG message
 end handle ? as HOL_ERR _ => Raise (wrap_exn "Datatype" "Hol_datatype" ?);

val Hol_datatype = astHol_datatype o ParseDatatype.parse;

val _ = Parse.temp_set_grammars ambient_grammars

end
