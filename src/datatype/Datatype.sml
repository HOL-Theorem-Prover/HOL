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

(*
*)
structure Datatype :> Datatype =
struct

open HolKernel Parse boolLib Prim_rec ParseDatatype;

local open ind_typeTheory in end;

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
 * maps a type variable (say 'a) to a term variable "f" of type 'a -> num.   *
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

(* Returns false if there is more than one type called for, because an
   earlier sorting process will ensure that enumerated types are
   presented singly. *)

fun is_enum_type_spec astl =
    case astl of
      [(ty,Constructors constrs)] => List.all (null o #2) constrs
    (* recall that constrs is a list of constr-name - type arguments pairs *)
    | _ => false


(* ----------------------------------------------------------------------
    Build a tyinfo list for an enumerated type.
   ---------------------------------------------------------------------- *)

fun build_enum_tyinfo (tyname, ast) = let
  open EnumType
in
  case ast of
    Constructors clist => let
      val constructors = map #1 clist
    in
      case duplicate_names constructors of
        NONE => (enum_type_to_tyinfo (tyname, constructors))
      | SOME s => raise ERR "build_enum" ("Duplicate constructor name: "^s)
    end
  | otherwise => raise ERR "build_enum_tyinfo" "Should never happen"
end

fun build_enum_tyinfos astl = map build_enum_tyinfo astl


(*---------------------------------------------------------------------------
    Returns a list of tyinfo thingies
 ---------------------------------------------------------------------------*)

local
  fun insert_size {def, const_tyopl} tyinfol =
    (case tyinfol of [] => raise ERR "build_tyinfos" "empty tyinfo list"
     | tyinfo::rst =>
       let
         val first_tyname = TypeBasePure.ty_name_of tyinfo
         fun insert_size info size_eqs =
           let
             val tyname = TypeBasePure.ty_name_of info
           in
             case assoc2 tyname const_tyopl of SOME(c,tyop)
               => TypeBasePure.put_size(c,size_eqs) info
             | NONE => (HOL_MESG
                        ("Can't find size constant for"^tyname);
                        raise ERR "build_tyinfos" "")
           end
       in
         insert_size tyinfo (TypeBasePure.ORIG def) ::
         map (C insert_size (TypeBasePure.COPY (first_tyname,def))) rst
       end
       handle HOL_ERR _ => tyinfol);
in
  fun build_tyinfos db {induction,recursion} =
    let
      val case_defs = Prim_rec.define_case_constant recursion
      val tyinfol = TypeBasePure.gen_tyinfo
        {ax=recursion, ind=induction, case_defs=case_defs}
    in
      case define_size recursion db
        of NONE => (HOL_MESG "Couldn't define size function"; tyinfol)
      | SOME s => insert_size s tyinfol
    end;
end

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

val big_record_size = 8 (* arbitrary choice *)

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
      if m <= 2 * big_record_size then
        [base, base + m div 2]
      else
        base :: builddexlist (base + big_record_size) (m - big_record_size)
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
    if len <= 2 * big_record_size then let
        val (l1, l2) = split_after (len div 2) fldlist
      in
        [l1, l2]
      end
    else let
        val (pfx, sfx) = split_after big_record_size fldlist
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
    case ast of
      (tyname, Constructors _) => ([ast], [])
    | (tyname, Record fields) =>
      if length fields >= big_record_size then
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
        length fldl >= big_record_size
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
    (* update function *)
    val subrec_fupdname =
        tyname ^ "_" ^ subrecord_fldname tyname subn ^ "_fupd"
    val subrec_fupd = prim_mk_const { Name = subrec_fupdname,
                                      Thy = current_theory()}
    val leaf_updname = leaf_accname ^ "_update"
    val leaf_upd = prim_mk_const {Name = leaf_updname, Thy = current_theory()}
    val upd_const_name = acc_const_name ^ "_update"
    val upd_const =
        mk_var(upd_const_name, field_ty --> (toprec_ty --> toprec_ty))
    val field_valvar = mk_var("x", field_ty)
    val upd_defn =
        mk_eq(list_mk_comb(upd_const, [field_valvar, rvar]),
              list_mk_comb(subrec_fupd,
                           [mk_comb(leaf_upd, field_valvar), rvar]))
    val upd_defn_th = new_definition(upd_const_name, upd_defn)
    val upd_defn_const = defn_hd upd_defn_th
    val _ = add_record_update(fld, upd_defn_const)
    (* fupdate function *)
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
    (acc_const_name, acc_defn_th) :: (upd_const_name, upd_defn_th) ::
    (fupd_const_name, fupd_defn_th) :: acc
  end
  fun foldthis (fld, (n, sthlist)) =
      (n + 1, define_functions n fld sthlist)
in
  (tyname, #2 (List.foldl foldthis (0, []) fldlist))
end

fun prove_bigrec_theorems ss (tyname, fldlist) = let
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
  fun mk_accessor fldname = let
    val accname = tyname ^ "_" ^ fldname
  in
    prim_mk_const {Name = accname, Thy = current_theory()}
  end
  val accessors = map (mk_accessor o fst) fldlist
  val (toprec_ty, _) = dom_rng (type_of (hd accessors))
  fun mk_update fldname = let
    val updname = tyname ^ "_" ^ fldname ^ "_update"
  in
    prim_mk_const {Name = updname, Thy = current_theory()}
  end
  val updates = map (mk_update o fst) fldlist
  val fld_tys = map (#1 o dom_rng o type_of) updates
  fun foldthis (ty, (n,acc)) = (n + 1, mk_var("v" ^ Int.toString n, ty) :: acc)
  val fld_vars = List.rev (#2 (foldl foldthis (1, []) fld_tys))
  fun mk_literal base values = let
    fun foldthis upd value acc = list_mk_comb(upd, [value, acc])
  in
    itlist2 foldthis updates values base
  end
  val arb = mk_arb toprec_ty
  val stdliteral = mk_literal arb fld_vars

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
  val goal =
      mk_forall(x,
                list_mk_exists(fld_vars, mk_eq(x, stdliteral)))
  val nchoto_name = tyname ^ "_literal_nchotomy"
  val literal_nchotomy =
      store_thm(nchoto_name, goal,
                GEN_TAC THEN
                MAP_EVERY (EXISTS_TAC o (fn t => mk_comb(t, x))) accessors THEN
                SIMP_TAC ss [] THEN SIMP_TAC ss [component_equality])

  (* literal equality *)
  val liteq_name = tyname ^ "_updates_eq_literal"
  val literal_equality0 =
      prove(mk_forall(x, mk_eq(mk_literal x fld_vars, stdliteral)),
            SIMP_TAC ss [] THEN SIMP_TAC ss [component_equality])
  val literal_equality =
      save_thm(liteq_name, SIMP_RULE ss [] literal_equality0)
  (* literal 1-1 *)
  val fld_vars' = map (mk_var o (prime ## I) o dest_var) fld_vars
  val lit11_name = tyname ^ "_literal_11"
  val literal_11 =
      save_thm(lit11_name,
               SIMP_RULE ss [] (SPECL [stdliteral, mk_literal arb fld_vars']
                                      component_equality))
  (* forall and exists *)
  val P = mk_var("P", toprec_ty --> bool)
  val forall =
      store_thm("FORALL_" ^ tyname,
                mk_forall(P,
                          mk_eq(mk_forall(x, mk_comb(P, x)),
                                list_mk_forall(fld_vars,
                                               mk_comb(P, stdliteral)))),
                GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
                GEN_TAC THEN
                STRUCT_CASES_TAC (SPEC x literal_nchotomy) THEN
                ASM_REWRITE_TAC [])
  val exists =
      store_thm("EXISTS_" ^ tyname,
                mk_forall(P,
                          mk_eq(mk_exists(x, mk_comb(P, x)),
                                list_mk_exists(fld_vars,
                                               mk_comb(P, stdliteral)))),
                GEN_TAC THEN EQ_TAC THENL [
                  DISCH_THEN (X_CHOOSE_THEN x ASSUME_TAC) THEN
                  EVERY_TCL (map X_CHOOSE_THEN fld_vars)
                            SUBST_ALL_TAC (SPEC x literal_nchotomy) THEN
                  MAP_EVERY EXISTS_TAC fld_vars THEN ASM_REWRITE_TAC [],
                  DISCH_THEN (EVERY_TCL (map X_CHOOSE_THEN fld_vars)
                                        ASSUME_TAC) THEN
                  EXISTS_TAC stdliteral THEN ASM_REWRITE_TAC []
                ])
in
  (tyname, [(liteq_name, literal_equality), (lit11_name, literal_11)])
end

(* ----------------------------------------------------------------------
    do the hard work of type definition
   ---------------------------------------------------------------------- *)

fun augment_tyinfos persistp tyis thminfo_list = let
  (* [tyis] is a list of tyinfos coupled with strings representing how to
     recreate them (strings which when eval-ed will be a function of type
     tyinfo -> tyinfo; these functions will be applied to the basic tyinfo
     created for the record type).

     [thminfo_list] is of type (string * (string * thm) list) list,
     basically an association list from type names to extra stuff.
     The theorems need to be added to the corresponding tyinfos, and
     they are accompanied by the names under which they have been
     stored in the theory segment.

     [persistp] is true iff we need to adjoin stuff to make the change
     persistent. *)
  fun tyi_compare((ty1, _), (ty2, _)) =
      String.compare(TypeBasePure.ty_name_of ty1,
                     TypeBasePure.ty_name_of ty2)
  val tyis = Listsort.sort tyi_compare tyis
  val thminfo_list = Listsort.sort
                       (fn ((s1,_), (s2,_)) => String.compare(s1, s2))
                       thminfo_list
  fun merge acc tyis (thmi_list : (string * (string * thm) list) list)  =
      case (tyis, thmi_list) of
        ([], _ :: _ ) => raise Fail "Datatype.sml: invariant failure 101"
      | ([], []) => acc
      | (_, []) => tyis @ acc
      | ((tyi_s as (tyi, ty_s))::tyi_rest, (th_s, thms)::thmi_rest) => let
        in
          case String.compare (TypeBasePure.ty_name_of tyi, th_s) of
            LESS => merge (tyi_s::acc) tyi_rest thmi_list
          | GREATER => raise Fail "Datatype.sml: invariant failure 102"
          | EQUAL => let
              val tyi' = RecordType.update_tyinfo (map #2 thms) tyi
              val ty_s' = if persistp then
                            "(RecordType.update_tyinfo [" ^
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
in
fun prim_define_type_from_astl prevtypes f db astl0 = let
  (* precondition: astl has been sorted, so that, for example,  those
     ast elements not referring to any others will be present only as
     singleton lists *)
  val astl = insert_tyarguments prevtypes astl0
in
  if includes_big_record astl then let
      val (newastls, bigrecords) = reformulate_record_types astl
      val (db, tyinfos) = f prevtypes db newastls
      val function_defns = map define_bigrec_functions bigrecords
      val tyinfos = augment_tyinfos true tyinfos function_defns
      val ss = let
        open simpLib boolSimps
        fun foldthis (tyi, ss) =
            ss ++ rewrites (#rewrs (TypeBasePure.simpls_of (fst tyi)))
      in
        foldl foldthis (bool_ss ++ combinSimps.COMBIN_ss) tyinfos
      end
      val newtheorems = map (prove_bigrec_theorems ss) bigrecords
     (* don't need to make this stuff persist because what's adjoined already
        will mention the theorems that should be in the typebase.  What we've
        done here is made the theorems look right. *)
      val tyinfos = augment_tyinfos false tyinfos newtheorems
    in
      (db, tyinfos)
    end
  else if is_enum_type_spec astl then
    (db, build_enum_tyinfos astl)
  else (db,
        map add_record_facts
            (zip (build_tyinfos db (new_asts_datatype astl))
                 (map field_names_of astl)))
end
end (* local *)

fun find_vartypes (pty, acc) = let
  open ParseDatatype
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


val empty_stringset = HOLset.empty String.compare
(* prevtypes below is an association list mapping the names of types
   previously defined in this "session" to the list of type variables that
   occurred on the RHS of the type definitions *)
fun define_type_from_astl prevtypes db astl = let
  val sorted_astll = sort_astl astl
  val f = define_type_from_astl
  fun handle_astl (astl, (prevtypes, db, tyinfo_acc)) = let
    val (db, new_tyinfos) = prim_define_type_from_astl prevtypes f db astl
    fun addtyi ((tyi, _), db) = TypeBasePure.add db tyi
    val alltyvars =
        List.foldl (fn ((_, dtf), acc) => dtForm_vartypes(dtf, acc))
                   empty_stringset
                   astl
  in
    (prevtypes @ map (fn (s, dtf) => (s, alltyvars)) astl,
     List.foldl addtyi db new_tyinfos,
     tyinfo_acc @ new_tyinfos)
  end
  val (_, db, tyinfos) =
      List.foldl handle_astl (prevtypes, db, []) sorted_astll
in
  (db, tyinfos)
end

fun primHol_datatype db q =
 let val astl = ParseDatatype.parse q handle (e as HOL_ERR _) => Raise e
 in
   #2 (define_type_from_astl [] db astl)
 end



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
        7. ty_to_bool_def   (* boolification of type defn *)
        8. one_one          (* one-one-ness of the constructors *)
        9. distinct         (* distinctness of the constructors *)

   We also adjoin some ML to the current theory so that if the theory
   gets exported and loaded in a later session, these "datatype"
   theorems are loaded automatically into theTypeBase.

 ---------------------------------------------------------------------------*)

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
                     ["(", term_to_string c, ") ",type_to_string (type_of c)]
                   val line = String.concat ["SOME(Parse.Term`", strc, "`,"]
               in S ("         size="^line); NL();
                  S ("                   "^s^"),")
               end
          fun do_boolify NONE = S "         boolify = NONE,"
            | do_boolify (SOME (c,s)) =
               let val strc = String.concat
                     ["(", term_to_string c, ") ",type_to_string (type_of c)]
                   val line = String.concat ["SOME(Parse.Term`", strc, "`,"]
               in S ("         boolify="^line); NL();
                  S ("                   "^s^"),")
               end
          fun do_extras extra_string =
              (S ("      val tyinfo0 = " ^ extra_string ^ "tyinfo0"); NL())
          fun do_string_etc ({ax,case_def,case_cong,induction,nchotomy,
            one_one,distinct,boolify,size}, extra_simpls_string) =
            (S "    let";                                               NL();
             S "      open TypeBasePure";                               NL();
             S "      val tyinfo0 = mk_tyinfo";                         NL();
             S("        {ax="^ax^",");                                  NL();
             S("         case_def="^case_def^",");                      NL();
             S("         case_cong="^case_cong^",");                    NL();
             S("         induction="^induction^",");                    NL();
             S("         nchotomy="^nchotomy^",");                      NL();
             do_size size;                                              NL();
             do_boolify boolify;                                        NL();
             S("         one_one="^one_one^",");                        NL();
             S("         distinct="^distinct^"}");                      NL();
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

fun write_tyinfo tyinfo =
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
   {ax        = axiom_name,
    induction = induction_name,
    case_def  = name"_case_def",
    case_cong = case_cong_name,
    nchotomy  = nchotomy_name,
    size      = size_info,
    boolify   = boolify_info,
    one_one   = one_one_name,
    distinct  = distinct_name}
 end;

val write_tyinfos = adjoin o map (write_tyinfo ## I);

fun persistent_tyinfo tyinfos_etc =
  let
    val (tyinfos, etc) = unzip tyinfos_etc
    val tyinfos = TypeBase.write tyinfos
    val () = app computeLib.write_datatype_info tyinfos
  in
    write_tyinfos (zip tyinfos etc)
  end;

fun Hol_datatype q = let
  val tyinfos_etc = primHol_datatype (TypeBase.theTypeBase()) q
  val tynames = map (TypeBasePure.ty_name_of o #1) tyinfos_etc
  val tynames = filter (not o is_substring bigrec_subdivider_string) tynames
  val tynames = map Lib.quote tynames
  val message = "Defined "^(if length tynames > 1 then "types" else "type")^
                ": "^String.concat (Lib.commafy tynames)
in
  persistent_tyinfo tyinfos_etc;
  HOL_MESG message
end handle ? as HOL_ERR _ => Raise (wrap_exn "Datatype" "Hol_datatype" ?);



end (* struct *)
