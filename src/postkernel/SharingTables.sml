structure SharingTables :> SharingTables =
struct

open Term Type

structure Map = Binarymap

(* ----------------------------------------------------------------------
    string sharing table
   ---------------------------------------------------------------------- *)

type stringtable =
     {size : int, map : (string,int) Map.dict, list : string list}

val CB = PP.block PP.CONSISTENT 0
val out = PP.add_string
val NL = PP.NL


val empty_strtable : stringtable =
    {size = 0, map = Map.mkDict String.compare, list = []}

fun theoryout_strtable (strtable : stringtable) =
    let
      fun printstr s = out (Lib.mlquote s)
    in
      CB [
        out "[",
        PP.block PP.INCONSISTENT 1 (
          PP.pr_list printstr [PP.add_break(1,0)] (List.rev (#list strtable))
        ),
        out "]"
      ]
    end

fun new_string s (strtable as {size,list,map}:stringtable) =
    case Map.peek(map, s) of
        SOME i => (i, strtable)
      | NONE => (size, {size = size + 1,
                        list = s :: list,
                        map = Map.insert(map,s,size)})

(* ----------------------------------------------------------------------
    IDs (also known as Theory-X pairs, where X is a Name for a constant,
    or Tyops for types)
   ---------------------------------------------------------------------- *)

type id = {Thy : string, Other : string}
type idtable = {idsize : int,
                idmap : (id, int) Map.dict,
                idlist : (int * int) list}

fun make_shared_id (id as {Thy,Other} : id) (strtable, idtable) =
    case Map.peek(#idmap idtable, id) of
      SOME i => (i, strtable, idtable)
    | NONE => let
        val {idsize, idmap, idlist} = idtable
        val (thyi, strtable) = new_string Thy strtable
        val (otheri, strtable) = new_string Other strtable
      in
        (idsize, strtable,
         {idsize = idsize + 1, idmap = Map.insert(idmap, id, idsize),
          idlist = (thyi,otheri) :: idlist})
      end
fun id_compare ({Other = id1, Thy = thy1}, {Other = id2, Thy = thy2}) =
    case String.compare(id1, id2) of
      EQUAL => String.compare(thy1, thy2)
    | x => x

val empty_idtable : idtable = {idsize = 0,
                               idmap = Map.mkDict id_compare,
                               idlist = []}


fun theoryout_idtable (idtable : idtable) = let
  val idlist = List.rev (#idlist idtable)
  fun print_id (Thyi, Otheri) =
      out (Int.toString Thyi^ " " ^ Int.toString Otheri)
  val print_ids = PP.pr_list print_id [PP.add_string ",", PP.add_break(1,0)]
in
  CB [out "[", PP.block PP.INCONSISTENT 1 (print_ids idlist), out "]"]
end

fun build_id_vector strings intpairs =
    Vector.fromList
      (map (fn (thyi,otheri) => {Thy = Vector.sub(strings,thyi),
                                 Other = Vector.sub(strings,otheri)})
           intpairs)


(* ----------------------------------------------------------------------
    Types
   ---------------------------------------------------------------------- *)

datatype shared_type = TYV of string
                     | TYOP of int list

type typetable = {tysize : int,
                  tymap : (hol_type, int)Map.dict,
                  tylist : shared_type list}

fun make_shared_type ty strtable idtable table =
    case Map.peek(#tymap table, ty) of
      SOME i => (i, strtable, idtable, table)
    | NONE => let
      in
        if is_vartype ty then let
            val {tysize, tymap, tylist} = table
          in
            (tysize, strtable, idtable,
             {tysize = tysize + 1,
              tymap = Map.insert(tymap, ty, tysize),
              tylist = TYV (dest_vartype ty) :: tylist})
          end
        else let
            val {Thy, Tyop, Args} = dest_thy_type ty
            val (id, strtable0, idtable0) =
                make_shared_id {Thy = Thy, Other = Tyop} (strtable, idtable)
            fun foldthis (tyarg, (results, strtable, idtable, table)) = let
              val (result, strtable', idtable', table') =
                  make_shared_type tyarg strtable idtable table
            in
              (result::results, strtable', idtable', table')
            end
            val (newargs, strtable', idtable', table') =
                List.foldr foldthis ([], strtable0, idtable0, table) Args
            val {tysize, tymap, tylist} = table'
          in
            (tysize, strtable', idtable',
             {tysize = tysize + 1,
              tymap = Map.insert(tymap, ty, tysize),
              tylist = TYOP (id :: newargs) :: tylist})
          end
      end

val empty_tytable : typetable =
    {tysize = 0, tymap = Map.mkDict Type.compare, tylist = [] }

fun build_type_vector idv shtylist = let
  fun build1 (shty, (n, tymap)) =
      case shty of
        TYV s => (n + 1, Map.insert(tymap, n, Type.mk_vartype s))
      | TYOP idargs => let
          val (id, Args) = valOf (List.getItem idargs)
          val args = map (fn i => Map.find(tymap, i)) Args
          val {Thy,Other} = Vector.sub(idv, id)
        in
          (n + 1,
           Map.insert(tymap, n,
                            Type.mk_thy_type {Thy = Thy, Tyop = Other,
                                              Args = args}))
        end
  val (_, tymap) =
      List.foldl build1 (0, Map.mkDict Int.compare) shtylist
in
  Vector.fromList (map #2 (Map.listItems tymap))
end

fun output_typetable {idtable_nm,tytable_nm} (tytable : typetable) = let
  fun output_shtype shty =
      case shty of
        TYV s => out ("TYV "^Lib.mlquote s)
      | TYOP args =>
        out ("TYOP ["^
             String.concat (Lib.commafy (map Int.toString args))^ "]")
  val output_shtypes = PP.pr_list output_shtype [out ",", PP.add_break (1,0)]
in
  CB [
    out "local open SharingTables", NL, out "in", NL,
    out ("val "^tytable_nm^" = build_type_vector "^idtable_nm), NL,
    out ("["),
    PP.block PP.INCONSISTENT 0 (output_shtypes (List.rev (#tylist tytable))),
    out "]", NL, out "end", NL
  ]
end

fun theoryout_typetable (tytable : typetable) = let
  fun output_shtype shty =
      case shty of
        TYV s => out ("TYV "^ Lib.mlquote s)
      | TYOP args =>
        out ("TYOP "^ String.concatWith " " (map Int.toString args))
  val output_shtypes = PP.pr_list output_shtype [out ",", PP.add_break (1,0)]
in
  CB [
    out "[",
    PP.block PP.INCONSISTENT 1 (output_shtypes (List.rev (#tylist tytable))),
    out "]"
  ]
end


(* ----------------------------------------------------------------------
    Terms
   ---------------------------------------------------------------------- *)

datatype shared_term = TMV of string * int
                     | TMC of int * int
                     | TMAp of int * int
                     | TMAbs of int * int

type termtable = {termsize : int,
                  termmap : (term, int)Map.dict,
                  termlist : shared_term list}

val empty_termtable : termtable =
    {termsize = 0, termmap = Map.mkDict Term.compare, termlist = [] }

fun make_shared_term tm (tables as (strtable,idtable,tytable,tmtable)) =
    case Map.peek(#termmap tmtable, tm) of
      SOME i => (i, tables)
    | NONE => let
      in
        if is_var tm then let
            val (s, ty) = dest_var tm
            val (ty_i, strtable, idtable, tytable) =
                make_shared_type ty strtable idtable tytable
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (strtable, idtable, tytable,
              {termsize = termsize + 1,
               termmap = Map.insert(termmap, tm, termsize),
               termlist = TMV (s, ty_i) :: termlist}))
          end
        else if is_const tm then let
            val {Thy,Name,Ty} = dest_thy_const tm
            val (id_i, strtable, idtable) =
                make_shared_id {Thy = Thy, Other = Name} (strtable, idtable)
            val (ty_i, strtable, idtable, tytable) =
                make_shared_type Ty strtable idtable tytable
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (strtable, idtable, tytable,
              {termsize = termsize + 1,
               termmap = Map.insert(termmap, tm, termsize),
               termlist = TMC (id_i, ty_i) :: termlist}))
          end
        else if is_comb tm then let
            val (f, x) = dest_comb tm
            val (f_i, tables) = make_shared_term f tables
            val (x_i, tables) = make_shared_term x tables
            val (strtable, idtable, tytable, tmtable) = tables
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (strtable, idtable, tytable,
              {termsize = termsize + 1,
               termmap = Map.insert(termmap, tm, termsize),
               termlist = TMAp(f_i, x_i) :: termlist}))
          end
        else  (* must be an abstraction *) let
            val (v, body) = dest_abs tm
            val (v_i, tables) = make_shared_term v tables
            val (body_i, tables) = make_shared_term body tables
            val (strtable, idtable, tytable, tmtable) = tables
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (strtable, idtable, tytable,
              {termsize = termsize + 1,
               termmap = Map.insert(termmap, tm, termsize),
               termlist = TMAbs(v_i, body_i) :: termlist}))
          end
      end

fun build_term_vector idv tyv shtmlist = let
  fun build1 (shtm, (n, tmmap)) =
      case shtm of
        TMV (s, tyn) => (n + 1,
                         Map.insert(tmmap, n, mk_var(s, Vector.sub(tyv, tyn))))
      | TMC (idn, tyn) => let
          val {Thy, Other} = Vector.sub(idv, idn)
          val ty = Vector.sub(tyv, tyn)
        in
          (n + 1, Map.insert(tmmap, n, mk_thy_const {Name = Other, Thy = Thy,
                                                     Ty = ty}))
        end
      | TMAp (f_n, xn) =>
        (n + 1, Map.insert(tmmap, n, mk_comb(Map.find(tmmap, f_n),
                                             Map.find(tmmap, xn))))
      | TMAbs (vn, bodyn) =>
        (n + 1, Map.insert(tmmap, n, mk_abs(Map.find(tmmap, vn),
                                            Map.find(tmmap, bodyn))))
  val (_, tmmap) = List.foldl build1 (0, Map.mkDict Int.compare) shtmlist
in
  Vector.fromList (map #2 (Map.listItems tmmap))
end

fun output_termtable names (tmtable: termtable) = let
  val {idtable_nm,tytable_nm,termtable_nm} = names
  fun ipair_string (x,y) = "("^Int.toString x^", "^Int.toString y^")"
  fun output_shtm shtm =
    case shtm of
        TMV (s, tyn) => out ("TMV(" ^ Lib.mlquote s ^", "^Int.toString tyn^")")
      | TMC p => out ("TMC"^ipair_string p)
      | TMAp p => out ("TMAp"^ipair_string p)
      | TMAbs p => out ("TMAbs"^ipair_string p)
  val output_shtms = PP.pr_list output_shtm [out ",", PP.add_break(1,0)]
in
  CB [
    out ("local open SharingTables"), NL,
    out ("in"), NL,
    out ("val "^termtable_nm^" = build_term_vector "^idtable_nm^" "^
         tytable_nm), NL,
    out ("["),
    PP.block PP.INCONSISTENT 0 (output_shtms (List.rev (#termlist tmtable))),
    out ("]"), NL,
    out "end", NL
  ]
end;

fun theoryout_termtable (tmtable: termtable) =
  let
    fun ipair_string (x,y) = Int.toString x^" "^Int.toString y
    fun output_shtm shtm =
      case shtm of
          TMV (s, tyn) =>
            out ("TMV " ^ Lib.mlquote s ^" "^Int.toString tyn)
        | TMC p => out ("TMC "^ipair_string p)
        | TMAp p => out ("TMAp "^ipair_string p)
        | TMAbs p => out ("TMAbs "^ipair_string p)
    val output_shtms = PP.pr_list output_shtm [out ",", PP.add_break(1,0)]
  in
    CB [
      out ("["),
      PP.block PP.INCONSISTENT 1 (output_shtms (List.rev (#termlist tmtable))),
      out ("]")
    ]
  end

end; (* struct *)
