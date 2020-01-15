structure SharingTables :> SharingTables =
struct

open Term Type

structure Map = Binarymap
exception SharingTables of string

type 'a sexppr = 'a -> HOLsexp.t

(* ----------------------------------------------------------------------
    string sharing table
   ---------------------------------------------------------------------- *)

type stringtable =
     {size : int, map : (string,int) Map.dict, list : string list}
type id = {Thy : string, Other : string}
type idtable = {idsize : int,
                idmap : (id, int) Map.dict,
                idlist : (int * int) list}

val empty_strtable : stringtable =
    {size = 0, map = Map.mkDict String.compare, list = []}

local
  open HOLsexp
in
fun enc_strtable (strtable : stringtable) =
    tagged_encode "string-table" (list_encode String)
                  (List.rev (#list strtable))
val dec_strings =
    Option.map Vector.fromList o
    tagged_decode "string-table" (list_decode string_decode)

fun enc_idtable (idtable : idtable) =
    tagged_encode "id-table" (list_encode (pair_encode(Integer,Integer)))
                  (List.rev (#idlist idtable))
fun dec_ids strv =
    Option.map (Vector.fromList o
                map (fn (i,j) => {Thy = Vector.sub(strv,i),
                                  Other = Vector.sub(strv,j)})) o
    tagged_decode "id-table" (list_decode (pair_decode(int_decode,int_decode)))

end (* local *)


fun theoryout_strtable (strtable : stringtable) =
    HOLsexp.printer (enc_strtable strtable)

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


fun theoryout_idtable (idtable : idtable) =
    HOLsexp.printer (enc_idtable idtable)

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

local
  open HOLsexp
in
fun shared_type_encode (TYV s) = String s
  | shared_type_encode (TYOP is) = List(map Integer is)

fun shared_type_decode s =
    case string_decode s of
        SOME str => SOME (TYV str)
      | _ => Option.map TYOP (list_decode int_decode s)

val enc_tytable : typetable encoder =
    tagged_encode "type-table" (list_encode shared_type_encode) o List.rev o
    #tylist

end (* local *)

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
          fun mapthis i =
              Map.find(tymap, i)
              handle Map.NotFound =>
                     raise SharingTables ("build_type_vector: (" ^
                                          String.concatWith " "
                                                (map Int.toString Args) ^
                                          "), " ^ Int.toString i ^
                                          " not found")
          val args = map mapthis Args
          val {Thy,Other} = Vector.sub(idv, id)
        in
          (n + 1,
           Map.insert(tymap, n,
                      Type.mk_thy_type {Thy = Thy, Tyop = Other, Args = args}))
        end
  val (_, tymap) =
      List.foldl build1 (0, Map.mkDict Int.compare) shtylist
in
  Vector.fromList (map #2 (Map.listItems tymap))
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

local
  open HOLsexp
in
fun shared_term_encode stm =
    case stm of
        TMV (s,i) => List[String s, Integer i]
      | TMC (i,j) => List[Integer i, Integer j]
      | TMAp(i,j) => List[Symbol "ap", Integer i, Integer j]
      | TMAbs(i,j) => List[Symbol "ab", Integer i, Integer j]
fun shared_term_decode s =
    let
      val (els, last) = strip_list s
    in
      if last <> NONE then NONE
      else
        case els of
            [String s, Integer i] => SOME (TMV (s,i))
          | [Integer i, Integer j] => SOME (TMC(i,j))
          | [Symbol "ap", Integer i, Integer j] => SOME (TMAp(i,j))
          | [Symbol "ab", Integer i, Integer j] => SOME (TMAbs(i,j))
          | _ => NONE
    end

val enc_tmtable : termtable encoder =
    tagged_encode "term-table" (list_encode shared_term_encode) o
    List.rev o #termlist
end (* local *)

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

end; (* struct *)
