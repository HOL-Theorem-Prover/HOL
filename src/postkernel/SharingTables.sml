structure SharingTables :> SharingTables =
struct

open Term Type DB_dtype
infix |>
fun x |> f = f x

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

(* ----------------------------------------------------------------------
    sharing table data more abstractly
   ---------------------------------------------------------------------- *)

type extract_data =
 {named_terms : (string * Term.term) list,
  unnamed_terms : Term.term list,
  named_types : (string * Type.hol_type) list,
  unnamed_types : Type.hol_type list,
  theorems : (string * Thm.thm * thminfo) list}

datatype sharing_data_in = SDI of {strtable : stringtable,
                                   idtable : idtable,
                                   tytable : typetable,
                                   tmtable : termtable,
                                   exp : extract_data}

fun empty_in exp = SDI{strtable = empty_strtable,
                       idtable = empty_idtable,
                       tytable = empty_tytable,
                       tmtable = empty_termtable,
                       exp = exp}

fun add_strings strs (SDI {strtable,idtable,tytable,tmtable,exp}) =
    let fun str1 (s, tab) = #2 (new_string s tab)
        val strtable = List.foldl str1 strtable strs
    in
      SDI{strtable = strtable, idtable = idtable, tytable = tytable,
          tmtable = tmtable, exp = exp}
    end

fun add_types tys (SDI{strtable,idtable,tytable,tmtable,exp}) =
    let
      fun dotypes (ty, (strtable, idtable, tytable)) = let
        val (_, strtable, idtable, tytable) =
            make_shared_type ty strtable idtable tytable
      in
        (strtable, idtable, tytable)
      end
      val (strtable,idtable,tytable) =
          List.foldl dotypes (strtable, idtable, tytable) tys
    in
      SDI{strtable = strtable, idtable = idtable, tytable = tytable,
          tmtable = tmtable, exp = exp}
    end

fun add_terms tms (SDI{strtable,idtable,tytable,tmtable,exp}) =
    let
      val tms = Term.all_atomsl tms empty_tmset |> HOLset.listItems
      val (strtable,idtable,tytable,tmtable) =
          List.foldl (fn (t,tables) => #2 (make_shared_term t tables))
                     (strtable,idtable,tytable,tmtable)
                     tms
    in
      SDI{strtable = strtable, idtable = idtable, tytable = tytable,
          tmtable = tmtable, exp = exp}
    end

fun thm_atoms acc th = Term.all_atomsl (Thm.concl th :: Thm.hyp th) acc

fun thml_atoms thlist acc =
    case thlist of
      [] => acc
    | (th::ths) => thml_atoms ths (thm_atoms acc th)

fun enc_dep findstr ((s,n),dl) =
    let open HOLsexp
        fun f (thy,l) = Cons(findstr thy, list_encode Integer l)
    in
      list_encode f ((s,[n]) :: dl)
    end

fun dest_dep d =
    case d of
        Dep.DEP_SAVED (did,thydl) => (did,thydl)
      | Dep.DEP_UNSAVED dl => raise SharingTables "Can't encode unsaved dep"

fun enc_tag findstr tag =
    let open HOLsexp
        val dep = Tag.dep_of tag
        val ocl = #1 (Tag.dest_tag tag)
    in
      pair_encode(enc_dep findstr o dest_dep, list_encode String) (dep,ocl)
    end

fun path_strings ps = let val {arcs,vol,...} = OS.Path.fromString ps
                      in
                        vol :: arcs
                      end

fun thminfo_strings ({loc,...}: thminfo) =
    case loc of
        Unknown => []
      | Located {scriptpath,...} => path_strings scriptpath


fun thm_strings (_ (* name *),th,i) =
    let val (sn, dl) = dest_dep (Tag.dep_of (Thm.tag th) )
    in
      #1 sn :: map #1 dl @ thminfo_strings i
    end

fun build_sharing_data (ed : extract_data) =
    let
      val {named_types, named_terms, unnamed_types, unnamed_terms, theorems} =
          ed
      val sdi = empty_in ed
                         |> add_types (map #2 named_types)
                         |> add_types unnamed_types
      val tm_atoms =
          thml_atoms (map #2 theorems) empty_tmset
                     |> Term.all_atomsl (unnamed_terms @ map #2 named_terms)
    in
      sdi |> add_terms (HOLset.listItems tm_atoms)
          |> add_strings (map #1 theorems)
          |> add_strings (List.concat (map thm_strings theorems))
    end

fun write_string (SDI{strtable,...}) s =
    Map.find(#map strtable,s)
    handle Map.NotFound =>
           raise SharingTables ("write_string: can't find \"" ^ s ^ "\"")
fun write_type (SDI{tytable,...}) ty =
    Map.find(#tymap tytable,ty)
fun write_term (SDI{tmtable,...}) =
    Term.write_raw (fn t => Map.find(#termmap tmtable,t))
    handle Map.NotFound => raise SharingTables "write_term: can't find term"

fun enc_thminfo findstr {private,loc,class} =
    let open HOLsexp
        val privtag = Integer (if private then 1 else 0)
        val classtag = Integer (case class of Axm => 0 | Def => 1 | Thm => 2)
    in
      case loc of
          Unknown => List [classtag, privtag]
        | Located{scriptpath,linenum,exact} =>
          let val {vol,arcs,...} = OS.Path.fromString scriptpath
              val tag = Integer (if exact then 1 else 0)
          in
            List (classtag :: privtag :: tag :: Integer linenum ::
                  map findstr (vol::arcs))
          end
    end

fun enc_sdata (sd as SDI{strtable,idtable,tytable,tmtable,exp}) =
    let
      open HOLsexp
      val {unnamed_types,named_types,unnamed_terms,named_terms,theorems} = exp
      val find_str = Integer o write_string sd
      val ty_encode = Integer o write_type sd
      val tm_encode = String o write_term sd

      fun enc_thm(s,th,info) =
          let
            val (tag, asl, w) = (Thm.tag th, Thm.hyp th, Thm.concl th)
            val i = Map.find(#map strtable, s)
          in
            pair4_encode
              (Integer,
               enc_tag find_str,
               enc_thminfo find_str,
               list_encode tm_encode)
              (i, tag, info, w::asl)
          end
    in

      tagged_encode "core-data" (
        pair_encode (
          tagged_encode "tables" (
            pair4_encode(enc_strtable,enc_idtable,enc_tytable,enc_tmtable)
          ),
          tagged_encode "exports" (
            pair3_encode(
              pair_encode( (* types *)
                list_encode ty_encode,
                list_encode (pair_encode(String,ty_encode))
              ),
              pair_encode( (* terms *)
                list_encode tm_encode,
                list_encode (pair_encode(String,tm_encode))
              ),
              list_encode enc_thm
            )
          )
        )
      ) ((strtable,idtable,tytable,tmtable),
         ((unnamed_types, named_types), (unnamed_terms, named_terms), theorems))
    end

type sharing_data_out =
     (string Vector.vector * id Vector.vector * Type.hol_type Vector.vector *
      Term.term Vector.vector * extract_data)


type 'a depinfo = {head : 'a * int, deps : ('a * int list) list}
fun mapdepinfo f ({head = (a,i),deps}:'a depinfo) : 'b depinfo =
    {head = (f a, i), deps = map (fn (a,l) => (f a, l)) deps}

fun translatepath slist =
    let
      val isAbs = case slist of
                      _ :: s :: _ => size s < 2 orelse
                                     String.substring(s,0,2) <> "$("
                    | _ => true
    in
      case slist of
          [] => OS.Path.toString {arcs = [], isAbs = true, vol = ""}
        | v::arcs => OS.Path.toString {arcs = arcs, isAbs = isAbs, vol = v}
    end
fun decclass 0 = Axm
  | decclass 1 = Def
  | decclass 2 = Thm
  | decclass i = raise SharingTables ("Bad theorem class: "^Int.toString i)

fun translate_info f ilist =
    case ilist of
        [classtag,privtag] =>
          {loc = Unknown, private = privtag <> 0, class = decclass classtag}
      | classtag::privatep::exactp::lnum::rest =>
          {loc = Located{scriptpath = translatepath (map f rest),
                         linenum = lnum, exact = (exactp <> 0)},
           private = privatep <> 0, class = decclass classtag}
      | _ => raise SharingTables "Bad theorem information"

fun read_thm strv tmvector thmrec =
    let
      val {name,depinfo:int depinfo,tagnames,encoded_hypscon,encodedloc} = thmrec
      val getstr = (fn i => Vector.sub(strv,i))
      val depinfo = mapdepinfo getstr depinfo
      val thminfo = translate_info getstr encodedloc
      val dd = (#head depinfo, #deps depinfo)
      val terms = map (Term.read_raw tmvector) encoded_hypscon
    in
      (Vector.sub(strv, name), Thm.disk_thm((dd,tagnames), terms), thminfo)
    end

val dep_decode = let
  open HOLsexp
  fun depmunge dilist =
      case dilist of
          [] => NONE
        | (n,[i]) :: rest => SOME{head = (n,i), deps = rest}
        | _ => NONE
in
  Option.mapPartial depmunge o
  list_decode (pair_decode(int_decode, list_decode int_decode))
end
val deptag_decode = let open HOLsexp in
                      pair_decode(dep_decode, list_decode string_decode)
                    end

(* really just maps to list of ints that need interpreting once string table
   is available *)
fun loc_decode s =
    let open HOLsexp
    in
      case s of
          Symbol "unknown_loc" => SOME []
        | _ => list_decode int_decode s
    end

val thm_decode =
    let
      open HOLsexp
      fun thmmunge(i,(di,tags),loc,tms) =
          {name = i, depinfo = di, tagnames = tags, encoded_hypscon = tms,
           encodedloc=loc}
    in
      Option.map thmmunge o
      pair4_decode (int_decode, deptag_decode, loc_decode,
                    list_decode string_decode)
    end

val prsexp = HOLPP.pp_to_string 70 HOLsexp.printer
fun force s dec t =
    case dec t of
        NONE => raise SharingTables ("Couldn't decode \""^s^"\": "^prsexp t)
      | SOME t => t

fun dec_sdata {with_strings,with_stridty} t =
    let
      open HOLsexp
      val decoder =
            tagged_decode "core-data" (
              pair_decode(
                tagged_decode "tables" (
                  pair4_decode(
                    dec_strings,
                    tagged_decode "id-table"
                       (list_decode (pair_decode(int_decode, int_decode))),
                    tagged_decode "type-table" (list_decode shared_type_decode),
                    tagged_decode "term-table" (list_decode shared_term_decode)
                  )
                ),
                tagged_decode "exports" (
                  pair3_decode(
                    pair_decode( (* types *)
                      list_decode int_decode,
                      list_decode (pair_decode(string_decode, int_decode))
                    ),
                    pair_decode( (* terms *)
                      list_decode string_decode,
                      list_decode (pair_decode(string_decode, string_decode))
                    ),
                    (* theorems *) list_decode thm_decode
                  )
                )
              )
            )
    in
      case decoder t of
          NONE => NONE
        | SOME ((strv,intplist,shtylist,shtmlist),
                ((raw_untys, raw_nmtys), (raw_untms, raw_nmtms), rawthms)) =>
          let
            fun sub v i = Vector.sub(v,i)
            val _ = with_strings (fn i => Vector.sub(strv,i))
            val idv = build_id_vector strv intplist
            val tyv = build_type_vector idv shtylist
            val _ = with_stridty (sub strv, sub idv, tyv)
            val tmv = build_term_vector idv tyv shtmlist
            val untys = map (fn i => Vector.sub(tyv,i)) raw_untys
            val nmtys = map (fn (s,i) => (s, Vector.sub(tyv,i))) raw_nmtys
            val untms = map (Term.read_raw tmv) raw_untms
            val nmtms = map (fn (nm,s) => (nm, Term.read_raw tmv s)) raw_nmtms
            val thms = map (read_thm strv tmv) rawthms
          in
            SOME (strv,idv,tyv,tmv,
                  {named_types = nmtys, unnamed_types = untys,
                   named_terms = nmtms, unnamed_terms = untms,
                   theorems = thms})
          end
    end

fun export_from_sharing_data (_, _, _, _, exp) = exp
fun read_term (_,_,_,tmv,_) = Term.read_raw tmv
fun read_string (strv,_,_,_,_) i = Vector.sub(strv,i)

end; (* struct *)
