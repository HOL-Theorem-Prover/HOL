(* ========================================================================== *)
(* FILE          : TheoryReader.sml                                           *)
(* DESCRIPTION   : Read theory data from disk                                 *)
(*                                                                            *)
(* AUTHOR        : Thibault Gauthier, University of Innsbruck                 *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure TheoryReader :> TheoryReader =
struct

type thm      = Thm.thm;
type term     = Term.term
type hol_type = Type.hol_type

open HolKernel SharingTables TheoryReader_dtype

fun temp_encoded_update sdata thyname {data,ty} =
    Theory.LoadableThyData.temp_encoded_update {
      thy = thyname,
      thydataty = ty,
      shared_readmaps = {strings = read_string sdata, terms = read_term sdata},
      data = data
    }

exception TheoryReader of string
val prsexp = HOLPP.pp_to_string 70 HOLsexp.printer


fun dtag s t =
    case HOLsexp.dest_tagged s t of
        NONE => raise TheoryReader ("Expecting tag "^s)
      | SOME t => t

fun dtaglist tags t =
    let open HOLsexp
    in
      case strip_list t of
          (_, SOME last) => raise TheoryReader
                                  ("Extraneous at end of list: " ^prsexp t)
        | (els, NONE) =>
          let
            fun recurse tags els A =
                case (tags,els) of
                    ([],[]) => List.rev A
                  | ([], e::_) => raise TheoryReader ("Extra list element: "^
                                                      prsexp e)
                  | (t::_, []) => raise TheoryReader ("No data for tag " ^ t)
                  | (t::ts, e::es) =>
                    let val e = dtag t e
                    in
                      recurse ts es (e::A)
                    end
          in
            recurse tags els []
          end
    end

fun force s dec t =
    case dec t of
        NONE => raise TheoryReader ("Couldn't decode \""^s^"\": "^prsexp t)
      | SOME t => t

fun string_to_class "A" = SOME DB.Axm
  | string_to_class "T" = SOME DB.Thm
  | string_to_class "D" = SOME DB.Def
  | string_to_class _ = NONE

val dec_thyname : raw_name HOLsexp.decoder =
    let open HOLsexp
    in
      HOLsexp.map_decode
        (fn (s,n1,n2) => {thy = s, tstamp1 = n1, tstamp2 = n2}) $
        pair3_decode (string_decode,
                      Option.map Arbnum.fromString o string_decode,
                      Option.map Arbnum.fromString o string_decode)
    end


(* ----------------------------------------------------------------------
    decoding raw theorems
   ---------------------------------------------------------------------- *)

fun decclass 0 = DB_dtype.Axm
  | decclass 1 = DB_dtype.Def
  | decclass 2 = DB_dtype.Thm
  | decclass i = raise SharingTables ("Bad theorem class: "^Int.toString i)

val dep_decode : int raw_dep HOLsexp.decoder = let
  open HOLsexp
  fun depmunge dilist =
      case dilist of
          [] => NONE
        | (n,[i]) :: rest => SOME{me = (n,i), deps = rest}
        | _ => NONE
in
  Option.mapPartial depmunge o
  list_decode (pair_decode(int_decode, list_decode int_decode))
end
val deptag_decode = let open HOLsexp in
                      pair_decode(dep_decode, list_decode string_decode)
                    end

fun loc_decode ilist =
    case ilist of
        [] => SOME rlUnknown
      | exactp :: lnum :: path =>
        SOME (rlLocated {path = path, linenum = lnum, exact = exactp <> 0})
      | _ => NONE

val info_decode = let
  open HOLsexp
  fun bind ilist =
      case ilist of
          ctag :: privtag :: rest =>
          Option.map (fn rl =>
                         {class = decclass ctag,
                          private = privtag <> 0,
                          loc = rl})
                     (loc_decode rest)
        | _ => NONE
in
  bind_decode (list_decode int_decode) bind
end

val thm_decode : raw_thm HOLsexp.decoder =
    let
      open HOLsexp
      fun thmmunge(i,(di,tags),{class,private,loc},tms) =
          case tms of
              [] => NONE
            | c::hyps =>
              SOME {
                name = i, deps = di, tags = tags, concl = c,
                hyps = hyps,class=class,private=private,loc=loc
              }
    in
      Option.mapPartial thmmunge o
      pair4_decode (int_decode, deptag_decode, info_decode,
                    list_decode string_decode)
    end


val core_decode =
    let open HOLsexp
    in
      map_decode
        (fn ((strt,idt,tyt,tmt), ((utys,ntys), (utms,ntms), thms)) =>
            {tables = {stringt = strt, idt = idt, typet = tyt, termt = tmt},
             exports = {
               unnamed_types = utys,
               named_types = ntys,
               unnamed_terms = utms,
               named_terms =
                 map (fn (n,t) => {name = n, encoded_term = t}) ntms,
               thms = thms
             }
        })
        (tagged_decode "core-data" (
            pair_decode(
              tagged_decode "tables" (
                pair4_decode(
                  dec_strings,
                  tagged_decode
                    "id-table"
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
        )
    end

fun load_raw_thydata {thyname, path} : raw_theory =
  let
    open HOLsexp
    val raw_data = fromFile path
    val raw_data = dtag "theory" raw_data
    val (thyparentage, rest) =
        case raw_data of
            Cons(t1,t2) => (t1,t2)
          | _ => raise TheoryReader "No thy-parentage prefix"
    val (thy_data, parents_data) =
        case thyparentage of
            Cons p => p
          | _ => raise TheoryReader "thyparentage not a pair"
    val fullthy as {thy,...} = force "thyname" dec_thyname thy_data
    val parents = force "parents" (list_decode dec_thyname) parents_data
    val ({tables,exports}, incorporate_data, thydata_data) =
        force "toplevel_decode" (
          pair3_decode (
            core_decode,
            tagged_decode "incorporate" SOME,
            tagged_decode "loadable-thydata" SOME
          )
        ) rest
    val (new_types, new_consts) =
        force "incorporate_decode" (
          pair_decode(
            tagged_decode "incorporate-types" (
              list_decode (pair_decode (string_decode, int_decode))
            ),
            tagged_decode "incorporate-consts" (
              list_decode (pair_decode (string_decode, int_decode))
            )
          )
        ) incorporate_data
  in
    { name = fullthy, parents = parents,
      tables = tables,
      exports = exports,
      newsig = {types = new_types, consts = new_consts},
      thydata = thydata_data
    }
  end

fun load_thydata (r as {thyname,path}) =
    let
      open HOLsexp
      val rawthy as {parents,tables,exports,name,...} = load_raw_thydata r
      fun mungename {thy,tstamp1,tstamp2} = (thy,tstamp1,tstamp2)
      val {thy = stored_name, ...} = name
      val _ = thyname = stored_name orelse
              raise TheoryReader
                    ("reading at " ^ path ^ " for theory " ^ thyname ^
                     " and got theory called " ^ stored_name ^ " instead")

      val _ = Theory.link_parents (mungename name) (map mungename parents)
      val {types=new_types,consts=new_consts} = #newsig rawthy
      fun before_types () = Theory.incorporate_types thyname new_types
      fun before_terms tyv =
          Theory.incorporate_consts
            thyname
            (map (fn (n,i) => (n,Vector.sub(tyv,i))) new_consts)
      val share_data =
            dec_sdata {
              before_types = before_types,
              before_terms = before_terms,
              tables = tables,
              exports = exports
            }
    val {theorems = named_thms,...} = export_from_sharing_data share_data

    val thmdict =
        List.foldl (fn ((n,th,i), D) => Symtab.update (n, (th,i)) D)
                   Symtab.empty
                   named_thms
    val _ = DB.bindl thyname named_thms
    val _ =
        app (temp_encoded_update share_data thyname) (
          force "thydata" (
            Option.map (map (fn (ty,d) => {data=d,ty=ty})) o
            list_decode(pair_decode(string_decode, SOME))
          )
          (#thydata rawthy)
        )
  in
    thmdict
  end handle Interrupt => raise Interrupt
           | e => raise TheoryReader ("Exception raised: " ^
                                      General.exnMessage e)

end;  (* TheoryReader *)
