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

open HolKernel SharingTables

fun temp_encoded_update tmvector thyname {data,ty} =
    Theory.LoadableThyData.temp_encoded_update {
      thy = thyname,
      thydataty = ty,
      read = Term.read_raw tmvector,
      data = data
    }

type depinfo = {head : string * int, deps : (string * int list) list}

fun read_thm tmvector {name,depinfo:depinfo,tagnames,encoded_hypscon} =
    let
      val dd = (#head depinfo, #deps depinfo)
      val terms = map (Term.read_raw tmvector) encoded_hypscon
    in
      (name, Thm.disk_thm((dd,tagnames), terms))
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
  list_decode (pair_decode(string_decode, list_decode int_decode))
end
val deptag_decode = let open HOLsexp in
                      pair_decode(dep_decode, list_decode string_decode)
                    end
val thm_decode =
    let
      open HOLsexp
      fun thmmunge(s,(di,tags),tms) =
          {name = s, depinfo = di, tagnames = tags, encoded_hypscon = tms}
    in
      Option.map thmmunge o
      pair3_decode (string_decode, deptag_decode, list_decode string_decode)
    end

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

fun string_to_class "Axm" = SOME DB.Axm
  | string_to_class "Thm" = SOME DB.Thm
  | string_to_class "Def" = SOME DB.Def
  | string_to_class _ = NONE

val class_decode = Option.mapPartial string_to_class o HOLsexp.symbol_decode

fun load_thydata thyname path =
  let
    open HOLsexp
    val raw_data = fromFile path
    val raw_data = dtag "theory" raw_data
    val (thyparentage, rest) =
        case raw_data of
            Cons(t1,t2) => (t1,t2)
          | _ => raise TheoryReader "No thy-parentage prefix"
    val [inctypes_data, stringtable_data, idtable_data, typetable_data,
         incconsts_data, termtable_data, theorems_data, classes_data,
         thydata_data] =
        dtaglist ["incorporate-types", "string-table",
                  "id-table", "type-table", "incorporate-consts", "term-table",
                  "theorems", "thm-classes", "loadable-thydata"] rest
    val dec_thy =
        pair3_decode (string_decode,
                      Option.map Arbnum.fromString o string_decode,
                      Option.map Arbnum.fromString o string_decode)
    val (thy_data, parents_data) =
        case thyparentage of
            Cons p => p
          | _ => raise TheoryReader "thyparentage not a pair"
    val (fullthy as (thyname, _, _)) = force "thyname" dec_thy thy_data
    val parents = force "parents" (list_decode dec_thy) parents_data
    val _ = Theory.link_parents fullthy parents

    val new_types =
        force "incorporate-types"
              (list_decode (pair_decode(string_decode, int_decode)))
              inctypes_data
    val _ = Theory.incorporate_types thyname new_types

    val strvector =
        Vector.fromList
          (force "string-table" (list_decode string_decode) stringtable_data)

    val idvector =
        build_id_vector strvector (
          force "id-table" (list_decode (pair_decode(int_decode, int_decode)))
                idtable_data
        )

    val tyvector =
        build_type_vector idvector (
          force "type-table" (list_decode shared_type_decode) typetable_data
        )

    val _ =
        Theory.incorporate_consts thyname tyvector (
          force "incorporate-consts"
                (list_decode (pair_decode(string_decode,int_decode)))
                incconsts_data
        )

    val tmvector =
        build_term_vector idvector tyvector (
          force "term-table" (list_decode shared_term_decode) termtable_data
        )
    val named_thms =
        map (read_thm tmvector) (
          force "theorems" (list_decode thm_decode) theorems_data
        )
    val thmdict = Redblackmap.fromList String.compare named_thms
    val _ =
        let
          val classinfo =
              force "thm-classes"
                    (list_decode(pair_decode(string_decode,class_decode)))
                    classes_data
          fun mapthis (n,c) =
              let val th =
                      Redblackmap.find (thmdict,n)
                      handle Redblackmap.NotFound =>
                             raise TheoryReader ("Couldn't lookup "^n)
              in (n,th,c)
              end
        in
          DB.bindl thyname (map mapthis classinfo)
        end
    val _ =
        app (temp_encoded_update tmvector thyname) (
          force "thydata" (
            Option.map (map (fn (ty,ds) => {data=String.concat ds,ty=ty})) o
            list_decode(pair_decode(string_decode, list_decode string_decode))
          ) thydata_data
        )
  in
    thmdict
  end handle Interrupt => raise Interrupt
           | e => raise TheoryReader ("Exception raised: " ^
                                      General.exnMessage e)

end;  (* TheoryReader *)
