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

fun temp_encoded_update sdata thyname {data,ty} =
    Theory.LoadableThyData.temp_encoded_update {
      thy = thyname,
      thydataty = ty,
      shared_readmaps = {strings = read_string sdata, terms = read_term sdata},
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
  bind_decode (
    list_decode (pair_decode(string_decode, list_decode int_decode))
  ) depmunge
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
      map_decode thmmunge (
        pair3_decode (string_decode, deptag_decode, list_decode string_decode)
      )
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

fun string_to_class "A" = SOME DB.Axm
  | string_to_class "T" = SOME DB.Thm
  | string_to_class "D" = SOME DB.Def
  | string_to_class _ = NONE

fun class_decode c =
    HOLsexp.map_decode (List.map (fn i => (i, c))) (
      HOLsexp.list_decode HOLsexp.int_decode
    )

fun load_thydata thyname path =
  let
    open HOLsexp
    val raw_data = fromFile path
    val raw_data = dtag "theory" raw_data
    val (thyparentage, rest) =
        case raw_data of
            Cons(t1,t2) => (t1,t2)
          | _ => raise TheoryReader "No thy-parentage prefix"
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
    val (core_data, incorporate_data, thydata_data) =
        force "toplevel_decode" (
          pair3_decode (
            SOME,
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
    fun with_strings _ = Theory.incorporate_types thyname new_types
    fun with_stridty (str,id,tyv) =
        Theory.incorporate_consts thyname tyv new_consts
    val share_data = force "decoding core-data" (
          dec_sdata {with_strings = with_strings, with_stridty = with_stridty}
        ) core_data
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
          ) thydata_data
        )
  in
    thmdict
  end handle Interrupt => raise Interrupt
           | e => raise TheoryReader ("Exception raised: " ^
                                      General.exnMessage e)

end;  (* TheoryReader *)
