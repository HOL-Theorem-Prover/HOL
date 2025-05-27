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

open HolKernel SharingTables RawTheory_dtype RawTheoryReader

fun temp_encoded_update sdata thyname {data,ty} =
    Theory.LoadableThyData.temp_encoded_update {
      thy = thyname,
      thydataty = ty,
      shared_readmaps = {strings = read_string sdata, terms = read_term sdata},
      data = data
    }


fun load_thydata (r as {thyname,path}) =
    let
      open HOLsexp
      val rawthy as {parents,tables,exports,name=stored_name,...} = load_raw_thydata r
      fun mungename {thy,hash} = (thy,hash)
      val _ = thyname = stored_name orelse
              raise TheoryReader
                    ("reading at " ^ path ^ " for theory " ^ thyname ^
                     " and got theory called " ^ stored_name ^ " instead")

      val hash = TheoryPP.minHash (* TODO: compute the actual hash *)
      val _ = Theory.link_parents (thyname, hash) (map mungename parents)
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
