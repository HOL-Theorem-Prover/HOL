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

fun read_thm tmvector {name,depinfo,tagnames,encoded_hypscon} =
    let
      val dd = (#head depinfo, #deps depinfo)
      val terms = map (Term.read_raw tmvector) encoded_hypscon
    in
      (name, Thm.disk_thm((dd,tagnames), terms))
    end

fun load_thydata thyname path =
  let
    val raw_data = TheoryDat_Parser.read_dat_file {filename=path}
    val {thyname = fullthy as (thyname, _, _), parents, new_types,
         idvector, ...} = raw_data
    val _ = Theory.link_parents fullthy parents
    val _ = Theory.incorporate_types thyname new_types
    val tyvector = build_type_vector idvector (#shared_types raw_data)
    val _ = Theory.incorporate_consts thyname tyvector (#new_consts raw_data)
    val tmvector = build_term_vector idvector tyvector (#shared_terms raw_data)
    val named_thms = map (read_thm tmvector) (#theorems raw_data)
    val thmdict = Redblackmap.fromList String.compare named_thms
    val _ = DB.bindl thyname
                     (map (fn (n,c) => (n,Redblackmap.find (thmdict,n),c))
                          (#classinfo raw_data))
    val _ = app (temp_encoded_update tmvector thyname) (#thydata raw_data)
  in
    thmdict
  end

end;  (* TheoryReader *)
