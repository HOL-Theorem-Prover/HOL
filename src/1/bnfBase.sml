structure bnfBase :> bnfBase =
struct

open HolKernel bnfBase_dtype parse_bnf

type t = thm info TypeNet.typenet

fun pure_lookup db ty = TypeNet.peek (db,ty)

fun pure_insert db ty info = TypeNet.insert(db,ty,info)

fun kname_to_thm_info (bI fields :kname info) : thm info =
   let
     val {map,set,gset,relator,bnd,mapID,mapO,mapIMAGE,...} = fields
     fun convertTN (tm,kname) = (tm,DB.fetch_knm kname)
     val convertN = DB.fetch_knm
   in
     bI {siblings = #siblings fields, map = map,
         set = set,
         relator = relator,
         bnd = bnd, gset = gset,
         mapID = convertN mapID, mapO = convertN mapO,
         mapIMAGE = List.map convertN mapIMAGE}
   end

local
  open ThyDataSexp
  exception OptionExn = Option.Option
  val termdef_ed = pair_ed (term_ed, kname_ed)
in
  fun tup2rec ((siblings,map,set,gset),
               (relator,bnd),
               (mapO,mapID,mapIMAGE)) =
      bI {siblings = siblings, map = map, set = set, gset = gset,
          relator = relator, bnd = bnd, mapO = mapO, mapID = mapID,
          mapIMAGE = mapIMAGE}
  fun rec2tup (bI {siblings , map, set, gset, relator, bnd, mapO, mapID,
                   mapIMAGE}) =
      ((siblings,map,set,gset), (relator,bnd), (mapO,mapID,mapIMAGE))

  val ed0 = pair3_ed (
        pair4_ed (add_label "siblings" $ list_ed type_ed,
                  add_label "map" $ term_ed,
                  add_label "set" $ list_ed term_ed,
                  add_label "gset" $ term_ed),
        pair_ed (add_label "relator" $ term_ed,
                 add_label "bnd" term_ed),
        pair3_ed (add_label "mapID" $ kname_ed,
                  add_label "mapO" $ kname_ed,
                  add_label "mapIMAGE" $ list_ed kname_ed)
      )
  val ed1 = bij_ed (rec2tup, tup2rec) ed0
  val bnf_ed = pair_ed (type_ed, ed1)
end

(*
(*tests*)
local open listTheory
val list_map_tm = ``MAP``
val list_map_def = { Thy = "list", Name = "MAP"}
val list_set1_tm = ``LIST_TO_SET``
val list_set1_def = {Thy = "list", Name = "LIST_TO_SET"}
val list_relator_tm = ``LIST_REL``
val list_relator_def = {Thy = "list", Name = "LIST_REL_DEF"}
val bound_tm = T
in
val list_bi = bI {siblings = [], map = (list_map_tm,list_map_def),
                  set = [(list_set1_tm,list_set1_def)],
                  relator = (list_relator_tm, list_relator_def),
                  bnd = bound_tm}
end
val test = toSEXP (``:'a list``,list_bi)
val SOME test2 = fromSEXP test
(*test2 should be equal to list_bi *)
*)

local
  val empty_t = TypeNet.empty : t
  fun apply_delta (ty,info) db = pure_insert db ty (kname_to_thm_info info)
  val adinfo = {tag = "BnfBase", initial_values = [("min", empty_t)],
                apply_delta = apply_delta} :
               (hol_type * kname info ,
                thm info TypeNet.typenet) AncestryData.adata_info
in
val full_result as {DB = thy_lookup,
                    get_global_value = fullDB,
                    record_delta = updateDB, ...} =
    AncestryData.fullmake {
      adinfo = adinfo,
      uptodate_delta = K true,
      sexps = { dec = #2 bnf_ed, enc = #1 bnf_ed},
      globinfo = {apply_to_global = apply_delta,
                  thy_finaliser = NONE,
                  initial_value = empty_t}
    }
end



end
