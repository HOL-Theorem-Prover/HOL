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
     bI {siblings = #siblings fields, map = convertTN map,
         set = List.map convertTN set,
         relator = convertTN relator,
         bnd = bnd, gset = convertTN gset,
         mapID = convertN mapID, mapO = convertN mapO,
         mapIMAGE = List.map convertN mapIMAGE}
   end

local
  open ThyDataSexp
  exception OptionExn = Option.Option
  fun toSEXP_term_definition (term,kname) = List[Term term,KName kname]
  fun fromSEXP_term_definition (List[Term term,KName kname]) = (term,kname)
    | fromSEXP_term_definition _ = raise OptionExn
in
  fun toSEXP0 (bI fields :kname info) =
      let
        val {siblings,map,set,gset,relator,bnd,mapO,mapID,mapIMAGE} = fields
      in
        List[
          List[String "siblings",List (List.map Type siblings)],
          List[String "map",toSEXP_term_definition map],
          List[String "set",List (List.map toSEXP_term_definition set)],
          List[String "gset",toSEXP_term_definition gset],
          List[String "relator", toSEXP_term_definition relator],
          List[String "bnd", Term bnd],
          List[String "mapID", KName mapID],
          List[String "mapO", KName mapO],
          List[String "mapIMAGE", List (List.map KName mapIMAGE)]
          ]
      end
  fun toSEXP (ty,b_info) = List[Type ty, toSEXP0 b_info]


  fun fromSEXP0 s =
     let
        fun dest_Type (Type t) = t
          | dest_Type  _ = raise OptionExn
        fun dest_KName (KName knm) = knm
          | dest_KName _ = raise OptionExn
        val fromSEXP_term_definition_list =
            List.map fromSEXP_term_definition
     in
        case s of
             List[
                 List[String "siblings",List siblings_sexps],
                 List[String "map",map_sexp],
                 List[String "set", List set_sexps],
                 List[String "gset", gset_sexp],
                 List[String "relator", relator_sexp],
                 List[String "bnd", Term bnd],
                 List[String "mapID", KName mapID],
                 List[String "mapO", KName mapO],
                 List[String "mapIMAGE", List mapimg_names]
             ] => bI {siblings = List.map dest_Type siblings_sexps,
                      map = fromSEXP_term_definition map_sexp,
                      gset = fromSEXP_term_definition gset_sexp,
                      set = fromSEXP_term_definition_list set_sexps,
                      relator = fromSEXP_term_definition relator_sexp,
                      bnd = bnd,
                      mapID = mapID,
                      mapO = mapO,
                      mapIMAGE = map dest_KName mapimg_names}
          | _ => raise OptionExn
     end

  fun fromSEXP s =
    case s of
        List[Type ty,b_info_sexp] =>
          (SOME (ty, fromSEXP0 b_info_sexp) handle OptionExn => NONE)
     |  _ => NONE
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
      sexps = { dec = fromSEXP, enc = toSEXP},
      globinfo = {apply_to_global = apply_delta,
                  thy_finaliser = NONE,
                  initial_value = empty_t}
    }
end



end
