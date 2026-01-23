structure bnfBase :> bnfBase =
struct

open HolKernel bnfBase_dtype parse_bnf

type t = thm info TypeNet.typenet

fun pure_lookup db ty = TypeNet.peek (db,ty)

fun pure_insert db ty info = TypeNet.insert(db,ty,info)

fun kname_to_thm_info (bI {siblings,map,set,relator,bnd}:kname info) =
   let
     fun convert (tm,kname) = (tm,DB.fetch_knm kname)
   in
     bI {siblings = siblings, map = convert map,
         set = List.map convert set, relator = convert relator,
         bnd = bnd}
   end

local
  open ThyDataSexp
  exception OptionExn = Option.Option
  fun toSEXP_term_defintion (term,kname) = List[Term term,KName kname]
  fun fromSEXP_term_definition (List[Term term,KName kname]) = (term,kname)
    | fromSEXP_term_definition _ = raise OptionExn
in
  fun toSEXP0 (bI {siblings,map,set,relator,bnd}:kname info) =
      List[
          List[String "siblings",List (List.map Type siblings)],
          List[String "map",toSEXP_term_defintion map],
          List[String "set",List (List.map toSEXP_term_defintion set)],
          List[String "relator", toSEXP_term_defintion relator],
          List[String "bnd", Term bnd]
          ]
  fun toSEXP (ty,b_info) = List[Type ty, toSEXP0 b_info]


  fun fromSEXP0 s =
     let
        fun dest_Type (Type t) = t
          | dest_Type  _ = raise OptionExn
        val fromSEXP_term_definition_list =
            List.map fromSEXP_term_definition
     in
        case s of
             List[
                 List[String "siblings",List siblings_sexps],
                 List[String "map",map_sexp],
                 List[String "set", List set_sexps],
                 List[String "relator", relator_sexp],
                 List[String "bnd", Term bnd]
             ] => bI {siblings = List.map dest_Type siblings_sexps,
                      map = fromSEXP_term_definition map_sexp,
                      set = fromSEXP_term_definition_list set_sexps,
                      relator = fromSEXP_term_definition relator_sexp,
                      bnd = bnd}
          | _ => raise OptionExn
     end

  fun fromSEXP s =
    case s of
        List[Type ty,b_info_sexp] => SOME (ty, fromSEXP0 b_info_sexp)
                                    handle OptionExn => NONE
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
                apply_delta = apply_delta} : (hol_type * kname info ,
                                              thm info TypeNet.typenet) AncestryData.adata_info
in
val full_result = AncestryData.fullmake
                              {adinfo = adinfo,
                               uptodate_delta = K true,
                               sexps = { dec = fromSEXP, enc = toSEXP},
                               globinfo = {apply_to_global = apply_delta,
                                           thy_finaliser = NONE,
                                           initial_value = empty_t}}
end



end
