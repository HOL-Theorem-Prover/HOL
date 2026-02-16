structure bnfBase :> bnfBase =
struct

open HolKernel bnfBase_dtype parse_bnf

type t = thm info KNametab.table
type key = KernelSig.kernelname

fun pure_lookup db tynm = KNametab.lookup db tynm

fun pure_insert (tynm, info) db = KNametab.update (tynm,info) db

fun kname_to_thm_info (bI fields :kname info) : thm info =
   let
     val {bnd,bndthms,canontype,gset,gsetIMAGE,gsetmap,
          map,mapID,mapO,mapIMAGE,mapCONG,
          relator,set,siblings} =
         fields
     val convertN = DB.fetch_knm
   in
     bI {
       bnd = bnd,
       bndthms = List.map convertN bndthms,
       canontype = canontype,

       gset = gset,
       gsetIMAGE = convertN gsetIMAGE,
       gsetmap = convertN gsetmap,

       map = map,
       mapCONG = convertN mapCONG,
       mapID = convertN mapID,
       mapIMAGE = List.map convertN mapIMAGE,
       mapO = convertN mapO,

       relator = relator,
       set = set,
       siblings = siblings
     }
   end

local
  open ThyDataSexp
  exception OptionExn = Option.Option
  val termdef_ed = pair_ed (term_ed, kname_ed)
in
  fun tup2rec ((siblings,map,set,gset),
               (relator,bnd,bndthms),
               (mapO,mapID,mapIMAGE,mapCONG),
               (canontype, gsetmap, gsetIMAGE)
              ) =
      bI {siblings = siblings, map = map, set = set, gset = gset,
          relator = relator, bnd = bnd, mapO = mapO, mapID = mapID,
          mapIMAGE = mapIMAGE, mapCONG = mapCONG, bndthms = bndthms,
          gsetmap = gsetmap, gsetIMAGE = gsetIMAGE, canontype = canontype}
  fun rec2tup (bI {siblings , map, set, gset,
                   relator, bnd, mapO, mapID,
                   mapIMAGE, mapCONG, bndthms,
                   gsetmap, gsetIMAGE, canontype}) =
      ((siblings,map,set,gset),
       (relator,bnd,bndthms),
       (mapO,mapID,mapIMAGE,mapCONG),
       (canontype,gsetmap, gsetIMAGE))


  val ed0 = pair4_ed (
        pair4_ed (add_label "siblings" $ list_ed type_ed,
                  add_label "map" $ term_ed,
                  add_label "set" $ list_ed term_ed,
                  add_label "gset" $ term_ed),
        pair3_ed (add_label "relator" $ term_ed,
                  add_label "bnd" term_ed,
                  add_label "bndthms" $ list_ed kname_ed),
        pair4_ed (add_label "mapID" kname_ed,
                  add_label "mapO" kname_ed,
                  add_label "mapIMAGE" $ list_ed kname_ed,
                  add_label "mapCONG" kname_ed),
        pair3_ed (add_label "canontype" type_ed,
                  add_label "gsetmap" kname_ed,
                  add_label "gsetIMAGE" kname_ed)
      )
  val ed1 = bij_ed (rec2tup, tup2rec) ed0
  val bnf_ed = pair_ed (kname_ed, ed1)
end

local
  val empty_t = KNametab.empty : t
  fun apply_delta (ty,info) db = pure_insert (ty, kname_to_thm_info info) db
  val adinfo = {tag = "BnfBase", initial_values = [("min", empty_t)],
                apply_delta = apply_delta} :
               (key * kname info, t) AncestryData.adata_info
in
val full_result as {DB = thy_lookup,
                    get_global_value = fullDB,
                    record_delta = prim_updateDB, ...} =
    AncestryData.fullmake {
      adinfo = adinfo,
      uptodate_delta = K true,
      sexps = { dec = #2 bnf_ed, enc = #1 bnf_ed},
      globinfo = {apply_to_global = apply_delta,
                  thy_finaliser = NONE,
                  initial_value = empty_t}
    }
end

val is_fun_type = can dom_rng

fun last_arrow ty =
    let val (d,r) = dom_rng ty
    in
      if is_fun_type r then last_arrow r
      else ty
    end

fun num_alphas ty =
    let
      fun itthis tyv c =
          if String.isPrefix "'a" (dest_vartype tyv) then c + 1
          else c
    in
      itlist itthis (type_vars ty) 0
    end

fun check p x tystring msg =
    (p x handle HOL_ERR _ => false) orelse
    raise mk_HOL_ERR "bnfBase" "sanity_check"
          ("Invalid info (" ^ msg ^ ") for type " ^ tystring)

fun kname_of_type ty =
    let val {Thy,Tyop,...} = dest_thy_type ty
    in
      {Thy = Thy, Name = Tyop}
    end

fun sanity_check (ty:key) ((info as bI {set,gset,map,canontype,...}) : thm info) =
    let val tys = "{Thy=\"" ^ #Thy ty ^ "\",Name=\"" ^ #Name ty ^ "\"}"
        val n = num_alphas canontype
        fun c p x m = check p x tys m

    in
      c (fn knm => kname_of_type canontype = knm) ty
        "Kernel name (key) doesn't correspond to canontype field" ;
      c (null o free_vars) map "map value not ground" ;
      c (List.all (null o free_vars)) set "a set value not ground" ;
      c (null o free_vars) gset "generic set value not ground" ;
      c (fn m =>
            (m |> type_of |> funpow n (#2 o dom_rng) |> dom_rng |> #1) =
            canontype)
        map
        "map constant's type incorrect"
    end

fun updateDB (ty,info as bI fields) =
    let val thm_info as bI thm_fields = kname_to_thm_info info
        val _ = sanity_check ty thm_info
    in
      prim_updateDB (ty, info)
    end
end
