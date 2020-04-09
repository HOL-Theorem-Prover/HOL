(* ========================================================================= *)
(* FILE          : mlTacticData.sml                                          *)
(* DESCRIPTION   : Storing data                                              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)


structure mlTacticData :> mlTacticData =
struct

open HolKernel boolLib Abbrev SharingTables Portable aiLib smlLexer
  mlFeature

val ERR = mk_HOL_ERR "mlTacticData"
fun err_msg s l = raise ERR s (String.concatWith " " (first_n 10 l))

(* -------------------------------------------------------------------------
   Tactic data type
   ------------------------------------------------------------------------- *)

type tacdata =
  {
  tacfea : (lbl,fea) Redblackmap.dict,
  tacfea_cthy : (lbl,fea) Redblackmap.dict,
  taccov : (string, int) Redblackmap.dict,
  tacdep : (goal, lbl list) Redblackmap.dict
  }

val empty_tacdata : tacdata =
  {
  tacfea = dempty lbl_compare,
  tacfea_cthy = dempty lbl_compare,
  taccov = dempty String.compare,
  tacdep = dempty goal_compare
  }

(* -------------------------------------------------------------------------
   Check if data is up-to-date before export
   ------------------------------------------------------------------------- *)

fun uptodate_goal (asl,w) = all uptodate_term (w :: asl)
fun uptodate_feav ((_,_,g,gl),_) = all uptodate_goal (g :: gl)


(* -------------------------------------------------------------------------
   Exporting terms
   ------------------------------------------------------------------------- *)

fun pp_tml tml =
  let
    val ed = {unnamed_terms = tml, named_terms = [], unnamed_types = [],
              named_types = [], theorems = []}
    val sdo = build_sharing_data ed
    val sexp = enc_sdata sdo
  in
    HOLsexp.printer sexp
  end

fun export_terml file tml =
  let
    val tml' = filter uptodate_term tml
    val _ = if length tml <> length tml'
            then print_endline "Warning: out-of-date terms are not exported"
            else ()
    val ostrm = Portable.open_out file
  in
    (PP.prettyPrint (curry TextIO.output ostrm, 75) (pp_tml tml');
     TextIO.closeOut ostrm)
  end

(* -------------------------------------------------------------------------
   Exporting tactic data
   ------------------------------------------------------------------------- *)

open HOLsexp
fun enc_goal enc_tm (asl,w) = list_encode enc_tm (w::asl)
fun dec_goal dec_tm =
    Option.map (fn (w,asl) => (asl,w)) o
    Option.mapPartial List.getItem o
    list_decode dec_tm

fun enc_goal_list enc_tm = list_encode (enc_goal enc_tm)
fun dec_goal_list dec_tm = list_decode (dec_goal dec_tm)
val enc_fea = Integer
val dec_fea = int_decode

fun enc_feav enc_tm (* ((stac,t,g,gl),fea) *) =
    tagged_encode "feav" (
      pair_encode(
        pair4_encode(
          String,
          String o Real.toString,
          enc_goal enc_tm,
          enc_goal_list enc_tm
        ),
        list_encode enc_fea
      )
    )
fun dec_feav dec_tm =
    tagged_decode "feav" (
      pair_decode(
        pair4_decode (
          string_decode,
          Option.mapPartial Real.fromString o string_decode,
          dec_goal dec_tm,
          dec_goal_list dec_tm
        ),
        list_decode dec_fea
      )
    )

fun compare_exact (t1,t2) = case (dest_term t1, dest_term t2) of
     (VAR _, VAR _) => Term.compare (t1,t2)
   | (VAR _, _) => LESS
   | (_, VAR _) => GREATER
   | (CONST _, CONST _) => Term.compare (t1,t2)
   | (CONST _, _) => LESS
   | (_, CONST _) => GREATER
   | (COMB p1, COMB p2) => cpl_compare compare_exact compare_exact (p1,p2)
   | (COMB _, _) => LESS
   | (_, COMB _) => GREATER
   | (LAMB p1, LAMB p2) => cpl_compare compare_exact compare_exact (p1,p2)

fun enc_feavl feavl =
  let
    val empty_exact = HOLset.empty compare_exact
    fun goal_terms ((asl,w),A) = HOLset.addList(A, w::asl)
    fun feav_terms (((stac,t,g,gl), fea), A) =
        List.foldl goal_terms A (g::gl)
    val all_terms = List.foldl feav_terms empty_exact feavl |> HOLset.listItems
    val ed = {named_terms = [], unnamed_terms = [], named_types = [],
              unnamed_types = [], theorems = []}
    val sdi = build_sharing_data ed
    val sdi = add_terms all_terms sdi
    fun write_term_aux sdi t = write_term sdi t 
      handle NotFound => raise ERR "write_term" (term_to_string t)
    val enc_feavldata = list_encode (enc_feav (String o write_term_aux sdi))
  in
    tagged_encode "feavl" (pair_encode(enc_sdata, enc_feavldata)) (sdi,feavl)
  end

fun dec_feavl t =
    let
      val a = {with_strings = fn _ => (), with_stridty = fn _ => ()}
      val (sdo, feav_data) =
          valOf (tagged_decode "feavl" (pair_decode(dec_sdata a, SOME)) t)
      val dec_tm = Option.map (read_term sdo) o string_decode
    in
      list_decode (dec_feav dec_tm) feav_data
    end

fun export_tacfea file tacfea =
  let
    val ostrm = Portable.open_out file
    fun is_local s = mem "tttRecord.local_tag" (partial_sml_lexer s)
    fun is_global feav = not (is_local (#1 (fst feav)))
    val feavl1 = filter is_global (dlist tacfea)
    val feavl2 = filter uptodate_feav feavl1
  in
    PP.prettyPrint (curry TextIO.output ostrm, 75)
                   (HOLsexp.printer (enc_feavl feavl2));
    TextIO.closeOut ostrm
  end

(* -------------------------------------------------------------------------
   Importing terms
   ------------------------------------------------------------------------- *)

fun import_terml file =
  let
    val t = HOLsexp.fromFile file
    val sdo = valOf (dec_sdata {with_strings = fn _ => (),
                                with_stridty = fn _ => ()} t)
  in
    #unnamed_terms (export_from_sharing_data sdo)
  end

(* -------------------------------------------------------------------------
   Importing tactic data
   ------------------------------------------------------------------------- *)

(* Feature vector *)
(*  val file = ttt_tacfea_dir ^ "/" ^ thy *)

fun import_tacfea file =
    let
      val t = HOLsexp.fromFile file
      val feavl = valOf (dec_feavl t)
    in
      dnew lbl_compare feavl
    end

(*
fun read_tacfea_thy thy =
  if mem thy ["min","bool"] then [] else read_feavdatal thy
*)

(* -------------------------------------------------------------------------
   Tactic data is recovered from tacfea
   ------------------------------------------------------------------------- *)

fun init_taccov tacfea =
  count_dict (dempty String.compare) (map (#1 o fst) (dlist tacfea))

fun update_tacdep (lbl,tacdep) =
  let
    val oldv = dfind (#3 lbl) tacdep handle NotFound => []
    val newv = lbl :: oldv
  in
    dadd (#3 lbl) newv tacdep
  end

fun init_tacdep tacfea =
  foldl update_tacdep (dempty goal_compare) (dkeys tacfea)

fun init_tacdata tacfea =
  {
  tacfea      = tacfea,
  tacfea_cthy = dempty lbl_compare,
  tacdep      = init_tacdep tacfea,
  taccov      = init_taccov tacfea
  }

fun import_tacdata filel =
  let val tacfea = union_dict lbl_compare (map import_tacfea filel) in
    init_tacdata tacfea
  end

(* -------------------------------------------------------------------------
   Tactictoe database management
   ------------------------------------------------------------------------- *)

val ttt_tacdata_dir = HOLDIR ^ "/src/tactictoe/ttt_tacdata"

fun exists_tacdata_thy thy = 
  let val file = ttt_tacdata_dir ^ "/" ^ thy in
    exists_file file andalso (not o null o readl) file
  end

fun ttt_create_tacdata () =
  let
    fun test file = exists_file file andalso (not o null o readl) file
    val thyl = ancestry (current_theory ())
    fun f x = ttt_tacdata_dir ^ "/" ^ x
    val filel = filter test (map f thyl)
    val thyl1 = map OS.Path.file filel
    val thyl2 = list_diff thyl thyl1
    val thyl3 = filter (fn x => not (mem x ["bool","min"])) thyl2
    val _ = if null thyl3 then () else print_endline
      ("Missing tactic data for theories: " ^  String.concatWith " " thyl3)
    val tacdata = import_tacdata filel
  in
    print_endline ("Loading " ^ its (dlength (#tacfea tacdata)) ^ " tactics");
    tacdata
  end

fun ttt_update_tacdata_aux {tacfea, tacfea_cthy, taccov, tacdep} (lbl,fea) =
  {
  tacfea      = dadd lbl fea tacfea,
  tacfea_cthy = dadd lbl fea tacfea_cthy,
  tacdep      = update_tacdep (lbl,tacdep),
  taccov      = count_dict taccov [#1 lbl]
  }

fun ttt_update_tacdata (lbl as (stac,t,g,gl), tacdata) =
  if op_mem goal_eq g gl orelse dmem lbl (#tacfea tacdata)
  then tacdata
  else ttt_update_tacdata_aux tacdata (lbl, feahash_of_goal g)

fun ttt_export_tacdata thy tacdata =
  let
    val _ = mkDir_err ttt_tacdata_dir
    val file = ttt_tacdata_dir ^ "/" ^ thy
  in
    print_endline file;
    export_tacfea file (#tacfea tacdata)
  end



end (* struct *)
