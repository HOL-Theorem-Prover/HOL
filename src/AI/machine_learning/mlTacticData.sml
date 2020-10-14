(* ========================================================================= *)
(* FILE          : mlTacticData.sml                                          *)
(* DESCRIPTION   : Tactic calls from TacticToe recording                     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlTacticData :> mlTacticData =
struct

open HolKernel boolLib Abbrev aiLib smlLexer mlFeature

val ERR = mk_HOL_ERR "mlTacticData"

(* -------------------------------------------------------------------------
   Tactictoe database data type
   ------------------------------------------------------------------------- *)

type stac = string
type loc = string * int * int
type call = {stac : stac, ogl : int list, fea : fea}

val loc_compare = triple_compare String.compare Int.compare Int.compare
fun call_compare (c1,c2) =
  cpl_compare String.compare fea_compare
    ((#stac c1,#fea c1),(#stac c2,#fea c2))

type tacdata =
  {
  calld : (string * int * int, call) Redblackmap.dict,
  taccov : (stac,int) Redblackmap.dict,
  symfreq : (int,int) Redblackmap.dict
  }

val empty_tacdata : tacdata =
  {
  calld = dempty loc_compare,
  taccov = dempty String.compare,
  symfreq = dempty Int.compare
  }

(* -------------------------------------------------------------------------
   Exporting tactic data
   ------------------------------------------------------------------------- *)

fun loc_to_string (s,i1,i2) =
  String.concatWith " " [s, its i1, its i2]

fun ilts il = String.concatWith " " (map its il)

fun call_to_string (loc,{stac,ogl,fea}) =
  [loc_to_string loc, stac, ilts ogl, ilts fea]

fun export_calls file calls1 =
  let
    fun is_local stac = mem "tttRecord.local_tag" (partial_sml_lexer stac)
    fun test call = not (is_local (#stac call))
    val calls2 = filter (test o snd) calls1
    val _ = debug ("export_calls: " ^ its (length calls2) ^ " filtered calls")
  in
    writel file (List.concat (map call_to_string calls2))
  end

fun export_tacdata thy file tacdata =
  let
    fun test (x,_,_) = (x = thy)
    val calls = filter (test o fst) (dlist (#calld tacdata))
  in
    print_endline ("Exporting tactic data to: " ^ file);
    export_calls file calls
  end

(* -------------------------------------------------------------------------
   Importing tactic data
   ------------------------------------------------------------------------- *)

fun loc_from_string s =
  let val (a,b,c) = triple_of_list (String.tokens Char.isSpace s) in
    (a, string_to_int b, string_to_int c)
  end

fun string_to_il s = map string_to_int (String.tokens Char.isSpace s)

fun call_from_string (s1,s2,s3,s4) =
  (loc_from_string s1,
   {stac = s2, ogl = string_to_il s3, fea = string_to_il s4})

fun import_calls file =
  let val l = mk_batch_full 4 (readl_empty file) in
    map (call_from_string o quadruple_of_list) l
  end

fun init_taccov calls =
  count_dict (dempty String.compare) (map (#stac o snd) calls)

fun init_symfreq calls =
  count_dict (dempty Int.compare) (List.concat (map (#fea o snd) calls))

fun init_tacdata calls =
  {
  calld = dnew loc_compare calls,
  taccov = init_taccov calls,
  symfreq = init_symfreq calls
  }

fun import_tacdata filel =
  let val calls = List.concat (map import_calls filel) in
    init_tacdata calls
  end

(* -------------------------------------------------------------------------
   Tactictoe database management
   ------------------------------------------------------------------------- *)

val ttt_tacdata_dir = HOLDIR ^ "/src/tactictoe/ttt_tacdata"

fun exists_tacdata_thy thy =
  exists_file (ttt_tacdata_dir ^ "/" ^ thy)

fun create_tacdata () =
  let
    fun test file = exists_file file
    val thyl = ancestry (current_theory ())
    fun f x = ttt_tacdata_dir ^ "/" ^ x
    val filel = filter test (map f thyl)
    val thyl1 = map OS.Path.file filel
    val thyl2 = list_diff thyl thyl1
    val thyl3 = filter (fn x => not (mem x ["bool","min"])) thyl2
    val _ = if null thyl3 then () else
      (
      print_endline ("Missing tactic data: " ^  String.concatWith " " thyl3);
      print_endline "Run tttUnfold.ttt_record ()"
      )
    val tacdata = import_tacdata filel
    val calln = dlength (#calld tacdata)
  in
    print_endline ("Loading " ^ its calln ^ " tactic calls");
    tacdata
  end

fun ttt_update_tacdata ((loc,call),{calld,taccov,symfreq}) =
  {
  calld = dadd loc call calld,
  taccov = count_dict taccov [#stac call],
  symfreq = count_dict symfreq (#fea call)
  }

fun ttt_export_tacdata thy tacdata =
  let
    val _ = mkDir_err ttt_tacdata_dir
    val file = ttt_tacdata_dir ^ "/" ^ thy
  in
    export_tacdata thy file tacdata
  end


end (* struct *)
