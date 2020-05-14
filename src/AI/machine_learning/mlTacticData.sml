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
   Tactictoe database data type
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

fun export_goal file (goal as (asl,w)) = export_terml file (w :: asl)

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

fun enc_feavl feavl =
  let
    val empty_exact = HOLset.empty term_compare_exact
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

fun import_goal file = let val l = import_terml file in (tl l, hd l) end

(* -------------------------------------------------------------------------
   Importing tactic data
   ------------------------------------------------------------------------- *)

fun import_tacfea file =
    let
      val t = HOLsexp.fromFile file
      val feavl = valOf (dec_feavl t)
    in
      dnew lbl_compare feavl
    end

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
  let
    val (l,t1) = add_time (map import_tacfea) filel
    val (tacfea,t2) = add_time (union_dict lbl_compare) l
    val (tacdata,t3) = add_time init_tacdata tacfea
  in
    tacdata
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
    val _ = if null thyl3 then () else
      (
      print_endline ("Missing tactic data: " ^  String.concatWith " " thyl3);
      print_endline "Run tttUnfold.ttt_record ()"
      )
    val _ = print_endline
    val tacdata = import_tacdata filel
  in
    print_endline ("Loading " ^ its (dlength (#tacfea tacdata)) ^
      " tactic calls");
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
    export_tacfea file (#tacfea_cthy tacdata)
  end

(* ------------------------------------------------------------------------
   Exporting search examples
   ------------------------------------------------------------------------ *)

type ex = (goal * string * (goal * goal list) * goal list) * bool

val exl_glob = ref []

(* human readable *)
fun string_of_ex ((ginit, stac, (gcur, ogl), pgl), b) =
  String.concatWith "\n" [
    "####",
    "inital goal: " ^ string_of_goal ginit,
    "tactic: " ^ stac,
    "input goal: " ^ string_of_goal gcur,
    "output goals: " ^
    String.concatWith " **** " (map string_of_goal ogl),
    "pending goals: " ^
    String.concatWith " **** " (map string_of_goal pgl),
    "positive: " ^ bts b
    ]

fun ttt_export_exl_human thy exl =
  let
    val dir = HOLDIR ^ "/src/tactictoe/exhuman"
    val _ = mkDir_err dir
    val file = dir ^ "/" ^ thy
  in
    writel file (map string_of_ex exl)
  end

(* S-expression *)
val enc_bool = String o bts
val dec_bool = Option.map string_to_bool o string_decode

fun enc_ex enc_tm (* ((ginit, stac, (gcur, ogl), pgl), b) *) =
  tagged_encode "ex" (
    pair_encode(
      pair4_encode(
        enc_goal enc_tm,
        String,
        pair_encode (enc_goal enc_tm, enc_goal_list enc_tm),
        enc_goal_list enc_tm
      ),
      enc_bool
    )
  )

fun dec_ex dec_tm =
  tagged_decode "ex" (
    pair_decode(
      pair4_decode (
        dec_goal dec_tm,
        string_decode,
        pair_decode (dec_goal dec_tm, dec_goal_list dec_tm),
        dec_goal_list dec_tm
      ),
      dec_bool
    )
  )

fun enc_exl exl =
  let
    val empty_exact = HOLset.empty term_compare_exact
    fun goal_terms ((asl,w),A) = HOLset.addList(A, w::asl)
    fun ex_terms (((ginit, stac, (gcur, ogl), pgl), b), A) =
        List.foldl goal_terms A (ginit :: gcur :: (ogl @ pgl))
    val all_terms = List.foldl ex_terms empty_exact exl |>
      HOLset.listItems
    val ed = {named_terms = [], unnamed_terms = [], named_types = [],
              unnamed_types = [], theorems = []}
    val sdi = build_sharing_data ed
    val sdi = add_terms all_terms sdi
    fun write_term_aux sdi t = write_term sdi t
      handle NotFound => raise ERR "write_term" (term_to_string t)
    val enc_exldata = list_encode (enc_ex (String o write_term_aux sdi))
  in
    tagged_encode "exl" (pair_encode (enc_sdata, enc_exldata)) (sdi,exl)
  end

fun dec_exl t =
    let
      val a = {with_strings = fn _ => (), with_stridty = fn _ => ()}
      val (sdo, ex_data) =
          valOf (tagged_decode "exl" (pair_decode(dec_sdata a, SOME)) t)
      val dec_tm = Option.map (read_term sdo) o string_decode
    in
      list_decode (dec_ex dec_tm) ex_data
    end

fun uptodate_ex ((ginit, _, (gcur, ogl), pgl), _) =
  all uptodate_goal (ginit :: gcur :: (ogl @ pgl))

fun ttt_export_exl thy exl1 =
  let
    val dir = HOLDIR ^ "/src/tactictoe/exhol"
    val _ = mkDir_err dir
    val file = dir ^ "/" ^ thy
    val ostrm = Portable.open_out file
    val exl2 = filter uptodate_ex exl1
  in
    PP.prettyPrint (curry TextIO.output ostrm, 75)
                   (HOLsexp.printer (enc_exl exl2));
    TextIO.closeOut ostrm
  end

fun ttt_import_exl thy =
  let
    val dir = HOLDIR ^ "/src/tactictoe/exhol"
    val file = dir ^ "/" ^ thy
  in
    valOf (dec_exl (HOLsexp.fromFile file))
  end

(* ------------------------------------------------------------------------
   Preparing search examples for learning with TNN
   ------------------------------------------------------------------------ *)

fun mk_cat2 x =
  list_mk_comb (mk_var ("cat2",``:bool -> bool -> bool``), x)
fun mk_cat3 x =
  list_mk_comb (mk_var ("cat3",``:bool -> bool -> bool -> bool``),x)

fun simplify_ex (ginit,_:string,(gcur,ogl),pgl) =
  mk_cat2 [list_mk_imp ginit,
    if null ogl
    then (list_mk_imp (hd pgl))
    else (list_mk_imp (hd ogl))]
  (*
  mk_cat3 [list_mk_imp ginit, list_mk_imp gcur,
    if null ogl then T else list_mk_conj (map list_mk_imp ogl)] *)

fun lambda_term fullty (v,bod) =
  let
    val ty1 = type_of v
    val ty2 = type_of bod
    val ty3 = mk_type ("fun",[ty1, mk_type ("fun", [ty2,fullty])])
  in
    list_mk_comb (mk_var ("ttt_lambda",ty3), [v,bod])
  end

fun add_lambda tm = case dest_term tm of
    COMB(Rator,Rand) => mk_comb (add_lambda Rator, add_lambda Rand)
  | LAMB(Var,Bod) => lambda_term (type_of tm) (Var, add_lambda Bod)
  | _ => tm

fun add_arity tm =
  let
    val (oper,argl) = strip_comb tm
    val a = length argl
    val newname =
      if is_var oper
      then
        let val prefix = if null argl then "V" else "v" in
          escape (prefix ^ fst (dest_var oper) ^ "." ^ its a)
        end
      else
        let val {Thy,Name,Ty} = dest_thy_const oper in
          escape ("c" ^ Thy ^ "." ^ Name ^ "." ^ its a)
        end
    val newoper = mk_var (newname, type_of oper)
  in
    list_mk_comb (newoper, map add_arity argl)
  end

fun not_null ((ginit,_:string,(gcur,ogl),pgl), _) =
  not (null ogl) orelse not (null pgl)

fun prepare_exl exl1 =
  let
    val exl1' = filter not_null exl1
    val exl2 = map (fn (a,b) => (simplify_ex a, b)) exl1'
    val exl3 = map_fst (add_arity o add_lambda) exl2
    val exl4 = map_snd (fn x => if x then [1.0] else [0.0]) exl3
    val vhead = mk_var ("head_", ``:bool -> bool``)
    val exl5 = map (fn (a,b) => [(mk_comb (vhead,a),b)]) exl4
  in
    exl5
  end

(* ------------------------------------------------------------------------
   Exporting examples to TPTP
   ------------------------------------------------------------------------ *)

fun is_singleton x = case x of [a] => true | _ => false

fun simp_tptp ((ginit,_:string,(gcur,ogl),pgl),b) =
  let
    val f = (add_arity o add_lambda)
    val tm = if null ogl then (list_mk_imp (hd pgl))
                         else (list_mk_imp (hd ogl))
  in
    (f (list_mk_imp ginit),(f tm,b))
  end

fun tptp_of_term tm =
  let
    val (oper,argl) = strip_comb tm
    val name = fst (dest_var oper)
  in
    if null argl then name else
    name ^ "(" ^ String.concatWith ", " (map tptp_of_term argl) ^ ")"
  end

fun export_tptpex termndict thy (cj,axl) =
  let
    val dir = HOLDIR ^ "/src/tactictoe/extptp"
    val _ = mkDir_err dir
    val cjname = thy ^ its (dfind cj termndict)
    val file = dir ^ "/" ^ cjname
    fun f (ax,b) =
      let
        val axname = thy ^ its (dfind ax termndict)
        val role = if b then "axiom_useful" else "axiom_redundant"
      in
        "fof(" ^ axname ^ "," ^ role ^ "," ^ tptp_of_term ax ^ ")."
      end
    fun g cj = "fof(" ^ cjname ^ ",conjecture," ^ tptp_of_term cj ^ ")."
  in
    writel file (g cj :: map f axl)
  end

fun ttt_export_tptpexl thy exl =
  let
    val exl' = filter not_null exl
    val tptpl1 = map simp_tptp exl'
    val tptpl2 = dlist (dregroup Term.compare tptpl1)
    val tptpl3 = filter (not o is_singleton o snd) tptpl2
    val terml1 = List.concat (map (fn (t1,t2l) => t1 :: map fst t2l) tptpl3)
    val terml2 = mk_term_set terml1
    val termndict = dnew Term.compare (number_snd 0 terml2)
  in
    app (export_tptpex termndict thy) tptpl3
  end

(*
load "aiLib"; open aiLib;
load "mlTacticData"; open mlTacticData;
val thyl = ancestry (current_theory ());
(*
fun g thy = ttt_export_tptpexl thy (ttt_import_exl thy)
   handle _ => print_endline thy;
app g thyl;
*)

fun f thy = ttt_import_exl thy handle _ => (print_endline thy; []);
val exl = List.concat (map f thyl);
val exl2 = prepare_exl exl;
val (train,test) = swap (part_n 1000 (shuffle exl2));

load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
val operl = mk_fast_set oper_compare
  (List.concat (map operl_of_term (map fst (List.concat exl2))));
val operdiml = map (fn x => (fst x, dim_std_arity (1,12) x)) operl;
val randtnn = random_tnn operdiml;

val trainparam =
  {ncore = 8, verbose = true,
   learning_rate = 0.04, batch_size = 16, nepoch = 100};
val schedule = [trainparam];
val tnn = train_tnn schedule randtnn (train,test);

val acctrain = tnn_accuracy tnn train;
val acctest = tnn_accuracy tnn test;
val _ = write_tnn "tnn_hd" tnn;

*)
end (* struct *)
