(*-------------------------------------------------------------------------- 
  Preparing files for the predictor
  the current_theory is always reexported under current_theory.fea
  -------------------------------------------------------------------------- *)

structure hhsPredict :> hhsPredict =
struct

open HolKernel Abbrev hhsTools hhsLog

val ERR = mk_HOL_ERR "hhsPredict"

val hhs_nolengthpen_flag = ref false



(* ----------------------------------------------------------------------
   TFIDF (symbols weight in a corpus)
   ---------------------------------------------------------------------- *)

fun learn_tfidf feal = 
  let
    val syms      = List.concat (map snd feal)
    val dict      = count_dict (dempty String.compare) syms
    val n         = length feal
    fun f (fea,freq) = 
      Math.ln (Real.fromInt n) - Math.ln (Real.fromInt freq)
  in
    Redblackmap.map f dict
  end

fun fast_learn_tfidf n dict fea = 
  let
    val new_dict  = count_dict dict fea
    fun f (_,freq) = 
      Math.ln (Real.fromInt n) - Math.ln (Real.fromInt freq)
  in
    Redblackmap.map f new_dict
  end

(*
fun mk_list n a = List.tabulate (n, fn _ => a);

val l1 = mk_list 1000 (); 
fun f () = mk_list 1000 1;
val l2 = map f l1;
val l3 = time List.concat l2;

val l4 = time fast_concat l2;

fun fast_concat l = case l of
    [] => []
  | a :: m => a @ fast_concat m
*)



(* ----------------------------------------------------------------------
   Scoring functions
   ---------------------------------------------------------------------- *)

fun inter_dict dict l =
  filter (fn x => dmem x dict) l

fun pow6_dist l = case l of 
    []     => 0.0
  | a :: m => Math.pow (a,6.0) + pow6_dist m

(* doesn't change the order now *)
fun first_n_diff n dict acc l =
  if null l orelse n <= 0
  then rev acc
  else 
    let val (a,m) = (hd l,tl l) in
      if dmem a dict
      then first_n_diff n dict acc m
      else first_n_diff (n - 1) (dadd a () dict) (a :: acc) m
    end

(* ----------------------------------------------------------------------
   KNN distance
   ---------------------------------------------------------------------- *)

fun knn_self_distance nfstfea symweight fea =
  let 
    val n       = Real.fromInt (length fea + length fea)
    val denom   = 1.0 + Math.ln (1.0 + n)
    fun wf s    = dfind s symweight handle _ => Math.ln (Real.fromInt nfstfea)
    val weightl = map wf fea
  in
    if !hhs_nolengthpen_flag
    then pow6_dist weightl
    else pow6_dist weightl / denom
  end

fun knn_distance symweight dict_o fea_p =
  let 
    val fea     = inter_dict dict_o fea_p
    val n       = Real.fromInt (length fea_p + Redblackmap.numItems dict_o)
    val denom   = 1.0 + Math.ln (1.0 + n)
    fun wf s    = dfind s symweight handle _ => raise ERR "knn_distance" s
    val weightl = map wf fea
  in
    if !hhs_nolengthpen_flag
    then pow6_dist weightl
    else pow6_dist weightl / denom
  end

(* ----------------------------------------------------------------------
   KNN predictor
   ---------------------------------------------------------------------- *)

(* sort feature vectors *)
fun knn_sort symweight feal fea_o =
  let 
    val dict_o = 
      Redblackmap.fromList String.compare (map (fn x => (x,())) fea_o)
    fun dist (lbl,fea_p) = ((lbl,fea_p), knn_distance symweight dict_o fea_p)
    fun compare ((_,x),(_,y)) = Real.compare (y,x)
    val l0 = map dist feal
  in
    map fst (dict_sort compare l0)
  end

fun knn_shark stac k symweight feal fea_o =
  let 
    val dict_o = 
      Redblackmap.fromList String.compare (map (fn x => (x,())) fea_o)
    fun dist (lbl,fea_p) = (lbl, knn_distance symweight dict_o fea_p)
    fun compare1 ((_,x),(_,y)) = Real.compare (y,x)
    val l0 = map dist feal
    val l1 = map fst (first_n k (dict_sort compare1 l0))
    val l2 = if mem stac l1 then l1 else stac :: l1
    val dict = count_dict (dempty String.compare) l2
    fun compare2 (s1,s2) = Int.compare (dfind s2 dict,dfind s1 dict)
  in
    dict_sort compare2 l2
  end

(* returns predictions with scores *)    
fun knn_score symweight n_adv feal fea_o =
  let 
    val dict_o = 
      Redblackmap.fromList String.compare (map (fn x => (x,())) fea_o)
    fun dist (lbl,fea_p) = (lbl, knn_distance symweight dict_o fea_p)
    fun compare0 ((_,x),(_,y)) = Real.compare (y,x)
    val l0 = map dist feal
    val l1 = dict_sort compare0 l0
    fun compare1 ((s1,_),(s2,_)) = String.compare (s1,s2)
  in
    first_n_diff n_adv (dempty compare1) [] l1
  end

fun knn symweight n_adv feal fea_o =
  map fst (knn_score symweight n_adv feal fea_o)

(*
fun knn_aux symweight n_adv feal fea_o =
  let 
    val dict_o = 
      Redblackmap.fromList String.compare (map (fn x => (x,())) fea_o)
    fun dist (lbl,fea_p) = (lbl, knn_distance symweight dict_o fea_p)
    fun compare ((_,x),(_,y)) = Real.compare (y,x)
    val l0 = map dist feal
    val l1 = dict_sort compare l0
  in
    first_n n_adv (dempty String.compare) (map fst l1)
  end

fun full_knn_aux n_adv feal fea_o =
  knn_aux (learn_tfidf feal) n_adv feal fea_o
*)

(* ----------------------------------------------------------------------
   Renaming objects, preparing for export
   ---------------------------------------------------------------------- *)
val feaname_counter = ref 0
val feaname_dict    = ref (dempty String.compare)
val thmname_counter = ref 0
val stac_counter    = ref 0
val stac_dict       = ref (dempty String.compare)
val unstac_dict     = ref (dempty String.compare)

fun name_fea fea = 
  dfind fea (!feaname_dict) 
  handle _ =>
    let 
      val named_fea = mlquote (int_to_string (!feaname_counter))
    in
      feaname_dict := dadd fea named_fea (!feaname_dict);
      feaname_counter := (!feaname_counter) + 1;
      named_fea
    end

fun name_stac stac =
  dfind stac (!stac_dict) 
  handle _ =>
  let 
    val named_stac = ("s" ^ int_to_string (!stac_counter))
  in 
    stac_dict    := dadd stac named_stac (!stac_dict);
    unstac_dict  := dadd named_stac stac (!unstac_dict);
    stac_counter := (!stac_counter) + 1;
    named_stac
  end

(* give different names to theorems of the same name *)
fun name_thm thm =
  let 
    val named_thm = ("t" ^ int_to_string (!thmname_counter))
  in 
    thmname_counter := (!thmname_counter) + 1;
    named_thm
  end

(*-------------------------------------------------------------------------- 
  External predictions
  -------------------------------------------------------------------------- *)


fun print_dep fname all_stac thmfeal_renamed =
  let
    val oc    = TextIO.openOut fname
    fun os s  = TextIO.output (oc,s)
    fun f stac = os (stac ^ ":\n")
    fun g (thm,_,stacl) = os (thm ^ ":" ^ String.concatWith " " stacl ^ "\n")
  in
    app f all_stac;
    app g thmfeal_renamed;
    TextIO.closeOut oc
  end

fun print_seq fname all_stac thmfeal_renamed =
  let
    val oc    = TextIO.openOut fname
    fun os s  = TextIO.output (oc,s)
    fun f stac = os (stac ^ "\n")
    fun g (thm,_,_) = os (thm ^ "\n")
  in
    app f all_stac;
    app g thmfeal_renamed;
    TextIO.closeOut oc
  end

fun print_csyms fname csyms =
  let  
    val oc    = TextIO.openOut fname
    fun os s  = TextIO.output (oc,s)
  in
    os (String.concatWith ", " csyms);
    os "\n";
    TextIO.closeOut oc
  end

fun print_syms fname all_stac thmfeal_renamed =
  let 
    val oc   = TextIO.openOut fname  
    fun os s = TextIO.output (oc,s)
    fun f stac = os (stac ^ ":\"stac\"\n")
    fun g (thm,fea,_) = os (thm ^ ":" ^ String.concatWith ", " fea ^ "\n")
  in
    app f all_stac;
    app g thmfeal_renamed;
    TextIO.closeOut oc
  end

fun export_knn dir thmfeal feag =
  let
    fun rename (thm,fea,stacl) = 
      (name_thm thm, map name_fea fea, map name_stac stacl)
    val thmfeal_renamed = map rename thmfeal
    val all_stac =
      let val l = List.concat (map (fn (_,_,z) => z) thmfeal_renamed) in
        mk_fast_set String.compare l
      end
    val feag_renamed = map name_fea feag
  in
    print_dep (dir ^ "/dep") all_stac thmfeal_renamed;
    print_seq (dir ^ "/seq") all_stac thmfeal_renamed;
    print_csyms (dir ^ "/csyms") feag_renamed;
    print_syms (dir ^ "/syms") all_stac thmfeal_renamed
  end

(*-------------------------------------------------------------------------- 
  External binary predictors
  -------------------------------------------------------------------------- *)

fun cmd_in_dir dir cmd =
  OS.Process.system ("cd " ^ dir ^ "; " ^ cmd)
 
fun bin_predict n predictor =
  let
    val predict_cmd =
      "../../holyhammer/predict/predict" ^ 
      " syms dep seq -n" ^
      " " ^ int_to_string n ^ 
      " -p " ^ predictor ^
      " < csyms" ^
      " > predict_out" ^
      " 2> predict_error"
  in
    cmd_in_dir hhs_predict_dir predict_cmd
  end

(*-------------------------------------------------------------------------- 
  Reading predictions 
  need to predict more than the number of theorems to start predicting 
  tactics
  -------------------------------------------------------------------------- *)

fun read_predictions n = 
  let 
    val s = hd (readl (hhs_predict_dir ^ "/predict_out"))
      handle _ => raise ERR "read_predictions" ""
    val sl = String.tokens Char.isSpace s
    fun unname_stac s = 
      if hd (explode s) = #"t"
      then NONE
      else SOME (dfind s (!unstac_dict))
  in
    first_n n (List.mapPartial unname_stac sl)
  end

(*-------------------------------------------------------------------------- 
  External tactic predictions
  -------------------------------------------------------------------------- *)

fun knn_ext n thmfeal feag =
  if thmfeal = [] then []
  else
    (
    thmname_counter := 0;
    feaname_counter := 0;
    feaname_dict    := dempty String.compare;
    stac_counter    := 0;
    stac_dict       := dempty String.compare;
    unstac_dict     := dempty String.compare;
    export_knn hhs_predict_dir thmfeal feag;
    bin_predict (4*n) "knn"; (* should remove theorem with no dependencies
                                and then call it on 2*n only *)
    read_predictions n
    )

(* ----------------------------------------------------------------------
   Renaming thms objects, preparing for export
   ---------------------------------------------------------------------- *)

val thm_counter    = ref 0
val thm_dict       = ref (dempty String.compare)
val unthm_dict     = ref (dempty String.compare)

fun tname_thm thm =
  dfind thm (!thm_dict) 
  handle _ =>
  let 
    val named_thm = ("t" ^ int_to_string (!thm_counter))
  in 
    thm_dict    := dadd thm named_thm (!thm_dict);
    unthm_dict  := dadd named_thm thm (!unthm_dict);
    thm_counter := (!thm_counter) + 1;
    named_thm
  end

(*-------------------------------------------------------------------------- 
  External predictions
  -------------------------------------------------------------------------- *)

fun tprint_dep fname thmfeal_renamed =
  let
    val oc    = TextIO.openOut fname
    fun os s  = TextIO.output (oc,s)
    fun g (thm,_,dep) = os (thm ^ ":" ^ String.concatWith " " dep ^ "\n")
  in
    app g thmfeal_renamed;
    TextIO.closeOut oc
  end

fun tprint_seq fname thmfeal_renamed =
  let
    val oc    = TextIO.openOut fname
    fun os s  = TextIO.output (oc,s)
    fun g (thm,_,_) = os (thm ^ "\n")
  in
    app g thmfeal_renamed;
    TextIO.closeOut oc
  end

fun tprint_csyms fname csyms =
  let  
    val oc    = TextIO.openOut fname
    fun os s  = TextIO.output (oc,s)
  in
    os (String.concatWith ", " csyms);
    os "\n";
    TextIO.closeOut oc
  end

fun tprint_syms fname thmfeal_renamed =
  let 
    val oc   = TextIO.openOut fname  
    fun os s = TextIO.output (oc,s)
    fun g (thm,fea,_) = os (thm ^ ":" ^ String.concatWith ", " fea ^ "\n")
  in
    app g thmfeal_renamed;
    TextIO.closeOut oc
  end

fun texport_knn dir thmfeal feag =
  let
    fun rename (thm,fea,dep) = 
      (tname_thm thm, map name_fea fea, map tname_thm dep)
    val thmfeal_renamed = map rename thmfeal
    val feag_renamed = map name_fea feag
  in
    tprint_dep (dir ^ "/dep") thmfeal_renamed;
    tprint_seq (dir ^ "/seq") thmfeal_renamed;
    tprint_csyms (dir ^ "/csyms") feag_renamed;
    tprint_syms (dir ^ "/syms") thmfeal_renamed
  end

(*-------------------------------------------------------------------------- 
  Reading thm predictions
  -------------------------------------------------------------------------- *)

fun tread_predictions () = 
  let 
    val s = hd (readl (hhs_predict_dir ^ "/predict_out"))
      handle _ => raise ERR "read_predictions" ""
    val sl = String.tokens Char.isSpace s
    fun unname_thm s = dfind s (!unthm_dict)
  in
    map unname_thm sl
  end

(*-------------------------------------------------------------------------- 
  External thm predictions
  -------------------------------------------------------------------------- *)

fun tknn_ext n thmfeal feag =
  if thmfeal = [] then []
  else
    (
    feaname_counter := 0;
    feaname_dict    := dempty String.compare;
    thm_counter    := 0;
    thm_dict       := dempty String.compare;
    unthm_dict     := dempty String.compare;
    texport_knn hhs_predict_dir thmfeal feag;
    bin_predict n "knn";
    tread_predictions ()
    )

end (* struct *)

(*-------------------------------------------------------------------------- 
  change the recording to add time and 
  a preselection of 1000 tactics based on the secondary features
    

  plan make the reproving until ...
  with the new predictors


  load "hhPredict";
  val tm = ``20+10=30``;
  val feal = all_fea ();
  val fea = feature_of tm;
  val symweight = learn_tfidf feal;
  val n_adv = 128;
  val predl = time (knn symweight feal n_adv) fea;
  val predl2 = map split_thmstring predl;  

  val predthml = map fetch_thmstring predl;

  METIS_PROVE predthml tm;
  holyHammer.hh_wo_pred predl2 holyHammer.Eprover [] tm;

  val l = time (hh_predict 128 "knn") tm;
  val l = time (hh_predict 128 "mepo") tm;

val l = time (hh_predict_overhead 1 "knn") tm;

  val l1 = map (fn (a,b) => DB.fetch a b) l;
  load "holyHammer";
  open holyHammer;
  hh_wo_pred l Eprover [] tm;

  fun first_n n l =
  if n <= 0 orelse l = [] then [] else (hd l) :: first_n (n - 1) (tl l)

  fun rm_last_n_string n s =
    let 
      val l = explode s
      val m = length l
    in
      implode (first_n (m - n) l)
    end

  fun thyname_of_scriptpath file_in =
    let 
      val scriptext = last (String.tokens (fn x => x = #"/") file_in)
      val (script,ext) = 
        pair_of_list (String.tokens (fn x => x = #".") scriptext)
    in 
      rm_last_n_string 6 script  
    end

  val l = readl "strategy/script_list";
  val thyl = map thyname_of_scriptpath l;
  val thyl1 = map (fn x => x ^ "Theory") thyl;

  val errl : string list ref = ref []
  fun load_err s = load s handle _ => errl := s :: (!errl)
  fun f_err f s = f s handle _ => errl := s :: (!errl)


  app load_err thyl1;
  errl := [];
  time (app (f_err pfea_of_thy)) thyl;
  
(* feature should be sets *)
(* it's actually a codistance 
val inter_time = ref 0.0
val pow6_time = ref 0.0
val dfind_time = ref 0.0
*)

  
  -------------------------------------------------------------------------- *)







