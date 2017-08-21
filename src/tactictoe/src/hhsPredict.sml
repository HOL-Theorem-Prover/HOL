(* =========================================================================  *)
(* FILE          : hhsPredictor.sml                                           *)
(* DESCRIPTION   : Tactic and theorem selections through external calls to    *)
(* machine learning programs                                                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsPredict :> hhsPredict =
struct

open HolKernel Abbrev hhsTools hhsTools

val ERR = mk_HOL_ERR "hhsPredict"

(* -------------------------------------------------------------------------- 
   TFIDF: weight of symbols                                     
   -------------------------------------------------------------------------- *)

fun learn_tfidf feavl = 
  let
    val syms      = List.concat (map snd feavl)
    val dict      = count_dict (dempty String.compare) syms
    val n         = length feavl
    fun f (fea,freq) = 
      Math.ln (Real.fromInt n) - Math.ln (Real.fromInt freq)
  in
    Redblackmap.map f dict
  end

(* -------------------------------------------------------------------------- 
   Scoring                                                                    
   -------------------------------------------------------------------------- *)

fun inter_dict dict l =
  filter (fn x => dmem x dict) l

fun pow6_dist l = case l of 
    []     => 0.0
  | a :: m => Math.pow (a,6.0) + pow6_dist m

fun taclbl_of ((a,_,_,_),_) = a

(* --------------------------------------------------------------------------
   KNN distance
   -------------------------------------------------------------------------- *)

fun knn_self_distance symweight fea =
  let
    fun wf s    = dfind s symweight handle _ => 0.0
    val weightl = map wf fea
  in
    pow6_dist weightl
  end

fun knn_distance symweight dict_o fea_p =
  let 
    val fea     = inter_dict dict_o fea_p
    fun wf s    = dfind s symweight 
      handle _ => raise ERR "knn_distance" s
    val weightl = map wf fea
  in
    pow6_dist weightl
  end

(* --------------------------------------------------------------------------
   Internal predictions
   -------------------------------------------------------------------------- *)

(* A label can be predicted multiple times *)
fun pre_knn symweight feal fea_o =
  let 
    val dict_o = dnew String.compare (map (fn x => (x,())) fea_o)
    fun dist (lbl,fea_p) = (lbl, knn_distance symweight dict_o fea_p)
    fun compare0 ((_,x),(_,y)) = Real.compare (y,x)
    val l0 = map dist feal
    val l1 = dict_sort compare0 l0
    val memdict = dempty String.compare
  in
    l1
  end

(* returns sorted labels with scores *)    
fun stacknn symweight n feal fea_o =
  let 
    val l1 = pre_knn symweight feal fea_o
    fun compare ((lbl1,_),(lbl2,_)) = String.compare (#1 lbl1,#1 lbl2)
    val l2 = mk_sameorder_set compare l1
  in
    first_n n l2
  end

fun thmknn symweight n feal fea_o =
  let 
    val l1 = pre_knn symweight feal fea_o
    fun compare ((lbl1,_),(lbl2,_)) = String.compare (lbl1,lbl2)
    val l2 = mk_sameorder_set compare l1
  in
    first_n n l2
  end    


(* --------------------------------------------------------------------------
   External executables
   -------------------------------------------------------------------------- *)

fun cmd_in_dir dir cmd =
  OS.Process.system ("cd " ^ dir ^ "; " ^ cmd)
 
fun bin_predict n predictor =
  let
    val predict_dir = HOLDIR ^ "/src/holyhammer/predict" 
    val predict_cmd = String.concatWith " "
      [predict_dir ^ "/predict",
      "syms","dep","seq","-n",int_to_string n,"-p",predictor,
      "<","csyms",">","predict_out","2> predict_error"]
  in
    cmd_in_dir hhs_predict_dir predict_cmd
  end

fun mepo_predict n predictor =
  let
    val predict_dir = HOLDIR ^ "/src/holyhammer/predict" 
    val predict_cmd = String.concatWith " "
      [predict_dir ^ "/mepo/mepo3","0","syms","dep",int_to_string n,"seq",
       "<","csyms",">","predict_out","2> predict_error"]
  in
    cmd_in_dir hhs_predict_dir predict_cmd
  end

(* --------------------------------------------------------------------------
   External tactic predictions
   -------------------------------------------------------------------------- *)

(* Renaming label and features *)
val fea_counter = ref 0
val fea_dict    = ref (dempty String.compare)

fun name_fea fea = 
  dfind fea (!fea_dict) 
  handle _ =>
    let 
      val named_fea = mlquote (int_to_string (!fea_counter))
    in
      fea_dict := dadd fea named_fea (!fea_dict);
      incr fea_counter;
      named_fea
    end

val feav_counter = ref 0
val feav_dict    = ref (dempty feav_compare)
val ifeav_dict   = ref (dempty String.compare)

fun name_feav feav = 
  dfind feav (!feav_dict) 
  handle _ =>
    let 
      val named_feav = "l" ^ int_to_string (!feav_counter)
    in
      feav_dict := dadd feav named_feav (!feav_dict);
      ifeav_dict := dadd named_feav feav (!ifeav_dict);
      incr feav_counter;
      named_feav
    end

fun print_dep fname feavl =
  let
    val oc    = TextIO.openOut fname
    fun os s  = TextIO.output (oc,s)
    fun f (lbl,_) = os (lbl ^ ":" ^ "\n")
  in
    app f feavl;
    TextIO.closeOut oc
  end

fun print_seq fname feavl =
  let
    val oc    = TextIO.openOut fname
    fun os s  = TextIO.output (oc,s)
    fun f (lbl,_) = os (lbl ^ "\n")
  in
    app f feavl;
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

fun print_syms fname feavl =
  let 
    val oc   = TextIO.openOut fname  
    fun os s = TextIO.output (oc,s)
    fun g (thm,fea) = os (thm ^ ":" ^ String.concatWith ", " fea ^ "\n")
  in
    app g feavl;
    TextIO.closeOut oc
  end

fun export_knn dir stacfea feag =
  let
    fun rename (lbl,fea) = (name_feav (lbl,fea), map name_fea fea)
    val feavl = map rename stacfea
    val csyms = map name_fea feag
  in
    print_dep (dir ^ "/dep") feavl;
    print_seq (dir ^ "/seq") feavl;
    print_csyms (dir ^ "/csyms") csyms;
    print_syms (dir ^ "/syms") feavl
  end

fun read_predictions () = 
  let 
    val s = hd (readl (hhs_predict_dir ^ "/predict_out"))
      handle _ => raise ERR "read_predictions" ""
    val sl = String.tokens Char.isSpace s
    fun unname_feav s = dfind s (!ifeav_dict)
  in
    map unname_feav sl
  end

fun stacknn_ext n stacfea feag =
  if null stacfea then []
  else
    (
    fea_counter := 0;
    fea_dict    := dempty String.compare;
    feav_counter := 0;
    feav_dict    := dempty feav_compare;
    ifeav_dict   := dempty String.compare;
    export_knn hhs_predict_dir stacfea feag;
    bin_predict n "knn";
    read_predictions ()
    )

(*--------------------------------------------------------------------------- 
  External theorem predictions
  --------------------------------------------------------------------------- *)

(* Renaming theorems *)
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

fun tprint_dep fname feavl =
  let
    val oc    = TextIO.openOut fname
    fun os s  = TextIO.output (oc,s)
    fun g (thm,_,dep) = os (thm ^ ":" ^ String.concatWith " " dep ^ "\n")
  in
    app g feavl;
    TextIO.closeOut oc
  end

fun tprint_seq fname feavl =
  let
    val oc    = TextIO.openOut fname
    fun os s  = TextIO.output (oc,s)
    fun g (thm,_,_) = os (thm ^ "\n")
  in
    app g feavl;
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

fun tprint_syms fname feavl =
  let 
    val oc   = TextIO.openOut fname  
    fun os s = TextIO.output (oc,s)
    fun g (thm,fea,_) = os (thm ^ ":" ^ String.concatWith ", " fea ^ "\n")
  in
    app g feavl;
    TextIO.closeOut oc
  end

fun texport_knn dir thmfeav feag =
  let
    fun rename (thm,fea,dep) = 
      (tname_thm thm, map name_fea fea, map tname_thm dep)
    val feavl = map rename thmfeav
    val csyms = map name_fea feag
  in
    tprint_dep (dir ^ "/dep") feavl;
    tprint_seq (dir ^ "/seq") feavl;
    tprint_csyms (dir ^ "/csyms") csyms;
    tprint_syms (dir ^ "/syms") feavl
  end

fun tread_predictions () = 
  let 
    val s = hd (readl (hhs_predict_dir ^ "/predict_out"))
      handle _ => raise ERR "read_predictions" ""
    val sl = String.tokens Char.isSpace s
    fun unname_thm s = dfind s (!unthm_dict)
  in
    map unname_thm sl
  end

fun thmknn_ext n thmfeal feag =
  if null thmfeal then [] else
    (
    fea_counter := 0;
    fea_dict    := dempty String.compare;
    thm_counter := 0;
    thm_dict    := dempty String.compare;
    unthm_dict  := dempty String.compare;
    texport_knn hhs_predict_dir thmfeal feag;
    ignore (bin_predict n "knn");
    tread_predictions ()
    )

fun thmmepo_ext n thmfeal feag =
  if null thmfeal then [] else
    (
    fea_counter := 0;
    fea_dict    := dempty String.compare;
    thm_counter := 0;
    thm_dict    := dempty String.compare;
    unthm_dict  := dempty String.compare;
    texport_knn hhs_predict_dir thmfeal feag;
    ignore (mepo_predict n);
    tread_predictions ()
    )

end (* struct *)








