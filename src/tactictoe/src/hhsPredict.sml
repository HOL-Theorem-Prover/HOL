(* =========================================================================  *)
(* FILE          : hhsPredictor.sml                                           *)
(* DESCRIPTION   : Tactic and theorem selections through external calls to    *)
(* machine learning programs                                                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsPredict :> hhsPredict =
struct

open HolKernel Abbrev hhsTools hhsTools hhsSetup

val ERR = mk_HOL_ERR "hhsPredict"

(* -------------------------------------------------------------------------- 
   TFIDF: weight of symbols (power of 6 comes from the distance)
   -------------------------------------------------------------------------- *)

fun learn_tfidf feavl = 
  let
    val syms      = List.concat (map snd feavl)
    val dict      = count_dict (dempty Int.compare) syms
    val n         = length feavl
    fun f (fea,freq) = 
      Math.pow (Math.ln (Real.fromInt n) - Math.ln (Real.fromInt freq), 6.0)
  in
    Redblackmap.map f dict
  end

(* -------------------------------------------------------------------------- 
   Scoring                                                                    
   -------------------------------------------------------------------------- *)

fun inter_dict dict l =
  filter (fn x => dmem x dict) l

fun union_dict dict l = dkeys (daddl (map (fn x => (x,())) l) dict)

(* --------------------------------------------------------------------------
   KNN distance
   -------------------------------------------------------------------------- *)

fun knn_self_distance symweight fea =
  let
    fun wf s    = dfind s symweight handle _ => 0.0
    val weightl = map wf fea
  in
    sum_real weightl
  end

fun knn_distance symweight dict_o fea_p =
  let 
    val fea_i   = inter_dict dict_o fea_p
    fun wf n    = dfind n symweight handle _ => raise ERR "knn_distance" ""
    val weightl = map wf fea_i
  in
    sum_real weightl
  end

(* borrow the symweight from theorem *)
fun knn_similarity symweight dict_o fea_p =
  let 
    val fea_i   = inter_dict dict_o fea_p
    val fea_u   = union_dict dict_o fea_p
    fun wf n    = dfind n symweight handle _ => raise ERR "knn_sim" ""
    val weightl1 = map wf fea_i
    val weightl2 = map wf fea_u
  in
    sum_real weightl1 / Math.ln (Math.e + sum_real weightl2)
  end

(* --------------------------------------------------------------------------
   Internal predictions
   -------------------------------------------------------------------------- *)

fun compare_score ((_,x),(_,y)) = Real.compare (y,x)

(* A label can be predicted multiple times *)
fun pre_knn symweight feal fea_o =
  let 
    val dict_o = dnew Int.compare (map (fn x => (x,())) fea_o)
    fun dist (lbl,fea_p) = (lbl, knn_distance symweight dict_o fea_p)
    val l0 = map dist feal
    val l1 = dict_sort compare_score l0
  in
    l1
  end

fun pre_sim symweight feal fea_o =
  let 
    val dict_o = dnew Int.compare (map (fn x => (x,())) fea_o)
    fun dist (lbl,fea_p) = (lbl, knn_similarity symweight dict_o fea_p)
    val l0 = map dist feal
    val l1 = dict_sort compare_score l0
  in
    l1
  end

(* Put features into the label *)  
fun pre_knn_fea symweight feal fea_o =
  let 
    val dict_o = dnew Int.compare (map (fn x => (x,())) fea_o)
    fun dist (lbl,fea) = ((lbl,fea), knn_distance symweight dict_o fea)
    val l0 = map dist feal
    val l1 = dict_sort compare_score l0
  in
    l1
  end  

(* eliminate duplicates with the same tactic string *)    
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
   Term prediction for tactic arguments. 
   Relies on mdict_glob to calculate symweight.
   -------------------------------------------------------------------------- *)

fun same_type term1 term2 =
  polymorphic (type_of term1) orelse type_of term1 = type_of term2

fun is_true _ = true

fun closest_subterm ((asl,w):goal) term =
  let 
    fun togoal t = ([],t)
    fun dummy_lbl l = map (fn (_,a) => ((),a)) l
    fun f x = (togoal x, hhsFeature.fea_of_goal (togoal x))
    val l0 = List.concat (map (rev o find_terms (same_type term)) (w :: asl))
    val l1 = if null l0 
              then List.concat (map (rev o find_terms is_true) (w :: asl))
              else l0
    val l2 = debug_t "mk_sameorder_set" (mk_sameorder_set Term.compare) l1
    val thmfeav = dlist (!mdict_glob)
    val feal = debug_t "features" (map f) l2
    val fea_o = hhsFeature.fea_of_goal ([],term)
    val symweight = 
      learn_tfidf (((),fea_o) :: dummy_lbl feal @ dummy_lbl thmfeav)
    val l3 = debug_t "pre_sim" pre_sim symweight feal fea_o
  in
    snd (fst (hd l3)) handle _ => raise ERR "closest_subterm" ""
  end

(* Example:

symweight = learn_tfidf feal

*)

(* --------------------------------------------------------------------------
   Goal evaluation for monte carlo tree search.
   -------------------------------------------------------------------------- *)

fun premcknn symweight radius feal fea = 
  map fst (first_n radius (pre_knn_fea symweight feal fea))

fun mcknn symweight radius feal fea =
  let
    fun ispos n (b,m) = b andalso m <= n
    fun isneg n (b,m) = (not b andalso m >= n) orelse (b andalso m > n)
    val bnl = map fst (first_n radius (pre_knn symweight feal fea))
    val nl = mk_fast_set Int.compare (map snd bnl)
    fun posf n = length (filter (ispos n) bnl)
    fun negf n = length (filter (isneg n) bnl)
    fun skewed_proba n = 
      let 
        val pos = Real.fromInt (posf n)
        val neg = Real.fromInt (negf n)
      in
        pos / ((neg + pos) * (Real.fromInt n))
      end
  in   
    list_rmax (map skewed_proba nl)
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
fun name_fea fea = mlquote (int_to_string fea)

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

(* actually produce repetitions    *)
fun stacknn_ext n stacfea feag =
  if null stacfea then []
  else
    (
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
    thm_counter := 0;
    thm_dict    := dempty String.compare;
    unthm_dict  := dempty String.compare;
    texport_knn hhs_predict_dir thmfeal feag;
    ignore (mepo_predict n);
    tread_predictions ()
    )

end (* struct *)
