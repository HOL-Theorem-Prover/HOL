(* ========================================================================== *)
(* FILE          : tttSynt.sml                                                *)
(* DESCRIPTION   : Synthesis of terms for conjecturing lemmas                 *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttSynt :> tttSynt =
struct

open HolKernel boolLib Abbrev tttTools

val ERR = mk_HOL_ERR "tttSynt"

val freq_limit = ref 3

(* --------------------------------------------------------------------------
   Debugging
   -------------------------------------------------------------------------- *)

val ttt_synt_dir = tactictoe_dir ^ "/log_synt"

fun log_synt_file file s =
  append_endline (ttt_synt_dir ^ "/" ^ file) s 

fun log_synt s = 
  (print_endline s; log_synt_file "log" s)

fun msg_synt l s = 
  let val s' = int_to_string (length l) ^ " " ^ s in
    log_synt s'
  end

(* --------------------------------------------------------------------------
   Stateful dictionnaries
   -------------------------------------------------------------------------- *)

type psubst = (int * int) list
type tsubst = (term * term) list

(* dictionnary *)
val cdict_glob = ref (dempty Term.compare)
val icdict_glob = ref (dempty Int.compare)
val cdict_loc = ref (dempty Int.compare)
val cjinfo_glob =ref (dempty Term.compare)


fun fconst_glob c =
  dfind c (!cdict_glob) handle NotFound =>
  let val cglob = dlength (!cdict_glob) in
    cdict_glob := dadd c cglob (!cdict_glob); 
    icdict_glob := dadd cglob c (!icdict_glob);
    cglob
  end

fun fconst_loc cglob =
  dfind cglob (!cdict_loc) handle NotFound =>
  let val cloc = dlength (!cdict_loc) in
    cdict_loc := dadd cglob cloc (!cdict_loc); 
    cloc
  end
  
fun fconst c = fconst_loc (fconst_glob c)

val type_errors = ref 0

fun init_synt () =
  (
  cdict_glob := dempty Term.compare;
  icdict_glob := dempty Int.compare;
  cjinfo_glob := dempty Term.compare;
  type_errors := 0
  )

(* --------------------------------------------------------------------------
   Conceptualization
   -------------------------------------------------------------------------- *)

fun is_varconst x = is_var x orelse is_const x
  
fun count_subtm tml = 
  let
    val d = ref (dempty Term.compare)
    fun count tm = 
      let val oldn = dfind tm (!d) handle NotFound => 0 in
        d := dadd tm (oldn + 1) (!d)
      end
    fun f tm = 
      let val subl = find_terms (not o is_varconst) tm in
        app count subl
      end
  in
    app f tml; !d
  end 

(* each concept is saved as a variable Cx *)
fun conceptualize_subtm tml = 
  let 
    val d = ref (dempty Term.compare)
    fun save_concept tm = 
      if dmem tm (!d) then () else 
      let val v = mk_var ("C" ^ int_to_string (dlength (!d)), type_of tm) in
        d := dadd tm v (!d)
      end
    fun f tm = 
      let val subl = find_terms (not o is_varconst) tm in
        app save_concept subl
      end
  in
    app f tml; !d
  end 

val concept_threshold = ref 3
val concept_flag = ref false

fun conceptualize countdict ceptdict tm =
  let 
    val subl0 = find_terms (not o is_varconst) tm 
    fun above_threshold tm = 
      (dfind tm countdict > !concept_threshold handle NotFound => false)
    val subl1 = filter above_threshold subl0
    fun cmp (tm1,tm2) = Int.compare (term_size tm2, term_size tm1)
    val subl2 = dict_sort cmp subl1
    fun f i tm = {redex = tm, residue = dfind tm ceptdict}
    val sub = mapi f subl2 
    val newtm = Term.subst sub tm
  in
    if term_eq newtm tm then [tm] else [tm,newtm]
  end

(* --------------------------------------------------------------------------
   Patterns
   -------------------------------------------------------------------------- *) 

datatype pattern =
    Pconst of int
  | Pcomb  of pattern * pattern
  | Plamb  of pattern * pattern

fun pattern_tm tm = 
  case dest_term tm of
    VAR _   => Pconst (fconst tm)
  | CONST _ => Pconst (fconst tm)
  | COMB(Rator,Rand) => Pcomb (pattern_tm Rator, pattern_tm Rand)
  | LAMB(Var,Bod)    => Plamb (pattern_tm Var, pattern_tm Bod)
  
fun patternify tm = 
  let 
    val _ = cdict_loc := dempty Int.compare
    fun cmp (a,b) = Int.compare (snd a, snd b)
    val p = pattern_tm tm
    val l1 = dlist (!cdict_loc)
    val l2 = dict_sort cmp l1
  in
    (p, map fst l2)
  end
  
fun p_compare (p1,p2) = case (p1,p2) of
    (Pconst i1,Pconst i2) => Int.compare (i1,i2)
  | (Pconst _,_) => LESS
  | (_,Pconst _) => GREATER
  | (Pcomb(a1,b1),Pcomb(a2,b2)) => 
    cpl_compare p_compare p_compare ((a1,b1),(a2,b2))
  | (Pcomb _,_) => LESS
  | (_,Pcomb _) => GREATER
  | (Plamb(a1,b1),Plamb(a2,b2)) => 
    cpl_compare p_compare p_compare ((a1,b1),(a2,b2))

(* --------------------------------------------------------------------------
   Patterns
   -------------------------------------------------------------------------- *) 

fun regroup tml =
  let
    val rdict = ref (dempty p_compare)
    val tml1 = mk_fast_set Term.compare tml
    fun f tm = 
      let 
        val (p,cl) = patternify tm 
        val oldl = dfind p (!rdict) handle NotFound => []  
      in
        rdict := dadd p (cl :: oldl) (!rdict)
      end
  in
    app f tml1; (!rdict)
  end
  
(* Substitutions *)
fun compare_kimin (a,b) = Int.compare (fst a, fst b)

fun prod l1 l2 = List.concat (map (fn x => map (fn y => (x,y)) l2) l1)

fun norm_psubst l = 
  let val l1 = filter (fn (x,y) => x <> y) l in
    dict_sort compare_kimin l1
  end
  
fun gen_subst_ll ll = 
  let 
    val ll1 = mk_fast_set (list_compare Int.compare) ll
    val ll2 = filter (fn x => length x > 1) ll1
    val cpl = prod ll2 ll2
    val cpl' = filter (fn (x,y) => x <> y) cpl
  in
    map combine cpl'
  end

val subst_compare = list_compare (cpl_compare Term.compare Term.compare)
val psubst_compare = list_compare (cpl_compare Int.compare Int.compare)
  
fun gen_psubst dict = 
  let 
    fun f (p,ll) = gen_subst_ll ll 
    val l1  = List.concat (map f (dlist dict))
    val l2  = map norm_psubst l1
    val _   = msg_synt l2 "inferred substitutions"
    val cmp = list_compare (cpl_compare Int.compare Int.compare)
    val dfreq = count_dict (dempty cmp) l2 
    val _   = msg_synt (dlist dfreq) "unique substitutions"
    val l3  = filter (fn (a,b) => b >= !freq_limit) (dlist dfreq)
    val _   = msg_synt l3 ("frequent substitutions " ^  
     (int_to_string (!freq_limit)))
  in
    l3
  end
  
fun read_subst l = 
  let 
    fun read_c c = dfind c (!icdict_glob)
    fun f (a,b) = (read_c a, read_c b) 
  in
    map f l
  end

(* Make a substitution that does allow for wrong type *)
fun unsafe_subst sub tm = 
  let val redreso = List.find (fn (red,res) => red = tm) sub in
    if isSome redreso then snd (valOf (redreso)) else
    (
      case dest_term tm of
        VAR(Name,Ty)       => tm
      | CONST{Name,Thy,Ty} => tm
      | COMB(Rator,Rand)   => mk_comb (unsafe_subst sub Rator, unsafe_subst sub Rand)
      | LAMB(Var,Bod)      => mk_abs (unsafe_subst sub Var, unsafe_subst sub Bod)
    )
  end

(* Conjecturing *)
fun subst_changed origin_dict sub tm = 
  let val tm' = unsafe_subst sub tm in
    if Term.compare (tm,tm') = EQUAL 
      then NONE 
    else if (type_of tm' = bool handle HOL_ERR _ => false) 
      then 
        let 
          val oldl = dfind tm' (!origin_dict) handle NotFound => [] 
          val newl = (sub,tm) :: oldl
        in
          origin_dict := dadd tm' newl (!origin_dict);
          SOME tm'
        end
    else (incr type_errors; NONE)
  end
  handle HOL_ERR _ => (incr type_errors; NONE)

fun int_div n1 n2 = 
   (if n2 = 0 then 0.0 else Real.fromInt n1 / Real.fromInt n2) 

fun my_gen_all tm = SOME (list_mk_forall (free_vars_lr tm, tm))
  handle HOL_ERR _ => (incr type_errors; NONE)

fun rank_sub origin_dict tml sub =
  let
    val cjl = 
      mk_fast_set Term.compare 
      (List.mapPartial (subst_changed origin_dict sub) tml) 
    val qcjl0 = List.mapPartial my_gen_all cjl
    val d = count_dict (dempty Term.compare) (List.mapPartial my_gen_all tml)
    val (qcjl1,qcjl2) = partition (fn x => dmem x d) qcjl0
    val (ntot,ngood,nbad) = (length qcjl0, length qcjl1, length qcjl2)
  in
    (sub, (qcjl2, int_div ngood ntot))
  end

fun inv_dict cmp d = 
  dnew cmp (map (fn (a,b) => (b,a)) (dlist d))

fun gen_cjl tml =
  let
    val _     = log_synt "initialize globals in tttSynt.sml" 
    val _     = init_synt ()
    val _     = log_synt "preparing the term set"
    val tml0 = mk_fast_set Term.compare tml
    val tml1 = map (snd o strip_forall o rename_bvarl (fn _ => "")) tml0
    val tml2 = mk_fast_set Term.compare tml1
    val _     = log_synt "patternify and pair terms"
    val pairdict = regroup tml2
    val _     = msg_synt (dlist (!cdict_glob)) " constants or variables"
    val _     = log_synt "generating substitutions"
    val subl0 = gen_psubst pairdict
    val _     = log_synt "reading substitutions"
    val subl1 = map read_subst (map fst subl0)
    val _     = log_synt "ranking substitutions"
    val origin_dict = ref (dempty Term.compare)
    val subl2 = map (rank_sub origin_dict tml2) subl1
    val subrank_dict = dnew subst_compare subl2
    val _     = log_synt (int_to_string (!type_errors) ^ " type errors")
    val cjl1  = dict_sort compare_rmax (map snd subl2)
    val cjl2  = List.concat (map fst cjl1)
    val cjl3  = mk_sameorder_set Term.compare cjl2
    val _     = msg_synt cjl3 "generated conjectures"
  in
    (cjl3, subrank_dict, !origin_dict)
  end

end (* struct *)
