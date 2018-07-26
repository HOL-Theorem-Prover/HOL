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

type psubst = (int * int) list

(* dictionnary *)
val cdict_glob = ref (dempty Term.compare)
val icdict_glob = ref (dempty Int.compare)
val cdict_loc = ref (dempty Int.compare)

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

(* database *)
val thyl = ancestry (current_theory ())
val thml = List.concat (map DB.thms thyl)

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

fun var_subtm tml = 
  let 
    val d = ref (dempty Term.compare)
    fun var tm = 
      if dmem tm (!d) then () else 
      let val v = mk_var ("C" ^ int_to_string (dlength (!d)), type_of tm) in
        d := dadd tm v (!d)
      end
    fun f tm = 
      let val subl = find_terms (not o is_varconst) tm in
        app var subl
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
    val _ = cdict_glob := dempty Term.compare
    val _ = icdict_glob := dempty Int.compare
    val dict = ref (dempty p_compare)
    val countdict = count_subtm tml
    val vardict = var_subtm tml
    val tml1 = 
      if !concept_flag 
      then List.concat (map (conceptualize countdict vardict) tml)
      else tml
    val tml2 = mk_fast_set Term.compare tml1
    fun f tm = 
      let 
        val (p,cl) = patternify tm 
        val oldl = dfind p (!dict) handle NotFound => []  
      in
        dict := dadd p (cl :: oldl) (!dict)
      end
  in
    app f tml2; (!dict,vardict)
  end
  
(* Substitutions *)
fun compare_snd_ir (a,b) = Int.compare (snd b, snd a)
fun compare_fst_i (a,b) = Int.compare (fst a, fst b)

fun prod l1 l2 = List.concat (map (fn x => map (fn y => (x,y)) l2) l1)

fun norm_psubst l = 
  let val l1 = filter (fn (x,y) => x <> y) l in
    dict_sort compare_fst_i l1
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
  
fun gen_psubst dict =
  let 
    fun f (p,ll) = gen_subst_ll ll 
    val l1 = List.concat (map f (dlist dict))
    val l2 = map norm_psubst l1
  in
    l2
  end
  
fun read_subst iceptdict l = 
  let 
    fun g tm = dfind tm iceptdict handle NotFound => tm
    fun f (a,b) = 
      {redex   = g (dfind a (!icdict_glob)), 
       residue = g (dfind b (!icdict_glob))} 
  in
    map f l
  end

(* Make a substitution that does allow for wrong type *)
fun unsafe_subst sub tm = 
  let val redreso = List.find (fn {redex,residue} => redex = tm) sub in
    if isSome redreso 
    then #residue (valOf (redreso))
    else
    (
      case dest_term tm of
        VAR(Name,Ty)       => tm
      | CONST{Name,Thy,Ty} => tm
      | COMB(Rator,Rand)   => 
        mk_comb (unsafe_subst sub Rator, unsafe_subst sub Rand)
      | LAMB(Var,Bod)      => 
        mk_abs (unsafe_subst sub Var, unsafe_subst sub Bod)
    )
  end

(* Conjecturing *)
fun subst_changed sub tm = 
  let val tm' = unsafe_subst sub tm in
    if Term.compare (tm,tm') = EQUAL then NONE else SOME (tm,tm')
  end
  handle _ => NONE

fun int_div n1 n2 = 
   (if n2 = 0 then 0.0 else Real.fromInt n1 / Real.fromInt n2) 

fun eval_subst tml (sub,nsub) =
  let
    val cjl0 = mk_fast_set (fn (x,y) => Term.compare (snd x,snd y))
      (List.mapPartial (subst_changed sub) tml)
    val d = count_dict (dempty Term.compare) tml
    val cjl1 = filter (fn x => dmem (snd x) d) cjl0
    val cjl2 = filter (fn x => not (dmem (snd x) d)) cjl0
    val ntot = length cjl0
    val ngood = length cjl1
  in
    (
    sub, 
    cjl2, 
    int_div ngood ntot * 100.0
    )
  end

fun inv_dict cmp d = 
  dnew cmp (map (fn (a,b) => (b,a)) (dlist d))

fun gen_cjl tmfea_org =
  let
    val tml_org0 = mk_fast_set Term.compare (map fst tmfea_org)
    val tml_org1 = map (snd o strip_forall o rename_bvarl (fn _ => "")) tml_org0
    val tml_org2 = mk_fast_set Term.compare tml_org1
    val (d0,ceptdict) = regroup tml_org2
    val iceptdict = inv_dict Term.compare ceptdict
    val substl = gen_psubst d0
    val d1 =
      count_dict (dempty (list_compare (cpl_compare Int.compare Int.compare))) 
      substl
    fun compare_snd_ir (a,b) = Int.compare (snd b, snd a)
    val l1 = dict_sort compare_snd_ir (dlist d1)
    val l2 =  filter (fn x => snd x > 2) l1
    val l3 = map (fn (sub,i) => (read_subst iceptdict sub,i)) l2
    val l4 = map (eval_subst tml_org2) l3
    fun compare_5 ((_,_,y),(_,_,x)) = Real.compare (x,y)
    val l5 = dict_sort compare_5 l4
    val l6 = map snd (List.concat (map #2 l5))
    val l7 = mk_sameorder_set Term.compare l6
  in
    l7
  end


end (* struct *)
