(* ========================================================================== *)
(* FILE          : tttSynt.sml                                               *)
(* DESCRIPTION   : Synthesis of terms for conjecturing lemmas                 *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttSynt :> tttSynt =
struct

open HolKernel boolLib Abbrev tttTools

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

(* Patterns *)
fun regroup tml =
  let 
    val _ = cdict_glob := dempty Term.compare
    val _ = icdict_glob := dempty Int.compare
    val dict = ref (dempty p_compare)
    fun f tm = 
      let 
        val (p,cl) = 
          (patternify o snd o strip_forall o rename_bvarl (fn _ => "")) tm 
        val oldl = dfind p (!dict) handle NotFound => []  
      in
        dict := dadd p (cl :: oldl) (!dict)
      end
  in
    app f tml; !dict
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
  
fun read_subst l = 
  let fun f (a,b) = 
    {redex = dfind a (!icdict_glob), residue = dfind b (!icdict_glob)} 
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

fun check_subst sub =
  all (fn {redex,residue} => type_of redex = type_of residue) sub

end

(*
load "tttSynt";
open tttTools tttSynt;
load "holyHammer";
open holyHammer;
open tttPredict;
open tttExec;

(* Todo: split conjucntions + remove duplicates *)

fun number_of_thm thm = 
  (Dep.depnumber_of o Dep.depid_of o Tag.dep_of o Thm.tag) thm
fun feai_of_term x = (x, tttFeature.fea_of_goal ([],x))
fun fea_of_term x = tttFeature.fea_of_goal ([],x)

val thyl = sort_thyl (ancestry (current_theory ()))
val thyl1 = map (fn (a,b) => (b,a)) (number_list 0 thyl)
val thyldict = dnew String.compare thyl1

val id_compare = 
  (cpl_compare Int.compare (cpl_compare Int.compare Int.compare))

val (dict_glob :
(int * (int * int),
      (string * thm) * bool * (term * int list) *
      (int, real) Redblackmap.dict) Redblackmap.dict ref)
= ref (dempty id_compare)
val (revtm_glob : (term, int * (int * int)) Redblackmap.dict ref)
= ref (dempty Term.compare) 

fun update_dict dict thy =
  let
    fun f b (name,thm) = 
      let 
        val tm = (concl o GEN_ALL o DISCH_ALL) thm
        val tmfea = feai_of_term tm
        val symweight = learn_tfidf [tmfea]
        val k = (dfind thy thyldict,(number_of_thm thm,0))
        val v = ((name,thm),b,tmfea,symweight)
      in
        if dmem tm (!revtm_glob) 
        then 
          let val oldid = dfind tm (!revtm_glob) in
            if id_compare (oldid,k) = LESS 
            then ()
            else revtm_glob := dadd tm k (!revtm_glob)
          end
          
        else revtm_glob := dadd tm k (!revtm_glob)
        ;
        dict := dadd k v (!dict)
      end
  in
    app (f false) (DB.theorems thy);
    app (f true) (DB.axioms thy @ DB.definitions thy)
  end
;
  
app (update_dict dict_glob) thyl;
dlength (!dict_glob);

(* Conjecturing *)
val l0 = dlist (!dict_glob)
val tmfea_org = map (#3 o snd) l0
val symweight_org = learn_tfidf tmfea_org

val tml_org = mk_fast_set Term.compare (map fst tmfea_org)
val d0 = regroup tml_org

val substl = gen_psubst d0
val d1 =
  count_dict (dempty (list_compare (cpl_compare Int.compare Int.compare))) 
  substl
fun compare_snd_ir (a,b) = Int.compare (snd b, snd a)
val l1 = dict_sort compare_snd_ir (dlist d1)
val l2 =  filter (fn x => snd x > 2) l1
val l3 = map (fn (sub,i) => (read_subst sub,i)) l2
val l4 = map (eval_subst tml_org) l3
fun compare_5 ((_,_,y),(_,_,x)) = Real.compare (x,y)
val l5 = dict_sort compare_5 l4;

fun mprove premises tm =
  let
    val goal = ([], tm)
    fun mk_goal x = ([],x)
    val thml = map (mk_thm o mk_goal) premises
    val tac = METIS_TAC thml
  in
    case hide_out (app_tac 0.1 tac) goal of
      SOME [] => true 
    | _ => false
  end

fun compare_size (a,b) = Int.compare (term_size b, term_size a)

fun minimize_aux l1 l2 tm = case l2 of
    []     => l1
  | a :: m => 
    if mprove (l1 @ m) tm 
    then minimize_aux l1 m tm
    else minimize_aux (a :: l1) m tm
    
fun miniprove tml tm = 
  let
    (* biggest first > advantage to small *)
    val tml' = dict_sort compare_size tml 
  in
    if mprove tml' tm 
    then SOME (minimize_aux [] tml' tm)
    else NONE
  end

fun eval_elem (sub,ttl,sc1) =
  let 
    fun eval_tt tt =
      let 
        val cj = snd tt
        val tml = tmknn 16 (symweight_org,tmfea_org) (fea_of_term cj)
        val ro = miniprove tml cj
      in
        case ro of
          SOME []     => NONE (* trivial *)
        | NONE        => NONE
        | SOME lemmas => SOME (cj,lemmas)
      end
  in
    List.mapPartial eval_tt ttl
  end
  
val l6 = first_n 10 l5; 
val cjl0 = List.concat (map eval_elem l6);
length cjl0;

(* Evaluation *)

datatype usage = Future | Irrelevant | Predicted | Redundant | Useful

val rl : (term * usage * (int * (int * int))) list ref = ref []

fun usage_of (cj,cjfea,cjid) (id,(_,b,(tm,fea),_)) =
  if b then () else
  if id_compare (cjid,id) = GREATER then rl := (cj,Future,id) :: !rl else
  let
    val l0 = dlist (!dict_glob)
    fun is_older (id',_) = id_compare (id',id) = LESS
    val l1 = filter is_older l0
    val tmfea = (cj,cjfea) :: (map (#3 o snd) l1)
    val symweight = learn_tfidf tmfea
    val tml16 = tmknn 16 (symweight,tmfea) fea
    val tml15 = filter (not o (term_eq cj)) tml16  
    val r =
      if not (mem cj tml16) 
        then (cj,Irrelevant,id)
      else if not (mprove tml16 tm) 
        then (cj,Predicted,id)
      else if mprove tml15 tm 
        then (cj,Redundant,id)
      else (cj,Useful,id)
  in
    rl := r :: !rl
  end

fun id_of_term tm = dfind tm (!revtm_glob)
fun term_of_id id = fst (#3 (dfind id (!dict_glob)))

fun eval_cj (cj,lemmas) =
  let
    val cjfea  = fea_of_term cj
    val idl    = map id_of_term lemmas
    val (i1,(i2,_)) = last (dict_sort id_compare idl)
    val cjid        = (i1,(i2,1))
  in
    dapp (usage_of (cj,cjfea,cjid)) (!dict_glob)
  end

val ull = (rl := []; app eval_cj cjl0; !rl)
val ull = !rl;
val ulu = filter (fn x => #2 x = Useful) ull;
val ulp = filter (fn x => #2 x = Predicted) ull;
val ulr = filter (fn x => #2 x = Redundant) ull;
val ulf = filter (fn x => #2 x = Future) ull;
length ull;
length ull - length ulf;
length ulp;
length ulp - length ulr;
length ulu; 

val ulur = map (fn (a,b,c) => (a,b,term_of_id c)) ulu; 


val (cj,lemmas) =  cjl0

*)







  
  
  
  
  
  
  
  
  


