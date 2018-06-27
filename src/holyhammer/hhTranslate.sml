(* ========================================================================== *)
(* FILE          : hhTranslate.sml                                            *)
(* DESCRIPTION   : HOL to FOL translations                                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(*                                                                            *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure hhTranslate :> hhTranslate =
struct

open HolKernel boolLib tttTools

(*----------------------------------------------------------------------------
   Variable names
  ----------------------------------------------------------------------------*)

(* renaming *)
local val vi = ref 0 in  
  fun rename_bvarl tm = 
    let 
      fun rename_aux tm = case dest_term tm of
        VAR(Name,Ty)       => tm
      | CONST{Name,Thy,Ty} => tm
      | COMB(Rator,Rand)   => mk_comb (rename_aux Rator, rename_aux Rand)
      | LAMB(Var,Bod)      => 
        let 
          val new_tm = rename_bvar ("V" ^ int_to_string (!vi)) tm
          val (v,bod) = dest_abs new_tm
          val _ = incr vi
        in
          mk_abs (v, rename_aux bod)
        end
    in
      rename_aux tm
    end
  fun reset_v () = vi := 0
end

(* find bound variables after renaming *)
fun all_bvar tm = 
  mk_fast_set Term.compare (map (fst o dest_abs) (find_terms is_abs tm))

(* lifting *)
local val li = ref 0 in  
  fun genvarl ty = 
    let val r =  mk_var ("gl" ^ int_to_string (!li), ty) in
      incr li; r
    end
  fun reset_gl () = li := 0
end

(* arity *)
local val ai = ref 0 in  
  fun genvara ty = 
    let val r =  mk_var ("ga" ^ int_to_string (!ai), ty) in
      incr ai; r
    end
  fun reset_ga () = ai := 0
end

(*----------------------------------------------------------------------------
   First-order atoms
   Warning: a and b are considered atoms is !a. a = b instead of a = b
  ----------------------------------------------------------------------------*)

fun must_pred tm =
  is_forall tm orelse is_exists tm orelse is_conj tm orelse is_disj tm orelse
  is_imp tm orelse is_eq tm orelse is_neg tm

local
  val (atoml: term list ref) = ref []
  fun atoms_aux tm =
    if is_conj tm orelse is_disj tm orelse is_imp_only tm orelse is_eq tm
      then (atoms_aux (lhand tm); atoms_aux (rand tm))
    else if is_neg tm      then atoms_aux (rand tm)
    else if is_forall tm   then atoms_aux (snd (dest_forall tm))
    else if is_exists tm   then atoms_aux (snd (dest_exists tm))
    else atoml := tm :: (!atoml)
in 
  fun atoms tm = (atoml := []; atoms_aux tm; !atoml)
end

(*----------------------------------------------------------------------------
  Arity
  ----------------------------------------------------------------------------*)

fun update_adict adict arity tm = 
  let val oldl = dfind tm (!adict) handle NotFound => [] in
    adict := dadd tm (arity :: oldl) (!adict)
  end

fun collect_arity_aux adict tm =
  if is_const tm orelse is_var tm then update_adict adict 0 tm 
  else if is_comb tm then
    let val (oper,argl) = strip_comb tm in
      update_adict adict (length argl) oper;
      app (collect_arity_aux adict) argl
    end 
  else if is_abs tm then collect_arity_aux adict (snd (dest_abs tm))
  else raise ERR "collect_arity_aux" ""
  
fun collect_arity tm = 
  let 
    val adict = ref (dempty Term.compare)
    fun f (_,l) = mk_fast_set Int.compare l 
  in  
    app (collect_arity_aux adict) (atoms tm); 
    Redblackmap.map f (!adict)
  end

(*----------------------------------------------------------------------------
   FOF Checks
 -----------------------------------------------------------------------------*)

(* Lambda *)
fun no_lambda tm = not (exists (can (find_term is_abs)) (atoms tm))
fun no_pred tm   = not (exists (can (find_term must_pred)) (atoms tm))

fun has_fofarity_bv tm =
  let 
    val adict = collect_arity tm 
    fun f x = length (dfind x adict) <= 1 handle NotFound => true
  in
    all f (all_bvar tm)
  end

(*----------------------------------------------------------------------------
  Lifting proposition and lambdas in the same pass.
  ----------------------------------------------------------------------------*)

fun ATOM_CONV conv tm =
  if is_forall tm orelse is_exists tm 
    then QUANT_CONV (ATOM_CONV conv) tm 
  else if is_conj tm orelse is_disj tm orelse is_imp_only tm orelse is_eq tm
    then BINOP_CONV (ATOM_CONV conv) tm else
  if is_neg tm 
    then RAND_CONV (ATOM_CONV conv) tm 
  else conv tm

fun FUN_EQ_CONVL vl eq = case vl of
    [] => REFL eq
  | a :: m => (STRIP_QUANT_CONV (X_FUN_EQ_CONV a) THENC FUN_EQ_CONVL m) eq
  
fun LIFT_CONV tm =
  let 
    fun test x = must_pred x orelse is_abs x
    val subtm = find_term test tm handle _ => raise ERR "LIFT_CONV" ""
    val fvl = free_vars_lr subtm
    val v = genvarl (type_of (list_mk_abs (fvl,subtm)))
    val rep = list_mk_comb (v,fvl)
    val eq  = list_mk_forall (fvl, (mk_eq (subtm,rep)))
    val thm = ASSUME eq
  in
    if is_abs subtm then 
      let 
        val (vl,bod) = strip_abs subtm
        val ethm1 = (FUN_EQ_CONVL vl THENC TOP_DEPTH_CONV BETA_CONV) eq
        val ethm2 = UNDISCH (snd (EQ_IMP_RULE ethm1))
        val cthm = PURE_REWRITE_CONV [thm] tm
      in
        PROVE_HYP ethm2 cthm 
      end
    else REWRITE_CONV [thm] tm
  end

(* Todo : make a completeness check for this function *)      
fun RPT_LIFT_CONV tm =
  let  
    val thmo = SOME (REPEATC (ATOM_CONV (TRY_CONV LIFT_CONV)) tm) 
    handle UNCHANGED => NONE
  in
    case thmo of
      SOME thm =>  
      let
        val (asl,w) = dest_thm thm
        val thml1 = List.concat (map RPT_LIFT_CONV asl)
      in
        thm :: thml1
      end
    | NONE => [REFL tm]
  end

(*----------------------------------------------------------------------------
  load "tttTools";
  open tttTools;
  show_assums := true;
  
  val tm = “(∀h y. y (h y) z)``;
  val tm = ``!f2 y. (λx y.x) = f2 y``;
  val tm = ``!y. y (\x.x) 2 = P (!z.z)``;
  val tm = ``(!h y. y (∀z. h (\x.x) y)) <=> (!x. (\x. x) T)``;

  RPT_LIFT_CONV term;
  val thm = REPEATC (ATOM_CONV LIFT_CONV) term;
  ----------------------------------------------------------------------------*)


(*----------------------------------------------------------------------------
  Lowest arity for bound variables. Arity 0. 
  ----------------------------------------------------------------------------*)

fun LET_CONV_MIN tm =
  let val (rator,rand) = dest_comb tm in
    SYM (ISPECL [rator,rand] LET_THM) 
  end
  
fun LET_CONV_AUX tm =
 (TRY_CONV (RATOR_CONV LET_CONV_AUX) THENC LET_CONV_MIN) tm

fun LET_CONV_BV bvl tm = 
  if not (is_comb tm) then NO_CONV tm else
    let val (f,_) = strip_comb tm in
      if mem f bvl then LET_CONV_AUX tm else NO_CONV tm
    end

(* Warning: assumes free variables and bound variables have distinct names *)
fun LET_CONV_BVL tm =
  let val bvl = all_bvar tm in
    TOP_DEPTH_CONV (LET_CONV_BV bvl) tm
  end
   
(*----------------------------------------------------------------------------
  Arity equations for constants and free variables.
  Naming is important here as we do not want free variables to have the same
  name across statements unless their definition are alpha equivalent.
  ----------------------------------------------------------------------------*)

fun strip_type ty =
  if is_vartype ty then ([],ty) else 
    case dest_type ty of
      ("fun",[a,b]) => 
      let val (tyl,im) = strip_type b in
        (a :: tyl, im)
      end
    | _             => ([],ty)

fun mk_arity_eq f n =
  let 
    val (tyl,_) = strip_type (type_of f) 
    val vl = map genvara tyl
    val t1 = list_mk_comb (f, List.take (vl,n))
  in
    LET_CONV_AUX t1
  end

fun all_arity_eq tm =
  let
    val l = dlist (collect_arity tm)
    fun g x = x <> 0
    fun f (tm,nl) = 
      if is_abs tm orelse is_comb tm then raise ERR "all_arity_eq" ""
      else map (mk_arity_eq tm) (filter g nl)
  in
    List.concat (map f l)
  end

(* Complete only if there isn't any existential over a function *) 
fun optim_arity_eq tm =
  let 
    val l = dlist (collect_arity tm)
    fun g x = x <> 0
    fun f (tm,nl) = 
      if is_abs tm orelse is_comb tm then raise ERR "all_arity_eq" ""
      else 
        if length nl >= 2 
        then map (mk_arity_eq tm) (filter g nl)
        else []
  in
    List.concat (map f l)
  end

(*----------------------------------------------------------------------------
  Full translation
  ----------------------------------------------------------------------------*)

fun prepare_tm tm =
  rename_bvarl (list_mk_forall (free_vars_lr tm, tm))

(* Delay the decision on which arity theorem to produce *) 
fun translate_tm tm =
  let 
    val tm1 = prepare_tm tm
    val thml1 = RPT_LIFT_CONV tm1
    val tml1 = map (rand o concl) thml1
    val thml2 = map (TRY_CONV LET_CONV_BVL THENC REFL) tml1
    val tml2 = map (rand o concl) thml2
  in
    tml2
  end

fun translate_pb premises cj =
  let
    val _ = (reset_v(); reset_gl (); reset_ga ())
    fun f (name,thm) =  (name,translate_tm (concl (DISCH_ALL thm)))
    val cj_tml = translate_tm cj
    val ax_tml = map f premises
    val big_tm = 
      list_mk_conj (map list_mk_conj (cj_tml :: (map snd ax_tml)))
    val ari_tml = map (concl o DISCH_ALL) (optim_arity_eq big_tm)
  in
    (ari_tml, ax_tml, cj_tml)
  end

(* todo: optimizations: 
  0) Rewrite connectives like ?!
  1) change the left hand side and right hand side of equality
  2) improve sharing 
*)

fun name_pb (ari_tml, ax_tml, cj_tml) =
  let
    (* arity *)
    fun name_ari i tm = ("arity" ^ int_to_string i, tm)
    val axl1 = mapi name_ari ari_tml
    (* axioms *)
    fun name_ax (name,tml) =
      let fun name_axi i tm = (name ^ "." ^ int_to_string i, tm) in
        mapi name_axi tml
      end
    val axl2 = List.concat (map name_ax ax_tml)
    (* conjecture *)
    fun name_cjdef i tm = ("cj_def" ^ int_to_string i, tm)
    val cj = hd cj_tml (* Relies on the behavior of RPT_LIFT_CONV *)
    val axl3 = mapi name_cjdef (tl cj_tml)
  in
    (axl1 @ axl2 @ axl3, cj)  
  end

(* 
  load "hhTranslate";
  open hhTranslate;
  val tm = ``(!f. (f + 0 = 0)) /\ P($+)``;
  val tm = ``∀z h y. h (\x. z x) y``;
  val tm = “(∀h y. y (h y) z)``;
  val tm = ``!f2 y. (λx y.x) = f2 y``;
  val tm = ``!y. y (\x.x) 2 = P (!z.z)``;
  val tm = ``(!h y. y (∀z. h (\x.x) y)) <=> (!x. (\x. x) T)``;
  
  val r = translate_pb [] tm;
  val (l,cj) = name_pb r;

  tttTools.dlist (collect_arity term);
  all_arity_eq term;
  
  1) generalize free variables 
  2) and rename variables 
  3) apply translate
  
   should produce a list of pairs (name,tml1,tml2)
  
  
  4) generate arity equations for free variables and constants 
     for the list of terms. (Unoptimized, so it can be local)
     simple name for arity theorems.
     
  6) print the list of terms to fof making sure to know where each term came
  from
  read the proof from Eprover and reconstruct it.
  
  
*)



end
