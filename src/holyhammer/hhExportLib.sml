(* ========================================================================= *)
(* FILE          : hhExportLib.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportLib :> hhExportLib =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate

val ERR = mk_HOL_ERR "hhExportLib"

(* -------------------------------------------------------------------------
   Directory
   ------------------------------------------------------------------------- *)

val hh_dir = HOLDIR ^ "/src/holyhammer"

(* -------------------------------------------------------------------------
   Writer shortcuts
   ------------------------------------------------------------------------- *)

fun os oc s = TextIO.output (oc,s)

fun osn oc s = TextIO.output (oc,s ^ "\n")

fun oiter_aux oc sep f l = case l of
    []     => ()
  | [a]    => f oc a
  | a :: m => (f oc a; os oc sep; oiter_aux oc sep f m)

fun oiter oc sep f l = oiter_aux oc sep f l

(* -------------------------------------------------------------------------
   Higher-order to first-order type
   ------------------------------------------------------------------------- *)

fun type_vars_in_term tm =
  type_varsl (map type_of (find_terms is_const tm @ all_vars tm))

fun strip_funty_aux ty =
  if is_vartype ty then [ty] else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in
          tya :: strip_funty_aux tyb
        end
      else [ty]
    end

fun strip_funty_n n ty =
  if is_vartype ty orelse n <= 0 then [ty] else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in
          tya :: strip_funty_n (n-1) tyb
        end
      else [ty]
    end

fun strip_funty ty = case strip_funty_aux ty of
    [] => raise ERR "strip_funty" ""
  | x => (last x, butlast x)


fun full_match_type t1 t2 =
  let
    val (sub1,al) = raw_match_type t1 t2 ([],[])
    fun id_sub a = {redex = a, residue = a}
    val sub2 = map id_sub al
    fun cmp (a,b) = Type.compare (#redex a, #redex b)
  in
    dict_sort cmp (sub1 @ sub2)
  end

fun full_apply_const c =
  let 
    val (imty,argtyl) = strip_funty (type_of c)
    fun f i x = mk_var ("V" ^ its i,x)
    val vl = mapi f argtyl 
  in
    list_mk_comb (c,vl)
  end

(* -------------------------------------------------------------------------
   Polymorphism and types
   ------------------------------------------------------------------------- *)

val ttype = "$tType"
val otype = "$o"

fun typearg_of_const tm =
  let
    val {Thy, Name, Ty} = dest_thy_const tm
    val mgty = type_of (prim_mk_const {Thy = Thy, Name = Name})
    val subst = full_match_type mgty Ty
  in 
    map #residue subst
  end

fun typearg_of_var tm =
  let
    val ty = snd (dest_var tm)
    val subst = full_match_type ty ty
  in 
    map #residue subst
  end

fun typearg_of_appvar tm =
  let
    val ty = snd (dest_var tm)
    val mgty = type_of (prim_mk_const {Thy = "bool", Name = "LET"})
    val subst = full_match_type mgty ty
  in 
    map #residue subst
  end

(* -------------------------------------------------------------------------
   Dependencies of terms
   ------------------------------------------------------------------------- *)

fun atoms_of tm =
  if is_eq tm andalso type_of (lhs tm) = bool
    then atoms_of (lhs tm) @ atoms_of (rhs tm)
  else if is_eq tm then [lhs tm, rhs tm]
  else if is_conj tm orelse is_disj tm orelse is_imp_only tm
    then atoms_of (lhand tm) @ atoms_of (rand tm)
  else if is_neg tm    then atoms_of (rand tm)
  else if is_forall tm then atoms_of (snd (dest_forall tm))
  else if is_exists tm then atoms_of (snd (dest_exists tm))
  else [tm]


(* -------------------------------------------------------------------------
   Theory and theorem ordering for chainy and bushy experiments
   ------------------------------------------------------------------------- *)

fun before_elem e l = case l of
    [] => raise ERR "before_elem" ""
  | a :: m => if a = e then [] else a :: before_elem e m

fun older_than th1 (name,th2) = 
  depnumber_of_thm th2 < depnumber_of_thm th1

fun add_ancestry thy = thy :: ancestry thy
fun sorted_ancestry thyl = 
  sort_thyl (mk_string_set (List.concat (map add_ancestry thyl)))

(* -------------------------------------------------------------------------
   Shared printing functions : fl = (f_vty, f_term)
   ------------------------------------------------------------------------- *)

fun shared_pred fl oc tm =
  if is_forall tm then shared_quant fl oc "!" (strip_forall tm)
  else if is_exists tm then shared_quant fl oc "?" (strip_exists tm)
  else if is_conj tm then shared_binop fl oc "&" (dest_conj tm)
  else if is_disj tm then shared_binop fl oc "|" (dest_disj tm)
  else if is_imp_only tm then shared_binop fl oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "(~ "; shared_pred fl oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r
      then shared_binop fl oc "<=>" (l,r)
      else (os oc "("; (snd fl) oc l; os oc " = "; (snd fl) oc r; os oc ")")
    end
  else (snd fl) oc tm
and shared_binop fl oc s (l,r) =
  (os oc "("; shared_pred fl oc l; os oc (" " ^ s ^ " "); 
   shared_pred fl oc r; os oc ")")
and shared_quant fl oc s (vl,bod) =
  (os oc s; os oc "["; oiter oc ", " (fst fl) vl;
   os oc "]: "; shared_pred fl oc bod)


(* -------------------------------------------------------------------------
   Standard export
   ------------------------------------------------------------------------- *)

fun depo_of_thm thm =
  let
    val (b,depl1) = intactdep_of_thm thm
    val depl2 = map (split_string "Theory.") depl1
  in
    if b then SOME depl2 else NONE
  end

fun write_dep ocdep fb_thm thy ((name,thm),role) =
  (
  osn ocdep (fb_thm (thy,name));
  (if role = "conjecture" then
    let
      val (b,depl1) = intactdep_of_thm thm
      val depl2 = map (split_string "Theory.") depl1
      val depl3 = map fb_thm depl2
    in
      osn ocdep role;
      osn ocdep (if b then  "intact" else "broken");
      oiter ocdep " " os depl3; os ocdep "\n"
    end
  else osn ocdep role;
  osn ocdep "")
  )

fun write_thy (f_tydef,f_constdef,f_thmdef,fb_thm) export_dir thy =
  let
    val _ = print (thy ^ " ")
    val filedep = export_dir ^ "/" ^ thy ^ ".dependency"
    val file = export_dir ^ "/" ^ thy ^ ".theory"
    val oc = TextIO.openOut file
    val ocdep = TextIO.openOut filedep
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (f_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (f_constdef oc) cl
      val cjl = map (fn x => (x,"conjecture")) (DB.theorems thy)
      val axl = map (fn x => (x,"axiom")) (DB.axioms thy @ DB.definitions thy)
      fun cmp (((_,th1),_),((_,th2),_)) =
        Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
      val thml = dict_sort cmp (cjl @ axl)
    in
      app (write_dep ocdep fb_thm thy) thml; 
      app (f_thmdef oc thy) thml;
      app TextIO.closeOut [oc,ocdep]
    end 
    handle Interrupt => (app TextIO.closeOut [oc,ocdep]; raise Interrupt)
  end

(* (f_vty 0) for fof or fff *)

end (* struct *)
