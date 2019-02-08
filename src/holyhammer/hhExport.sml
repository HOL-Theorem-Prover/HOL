(* ===================================================================== *)
(* FILE          : hhExport.sml                                          *)
(* DESCRIPTION   : Export HOL4 theories in a s-expression format         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2018                                                  *)
(* ===================================================================== *)

structure hhExport :> hhExport =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate holyHammer

val ERR = mk_HOL_ERR "hhExport"

(* -------------------------------------------------------------------------
   Preparing and analysing the formula
   ------------------------------------------------------------------------- *)

fun prep_tm tm = rename_bvarl escape (list_mk_forall (free_vars_lr tm, tm))
fun prep_thm thm = prep_tm (concl (DISCH_ALL thm))

fun full_match_type t1 t2 =
  let
    val (sub1,al) = raw_match_type t1 t2 ([],[])
    fun id_sub a = {redex = a, residue = a}
    val sub2 = map id_sub al
    fun cmp (a,b) = Type.compare (#redex a, #redex b)
  in
    dict_sort cmp (sub1 @ sub2)
  end

(* warning: some variables are considered constant.*)
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

(* ------------------------------------------------------------------------
   thf escaping : variables escaped by prep_tm
   ------------------------------------------------------------------------ *)

fun th1_var v = fst (dest_var v)
fun th1b_const (thy,name) = escape ("c." ^ thy ^ "." ^ name)
fun th1_const c =
  let val {Name,Thy,Ty} = dest_thy_const c in th1b_const (Thy,Name) end
fun th1_vartype ty = "A" ^ (escape (dest_vartype ty))
fun th1b_tyop (thy,tyop) = escape ("ty." ^ thy ^ "." ^ tyop)
fun th1_tyop ty =
  let val {Args,Thy,Tyop} = dest_thy_type ty in th1b_tyop (Thy,Tyop) end
fun th1b_thm (thy,name) = escape ("thm" ^ "." ^ thy ^ "." ^ name)

(* -------------------------------------------------------------------------
    TH1 terms
   ------------------------------------------------------------------------- *)

fun th1_type oc ty =
  if is_vartype ty then os oc (th1_vartype ty) else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "bool" then os oc "$o"
      else if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in    
          os oc "("; th1_type oc tya;
          os oc " > "; th1_type oc tyb; os oc ")"
        end
      else if null Args then os oc (th1_tyop ty)
      else (os oc "("; os oc (th1_tyop ty); os oc " @ ";
            oiter oc " @ " th1_type Args; os oc ")")
    end

fun th1_var_and_type oc v =  
  let val (vs,ty) = dest_var v in os oc (vs ^ ":"); th1_type oc ty end

fun th1_term oc tm =
  if is_var tm then os oc (th1_var tm)
  else if is_const tm then
    let val resl = typearg_of_const tm in
      if null resl
      then os oc (th1_const tm)
      else (os oc "("; os oc (th1_const tm); os oc " @ ";
            oiter oc " @ " th1_type resl; os oc ")")
    end
  else if is_comb tm then
    let val (rator,argl) = strip_comb tm in
      os oc "("; th1_term oc rator;
      os oc " @ "; oiter oc " @ " th1_term argl; os oc ")"
    end
  else if is_abs tm then
    let val (vl,bod) = strip_abs tm in
      os oc "^[";
      oiter oc ", " th1_var_and_type vl;
      os oc "]: "; th1_term oc bod
    end
  else raise ERR "th1_term" ""

(* could be shared *)
fun th1_pred oc tm =
  if is_forall tm then th1_quant oc "!" (strip_forall tm)
  else if is_exists tm then th1_quant oc "?" (strip_exists tm)
  else if is_conj tm then th1_binop oc "&" (dest_conj tm)
  else if is_disj tm then th1_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then th1_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "(~ "; th1_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r (* optimization *)
      then th1_binop oc "<=>" (l,r)
      else (os oc "("; 
            th1_term oc l; os oc " = ";  
            th1_term oc r; os oc ")")
    end
  else th1_term oc tm
and th1_binop oc s (l,r) =
  (os oc "("; th1_pred oc l; os oc (" " ^ s ^ " "); 
   th1_pred oc r; os oc ")")
and th1_quant oc s (vl,bod) =
  (os oc s; os oc "["; oiter oc ", " th1_var_and_type vl;
   os oc "]: "; th1_pred oc bod)

fun th1_formula oc tm =
  let 
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o th1_vartype) tvl
    val s = String.concatWith ", " tvls
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    th1_pred oc tm
  end

(* -------------------------------------------------------------------------
    TH1 definitions
   ------------------------------------------------------------------------- *)

fun th1_ttype arity =
  String.concatWith " > " (List.tabulate (arity + 1, fn _ => ttype))

fun th1_tydef oc thy (tyop,arity) =
  (os oc ("thf(" ^ th1b_tyop (thy,tyop) ^ ",type,");
   os oc (th1b_tyop (thy,tyop) ^ ":"); os oc (th1_ttype arity); osn oc ").")

fun th1_tyquant_type oc ty =
  let 
    val tvl = dict_sort Type.compare (type_vars ty) 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o th1_vartype) tvl
    val s = String.concatWith "," tvls
  in
    if null tvl then () else os oc ("!>[" ^ s ^ "]: ");
    th1_type oc ty
  end

fun th1_constdef oc (thy,name) =
  let val ty = type_of (prim_mk_const {Thy = thy, Name = name}) in
    comment oc ("c." ^ thy ^ "." ^ name ^ ": " ^ 
      rm_endline (type_to_string ty));
    os oc ("thf(" ^ th1b_const (thy,name) ^ ",type,");
    os oc (th1b_const (thy,name) ^ ":"); th1_tyquant_type oc ty; osn oc ")."
  end

fun th1_thmdef oc thy ((name,thm),role) =
  let val tm = prep_thm thm in
    comment oc (thy ^ "." ^ name ^ ": " ^ rm_endline (term_to_string tm));
    os oc ("thf(" ^ (th1b_thm (thy,name)) ^ "," ^ role ^ ",");
    th1_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   tf1 escaping : variables escaped by prep_tm
   ------------------------------------------------------------------------- *)

val combin_extra_flag = ref false

fun tf1_var arity v = fst (dest_var v) ^ "_" ^ int_to_string arity
fun tf1b_const arity (thy,name) = 
  if !combin_extra_flag 
  then escape ("c.combin-extra." ^ name) ^ "_" ^ int_to_string arity
  else escape ("c." ^ thy ^ "." ^ name) ^ "_" ^ int_to_string arity

fun tf1_const arity c =
  let val {Name,Thy,Ty} = dest_thy_const c in tf1b_const arity (Thy,Name) end

fun tf1_constvar arity tm =
  if is_const tm then tf1_const arity tm
  else if is_var tm then tf1_var arity tm
  else "!!Abstraction!!"

fun tf1_vartype ty = "A" ^ (escape (dest_vartype ty))
fun tf1b_tyop (thy,tyop) = escape ("ty." ^ thy ^ "." ^ tyop)
fun tf1_tyop ty =
  let val {Args,Thy,Tyop} = dest_thy_type ty in tf1b_tyop (Thy,Tyop) end

fun tf1b_thm (thy,name) = escape ("thm" ^ "." ^ thy ^ "." ^ name)

(* -------------------------------------------------------------------------
   tf1 terms
   ------------------------------------------------------------------------- *)

fun tf1_utype oc ty =
  if is_vartype ty then os oc (tf1_vartype ty) else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if null Args then os oc (tf1_tyop ty) else 
        (os oc (tf1_tyop ty);
         os oc "("; oiter oc "," tf1_utype Args; os oc ")")
    end

fun tf1_type arity oc ty = case strip_funty_n arity ty of
    [] => raise ERR "tf1_type" ""
  | [imty] => tf1_utype oc imty
  | [imty,uty] => 
    (os oc "("; tf1_utype oc uty; os oc " > "; tf1_utype oc imty;
     os oc ")")
  | l =>
    (os oc "(("; 
     oiter oc " * " tf1_utype (butlast l); os oc ") > "; 
     tf1_utype oc (last l); os oc ")")

fun tf1_var_and_type arity oc v =  
  let val (_,ty) = dest_var v in 
    os oc (tf1_var arity v ^ ":"); tf1_utype oc ty 
  end

fun tf1_term oc tm =
  if is_var tm then os oc (tf1_var 0 tm)
  else if is_const tm then os oc (tf1_const 0 tm)
  else if is_comb tm then
    let 
      val (rator,argl) = strip_comb tm
      val arity = length argl
      val tyargl = 
        if is_var rator then  
          if fst (dest_var rator) = "app" 
          then typearg_of_appvar rator
          else typearg_of_var rator
        else typearg_of_const rator
    in
      os oc (tf1_constvar arity rator); 
      os oc "("; 
      if null tyargl then () else 
      (oiter oc "," tf1_utype tyargl; os oc ",");
      oiter oc "," tf1_term argl; 
      os oc ")"
    end
  else raise ERR "tf1_term" "abstraction"

fun tf1_pred oc tm =
  if is_forall tm then tf1_quant oc "!" (strip_forall tm)
  else if is_exists tm then tf1_quant oc "?" (strip_exists tm)
  else if is_conj tm then tf1_binop oc "&" (dest_conj tm)
  else if is_disj tm then tf1_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then tf1_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "(~ "; tf1_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r
      then tf1_binop oc "<=>" (l,r)
      else (os oc "("; tf1_term oc l; os oc " = ";  
            tf1_term oc r; os oc ")")
    end
  else tf1_term oc tm
and tf1_binop oc s (l,r) =
  (os oc "("; tf1_pred oc l; os oc (" " ^ s ^ " "); 
   tf1_pred oc r; os oc ")")
and tf1_quant oc s (vl,bod) =
  (os oc s; os oc "["; oiter oc ", " (tf1_var_and_type 0) vl;
   os oc "]: "; tf1_pred oc bod)

fun tf1_formula oc tm =
  let 
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o tf1_vartype) tvl
    val s = String.concatWith ", " tvls
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    tf1_pred oc tm
  end

(* -------------------------------------------------------------------------
    tf1 definitions
   ------------------------------------------------------------------------- *)

fun tf1_ttype arity =
  if arity <= 1 then String.concatWith " > " [ttype,ttype] else
  "(" ^ String.concatWith " * " (List.tabulate (arity, fn _ => ttype)) ^ ")"
  ^ " > " ^ ttype 

fun tf1_tydef oc thy (tyop,arity) =
  let val tfname = tf1b_tyop (thy,tyop) in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
    os oc (tf1_ttype arity); osn oc ")."
  end

fun tf1_tyquant_type oc arity ty =
  let 
    val tvl = dict_sort Type.compare (type_vars ty) 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o tf1_vartype) tvl
    val s = String.concatWith "," tvls
  in
    if null tvl then () else os oc ("!>[" ^ s ^ "]: ");
    tf1_type arity oc ty
  end

fun tf1_constdef_arity_alone oc thy arity c (name,ty) =
  let val tfname = tf1b_const arity (thy,name) in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ")."
  end

fun tf1_constdef_arity oc thy arity c (name,ty) =
  let 
    val tfname = tf1b_const arity (thy,name) 
  in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ").";
    (if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq c arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc ("tff(" ^ arity_prefix ^ tfname ^ ",axiom,");
       tf1_formula oc eq; osn oc ").")
    end)
  end

fun tf1_vardef_arity oc (v,arity) =
  if fst (dest_var v) = "app" then () else 
  let 
    val tfname = tf1_var arity v 
    val ty = snd (dest_var v)
  in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ").";
    (
    if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq v arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc ("tff(" ^ arity_prefix ^ tfname ^ ",axiom,");
       tf1_formula oc eq; osn oc ").")
    end
    )
  end

fun tf1_constdef oc thy (name,ty) =
  let
    val maxarity = length (snd (strip_funty ty))
    val c = mk_thy_const {Name=name,Thy=thy,Ty=ty}
    fun f n = tf1_constdef_arity oc thy n c (name,ty)
  in
    comment oc ("c." ^ thy ^ "." ^ name ^ ": " ^ 
      rm_endline (type_to_string ty));
    ignore (List.tabulate (maxarity + 1, f))
  end

fun tf1_vardef oc v =
  let 
    val ty = snd (dest_var v)
    val maxarity = length (snd (strip_funty ty))
    fun f n = tf1_vardef_arity oc (v,n) 
  in
    comment oc ("fdef." ^ fst (dest_var v) ^ ": " ^ 
      rm_endline (type_to_string ty));
    ignore (List.tabulate (maxarity + 1, f))
  end

fun write_tf1_app dir = 
  let
    val file = dir ^ "/app-extra.ax"
    val oc = TextIO.openOut file
  in
    let
      val ty = type_of (prim_mk_const {Thy = "bool", Name = "LET"})
      val arity = 2
      val tfname = "app_2"
    in
      os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
      tf1_tyquant_type oc arity ty; osn oc ").";
      TextIO.closeOut oc
    end 
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end 

fun tf1_thmdef oc thy ((name,thm),role) =
  let 
    val tm = concl (DISCH_ALL thm)
    val tml = translate_tm tm
    val vl = free_vars_lr (list_mk_conj (rev tml))
    val (cj,defl) = (hd tml, rev (tl tml))
    fun f i def = 
      (
      os oc ("tff(" ^ escape ("fthm" ^ its i ^ ".") ^
      (tf1b_thm (thy,name)) ^ "," ^ role ^ ",");
      tf1_formula oc def; osn oc ")."
      )
  in
    comment oc ("thm." ^ thy ^ "." ^ name ^ ": " ^ 
      rm_endline (term_to_string tm));
    app (tf1_vardef oc) vl;
    ignore (mapi f defl);
    os oc ("tff(" ^ (tf1b_thm (thy,name)) ^ "," ^ role ^ ",");
    tf1_formula oc cj; osn oc ")."
  end

(* -------------------------------------------------------------------------
   S-expression 
   ------------------------------------------------------------------------- *)

fun double_quote s = "\"" ^ s ^ "\""
val sexpr_var = double_quote o th1_var
val sexpr_const = double_quote o th1_const
val sexpr_vartype = double_quote o th1_vartype
val sexpr_tyop = double_quote o th1_tyop

val sexprb_const = double_quote o th1b_const
val sexprb_tyop = double_quote o th1b_tyop
val sexprb_thm = double_quote o th1b_thm

fun sexpr_type oc ty =
  if is_vartype ty then os oc (sexpr_vartype ty) else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if null Args
      then os oc (sexpr_tyop ty)
      else (os oc "("; os oc (sexpr_tyop ty);
            os oc " "; oiter oc " " sexpr_type Args; os oc ")")
    end

fun sexpr_term oc tm =
  if is_var tm then os oc (sexpr_var tm)
  else if is_const tm then
    let
      val {Thy, Name, Ty} = dest_thy_const tm
      val mgty = type_of (prim_mk_const {Thy = Thy, Name = Name})
      val subst = full_match_type mgty Ty
      val resl = map #residue subst
    in
      if null resl
      then os oc (sexpr_const tm)
      else (os oc "("; os oc (sexpr_const tm); os oc " ";
            oiter oc " " sexpr_type resl; os oc ")")
    end
  else if is_comb tm then
    let val (rator,argl) = strip_comb tm in
      os oc "("; sexpr_term oc rator;
      os oc " "; oiter oc " " sexpr_term argl; os oc ")"
    end
  else if is_abs tm then
    let val (bvar,body) = dest_abs tm in
      os oc "("; os oc "lambda"; os oc " ";
      os oc (sexpr_var bvar); os oc " ";
      sexpr_type oc (type_of bvar); os oc " ";
      sexpr_term oc body; os oc ")"
    end
  else raise ERR "sexpr_term" ""

fun sexpr_tydef oc thy (tyop,arity) =
  (
  os oc "(type_definition ";
  os oc (sexprb_tyop (thy,tyop)); os oc " ";
  os oc (int_to_string arity); os oc ")\n"
  )

fun sexpr_tyquant_type oc ty =
  let val tvl = dict_sort Type.compare (type_vars ty) in
    if null tvl
    then sexpr_type oc ty
    else
      (
      os oc "(forall_tyvarl_type ";
      os oc "("; oiter oc " " sexpr_type tvl; os oc ")"; os oc " ";
      sexpr_type oc ty; os oc ")"
      )
  end

fun sexpr_tyquant_term oc tm =
  let
    val tyl = map type_of (find_terms is_const tm @ all_vars tm)
    val tvl = dict_sort Type.compare (type_varsl tyl)
  in
    if null tvl
    then sexpr_term oc tm
    else
      (
      os oc "("; os oc "forall_tyvarl_term"; os oc " ";
      os oc "("; oiter oc " " sexpr_type tvl; os oc ")"; os oc " ";
      sexpr_term oc tm; os oc ")"
      )
  end

fun sexpr_constdef oc thy (name,ty) =
  (
  osn oc ("; c." ^ thy ^ "." ^ name ^ ": " ^ rm_endline (type_to_string ty));
  os oc "("; os oc "constant_definition"; os oc " ";
  os oc (sexprb_const (thy,name)); os oc " ";
  sexpr_tyquant_type oc ty; os oc ")\n"
  )

fun sexpr_thmdef oc thy ((name,thm),role) =
  let val tm = prep_thm thm in
    osn oc ("; " ^ thy ^ "." ^ name ^ ": " ^ rm_endline (term_to_string tm));
    os oc "("; os oc role; os oc " ";
    os oc (sexprb_thm (thy,name)); os oc " ";
    sexpr_tyquant_term oc tm; os oc ")\n"
  end

(* -------------------------------------------------------------------------
   Exporting theories using one of the format defined above.
   ------------------------------------------------------------------------- *)

val hh_dir = HOLDIR ^ "/src/holyhammer"
val sexpr_dir = hh_dir ^ "/export_sexpr"

val th1_bushy_dir = hh_dir ^ "/export_th1_bushy"
val th1_chainy_dir = hh_dir ^ "/export_th1_chainy"

val tf1_bushy_dir = hh_dir ^ "/export_tf1_bushy"
val tf1_chainy_dir = hh_dir ^ "/export_tf1_chainy"

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
    val filedep = export_dir ^ "/" ^ thy ^ ".dep"
    val file = export_dir ^ "/" ^ thy ^ ".pb"
    val oc = TextIO.openOut file
    val ocdep = TextIO.openOut filedep
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (f_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (f_constdef oc thy) cl
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

fun write_thyaxiom dir thy =
  let
    val file = dir ^ "/" ^ thy ^ ".ax"
    val oc = TextIO.openOut file
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (th1_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (th1_constdef oc) cl
      val axl0 = map (fn x => (x,"axiom")) (DB.thms thy)
      fun cmp (((_,th1),_),((_,th2),_)) =
        Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
      val axl1 = dict_sort cmp axl0
    in
      app (th1_thmdef oc thy) axl1;
      TextIO.closeOut oc
    end
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thydecl dir thy =
  let
    val file = dir ^ "/" ^ thy ^ "-decl.ax"
    val oc = TextIO.openOut file
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (th1_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (th1_constdef oc) cl
    in
      TextIO.closeOut oc
    end
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

(* -------------------------------------------------------------------------
   Combinator for making it less theorem decreasing. (i.e. complete)
   ------------------------------------------------------------------------- *)

fun write_combin (f_constdef,f_thmdef) dir = 
  let
    val file = dir ^ "/combin-extra.ax"
    val oc = TextIO.openOut file
  in
    let
      val _ = combin_extra_flag := true
      val cl0 = ["S","K","I"]
      val axl0 = map (fn x => x ^ "_DEF") cl0
      val thy = "combin"
      val THEORY(_,t) = dest_theory thy
      val cl1 = #consts t
      val cl2 = filter (fn x => mem (fst x) cl0) cl1
      val _ = app (f_constdef oc thy) cl2
      val axl1 = filter (fn x => mem (fst x) axl0) (DB.definitions thy)
      val axl2 = map (fn x => (x,"axiom")) axl1
    in
      app (f_thmdef oc thy) axl2;
      combin_extra_flag := false;
      TextIO.closeOut oc
    end 
    handle Interrupt => 
    (TextIO.closeOut oc; combin_extra_flag := false; raise Interrupt)
  end 

(*
fun tf1_top_cdef oc arity (tfname,ty) =
  (os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
   tf1_tyquant_type oc arity ty; osn oc ").")

fun write_tf1_app dir = 
  let
    val file = dir ^ "/app-extra.ax"
    val oc = TextIO.openOut file
  in
    let
      val ty = type_of (prim_mk_const {Thy = "bool", Name = "LET"})
      val tfname = "app_2"
    in
      tf1_top_cdef oc arity (tfname,ty);
      TextIO.closeOut oc
    end 
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end 
*)

(* -------------------------------------------------------------------------
   Logical operators equations with term level counterpart.
   ------------------------------------------------------------------------- *)

fun full_apply_const c =
  let 
    val (imty,argtyl) = strip_funty (type_of c)
    fun f i x = mk_var ("V" ^ its i,x)
    val vl = mapi f argtyl 
  in
    list_mk_comb (c,vl)
  end    

fun th1_logicformula oc (thy,name) = 
  let 
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o th1_vartype) tvl
    val s = String.concatWith ", " tvls
    val vl = free_vars_lr tm 
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    os oc "!["; oiter oc ", " th1_var_and_type vl; os oc "]: ";
    os oc "("; th1_term oc tm ; os oc " <=> "; th1_pred oc tm; os oc ")"
  end

val logicconstl_glob = 
  let fun f c = let val {Thy,Name,Ty} = dest_thy_const c in (Thy,Name) end in
    map f [``$/\``,``$\/``,``$~``,``$==>``,``$= : 'a -> 'a -> bool``]
  end
fun is_logicconst x = mem x logicconstl_glob


fun th1_logicdef oc (thy,name) =
  (
  os oc ("thf(" ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
  th1_logicformula oc (thy,name); osn oc ")."
  )

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

fun is_quantconst x = mem x [("bool","!"),("bool","?")]

fun th1_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val tm = concl thm
  in
    comment oc (term_to_string tm);
    os oc ("thf(" ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
    th1_formula oc tm; osn oc ")."
  end

fun write_boolextra dir = 
  let
    val file = dir ^ "/bool-extra.ax"
    val oc = TextIO.openOut file
  in
    (
    app (th1_logicdef oc) logicconstl_glob;
    app (th1_quantdef oc) [("bool","!"),("bool","?")];
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

(* -------------------------------------------------------------------------
   Bushy and chainy exports
   ------------------------------------------------------------------------- *)

val id_compare = cpl_compare String.compare String.compare

fun type_set tm = mk_type_set (map type_of (find_terms (fn _ => true) tm))
fun tyop_set topty = 
  let 
    val l = ref [] 
    fun loop ty = 
      if is_vartype ty then () else
      let val {Args,Thy,Tyop} = dest_thy_type ty in
        l := ((Thy,Tyop),length Args) :: !l; app loop Args 
      end
  in 
    loop topty; mk_fast_set (cpl_compare id_compare Int.compare) (!l)
  end

fun const_set tm = mk_term_set (find_terms is_const tm) 

fun write_cj_bushy thy ((name,thm),depl) =
  let 
    val file = th1_bushy_dir ^ "/" ^ th1b_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val pretml = map (prep_thm o thmfetch) depl
    val tml = mk_term_set (List.concat (map atoms_of pretml))
    val tyl = mk_type_set (List.concat (map type_set tml))
    val tyopl = mk_fast_set (cpl_compare id_compare Int.compare) 
      (List.concat (map tyop_set tyl))
    val cl = mk_term_set (List.concat (map const_set tml)) 
    fun ftyop ((tyopthy,tyopname),tyoparity) = 
      th1_tydef oc tyopthy (tyopname,tyoparity)
    fun fc c =
      let 
        val {Name=cname,Thy=cthy,...} = dest_thy_const c 
        val cid = (cthy,cname)
      in
        th1_constdef oc cid;
        (
        if is_logicconst cid then th1_logicdef oc cid
        else if is_quantconst cid then th1_quantdef oc cid
        else ()
        )
      end
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        th1_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app ftyop tyopl; app fc cl; app fax depl;
    th1_thmdef oc thy ((name,thm),"conjecture"); 
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun include_thy oc thy = osn oc ("include('" ^ thy ^ ".ax').")
fun include_thydecl oc thy = osn oc ("include('" ^ thy ^ "-decl.ax').")

fun write_thy_bushy thy =
  let 
    val cjl = DB.theorems thy
    fun f (name,thm) = case depo_of_thm thm of
        NONE => NONE
      | SOME depl => SOME ((name,thm), depl)
    val cjdepl = List.mapPartial f cjl
  in
    print (thy ^ " ");
    app (write_cj_bushy thy) cjdepl
  end 

fun before_elem e l = case l of
    [] => raise ERR "before_elem" ""
  | a :: m => if a = e then [] else a :: before_elem e m

fun older_than th1 (name,th2) = 
  depnumber_of_thm th2 < depnumber_of_thm th1

fun write_cj_chainy thyl thy (name,thm) =
  let 
    val file = th1_chainy_dir ^ "/" ^ th1b_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val axl0 = DB.thms thy
    val axl1 = filter (older_than thm) axl0
    fun cmp ((_,th1),(_,th2)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
    val axl2 = map (fn (x,_) => (thy,x)) (dict_sort cmp axl1)
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        th1_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app (include_thy oc) thyl;
    include_thydecl oc thy;
    include_thy oc "bool-extra";
    app fax axl2;
    th1_thmdef oc thy ((name,thm),"conjecture"); 
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_chainy thyl thy =
  let val thyl_before = before_elem thy thyl in
    print (thy ^ " ");
    app (write_cj_chainy thyl_before thy) (DB.theorems thy)
  end

(* -------------------------------------------------------------------------
   Export functions
   ------------------------------------------------------------------------- *)

fun add_ancestry thy = thy :: ancestry thy
fun sorted_ancestry thyl = 
  sort_thyl (mk_string_set (List.concat (map add_ancestry thyl)))

(* load_sigobj (); sort_thyl (ancestry "scratch"); *)
fun th1_export_bushy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err th1_bushy_dir; app write_thy_bushy thyl
  end

fun th1_export_chainy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err th1_chainy_dir; 
    write_boolextra th1_chainy_dir;
    app (write_thyaxiom th1_chainy_dir) thyl;
    app (write_thydecl th1_chainy_dir) thyl;
    app (write_thy_chainy thyl) thyl
  end

(*
fun th1_export thyl =
  let
    val file = th1_dir ^ "/theory_order.info"
    val fl = (th1_tydef, th1_constdef, th1_thmdef, th1b_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err th1_dir;
    write_combin fl th1_dir;
    write_logic th1_dir;
    app (write_thy fl th1_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

fun th1_export_decl thyl =
  let
    val fl = (th1_tydef, th1_constdef)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err th1_decl_dir; app (write_thy_decl fl th1_decl_dir) thyl
  end

fun th1_export_ax thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err th1_ax_dir; 
    app (write_thy_ax th1_thmdef th1_ax_dir) thyl
  end

fun tf1_export thyl =
  let
    val file = tf1_dir ^ "/theory_order.info"
    val fl = (tf1_tydef, tf1_constdef, tf1_thmdef, tf1b_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err tf1_dir;
    write_combin fl tf1_dir;
    write_logic tf1_dir;
    app (write_thy fl tf1_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

fun sexpr_export thyl =
  let
    val file = sexpr_dir ^ "/theory_order.info"
    val fl = (sexpr_tydef, sexpr_constdef, sexpr_thmdef, sexprb_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err sexpr_dir;
    app (write_thy fl sexpr_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

(* -------------------------------------------------------------------------
   fof
   ------------------------------------------------------------------------- *)

val fof_export_dir = HOLDIR ^ "/src/holyhammer/export_fof"
val fof_targets_file = fof_export_dir ^ "/fof_targets"
val fof_problems_dir = fof_export_dir ^ "/fof_problems"
val fof_chainy_dir = fof_export_dir ^ "/fof_chainy"

fun fof_export_pb (file,(premises,cj)) =
  (
  append_endline fof_targets_file file;
  translate_write_file file (premises,cj)
  )

fun fof_export_thy thy =
  let
    val _ = mkDir_err fof_export_dir
    val _ = mkDir_err fof_problems_dir
    val thml = DB.theorems thy
    val pbl1 = map_snd (fn x => (intactdep_of_thm x, x)) thml
    val pbl2 = filter (fn (_,x) => fst (fst x)) pbl1
    val pbl3 = map_snd (fn (a,b) => (snd a, list_mk_imp (dest_thm b))) pbl2
    val pbl4 = map_fst (fn x => fof_problems_dir ^ "/" ^ th1b_thm (thy,x)) pbl3
  in
    app fof_export_pb pbl4
  end
*)
(*
fun fof_export_statement_thy thy =
  let
    val _ = mkDir_err fof_export_dir
    val _ = mkDir_err fof_problems_dir
    val thml = DB.thms thy
    fun cmp ((_,th1),(_,th2)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
    val pbl1 = map_snd (fn x => ([], x)) thml
    val pbl3 = map_snd (fn (a,b) => (a, list_mk_imp (dest_thm b))) pbl1
    val pbl4 = map_fst (fn x => fof_problems_dir ^ "/" ^ sexpr_thm (thy,x)) pbl3
  in
    app fof_export_pb pbl4
  end
*)

end (* struct *)

(* Example
  load "hhExport"; open hhExport;
  th1_export_bushy ["list"];
  
  comment_flag := true;  

*)
