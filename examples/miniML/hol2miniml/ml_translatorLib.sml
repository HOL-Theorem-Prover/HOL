structure ml_translatorLib :> ml_translatorLib =
struct

open HolKernel boolLib bossLib;

open MiniMLTheory MiniMLTerminationTheory Print_astTerminationTheory;
open determTheory ml_translatorTheory;
open arithmeticTheory listTheory combinTheory pairTheory;
open integerTheory intLib ml_optimiseTheory;

infix \\ val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
val auto_print = true

(* a very quiet version of Define -- by Anthony Fox *)

val quietDefine = (* Define *)
  Lib.with_flag (Feedback.emit_ERR, false)
    (Lib.with_flag (Feedback.emit_MESG, false)
       (Feedback.trace ("auto Defn.tgoal", 0) TotalDefn.Define))

local
  val names = ref [""]
  fun find_name str n = let
    val new_name = str ^ "_" ^ (int_to_string n)
    in if mem new_name (!names) then find_name str (n+1) else new_name end
  fun find_new_name str =
    if mem str (!names) then find_name str 1 else str
in
  fun get_unique_name str = let
    val new_name = find_new_name str
    val _ = (names := new_name :: (!names))
    in new_name end
end

(* collecting declarations *)

local
  val decls = ref (tl [(T,"","")])
  fun print_str str = (print "\n"; print str; print "\n\n"; str)
  fun dec2str sml d = if not auto_print then "" else let
    val result =
      (if sml then ``dec_to_sml_string ^d`` else ``dec_to_ocaml_string ^d``)
      |> EVAL |> concl |> rand |> stringSyntax.fromHOLstring
      handle HOL_ERR _ => failwith("\nUnable to print "^(term_to_string d)^"\n\n")
    in result end;
in
  fun add_decl d = (decls := (d,print_str (dec2str true d), dec2str false d)::(!decls))
  fun get_decls () = rev (!decls)
end


(* printing output *)

val string2ident = let
  fun g c = if #"0" <= c andalso c <= #"9" then implode [c] else
            if #"a" <= c andalso c <= #"z" then implode [c] else
            if #"A" <= c andalso c <= #"Z" then implode [c] else
            if mem c [#"_"] then implode [c] else "C" ^ int_to_string (ord c)
  in String.translate g end

fun D th = let
  val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  in if is_imp (concl th) then th else DISCH T th end

local
  val base_filename = ref "";
  fun clear_file suffix = let
    val t = TextIO.openOut((!base_filename) ^ suffix)
    val _ = TextIO.closeOut(t)
    in () end
  fun get_filename () =
    if not auto_print then !base_filename else
    if !base_filename = "" then let
      val name = current_theory()
      val _ = (base_filename := name)
      val _ = clear_file "_ml.txt"
      val _ = clear_file "_ocaml.txt"
      val _ = clear_file "_hol.txt"
      val _ = clear_file "_thm.txt"
      in name end
    else !base_filename
  fun append_to_file suffix strs = let
    val t = TextIO.openAppend(get_filename() ^ suffix)
    val _ = map (fn s => TextIO.output(t,s)) strs
    val _ = TextIO.closeOut(t)
    in () end
  fun print_ml_file () = let
    val _ = clear_file "_ast.txt"
    val _ = clear_file "_ml.txt"
    val _ = clear_file "_ocaml.txt"
    fun print_decl (tm,s,s') = let
      val _ = append_to_file "_ast.txt" ["\n",term_to_string tm,"\n"]
      val _ = append_to_file "_ml.txt" ["\n",s,"\n"]
      val _ = append_to_file "_ocaml.txt" ["\n",s',"\n"]
      in () end
    val _ = map print_decl (get_decls())
    in () end
in
  fun print_results fname original_def th code_tm pre =
    if get_filename() = "" then () else let
      val filename = get_filename()
      val def_str = thm_to_string original_def
      val th_str = thm_to_string (D th |> REWRITE_RULE [GSYM CONJ_ASSOC,Eval_Var_EQ,PRECONDITION_def])
      val ml_str = term_to_string code_tm
     (* val _ = append_to_file "_ml.txt" ["\n" ^ fname ^ ":\n\n",ml_str,"\n"] *)
      val _ = append_to_file "_hol.txt" ["\n",def_str,"\n"]
      val _ = append_to_file "_thm.txt" ["\nCertificate theorem for "^fname^":\n\n",th_str,"\n"]
      val _ = case pre of NONE => ()
              | SOME pre_def => append_to_file "_thm.txt" ["\nDefinition of side condition for "^fname^":\n\n",thm_to_string pre_def,"\n"]
      val _ = print_ml_file ()
      in () end;
  fun print_inv_def inv_def = if get_filename() = "" then () else let
    val th_str = thm_to_string inv_def
    val _ = append_to_file "_thm.txt" ["\nDefinition of refinement invariant:\n\n",th_str,"\n"]
    in () end;
  fun clear_filename () = (base_filename := "")
  fun set_filename name = (base_filename := name;
    clear_file "_ocaml.txt"; clear_file "_ml.txt"; clear_file "_hol.txt"; clear_file "_thm.txt")
end

exception UnableToTranslate of term;
exception UnableToDefine of term;


(* mapping HOL types into corresponding invariants *)

exception UnsupportedType of hol_type;

fun dest_fun_type ty = let
  val (name,args) = dest_type ty
  in if name = "fun" then (el 1 args, el 2 args) else failwith("not fun type") end

local
  val type_mappings = ref ([]:(hol_type * hol_type) list)
  fun find_type_mapping ty =
    first (fn (t,_) => can (match_type t) ty) (!type_mappings)
  fun free_typevars ty =
    if can dest_vartype ty then [ty] else let
    val (name,tt) = dest_type ty
    in Lib.flatten (map free_typevars tt) end
    handle HOL_ERR _ => []
in
  fun add_new_type_mapping ty target_ty =
    (type_mappings := (ty,target_ty) :: (!type_mappings))
  fun type2t ty =
    if ty = ``:bool`` then ``Tbool`` else
    if ty = ``:int`` then ``Tnum`` else
    if ty = ``:num`` then ``Tnum`` else
    if can dest_vartype ty then
      mk_comb(``Tvar``,stringSyntax.fromMLstring (dest_vartype ty))
    else let
      val (lhs,rhs) = find_type_mapping ty
      val i = match_type lhs ty
      val xs = free_typevars rhs
      val i = filter (fn {redex = a, residue = _} => mem a xs) i
      val tm = type2t rhs
      val s = map (fn {redex = a, residue = b} => type2t a |-> type2t b) i
      in subst s tm end handle HOL_ERR _ =>
    let
      val (name,tt) = dest_type ty
      val tt = map type2t tt
      val name_tm = stringSyntax.fromMLstring name
      val tt_list = listSyntax.mk_list(tt,type_of ``Tbool``)
      in if name = "fun" then ``Tfn ^(el 1 tt) ^(el 2 tt)`` else
           ``Tapp ^tt_list ^name_tm`` end
end

local
  val other_types = ref (fn (ty:hol_type) => (fail()):term)
  val user_supplied_types = ref ([]:hol_type list)
in
  fun get_type_inv ty =
    if is_vartype ty then let
      val name = dest_vartype ty |> explode |> tl |> implode
      in mk_var(name,mk_type("fun",[ty,``:v->bool``])) end else
    if can dest_fun_type ty then let
      val (t1,t2) = dest_fun_type ty
      in ``Arrow (^(get_type_inv t1)) (^(get_type_inv t2))`` end else
    if ty = ``:bool`` then ``BOOL`` else
    if ty = ``:num`` then ``NUM`` else
    if ty = ``:int`` then ``INT`` else
      (!other_types) ty handle HOL_ERR _ => raise UnsupportedType ty
  fun new_type_inv f = let
    val old = (!other_types)
    in (other_types := (fn y => (f y handle HOL_ERR _ => old y))) end
  fun add_type_inv tm target_ty = let
    val ty = fst (dest_fun_type (type_of tm))
    val _ = add_new_type_mapping ty target_ty
    val _ = user_supplied_types := ty::(!user_supplied_types)
    val f = (fn x => if x = ty then tm else fail())
    in new_type_inv f end
  fun get_user_supplied_types () = (!user_supplied_types)
end


(* support for user-defined data-types *)

fun type_of_cases_const ty = let
  val th = TypeBase.case_def_of ty
  val ty = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
              |> concl |> dest_eq |> fst |> rator |> type_of
  in ty end

fun name_of_type ty = let
  val th = TypeBase.case_def_of ty
  val case_const = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                      |> concl |> dest_eq |> fst |> repeat rator
  val name = case_const |> dest_const |> fst |> explode |> rev
                        |> funpow 5 tl |> rev |> implode
  in name end;

fun remove_primes th = let
  fun last s = substring(s,size s-1,1)
  fun delete_last_prime s = if last s = "'" then substring(s,0,size(s)-1) else fail()
  fun foo [] ys i = i
    | foo (x::xs) ys i = let
      val name = (fst o dest_var) x
      val new_name = repeat delete_last_prime name
      in if name = new_name then foo xs (x::ys) i else let
        val new_var = mk_var(new_name,type_of x)
        in foo xs (new_var::ys) ((x |-> new_var) :: i) end end
  val i = foo (free_varsl (concl th :: hyp th)) [] []
  in INST i th end

fun get_nchotomy_of ty = let (* ensures that good variables names are used *)
  val case_th = TypeBase.nchotomy_of ty
  val ty0 = type_of (hd (SPEC_ALL case_th |> concl |> free_vars))
  val case_th = INST_TYPE (match_type ty0 ty) case_th
  val xs = map rand (find_terms is_eq (concl case_th))
  val x_var = mk_var("x",ty)
  fun mk_lines [] = []
    | mk_lines (x::xs) = let
    val k = length xs + 1
    fun rename [] = []
      | rename (x::xs) = let val n = int_to_string k ^ "_" ^
                                     int_to_string (length xs + 1)
                          in (x,mk_var("x" ^ n, type_of x),
                                mk_var("v" ^ n,``:v``)) end :: rename xs
    val vars = rev (rename (free_vars x))
    val new_x = subst (map (fn (x,y,z) => x |-> y) vars) x
    val tm = list_mk_exists(rev (free_vars new_x), mk_eq(x_var,new_x))
    in tm :: mk_lines xs end
  val goal = mk_forall(x_var,list_mk_disj (rev (mk_lines xs)))
  val lemma = prove(goal,
    STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x` case_th)
    \\ FULL_SIMP_TAC (srw_ss()) []);
  in lemma end

(*
val ty = ``:'a list``
val ty = ``:'a # 'b``
val ty = ``:unit``
val _ = Hol_datatype `TREE = LEAF of 'a | BRANCH of TREE => TREE`;
register_type ty
val _ = Hol_datatype `BTREE = BLEAF of ('a TREE) | BBRANCH of BTREE => BTREE`;
val ty = ``:'a BTREE``
*)

fun clean_lowercase s = let
  fun f c = if #"a" <= c andalso c <= #"z" then implode [c] else
            if #"A" <= c andalso c <= #"Z" then implode [chr (ord c + 32)] else
            if mem c [#"_",#"'"] then implode [c] else ""
  in String.translate f s end;

fun clean_uppercase s = let
  fun f c = if #"a" <= c andalso c <= #"z" then implode [chr (ord c - 32)] else
            if #"A" <= c andalso c <= #"Z" then implode [c] else
            if mem c [#"_",#"'"] then implode [c] else ""
  in String.translate f s end;

fun tag_name type_name const_name = let
  val x = clean_lowercase type_name
  val y = clean_lowercase const_name
  fun upper_case_hd s =
    clean_uppercase (implode [hd (explode s)]) ^ implode (tl (explode s))
  in if y = "" then upper_case_hd x else upper_case_hd y end

local
  val inv_defs = ref (tl [(alpha,TRUTH)])
in
  fun get_inv_def ty = snd (first (fn (t,_) => t = ty) (!inv_defs))
  fun set_inv_def (ty,inv_def) = (inv_defs := (ty,inv_def) :: (!inv_defs))
end

val last_def_fail = ref T

fun dest_args tm =
  let val (x,y) = dest_comb tm in dest_args x @ [y] end
  handle HOL_ERR _ => []

fun derive_record_specific_thms ty = let
  val ty_name = name_of_type ty
  val access_funs =
    TypeBase.accessors_of ty
    |> map (rator o fst o dest_eq o concl o SPEC_ALL)
  val update_funs =
    TypeBase.updates_of ty
    |> map (rator o rator o fst o dest_eq o concl o SPEC_ALL)
  val tm =
    DB.fetch "-" (ty_name ^ "_11")
    |> SPEC_ALL |> concl |> dest_eq |> fst |> dest_eq |> fst
  val xs = dest_args tm
  val c = repeat rator tm
  val case_tm =
    DB.fetch "-" (ty_name ^ "_case_cong")
    |> SPEC_ALL |> UNDISCH_ALL |> concl |> dest_eq |> fst |> repeat rator
  fun prove_accessor_eq (a,x) = let
     val v = mk_var("v",type_of tm)
     val f = foldr (fn (v,tm) => mk_abs(v,tm)) x xs
     val ty1 = case_tm |> type_of |> dest_type  |> snd |> hd
     val i = match_type ty1 (type_of f)
     val rhs = mk_comb(mk_comb(inst i case_tm,f),v)
     val lhs = mk_comb(a,v)
     val goal = mk_forall(v,mk_eq(lhs,rhs))
     val lemma = prove(goal,Cases THEN SRW_TAC [] [])
     in lemma end
  val a_lemmas = map prove_accessor_eq (zip access_funs xs)
  fun prove_updates_eq (a,x) = let
     val v = mk_var("v",type_of tm)
     val t = type_of x
     val g = mk_var("g",mk_type("fun",[t,t]))
     val f = foldr mk_abs (subst [x|->mk_comb(g,x)] tm) xs
     val ty1 = case_tm |> type_of |> dest_type  |> snd |> hd
     val i = match_type ty1 (type_of f)
     val rhs = mk_comb(mk_comb(inst i case_tm,f),v)
     val lhs = mk_comb(mk_comb(a,g),v)
     val goal = mk_forall(v,mk_forall(g,mk_eq(lhs,rhs)))
     val tac = Cases THEN SRW_TAC [] [DB.fetch "-" (ty_name ^ "_fn_updates")]
     in prove(goal,tac) end
  val b_lemmas = map prove_updates_eq (zip update_funs xs)
  val arb = mk_arb(type_of tm)
  val tm2 = foldr (fn ((a,x),y) => mk_comb(``^a (K ^x)``,y)) arb (zip update_funs xs)
  val goal = mk_eq(tm2,tm)
  val rw_lemma = prove(goal,SRW_TAC [] [DB.fetch "-" (ty_name ^ "_component_equality")])
  val rw_lemmas = CONJ (DB.fetch "-" (ty_name ^ "_fupdcanon")) rw_lemma
  in (a_lemmas @ b_lemmas, [rw_lemmas]) end

fun derive_thms_for_type ty = let
  val (ty,ret_ty) = dest_fun_type (type_of_cases_const ty)
  val case_of_th = TypeBase.case_def_of ty
  val is_record = 0 < length(TypeBase.fields_of ty)
  val name = if is_record then name_of_type ty ^ "_record" else name_of_type ty
  val _ = print ("Adding type " ^ type_to_string ty ^ "\n")
  (* derive case theorem *)
  val case_th = get_nchotomy_of ty
  (* define a MiniML datatype declaration *)
  val dtype = let
    val xs = map rand (find_terms is_eq (concl case_th))
    val y = hd (map (fst o dest_eq) (find_terms is_eq (concl case_th)))
    fun mk_line x = let
      val tag = tag_name name (repeat rator x |> dest_const |> fst)
      val ts = map (type2t o type_of) (dest_args x)
      val tm = pairSyntax.mk_pair(stringSyntax.fromMLstring tag,
                 listSyntax.mk_list(ts,type_of ``Tbool``))
      in tm end
    val lines = listSyntax.mk_list(map mk_line xs,``:tvarN # t list``)
    val (name,ts) = dest_type (type_of y)
    val ts = map (stringSyntax.fromMLstring o dest_vartype) ts
    val ts_tm = listSyntax.mk_list(ts,``:string``)
    val name_tm = stringSyntax.fromMLstring name
    val dtype = ``Dtype [(^ts_tm,^name_tm,^lines)]``
    in dtype end
  (* define coupling invariant for data refinement *)
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
  fun define_abs name ty case_th = let
    val xs = map rand (find_terms is_eq (concl case_th))
    val ty = type_of (hd (SPEC_ALL case_th |> concl |> free_vars))
    val vars = type_vars ty
    val ss = map get_type_inv vars
    val input = mk_var("input",ty)
    val def_name = mk_var(name,list_mk_type (ss @ [input]) ``:v -> bool``)
    val lhs = foldl (fn (x,y) => mk_comb(y,x)) def_name (ss @ [input,``v:v``])
    fun mk_lines [] = []
      | mk_lines (x::xs) = let
      val k = length xs + 1
      val tag = tag_name name (repeat rator x |> dest_const |> fst)
      fun rename [] = []
        | rename (x::xs) = let val n = int_to_string k ^ "_" ^
                                       int_to_string (length xs + 1)
                           in (x,mk_var("v" ^ n,``:v``)) end :: rename xs
      val vars = rev (rename (free_vars x))
      val ty_list = mk_type("list",[ty])
      val list_ty = ``:(^ty -> v -> bool) -> ^ty list -> v -> bool``
      fun find_inv tm =
        if type_of tm = ty then (subst [input|->tm] (rator lhs)) else
        if type_of tm = ty_list then mk_comb(mk_comb(mk_const("list",list_ty),rator (rator lhs)),tm) else
          (mk_comb(get_type_inv (type_of tm),tm))
      val ys = map (fn (y,z) => mk_comb(find_inv y,z)) vars
      val tm = if ys = [] then T else list_mk_conj ys
      val str = stringLib.fromMLstring tag
      val vs = listSyntax.mk_list(map (fn (_,z) => z) vars,``:v``)
      val tm = mk_conj(``v = Conv (SOME ^str) ^vs``,tm)
      val tm = list_mk_exists (map (fn (_,z) => z) vars, tm)
      val tm = subst [input |-> x] (mk_eq(lhs,tm))
      val vs = filter (fn x => x <> def_name) (free_vars tm)
      in tm :: mk_lines xs end
    val inv_def = quietDefine [ANTIQUOTE (list_mk_conj (rev (mk_lines xs)))]
                  handle HOL_ERR _ =>
                  get_inv_def ty
                  handle HOL_ERR _ =>
                  ((last_def_fail := (list_mk_conj (rev (mk_lines xs))));
                   raise UnableToDefine (list_mk_conj (rev (mk_lines xs))))
    in inv_def end
  val inv_def = define_abs name ty case_th
  val _ = print_inv_def inv_def
  val inv_lhs = inv_def |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                        |> dest_eq |> fst
  (* prove EqualityType lemma, e.g. !a. EqualityType a ==> EqualityType (list a) *)
  val eq_lemma = if can get_inv_def ty then TRUTH else let
    val tm = rator (rator inv_lhs)
    fun list_dest f tm = let val (x,y) = f tm
                         in list_dest f x @ list_dest f y end handle HOL_ERR _ => [tm]
    val xs =
      inv_def |> RW [GSYM CONJ_ASSOC] |> SPEC_ALL |> CONJUNCTS
              |> map (snd o dest_eq o concl o SPEC_ALL)
              |> map (last o list_dest dest_exists)
              |> map (tl o list_dest dest_conj) |> Lib.flatten
              |> map (rator o rator) |> filter (fn t => t <> tm)
    val ys = map (fn tm => ``EqualityType ^tm``) xs
    val tm1 = ``EqualityType ^tm``
    val tm2 = if ys = [] then T else list_mk_conj ys
    val goal = mk_imp(tm2,tm1)
    val eq_lemma = prove(goal,
      REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [EqualityType_def]
      \\ STRIP_TAC THEN1
       (REPEAT (Q.PAT_ASSUM `!x1 x2 x3 x4. bbb` (K ALL_TAC))
        \\ (Induct ORELSE Cases)
        \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS]
        \\ REPEAT STRIP_TAC \\ RES_TAC)
      THEN1
       (REPEAT (Q.PAT_ASSUM `!x1 x2. bbb ==> bbbb` (K ALL_TAC))
        \\ (Induct ORELSE Cases)
        \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS]
        \\ Cases_on `x2` \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS]
        \\ REPEAT STRIP_TAC \\ METIS_TAC []))
    in eq_lemma end handle HOL_ERR _ => TRUTH
  (* make new inv_def part of get_type_inv *)
  val inv = rator (rator inv_lhs)
  fun extension_to_get_inv_type ty0 = let
    val i = match_type ty ty0
    val ii = map (fn {redex = x, residue = y} => (x,y)) i
    val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
    in subst ss (inst i inv) end
  val _ = new_type_inv extension_to_get_inv_type
  (* prove lemma for case_of *)
  val (case_lemma,ts) = let
    val cases_th = case_of_th
    val cases_tm =
      cases_th |> CONJUNCTS |> hd |> concl |> repeat (snd o dest_forall)
               |> dest_eq |> fst |> rator
    fun rename [] = []
      | rename (x::xs) = let val k = "f" ^ int_to_string (length xs + 1)
                         in (x,mk_var(k,type_of x)) :: rename xs end
    val vs = rev (rename (free_vars cases_tm))
    val cases_tm = subst (map (fn (x,y) => x |-> y) vs) cases_tm
    val input_var = mk_var("x",ty)
    val exp = mk_comb(cases_tm,input_var)
    val ret_ty = type_of exp
    val xs = rev (map rand (find_terms is_eq (concl case_th)))
    fun add_nums [] = []
      | add_nums (x::xs) = (x,length xs+1) :: add_nums xs
    val ys = rev (add_nums (rev (zip (map snd vs) xs)))
    fun str_tl s = implode (tl (explode s))
    fun list_app x [] = x
      | list_app x (y::ys) = list_app (mk_comb(x,y)) ys
    fun mk_vars ((f,tm),n) = let
      val xs = rev (free_vars tm)
      val fxs = list_app f xs
      val pxs = list_app (mk_var("b" ^ int_to_string n,list_mk_type xs ``:bool``)) xs
      val xs = map (fn x => let val s = str_tl (fst (dest_var x)) in
                            (x,mk_var("n" ^ s,``:string``),
                               mk_var("v" ^ s,``:v``)) end) xs
      val exp = mk_var("exp" ^ int_to_string n, ``:exp``)
      in (n,f,fxs,pxs,tm,exp,xs) end
    val ts = map mk_vars ys
    (* patterns *)
    val patterns = map (fn (n,f,fxs,pxs,tm,exp,xs) => let
      val str = tag_name name (repeat rator tm |> dest_const |> fst)
      val str = stringSyntax.fromMLstring str
      val vars = map (fn (x,n,v) => ``Pvar ^n``) xs
      val vars = listSyntax.mk_list(vars,``:pat``)
      in ``(Pcon (SOME ^str) ^vars, ^exp)`` end) ts
    val patterns = listSyntax.mk_list(patterns,``:pat # exp``)
    val ret_inv = get_type_inv ret_ty
    val result = mk_comb(ret_inv,exp)
    val exp_var = mk_var("exp", ``:exp``)
    val result = ``Eval env (Mat ^exp_var ^patterns) ^result``
    (* assums *)
    val vs = map (fn (n,f,fxs,pxs,tm,exp,xs) => map (fn (x,_,_) => x) xs) ts |> flatten
    val b0 = mk_var("b0",``:bool``)
    fun mk_container tm = mk_comb(``CONTAINER:bool->bool``,tm)
    val tm = b0::map (fn (n,f,fxs,pxs,tm,exp,xs) => mk_imp(mk_container(mk_eq(input_var,tm)),pxs)) ts
             |> list_mk_conj
    val tm = list_mk_forall(vs,tm)
    val result = mk_imp(``TAG () ^tm``,result)
    (* tags *)
    fun find_inv tm =
      if type_of tm = ty then (mk_comb(rator (rator inv_lhs),tm)) else
        (mk_comb(get_type_inv (type_of tm),tm))
    fun mk_hyp (n,f,fxs,pxs,tm,exp,xs) = let
      val env = mk_var("env",``:envE``)
      val env = foldr (fn ((x,n,v),y) =>
        listSyntax.mk_cons(pairSyntax.mk_pair(n,v),y)) env (rev xs)
      val tm = map (fn (x,n,v) => mk_comb(find_inv x,v)) xs @ [pxs]
      val tm = if tm = [] then T else list_mk_conj tm
      val tm = mk_imp(tm,``Eval ^env ^exp (^ret_inv ^fxs)``)
      val vs = map (fn (x,_,_) => x) xs @ map (fn (_,_,v) => v) xs
      val tm = list_mk_forall(vs,tm)
      val n = numSyntax.term_of_int n
      val tm = ``TAG ^n ^tm``
      in tm end;
    (* all_distincts *)
    fun mk_alld (n,f,fxs,pxs,tm,exp,xs) = let
      val tt = listSyntax.mk_list(map (fn (_,x,_) => x) xs,``:string``)
      val tt = mk_comb(``ALL_DISTINCT:string list -> bool``,tt)
      in tt end
    val tt = list_mk_conj(map mk_alld ts) handle HOL_ERR _ => T
    (* goal *)
    val hyps = map mk_hyp ts
    val x = mk_comb(rator (rator inv_lhs),input_var)
    val hyp0 = ``TAG 0 (b0 ==> Eval env ^exp_var ^x)``
    val hyps = list_mk_conj(hyp0::hyps)
    val goal = mk_imp(tt,mk_imp(hyps,result))
    val init_tac =
          PURE_REWRITE_TAC [CONTAINER_def]
          \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x` case_th)
    fun case_tac n =
          Q.PAT_ASSUM `TAG 0 bbb` (MP_TAC o REWRITE_RULE [TAG_def,inv_def,Eval_def])
          \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
          \\ Q.PAT_ASSUM `TAG () bbb` (STRIP_ASSUME_TAC o remove_primes o
               SPEC_ALL o REWRITE_RULE [TAG_def,inv_def,Eval_def])
          \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT] \\ FULL_SIMP_TAC std_ss [inv_def]
          \\ Q.PAT_ASSUM `TAG ^(numSyntax.term_of_int n) bbb`
               (STRIP_ASSUME_TAC o REWRITE_RULE [TAG_def])
          \\ REPEAT (Q.PAT_ASSUM `TAG xxx yyy` (K ALL_TAC))
          \\ POP_ASSUM (MP_TAC o remove_primes o SPEC_ALL o REWRITE_RULE [Eval_def])
          \\ FULL_SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
          \\ Q.EXISTS_TAC `res'` \\ FULL_SIMP_TAC std_ss []
          \\ ASM_SIMP_TAC (srw_ss()) []
          \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
          \\ Q.EXISTS_TAC `res` \\ FULL_SIMP_TAC std_ss []
          \\ NTAC 10 (ASM_SIMP_TAC (srw_ss())
               [Once evaluate'_cases,pmatch'_def,bind_def,pat_bindings_def])
    val tac = init_tac THENL (map (fn (n,f,fxs,pxs,tm,exp,xs) => case_tac n) ts)
    val case_lemma = prove(goal,tac)
    val case_lemma = case_lemma |> PURE_REWRITE_RULE [TAG_def]
    in (case_lemma,ts) end;
  (* prove lemmas for constructors *)
  fun derive_cons (n,f,fxs,pxs,tm,exp,xs) = let
    val pat = tm
    fun str_tl s = implode (tl (explode s))
    val exps = map (fn (x,_,_) => (x,mk_var("exp" ^ str_tl (fst (dest_var x)), ``:exp``))) xs
    val tag = tag_name name (repeat rator tm |> dest_const |> fst)
    val str = stringLib.fromMLstring tag
    val exps_tm = listSyntax.mk_list(map snd exps,``:exp``)
    val inv = inv_lhs |> rator |> rator
    val result = ``Eval env (Con (SOME ^str) ^exps_tm) (^inv ^tm)``
    fun find_inv tm =
      if type_of tm = ty then (mk_comb(rator (rator inv_lhs),tm)) else
        (mk_comb(get_type_inv (type_of tm),tm))
    val tms = map (fn (x,exp) => ``Eval env ^exp ^(find_inv x)``) exps
    val tm = if tms = [] then T else list_mk_conj tms
    val goal = mk_imp(tm,result)
    fun add_primes str 0 = []
      | add_primes str n = mk_var(str,``:v``) :: add_primes (str ^ "'") (n-1)
    val witness = listSyntax.mk_list(add_primes "res" (length xs),``:v``)
    val lemma = prove(goal,
      SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
      \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) [PULL_EXISTS]
      \\ EXISTS_TAC witness \\ ASM_SIMP_TAC (srw_ss()) [inv_def,evaluate_list_SIMP])
    in (pat,lemma) end;
  val conses = map derive_cons ts
  val _ = add_decl dtype
  val (rws1,rws2) = if not is_record then ([],[]) else derive_record_specific_thms ty
  in (rws1,rws2,(ty,eq_lemma,inv_def,conses,case_lemma,ts)) end

local
  val translator = ref (fn th => I (th:thm))
  fun do_translate th = (!translator) th
  val preprocessor_rws = ref ([]:thm list)
  val memory = ref []
  val user_defined_eq_lemmas = ref []
  fun add_type ty = let
    val (rws1,rws2,res) = derive_thms_for_type ty
    val _ = (memory := res :: (!memory))
    val _ = (preprocessor_rws := rws2 @ (!preprocessor_rws))
    val _ = map do_translate rws1
    in res end
  fun lookup ty = first (fn (ty1,_,_,_,_,_) => can (match_type ty1) ty) (!memory)
  fun lookup_type ty = lookup ty handle HOL_ERR _ => add_type ty
  fun conses_of ty = let
    val (ty,eq_lemma,inv_def,conses,case_lemma,ts) = lookup ty
    in conses end
  fun stored_eq_lemmas () =
    map (fn (ty,eq_lemma,inv_def,conses,case_lemma,ts) => eq_lemma) (!memory)
  val init_eq_lemmas = map (DISCH T) (CONJUNCTS EqualityType_NUM_BOOL)
in
  fun get_preprocessor_rws () = !preprocessor_rws
  fun set_translator t = (translator := t)
  fun register_type ty =
    (lookup_type ty; ())
    handle UnsupportedType ty1 => (register_type ty1; register_type ty)
  fun cons_for tm = let
    val ty = type_of tm
    val conses = conses_of ty
    val (pat,th) = first (fn (x,th) => can (match_term x) tm) conses
    val i = snd (match_term pat tm)
    val ii = map (fn {redex = x, residue = y} => (x,y)) i
    val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
    in INST ss (INST_TYPE i th) end
    handle HOL_ERR _ => failwith("Not a constructor for a registered type.")
  fun case_of ty = let
    val (ty,eq_lemma,inv_def,conses,case_lemma,ts) = lookup ty
    in (case_lemma,ts) end
  fun eq_lemmas () =
    init_eq_lemmas @ filter (fn th => concl th <> T) (stored_eq_lemmas())
                   @ (!user_defined_eq_lemmas)
  fun store_eq_thm th = ((user_defined_eq_lemmas := th::(!user_defined_eq_lemmas));th)
end

fun register_term_types tm = let
  fun every_term f tm =
    ((if is_abs tm then every_term f (snd (dest_abs tm)) else
      if is_comb tm then (every_term f (rand tm); every_term f (rator tm)) else ()); f tm)
  val special_types = [``:num``,``:int``,``:bool``] @ get_user_supplied_types ()
  fun ignore_type ty =
    if can (first (fn ty1 => can (match_type ty1) ty)) special_types then true else
    if not (can dest_type ty) then true else
    if can (dest_fun_type) ty then true else false
  fun register_term_type tm = let
    val ty = type_of tm
    in if ignore_type ty then () else register_type ty
    end
  in every_term register_term_type tm end;

(* tests:
register_type ``:'a list``;
register_type ``:'a + num``;
register_type ``:num option``;
register_type ``:unit``;
*)

fun inst_cons_thm tm hol2deep = let
  val th = cons_for tm |> UNDISCH_ALL
  val res = th |> concl |> rand |> rand
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val xs = args res
  val ss = fst (match_term res tm)
  val ys = map (fn x => hol2deep (subst ss x)) xs
  val th1 = if length ys = 0 then TRUTH else LIST_CONJ ys
  in MATCH_MP (D th) th1 end

fun inst_case_thm_for tm = let
  val (_,_,names) = TypeBase.dest_case tm
  val names = map fst names
  val (th,ts) = case_of (type_of (rand tm))
  val pat = th |> UNDISCH_ALL |> concl |> rand |> rand
  val (ss,i) = match_term pat tm
  val th = INST ss (INST_TYPE i th)
  val ii = map (fn {redex = x, residue = y} => (x,y)) i
  val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
  val th = INST ss th
  val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val ns = map (fn n => (n,args n)) names
  val ns = map (fn (n,f,fxs,pxs,tm,exp,xs) => let
      val aa = snd (first (fn (pat,_) => can (match_term tm) pat) ns)
      in zip aa xs end) ts |> flatten
  val ms = map (fn (b,(x,n,v)) => n |-> stringSyntax.fromMLstring (fst (dest_var b))) ns
  val th = INST ms th
  val ks = map (fn (b,(x,n,v)) => (fst (dest_var x), fst (dest_var b))) ns @
           map (fn (b,(x,n,v)) => (fst (dest_var v), fst (dest_var b) ^ "{value}")) ns
  fun rename_bound_conv tm = let
    val (v,x) = dest_abs tm
    val (s,ty) = dest_var v
    val new_s = snd (first (fn (z,_) => z = s) ks)
    in ALPHA_CONV (mk_var(new_s,ty)) tm end handle HOL_ERR _ => NO_CONV tm
  val th = CONV_RULE (DEPTH_CONV rename_bound_conv) th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th
  val th = MP th TRUTH
  in th end;

val sat_hyp_lemma = prove(
  ``(b1 ==> (x1 = x2)) /\ (x1 ==> y) ==> b1 /\ x2 ==> y``,
  Cases_on `b1` \\ Cases_on `x1` \\ Cases_on `x2` \\ Cases_on `y` \\ EVAL_TAC);

val last_fail = ref T;
(*
  val tm = !last_fail
*)

fun inst_case_thm tm hol2deep = let
  val th = inst_case_thm_for tm
  val th = CONV_RULE (RATOR_CONV (PURE_REWRITE_CONV [CONJ_ASSOC])) th
  val (hyps,rest) = dest_imp (concl th)
  fun list_dest_forall tm = let
    val (v,tm) = dest_forall tm
    val (vs,tm) = list_dest_forall tm
    in (v::vs,tm) end handle HOL_ERR _ => ([],tm)
  fun take 0 xs = [] | take n xs = hd xs :: take (n-1) (tl xs)
  fun sat_hyp tm = let
    val (vs,x) = list_dest_forall tm
    val (x,y) = dest_imp x
    val z = y |> rand |> rand
    val lemma = hol2deep z
    val lemma = D lemma
    val new_env = y |> rator |> rator |> rand
    val env = mk_var("env",``:envE``)
    val lemma = INST [env|->new_env] lemma
    val (x1,x2) = dest_conj x handle HOL_ERR _ => (T,x)
    val (z1,z2) = dest_imp (concl lemma)
    val thz =
      QCONV (SIMP_CONV std_ss [ASSUME x1,Eval_Var_SIMP] THENC
             DEPTH_CONV stringLib.string_EQ_CONV THENC
             SIMP_CONV std_ss []) z1 |> DISCH x1
    val lemma = MATCH_MP sat_hyp_lemma (CONJ thz lemma)
    val bs = take (length vs div 2) vs
    fun LIST_UNBETA_CONV [] = ALL_CONV
      | LIST_UNBETA_CONV (x::xs) =
          UNBETA_CONV x THENC RATOR_CONV (LIST_UNBETA_CONV xs)
    val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
                  (LIST_UNBETA_CONV (rev bs))) lemma
    val lemma = GENL vs lemma
    val _ = can (match_term tm) (concl lemma) orelse failwith("sat_hyp failed")
    in lemma end handle HOL_ERR _ => (print_term tm; last_fail := tm; fail())
  fun sat_hyps tm = if is_conj tm then let
    val (x,y) = dest_conj tm
    in CONJ (sat_hyps x) (sat_hyps y) end else sat_hyp tm
  val lemma = sat_hyps hyps
  val th = MATCH_MP th lemma
  val th = CONV_RULE (RATOR_CONV (DEPTH_CONV BETA_CONV THENC
                                  REWRITE_CONV [])) th
  in th end;

fun SIMP_EqualityType_ASSUMS th = let
  val lemmas = eq_lemmas () |> map (UNDISCH_ALL o RW [GSYM AND_IMP_INTRO])
  val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val xs = map (fn th => (concl th,th)) lemmas
  fun find_match [] tm = fail()
    | find_match ((pat,th1)::xs) tm = let
        val (ss,i) = match_term pat tm
        in INST ss (INST_TYPE i th1) end
        handle HOL_ERR _ => find_match xs tm
  fun remove_one th = let
    val hs = hyp th
    val tm = first (can (find_match xs)) hs
    val lemma = find_match xs tm
    val th = MP (DISCH tm th) lemma
    in remove_one th end handle HOL_ERR _ => th
  in remove_one th end;

(* The preprocessor -- returns (def,ind). Here def is the original
   definition stated as a single line:

     foo v1 v2 v3 ... vN = RHS

   where vi are variables. The second return value is an option type:
   if NONE then foo is not recursive, if SOME th then th is an
   induction theorem that matches the structure of foo. *)

fun pattern_complete def vs = let
  val lines = def |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL
                  |> map (fst o dest_eq o concl)
  val const = hd lines |> repeat rator
  val ws = map (fn v => (v,genvar (type_of v))) vs
  val tm = foldl (fn (x,y) => mk_comb(y,snd x)) const ws
  fun tt line = let
    val i = fst (match_term tm line)
    val x = list_mk_exists(rev (free_vars line),
              list_mk_conj (map (fn v => mk_eq(snd v,subst i (snd v))) ws))
    in x end
  val pat_tm = list_mk_disj (map tt lines)
  val pat_tm = subst (map (fn (y,x) => x |-> y) ws) pat_tm
  val pre_tm = ``PRECONDITION ^pat_tm``
  in pre_tm end

fun single_line_def def = let
  val lhs = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                |> concl |> dest_eq |> fst
  val const = lhs |> repeat rator
  fun mk_container tm = ``CONTAINER ^tm``
  in if filter (not o is_var) (dest_args lhs) = [] then (def,NONE) else let
  val name = const |> dest_const |> fst
  val thy = #Thy (dest_thy_const const)
  val rw = fetch thy (name ^ "_curried_def")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_curried_DEF")
           handle HOL_ERR _ => let
           val arg = mk_var("x",const |> type_of |> dest_type |> snd |> hd)
           in REFL (mk_comb(const,arg)) end
  val tpc = rw |> SPEC_ALL |> concl |> dest_eq |> snd |> rator
  val args = rw |> SPEC_ALL |> concl |> dest_eq |> snd |> rand
  val tp = fetch thy (name ^ "_tupled_primitive_def")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_tupled_primitive_DEF")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_primitive_def")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_primitive_DEF")
  val (v,tm) = tp |> concl |> rand |> rand |> dest_abs
  val goal = mk_eq(mk_comb(tpc,args),mk_comb(subst [v|->tpc] tm,args))
  val pre_tm =
    if not (can (find_term is_arb) tm) then T else let
      val vs = rw |> SPEC_ALL |> concl |> dest_eq |> fst |> dest_args
      val pre_tm = pattern_complete def vs
      in pre_tm end
  val goal = mk_imp(pre_tm,goal)
  val lemma = prove(goal,
    SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,GSYM rw]
    \\ REPEAT STRIP_TAC
    \\ CONV_TAC (BINOP_CONV (REWR_CONV (GSYM CONTAINER_def)))
    \\ SRW_TAC [] []
    \\ REPEAT BasicProvers.FULL_CASE_TAC
    \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [def]))
    \\ SRW_TAC [] []
    \\ POP_ASSUM MP_TAC \\ REWRITE_TAC [PRECONDITION_def])
  val lemma = lemma |> RW [] |> UNDISCH_ALL
  val new_def =
    rw |> SPEC_ALL |> CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [lemma]))
       |> CONV_RULE (RAND_CONV BETA_CONV)
       |> REWRITE_RULE [I_THM]
       |> ONCE_REWRITE_RULE [GSYM rw]
  in (new_def,NONE) end handle HOL_ERR _ => let
  val v = mk_var("generated_definition",mk_type("fun",[``:unit``,type_of const]))
  val lemma  = def |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
  val def_tm = (subst [const|->mk_comb(v,``()``)] (concl lemma))
  val _ = quietDefine [ANTIQUOTE def_tm]
  val curried = fetch "-" "generated_definition_curried_def"
  val c = curried |> SPEC_ALL |> concl |> dest_eq |> snd |> rand
  val c2 = curried |> SPEC_ALL |> concl |> dest_eq |> fst
  val c1 = curried |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  val tupled = fetch "-" "generated_definition_tupled_primitive_def"
  val ind = fetch "-" "generated_definition_ind"
            |> Q.SPEC `\x. very_unlikely_name`
            |> CONV_RULE (DEPTH_CONV BETA_CONV)
            |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss []))
            |> Q.GEN `very_unlikely_name`
  val cc = tupled |> concl |> dest_eq |> fst
  val (v,tm) = tupled |> concl |> rand |> rand |> dest_abs
  val (a,tm) = dest_abs tm
  val tm = (REWRITE_CONV [GSYM FALSE_def,GSYM TRUE_def] THENC
            SIMP_CONV std_ss [Once pair_case_def,GSYM curried]) (subst [a|->c,v|->cc] tm)
           |> concl |> rand |> rator |> rand
  val vs = free_vars tm
  val goal = mk_eq(mk_container c2, mk_container tm)
  val pre_tm =
    if not (can (find_term is_arb) goal) then T else let
      val vs = curried |> SPEC_ALL |> concl |> dest_eq |> fst |> dest_args |> tl
      val pre_tm = pattern_complete def vs
      in pre_tm end
  val vs = filter (fn x => not (mem x vs)) (free_vars goal)
  val goal = subst (map (fn v => v |-> ``():unit``) vs) goal
  val goal = subst [mk_comb(c1,``():unit``)|->const] goal
  val goal = mk_imp(pre_tm,goal)
  val lemma = prove(goal,
    SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,TRUE_def,FALSE_def] \\ SRW_TAC [] []
    \\ REPEAT BasicProvers.FULL_CASE_TAC
    \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [def]))
    \\ SRW_TAC [] [] \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ POP_ASSUM MP_TAC \\ REWRITE_TAC [PRECONDITION_def])
    |> REWRITE_RULE [EVAL ``PRECONDITION T``]
    |> UNDISCH_ALL |> CONV_RULE (BINOP_CONV (REWR_CONV CONTAINER_def))
  in (lemma,SOME ind) end end

fun remove_pair_abs def = let
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val def = SPEC_ALL def
  fun delete_pair_arg def = let
    val (lhs,rhs) = def |> concl |> dest_eq
    val xs = args lhs
    val p = first pairSyntax.is_pair xs
    val v = hd (rev (free_vars p)) |> dest_var |> fst
    val v = mk_var(v,type_of p)
    val goal = mk_eq(subst [p|->v] lhs,mk_comb(pairSyntax.mk_pabs(p,rhs),v))
    val lemma = prove(goal,
      SPEC_TAC (v,v) \\ FULL_SIMP_TAC std_ss [FORALL_PROD]
      \\ SIMP_TAC std_ss [Once def]);
    in delete_pair_arg lemma end handle HOL_ERR _ => def
  val def = delete_pair_arg def
  val def' = (* if can (find_term (can (match_term ``UNCURRY``))) (concl def) then *)
              SIMP_RULE std_ss [UNCURRY_SIMP] def
            (* else def *)
  in if concl def' = T then def else def' end

fun is_rec_def def = let
  val thms = def |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL
  val const = hd thms |> concl |> dest_eq |> fst |> repeat rator
  val rhss = thms |> map (snd o dest_eq o concl)
  in can (first (can (find_term (fn tm => tm = const)))) rhss end

fun is_NONE NONE = true | is_NONE _ = false

fun find_ind_thm def = let
  val const = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                  |> dest_eq |> fst |> repeat rator
  val r = dest_thy_const const
  val ind = fetch (#Thy r) ((#Name r) ^ "_ind")
            handle HOL_ERR _ =>
            fetch (#Thy r) ((#Name r) ^ "_IND")
            handle HOL_ERR _ =>
            fetch (#Thy r) ("ConstMult_ind")
  in ind end

fun rename_bound_vars_rule prefix th = let
  val i = ref 0
  fun next_name () = (i:= !i+1; prefix ^ int_to_string (!i))
  fun next_var v = mk_var(next_name (), type_of v)
  fun next_alpha_conv tm = let
    val (v,_) = dest_abs tm
    val _ = not (String.isPrefix prefix (fst (dest_var v))) orelse fail()
    in ALPHA_CONV (next_var v) tm end handle HOL_ERR _ => NO_CONV tm
  in CONV_RULE (DEPTH_CONV next_alpha_conv) th end

fun split_let_and_conv tm = let
  val (xs,b) = pairSyntax.dest_anylet tm
  val _ = 1 < length xs orelse fail()
  val _ = map (fn (x,y) => if is_var x then () else fail()) xs
  val ys = map (fn (x,y) => (x,genvar(type_of x),y)) xs
  val b2 = subst (map (fn (x,y,_) => x |-> y) ys) b
  val tm2 = foldr (fn ((x,y,z),b) => pairSyntax.mk_anylet([(y,z)],b)) b2 ys
  val goal = mk_eq(tm,tm2)
  val lemma = prove(goal, REWRITE_TAC [LET_THM] (* potentially bad *)
                          THEN CONV_TAC (DEPTH_CONV BETA_CONV)
                          THEN REWRITE_TAC [])
  in lemma end handle HOL_ERR _ => NO_CONV tm;

fun preprocess_def def = let
  val is_rec = is_rec_def def
  val (def,ind) = single_line_def def
  val def = RW1 [GSYM TRUE_def, GSYM FALSE_def] def
  val def = remove_pair_abs def |> SPEC_ALL
  val def = CONV_RULE (DEPTH_CONV split_let_and_conv) def
  val def = rename_bound_vars_rule "v" (GEN_ALL def) |> SPEC_ALL
  val ind = if is_rec andalso is_NONE ind then SOME (find_ind_thm def) else ind
  val def = if def |> SPEC_ALL |> concl |> dest_eq |> fst |> is_const
            then SPEC_ALL (RW1 [FUN_EQ_THM] def) else def
  val def = PURE_REWRITE_RULE ([ADD1,boolTheory.literal_case_DEF,
              boolTheory.bool_case_DEF,num_case_thm] @ get_preprocessor_rws()) def
  val def = CONV_RULE (REDEPTH_CONV BETA_CONV) def
  in (is_rec,def,ind) end;

(*

val pre_lemma = EVAL ``PRECONDITION T``

fun collect_pres th = let
  val th1 = th |> DISCH_ALL |> PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val hs = hyp th1
  val pat1 = ``Eval env exp P``
  val pat2 = ``EqualityType (Q:'a -> v -> bool)``
  fun is_pre tm = not (can (match_term pat1) tm)
          andalso not (can (match_term pat2) tm)
  val th = foldr (fn (tm,th) => DISCH tm th) th1 (T::filter is_pre hs)
  val c1 = SIMP_CONV std_ss [PRECONDITION_def,CONTAINER_def]
  val c2 = REWR_CONV (GSYM PRECONDITION_def)
  val th = PURE_REWRITE_RULE [AND_IMP_INTRO] th
           |> CONV_RULE ((RATOR_CONV o RAND_CONV) (c1 THENC c2)) |> RW []
  in RW [pre_lemma] th end

*)

(* definition of the main work horse: hol2deep: term -> thm *)

fun dest_builtin_binop tm = let
  val (px,y) = dest_comb tm
  val (p,x) = dest_comb px
  in (p,x,y,if p = ``($+):num->num->num`` then SPEC_ALL Eval_NUM_ADD else
            if p = ``($-):num->num->num`` then SPEC_ALL Eval_NUM_SUB else
            if p = ``($*):num->num->num`` then SPEC_ALL Eval_NUM_MULT else
            if p = ``($DIV):num->num->num`` then SPEC_ALL Eval_NUM_DIV else
            if p = ``($MOD):num->num->num`` then SPEC_ALL Eval_NUM_MOD else
            if p = ``($<):num->num->bool`` then SPEC_ALL Eval_NUM_LESS else
            if p = ``($<=):num->num->bool`` then SPEC_ALL Eval_NUM_LESS_EQ else
            if p = ``($>):num->num->bool`` then SPEC_ALL Eval_NUM_GREATER else
            if p = ``($>=):num->num->bool`` then SPEC_ALL Eval_NUM_GREATER_EQ else
            if p = ``($+):int->int->int`` then SPEC_ALL Eval_INT_ADD else
            if p = ``($-):int->int->int`` then SPEC_ALL Eval_INT_SUB else
            if p = ``($*):int->int->int`` then SPEC_ALL Eval_INT_MULT else
            if p = ``($/):int->int->int`` then SPEC_ALL Eval_INT_DIV else
            if p = ``($%):int->int->int`` then SPEC_ALL Eval_INT_MOD else
            if p = ``($<):int->int->bool`` then SPEC_ALL Eval_INT_LESS else
            if p = ``($<=):int->int->bool`` then SPEC_ALL Eval_INT_LESS_EQ else
            if p = ``($>):int->int->bool`` then SPEC_ALL Eval_INT_GREATER else
            if p = ``($>=):int->int->bool`` then SPEC_ALL Eval_INT_GREATER_EQ else
            if p = ``($/\):bool->bool->bool`` then SPEC_ALL Eval_And else
            if p = ``($\/):bool->bool->bool`` then SPEC_ALL Eval_Or else
            if p = ``($==>):bool->bool->bool`` then SPEC_ALL Eval_Implies else
              failwith("Not a builtin operator"))
  end

fun inst_Eval_env v th = let
  val thx = th
  val name = fst (dest_var v)
  val str = stringLib.fromMLstring name
  val inv = get_type_inv (type_of v)
  val assum = ``Eval env (Var ^str) (^inv ^v)``
  val new_env = ``(^str,v:v)::env``
  val old_env = new_env |> rand
  val th = thx |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum |> SIMP_RULE bool_ss []
               |> INST [old_env|->new_env]
               |> SIMP_RULE bool_ss [Eval_Var_SIMP]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> SIMP_RULE bool_ss [SafeVar_def]
  val new_assum = fst (dest_imp (concl th))
  val th1 = th |> UNDISCH_ALL
               |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
               |> DISCH new_assum
  in th1 end;

val PUSH_FORALL_INTO_IMP =
  METIS_PROVE [] ``!P Q. (!x. P x ==> Q x) ==> (!x. P x) ==> (!x. Q x)``

fun FORCE_GEN v th1 = GEN v th1 handle HOL_ERR _ => let
  val hs = hyp th1
  val xs = filter (fn tm => mem v (free_vars tm)) hs
  val th2 =  DISCH T th1
  val th3 = foldr (fn (tm,th) => ONCE_REWRITE_RULE [AND_IMP_INTRO] (DISCH tm th)) th2 xs
  val th4 = GEN v th3
  val th4 = HO_MATCH_MP PUSH_FORALL_INTO_IMP th4
  in UNDISCH th4 end

fun apply_Eval_Fun v th fix = let
  val th1 = inst_Eval_env v th
  val th2 = if fix then MATCH_MP Eval_Fun_Eq (GEN ``v:v`` th1)
                   else MATCH_MP Eval_Fun (GEN ``v:v`` (FORCE_GEN v th1))
  in th2 end;

fun apply_Eval_Recclosure fname v th = let
  val vname = fst (dest_var v)
  val vname_str = stringLib.fromMLstring vname
  val fname_str = stringLib.fromMLstring fname
  val body = th |> UNDISCH_ALL |> concl |> rator |> rand
  val inv = get_type_inv (type_of v)
  val new_env = ``(^vname_str,v:v)::(^fname_str,
                    Recclosure env [(^fname_str,^vname_str,^body)] ^fname_str)::env``
  val old_env = ``env:(string # v) list``
  val assum = subst [old_env|->new_env] ``Eval env (Var ^vname_str) (^inv ^v)``
  val thx = th |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum |> SIMP_RULE bool_ss []
               |> INST [old_env|->new_env]
               |> SIMP_RULE bool_ss [Eval_Var_SIMP]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> SIMP_RULE bool_ss [SafeVar_def]
  val new_assum = fst (dest_imp (concl thx))
  val th1 = thx |> UNDISCH_ALL
                |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
                |> DISCH new_assum
  val th2 = MATCH_MP Eval_Recclosure (Q.INST [`env`|->`cl_env`] (GEN ``v:v`` th1))
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = D th2 |> REWRITE_RULE [assum]
  val lemma = MATCH_MP Eval_Eq_Recclosure assum
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    in INST i (INST_TYPE t lemma) end handle HOL_ERR _ => NO_CONV tm
  val th4 = CONV_RULE (QCONV (DEPTH_CONV replace_conv)) th3
  in th4 end

fun clean_assumptions th4 = let
  (* lift cl_env assumptions out *)
  val env = mk_var("env",``:(string # v) list``)
  val pattern = ``Eval env (Var name) ($= x)``
  val cl_assums = find_terms (fn tm => can (match_term pattern) tm andalso
                      ((tm |> rator  |> rator |> rand) <> env)) (concl th4)
  val th5 = REWRITE_RULE (map ASSUME cl_assums) th4
  (* lift EqualityType assumptions out *)
  val pattern = ``EqualityType (a:'a->v->bool)``
  val eq_assums = find_terms (can (match_term pattern)) (concl th5)
  val th6 = REWRITE_RULE (map ASSUME eq_assums) th5
  in th6 end;

local
  val memory = ref (tl [(T,TRUTH)])
in
  fun store_cert const th =
    (((if is_const const then save_thm("Eval_" ^ string2ident (fst (dest_const const)) ^ "_thm", th) else TRUTH) handle HOL_ERR _ => TRUTH);
     memory := (const,th)::(!memory))
  fun lookup_cert const = snd (first (fn (c,_) => can (match_term c) const) (!memory))
  fun delete_cert const = (memory := filter (fn (c,_) => c <> const) (!memory))
  fun get_mem () = !memory
end

fun store_eval_thm th = let
  val th1 = UNDISCH_ALL th
  val pat = th1 |> concl |> rand |> rand
  val _ = store_cert pat th1
  in th end

fun get_pre_var lhs fname = let
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
  val args = dest_args lhs
  val ty = list_mk_type args ``:bool``
  val v = mk_var(fname ^ "_side",ty)
  in (foldl (fn (x,y) => mk_comb(y,x)) v args) end

local
  val rec_pattern = ref T;
  val rec_fname = ref "";
in
  fun install_rec_pattern tm fname =
    (rec_pattern := tm; rec_fname := fname; get_pre_var tm fname)
  fun can_match_rec_pattern tm = can (match_term (!rec_pattern)) tm
  fun uninstall_rec_pattern () = (rec_pattern := ``ARB:bool``)
  fun rec_fun () = repeat rator (!rec_pattern)
  fun rec_term () = (!rec_pattern)
  fun rec_name () = (!rec_fname)
  fun rec_pre_var () = get_pre_var (!rec_pattern) (!rec_fname)
end

fun check_inv name tm result = let
  val tm2 = result |> concl |> rand |> rand
  in if aconv tm2 tm then result else let
    val _ = print ("\n\nhol2deep failed at '" ^ name ^ "'\n\ntarget:\n\n")
    val _ = print_term tm
    val _ = print "\n\nbut derived:\n\n"
    val _ = print_term tm2
    val _ = print "\n\n\n"
    in failwith("checkinv") end end

fun MY_MATCH_MP th1 th2 = let
  val tm1 = fst (dest_imp (concl th1))
  val tm2 = concl th2
  val (s,i) = match_term tm1 tm2
  in MP (INST s (INST_TYPE i th1)) th2 end;

fun force_remove_fix thx = let
  val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
  val xs = map rand (find_terms (can (match_term pat)) (concl thx))
  val s = SIMP_RULE std_ss [Eval_FUN_FORALL_EQ,FUN_QUANT_SIMP]
  val thx = foldr (fn (x,th) => s (FORCE_GEN x th)) thx xs
  in thx end;

fun rm_fix res = let
  val lemma = mk_thm([],``Eq b x = b``)
  val tm2 = QCONV (REWRITE_CONV [lemma]) res |> concl |> dest_eq |> snd
  in tm2 end

fun hol2deep tm =
  (* variables *)
  if is_var tm then let
    val (name,ty) = dest_var tm
    val inv = get_type_inv ty
    val str = stringSyntax.fromMLstring name
    val result = ASSUME (mk_comb(``Eval env (Var ^str)``,mk_comb(inv,tm)))
    in check_inv "var" tm result end else
  (* constants *)
  if numSyntax.is_numeral tm then SPEC tm Eval_Val_NUM else
  if intSyntax.is_int_literal tm then SPEC tm Eval_Val_INT else
  if (tm = T) orelse (tm = F) then SPEC tm Eval_Val_BOOL else
  if (tm = ``TRUE``) orelse (tm = ``FALSE``) then SPEC tm Eval_Val_BOOL else
  if (* is_const tm andalso *) can lookup_cert tm then let
    val th = lookup_cert tm
    val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val xs = find_terms (can (match_term pat)) (concl th) |> map rand
    val ss = map (fn v => v |-> genvar(type_of v)) xs
    val th = INST ss th
    val res = th |> UNDISCH_ALL |> concl |> rand
    val inv = get_type_inv (type_of tm)
    val target = mk_comb(inv,tm)
    val (ss,ii) = match_term res target handle HOL_ERR _ =>
                  match_term (rm_fix res) (rm_fix target) handle HOL_ERR _ => ([],[])
    val result = INST ss (INST_TYPE ii th)
    in check_inv "lookup_cert" tm result end else
  (* data-type constructor *)
  inst_cons_thm tm hol2deep handle HOL_ERR _ =>
  (* data-type pattern-matching *)
  inst_case_thm tm hol2deep handle HOL_ERR _ =>
  (* recursive pattern *)
  if can_match_rec_pattern tm then let
    fun dest_args tm = rand tm :: dest_args (rator tm) handle HOL_ERR _ => []
    val xs = dest_args tm
    val f = rec_fun ()
    val str = stringLib.fromMLstring (rec_name())
    fun mk_fix tm = let
      val inv = get_type_inv (type_of tm)
      in ``Eq ^inv ^tm`` end
    fun mk_arrow x y = ``Arrow ^x ^y``
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_arrow (mk_fix x) res)
    val inv = mk_inv xs (get_type_inv (type_of tm))
    val ss = fst (match_term (rec_term ()) tm)
    val pre = subst ss (rec_pre_var ())
    val h = ASSUME ``PreImp ^pre (Eval env (Var ^str) (^inv ^f))``
            |> RW [PreImp_def] |> UNDISCH
    val ys = map (fn tm => MATCH_MP Eval_Eq (hol2deep tm)) xs
    fun apply_arrow hyp [] = hyp
      | apply_arrow hyp (x::xs) =
          MATCH_MP (MATCH_MP Eval_Arrow (apply_arrow hyp xs)) x
    val result = apply_arrow h ys
    in check_inv "rec_pattern" tm result end else
  (* built-in binary operations *)
  if can dest_builtin_binop tm then let
    val (p,x1,x2,lemma) = dest_builtin_binop tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val result = MATCH_MP (MATCH_MP lemma th1) th2 |> UNDISCH_ALL
    in check_inv "binop" tm result end else
  (* boolean not *)
  if can (match_term ``~(b:bool)``) tm then let
    val x1 = rand tm
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_Bool_Not th1
    in check_inv "not" tm result end else
  (* equality: n = 0 *)
  if can (match_term ``(n = (0:num))``) tm then let
    val x1 = fst (dest_eq tm)
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_NUM_EQ_0 th1
    in check_inv "num_eq_0" tm result end else
  (* equality: 0 = n *)
  if can (match_term ``(0 = (n:num))``) tm then let
    val x1 = snd (dest_eq tm)
    val th1 = hol2deep x1
    val result = MATCH_MP (GSYM Eval_NUM_EQ_0) th1
    in check_inv "0_eq_num" tm result end else
  (* equality *)
  if is_eq tm then let
    val (x1,x2) = dest_eq tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val result = MATCH_MP Eval_Equality (CONJ th1 th2) |> UNDISCH
    in check_inv "equal" tm result end else
  (* if statements *)
  if is_cond tm then let
    val (x1,x2,x3) = dest_cond tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val th3 = hol2deep x3
    val th = MATCH_MP Eval_If (LIST_CONJ [D th1, D th2, D th3])
    val result = UNDISCH th
    in check_inv "if" tm result end else
  (* let expressions *)
  if can dest_let tm andalso is_abs (fst (dest_let tm)) then let
    val (x,y) = dest_let tm
    val (v,x) = dest_abs x
    val th1 = hol2deep y
    val th2 = hol2deep x
    val th2 = inst_Eval_env v th2
    val th2 = th2 |> GEN ``v:v``
    val z = th1 |> concl |> rand |> rand
    val th2 = INST [v|->z] th2
    val result = MATCH_MP Eval_Let (CONJ th1 th2)
    in check_inv "let" tm result end else
  (* normal function applications *)
  if is_comb tm then let
    val (f,x) = dest_comb tm
    val thf = hol2deep f
    val thx = hol2deep x
    val thx = force_remove_fix thx
    val result = MATCH_MP (MATCH_MP Eval_Arrow thf) thx handle HOL_ERR _ =>
                 MY_MATCH_MP (MATCH_MP Eval_Arrow thf) (MATCH_MP Eval_Eq thx)
    in check_inv "comb" tm result end else
  (* lambda applications *)
  if is_abs tm then let
    val (v,x) = dest_abs tm
    val thx = hol2deep x
    val result = apply_Eval_Fun v thx false
    in check_inv "abs" tm result end else
  if is_arb tm then let
    val inv = get_type_inv (type_of tm)
    val goal = ``PRECONDITION F ==> Eval env (Raise Bind_error) (^inv ^tm)``
    val result = prove(goal,SIMP_TAC std_ss [PRECONDITION_def]) |> UNDISCH
    in check_inv "arb" tm result end
  else raise (UnableToTranslate tm)

(*
val tm = f
val tm = rhs
val tm = z
*)

(* collect precondition *)

val PRECONDITION_EQ_CONTAINER = prove(
  ``(PRECONDITION p = CONTAINER p) /\
    (CONTAINER ~p = ~CONTAINER p) /\ CONTAINER T``,
  EVAL_TAC);

val CONTAINER_NOT_ZERO = prove(
  ``!P. (~(CONTAINER (b = 0)) ==> P b) =
        !n. (CONTAINER (b = SUC n)) ==> P (SUC n:num)``,
  REPEAT STRIP_TAC THEN Cases_on `b`
  THEN EVAL_TAC THEN SRW_TAC [] [ADD1]);

fun clean_precondition pre_def = let
  val th = SIMP_RULE (srw_ss()) [] pre_def
  val th = REWRITE_RULE [CONTAINER_def] th
  val th = rename_bound_vars_rule "v" (GEN_ALL th) |> SPEC_ALL
  in th end;

fun extract_precondition th pre_var is_rec =
  if not is_rec then if is_imp (concl th) then let
    val c = (REWRITE_CONV [CONTAINER_def,PRECONDITION_def] THENC
             ONCE_REWRITE_CONV [GSYM PRECONDITION_def])
    val c = (RATOR_CONV o RAND_CONV) c
    val th = CONV_RULE c th
    val rhs = th |> concl |> dest_imp |> fst |> rand
    in if free_vars rhs = [] then
      (UNDISCH_ALL (SIMP_RULE std_ss [EVAL ``PRECONDITION T``] th),NONE)
    else let
    val def_tm = mk_eq(pre_var,rhs)
    val pre_def = quietDefine [ANTIQUOTE def_tm]
    val c = REWR_CONV (GSYM pre_def)
    val c = (RATOR_CONV o RAND_CONV o RAND_CONV) c
    val th = CONV_RULE c th |> UNDISCH_ALL
    val pre_def = clean_precondition pre_def
    in (th,SOME pre_def) end end else (th,NONE)
  else let
  fun rename_bound_vars_rule th = let
    val i = ref 0
    fun next_name () = (i:= !i+1; "v__" ^ int_to_string (!i))
    fun next_var v = mk_var(next_name (), type_of v)
    fun next_alpha_conv tm = let
      val (v,_) = dest_abs tm
      val _ = not (String.isPrefix "v__" (fst (dest_var v))) orelse fail()
      in ALPHA_CONV (next_var v) tm end handle HOL_ERR _ => NO_CONV tm
    in CONV_RULE (DEPTH_CONV next_alpha_conv) th end
  val th = SIMP_RULE bool_ss [CONTAINER_NOT_ZERO] th
  val th = rename_bound_vars_rule th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (REWRITE_CONV [GSYM AND_IMP_INTRO])) th
  val tm = concl th |> dest_imp |> fst
  fun replace_any_match pat tm = let
    val xs = find_terms (can (match_term pat)) tm
    in subst (map (fn x => x |-> T) xs) tm end
  val rw1 = mk_thm([],``PRECONDITION b = T``)
  val tm1 = QCONV (REWRITE_CONV [rw1]) tm |> concl |> rand
  val pat = Eval_def |> SPEC_ALL |> concl |> dest_eq |> fst
  val rw2 = mk_thm([],pat)
  val tm2 = QCONV (REWRITE_CONV [rw2,PreImp_def]) tm |> concl |> rand
  (* check whether the precondition is T *)
  val (no_pre,th5) = let
    val pre_v = repeat rator pre_var
    val true_pre = list_mk_abs ((dest_args pre_var), T)
    val tm3 = subst [pre_v |-> true_pre] tm2
    val res = QCONV (REWRITE_CONV [rw2,PreImp_def,PRECONDITION_def,CONTAINER_def]) tm3 |> concl |> rand
    val th5 = INST [pre_v |-> true_pre] th
                |> SIMP_RULE bool_ss [PRECONDITION_EQ_CONTAINER]
                |> PURE_REWRITE_RULE [PreImp_def,PRECONDITION_def]
                |> CONV_RULE (DEPTH_CONV BETA_CONV THENC
                              (RATOR_CONV o RAND_CONV) (REWRITE_CONV []))
    in (res = T, th5) end
  in if no_pre then (th5,NONE) else let
  (* define precondition *)
  fun list_dest_forall tm = let
    val (v,tm) = dest_forall tm
    val (vs,tm) = list_dest_forall tm
    in (v::vs,tm) end handle HOL_ERR _ => ([],tm)
  fun my_list_mk_conj [] = T
    | my_list_mk_conj xs = list_mk_conj xs
  fun list_dest f tm = let val (x,y) = f tm
                       in list_dest f x @ list_dest f y end handle HOL_ERR _ => [tm]
  val list_dest_conj = list_dest dest_conj
  val tms = list_dest_conj tm2
  val tm = first is_forall tms handle HOL_ERR _ => first is_imp tms
  val others = my_list_mk_conj (filter (fn x => x <> tm) tms)
  val pat = ``CONTAINER (x = y:'a) ==> z``
  fun dest_container_eq_imp tm = let
    val _ = match_term pat tm
    val (xy,z) = dest_imp tm
    val (x,y) = dest_eq (rand xy)
    val _ = dest_var x
    in (x,y,z) end
  fun cons_fst x (y,z) = (x::y,z)
  fun dest_forall_match tm = let
    val xs = list_dest_conj (snd (list_dest_forall tm))
             |> map dest_container_eq_imp
    val ys = map (fn (x,y,z) => map (cons_fst (x,y)) (dest_forall_match z)) xs
    in Lib.flatten ys end handle HOL_ERR _ => [([],tm)]
  val vs = dest_args pre_var
  val ws = map (fn v => (v,mk_var(fst (dest_var v) ^ "AA",type_of v))) vs
  val xs = map (fn (x,y) => (x,y,others)) (dest_forall_match tm @ [(ws,T)])
  fun process_line (x,y,z) = let
    val (x1,x2) = foldl (fn ((x1,x2),(z1,z2)) => (subst [x1 |-> x2] z1, subst [x1 |-> x2] z2)) (pre_var,z) x
    fun simp tm = QCONV (SIMP_CONV (srw_ss()) [PRECONDITION_def]) tm |> concl |> rand
    in mk_eq(x1,simp(mk_conj(y,x2))) end
  val def_tm = list_mk_conj (map process_line xs)
  fun alternative_definition_of_pre pre_var tm2 = let
    val rw = QCONV (REWRITE_CONV [PRECONDITION_def,CONTAINER_def]) tm2
    val gg = rw |> concl |> dest_eq |> snd
    val gg = (mk_imp(gg,pre_var))
    val (_,_,pre_def) = Hol_reln [ANTIQUOTE gg]
    val const = pre_def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
    val v = repeat rator pre_var
    in subst [v|->const] tm2 |> (REWR_CONV rw THENC REWR_CONV (GSYM pre_def))
       |> GSYM end
  val pre_def = quietDefine [ANTIQUOTE def_tm]
                handle HOL_ERR _ =>
                alternative_definition_of_pre pre_var tm2
  val pre_def = fst (single_line_def pre_def)
  val pre_const = pre_def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  val pre_v = pre_var |> repeat rator
  (* prove pre is sufficient *)
  val s = subst [pre_v|->pre_const]
  val goal = mk_imp(s pre_var, s tm2)
  val pre_thm = prove(goal,
    CONV_TAC (RATOR_CONV (PURE_ONCE_REWRITE_CONV [pre_def]))
    THEN REPEAT BasicProvers.FULL_CASE_TAC
    THEN FULL_SIMP_TAC (srw_ss()) [PULL_FORALL,CONTAINER_def,
      PRECONDITION_def,PreImp_def])
  (* simplify main thm *)
  val goal_lhs = mk_conj(subst [pre_v|->pre_const] tm1,
                     subst [pre_v|->pre_const] pre_var)
  val th = INST [pre_v|->pre_const] th
  val tm = concl th |> dest_imp |> fst
  val goal = mk_imp(goal_lhs,tm)
  val lemma = prove(goal,STRIP_TAC THEN IMP_RES_TAC pre_thm THEN METIS_TAC [])
  val th = MP th (UNDISCH lemma)
  val th = th |> DISCH goal_lhs
  val th = MATCH_MP IMP_PreImp th
  val pre_def = clean_precondition pre_def
  in (th,SOME pre_def) end end


(* main translation routines *)

fun translate def = let
  val original_def = def
  fun the (SOME x) = x | the _ = failwith("the of NONE")
  (* perform preprocessing -- reformulate def *)
  val (is_rec,def,ind) = preprocess_def def
  val (lhs,rhs) = dest_eq (concl def)
  val fname = repeat rator lhs |> dest_const |> fst |> get_unique_name
  val fname_str = stringLib.fromMLstring fname
  (* read off information *)
  val _ = register_term_types (concl def)
  fun rev_param_list tm = rand tm :: rev_param_list (rator tm) handle HOL_ERR _ => []
  val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
  val no_params = (length rev_params = 0)
  (* derive deep embedding *)
  val _ = delete_cert (repeat rator lhs)
  val pre_var = install_rec_pattern lhs fname
  val th_rhs = hol2deep rhs
  val _ = uninstall_rec_pattern ()
  (* deal with constant functions *)
  val th = if not no_params then th_rhs else
             mk_comb(rand (concl th_rhs),mk_var("v",``:v``))
             |> EVAL |> SIMP_RULE std_ss [] |> Q.GEN `v`
             |> MATCH_MP Eval_CONST |> UNDISCH
  (* replace rhs with lhs in th *)
  val th = CONV_RULE ((RAND_CONV o RAND_CONV)
             (REWRITE_CONV [CONTAINER_def] THENC ONCE_REWRITE_CONV [GSYM def])) th
  (* optimise generated code *)
  val th = MATCH_MP Eval_OPTIMISE (UNDISCH_ALL th)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th
  val th = D th
  (* abstract parameters *)
  val (th,v) = if no_params then (th,T) else
                 (foldr (fn (v,th) => apply_Eval_Fun v th true) th (rev (butlast rev_params)),
                  last rev_params)
  val th = if no_params then th |> Q.INST [`name`|->`^fname_str`] else
           if is_rec then apply_Eval_Recclosure fname v th
                            |> clean_assumptions
                     else apply_Eval_Fun v th true
                            |> MATCH_MP Eval_Eq_Fun
                            |> Q.INST [`env`|->`cl_env`]
                            |> Q.SPEC `temp_env` |> D
                            |> clean_assumptions
                            |> Q.INST [`temp_env`|->`env`]
                            |> Q.INST [`name`|->`^fname_str`]
  val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
  val th = th |> INST [mk_var("cl_env",``:envE``)|->mk_var(fname^"_env",``:envE``)]
  (* collect precondition *)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                      (SIMP_CONV std_ss [EVAL ``CONTAINER TRUE``,
                                         EVAL ``CONTAINER FALSE``])) th
  val (th,pre) = if no_params then (th,NONE) else extract_precondition th pre_var is_rec
  (* apply induction *)
  val th = if not is_rec then th else let
    val th = REWRITE_RULE [CONTAINER_def] th
    val hs = hyp th
    val hyp_tm = list_mk_abs(rev rev_params, th |> UNDISCH_ALL |> concl)
    val goal = list_mk_forall(rev rev_params, th |> UNDISCH_ALL |> concl)
    val goal = mk_imp(list_mk_conj hs,goal)
    val ind_thm = (the ind)
    val ind_thm = rename_bound_vars_rule "i" ind_thm
                  |> SIMP_RULE std_ss []
(*
    set_goal([],goal)
*)
    val lemma = prove(goal,
      STRIP_TAC
      \\ SIMP_TAC std_ss [FORALL_PROD]
      \\ MATCH_MP_TAC (SPEC hyp_tm ind_thm |> CONV_RULE (DEPTH_CONV BETA_CONV))
      \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC th
      \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
      \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
      \\ METIS_TAC []);
    val th = UNDISCH lemma |> SPECL (rev rev_params)
    val th = RW [PreImp_def] th |> UNDISCH_ALL
    in th end
  (* remove Eq *)
  fun f (v,th) =
    HO_MATCH_MP Eval_FUN_FORALL (GEN v th) |> SIMP_RULE std_ss [FUN_QUANT_SIMP]
  val th = foldr f th rev_params handle HOL_ERR _ => th
  (* abbreviate code *)
  val code_name = string2ident fname ^ "_ml"
  val fname_tm = stringSyntax.fromMLstring (string2ident fname)
  val th = DISCH_ALL th
  val raw_code_tm = if no_params then th |> concl |> dest_imp |> fst |> rand else
                (find_term (can (match_term ``Recclosure i (f::fns) n``)) (concl th))
                |> rator
                handle HOL_ERR _ =>
                (find_term (can (match_term ``Closure i n (f x)``)) (concl th))
  val code_tm = rand raw_code_tm
  val fname_tm = stringSyntax.fromMLstring fname
  val dlet =
    if is_rec then ``Dletrec ^code_tm`` else
    if no_params then ``Dlet (Pvar ^fname_tm) ^(th_rhs |> concl |> rator |> rand)``
    else ``Dlet (Pvar ^fname_tm) (Fun ^(raw_code_tm |> rator |> rand) ^code_tm)``
  val _ = add_decl dlet
  val code_abbrev = new_definition(code_name ^ "_def",
    mk_eq(mk_var(code_name,type_of code_tm),code_tm))
  val th = REWRITE_RULE [GSYM code_abbrev] th |> UNDISCH_ALL
  (* simpliy EqualityType *)
  val th = SIMP_EqualityType_ASSUMS th
  (* store certificate for later use *)
  val _ = store_cert (repeat rator lhs) th
  (* print result into files *)
  val _ = print_results fname original_def th code_tm pre
  in th end handle UnableToTranslate tm => let
    val _ = print "\n\nCannot translate term:  "
    val _ = print_term tm
    val _ = print "\n\n"
    in raise UnableToTranslate tm end;

val _ = set_translator translate;

fun mlDefine q = let
  val def = Define q
  val th = translate def
  val _ = print "\n"
  val _ = print_thm th
  val _ = print "\n\n"
  in def end;

fun mltDefine name q tac = let
  val def = tDefine name q tac
  val th = translate def
  val _ = print "\n"
  val _ = print_thm th
  val _ = print "\n\n"
  in def end;

end
