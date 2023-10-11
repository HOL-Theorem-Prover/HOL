structure lisp_extractLib :> lisp_extractLib =
struct

open HolKernel boolLib bossLib;
open lisp_extractTheory lisp_semanticsTheory;

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open optionTheory arithmeticTheory relationTheory;
open stringLib pairSyntax;

infix \\
val op \\ = op THEN;
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

fun allowing_rebinds f x = Feedback.trace ("Theory.allow_rebinds", 1) f x

(* definitions *)

fun remove_let_and_conv tm = let
  val (xs,b) = pairSyntax.dest_anylet tm
  val _ = 1 < length xs orelse fail()
  fun mk_tuple [] = fail()
    | mk_tuple [x] = x
    | mk_tuple (x::xs) = pairSyntax.mk_pair(x,mk_tuple xs)
  val vs = mk_tuple (map fst xs)
  val ys = mk_tuple (map snd xs)
  val result = pairSyntax.mk_anylet([(vs,ys)],b)
  val th1 = pairLib.let_CONV tm
  val th2 = pairLib.let_CONV result
  in TRANS th1 (SYM th2) end handle HOL_ERR _ => NO_CONV tm

fun new_def def_tm term_tac = let
  val name = def_tm |> dest_eq |> fst |> repeat rator |> dest_var |> fst
  val def_rw = QCONV (DEPTH_CONV remove_let_and_conv) def_tm
  val new_def_tm = def_rw |> concl |> rand
  val def = case term_tac of
               NONE   => Define [ANTIQUOTE new_def_tm]
             | SOME x => tDefine name [ANTIQUOTE new_def_tm] x
  val def = def |> SPEC_ALL |> CONV_RULE (REWR_CONV (SYM def_rw))
  val ind = (SOME (fetch "-" (name^"_ind") |> PURE_REWRITE_RULE [pairTheory.PAIR_EQ])
            handle HOL_ERR _ => NONE)
  in (def,ind) end

val new_def = allowing_rebinds new_def

(* ML equivalent of term datatype defined in lisp_semanticsTheory *)

datatype
  primitive_op = op_CONS | op_EQUAL | op_LESS | op_SYMBOL_LESS | op_ADD | op_SUB |
                 op_ATOMP | op_CONSP | op_NATP | op_SYMBOLP | op_CAR | op_CDR

datatype
  mfunc = PrimitiveFun of primitive_op
        | mDefine | Print | Error | Funcall | Fun of string;

datatype
  mterm = Const of term
        | Var of string
        | App of mfunc * mterm list
        | If of mterm * mterm * mterm
        | LamApp of string list * mterm * mterm list
        | Or of mterm list
        (* only macros below *)
        | And of mterm list
        | Cond of (mterm * mterm) list
        | Let of (string * mterm) list * mterm
        | LetStar of (string * mterm) list * mterm
        | First of mterm | Second of mterm | Third of mterm
        | Fourth of mterm | Fifth of mterm | List of mterm list
        | Defun of string * string list * term;


(* a mapping: term -> mterm *)

fun dest_primitive_op tm =
  if tm ~~ ``opCONS`` then op_CONS else
  if tm ~~ ``opEQUAL`` then op_EQUAL else
  if tm ~~ ``opLESS`` then op_LESS else
  if tm ~~ ``opSYMBOL_LESS`` then op_SYMBOL_LESS else
  if tm ~~ ``opADD`` then op_ADD else
  if tm ~~ ``opSUB`` then op_SUB else
  if tm ~~ ``opCONSP`` then op_CONSP else
  if tm ~~ ``opSYMBOLP`` then op_SYMBOLP else
  if tm ~~ ``opNATP`` then op_NATP else
  if tm ~~ ``opCAR`` then op_CAR else
  if tm ~~ ``opCDR`` then op_CDR else fail()

fun dest_func tm = let
  val p = repeat rator tm
  in if p ~~ ``PrimitiveFun`` then PrimitiveFun (dest_primitive_op (rand tm)) else
     if p ~~ ``Define`` then mDefine else
     if p ~~ ``Print`` then Print else
     if p ~~ ``Error`` then Error else
     if p ~~ ``Funcall`` then Funcall else
     if p ~~ ``Fun`` then Fun (stringSyntax.fromHOLstring (rand tm)) else fail()
  end

fun dest_term tm = let
  fun list_dest f tm = let val (x,y) = f tm in list_dest f x @ [y] end
                       handle HOL_ERR _ => [tm];
  val xs = list_dest dest_comb tm
  val p = repeat rator tm
  in if p ~~ ``Const`` then Const (rand tm) else
     if p ~~ ``Var`` then Var (stringSyntax.fromHOLstring (rand tm)) else
     if p ~~ ``App`` then App ((dest_func (tm |> rator |> rand)),
                               map (dest_term) (fst (listSyntax.dest_list (rand tm)))) else
     if p ~~ ``If`` then If (dest_term (el 2 xs),dest_term (el 3 xs),dest_term (el 4 xs)) else
     if p ~~ ``LamApp`` then
       LamApp (map stringSyntax.fromHOLstring
                   (fst (listSyntax.dest_list (el 2 xs))),
               dest_term (el 3 xs),
               map (dest_term) (fst (listSyntax.dest_list (el 4 xs)))) else
     if p ~~ ``First`` then First (dest_term (rand tm)) else
     if p ~~ ``Second`` then Second (dest_term (rand tm)) else
     if p ~~ ``Third`` then Third (dest_term (rand tm)) else
     if p ~~ ``Fourth`` then Fourth (dest_term (rand tm)) else
     if p ~~ ``Fifth`` then Fifth (dest_term (rand tm)) else
     if p ~~ ``Or`` then Or (map (dest_term) (fst (listSyntax.dest_list (rand tm)))) else
     if p ~~ ``And`` then And (map (dest_term) (fst (listSyntax.dest_list (rand tm)))) else
     if p ~~ ``List`` then List (map (dest_term) (fst (listSyntax.dest_list (rand tm)))) else
     if p ~~ ``Let`` then
       Let (map
              ((fn (x,y) => (stringSyntax.fromHOLstring x, dest_term y)) o
               pairSyntax.dest_pair)
              (fst (listSyntax.dest_list (el 2 xs))),
            dest_term (el 3 xs)) else
     if p ~~ ``LetStar`` then
       LetStar (map
                  ((fn (x,y) => (stringSyntax.fromHOLstring x, dest_term y)) o
                   pairSyntax.dest_pair)
                  (fst (listSyntax.dest_list (el 2 xs))),
                dest_term (el 3 xs)) else
     if p ~~ ``Cond`` then
       Cond (map
               ((fn (x,y) => (dest_term x, dest_term y)) o pairSyntax.dest_pair)
               (fst (listSyntax.dest_list (el 2 xs)))) else
     if p ~~ ``Defun`` then Defun (stringSyntax.fromHOLstring (el 2 xs),
       map stringSyntax.fromHOLstring (fst (listSyntax.dest_list (el 3 xs))),
       el 4 xs) else fail()
  end


(* mapping from shallow embeddings to deep embeddings *)

infix $$
val op $$ = mk_comb

val string_uppercase = let
  fun uppercase_char c =
    if #"a" <= c andalso c <= #"z" then chr (ord c - (ord #"a" - ord #"A")) else c
  in String.translate (fn c => implode [uppercase_char c]) end

fun shallow_to_deep tm = let
  fun fromHOLstring s = string_uppercase (stringSyntax.fromHOLstring s)
  fun fromMLstring s = stringSyntax.fromMLstring (string_uppercase s)
  fun is_const tm =
    (if rator tm ~~ ``Sym`` then can fromHOLstring (rand tm) else
     if rator tm ~~ ``Val`` then can numSyntax.int_of_term (rand tm) else
     if rator (rator tm) ~~ ``Dot`` then is_const (rand (rator tm)) andalso
                                         is_const (rand tm)
     else false) handle HOL_ERR _ => false
  val lisp_primitives =
    [(``Dot``,``opCONS``),
     (``LISP_CONS``,``opCONS``),
     (``LISP_EQUAL:SExp->SExp->SExp``,``opEQUAL``),
     (``LISP_LESS``,``opLESS``),
     (``LISP_SYMBOL_LESS``,``opSYMBOL_LESS``),
     (``LISP_ADD``,``opADD``),
     (``LISP_SUB``,``opSUB``),
     (``LISP_CONSP``,``opCONSP``),
     (``LISP_SYMBOLP``,``opSYMBOLP``),
     (``LISP_NUMBERP``,``opNATP``),
     (``CAR``,``opCAR``),
     (``CDR``,``opCDR``)]
  fun aux_fail tm =
    failwith("Unable to translate: \n\n" ^ term_to_string tm ^ "\n\n")
  fun aux tm =
    if is_const tm then ``Const`` $$ tm else
    if can (match_term ``Val n``) tm then aux_fail tm else
    if can (match_term ``Sym s``) tm then aux_fail tm else
    if is_var tm then let
      val (s,ty) = dest_var tm
      val _ = ty = ``:SExp`` orelse failwith("Variable of wrong type: " ^ s)
      in ``Var`` $$ fromMLstring s end
    else if is_cond tm then let
      val (x1,x2,x3) = dest_cond tm
      val _ = if rator x1 ~~ ``isTrue`` then () else aux_fail x1
      in ``If`` $$ aux (rand x1) $$ aux x2 $$ aux x3 end
    else if can pairSyntax.dest_anylet tm then let
      val (xs,x) = pairSyntax.dest_anylet tm
      val ys = map (fn (x,y) => pairSyntax.mk_pair(x |> dest_var |> fst |> fromMLstring, aux y)) xs
      val y = listSyntax.mk_list(ys,``:string # term``)
      in ``Let`` $$ y $$ (aux x) end
    else (* general function application *) let
      fun list_dest f tm = let val (x,y) = f tm in list_dest f x @ [y] end
                           handle HOL_ERR _ => [tm];
      val xs = list_dest dest_comb tm
      val (x,xs) = (hd xs, tl xs)
      fun lookup x [] = fail()
        | lookup x ((y,z)::zs) = if x ~~ y then z else lookup x zs
      val f = ``PrimitiveFun`` $$ lookup x lisp_primitives handle HOL_ERR _ =>
              ``Fun`` $$ fromMLstring (fst (dest_const x))
              handle HOL_ERR _ => aux_fail x
      val ys = map aux xs
      in ``App`` $$ f $$ listSyntax.mk_list(ys,``:term``) end
  fun preprocess tm = QCONV (REWRITE_CONV [isTrue_INTRO]) tm
  val th = preprocess tm
  val tm2 = rand (concl th)
  in (aux tm2, th) end

(*
val tm = ``let x = LISP_ADD x y in let z = y in LISP_SUB x y``
dest_term (fst (shallow_to_deep tm))

 plan: provide a method which, given a list of definition and
 induction thm pairs, produces deep embeddings and correspondence
 proofs.

*)


(* state of extraction function *)

local
  val lookup_thm = ref TRUTH;
  val assum_rw = ref TRUTH;
  val assum_clauses = ref (tl [TRUTH]);
  val atbl = ref (fn (name:string) => (fail():thm));
  fun set_assum_rw th = let
    val (x,y) = th |> SPEC_ALL |> concl |> dest_eq
    val name = (repeat rator x |> dest_const |> fst) ^ "_abbrev"
    val z = rand y
    val rw = Define `^(mk_eq(mk_var(name,type_of z),z))`
    val _ = assum_rw := (RW [GSYM rw] th)
    in th end
  fun fupdate x y f i = if x = i then y else f i;
  val lemma = prove(``(x = (y:bool)) ==> (x ==> y)``,SIMP_TAC std_ss [])
in
  fun set_lookup_thm th = (lookup_thm := th)
  fun get_lookup_thm () = !lookup_thm
  fun atbl_install name th = (atbl := fupdate name th (!atbl))
  fun atbl_lookup name = (!atbl) name
  fun install_assum_eq th =
    th |> SPEC_ALL |> concl |> rator |> rand
       |> (REWRITE_CONV [GSYM CONJ_ASSOC,set_assum_rw th,fns_assum_def,EVERY_DEF]
           THENC DEPTH_CONV (PairRules.PBETA_CONV))
       |> MATCH_MP lemma |> UNDISCH
       |> set_lookup_thm
  fun get_assum_rw () = !assum_rw
  fun add_assum_clause th = (assum_clauses := th::(!assum_clauses))
  fun get_assum_clauses () = !assum_clauses
end


(* R_ev a function which evaluates the semantics of pure functions *)

val PRW1 = PURE_ONCE_REWRITE_RULE

val mk_string = stringSyntax.fromMLstring

val simplify_name = let
  val normal_chars = explode "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
  fun to_lower c =
    if #"A" <= c andalso c <= #"Z"
    then chr (ord c + (ord #"a" - ord #"A")) else c
  in fn s =>
       if s = "<=" then "less_eq" else
         String.translate (fn c => if mem c normal_chars then implode [to_lower c] else "_") s end

fun prim2term op_CONS = ``opCONS``
  | prim2term op_EQUAL = ``opEQUAL``
  | prim2term op_LESS = ``opLESS``
  | prim2term op_SYMBOL_LESS = ``opSYMBOL_LESS``
  | prim2term op_ADD = ``opADD``
  | prim2term op_SUB = ``opSUB``
  | prim2term op_ATOMP = ``opATOMP``
  | prim2term op_CONSP = ``opCONSP``
  | prim2term op_NATP = ``opNATP``
  | prim2term op_SYMBOLP = ``opSYMBOLP``
  | prim2term op_CAR = ``opCAR``
  | prim2term op_CDR = ``opCDR``

fun R_ap (PrimitiveFun p) = SIMP_RULE std_ss [EVAL_DATA_OP_def] (SPEC (prim2term p) R_ap_PrimiveFun)
  | R_ap (Fun name) = atbl_lookup name
  | R_ap mDefine = R_ap_Define
  | R_ap Error = R_ap_Error
  | R_ap Print = R_ap_Print
  | R_ap (Funcall) = R_ap_Funcall

fun R_ev (Const c) = SPEC c R_ev_Const
  | R_ev (Var v) = SPEC (mk_string v) R_ev_Var
  | R_ev (If (x,y,z)) = MATCH_MP (MATCH_MP R_ev_If (LIST_CONJ [R_ev y,R_ev z])) (R_ev x)
  | R_ev (Or []) = R_ev_Or_NIL
  | R_ev (Or [x]) = MATCH_MP R_ev_Or_SING (R_ev x)
  | R_ev (Or (x::y::xs)) = MATCH_MP (MATCH_MP R_ev_Or_CONS_CONS (R_ev (Or (y::xs)))) (R_ev x)
  | R_ev (App (f,args)) = let
      fun R_evl [] = R_evl_NIL
        | R_evl (x::xs) = MATCH_MP (MATCH_MP R_evl_CONS (R_evl xs)) x
      val th = DISCH_ALL (R_evl (map (UNDISCH o R_ev) args))
               |> PURE_REWRITE_RULE [AND_IMP_INTRO]
      val th = if is_imp (concl th) then th else DISCH T th
      val th = MATCH_MP (MATCH_MP R_ev_App (R_ap f)) th
      val c = SIMP_CONV std_ss [TL,HD,EL_simp_restricted,LENGTH,EL]
      val th = CONV_RULE (BINOP_CONV c) th
      in th end
  | R_ev (LamApp (vs,body,args)) = let
      val th = MATCH_MP R_ev_LamApp (R_ev (Let (zip vs args,body)))
      val th = CONV_RULE ((RAND_CONV o RATOR_CONV o RAND_CONV o
                           RATOR_CONV o RAND_CONV) EVAL) th
      in th end
  | R_ev (Let (xs,x)) = let
      fun R_evl [] = R_evl_NIL
        | R_evl (x::xs) = MATCH_MP (MATCH_MP R_evl_CONS (R_evl xs)) x
      val th = DISCH_ALL (R_evl (map (UNDISCH o R_ev o snd) xs))
               |> PURE_REWRITE_RULE [AND_IMP_INTRO]
      val exps = th |> concl |> rand |> rand |> rator |> rand
      val xs1 = listSyntax.mk_list(map mk_string (map fst xs),``:string``)
      val th = MATCH_MP (SPEC xs1 R_ev_Let) th
      val th1 = R_ev x
      val tm1 = th1 |> concl |> rand |> rator |> rand |> rand
      val tm2 = th |> concl |> dest_imp |> fst |> rand |> rator |> rand |> rand
      val th = MATCH_MP th (INST (fst (match_term tm1 tm2)) th1)
      val c = SIMP_CONV std_ss [TL,HD,EL_simp_restricted,LENGTH,EL,ZIP]
      val th = CONV_RULE (BINOP_CONV c) th
      val tm = th |> concl |> rand |> rand |> rator |> rand
      val xs3 = map (fn x => mk_var(simplify_name(fst x),``:SExp``)) xs
      val xs4 = fst (listSyntax.dest_list exps)
      val tm2 = subst [``VarBind ^xs1 ^exps`` |-> ``VarBind ^xs1 ^(listSyntax.mk_list(xs3,``:SExp``))``] tm
      val tm3 = pairSyntax.mk_anylet(zip xs3 xs4,tm2)
      val rw = GSYM (pairLib.let_CONV tm3)
      val _ = ((fst o dest_eq o concl) rw ~~ tm) orelse
              failwith("R_ev (Let ...) failed.")
      val th = CONV_RULE ((RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV) (REWR_CONV rw)) th
      in th end
  | R_ev (LetStar ([],x)) = PRW1 [R_ev_LetStar_NIL] (R_ev x)
  | R_ev (LetStar ((v::vs),x)) = PRW1 [R_ev_LetStar_CONS] (R_ev (Let ([v],LetStar (vs,x))))
  | R_ev (First x)  = MATCH_MP R_ev_FIRST  (R_ev x)
  | R_ev (Second x) = MATCH_MP R_ev_SECOND (R_ev x)
  | R_ev (Third x)  = MATCH_MP R_ev_THIRD  (R_ev x)
  | R_ev (Fourth x) = MATCH_MP R_ev_FOURTH (R_ev x)
  | R_ev (Fifth x)  = MATCH_MP R_ev_FIFTH  (R_ev x)
  | R_ev (And [])  = PRW1 [R_ev_And_NIL] (R_ev (Const ``Sym "T"``))
  | R_ev (And [x])  = PRW1 [R_ev_And_SING] (R_ev x)
  | R_ev (And (x::y::xs))  = PRW1 [R_ev_And_CONS] (R_ev (If (x,And (y::xs),Const ``Sym "NIL"``)))
  | R_ev (List [])  = PRW1 [R_ev_List_NIL] (R_ev (Const ``Sym "NIL"``))
  | R_ev (List (x::xs)) = PRW1 [R_ev_List_CONS] (R_ev (App (PrimitiveFun op_CONS,[x,List xs])))
  | R_ev (Cond [])  = PRW1 [R_ev_Cond_NIL] (R_ev (Const ``Sym "NIL"``))
  | R_ev (Cond ((x1,x2)::xs))  = PRW1 [R_ev_Cond_CONS] (R_ev (If (x1,x2,Cond xs)))
  | R_ev _ = failwith("Unsupported construct.")


(* extraction of pure functions *)

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

local
  val tm1 = ``(f:'a |-> 'b) ' z``
  val tm2 = ``x IN FDOM (f:'a |-> 'b)``
in
  fun is_fapply_or_in_fdom tm =
    can (match_term tm1) tm orelse can (match_term tm2) tm
end

fun eval_fappy_conv tm =
  if not (is_fapply_or_in_fdom tm) then NO_CONV tm else
    (REWRITE_CONV [VarBind_def,VarBindAux_def,FDOM_FUPDATE,FDOM_FEMPTY,IN_INSERT,
       IN_UNION,REVERSE_DEF,APPEND,FAPPLY_FUPDATE_THM,FUNION_DEF,NOT_IN_EMPTY] THENC
     DEPTH_CONV stringLib.string_EQ_CONV THENC
     REWRITE_CONV []) tm

fun diff xs ys = filter (fn x => not (mem x ys)) xs
fun mk_sexp_fun_ty x = mk_type("fun",[``:SExp``,x])
fun CS rw = ConseqConv.CONSEQ_REWRITE_CONV ([], rw, [])
            ConseqConv.CONSEQ_CONV_STRENGTHEN_direction

fun pure_extract name term_tac = let
  val _ = print ("extracting: "^name^"\n")
  (* evaluate semantics *)
  val name_tm = stringSyntax.fromMLstring name
  val (ps,t) = ``(k:string |-> string list # term) ' ^name_tm``
                |> REWRITE_CONV [get_lookup_thm()]
                |> concl |> rand |> pairSyntax.dest_pair
  val args = ps |> listSyntax.dest_list |> fst |> map stringSyntax.fromHOLstring
                |> map (fn s => mk_var(simplify_name s,``:SExp``))
                |> (fn xs => listSyntax.mk_list(xs,``:SExp``))
  val v = mk_var("__result__",``:SExp list -> SExp``)
  val lemma = DISCH_ALL (ASSUME ``R_ap (Fun ^name_tm,args,e,fns,io,ok) (^v args,fns,io,ok)``)
  val _ = atbl_install name lemma
  fun FORCE_UNDISCH th = UNDISCH th handle HOL_ERR _ => th
  val mt = dest_term t
  val th1 = FORCE_UNDISCH (SIMP_RULE std_ss [] (R_ev mt)) |> remove_primes
  val th2 = CS [R_ap_Fun] ``R_ap (Fun ^name_tm,^args,e,k,io,ok) (ans,k2,io2,ok2)``
            |> SIMP_RULE std_ss [get_lookup_thm(),LENGTH]
  val tm2 = th2 |> concl |> rator |> rand
  val tm1 = th1 |> concl
  val s = fst (match_term (rator tm1) (rator tm2))
  val c = DEPTH_CONV eval_fappy_conv
  val th4 = MATCH_MP th2 (INST s th1) |> DISCH_ALL |> RW [AND_IMP_INTRO]
            |> CONV_RULE (BINOP_CONV c)
  (* invent function *)
  val good_name = simplify_name name
  val params = listSyntax.dest_list args |> fst
  val ty = foldr (fn (x,y) => mk_sexp_fun_ty y) ``:SExp`` params
  val new_fun = mk_var(good_name,ty)
  val lhs = foldl (fn (x,y) => mk_comb(y,x)) new_fun params
  fun mk_els [] access = []
    | mk_els (x::xs) access = ((x:term) |-> ``HD ^access``) :: mk_els xs ``TL ^access``
  val args_var = ``args:SExp list``
  val tm = mk_abs(args_var,subst (mk_els params args_var) lhs)
  val th5 = INST [v|->tm] th4 |> SIMP_RULE std_ss [HD,TL,isTrue_if]
  val rhs = th5 |> concl |> rand |> rand |> rator |> rand
  val def_tm = mk_eq(lhs,rhs)
  val (def,ind) = new_def def_tm term_tac
  val const_tm = def |> SPEC_ALL |> concl |> rator |> rand |> repeat rator
  (* prove certificate theorem *)
  val th6 = INST [new_fun |-> const_tm] th5 |> RW1 [GSYM def]
  val goal = mk_imp(hd (hyp (get_lookup_thm())),th6 |> concl |> rand)
  val f = foldr mk_abs goal params
  val forall_goal = foldr mk_forall goal params
  val result = case ind of
      NONE    => RW [] th6
    | SOME i  => let
        val i = ISPEC f i |> CONV_RULE (DEPTH_CONV BETA_CONV)
        val result = prove(i |> concl |> rand,
          PURE_ONCE_REWRITE_TAC [R_ap_SET_ENV]
          \\ MATCH_MP_TAC (RW1 [R_ap_SET_ENV] i) \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC (RW1 [R_ap_SET_ENV] th6) \\ ASM_REWRITE_TAC []
          \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [] \\ RES_TAC
          \\ METIS_TAC []) |> SPECL params
        in result end
  (* install for future use *)
  val _ = atbl_install name result
  val _ = save_thm(good_name ^ "_def[compute]",def)
  val _ = save_thm("R_ev_" ^ good_name,result)
  in def end;

val pure_extract = fn n => fn tac => allowing_rebinds (pure_extract n) tac

fun pure_extract_mutual_rec names term_tac = let
  val _ = print "extracting:"
  val _ = map (fn name => print (" " ^ name)) names
  val _ = print "\n"
  (* evaluate semantics *)
  fun gen_data name = let
    val name_tm = stringSyntax.fromMLstring name
    val (ps,t) = ``(k:string |-> string list # term) ' ^name_tm``
                  |> REWRITE_CONV [get_lookup_thm()]
                  |> concl |> rand |> pairSyntax.dest_pair
    val args = ps |> listSyntax.dest_list |> fst |> map stringSyntax.fromHOLstring
                  |> map (fn s => mk_var(simplify_name s,``:SExp``))
                  |> (fn xs => listSyntax.mk_list(xs,``:SExp``))
    val v = mk_var("__" ^ name ^ "__result__",``:SExp list -> SExp``)
    val lemma = DISCH_ALL (ASSUME ``R_ap (Fun ^name_tm,args,e,fns,io,ok) (^v args,fns,io,ok)``)
    val _ = atbl_install name lemma
    in (name,name_tm,t,args,v,lemma) end
  val data = map gen_data names
  fun FORCE_UNDISCH th = UNDISCH th handle HOL_ERR _ => th
  fun derive_thm (name,name_tm,t,args,v,lemma) = let
    val mt = dest_term t
    val th1 = FORCE_UNDISCH (SIMP_RULE std_ss [] (R_ev mt)) |> remove_primes
    val th2 = CS [R_ap_Fun] ``R_ap (Fun ^name_tm,^args,e,k,io,ok) (ans,k2,io2,ok2)``
              |> SIMP_RULE std_ss [get_lookup_thm(),LENGTH]
    val tm2 = th2 |> concl |> rator |> rand
    val tm1 = th1 |> concl
    val s = fst (match_term (rator tm1) (rator tm2))
    val c = DEPTH_CONV eval_fappy_conv
    val th4 = MATCH_MP th2 (INST s th1) |> DISCH_ALL |> RW [AND_IMP_INTRO]
              |> CONV_RULE (BINOP_CONV c)
    in th4 end;
  val thms = map derive_thm data
  (* invent function *)
  fun common_name [] = ""
    | common_name [name] = name
    | common_name (x::xs) = x ^ "_" ^ common_name xs
  val good_name = simplify_name (common_name names)
  fun mk_tuple [] = mk_var("()",``:unit``)
    | mk_tuple [x] = x
    | mk_tuple (x::xs) = pairSyntax.mk_pair(x,mk_tuple xs)
  val xs = map (fn (name,name_tm,t,args,v,lemma) =>
                  mk_tuple (listSyntax.dest_list args |> fst)) data
  fun list_mk_sum_ty [] = fail()
    | list_mk_sum_ty [x] = x
    | list_mk_sum_ty (x::xs) = mk_type("sum",[x,list_mk_sum_ty xs])
  val input_ty = list_mk_sum_ty (map type_of xs)
  val new_fun = mk_var(good_name,mk_type("fun",[input_ty,``:SExp``]))
  fun params [] ty = []
    | params [v] ty = [v]
    | params (v::vs) ty = let
        val ts = snd (dest_type ty)
        val t1 = el 1 ts
        val t2 = el 2 ts
        in sumSyntax.mk_inl(v,t2) ::
           map (fn x => sumSyntax.mk_inr(x,t1)) (params vs t2) end
  val ps = params xs input_ty
  val lhs = map (fn x => mk_comb(new_fun,x)) ps
  fun mk_els [] access = []
    | mk_els (x::xs) access = ((x:term) |-> ``HD ^access``) :: mk_els xs ``TL ^access``
  val args_var = ``args:SExp list``
  fun make_subs ((name,name_tm,t,args,v,lemma),(input,l)) =
    v |-> mk_abs(args_var,subst (mk_els (fst (listSyntax.dest_list args)) args_var) l)
  val ss = map make_subs (zip data (zip ps lhs))
  val ys = map (SIMP_RULE std_ss [HD,TL,isTrue_if] o INST ss) thms
  val rhs = map (fst o pairSyntax.dest_pair o
                 snd o dest_comb o snd o dest_comb o concl) ys
  val def_tm = list_mk_conj (map mk_eq (zip lhs rhs))
  val def = case term_tac of
               NONE => Define [ANTIQUOTE def_tm]
             | SOME t => tDefine good_name [ANTIQUOTE def_tm] t
  val ind = fetch "-" (good_name ^ "_ind")
  val const_tm = def |> SPEC_ALL |> CONJUNCTS |> last
                     |> concl |> rator |> rand |> repeat rator
  (* prove certificate theorem *)
  val zs = map (RW1 [R_ap_SET_ENV] o RW1 [GSYM def] o INST [new_fun|->const_tm]) ys
  val aps = map (snd o dest_comb o concl) zs
  val extra = hd aps |> rand |> rand
  val new_prop = mk_var(good_name ^ "_prop",mk_type("fun",[type_of extra,mk_type("fun",[input_ty,``:bool``])]))
  val ind_hyp_tm = map (fn (x,y) => mk_eq(mk_comb(mk_comb(new_prop,extra),x),y)) (zip ps aps)
                   |> list_mk_conj
  val ind_hyp = Define [ANTIQUOTE ind_hyp_tm] |> SPEC_ALL
  val tm = ind_hyp |> CONJUNCTS |> hd |> concl |> rator |> rand |> rator
  val input_var = mk_var("input",input_ty)
  val tt = mk_comb(tm,input_var)
  val tt = mk_imp(hd (hyp (get_lookup_thm())),tt)
  val goal = mk_forall(input_var,tt)
  val i = ISPEC (mk_abs(input_var,tt)) ind |> CONV_RULE (DEPTH_CONV BETA_CONV)
  val th = prove(i |> concl |> rand,
   MATCH_MP_TAC i \\ SIMP_TAC std_ss [ind_hyp]
   \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
   \\ EVERY (map IMP_RES_TAC zs) \\ FULL_SIMP_TAC std_ss [])
  val rs = (map (fn p => RW [ind_hyp] (SPEC p th)
        |> CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [GSYM R_ap_SET_ENV]))) ps)
  (* split the common definition *)
  fun define_parts ((name,name_tm,t,args,v,lemma),th) = let
    val tm = th |> concl |> rand |> rand |> pairSyntax.dest_pair |> fst
    val vs = free_vars tm
    val ty = foldr (fn (x,y) => mk_sexp_fun_ty y) ``:SExp`` vs
    val new_fun = mk_var(simplify_name name,ty)
    val l = foldl (fn (x,y) => mk_comb(y,x)) new_fun (fst (listSyntax.dest_list args))
    val part = Define [ANTIQUOTE (mk_eq(l,tm))]
    in part end
  val defs = map define_parts (zip data rs)
  val result = map (RW (map GSYM defs)) rs
  val real_defs = RW (map GSYM defs) def |> CONJUNCTS
  val _ = map (fn (name,def) => save_thm(simplify_name name ^ "_def",def)) (zip names real_defs)
  val _ = map (fn (name,res) => save_thm("R_ev_" ^ simplify_name name,res)) (zip names result)
  (* install for future use *)
  val _ = map (fn (name,res) => atbl_install name res) (zip names result)
  in def end;


(* G_ev a function which evaluates the semantics of any functions *)

local
  val R_ev_format = ``b ==> R_ev x (x1,x2,x3,x4)``
  val R_ev_EXAPND_LEMMA = prove(
    ``(b ==> R_ev x y) ==>
      (b ==> R_ev x (FST y,FST (SND y),FST (SND (SND y)),SND (SND (SND y))))``,
    SIMP_TAC std_ss []);
in
  fun R_ev_EXPAND th =
    if can (match_term R_ev_format) (concl th) then th else
      MATCH_MP R_ev_EXAPND_LEMMA th
end

fun TUPLE_CONV c tm =
  if pairSyntax.is_pair tm then
    ((RATOR_CONV o RAND_CONV) c THENC
     RAND_CONV (TUPLE_CONV c)) tm
  else c tm

fun G_ev (Const c) = SPEC c R_ev_Const
  | G_ev (Var v) = SPEC (mk_string v) R_ev_Var
  | G_ev (If (x,y,z)) = let
      val th = LIST_CONJ [G_ev y, G_ev z]
      val th = MATCH_MP (MATCH_MP R_ev_If_GENERAL th) (R_ev_EXPAND (G_ev x))
      val th = CONV_RULE (BINOP_CONV (REWRITE_CONV [])) th
      in th end
  | G_ev (Or []) = R_ev_Or_NIL
  | G_ev (Or [x]) = PRW1 [R_ev_Or_SING_EQ] (G_ev x)
  | G_ev (Or (x::y::xs)) = let
      val th = (G_ev (Or (y::xs)))
      val th = MATCH_MP (MATCH_MP R_ev_Or_CONS_CONS_GENERAL th) (R_ev_EXPAND (G_ev x))
      val th = CONV_RULE (BINOP_CONV (REWRITE_CONV [])) th
      in th end
  | G_ev (App (f,args)) = let
      fun R_evl [] = DISCH T R_evl_NIL
        | R_evl (x::xs) = MATCH_MP (MATCH_MP R_evl_CONS_GENERAL (R_evl xs)) x
      val th = R_evl (map (R_ev_EXPAND o G_ev) args)
      val th = MATCH_MP (MATCH_MP R_ev_App (R_ap f)) th
      val c = REWRITE_CONV [TL,HD,EL_simp_restricted,LENGTH,EL]
      val th = CONV_RULE (BINOP_CONV c) th
      in th end
  | G_ev (Let (xs,x)) = let
      val prefix = "let " ^ concat (map ((fn x => x ^ " ") o fst) xs) ^ ": "
      val _ = print (prefix ^ "starts\n")
      fun R_evl [] = DISCH T R_evl_NIL
        | R_evl (x::xs) = MATCH_MP (MATCH_MP R_evl_CONS_GENERAL (R_evl xs)) x
      val s = REWRITE_CONV [FST_SND_IF,pairTheory.FST,pairTheory.SND]
      val th = R_evl (map (R_ev_EXPAND o G_ev o snd) xs)
               |> CONV_RULE ((RAND_CONV o RAND_CONV) (TUPLE_CONV s))
      val exps = th |> concl |> rand |> rand |> rator |> rand
      val xs1 = listSyntax.mk_list(map mk_string (map fst xs),``:string``)
      val th = MATCH_MP (SPEC xs1 R_ev_Let_GENERAL) th
      val th = PRW1 [pairTheory.SND,pairTheory.FST] th
      val _ = print (prefix ^ "down\n")
      val th0 = G_ev x
      val _ = print (prefix ^ "up, expanding\n")
      val th1 = R_ev_EXPAND th0
      val _ = print (prefix ^ "simp\n")
      val th1 = CONV_RULE ((RAND_CONV o RAND_CONV) (TUPLE_CONV s)) th1
      val _ = print (prefix ^ "match\n")
      val tm1 = th1 |> concl |> rand |> rator |> rand |> rand
      val tm2 = th |> concl |> dest_imp |> fst |> rand |> rator |> rand |> rand
      val th = MATCH_MP th (INST (fst (match_term tm1 tm2)) th1)
      val _ = print (prefix ^ "cleaning\n")
      val c = REWRITE_CONV [TL,HD,EL_simp_restricted,LENGTH,EL,ZIP]
      val th = CONV_RULE (BINOP_CONV c) th
      val tm = th |> concl |> rand |> rand
      val pre = th |> concl |> rator |> rand
      val xs3 = map (fn x => mk_var(simplify_name(fst x),``:SExp``)) xs
      val xs4 = fst (listSyntax.dest_list exps)
      val sub = [``VarBind ^xs1 ^exps`` |->
                 ``VarBind ^xs1 ^(listSyntax.mk_list(xs3,``:SExp``))``]
      val tm2 = subst sub tm
      val pre2 = subst sub pre
      val tm3 = pairSyntax.mk_anylet(zip xs3 xs4,tm2)
      val pre3 = pairSyntax.mk_anylet(zip xs3 xs4,pre2)
      val rw = SYM (pairLib.let_CONV tm3)
      val pre_rw = SYM (pairLib.let_CONV pre3)
      val th = CONV_RULE ((RAND_CONV o RAND_CONV) (REWR_CONV rw) THENC
                          (RATOR_CONV o RAND_CONV) (REWR_CONV pre_rw)) th
      val _ = print (prefix ^ "done\n")
      in th end
  | G_ev (LamApp (vs,body,args)) = let
      val th = MATCH_MP R_ev_LamApp (G_ev (Let (zip vs args,body)))
      val th = CONV_RULE ((RAND_CONV o RATOR_CONV o RAND_CONV o
                           RATOR_CONV o RAND_CONV) EVAL) th
      in th end
  | G_ev (LetStar ([],x)) = PRW1 [R_ev_LetStar_NIL] (G_ev x)
  | G_ev (LetStar ((v::vs),x)) = PRW1 [R_ev_LetStar_CONS] (G_ev (Let ([v],LetStar (vs,x))))
  | G_ev (First x)  = MATCH_MP R_ev_FIRST_GENERAL  (G_ev x)
  | G_ev (Second x) = MATCH_MP R_ev_SECOND_GENERAL (G_ev x)
  | G_ev (Third x)  = MATCH_MP R_ev_THIRD_GENERAL  (G_ev x)
  | G_ev (Fourth x) = MATCH_MP R_ev_FOURTH_GENERAL (G_ev x)
  | G_ev (Fifth x)  = MATCH_MP R_ev_FIFTH_GENERAL  (G_ev x)
  | G_ev (And [])  = PRW1 [R_ev_And_NIL] (G_ev (Const ``Sym "T"``))
  | G_ev (And [x])  = PRW1 [R_ev_And_SING] (G_ev x)
  | G_ev (And (x::y::xs))  = PRW1 [R_ev_And_CONS] (G_ev (If (x,And (y::xs),Const ``Sym "NIL"``)))
  | G_ev (List [])  = PRW1 [R_ev_List_NIL] (G_ev (Const ``Sym "NIL"``))
  | G_ev (List (x::xs)) = PRW1 [R_ev_List_CONS] (G_ev (App (PrimitiveFun op_CONS,[x,List xs])))
  | G_ev (Cond [])  = PRW1 [R_ev_Cond_NIL] (G_ev (Const ``Sym "NIL"``))
  | G_ev (Cond ((x1,x2)::xs))  = PRW1 [R_ev_Cond_CONS] (G_ev (If (x1,x2,Cond xs)))
  | G_ev _ = failwith("Unsupported construct.")


(* extraction of impure functions *)

val let_intro_rule = let
  val let_lemma = prove(``!f x. f x = LET (f:'a->'b) x``,SIMP_TAC std_ss [LET_DEF])
  fun let_intro_conv_aux tm = let
    val (x,y) = dest_comb tm
    val (vs,a) = pairSyntax.dest_pabs x
    val _ = pairSyntax.is_pair vs orelse fail()
    in ISPEC y (ISPEC x let_lemma) end
  in CONV_RULE (DEPTH_CONV let_intro_conv_aux) end;

val expand_pair_eq_rule = let
  val pair_eq_lemma = prove(
    ``!p x y. ((x,y) = p) = (((x:'a) = FST p) /\ ((y:'b) = SND p))``,
    Cases_on `p` \\ SIMP_TAC std_ss [])
  fun let_intro_conv_aux tm = let
    val (xy,p) = dest_eq tm
    val (x,y) = dest_pair xy
    in ISPEC y (ISPEC x (ISPEC p pair_eq_lemma)) end
  in PURE_REWRITE_RULE [pair_eq_lemma] end

fun mk_fun_ty t x = mk_type("fun",[t,x])

val R_ap_format = ``R_ap x y``

fun extract_side_condition tm =
  if tm ~~ T then T else let
  val (x,y) = dest_conj tm
  val x1 = extract_side_condition x
  val y1 = extract_side_condition y
  in if x1 ~~ T then y1 else
     if y1 ~~ T then x1 else mk_conj(x1,y1) end
  handle HOL_ERR _ => let
  val fns_assum = hd (hyp (get_lookup_thm()))
  val _ = match_term fns_assum tm
  in T end
  handle HOL_ERR _ => let
  val (x,y,z) = dest_cond tm
  val y1 = extract_side_condition y
  val z1 = extract_side_condition z
  in if y1 ~~ T andalso z1 ~~ T then T else mk_cond(x,y1,z1) end
  handle HOL_ERR _ => let
  val (x,y) = dest_imp tm
  val y1 = extract_side_condition y
  in if y1 ~~ T then T else mk_imp(x,y1) end
  handle HOL_ERR _ => let
  val _ = match_term R_ap_format tm
  in T end
  handle HOL_ERR _ => let
  val (xs,b) = pairSyntax.dest_anylet tm
  val b1 = extract_side_condition b
  in if b1 ~~ T then T else pairSyntax.mk_anylet(xs,b1) end
  handle HOL_ERR _ => tm

fun impure_extract_aux name term_tac use_short_cut = let
  val _ = print ("extracting: "^name^"\n")
  (* evaluate semantics *)
  val name_tm = stringSyntax.fromMLstring name
  val (ps,t) = ``(k:string |-> string list # term) ' ^name_tm``
                |> REWRITE_CONV [get_lookup_thm()]
                |> concl |> rand |> pairSyntax.dest_pair
  val args = ps |> listSyntax.dest_list |> fst |> map stringSyntax.fromHOLstring
                |> map (fn s => mk_var(simplify_name s,``:SExp``))
                |> (fn xs => listSyntax.mk_list(xs,``:SExp``))
  val ty = ``:(string |-> string list # term) # string # bool``
  val v = mk_var("__result__",``:SExp list # ^ty -> SExp # ^ty``)
  val v2 = mk_var("__result_side__",``:SExp list # ^ty -> bool``)
  val lemma = DISCH_ALL (ASSUME ``R_ap (Fun ^name_tm,args,e,fns,io,ok) (^v (args,fns,io,ok))``)
              |> DISCH ``^v2 (args,fns,io,ok)`` |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val _ = atbl_install name lemma
  fun FORCE_UNDISCH th = UNDISCH th handle HOL_ERR _ => th
  val mt = dest_term t
  val th0 = G_ev mt
  val th1 = FORCE_UNDISCH (SIMP_RULE std_ss [FST_SND_IF,EL,HD] th0) |> remove_primes
  val th2 = CS [R_ap_Fun] ``R_ap (Fun ^name_tm,^args,e,k,io,ok) res``
            |> SIMP_RULE std_ss [get_lookup_thm(),LENGTH]
  val tm2 = th2 |> concl |> rator |> rand
  val tm1 = th1 |> concl
  val s = fst (match_term (rator tm1) (rator tm2))
  val c = DEPTH_CONV eval_fappy_conv
  val th4 = MATCH_MP th2 (INST s th1) |> DISCH_ALL |> RW [AND_IMP_INTRO]
            |> CONV_RULE (BINOP_CONV c) |> RW [isTrue_T]
  val th4 = if not use_short_cut then th4 else
              SPECL [name_tm,ps,args,t] R_ap_NOT_OK
              |> SIMP_RULE std_ss [get_lookup_thm(),LENGTH]
              |> (fn th5 => MATCH_MP th5 th4) |> DISCH_ALL |> RW [AND_IMP_INTRO]
  (* invent function *)
  val good_name = simplify_name name
  val params1 = listSyntax.dest_list args |> fst
  val tm = R_ev_Const |> SPEC_ALL |> Q.INST [`fns`|->`k`] |> concl |> rand |> rand |> rand
  val params = params1 @ rev (free_vars tm)
  val fun_ty = foldr (fn (x,y) => mk_fun_ty (type_of x) y) ``:SExp # ^ty`` params
  val new_fun = mk_var(good_name,fun_ty)
  val lhs = foldl (fn (x,y) => mk_comb(y,x)) new_fun params
  fun mk_els [] access = []
    | mk_els (x::xs) access = ((x:term) |-> ``HD ^access``) :: mk_els xs ``TL ^access``
  val args_var = ``args:SExp list``
  val vars = ``(args,k,io,ok): (SExp list # (string |-> string list # term) # string # bool)``
  val tm = pairSyntax.mk_pabs(vars,subst (mk_els params1 args_var) lhs)
  val th5 = INST [v|->tm] th4 |> SIMP_RULE std_ss [HD,TL,isTrue_if] |> let_intro_rule
  val rhs = th5 |> concl |> rand |> rand
  val def_tm = mk_eq(lhs,rhs)
  val (def,ind) = new_def def_tm term_tac
  val const_tm = def |> SPEC_ALL |> concl |> rator |> rand |> repeat rator
  (* invent side condition *)
  val fns_assum = hd (hyp (get_lookup_thm()))
  val tm = fst (dest_imp (concl th4))
  val side_fun_ty = foldr (fn (x,y) => mk_fun_ty (type_of x) y) ``:bool`` params
  val side_new_fun = mk_var(good_name ^ "_side",side_fun_ty)
  val side_lhs = foldl (fn (x,y) => mk_comb(y,x)) side_new_fun params
  val side_tm = pairSyntax.mk_pabs(vars,subst (mk_els params1 args_var) side_lhs)
  val side_rhs = subst [v2|->side_tm] (extract_side_condition tm)
                 |> QCONV (SIMP_CONV std_ss [HD,TL,FST_SND_IF,isTrue_if])
                 |> let_intro_rule |> concl |> rand
  val side_def_tm = mk_eq(side_lhs,side_rhs)
  val (side_def,_) = new_def side_def_tm term_tac
  val side_const_tm_full = side_def |> SPEC_ALL |> concl |> rator |> rand
  val side_const_tm = side_const_tm_full |> repeat rator
  val th6 = INST [v2|->side_tm] th5 |> SIMP_RULE std_ss [HD,TL,isTrue_if] |> let_intro_rule
  (* prove certificate theorem *)
  val th7 = INST [new_fun |-> const_tm, side_new_fun |-> side_const_tm] th6 |> RW1 [GSYM def]
  val lhs = mk_conj(hd (hyp (get_lookup_thm())),side_const_tm_full)
  val goal = mk_imp(lhs,th7 |> concl |> rand)
  val f = foldr mk_abs goal params
  val forall_goal = foldr mk_forall goal params
(*
   val (SOME i) = ind
   set_goal([],i |> concl |> rand)
   set_goal([],forall_goal)
*)
  val result = case ind of
      NONE    => let
        val result = prove(forall_goal,
          PURE_ONCE_REWRITE_TAC [side_def]
          \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC th7
          \\ FULL_SIMP_TAC std_ss [LET_DEF]
          \\ SRW_TAC [] []
          \\ FULL_SIMP_TAC std_ss (get_assum_clauses())) |> SPECL params
        in result end
    | SOME i  => let
        val i = SIMP_RULE std_ss [] (expand_pair_eq_rule i)
        val i = ISPEC f i |> CONV_RULE (DEPTH_CONV BETA_CONV)
        val result = prove(i |> concl |> rand,
          PURE_ONCE_REWRITE_TAC [R_ap_SET_ENV]
          \\ MATCH_MP_TAC (RW1 [R_ap_SET_ENV] i) \\ REPEAT STRIP_TAC
          \\ Q.PAT_ASSUM [ANTIQUOTE side_const_tm_full] MP_TAC
          \\ ONCE_REWRITE_TAC [side_def] \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC (RW1 [R_ap_SET_ENV] th7) \\ ASM_REWRITE_TAC []
          \\ FULL_SIMP_TAC std_ss [LET_DEF]
          \\ REPEAT (POP_ASSUM MP_TAC)
          \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
          \\ ONCE_REWRITE_TAC [R_ap_SET_ENV]
          \\ FULL_SIMP_TAC std_ss (get_assum_clauses())
          \\ METIS_TAC []) |> SPECL params
        in result end
  (* derive assum clause *)
  val func_tm = def |> SPEC_ALL |> concl |> rator |> rand
  val assum_tm = (hd (hyp (get_lookup_thm())))
  val goal = mk_imp(assum_tm,mk_comb(rator assum_tm,mk_fst(mk_snd(func_tm))))
  val f = foldr mk_abs goal params
  val forall_goal = foldr mk_forall goal params
(*
   val (SOME i) = ind
   set_goal([],i |> concl |> rand)
   set_goal([],forall_goal)
*)
  val clause_rw = (fns_assum_add_def_IMP::
                   fns_assum_funcall_IMP::
                   (map (RW[get_assum_rw()]) (get_assum_clauses())))
  val clause = case ind of
      NONE    => let
        val clause = prove(forall_goal,
          SRW_TAC [] [def,LET_DEF,get_assum_rw()]
          \\ IMP_RES_TAC fns_assum_funcall_IMP
          \\ FULL_SIMP_TAC std_ss clause_rw) |> SPECL params
          handle HOL_ERR _ => TRUTH
        in clause end
    | SOME i  => let
        val i = SIMP_RULE std_ss [] (expand_pair_eq_rule i)
        val i = ISPEC f i |> CONV_RULE (DEPTH_CONV BETA_CONV)
        val clause = prove(i |> concl |> rand,
          MATCH_MP_TAC i \\ SRW_TAC [] [get_assum_rw()]
          \\ REPEAT STRIP_TAC
          \\ ONCE_REWRITE_TAC [def]
          \\ FULL_SIMP_TAC std_ss [LET_DEF]
          \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
          \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [EL]
          \\ FULL_SIMP_TAC std_ss clause_rw
          \\ METIS_TAC clause_rw) |> SPECL params
        in clause end
  (* install for future use *)
  val _ = atbl_install name result
  val _ = add_assum_clause clause
  val _ = save_thm(good_name ^ "_def",def)
  val _ = save_thm("R_ev_" ^ good_name,result)
  in def end;

val impure_extract_aux =
    fn n => fn tac => fn b => allowing_rebinds (impure_extract_aux n tac) b

fun impure_extract name term_tac =
  impure_extract_aux name term_tac false

fun impure_extract_cut name term_tac =
  impure_extract_aux name term_tac true


(* generator *)

fun deep_embeddings base_name defs_inds = let
  (* generate deep embeddings *)
  fun fromMLstring s = stringSyntax.fromMLstring (string_uppercase s)
  fun parts (def,ind) = let
    val (x,y) = dest_eq (concl (SPEC_ALL def))
    val (body,rw) = shallow_to_deep y
    fun list_dest f tm = let val (x,y) = f tm in list_dest f x @ [y] end
                         handle HOL_ERR _ => [tm];
    val xs = list_dest dest_comb x
    val params = xs |> tl |> map (fst o dest_var)
    val name = xs |> hd |> dest_const |> fst
    val strs = listSyntax.mk_list(map fromMLstring params,``:string``)
    val x1 = pairSyntax.mk_pair(strs,body)
    val x1 = pairSyntax.mk_pair(fromMLstring name,x1)
    in (name,params,def,ind,body,rw,x1) end;
  val ps = map parts defs_inds
  val xs = ps |> map (fn (name,params,def,ind,body,rw,x1) => x1)
  val xs = listSyntax.mk_list(xs,type_of (hd xs))
  val x = SPEC xs (Q.SPEC `k` fns_assum_def) |> concl |> dest_eq |> fst
  val tm = ``v k = ^x``
  val v = tm |> dest_eq |> fst |> repeat rator
  val vv = mk_var(base_name,type_of v)
  val fns_assum = new_definition(base_name^"_def",subst [v|->vv] tm) |> SPEC_ALL
  (* prove correspondence *)
  val _ = install_assum_eq fns_assum
(*
    val (name,params,def,ind,body,rw,x1) = el 1 ps
*)
  fun prove_corr (name,params,def,ind,body,rw,x1) = let
    val name_tm = fromMLstring name
    val (ps,t) = ``(k:string |-> string list # term) ' ^name_tm``
                  |> REWRITE_CONV [get_lookup_thm()]
                  |> concl |> rand |> pairSyntax.dest_pair
    val args = ps |> listSyntax.dest_list |> fst |> map stringSyntax.fromHOLstring
                  |> map (fn s => mk_var(simplify_name s,``:SExp``))
                  |> (fn xs => listSyntax.mk_list(xs,``:SExp``))
    val v = mk_var("__result__",``:SExp list -> SExp``)
    val lemma = DISCH_ALL (ASSUME ``R_ap (Fun ^name_tm,args,e,fns,io,ok) (^v args,fns,io,ok)``)
    val _ = atbl_install (string_uppercase name) lemma
    fun FORCE_UNDISCH th = UNDISCH th handle HOL_ERR _ => th
    val mt = dest_term t
    val th1 = FORCE_UNDISCH (SIMP_RULE std_ss [] (R_ev mt)) |> remove_primes
    val th2 = CS [R_ap_Fun] ``R_ap (Fun ^name_tm,^args,e,k,io,ok) (ans,k2,io2,ok2)``
              |> SIMP_RULE std_ss [get_lookup_thm(),LENGTH]
    val tm2 = th2 |> concl |> rator |> rand
    val tm1 = th1 |> concl
    val s = fst (match_term (rator tm1) (rator tm2))
    val c = DEPTH_CONV eval_fappy_conv
    val th4 = MATCH_MP th2 (INST s th1) |> DISCH_ALL |> RW [AND_IMP_INTRO]
              |> CONV_RULE (BINOP_CONV c)
    (* connect function *)
    val good_name = simplify_name name
    val params = listSyntax.dest_list args |> fst
    val ty = foldr (fn (x,y) => mk_sexp_fun_ty y) ``:SExp`` params
    val new_fun = def |> concl |> dest_eq |> fst |> repeat rator
    val lhs = foldl (fn (x,y) => mk_comb(y,x)) new_fun params
    fun mk_els [] access = []
      | mk_els (x::xs) access = ((x:term) |-> ``HD ^access``) :: mk_els xs ``TL ^access``
    val args_var = ``args:SExp list``
    val tm = mk_abs(args_var,subst (mk_els params args_var) lhs)
    val th5 = INST [v|->tm] th4 |> SIMP_RULE std_ss [HD,TL,isTrue_if]
    val def1 = def |> ONCE_REWRITE_RULE [rw]
    val th6 = th5 |> REWRITE_RULE [lisp_sexpTheory.LISP_CONS_def]
              |> CONV_RULE ((RAND_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM def1]))
    (* prove certificate theorem *)
    val goal = mk_imp(hd (hyp (get_lookup_thm())),th6 |> concl |> rand)
    val f = foldr mk_abs goal params
    val forall_goal = foldr mk_forall goal params
    val result = if concl ind ~~ T then RW [] th6 else let
          val i = ISPEC f ind |> CONV_RULE (DEPTH_CONV BETA_CONV)
          val i = REWRITE_RULE [isTrue_INTRO] i
          val result = prove(i |> concl |> rand,
            PURE_ONCE_REWRITE_TAC [R_ap_SET_ENV]
            \\ MATCH_MP_TAC (RW1 [R_ap_SET_ENV] i) \\ REPEAT STRIP_TAC
            \\ MATCH_MP_TAC (RW1 [R_ap_SET_ENV] th6) \\ ASM_REWRITE_TAC []
            \\ REPEAT STRIP_TAC \\ METIS_TAC [isTrue_INTRO]) |> SPECL params
          in result end
    (* install for future use *)
    val _ = atbl_install (string_uppercase name) result
    val _ = save_thm("R_ap_" ^ name,result)
    in result end;
  val thms = map prove_corr ps
  in (fns_assum,thms) end;


end;
