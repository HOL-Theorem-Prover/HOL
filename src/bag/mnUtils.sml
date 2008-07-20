structure mnUtils = struct

infix ##

local
  open HolKernel boolLib Parse
  (* Fix the grammar used by this file *)
  val ambient_grammars = Parse.current_grammars()
  val _ = Parse.temp_set_grammars arithmeticTheory.arithmetic_grammars
  val oldmesonchat = !mesonLib.chatting
  val _ = mesonLib.chatting := 0;
in

infix myTRANS THEN ORELSE ORELSEC THENL THENC |->;
fun th1 myTRANS th2 = TRANS th1 th2;
fun failwith fname s =
    raise HOL_ERR {message=s, origin_function= fname,
                   origin_structure="mn_tactics"};
fun foldr f zero []      = zero
  | foldr f zero (x::xs) = f x (foldr f zero xs);
fun foldl f zero []      = zero
  | foldl f zero (x::xs) = foldl f (f zero x) xs;
fun chop f [] = ([],[])
  | chop f (list as (head::tail)) =
         if (f head) then
            ([],list)
         else
            let val (sub1,rest) = chop f (tl list) in
              (head::sub1, rest)
            end;
fun chopn 0 l       = ([],l)
  | chopn n (x::xs) = if n < 0 then failwith "chopn" "chop_list" else
                      let val (fhalf, shalf) = chopn (n-1) xs in
                        (x::fhalf, shalf)
                      end
  | chopn _ _       = failwith "chopn" "chop_list";
fun insert n e l =
    if n < 1 then failwith "insert" "Bad position to insert at" else
    if n = 1 then e::l else (hd l)::(insert (n-1) e (tl l));
fun delete n l =
    if n < 1 then failwith "delete" "Bad position to delete at" else
    if n = 1 then tl l
    else (hd l)::(delete (n-1) (tl l));
fun update n e = (insert n e) o (delete n);
fun findi e [] = failwith "findi" "Couldn't find element" |
    findi e (x::xs) = if e = x then 1 else 1 + findi e xs
val reverse = rev;
fun butlast []         = failwith "butlast" "empty list"
  | butlast [x]        = []
  | butlast (x::y::xs) = x::(butlast (y::xs));
fun remove x [] = failwith "remove" "remove: no such element"
  | remove x (y::xs) = if (x = y) then xs else y::(remove x xs)
val lookup  = assoc;
fun rev_assoc k [] = failwith "rev_assoc" "no such element"
  | rev_assoc k ((v, k')::xs) = if k = k' then v else rev_assoc k xs
fun entry key value [] = [(key,value)]
  | entry key value ((k,v)::xs) =
       if (k = key) then
          (key,value)::xs
       else
          (k,v)::(entry key value xs);
fun has_value item lst =
    can (lookup item) lst;
val is_letter = Char.isAlpha;
val is_num = Char.isDigit;
val is_alphanum = Char.isAlphaNum;
fun is_quant   t    = (is_exists t) orelse (is_forall t);;
fun get_quant_dest term =
                      if (is_exists term) then
                          dest_exists
                      else
                          dest_forall;
fun dest_quant t    = if (is_exists t) then
                          dest_exists t
                      else
                          dest_forall t;
fun is_connective t = (is_conj t) orelse (is_disj t) orelse
                      (is_imp t andalso not (is_neg t));
fun get_conn_dest t = if (is_conj t) then dest_conj else
                      if (is_disj t) then dest_disj else
                      if (is_imp t)  then dest_imp
                      else failwith "get_conn_dest" "Bad connective";
fun get_const_type str = type_of (hd (Term.decls str));
fun myis_imp t = is_imp t andalso not (is_neg t)
(* Copyright 1993, Laboratory for Applied Logic, Brigham Young
   University. All rights reserved. Reproduction of all or part of this
   work is permitted for educational or research use provided that this
   copyright notice is included in any copy.  *)
fun dest_all_type ty =
  if is_vartype ty then
    (dest_vartype ty,[]: hol_type list)
  else
    dest_type ty;
fun type2string ty =
  let fun string_aux ty =
        let val (s,terml) = dest_all_type ty
        in
            if null terml then
               s
            else
               let val sl         = map string_aux terml
                   fun comapp x y = x^","^y
               in
                   "("^(foldl comapp (hd sl) (tl sl))^")"^s
               end
        end
  in
      (string_aux ty)
  end;
fun app_letter ty =
  let val (operator,l) = dest_all_type ty
  in
      hd (explode operator)
  end;
val CONJ_ss = simpLib.SSFRAG {
  name=SOME"CONJ",
  ac = [], convs = [], dprocs = [],
  filter = NONE, rewrs = [], congs = [GEN_ALL (
   tautLib.TAUT_PROVE (Term`(P ==> (Q = Q')) ==> (Q' ==> (P = P')) ==>
                       ((P /\ Q) = (P' /\ Q'))`))]}
infix ++;
fun ss ++ sd = simpLib.++(ss,sd);
fun dMESON_TAC d ths = mesonLib.GEN_MESON_TAC 0 d 1 ths ORELSE ALL_TAC;
val MESON_TAC = mesonLib.MESON_TAC;
val ASM_MESON_TAC = mesonLib.ASM_MESON_TAC;
fun find_match {pattern, term} = let
    fun find_match_aux term =
        match_term pattern term
        handle HOL_ERR _ =>
            find_match_aux (snd(dest_abs term))
            handle HOL_ERR _ =>
                find_match_aux (rator term)
                handle HOL_ERR _ =>
                    find_match_aux (rand term)
                    handle HOL_ERR _ =>
                       failwith "find_match" "no match"
    in
        find_match_aux term
end;
fun myvariant termlist trm =
let
  open Psyntax
  fun varclash v1 v2 =
    let val (str1,_) = dest_var v1
        and (str2,_) = dest_var v2
    in
      str1 = str2
    end
  fun try_numbered_vars n base typ tl =
    let val attempt = mk_var(base^Int.toString n, typ)
    in
      if not (exists (varclash attempt) tl) then
        attempt
      else
        try_numbered_vars (n+1) base typ tl
    end
  val (str,typ) = dest_var trm
  val base =
    let val (bstr,_) = chop (not o is_alphanum) (explode str) in
      implode bstr
    end
  val prime_var = mk_var(base^"'", typ)
in
  if not (exists (varclash trm) termlist) then
    trm
  else if not (exists (varclash prime_var) termlist) then
    prime_var
       else try_numbered_vars 0 base typ termlist
end;
fun tofl P i        = if (P i) then i
                      else raise HOL_ERR {message = "tofl failed",
                                          origin_function = "tofl",
                                          origin_structure = "mn_tactics"};
infix >-
fun f >- g          = g o f;
fun dub x           = (x,x);
fun my_distinct thm =
  let val base = valOf (hd (Prim_rec.prove_constructors_distinct thm)) in
    CONJ base (GSYM base)
  end;
val ETA_RULE = CONV_RULE (DEPTH_CONV ETA_CONV);
val ARITH_PROVE = numLib.ARITH_CONV >- EQT_ELIM;
val SIMP_TAC = simpLib.SIMP_TAC
val SIMP_CONV = simpLib.SIMP_CONV
val ASM_SIMP_TAC = simpLib.ASM_SIMP_TAC
val FULL_SIMP_TAC = simpLib.FULL_SIMP_TAC
val SIMP_RULE = simpLib.SIMP_RULE
val ARITH_CONV = numLib.ARITH_CONV
(* val hol_ss = HOLSimps.hol_ss *)

local val base_ss =
        simpLib.++(simpLib.++(boolSimps.bool_ss, pairSimps.PAIR_ss),
                   combinSimps.COMBIN_ss)
in
val mn_ss = simpLib.++(base_ss, numSimps.ARITH_ss)
end;


val dest_quant_CONV = RAND_CONV o ABS_CONV;
fun strip_imp_CONV c term =
  let fun strip_imp_conval term =
        if (is_imp term) then
          RAND_CONV o strip_imp_conval (snd (dest_imp term))
        else I
  in
      (strip_imp_conval term) c term
  end
fun fn_CONV c term = let
   fun fn_conval term =
      if (is_comb term) then
         RATOR_CONV o (fn_conval (fst (dest_comb term)))
      else I in
   (fn_conval term) c term end;
fun arg_CONV n c term = let
   fun arg_conval curpos n =
      if (curpos = n) then RAND_CONV
                      else RATOR_CONV o arg_conval (curpos - 1) n
   val (fnc,args) = strip_comb term
   val num_args = length args in
   if (num_args < n orelse n < 1) then
      failwith "arg_CONV" "Bad argnum spec."
   else
      (arg_conval num_args n) c term end;
fun binop_CONV n test fstr c term = let
   val conv = if (n=1) then RATOR_CONV o RAND_CONV else RAND_CONV in
   if (test term) then conv c term else failwith "binop_CONV" fstr end;
val disj1_CONV = binop_CONV 1 is_disj "Term not a disjunction";
val disj2_CONV = binop_CONV 2 is_disj "Term not a disjunction";
val conj1_CONV = binop_CONV 1 is_conj "Term not a conjunction";
val conj2_CONV = binop_CONV 2 is_conj "Term not a conjunction";
val lhs_CONV   = binop_CONV 1 is_eq   "Term not an equality";
val rhs_CONV   = binop_CONV 2 is_eq   "Term not an equality";
val ant_CONV   = binop_CONV 1 is_imp  "Term not an implication";
val consq_CONV = binop_CONV 2 is_imp  "Term not an implication";
val fst_CONV   = binop_CONV 1 pairSyntax.is_pair "Term not a pair";
val snd_CONV   = binop_CONV 2 pairSyntax.is_pair "Term not a pair";
fun neg_CONV c term =
   if (is_neg term) then RAND_CONV c term
                    else failwith "neg_CONV" "Term not a negation";
fun conjl_CONV n c term = let
   val conjs = strip_conj term
   val newterm = list_mk_conj conjs
   val numconjs = length conjs
   val substthm = c (el n conjs)
   val subsvar = genvar (==`:bool`==)
   val template = list_mk_conj (insert n subsvar (delete n conjs))
   val res1 = CONJUNCTS_CONV (term,newterm)
   val res2 =
     SUBST_CONV [subsvar |-> substthm] template newterm in
   TRANS res1 res2
end;
fun LAST_EXISTS_CONV conv tm =
  let val (var,body) = dest_exists tm
  in
      if (is_exists body) then
        dest_quant_CONV (LAST_EXISTS_CONV conv) tm
      else
        conv tm
  end;
fun LAST_FORALL_CONV conv tm =
  let val (var,body) = dest_forall tm
  in
      if (is_forall body) then
        dest_quant_CONV (LAST_FORALL_CONV conv) tm
      else
        conv tm
  end;
fun is_pair_type t =
   (fst (dest_type (type_of t)) = "prod") handle _ => false;
fun pair_CONV t =
   if is_pair_type t then
      let val th = ISPEC t (GSYM pairTheory.PAIR) in
         (PURE_ONCE_REWRITE_CONV [th] THENC
          RAND_CONV pair_CONV THENC
          RAND_CONV (RATOR_CONV pair_CONV)) t
      end
   else
      REFL t;
val PAIR_EQ = pairTheory.PAIR_EQ
val pair_CASES = pairTheory.ABS_PAIR_THM
fun split_pair t =
  if (not (is_pair_type t)) then
    raise (failwith "split_pair" "Must have pair term given as argument")
  else
    let val sthm = ISPEC t pair_CASES
    in
        CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC) sthm
    end
fun CONJ_CONV th term = let
    fun th_convert th = let
        val t = concl th in
        if (is_eq t) then (dest_eq t, th) else
        if (is_neg t) then ((dest_neg t, (--`F`--)), EQF_INTRO th)
                      else ((t, (--`T`--)), EQT_INTRO th) end
    val ((lhs,rhs),substh) = th_convert th
    val thm_conjs = strip_conj lhs
    val trm_conjs = strip_conj term in
    if (List.all (C mem trm_conjs) thm_conjs) then let
       val newterm_conjs = filter (not o C mem thm_conjs) trm_conjs
       fun conjwithnew trm =
            if null newterm_conjs then
               trm
            else
               (--`^trm /\ ^(list_mk_conj newterm_conjs)`--)
       val reorder_term = conjwithnew lhs
       val newterm = conjwithnew rhs
       val reorder_thm =
            CONJUNCTS_CONV(term,reorder_term) in
       TRANS reorder_thm
             (prove((--`^reorder_term = ^newterm`--),
                    SUBST1_TAC substh THEN REFL_TAC)) end
    else failwith "CONJ_CONV" "No subset" end;
local
  fun inst' subst th acc =
    if (is_forall (concl th)) then
      let val (v, _) = dest_forall (concl th)
      in
          inst' subst (SPEC v th) (v::acc)
      end
    else
      let val vs = set_diff acc (map #redex subst)
      in
          GENL (rev vs) (INST subst th)
           handle
            HOL_ERR {message, origin_function, origin_structure} =>
           raise HOL_ERR {message =  origin_function^": "^message,
                          origin_structure = "mnUtils",
                          origin_function = "gINST"}
      end
in
  fun gINST subst th = inst' subst th []
end;
val ASSUME_THEN:term -> thm_tactic -> tactic =
  fn t => fn f => f (ASSUME t)
val DISJ_IMP_THM = prove(
  Term`!P Q R. P \/ Q ==> R = (P ==> R) /\ (Q ==> R)`,
  tautLib.TAUT_TAC);
val IMP_CONJ_THM = prove(
  Term`!P Q R. P ==> Q /\ R = (P ==> Q) /\ (P ==> R)`,
  tautLib.TAUT_TAC);
fun np t = prove(t,MESON_TAC [])
fun ct t =
  prove(t, REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [])
val IMP2_THM = AND_IMP_INTRO
val IMP_CONJ_THM =
  np (--`!P Q R. (P ==> Q /\ R) = (P ==> Q) /\ (P ==> R)`--)
val fCOND_OUT_THM = COND_RAND
val aCOND_OUT_THM = COND_RATOR
val LEFT_AND_EXISTS_THM =
  np (--`!P Q. (?x:'a. P x) /\ Q = ?x. P x /\ Q`--)
val RIGHT_AND_EXISTS_THM =
  np (--`!P Q. Q /\ (?x:'a. P x) = ?x. Q /\ P x`--)
val EXISTS_OR_THM =
  np (--`!P Q. (?x:'a. P x \/ Q x) = (?x. P x) \/ (?x. Q x)`--)
val FORALL_AND_THM =
  np (--`!P Q. (!x:'a. P x /\ Q x) = (!x. P x) /\ (!x. Q x)`--)
val LEFT_IMP_EXISTS_THM =
  np (--`!P Q. (?x:'a. P x) ==> Q = !x. P x ==> Q`--)
val NOT_FORALL_THM = np (--`!P. ~(!x:'a. P x) = (?x. ~ (P x))`--)
val RIGHT_IMP_FORALL_THM =
  np (Term`!P Q. (P ==> !x:'a. Q x) = (!x. P ==> Q x)`)
fun myMATCH_MP impthm thm =
  let
    val con_imp = concl >- strip_forall >- snd >- dest_imp
    fun disj_mps th acc =
      if (is_conj (concl th)) then
        disj_mps (CONJUNCT2 th) (disj_mps (CONJUNCT1 th) acc)
      else if ((con_imp >- fst >- is_disj) th) then
        disj_mps (CONV_RULE (
          STRIP_QUANT_CONV (REWR_CONV DISJ_IMP_THM) THENC
          REPEATC (LAST_FORALL_CONV FORALL_AND_CONV)) th) acc
      else
        th::acc
    val ths = disj_mps impthm [impthm]
      handle _ => failwith "myMATCH_MP" "Theorem not an implication"
  in
    hd (mapfilter (C MATCH_MP thm) ths)
    handle List.Empty =>
      failwith "myMATCH_MP" "No matches"
  end
fun lastn n list =
  let val len = length list
      fun lastn' n len list =
        if (n > len) then      raise Fail "List not long enough"
        else if (n = len) then list
        else                   lastn' n (len - 1) (tl list)
  in
      lastn' n len list
  end

fun myEXISTS t th =
  let val (var,body) = dest_exists t
      val (mtch,_) = match_term body (concl th)
      val inst = valOf(subst_assoc (equal var) mtch)
  in
      EXISTS (t,inst) th
  end
fun myEXISTSplus t th =
  let val _ = can (match_term (snd (strip_exists t)))
                  (snd (strip_exists (concl th))) orelse
              raise Fail ""
  in
      prove(t, dMESON_TAC 4 [th])
  end handle _ => raise Fail "myEXISTSplus: doesn't follow"

fun SYM_TAC ((asl:term list), goal) =
  let val (l,r) = dest_eq goal in
    ([(asl,mk_eq(r,l))], fn [th] => SYM th)
  end;

val RWT          = REWRITE_TAC [];;
val ARWT         = ASM_REWRITE_TAC [];;
val carwt        = REPEAT CONJ_TAC THEN
                   (FIRST_ASSUM ACCEPT_TAC ORELSE ALL_TAC);;
val FUN_EQ_TAC   = CONV_TAC FUN_EQ_CONV THEN STRIP_TAC;;
fun REPEATN n t  = if n < 1 then ALL_TAC
                            else t THEN (REPEATN (n-1) t);
fun REPEATNC n c = if n < 1 then REFL
                            else c THENC (REPEATNC (n-1) c);
val multi_exists = MAP_EVERY EXISTS_TAC;
infix THEN_TAC
fun (f THEN_TAC g) x = f x THEN g x
local
  val not_not = tautLib.TAUT_PROVE (--`!p. p = ~~p`--)
in
  val myCONTR_TAC = CONV_TAC (REWR_CONV not_not) THEN STRIP_TAC
end
fun pwith t tl =
  SUBGOAL_THEN t ASSUME_TAC THENL [ASM_MESON_TAC tl, ALL_TAC];
fun rename_vars varlist term =
  let
    val (strip, list_mk) =
       if (is_exists term) then
          (strip_exists, list_mk_exists) else
       if (is_forall term) then
          (strip_forall, list_mk_forall)
       else
          failwith "rename_vars" "Term not quantified with something I can handle"
    val (ex_vars, body) = strip term
    val (tochange, unchanged) = chopn (length varlist) ex_vars
    val new_vars = varlist @ unchanged
    val new_body = subst (map2 (curry op |->)  tochange varlist) body in
    ALPHA (list_mk (ex_vars, body)) (list_mk (new_vars, new_body))
  end;
val ABBREV_TAC:term -> tactic = fn tm =>
  let val (v, t) = dest_eq tm
  in
      CHOOSE_THEN (fn th => SUBST_ALL_TAC th THEN ASSUME_TAC th)
                  (EXISTS (mk_exists(v, mk_eq(t,v)), t) (REFL t))
  end;
local
  val imp_conjs =
    REWRITE_RULE [IMP_CONJ_THM] >-
    CONV_RULE (REDEPTH_CONV FORALL_AND_CONV) >- CONJUNCTS
in
  fun myMMP th =
    MATCH_MP_TAC th ORELSE
    FIRST (map MATCH_MP_TAC (imp_conjs th))
end;
fun AP_TAC (asl, g) =
  let val _ = if (not (is_eq g)) then
                failwith "AP_TAC" "Not an equality goal" else ()
      val (lhs, rhs) = dest_eq g
      val (lf, la) = dest_comb lhs handle _ =>
                       failwith "AP_TAC" "lhs must be an application"
      val (rf, ra) = dest_comb rhs handle _ =>
                       failwith "AP_TAC" "rhs must be an application"
  in
      if (lf = rf) then AP_TERM_TAC (asl, g) else
      if (la = ra) then AP_THM_TAC (asl, g) else
      failwith "AP_TAC" "One of function or argument must be equal"
  end
val APn_TAC = REPEAT AP_TAC;
fun only_P_disjs P (asl, g) =
  let val gdisjs = strip_disj g
      val (P_disjs,rest) = partition P gdisjs
      fun my_mk_disj [] = Term`F`
        | my_mk_disj x = list_mk_disj x
      val new_g = mk_disj(my_mk_disj P_disjs, my_mk_disj rest)
      val rewrites =
        tautLib.TAUT_PROVE (Term`!p. (p \/ F = p) /\ (F \/ p = p)`)
      val new_g_eq_thm = prove(
        mk_eq(g, new_g),
        PURE_REWRITE_TAC [rewrites] THEN
        CONV_TAC (AC_CONV (DISJ_ASSOC, DISJ_SYM)))
  in
      CONV_TAC (REWR_CONV new_g_eq_thm) THEN DISJ1_TAC
  end (asl, g)
val only_free_disjs = free_in >- only_P_disjs
val UTOP      = POP_ASSUM MP_TAC;
val DROPIT    = POP_ASSUM (K ALL_TAC);
val UD_AND    = UTOP THEN PURE_REWRITE_TAC [IMP2_THM];

val ACCASS    = POP_ASSUM MATCH_ACCEPT_TAC;
val SWAP      = POP_ASSUM (fn th1 =>
                   (POP_ASSUM (fn th2 => ASSUME_TAC th1 THEN
                                         ASSUME_TAC th2)));
val dswap     = POP_ASSUM (fn th => SWAP THEN ASSUME_TAC th);
val bounce    = UD_AND THEN STRIP_TAC;
val rotate    = POP_ASSUM_LIST
                   (fn (hd::tl) => let
                       val newlist = reverse (tl @ [hd]) in
                       MAP_EVERY ASSUME_TAC newlist
                    end | [] => raise Fail "");
fun rotn n    = REPEATN n rotate;
fun EVERY_OK_ASSUM ttac = EVERY_ASSUM (TRY o ttac)
val myDISCH_TAC = DISCH_THEN STRIP_ASSUME_TAC
(* the standard DISCH_TAC doesn't do any useful stripping *)
val ELIM1_TAC =
  let fun apply thm =
        let fun chkeq thm =
              let val con = concl thm
              in
                  is_var (lhs con) andalso not (free_in (lhs con) (rhs con))
              end
            fun check thm =
              let val con = concl thm in
                if (is_eq con) then
                  if (chkeq thm) then ([thm],[]) else
                  if (chkeq (SYM thm)) then ([SYM thm], []) else
                  if (pairSyntax.is_pair (lhs con) andalso
                      pairSyntax.is_pair (rhs con)) then
                    let val conjs = CONJUNCTS (REWRITE_RULE [PAIR_EQ] thm)
                        val (ys,ns) = unzip (map check conjs)
                    in
                        (flatten ys, flatten ns)
                    end else ([], [thm])
                else
                   if (is_var con) then ([EQT_INTRO thm], []) else
                   if (is_neg con) andalso (is_var (dest_neg con)) then
                      ([EQF_INTRO thm], [])
                   else ([], [thm])
              end
            val (usables, to_assume) = check thm
            val con = concl thm
        in
            if (null usables) andalso (length to_assume = 1) then NO_TAC
            else
               UNDISCH_TAC con THEN DISCH_THEN (K ALL_TAC) THEN
               MAP_EVERY ASSUME_TAC to_assume THEN
               MAP_EVERY SUBST_ALL_TAC usables
         end
      fun elim_refl thm =
        let val con = concl thm
        in
            if (is_eq con andalso (rhs con) = (lhs con)) orelse
               (con = concl TRUTH) then
               UNDISCH_TAC con THEN DISCH_THEN (K ALL_TAC)
            else
               NO_TAC
        end
  in
      TRY (FIRST_ASSUM apply) THEN TRY (FIRST_ASSUM elim_refl)
  end
val ELIM_TAC = REPEAT (CHANGED_TAC ELIM1_TAC);
fun SIMP_PROVE_TAC ss t =
  ASSUM_LIST (fn thl =>
              ASSUME_TAC (EQT_ELIM (SIMP_CONV ss thl t)))
fun CLEAR_ASM P =
    FIRST_ASSUM (UNDISCH_TAC o tofl P o concl) THEN
    DISCH_THEN (K ALL_TAC);
fun CLEAR_ASMS P =
    REPEAT (CLEAR_ASM P);
fun sX_CHOOSE_THEN s ttac th =
  let val (v,_) = dest_exists (concl th)
  in
      X_CHOOSE_THEN (mk_var(s, type_of v)) ttac th
  end
local
  val con_is_imp = concl >- strip_forall >- snd >- is_imp
  val con_hyp = concl >- strip_forall >- snd >- dest_imp >- fst
  fun res_search' nres cex_seen des thml sl c thm =
    let val f_a = if des then FIRST_X_ASSUM else FIRST_ASSUM
        val und_then = if des then UNDISCH_THEN
                              else ASSUME_THEN
        val newthml = tl thml handle _ => []
    in
      if (nres = 0) then
        c thm
      else if null thml orelse (is_var (hd thml)) then
        if con_is_imp thm then let
            val stdfinish0 =
                f_a (MATCH_MP thm >-
                     res_search' (nres - 1) cex_seen des newthml sl c)
            val stdfinish = if cex_seen then stdfinish0 ORELSE c thm
                            else stdfinish0
          in
            if is_exists (con_hyp thm) then
              res_search' nres cex_seen des thml sl c
                          (CONV_RULE (STRIP_QUANT_CONV LEFT_IMP_EXISTS_CONV)
                                     thm)
            else if is_conj (con_hyp thm) then
              res_search' nres cex_seen des thml sl c
                          (CONV_RULE (STRIP_QUANT_CONV
                                        (REWR_CONV (GSYM IMP2_THM))) thm)
            else if is_disj (con_hyp thm) then let
                val (fa_vars, _) = strip_forall (concl thm)
                val (th1, th2) =
                    (GENL fa_vars ## GENL fa_vars)
                      (CONJ_PAIR (SPEC_ALL (CONV_RULE
                                              (STRIP_QUANT_CONV
                                                 (REWR_CONV DISJ_IMP_THM))
                                              thm)))
              in
                stdfinish ORELSE
                res_search' nres cex_seen des thml sl c th1 ORELSE
                res_search' nres cex_seen des thml sl c th2
              end
            else if is_eq (con_hyp thm) then let
                val (l,r) = dest_eq (con_hyp thm)
              in
                if compare(l,r) = EQUAL then
                  res_search' (nres - 1) cex_seen des thml sl c
                              (MATCH_MP thm (ALPHA l r))
                else
                  stdfinish
              end
            else
              stdfinish
          end
        else if is_exists (concl thm) then
          if null sl then
            CHOOSE_THEN (res_search' (nres - 1) true des thml sl c) thm
          else
            sX_CHOOSE_THEN (hd sl)
              (res_search' (nres - 1) true des thml (tl sl) c) thm
        else if is_conj (concl thm) then
          CONJUNCTS_THEN (res_search' (nres - 1) true des thml sl c) thm
        else
          c thm
      else
        und_then (hd thml)
          (MATCH_MP thm >-
           res_search' (nres - 1) cex_seen des (tl thml) sl c)
    end
in
  fun res_search destp tl sl =
    res_search' ~1 false destp tl sl STRIP_ASSUME_TAC
  val res_search_then = res_search' ~1 false
  fun nres_search_then n = res_search' n false
end;

val EX_QVAR_SWAP_THM =
  prove ((--`!(f:'a->'b->bool).(? x y. f x y) = (? y x . f x y)`--),
         STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
          (multi_exists [(--`x:'a`--),(--`y:'b`--)] ORELSE
           multi_exists [(--`y:'b`--),(--`x:'a`--)]) THEN
         ACCASS);
val FA_QVAR_SWAP_THM =
  prove ((--`!(f:'a->'b->bool).(!x y. f x y) = (!y x. f x y)`--),
         STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ARWT);

fun swap_vars term = let
  val (dest, list_mk, qvar_thm) =
      if (is_exists term) then
         (dest_exists, LIST_MK_EXISTS, EX_QVAR_SWAP_THM) else
      if (is_forall term) then
         (dest_forall, C (foldr FORALL_EQ), FA_QVAR_SWAP_THM)
      else
         failwith "swap_vars"
         "Formula must be universally or existentially quantified"
  val (fst_var, fst_body) = dest term
  val (snd_var, snd_body) = dest fst_body
  val fnc = list_mk_abs ([fst_var,snd_var], snd_body)
  val fn_rewrite =
     SYM (LIST_BETA_CONV (list_mk_comb (fnc, [fst_var,snd_var])))
  val ex_rewrite = list_mk [fst_var,snd_var] fn_rewrite
  val inst_thm = ISPEC fnc qvar_thm
  val final_thm =
      TRANS inst_thm
            (rename_vars [snd_var,fst_var] (rhs (concl inst_thm))) in
  BETA_RULE (SUBS [final_thm] ex_rewrite) end;


local
  datatype binop   = /\ | \/ | ==>
  datatype quanty  = ? | !
  datatype direction = Left | Right
  datatype pq_info = Quantified |
                     BinOp of (direction*binop) |
                     Negated |
                     NoPInfo
  datatype findresult = Found of (term*((conv->conv)*(conv->conv))) |
                        NotFound of int
  fun t2mlsym t =
     case fst(dest_const t) of
        "/\\" => /\ |
        "\\/" => \/ |
        "==>" => ==> |
        _     => failwith "t2mlsym" "Bad boolean operator"
  fun split_found (Found(t,f)) = (t,f)
    | split_found _            = failwith "split_found" "Bad findresult"
  fun find_qterm term var (f,pf) pinfo (pos::postl) =
      if (is_var term orelse is_const term) then
         (NotFound 0, NoPInfo) else
      if (is_quant term) then let
         val dest        = get_quant_dest term
         val (qvar, bdy) = dest term                and
             newf        = f o RAND_CONV o ABS_CONV in
         if (var = qvar) then
            if (pos = 1) then
               if (null postl) then
                  (Found (term,(f,pf)), pinfo)
               else
                  find_qterm bdy var (newf, f) Quantified postl
            else
               (NotFound 1, NoPInfo)
         else
            find_qterm bdy var (newf, f) Quantified (pos::postl)
      end else
      if (is_connective term) then let
         val (dest, opr) = (get_conn_dest term, fst (strip_comb term))
         val (arg1, arg2) = dest term                  and
             arg1f        = f o RATOR_CONV o RAND_CONV and
             arg1p        = BinOp(Left, t2mlsym opr)
         val res1 =
               find_qterm arg1 var (arg1f, f) arg1p (pos::postl) in
         case res1 of
            (NotFound n, _) => let
               val arg2f = f o RAND_CONV              and
                   arg2p = BinOp(Right, t2mlsym opr)
               val res2 =
                  find_qterm arg2 var (arg2f, f) arg2p (pos - n::postl) in
               case res2 of
                 (NotFound m, p) => (NotFound (n+m), p) |
                 x               => x end |
            x               =>  x
      end else
      if (is_neg term) then let
         val arg = dest_neg term
         val newf = f o RATOR_CONV in
         find_qterm arg var (newf, f) Negated (pos::postl)
      end else
      if (is_comb term) then let
         val (fnc, arg) = dest_comb term
         val fnf = f o RATOR_CONV
         val res1 = find_qterm fnc var (fnf,f) NoPInfo (pos::postl) in
         case res1 of
           (NotFound n, _) => let
              val argf = f o RAND_CONV
              val res2 =
                 find_qterm arg var (argf,f) NoPInfo (pos - n::postl) in
              case res2 of
                 (NotFound m, p) => (NotFound (n+m), p) |
                 x                => x end |
           x               => x
      end else
      if (is_abs term) then let
         val (_,body) = dest_abs term in
         find_qterm body var (f o ABS_CONV, f) NoPInfo (pos::postl)
      end
      else
         failwith "find_qterm" "Can't handle funny term type"
     | find_qterm _ _ _ _ _ = failwith "find_qterm" "Need non-empty position list";
in
  local
    val forall_tac =
      EQ_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN ARWT
    fun exists_tac ty =
      EQ_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
      EXISTS_TAC (mk_arb ty) THEN
      ARWT
  in
    fun rmqvar t =
      let val (qvar,body,tac) =
            if (is_exists t) then
              let val (Bvar,Body) = dest_exists t in
                 (Bvar, Body, exists_tac (type_of Bvar))
              end
            else if (is_forall t) then
              let val (Bvar, Body) = dest_forall t in
                (Bvar, Body, forall_tac) end
            else
              failwith "rmqvar" "Needs to be a quantified term"
      in
          if (mem qvar (free_vars body)) then
            failwith "rmqvar" "Variable can't be free in body"
          else
            prove((--`^t = ^body`--), tac)
      end
  end;
  local
    fun get_in_conv q bdy = let
        val qs = fst (dest_const q) in
        if (is_conj bdy) then
           if (qs = "!") then FORALL_AND_CONV
                         else EXISTS_AND_CONV else
        if (is_disj bdy) then
           if (qs = "!") then FORALL_OR_CONV
                         else EXISTS_OR_CONV else
        if (is_imp bdy)  then
           if (qs = "!") then FORALL_IMP_CONV
                         else EXISTS_IMP_CONV else
        if (is_neg bdy)  then
           if (qs = "!") then FORALL_NOT_CONV
                         else EXISTS_NOT_CONV else
        if (is_quant bdy) then swap_vars
        else rmqvar
    end
  in
    fun std_move_in var posl term = let
      val (f,pi) =
        find_qterm term var (I,(fn _ => raise Fail "")) NoPInfo posl in
      case f of
         NotFound _     => failwith "std_move_in" "Couldn't find variable" |
         Found(t,(f,_)) => let val (quant,abs) = dest_comb t
                               val (_,body) = dest_abs abs
                               val c = get_in_conv quant body in
                               f c term
                           end
    end;
    fun move_in var  = std_move_in var [1]
    val rmove_in     = REPEATC o move_in
    val move_in_TAC  = CONV_TAC o move_in
    val rmove_in_TAC = CONV_TAC o rmove_in
  end;
  local
    fun get_out_conv pi q = let
      val AFC = AND_FORALL_CONV and
          AEC = AND_EXISTS_CONV and
          OFC = OR_FORALL_CONV  and
          OEC = OR_EXISTS_CONV in
      case (pi,q) of
       (Quantified,_)       => swap_vars |
       (BinOp(Left,/\),!)   => AFC ORELSEC LEFT_AND_FORALL_CONV |
       (BinOp(Left,/\),?)   => AEC ORELSEC LEFT_AND_EXISTS_CONV |
       (BinOp(Right,/\),!)  => AFC ORELSEC RIGHT_AND_FORALL_CONV |
       (BinOp(Right,/\),?)  => AEC ORELSEC RIGHT_AND_EXISTS_CONV |

       (BinOp(Left,==>),!)  => LEFT_IMP_FORALL_CONV |
       (BinOp(Left,==>),?)  => LEFT_IMP_EXISTS_CONV |
       (BinOp(Right,==>),!) => RIGHT_IMP_FORALL_CONV |
       (BinOp(Right,==>),?) => RIGHT_IMP_EXISTS_CONV |

       (BinOp(Left,\/),!)   => OFC ORELSEC LEFT_OR_FORALL_CONV |
       (BinOp(Left,\/),?)   => OEC ORELSEC LEFT_OR_EXISTS_CONV |
       (BinOp(Right,\/),!)  => OFC ORELSEC RIGHT_OR_FORALL_CONV |
       (BinOp(Right,\/),?)  => OEC ORELSEC RIGHT_OR_EXISTS_CONV |

       (Negated, !)         => NOT_FORALL_CONV |
       (Negated, ?)         => NOT_EXISTS_CONV |
       (NoPInfo, _)         => raise Fail "This can't happen"
    end
  in
    fun std_move_out var posl term = let
      val (f,pi) =
         find_qterm term var (I,(fn _ => raise Fail "")) NoPInfo posl in
      case f of
        NotFound _   =>  failwith "std_move_out" "Couldn't find variable" |
        Found(t,(_,p)) =>  let val quant =
                           (if is_exists t then ? else !) in
                         case pi of
                           NoPInfo  =>
                             failwith "std_move_out" "No conv to move var" |
                           _        => let
                             val c = get_out_conv pi quant
                           in
                             p c term
                           end
                         end
    end;
    fun move_out var = std_move_out var [1];
    fun move_out_TAC var = CONV_TAC (move_out var)
    fun rmove_out var = REPEATC (move_out var)
    fun rmove_out_TAC var = CONV_TAC (rmove_out var)
  end;
end;
val EX_OUT_CONV = REDEPTH_CONV (
  AND_EXISTS_CONV ORELSEC LEFT_AND_EXISTS_CONV ORELSEC
                          RIGHT_AND_EXISTS_CONV ORELSEC
  OR_EXISTS_CONV  ORELSEC LEFT_OR_EXISTS_CONV ORELSEC
                          RIGHT_OR_EXISTS_CONV ORELSEC
  LEFT_IMP_EXISTS_CONV ORELSEC RIGHT_IMP_EXISTS_CONV ORELSEC
  NOT_EXISTS_CONV)
val FA_OUT_CONV = REDEPTH_CONV (
  AND_FORALL_CONV ORELSEC LEFT_AND_FORALL_CONV ORELSEC
                          RIGHT_AND_FORALL_CONV ORELSEC
  OR_FORALL_CONV  ORELSEC LEFT_OR_FORALL_CONV ORELSEC
                          RIGHT_OR_FORALL_CONV ORELSEC
  LEFT_IMP_FORALL_CONV ORELSEC RIGHT_IMP_FORALL_CONV ORELSEC
  NOT_FORALL_CONV)
val EXIN_CONJ_CONV = EXISTS_AND_REORDER_CONV
val EXDISJ_THMS = [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM,
                   LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
                   EXISTS_OR_THM, DE_MORGAN_THM, GSYM DISJ_ASSOC]
val EXDISJ_NORM = SIMP_CONV mn_ss EXDISJ_THMS
val exdisj_set = simpLib.rewrites EXDISJ_THMS
val IMPNORM_THMS = [LEFT_IMP_EXISTS_THM, DISJ_IMP_THM, GSYM IMP2_THM,
                    IMP_CONJ_THM]
val impnorm_set = simpLib.rewrites IMPNORM_THMS
local
  fun imp_convert term =
      if is_imp term then dest_imp term else
      if is_neg term then (dest_neg term, (--`F`--))
      else ((--`T`--), term);
  fun neg_version term =
    if is_neg term then dest_neg term
                   else mk_neg term;
in
  fun move_conj_right conj term = let
      val (lhs,rhs) = imp_convert term
      val conjs = strip_conj lhs
      val (rest,newconjs) = partition (curry op= conj) conjs in
      if (null rest) then
         failwith "move_conj_right" "Must specify an existing conjunct"
      else let
        val newlhs = if null newconjs then (--`T`--)
                                      else list_mk_conj newconjs
        val neg_c  = neg_version conj
        val newrhs = if rhs = (--`F`--) then neg_c
                                        else (--`^neg_c \/ ^rhs`--)
        val newimp =
             if newlhs = (--`T`--) then newrhs
                                   else (--`^newlhs ==> ^newrhs`--) in
        prove((--`^term = ^newimp`--), tautLib.TAUT_TAC)
      end
  end;
  fun move_disj_left disj term = let
      val (lhs,rhs) = imp_convert term
      val disjs = strip_disj rhs
      val (rest,newdisjs) = partition (curry op= disj) disjs in
      if (null rest) then
         failwith "move_disj_left" "Must specify an existing disjunct"
      else let
        val neg_d = neg_version disj
        val newlhs = if lhs = (--`T`--) then neg_d
                                        else (--`^neg_d /\ ^lhs`--)
        val newrhs = if null newdisjs then (--`F`--)
                                      else list_mk_disj newdisjs
        val newimp =
            if newrhs = (--`F`--) then mk_neg newlhs
                                  else (--`^newlhs ==> ^newrhs`--) in
        prove((--`^term = ^newimp`--), tautLib.TAUT_TAC)
      end
  end;
  fun move_disjs_left term = let
      val (_,rhs) = imp_convert term
      val disjs = strip_disj rhs
      val convs = map move_disj_left disjs in
      EVERY_CONV convs term
  end;
  fun move_conjs_right term = let
      val (lhs, _) = imp_convert term
      val conjs = strip_conj lhs
      val convs = map move_conj_right conjs in
      EVERY_CONV convs term
  end;
end;

val _ = mesonLib.chatting := oldmesonchat
val _ = Parse.temp_set_grammars ambient_grammars
end;

end;
