(* ========================================================================= *)
(* A home for the less valuable or more recondite stuff from HOL88.          *)
(* ========================================================================= *)

let dest_neg_imp tm =
  try dest_imp tm with Failure _ ->
  try (dest_neg tm,mk_const("F",[]))
  with Failure _ -> failwith "dest_neg_imp";;

(* ------------------------------------------------------------------------- *)
(* The quantifier movement conversions.                                      *)
(* ------------------------------------------------------------------------- *)

let (CONV_OF_RCONV: conv -> conv) =
  let rec get_bv tm =
    if is_abs tm then bndvar tm
    else if is_comb tm then try get_bv (rand tm)
            with Failure _ -> get_bv (rator tm)
    else failwith "" in
  fun conv tm ->
  let v = get_bv tm in
  let th1 = conv tm in
  let th2 = ONCE_DEPTH_CONV (GEN_ALPHA_CONV v) (rhs(concl th1)) in
  TRANS th1 th2;;

let (CONV_OF_THM: thm -> conv) =
  CONV_OF_RCONV o REWR_CONV;;

let (X_FUN_EQ_CONV:term->conv) =
  fun v -> (REWR_CONV FUN_EQ_THM) THENC GEN_ALPHA_CONV v;;

let (FUN_EQ_CONV:conv) =
  fun tm ->
    let vars = frees tm in
    let op,[ty1;ty2] = dest_type(type_of (lhs tm)) in
    if op = "fun"
       then let varnm =
                if (is_vartype ty1) then "x" else
                   hd(explode(fst(dest_type ty1))) in
            let x = variant vars (mk_var(varnm,ty1)) in
            X_FUN_EQ_CONV x tm
       else failwith "FUN_EQ_CONV";;

let (OLD_SKOLEM_CONV:conv) =
  SINGLE_DEPTH_CONV (REWR_CONV SKOLEM_THM);;

let (X_SKOLEM_CONV:term->conv) =
  fun v -> OLD_SKOLEM_CONV THENC GEN_ALPHA_CONV v;;

let EXISTS_UNIQUE_CONV tm =
  let v = bndvar(rand tm) in
  let th1 = REWR_CONV EXISTS_UNIQUE_THM tm in
  let tm1 = rhs(concl th1) in
  let vars = frees tm1 in
  let v = variant vars v in
  let v' = variant (v::vars) v in
  let th2 =
   (LAND_CONV(GEN_ALPHA_CONV v) THENC
    RAND_CONV(BINDER_CONV(GEN_ALPHA_CONV v') THENC
              GEN_ALPHA_CONV v)) tm1 in
  TRANS th1 th2;;

let NOT_FORALL_CONV = CONV_OF_THM NOT_FORALL_THM;;

let NOT_EXISTS_CONV = CONV_OF_THM NOT_EXISTS_THM;;

let RIGHT_IMP_EXISTS_CONV = CONV_OF_THM RIGHT_IMP_EXISTS_THM;;

let FORALL_IMP_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_FORALL_IMP_THM ORELSEC
   REWR_CONV RIGHT_FORALL_IMP_THM ORELSEC
   REWR_CONV LEFT_FORALL_IMP_THM);;

let EXISTS_AND_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_EXISTS_AND_THM ORELSEC
   REWR_CONV LEFT_EXISTS_AND_THM ORELSEC
   REWR_CONV RIGHT_EXISTS_AND_THM);;

let LEFT_IMP_EXISTS_CONV = CONV_OF_THM LEFT_IMP_EXISTS_THM;;

let LEFT_AND_EXISTS_CONV tm =
  let v = bndvar(rand(rand(rator tm))) in
  (REWR_CONV LEFT_AND_EXISTS_THM THENC TRY_CONV (GEN_ALPHA_CONV v)) tm;;

let RIGHT_AND_EXISTS_CONV =
  CONV_OF_THM RIGHT_AND_EXISTS_THM;;

let AND_FORALL_CONV = CONV_OF_THM AND_FORALL_THM;;

(* ------------------------------------------------------------------------- *)
(* The slew of named tautologies.                                            *)
(* ------------------------------------------------------------------------- *)

let F_IMP = TAUT `!t. ~t ==> t ==> F`;;

let LEFT_AND_OVER_OR = TAUT
  `!t1 t2 t3. t1 /\ (t2 \/ t3) = t1 /\ t2 \/ t1 /\ t3`;;

let RIGHT_AND_OVER_OR = TAUT
  `!t1 t2 t3. (t2 \/ t3) /\ t1 = t2 /\ t1 \/ t3 /\ t1`;;

(* ------------------------------------------------------------------------- *)
(* Something trivial and useless.                                            *)
(* ------------------------------------------------------------------------- *)

let INST_TY_TERM(substl,insttyl) th = INST substl (INST_TYPE insttyl th);;

(* ------------------------------------------------------------------------- *)
(* Derived rules.                                                            *)
(* ------------------------------------------------------------------------- *)

let NOT_MP thi th =
  try MP thi th with Failure _ ->
  try let t = dest_neg (concl thi) in
      MP(MP (SPEC t F_IMP) thi) th
  with Failure _ -> failwith "NOT_MP";;

(* ------------------------------------------------------------------------- *)
(* Creating half abstractions.                                               *)
(* ------------------------------------------------------------------------- *)

let MK_ABS qth =
  try let ov = bndvar(rand(concl qth)) in
      let bv,rth = SPEC_VAR qth in
      let sth = ABS bv rth in
      let cnv = ALPHA_CONV ov in
      CONV_RULE(SUB_CONV cnv) sth
  with Failure _ -> failwith "MK_ABS";;

let HALF_MK_ABS th =
  try let th1 = MK_ABS th in
      CONV_RULE(LAND_CONV ETA_CONV) th1
  with Failure _ -> failwith "HALF_MK_ABS";;

(* ------------------------------------------------------------------------- *)
(* Old substitution primitive, now a (not very efficient) derived rule.      *)
(* ------------------------------------------------------------------------- *)

let SUBST thl pat th =
  let eqs,vs = unzip thl in
  let gvs = map (genvar o type_of) vs in
  let gpat = subst (zip gvs vs) pat in
  let ls,rs = unzip (map (dest_eq o concl) eqs) in
  let ths = map (ASSUME o mk_eq) (zip gvs rs) in
  let th1 = ASSUME gpat in
  let th2 = SUBS ths th1 in
  let th3 = itlist DISCH (map concl ths) (DISCH gpat th2) in
  let th4 = INST (zip ls gvs) th3 in
  MP (rev_itlist (C MP) eqs th4) th;;

(* ------------------------------------------------------------------------- *)
(* Resolution stuff.                                                         *)
(* ------------------------------------------------------------------------- *)

let RES_CANON =
    let not_elim th =
      if is_neg (concl th) then true,(NOT_ELIM th) else (false,th) in
    let rec canon fl th =
       let w = concl th in
       if (is_conj w) then
          let (th1,th2) = CONJ_PAIR th in (canon fl th1) @ (canon fl th2) else
       if ((is_imp w) & not(is_neg w)) then
          let ante,conc = dest_neg_imp w in
          if (is_conj ante) then
             let a,b = dest_conj ante in
             let cth = NOT_MP th (CONJ (ASSUME a) (ASSUME b)) in
             let th1 = DISCH b cth and th2 = DISCH a cth in
                 (canon true (DISCH a th1)) @ (canon true (DISCH b th2)) else
          if (is_disj ante) then
             let a,b = dest_disj ante in
             let ath = DISJ1 (ASSUME a) b and bth = DISJ2 a (ASSUME b) in
             let th1 = DISCH a (NOT_MP th ath) and
                 th2 = DISCH b (NOT_MP th bth) in
                 (canon true th1) @ (canon true th2) else
          if (is_exists ante) then
             let v,body = dest_exists ante in
             let newv = variant (thm_frees th) v in
             let newa = subst [newv,v] body in
             let th1 = NOT_MP th (EXISTS (ante, newv) (ASSUME newa)) in
                 canon true (DISCH newa th1) else
             map (GEN_ALL o (DISCH ante)) (canon true (UNDISCH th)) else
       if (is_eq w & (type_of (rand w) = `:bool`)) then
          let (th1,th2) = EQ_IMP_RULE th in
          (if fl then [GEN_ALL th] else []) @ (canon true th1) @ (canon true th2) else
       if (is_forall w) then
           let vs,body = strip_forall w in
           let fvs = thm_frees th in
           let vfn = fun l -> variant (l @ fvs) in
           let nvs = itlist (fun v nv -> let v' = vfn nv v in (v'::nv)) vs [] in
               canon fl (SPECL nvs th) else
       if fl then [GEN_ALL th] else [] in
    fun th -> try let args = map (not_elim o SPEC_ALL) (CONJUNCTS (SPEC_ALL th)) in
                  let imps = flat (map (map GEN_ALL o (uncurry canon)) args) in
                  assert (prefix not o prefix= []) imps
              with Failure _ ->
                failwith "RES_CANON: no implication is derivable from input thm.";;

let IMP_RES_THEN,RES_THEN =
  let MATCH_MP impth =
      let sth = SPEC_ALL impth in
      let matchfn = (fun (a,b,c) -> b,c) o
                    term_match [] (fst(dest_neg_imp(concl sth))) in
         fun th -> NOT_MP (INST_TY_TERM (matchfn (concl th)) sth) th in
  let check st l = (if l = [] then failwith st else l) in
  let IMP_RES_THEN ttac impth =
      let ths = try RES_CANON impth with Failure _ -> failwith "IMP_RES_THEN: no implication" in
      ASSUM_LIST
       (fun asl ->
        let l = itlist (fun th -> prefix@ (mapfilter (MATCH_MP th) asl)) ths [] in
        let res = check "IMP_RES_THEN: no resolvents " l in
        let tacs = check "IMP_RES_THEN: no tactics" (mapfilter ttac res) in
        EVERY tacs) in
  let RES_THEN ttac (asl,g) =
      let asm = map snd asl in
      let ths = itlist prefix@ (mapfilter RES_CANON asm) [] in
      let imps = check "RES_THEN: no implication" ths in
      let l = itlist (fun th -> prefix@ (mapfilter (MATCH_MP th) asm)) imps [] in
      let res = check "RES_THEN: no resolvents " l in
      let tacs = check "RES_THEN: no tactics" (mapfilter ttac res) in
          EVERY tacs (asl,g) in
  IMP_RES_THEN,RES_THEN;;

(* ------------------------------------------------------------------------- *)
(* The order of picking conditionals is different!                           *)
(* ------------------------------------------------------------------------- *)

let (LCOND_CASES_TAC :tactic) =
    let is_good_cond tm =
      try not(is_const(fst(dest_cond tm)))
      with Failure _ -> false in
    fun (asl,w) ->
      let cond = find_term (fun tm -> is_good_cond tm & free_in tm w) w in
      let p,(t,u) = dest_cond cond in
      let inst = INST_TYPE [type_of t, `:A`] COND_CLAUSES in
      let (ct,cf) = CONJ_PAIR (SPEC u (SPEC t inst)) in
      DISJ_CASES_THEN2
         (fun th -> SUBST1_TAC (EQT_INTRO th) THEN
               SUBST1_TAC ct THEN ASSUME_TAC th)
         (fun th -> SUBST1_TAC (EQF_INTRO th) THEN
               SUBST1_TAC cf THEN ASSUME_TAC th)
         (SPEC p EXCLUDED_MIDDLE)
         (asl,w) ;;

(* ------------------------------------------------------------------------- *)
(* MATCH_MP_TAC allows universals on the right of implication.               *)
(* Here's a crude hack to allow it.                                          *)
(* ------------------------------------------------------------------------- *)

let MATCH_MP_TAC th =
  MATCH_MP_TAC th ORELSE
  MATCH_MP_TAC(PURE_REWRITE_RULE[RIGHT_IMP_FORALL_THM] th);;

(* ------------------------------------------------------------------------- *)
(* Various theorems have different names.                                    *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;

let LESS_EQUAL_ANTISYM = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_ANTISYM)));;
let NOT_LESS_0 = GEN_ALL(EQF_ELIM(SPEC_ALL(CONJUNCT1 LT)));;
let LESS_LEMMA1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL(CONJUNCT2 LT))));;
let LESS_SUC_REFL = ARITH_RULE `!n. n < SUC n`;;
let LESS_EQ_SUC_REFL = ARITH_RULE `!n. n <= SUC n`;;
let LESS_EQUAL_ADD = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_EXISTS)));;
let LESS_EQ_IMP_LESS_SUC = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_SUC_LE)));;
let LESS_MONO_ADD = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_ADD_RCANCEL)));;
let LESS_SUC = ARITH_RULE `!m n. m < n ==> m < (SUC n)`;;
let num_CASES = prove(`!m. (m = 0) \/ (?n. m = SUC n)`,
                      INDUCT_TAC THEN ASM_MESON_TAC[]);;
let LESS_ADD_1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL
  (REWRITE_RULE[ADD1] LT_EXISTS))));;
let SUC_SUB1 = ARITH_RULE `!m. SUC m - 1 = m`;;
let LESS_ADD_SUC = ARITH_RULE `!m n. m < m + SUC n`;;
let OR_LESS = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_SUC_LT)));;
let NOT_SUC_LESS_EQ = ARITH_RULE `!n m. ~(SUC n <= m) = m <= n`;;
let LESS_LESS_CASES = ARITH_RULE `!m n. (m = n) \/ m < n \/ n < m`;;
let SUB_SUB = prove
 (`!b c. c <= b ==> (!a. a - (b - c) = (a + c) - b)`,
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN ARITH_TAC);;
let LESS_CASES_IMP = ARITH_RULE `!m n. ~(m < n) /\ ~(m = n) ==> n < m`;;
let SUB_LESS_EQ = ARITH_RULE `!n m. (n - m) <= n`;;
let SUB_EQ_EQ_0 = ARITH_RULE `!m n. (m - n = m) = (m = 0) \/ (n = 0)`;;
let SUB_LEFT_LESS_EQ =
  ARITH_RULE `!m n p. m <= (n - p) = (m + p) <= n \/ m <= 0`;;
let SUB_LEFT_LESS_EQ =
  ARITH_RULE `!m n p. m <= (n - p) = (m + p) <= n \/ m <= 0`;;
let SUB_LEFT_GREATER_EQ = ARITH_RULE `!m n p. m >= (n - p) = (m + p) >= n`;;
let LESS_0_CASES = ARITH_RULE `!m. (0 = m) \/ 0 < m`;;
let LESS_OR = ARITH_RULE `!m n. m < n ==> (SUC m) <= n`;;
let SUB_OLD = prove(`(!m. 0 - m = 0) /\
                 (!m n. (SUC m) - n = (m < n => 0 | SUC(m - n)))`,
                REPEAT STRIP_TAC THEN TRY LCOND_CASES_TAC THEN
                ASM_REWRITE_TAC[] THEN TRY (POP_ASSUM MP_TAC) THEN
                ARITH_TAC);;

(*============================================================================*)
(* Various useful tactics, conversions etc.                                   *)
(*============================================================================*)

(*----------------------------------------------------------------------------*)
(* SYM_CANON_CONV - Canonicalizes single application of symmetric operator    *)
(* Rewrites `so as to make fn true`, e.g. fn = $<< or fn = curry$= `1` o fst  *)
(*----------------------------------------------------------------------------*)

let SYM_CANON_CONV sym fn =
  REWR_CONV sym o
  assert (prefix not o fn o ((snd o dest_comb) F_F I) o dest_comb);;

(*----------------------------------------------------------------------------*)
(* IMP_SUBST_TAC - Implicational substitution for deepest matchable term      *)
(*----------------------------------------------------------------------------*)

let (IMP_SUBST_TAC:thm_tactic) =
  fun th (asl,w) ->
    let tms = find_terms (can (PART_MATCH (lhs o snd o dest_imp) th)) w in
    let tm1 = hd (sort (uncurry free_in) tms) in
    let th1 = PART_MATCH (lhs o snd o dest_imp) th tm1 in
    let (a,(l,r)) = (I F_F dest_eq) (dest_imp (concl th1)) in
    let gv = genvar (type_of l) in
    let pat = subst[gv,l] w in
    null_meta,
    [(asl,a); (asl,subst[(r,gv)] pat)],
    fun i [t1;t2] -> SUBST[(SYM(MP th1 t1),gv)] pat t2;;

(*---------------------------------------------------------------*)
(* EXT_CONV `!x. f x = g x` = |- (!x. f x = g x) = (f = g)       *)
(*---------------------------------------------------------------*)

let EXT_CONV =  SYM o uncurry X_FUN_EQ_CONV o
      (I F_F (mk_eq o (rator F_F rator) o dest_eq)) o dest_forall;;

(*----------------------------------------------------------------------------*)
(* EQUAL_TAC - Strip down to unequal core (usually too enthusiastic)          *)
(*----------------------------------------------------------------------------*)

let EQUAL_TAC = REPEAT(FIRST [AP_TERM_TAC; AP_THM_TAC; ABS_TAC]);;

(*----------------------------------------------------------------------------*)
(* X_BETA_CONV `v` `tm[v]` = |- tm[v] = (\v. tm[v]) v                         *)
(*----------------------------------------------------------------------------*)

let X_BETA_CONV v tm =
  SYM(BETA_CONV(mk_comb(mk_abs(v,tm),v)));;

(*----------------------------------------------------------------------------*)
(* EXACT_CONV - Rewrite with theorem matching exactly one in a list           *)
(*----------------------------------------------------------------------------*)

let EXACT_CONV =
  ONCE_DEPTH_CONV o FIRST_CONV o
  map (fun t -> K t o assert(prefix=(lhs(concl t))));;

(*----------------------------------------------------------------------------*)
(* Rather ad-hoc higher-order fiddling conversion                             *)
(* |- (\x. f t1[x] ... tn[x]) = (\x. f ((\x. t1[x]) x) ... ((\x. tn[x]) x))   *)
(*----------------------------------------------------------------------------*)

let HABS_CONV tm =
  let v,bod = dest_abs tm in
  let hop,pl = strip_comb bod in
  let eql = rev(map (X_BETA_CONV v) pl) in
  ABS v (itlist (C(curry MK_COMB)) eql (REFL hop));;

(*----------------------------------------------------------------------------*)
(* Expand an abbreviation                                                     *)
(*----------------------------------------------------------------------------*)

let EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
  assert(prefix= s o fst o dest_var o rhs o concl)) THEN BETA_TAC;;

(* ------------------------------------------------------------------------- *)
(* Set up the reals.                                                         *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let real_le = prove
 (`!x y. x <= y = ~(y < x)`,
  REWRITE_TAC[REAL_NOT_LT]);;

(* ------------------------------------------------------------------------- *)
(* Link a few theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

let REAL_10 = REAL_ARITH `~(&1 = &0)`;;

let REAL_LDISTRIB = REAL_ADD_LDISTRIB;;

let  REAL_LT_IADD = REAL_ARITH `!x y z. y < z ==> x + y < x + z`;;

(*----------------------------------------------------------------------------*)
(* Prove lots of boring field theorems                                        *)
(*----------------------------------------------------------------------------*)

let REAL_MUL_RID = prove(
  `!x. x * &1 = x`,
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LID);;

let REAL_MUL_RINV = prove(
  `!x. ~(x = &0) ==> (x * (inv x) = &1)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LINV);;

let REAL_RDISTRIB = prove(
  `!x y z. (x + y) * z = (x * z) + (y * z)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LDISTRIB);;

let REAL_EQ_LADD = prove(
  `!x y z. (x + y = x + z) = (y = z)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(+) (-- x)`) THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let REAL_EQ_RADD = prove(
  `!x y z. (x + z = y + z) = (x = y)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_EQ_LADD);;

let REAL_ADD_LID_UNIQ = prove(
  `!x y. (x + y = y) = (x = &0)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_ADD_LID]
  THEN MATCH_ACCEPT_TAC REAL_EQ_RADD);;

let REAL_ADD_RID_UNIQ = prove(
  `!x y. (x + y = x) = (y = &0)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_ADD_LID_UNIQ);;

let REAL_LNEG_UNIQ = prove(
  `!x y. (x + y = &0) = (x = --y)`,
  REPEAT GEN_TAC THEN SUBST1_TAC (SYM(SPEC `y:real` REAL_ADD_LINV)) THEN
  MATCH_ACCEPT_TAC REAL_EQ_RADD);;

let REAL_RNEG_UNIQ = prove(
  `!x y. (x + y = &0) = (y = --x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LNEG_UNIQ);;

let REAL_NEG_ADD = prove(
  `!x y. --(x + y) = (--x) + (--y)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ] THEN
  ONCE_REWRITE_TAC[AC REAL_ADD_AC
    `(a + b) + (c + d) = (a + c) + (b + d)`] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID]);;

let REAL_MUL_LZERO = prove(
  `!x. &0 * x = &0`,
  GEN_TAC THEN SUBST1_TAC(SYM(SPECL [`&0 * x`; `&0 * x`] REAL_ADD_LID_UNIQ))
  THEN REWRITE_TAC[GSYM REAL_RDISTRIB; REAL_ADD_LID]);;

let REAL_MUL_RZERO = prove(
  `!x. x * &0 = &0`,
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LZERO);;

let REAL_NEG_LMUL = prove(
  `!x y. --(x * y) = (--x) * y`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ; GSYM REAL_RDISTRIB;
              REAL_ADD_LINV; REAL_MUL_LZERO]);;

let REAL_NEG_RMUL = prove(
  `!x y. --(x * y) = x * (--y)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_NEG_LMUL);;

let REAL_NEGNEG = prove(
  `!x. --(--x) = x`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ; REAL_ADD_RINV]);;

let REAL_NEG_MUL2 = prove(
  `!x y. (--x) * (--y) = x * y`,
  REWRITE_TAC[GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL; REAL_NEGNEG]);;

let REAL_LT_LADD = prove(
  `!x y z. (x + y) < (x + z) = y < z`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `--x` o MATCH_MP REAL_LT_IADD) THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID];
    MATCH_ACCEPT_TAC REAL_LT_IADD]);;

let REAL_LT_RADD = prove(
  `!x y z. (x + z) < (y + z) = x < y`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LADD);;

let REAL_NOT_LT = prove(
  `!x y. ~(x < y) = y <= x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_le]);;

let REAL_LT_ANTISYM = prove(
  `!x y. ~(x < y /\ y < x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_TRANS) THEN
  REWRITE_TAC[REAL_LT_REFL]);;

let REAL_LT_GT = prove(
  `!x y. x < y ==> ~(y < x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o CONJ th)) THEN
  REWRITE_TAC[REAL_LT_ANTISYM]);;

let REAL_NOT_LE = prove(
  `!x y. ~(x <= y) = y < x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_le]);;

let REAL_LE_TOTAL = prove(
  `!x y. x <= y \/ y <= x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_le; GSYM DE_MORGAN_THM; REAL_LT_ANTISYM]);;

let REAL_LE_REFL = prove(
  `!x. x <= x`,
  GEN_TAC THEN REWRITE_TAC[real_le; REAL_LT_REFL]);;

let REAL_LE_LT = prove(
  `!x y. x <= y = x < y \/ (x = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_le] THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [`x:real`; `y:real`] REAL_LT_TOTAL) THEN ASM_REWRITE_TAC[];
    DISCH_THEN(DISJ_CASES_THEN2
     (prefix THEN (MATCH_MP_TAC REAL_LT_GT) o ACCEPT_TAC) SUBST1_TAC) THEN
    MATCH_ACCEPT_TAC REAL_LT_REFL]);;

let REAL_LT_LE = prove(
  `!x y. x < y = x <= y /\ ~(x = y)`,
  let lemma = TAUT `~(a /\ ~a)` in
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT; RIGHT_AND_OVER_OR; lemma]
  THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL]);;

let REAL_LT_IMP_LE = prove(
  `!x y. x < y ==> x <= y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_LT]);;

let REAL_LTE_TRANS = prove(
  `!x y z. x < y /\ y <= z ==> x < z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT; LEFT_AND_OVER_OR] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP REAL_LT_TRANS)
    (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN REWRITE_TAC[]);;

let REAL_LE_TRANS = prove(
  `!x y z. x <= y /\ y <= z ==> x <= z`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC))
  THEN REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C CONJ (ASSUME `y < z`)) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REAL_LT_IMP_LE o MATCH_MP REAL_LET_TRANS));;

let REAL_LTE_ANTSYM = prove(
  `!x y. ~(x <= y /\ y < x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LET_ANTISYM);;

let REAL_NEG_LT0 = prove(
  `!x. (--x) < &0 = &0 < x`,
  GEN_TAC THEN SUBST1_TAC(SYM(SPECL [`--x`; `&0`; `x:real`] REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID]);;

let REAL_NEG_GT0 = prove(
  `!x. &0 < (--x) = x < &0`,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LT0; REAL_NEGNEG]);;

let REAL_NEG_LE0 = prove(
  `!x. (--x) <= &0 = &0 <= x`,
  GEN_TAC THEN REWRITE_TAC[real_le] THEN
  REWRITE_TAC[REAL_NEG_GT0]);;

let REAL_NEG_GE0 = prove(
  `!x. &0 <= (--x) = x <= &0`,
  GEN_TAC THEN REWRITE_TAC[real_le] THEN
  REWRITE_TAC[REAL_NEG_LT0]);;

let REAL_LT_NEGTOTAL = prove(
  `!x. (x = &0) \/ (&0 < x) \/ (&0 < --x)`,
  GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [`x:real`; `&0`] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[SYM(REWRITE_RULE[REAL_NEGNEG] (SPEC `--x` REAL_NEG_LT0))]);;

let REAL_LE_NEGTOTAL = prove(
  `!x. &0 <= x \/ &0 <= --x`,
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC `x:real` REAL_LT_NEGTOTAL) THEN
  ASM_REWRITE_TAC[]);;

let REAL_LE_MUL = prove(
  `!x y. &0 <= x /\ &0 <= y ==> &0 <= (x * y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  MAP_EVERY ASM_CASES_TAC [`&0 = x`; `&0 = y`] THEN
  ASM_REWRITE_TAC[] THEN TRY(FIRST_ASSUM(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  DISCH_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_REWRITE_TAC[]);;

let REAL_LE_SQUARE = prove(
  `!x. &0 <= x * x`,
  GEN_TAC THEN DISJ_CASES_TAC (SPEC `x:real` REAL_LE_NEGTOTAL) THEN
  POP_ASSUM(MP_TAC o MATCH_MP REAL_LE_MUL o W CONJ) THEN
  REWRITE_TAC[GSYM REAL_NEG_RMUL; GSYM REAL_NEG_LMUL; REAL_NEGNEG]);;

let REAL_LT_01 = prove(
  `&0 < &1`,
  REWRITE_TAC[REAL_LT_LE; REAL_LE_01] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_10]);;

let REAL_LE_LADD = prove(
  `!x y z. (x + y) <= (x + z) = y <= z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_le] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LADD);;

let REAL_LE_RADD = prove(
  `!x y z. (x + z) <= (y + z) = x <= y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_le] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_RADD);;

let REAL_LT_ADD2 = prove(
  `!w x y z. w < x /\ y < z ==> (w + y) < (x + z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `w + z` THEN
  ASM_REWRITE_TAC[REAL_LT_LADD; REAL_LT_RADD]);;

let REAL_LT_ADD = prove(
  `!x y. &0 < x /\ &0 < y ==> &0 < (x + y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
  REWRITE_TAC[REAL_ADD_LID]);;

let REAL_LT_ADDNEG = prove(
  `!x y z. y < (x + (--z)) = (y + z) < x`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [`y:real`; `x + (--z)`; `z:real`] REAL_LT_RADD)) THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_RID]);;

let REAL_LT_ADDNEG2 = prove(
  `!x y z. (x + (--y)) < z = x < (z + y)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [`x + (-- y)`; `z:real`; `y:real`] REAL_LT_RADD)) THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_RID]);;

let REAL_LT_ADD1 = prove(
  `!x y. x <= y ==> x < (y + &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [POP_ASSUM(MP_TAC o MATCH_MP REAL_LT_ADD2 o C CONJ REAL_LT_01) THEN
    REWRITE_TAC[REAL_ADD_RID];
    POP_ASSUM SUBST1_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_LT_LADD; REAL_LT_01]]);;

let REAL_SUB_ADD = prove(
  `!x y. (x - y) + y = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC;
    REAL_ADD_LINV; REAL_ADD_RID]);;

let REAL_SUB_ADD2 = prove(
  `!x y. y + (x - y) = x`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_SUB_ADD);;

let REAL_SUB_REFL = prove(
  `!x. x - x = &0`,
  GEN_TAC THEN REWRITE_TAC[real_sub; REAL_ADD_RINV]);;

let REAL_SUB_0 = prove(
  `!x y. (x - y = &0) = (x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C AP_THM `y:real` o AP_TERM `(+)`) THEN
    REWRITE_TAC[REAL_SUB_ADD; REAL_ADD_LID];
    DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC REAL_SUB_REFL]);;

let REAL_LE_DOUBLE = prove(
  `!x. &0 <= x + x = &0 <= x`,
  GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2 o W CONJ);
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_ADD2 o W CONJ)] THEN
  REWRITE_TAC[REAL_ADD_LID]);;

let REAL_LE_NEGL = prove(
  `!x. (--x <= x) = (&0 <= x)`,
  GEN_TAC THEN SUBST1_TAC (SYM(SPECL [`x:real`; `--x`; `x:real`] REAL_LE_LADD))
  THEN REWRITE_TAC[REAL_ADD_RINV; REAL_LE_DOUBLE]);;

let REAL_LE_NEGR = prove(
  `!x. (x <= --x) = (x <= &0)`,
  GEN_TAC THEN SUBST1_TAC(SYM(SPEC `x:real` REAL_NEGNEG)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_LE_NEGL] THEN REWRITE_TAC[REAL_NEG_GE0] THEN
  REWRITE_TAC[REAL_NEGNEG]);;

let REAL_NEG_EQ0 = prove(
  `!x. (--x = &0) = (x = &0)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(+) x`);
    DISCH_THEN(MP_TAC o AP_TERM `(+) (--x)`)] THEN
  REWRITE_TAC[REAL_ADD_RINV; REAL_ADD_LINV; REAL_ADD_RID] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let REAL_NEG_0 = prove(
  `--(&0) = &0`,
  REWRITE_TAC[REAL_NEG_EQ0]);;

let REAL_NEG_SUB = prove(
  `!x y. --(x - y) = y - x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub; REAL_NEG_ADD; REAL_NEGNEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);;

let REAL_SUB_LT = prove(
  `!x y. &0 < x - y = y < x`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [`&0`; `x - y`; `y:real`] REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD; REAL_ADD_LID]);;

let REAL_SUB_LE = prove(
  `!x y. &0 <= (x - y) = y <= x`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [`&0`; `x - y`; `y:real`] REAL_LE_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD; REAL_ADD_LID]);;

let REAL_EQ_LMUL = prove(
  `!x y z. (x * y = x * z) = (x = &0) \/ (y = z)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(*) (inv x)`) THEN
    ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM(fun th -> REWRITE_TAC
      [REAL_MUL_ASSOC; MATCH_MP REAL_MUL_LINV th]) THEN
    REWRITE_TAC[REAL_MUL_LID];
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_LZERO]]);;

let REAL_EQ_RMUL = prove(
  `!x y z. (x * z = y * z) = (z = &0) \/ (x = y)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_EQ_LMUL);;

let REAL_SUB_LDISTRIB = prove(
  `!x y z. x * (y - z) = (x * y) - (x * z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub; REAL_LDISTRIB; REAL_NEG_RMUL]);;

let REAL_SUB_RDISTRIB = prove(
  `!x y z. (x - y) * z = (x * z) - (y * z)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_SUB_LDISTRIB);;

let REAL_NEG_EQ = prove(
  `!x y. (--x = y) = (x = --y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM); DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_NEGNEG]);;

let REAL_NEG_MINUS1 = prove(
  `!x. --x = (--(&1)) * x`,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
  REWRITE_TAC[REAL_MUL_LID]);;

let REAL_INV_NZ = prove(
  `!x. ~(x = &0) ==> ~(inv x = &0)`,
  GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o C AP_THM `x:real` o AP_TERM `(*)`) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_10]);;

let REAL_INVINV = prove(
  `!x. ~(x = &0) ==> (inv (inv x) = x)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_MUL_RINV) THEN
  ASM_CASES_TAC `inv x = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; GSYM REAL_10] THEN
  MP_TAC(SPECL [`inv(inv x)`; `x:real`; `inv x`] REAL_EQ_RMUL)
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
  FIRST_ASSUM ACCEPT_TAC);;

let REAL_LT_IMP_NE = prove(
  `!x y. x < y ==> ~(x = y)`,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_LT_REFL]);;

let REAL_INV_POS = prove(
  `!x. &0 < x ==> &0 < inv x`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT_TCL DISJ_CASES_THEN
   MP_TAC (SPECL [`inv x`; `&0`] REAL_LT_TOTAL) THENL
   [POP_ASSUM(ASSUME_TAC o MATCH_MP REAL_INV_NZ o
              GSYM o MATCH_MP REAL_LT_IMP_NE) THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[GSYM REAL_NEG_GT0] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL o C CONJ (ASSUME `&0 < x`)) THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
    POP_ASSUM(fun th -> REWRITE_TAC
     [MATCH_MP REAL_MUL_LINV (GSYM (MATCH_MP REAL_LT_IMP_NE th))]) THEN
    REWRITE_TAC[REAL_NEG_GT0] THEN DISCH_THEN(MP_TAC o CONJ REAL_LT_01) THEN
    REWRITE_TAC[REAL_LT_ANTISYM];
    REWRITE_TAC[]]);;

let REAL_LT_LMUL_0 = prove(
  `!x y. &0 < x ==> (&0 < (x * y) = &0 < y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [FIRST_ASSUM(fun th ->
      DISCH_THEN(MP_TAC o CONJ (MATCH_MP REAL_INV_POS th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC
      [MATCH_MP REAL_MUL_LINV (GSYM (MATCH_MP REAL_LT_IMP_NE th))]) THEN
    REWRITE_TAC[REAL_MUL_LID];
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]);;

let REAL_LT_RMUL_0 = prove(
  `!x y. &0 < y ==> (&0 < (x * y) = &0 < x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LMUL_0);;

let REAL_LT_LMUL_EQ = prove(
  `!x y z. &0 < x ==> ((x * y) < (x * z) = y < z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LMUL_0);;

let REAL_LT_RMUL_EQ = prove(
  `!x y z. &0 < z ==> ((x * z) < (y * z) = x < y)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LMUL_EQ);;

let REAL_LT_RMUL_IMP = prove(
  `!x y z. x < y /\ &0 < z ==> (x * z) < (y * z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  POP_ASSUM(fun th -> REWRITE_TAC[GEN_ALL(MATCH_MP REAL_LT_RMUL_EQ th)]));;

let REAL_LT_LMUL_IMP = prove(
  `!x y z. y < z  /\ &0 < x ==> (x * y) < (x * z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  POP_ASSUM(fun th -> REWRITE_TAC[GEN_ALL(MATCH_MP REAL_LT_LMUL_EQ th)]));;

let REAL_LINV_UNIQ = prove(
  `!x y. (x * y = &1) ==> (x = inv y)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; GSYM REAL_10] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(*) (inv x)`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC REAL_INVINV);;

let REAL_RINV_UNIQ = prove(
  `!x y. (x * y = &1) ==> (y = inv x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LINV_UNIQ);;

let REAL_NEG_INV = prove(
  `!x. ~(x = &0) ==> (--(inv x) = inv(--x))`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL] THEN
  POP_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_NEGNEG]);;

let REAL_INV_1OVER = prove(
  `!x. inv x = &1 / x`,
  GEN_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LID]);;

(*----------------------------------------------------------------------------*)
(* Prove homomorphisms for the inclusion map                                  *)
(*----------------------------------------------------------------------------*)

let REAL = prove(
  `!n. &(SUC n) = &n + &1`,
  REWRITE_TAC[ADD1; REAL_OF_NUM_ADD]);;

let REAL_POS = prove(
  `!n. &0 <= &n`,
  INDUCT_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n` THEN ASM_REWRITE_TAC[REAL] THEN
  REWRITE_TAC[REAL_LE_ADDR; REAL_LE_01]);;

let REAL_LE = prove(
  `!m n. &m <= &n = m <= n`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
   [REAL; REAL_LE_RADD; LE_0; LE_SUC; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM NOT_LT; LT_0] THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n` THEN
    ASM_REWRITE_TAC[LE_0; REAL_LE_ADDR; REAL_LE_01];
    DISCH_THEN(MP_TAC o C CONJ (SPEC `m:num` REAL_POS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
    REWRITE_TAC[REAL_NOT_LE; REAL_LT_ADDR; REAL_LT_01]]);;

let REAL_LT = prove(
  `!m n. &m < &n = m < n`,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC ((REWRITE_RULE[] o AP_TERM `(~)` o
    REWRITE_RULE[GSYM NOT_LT; GSYM REAL_NOT_LT]) (SPEC_ALL REAL_LE)));;

let REAL_INJ = prove(
  `!m n. (&m = &n) = (m = n)`,
  let th = prove(`(m = n) = m:num <= n /\ n <= m`,
                 EQ_TAC THENL
                  [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_REFL];
                   MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[th; GSYM REAL_LE_ANTISYM; REAL_LE]);;

let REAL_ADD = prove(
  `!m n. &m + &n = &(m + n)`,
  INDUCT_TAC THEN REWRITE_TAC[REAL; ADD; REAL_ADD_LID] THEN
  RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ADD_AC]);;

let REAL_MUL = prove(
  `!m n. &m * &n = &(m * n)`,
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; MULT_CLAUSES; REAL;
    GSYM REAL_ADD; REAL_RDISTRIB] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[REAL_MUL_LID]);;

(*----------------------------------------------------------------------------*)
(* Now more theorems                                                          *)
(*----------------------------------------------------------------------------*)

let REAL_INV1 = prove(
  `inv(&1) = &1`,
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[REAL_MUL_LID]);;

let REAL_DIV_LZERO = prove(
  `!x. &0 / x = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

let REAL_LT_NZ = prove(
  `!n. ~(&n = &0) = (&0 < &n)`,
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  ASM_CASES_TAC `&n = &0` THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS]);;

let REAL_NZ_IMP_LT = prove(
  `!n. ~(n = 0) ==> &0 < &n`,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_INJ; REAL_LT_NZ]);;

let REAL_LT_RDIV_0 = prove(
  `!y z. &0 < z ==> (&0 < (y / z) = &0 < y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL_0 THEN
  MATCH_MP_TAC REAL_INV_POS THEN POP_ASSUM ACCEPT_TAC);;

let REAL_LT_RDIV = prove(
  `!x y z. &0 < z ==> ((x / z) < (y / z) = x < y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL_EQ THEN
  MATCH_MP_TAC REAL_INV_POS THEN POP_ASSUM ACCEPT_TAC);;

let REAL_LT_FRACTION_0 = prove(
  `!n d. ~(n = 0) ==> (&0 < (d / &n) = &0 < d)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_RDIV_0 THEN
  ASM_REWRITE_TAC[GSYM REAL_LT_NZ; REAL_INJ]);;

let REAL_LT_MULTIPLE = prove(
  `!n d. 1 < n ==> (d < (&n * d) = &0 < d)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN INDUCT_TAC THENL
   [REWRITE_TAC[num_CONV `1`; NOT_LESS_0];
    POP_ASSUM MP_TAC THEN ASM_CASES_TAC `1 < n` THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[REAL; REAL_LDISTRIB; REAL_MUL_RID; REAL_LT_ADDL] THEN
      MATCH_MP_TAC REAL_LT_RMUL_0 THEN REWRITE_TAC[REAL_LT] THEN
      MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `1` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[num_CONV `1`; LT_0];
      GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LESS_LEMMA1) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL; REAL_LDISTRIB; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_LT_ADDL]]]);;

let REAL_LT_FRACTION = prove(
  `!n d. (1 < n) ==> ((d / &n) < d = &0 < d)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[NOT_LESS_0] THEN DISCH_TAC THEN
  UNDISCH_TAC `1 < n` THEN
  FIRST_ASSUM(fun th -> let th1 = REWRITE_RULE[GSYM REAL_INJ] th in
    MAP_EVERY ASSUME_TAC [th1; REWRITE_RULE[REAL_LT_NZ] th1]) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
                     [GSYM(MATCH_MP REAL_LT_RMUL_EQ th)]) THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_MULTIPLE);;

let REAL_LT_HALF1 = prove(
  `!d. &0 < (d / &2) = &0 < d`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_FRACTION_0 THEN
  REWRITE_TAC[num_CONV `2`; NOT_SUC]);;

let REAL_LT_HALF2 = prove(
  `!d. (d / &2) < d = &0 < d`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_FRACTION THEN
  CONV_TAC(RAND_CONV num_CONV) THEN
  REWRITE_TAC[LESS_SUC_REFL]);;

let REAL_DOUBLE = prove(
  `!x. x + x = &2 * x`,
  GEN_TAC THEN REWRITE_TAC[num_CONV `2`; REAL] THEN
  REWRITE_TAC[REAL_RDISTRIB; REAL_MUL_LID]);;

let REAL_HALF_DOUBLE = prove(
  `!x. (x / &2) + (x / &2) = x`,
  GEN_TAC THEN REWRITE_TAC[REAL_DOUBLE] THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC[REAL_INJ] THEN
  REWRITE_TAC[num_CONV `2`; NOT_SUC]);;

let REAL_SUB_SUB = prove(
  `!x y. (x - y) - x = --y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
  ONCE_REWRITE_TAC[AC REAL_ADD_AC
    `(a + b) + c = (c + a) + b`] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID]);;

let REAL_LT_ADD_SUB = prove(
  `!x y z. (x + y) < z = x < (z - y)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [`x:real`; `z - y`; `y:real`] REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD]);;

let REAL_LT_SUB_RADD = prove(
  `!x y z. (x - y) < z = x < z + y`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [`x - y`; `z:real`; `y:real`] REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD]);;

let REAL_LT_SUB_LADD = prove(
  `!x y z. x < (y - z) = (x + z) < y`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [`x + z`; `y:real`; `--z`] REAL_LT_RADD)) THEN
  REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC; REAL_ADD_RINV; REAL_ADD_RID]);;

let REAL_LE_SUB_LADD = prove(
  `!x y z. x <= (y - z) = (x + z) <= y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT; REAL_LT_SUB_RADD]);;

let REAL_LE_SUB_RADD = prove(
  `!x y z. (x - y) <= z = x <= z + y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT; REAL_LT_SUB_LADD]);;

let REAL_LT_NEG = prove(
  `!x y. --x < --y = y < x`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL[`--x`; `--y`; `x + y`] REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_RINV; REAL_ADD_LID]);;

let REAL_LE_NEG = prove(
  `!x y. --x <= --y = y <= x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[REAL_LT_NEG]);;

let REAL_SUB_LZERO = prove(
  `!x. &0 - x = --x`,
  GEN_TAC THEN REWRITE_TAC[real_sub; REAL_ADD_LID]);;

let REAL_SUB_RZERO = prove(
  `!x. x - &0 = x`,
  GEN_TAC THEN REWRITE_TAC[real_sub; REAL_NEG_0; REAL_ADD_RID]);;

let REAL_LTE_ADD2 = prove(
  `!w x y z. w < x /\ y <= z ==> (w + y) < (x + z)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LET_ADD2);;

let REAL_LTE_ADD = prove(
  `!x y. &0 < x /\ &0 <= y ==> &0 < (x + y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBST1_TAC(SYM(SPEC `&0` REAL_ADD_LID)) THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN
  ASM_REWRITE_TAC[]);;

let REAL_LT_MUL2_ALT = prove(
  `!x1 x2 y1 y2. &0 <= x1 /\ &0 <= y1 /\ x1 < x2 /\ y1 < y2 ==>
        (x1 * y1) < (x2 * y2)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `!a b c d.
    (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC REAL_ADD_AC
      `(a + b) + (c + d) = (b + c) + (a + d)`] THEN
    REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID];
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x1:real` THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);;

let REAL_SUB_LNEG = prove(
  `!x y. (--x) - y = --(x + y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub; REAL_NEG_ADD]);;

let REAL_SUB_RNEG = prove(
  `!x y. x - (--y) = x + y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub; REAL_NEGNEG]);;

let REAL_SUB_NEG2 = prove(
  `!x y. (--x) - (--y) = y - x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_SUB_LNEG] THEN
  REWRITE_TAC[real_sub; REAL_NEG_ADD; REAL_NEGNEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);;

let REAL_SUB_TRIANGLE = prove(
  `!a b c. (a - b) + (b - c) = a - c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
  ONCE_REWRITE_TAC[AC REAL_ADD_AC
    `(a + b) + (c + d) = (b + c) + (a + d)`] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID]);;

let REAL_INV_MUL_WEAK = prove(
  `!x y. ~(x = &0) /\ ~(y = &0) ==>
             (inv(x * y) = inv(x) * inv(y))`,
  REWRITE_TAC[REAL_INV_MUL]);;

let REAL_LE_LMUL_LOCAL = prove(
  `!x y z. &0 < x ==> ((x * y) <= (x * z) = y <= z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC REAL_LT_LMUL_EQ THEN ASM_REWRITE_TAC[]);;

let REAL_LE_RMUL_EQ = prove(
  `!x y z. &0 < z ==> ((x * z) <= (y * z) = x <= y)`,
   REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   MATCH_ACCEPT_TAC REAL_LE_LMUL_LOCAL);;

let REAL_SUB_INV2 = prove(
  `!x y. ~(x = &0) /\ ~(y = &0) ==>
                (inv(x) - inv(y) = (y - x) / (x * y))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[real_div; REAL_SUB_RDISTRIB] THEN
  SUBGOAL_THEN `inv(x * y) = inv(x) * inv(y)` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INV_MUL_WEAK THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  EVERY_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  EVERY_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID]);;

let REAL_SUB_SUB2 = prove(
  `!x y. x - (x - y) = y`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NEGNEG] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_NEG_SUB; REAL_SUB_SUB]);;

let REAL_MEAN = prove(
  `!x y. x < y ==> ?z. x < z /\ z < y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_DOWN o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT])
  THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x + d` THEN ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  ASM_REWRITE_TAC[GSYM REAL_LT_SUB_LADD]);;

let REAL_EQ_LMUL2 = prove(
  `!x y z. ~(x = &0) ==> ((y = z) = (x * y = x * z))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:real`; `y:real`; `z:real`] REAL_EQ_LMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN REFL_TAC);;

let REAL_LE_MUL2V = prove(
  `!x1 x2 y1 y2.
    (& 0) <= x1 /\ (& 0) <= y1 /\ x1 <= x2 /\ y1 <= y2 ==>
    (x1 * y1) <= (x2 * y2)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SPECL [`x1:real`; `x2:real`] REAL_LE_LT) THEN
  ASM_CASES_TAC `x1:real = x2` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [UNDISCH_TAC `&0 <= x2` THEN
    DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
     [FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL_LOCAL th]);
      SUBST1_TAC(SYM(ASSUME `&0 = x2`)) THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL]]; ALL_TAC] THEN
  UNDISCH_TAC `y1 <= y2` THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_MUL2_ALT THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `&0 <= y1` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP REAL_LE_RMUL_EQ th]) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    SUBST1_TAC(SYM(ASSUME `&0 = y2`)) THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]]);;

let REAL_LE_LDIV = prove(
  `!x y z. &0 < x /\ y <= (z * x) ==> (y / x) <= z`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
  SUBGOAL_THEN `y = (y / x) * x` MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC;
    DISCH_THEN(fun t -> GEN_REWRITE_TAC (funpow 2 LAND_CONV) [t])
    THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN POP_ASSUM ACCEPT_TAC]);;

let REAL_LE_RDIV = prove(
  `!x y z. &0 < x /\ (y * x) <= z ==> y <= (z / x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
  SUBGOAL_THEN `z = (z / x) * x` MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC;
    DISCH_THEN(fun t -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [t])
    THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN POP_ASSUM ACCEPT_TAC]);;

let REAL_LT_1 = prove(
  `!x y. &0 <= x /\ x < y ==> (x / y) < &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x / y) < &1 = ((x / y) * y) < (&1 * y)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_RMUL_EQ THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x:real` THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(x / y) * y = x` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_MUL_LID]]]);;

let REAL_LE_LMUL_IMP = prove(
  `!x y z. &0 <= x /\ y <= z ==> (x * y) <= (x * z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL_LOCAL th]);
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_ACCEPT_TAC REAL_LE_REFL]);;

let REAL_LE_RMUL_IMP = prove(
  `!x y z. &0 <= x /\ y <= z ==> (y * x) <= (z * x)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_LE_LMUL_IMP);;

let REAL_INV_LT1 = prove(
  `!x. &0 < x /\ x < &1 ==> &1 < inv(x)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_INV_POS) THEN
  GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`inv(x)`; `&1`; `x:real`; `&1`] REAL_LT_MUL2_ALT) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NE) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_LINV THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&0 < &0` THEN
      REWRITE_TAC[REAL_LT_REFL]];
    DISCH_THEN(MP_TAC o AP_TERM `inv`) THEN REWRITE_TAC[REAL_INV1] THEN
    SUBGOAL_THEN `inv(inv x) = x` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INVINV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 < &1` THEN
      REWRITE_TAC[REAL_LT_REFL]]]);;

let REAL_POS_NZ = prove(
  `!x. &0 < x ==> ~(x = &0)`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_LT_IMP_NE) THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN POP_ASSUM ACCEPT_TAC);;

let REAL_EQ_RMUL_IMP = prove(
  `!x y z. ~(z = &0) /\ (x * z = y * z) ==> (x = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[REAL_EQ_RMUL]);;

let REAL_EQ_LMUL_IMP = prove(
  `!x y z. ~(x = &0) /\ (x * y = x * z) ==> (y = z)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_EQ_RMUL_IMP);;

let REAL_FACT_NZ = prove(
  `!n. ~(&(FACT n) = &0)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
  REWRITE_TAC[REAL_LT; FACT_LT]);;

let REAL_POSSQ = prove(
  `!x. &0 < (x * x) = ~(x = &0)`,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN AP_TERM_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C CONJ (SPEC `x:real` REAL_LE_SQUARE)) THEN
    REWRITE_TAC[REAL_LE_ANTISYM; REAL_ENTIRE];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL]]);;

let REAL_SUMSQ = prove(
  `!x y. ((x * x) + (y * y) = &0) = (x = &0) /\ (y = &0)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    DISCH_THEN DISJ_CASES_TAC THEN MATCH_MP_TAC REAL_POS_NZ THENL
     [MATCH_MP_TAC REAL_LTE_ADD; MATCH_MP_TAC REAL_LET_ADD] THEN
    ASM_REWRITE_TAC[REAL_POSSQ; REAL_LE_SQUARE];
    DISCH_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID]]);;

let REAL_EQ_NEG = prove(
  `!x y. (--x = --y) = (x = y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; REAL_LE_NEG] THEN
  MATCH_ACCEPT_TAC CONJ_SYM);;

let REAL_DIV_MUL2 = prove(
  `!x z. ~(x = &0) /\ ~(z = &0) ==> !y. y / z = (x * y) / (x * z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[real_div] THEN IMP_SUBST_TAC REAL_INV_MUL_WEAK THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
    `(a * b) * (c * d) = (c * a) * (b * d)`] THEN
  IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LID]);;

let REAL_MIDDLE1 = prove(
  `!a b. a <= b ==> a <= (a + b) / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_RDIV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_DOUBLE] THEN
  ASM_REWRITE_TAC[GSYM REAL_DOUBLE; REAL_LE_LADD] THEN
  REWRITE_TAC[num_CONV `2`; REAL_LT; LT_0]);;

let REAL_MIDDLE2 = prove(
  `!a b. a <= b ==> ((a + b) / &2) <= b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_LDIV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_DOUBLE] THEN
  ASM_REWRITE_TAC[GSYM REAL_DOUBLE; REAL_LE_RADD] THEN
  REWRITE_TAC[num_CONV `2`; REAL_LT; LT_0]);;

(*----------------------------------------------------------------------------*)
(* Define usual norm (absolute distance) on the real line                     *)
(*----------------------------------------------------------------------------*)

let ABS_ZERO = prove(
  `!x. (abs(x) = &0) = (x = &0)`,
  GEN_TAC THEN REWRITE_TAC[real_abs] THEN
  LCOND_CASES_TAC THEN REWRITE_TAC[REAL_NEG_EQ0]);;

let ABS_0 = prove(
  `abs(&0) = &0`,
  REWRITE_TAC[ABS_ZERO]);;

let ABS_1 = prove(
  `abs(&1) = &1`,
  REWRITE_TAC[real_abs; REAL_LE; LE_0]);;

let ABS_NEG = prove(
  `!x. abs(--x) = abs(x)`,
  GEN_TAC THEN REWRITE_TAC[real_abs; REAL_NEGNEG; REAL_NEG_GE0] THEN
  REPEAT LCOND_CASES_TAC THEN REWRITE_TAC[] THENL
   [MP_TAC(CONJ (ASSUME `&0 <= x`) (ASSUME `x <= &0`)) THEN
    REWRITE_TAC[REAL_LE_ANTISYM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_NEG_0];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    W(MP_TAC o end_itlist CONJ o map snd o fst) THEN
    REWRITE_TAC[REAL_LT_ANTISYM]]);;

let ABS_TRIANGLE = prove(
  `!x y. abs(x + y) <= abs(x) + abs(y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_abs] THEN
  REPEAT LCOND_CASES_TAC THEN
  REWRITE_TAC[REAL_NEG_ADD; REAL_LE_REFL; REAL_LE_LADD; REAL_LE_RADD] THEN
  ASM_REWRITE_TAC[GSYM REAL_NEG_ADD; REAL_LE_NEGL; REAL_LE_NEGR] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(UNDISCH_TAC `(x + y) < &0`) THEN SUBST1_TAC(SYM(SPEC `&0` REAL_ADD_LID))
  THEN REWRITE_TAC[REAL_NOT_LT] THEN
  MAP_FIRST MATCH_MP_TAC [REAL_LT_ADD2; REAL_LE_ADD2] THEN
  ASM_REWRITE_TAC[]);;

let ABS_POS = prove(
  `!x. &0 <= abs(x)`,
  GEN_TAC THEN ASM_CASES_TAC `&0 <= x` THENL
   [ALL_TAC;
    MP_TAC(SPEC `x:real` REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[real_abs]);;

let ABS_MUL = prove(
  `!x y. abs(x * y) = abs(x) * abs(y)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 <= x` THENL
   [ALL_TAC;
    MP_TAC(SPEC `x:real` REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM ABS_NEG] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM ABS_NEG]
    THEN REWRITE_TAC[REAL_NEG_LMUL]] THEN
  (ASM_CASES_TAC `&0 <= y` THENL
    [ALL_TAC;
     MP_TAC(SPEC `y:real` REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
     POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [GSYM ABS_NEG] THEN
     GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM ABS_NEG] THEN
     REWRITE_TAC[REAL_NEG_RMUL]]) THEN
  ASSUM_LIST(ASSUME_TAC o MATCH_MP REAL_LE_MUL o end_itlist CONJ o rev) THEN
  ASM_REWRITE_TAC[real_abs]);;

let ABS_LT_MUL2 = prove(
  `!w x y z. abs(w) < y /\ abs(x) < z ==> abs(w * x) < (y * z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2_ALT THEN
  ASM_REWRITE_TAC[ABS_POS]);;

let ABS_SUB = prove(
  `!x y. abs(x - y) = abs(y - x)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_NEG_SUB] THEN
  REWRITE_TAC[ABS_NEG]);;

let ABS_NZ = prove(
  `!x. ~(x = &0) = &0 < abs(x)`,
  GEN_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABS_ZERO] THEN
    REWRITE_TAC[TAUT `~a ==> b = b \/ a`] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC[GSYM REAL_LE_LT; ABS_POS];
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_abs; REAL_LT_REFL; REAL_LE_REFL]]);;

let ABS_INV = prove(
  `!x. ~(x = &0) ==> (abs(inv x) = inv(abs(x)))`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[real_abs; REAL_LE] THEN
  REWRITE_TAC[num_CONV `1`; GSYM NOT_LT; NOT_LESS_0]);;

let ABS_ABS = prove(
  `!x. abs(abs(x)) = abs(x)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [real_abs] THEN
  REWRITE_TAC[ABS_POS]);;

let ABS_LE = prove(
  `!x. x <= abs(x)`,
  GEN_TAC THEN REWRITE_TAC[real_abs] THEN
  LCOND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_LE_NEGR] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_NOT_LE]);;

let ABS_REFL = prove(
  `!x. (abs(x) = x) = &0 <= x`,
  GEN_TAC THEN REWRITE_TAC[real_abs] THEN
  ASM_CASES_TAC `&0 <= x` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  ONCE_REWRITE_TAC[GSYM REAL_RNEG_UNIQ] THEN
  REWRITE_TAC[REAL_DOUBLE; REAL_ENTIRE; REAL_INJ] THEN
  REWRITE_TAC[num_CONV `2`; NOT_SUC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_LE_REFL]);;

let ABS_N = prove(
  `!n. abs(&n) = &n`,
  GEN_TAC THEN REWRITE_TAC[ABS_REFL; REAL_LE; LE_0]);;

let ABS_BETWEEN = prove(
  `!x y d. &0 < d /\ ((x - d) < y) /\ (y < (x + d)) = abs(y - x) < d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_abs] THEN
  REWRITE_TAC[REAL_SUB_LE] THEN REWRITE_TAC[REAL_NEG_SUB] THEN
  LCOND_CASES_TAC THEN REWRITE_TAC[REAL_LT_SUB_RADD] THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV) [REAL_ADD_SYM] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `x < (x + d)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `y:real` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_ADDR] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `y:real` THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    SUBGOAL_THEN `y < (y + d)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `x:real` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_ADDR] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `x:real` THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR]]);;

let ABS_BOUND = prove(
  `!x y d. abs(x - y) < d ==> y < (x + d)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  ONCE_REWRITE_TAC[GSYM ABS_BETWEEN] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let ABS_STILLNZ = prove(
  `!x y. abs(x - y) < abs(y) ==> ~(x = &0)`,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_LZERO; ABS_NEG; REAL_LT_REFL]);;

let ABS_CASES = prove(
  `!x. (x = &0) \/ &0 < abs(x)`,
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_NZ] THEN
  BOOL_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[]);;

let ABS_BETWEEN1 = prove(
  `!x y z. x < z /\ (abs(y - x)) < (z - x) ==> y < z`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (SPECL [`x:real`; `y:real`] REAL_LET_TOTAL) THENL
   [ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN
    REWRITE_TAC[real_sub; REAL_LT_RADD] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2);
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[]]);;

let ABS_SIGN = prove(
  `!x y. abs(x - y) < y ==> &0 < x`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ABS_BOUND) THEN
  REWRITE_TAC[REAL_LT_ADDL]);;

let ABS_SIGN2 = prove(
  `!x y. abs(x - y) < --y ==> x < &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`--x`; `--y`] ABS_SIGN) THEN
  REWRITE_TAC[REAL_SUB_NEG2] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[GSYM REAL_NEG_LT0; REAL_NEGNEG]);;

let ABS_DIV = prove(
  `!y. ~(y = &0) ==> !x. abs(x / y) = abs(x) / abs(y)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[real_div] THEN
  REWRITE_TAC[ABS_MUL] THEN
  POP_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ABS_INV th]));;

let ABS_CIRCLE = prove(
  `!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(x) + abs(h)` THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN
  POP_ASSUM(MP_TAC o CONJ (SPEC `abs(x)` REAL_LE_REFL)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LET_ADD2) THEN
  REWRITE_TAC[REAL_SUB_ADD2]);;

let REAL_SUB_ABS = prove(
  `!x y. (abs(x) - abs(y)) <= abs(x - y)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(abs(x - y) + abs(y)) - abs(y)` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[real_sub] THEN REWRITE_TAC[REAL_LE_RADD] THEN
    SUBST1_TAC(SYM(SPECL [`x:real`; `y:real`] REAL_SUB_ADD)) THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_SUB_ADD] THEN
    MATCH_ACCEPT_TAC ABS_TRIANGLE;
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    REWRITE_TAC[REAL_ADD_SUB; REAL_LE_REFL]]);;

let ABS_SUB_ABS = prove(
  `!x y. abs(abs(x) - abs(y)) <= abs(x - y)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [real_abs] THEN
  LCOND_CASES_TAC THEN REWRITE_TAC[REAL_SUB_ABS] THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN
  REWRITE_TAC[REAL_SUB_ABS]);;

let ABS_BETWEEN2 = prove(
  `!x0 x y0 y. x0 < y0 /\ abs(x - x0) < (y0 - x0) / &2 /\
                          abs(y - y0) < (y0 - x0) / &2
        ==> x < y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `x < y0 /\ x0 < y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`x0:real`; `x:real`; `y0 - x0`] ABS_BOUND) THEN
      REWRITE_TAC[REAL_SUB_ADD2] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[ABS_SUB] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC `(y0 - x0) / &2` THEN ASM_REWRITE_TAC[REAL_LT_HALF2] THEN
      ASM_REWRITE_TAC[REAL_SUB_LT];
      GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
      PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(AC REAL_ADD_AC
       `(y0 + --x0) + (x0 + --y) = (--x0 + x0) + (y0 + --y)`) THEN
      REWRITE_TAC[GSYM real_sub; REAL_ADD_LINV; REAL_ADD_LID] THEN
      DISCH_TAC THEN
      MP_TAC(SPECL [`y0 - x0`; `x0 - y`] REAL_LE_ADDR) THEN
      ASM_REWRITE_TAC[REAL_SUB_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(y0 <= y)` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_NOT_LE] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `y0 - x0` THEN
        ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_SUB_LT]; ALL_TAC] THEN
      UNDISCH_TAC `abs(y - y0) < (y0 - x0) / &2` THEN
      ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN
      REWRITE_TAC[REAL_NEG_SUB] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y0 - x0) < (y0 - x0) / &2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `y0 - y` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      REWRITE_TAC[REAL_LT_HALF2] THEN ASM_REWRITE_TAC[REAL_SUB_LT]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(x0 - y) < (y0 - x0) / &2` ASSUME_TAC THENL
   [REWRITE_TAC[real_abs; REAL_SUB_LE] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_NEG_SUB] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `x - x0` THEN REWRITE_TAC[real_sub; REAL_LE_RADD] THEN
    ASM_REWRITE_TAC[GSYM real_sub] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(x - x0)` THEN ASM_REWRITE_TAC[ABS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(y0 - x0) < ((y0 - x0) / &2) + ((y0 - x0) / &2)`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_HALF_DOUBLE; REAL_NOT_LT; ABS_LE]] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(y0 - y) + abs(y - x0)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LT_ADD2 THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `y0 - x0 = (y0 - y) + (y - x0)` SUBST1_TAC THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN
  REWRITE_TAC[real_sub] THEN
  ONCE_REWRITE_TAC[AC REAL_ADD_AC
    `(a + b) + (c + d) = (b + c) + (a + d)`] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID]);;

let ABS_BOUNDS = prove(
  `!x k. abs(x) <= k = --k <= x /\ x <= k`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_LE_NEG] THEN
  REWRITE_TAC[REAL_NEGNEG] THEN REWRITE_TAC[real_abs] THEN
  LCOND_CASES_TAC THENL
   [REWRITE_TAC[TAUT `(a = b /\ a) = a ==> b`] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[REAL_LE_NEGL];
    REWRITE_TAC[TAUT `(a = a /\ b) = a ==> b`] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `--x` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LE_NEGR] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE]]);;

(*----------------------------------------------------------------------------*)
(* Define integer powers                                                      *)
(*----------------------------------------------------------------------------*)

let pow = real_pow;;

let POW_0 = prove(
  `!n. &0 pow (SUC n) = &0`,
  INDUCT_TAC THEN REWRITE_TAC[pow; REAL_MUL_LZERO]);;

let POW_NZ = prove(
  `!c n. ~(c = &0) ==> ~(c pow n = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[pow; REAL_10; REAL_ENTIRE]);;

let POW_INV = prove(
  `!c. ~(c = &0) ==> !n. (inv(c pow n) = (inv c) pow n)`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[pow; REAL_INV1] THEN
  MP_TAC(SPECL [`c:real`; `c pow n`] REAL_INV_MUL_WEAK) THEN
  ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `~(c pow n = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC POW_NZ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let POW_ABS = prove(
  `!c n. abs(c) pow n = abs(c pow n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow; ABS_1; ABS_MUL]);;

let POW_PLUS1 = prove(
  `!e. &0 < e ==> !n. (&1 + (&n * e)) <= (&1 + e) pow n`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[pow; REAL_MUL_LZERO; REAL_ADD_RID; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + e) * (&1 + (&n * e))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_RDISTRIB; REAL; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_LDISTRIB;REAL_MUL_RID; REAL_ADD_ASSOC; REAL_LE_ADDR] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_SQUARE; REAL_LE; LE_0];
    SUBGOAL_THEN `&0 < (&1 + e)`
      (fun th -> ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL_LOCAL th]) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_LID] THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LT] THEN REWRITE_TAC[num_CONV `1`; LT_0]]);;

let POW_ADD = prove(
  `!c m n. c pow (m + n) = (c pow m) * (c pow n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow; ADD_CLAUSES; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let POW_1 = prove(
  `!x. x pow 1 = x`,
  GEN_TAC THEN REWRITE_TAC[num_CONV `1`] THEN
  REWRITE_TAC[pow; REAL_MUL_RID]);;

let POW_2 = prove(
  `!x. x pow 2 = x * x`,
  GEN_TAC THEN REWRITE_TAC[num_CONV `2`] THEN
  REWRITE_TAC[pow; POW_1]);;

let POW_POS = prove(
  `!x n. &0 <= x ==> &0 <= (x pow n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[pow; REAL_LE_01] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]);;

let POW_LE = prove(
  `!n x y. &0 <= x /\ x <= y ==> (x pow n) <= (y pow n)`,
  INDUCT_TAC THEN REWRITE_TAC[pow; REAL_LE_REFL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL2V THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[POW_POS]);;

let POW_M1 = prove(
  `!n. abs((--(&1)) pow n) = &1`,
  INDUCT_TAC THEN REWRITE_TAC[pow; ABS_NEG; ABS_1] THEN
  ASM_REWRITE_TAC[ABS_MUL; ABS_NEG; ABS_1; REAL_MUL_LID]);;

let POW_MUL = prove(
  `!n x y. (x * y) pow n = (x pow n) * (y pow n)`,
  INDUCT_TAC THEN REWRITE_TAC[pow; REAL_MUL_LID] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let REAL_LE_POW2 = prove(
  `!x. &0 <= x pow 2`,
  GEN_TAC THEN REWRITE_TAC[POW_2; REAL_LE_SQUARE]);;

let ABS_POW2 = prove(
  `!x. abs(x pow 2) = x pow 2`,
  GEN_TAC THEN REWRITE_TAC[ABS_REFL; REAL_LE_POW2]);;

let REAL_POW2_ABS = prove(
  `!x. abs(x) pow 2 = x pow 2`,
  GEN_TAC THEN REWRITE_TAC[POW_2; POW_MUL] THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  REWRITE_TAC[GSYM POW_2; ABS_POW2]);;

let REAL_LE1_POW2 = prove(
  `!x. &1 <= x ==> &1 <= (x pow 2)`,
  GEN_TAC THEN REWRITE_TAC[POW_2] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2V THEN ASM_REWRITE_TAC[REAL_LE_01]);;

let REAL_LT1_POW2 = prove(
  `!x. &1 < x ==> &1 < (x pow 2)`,
  GEN_TAC THEN REWRITE_TAC[POW_2] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_MUL2_ALT THEN ASM_REWRITE_TAC[REAL_LE_01]);;

let POW_POS_LT = prove(
  `!x n. &0 < x ==> &0 < (x pow (SUC n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[];
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC POW_NZ THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN ASM_REWRITE_TAC[]]);;

let POW_2_LE1 = prove(
  `!n. &1 <= &2 pow n`,
  INDUCT_TAC THEN REWRITE_TAC[pow; REAL_LE_REFL] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2V THEN ASM_REWRITE_TAC[REAL_LE] THEN
  REWRITE_TAC[LE_0; num_CONV `2`; LESS_EQ_SUC_REFL]);;

let POW_2_LT = prove(
  `!n. &n < &2 pow n`,
  INDUCT_TAC THEN REWRITE_TAC[pow; REAL_LT_01] THEN
  REWRITE_TAC[ADD1; GSYM REAL_ADD; GSYM REAL_DOUBLE] THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[POW_2_LE1]);;

let POW_MINUS1 = prove(
  `!n. (--(&1)) pow (2 * n) = &1`,
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; pow] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; ADD_CLAUSES] THEN
  REWRITE_TAC[pow] THEN
  REWRITE_TAC[SYM(num_CONV `2`); SYM(num_CONV `1`)] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_NEGNEG]);;

(*----------------------------------------------------------------------------*)
(* Derive the supremum property for an arbitrary bounded nonempty set         *)
(*----------------------------------------------------------------------------*)

let REAL_SUP_EXISTS = prove(
  `!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) = y < s)`,
  GEN_TAC THEN MP_TAC(SPEC `P:real->bool` REAL_COMPLETE) THEN
  MESON_TAC[REAL_LT_IMP_LE; REAL_LTE_TRANS; REAL_NOT_LT]);;

let sup = new_definition(
  `sup P = @s. !y. (?x. P x /\ y < x) = y < s`);;

let REAL_SUP = prove(
  `!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. (?x. P x /\ y < x) = y < sup P)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o SELECT_RULE o MATCH_MP REAL_SUP_EXISTS)
  THEN REWRITE_TAC[GSYM sup]);;

let REAL_SUP_UBOUND = prove(
  `!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. P y ==> y <= sup P)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `sup P` o MATCH_MP REAL_SUP) THEN
  REWRITE_TAC[REAL_LT_REFL] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
  X_GEN_TAC `x:real` THEN RULE_ASSUM_TAC(SPEC `x:real`) THEN
  DISCH_THEN (SUBST_ALL_TAC o EQT_INTRO) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_NOT_LT]);;

let SETOK_LE_LT = prove(
  `!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) =
       (?x. P x) /\ (?z. !x. P x ==> x < z)`,
  GEN_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `z:real`)
  THENL (map EXISTS_TAC [`z + &1`; `z:real`]) THEN GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[REAL_LT_ADD1; REAL_LT_IMP_LE]);;

let REAL_SUP_LE = prove(
  `!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
           (!y. (?x. P x /\ y < x) = y < sup P)`,
  GEN_TAC THEN REWRITE_TAC[SETOK_LE_LT; REAL_SUP]);;

let REAL_SUP_UBOUND_LE = prove(
  `!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
          (!y. P y ==> y <= sup P)`,
  GEN_TAC THEN REWRITE_TAC[SETOK_LE_LT; REAL_SUP_UBOUND]);;

(*----------------------------------------------------------------------------*)
(* Prove the Archimedean property                                             *)
(*----------------------------------------------------------------------------*)

let REAL_ARCH = prove(
  `!x. &0 < x ==> !y. ?n. y < &n * x`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a = ~(~a)`] THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC `\z. ?n. z = &n * x` REAL_SUP_LE) THEN BETA_TAC THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o
       funpow 2 (fst o dest_imp) o snd)
  THENL [CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&n * x`; `n:num`] THEN REFL_TAC;
    EXISTS_TAC `y:real` THEN GEN_TAC THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `sup(\z. ?n. z = &n * x) - x`) THEN
  REWRITE_TAC[REAL_LT_SUB_RADD; REAL_LT_ADDR] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_RDISTRIB] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `sup(\z. ?n. z = &n * x)`) THEN
  REWRITE_TAC[REAL_LT_REFL] THEN EXISTS_TAC `(&n + &1) * x` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `n + 1` THEN
  REWRITE_TAC[REAL_ADD]);;

let REAL_ARCH_LEAST = prove(
  `!y. &0 < y ==> !x. &0 <= x ==>
                        ?n. (&n * y) <= x /\ x < (&(SUC n) * y)`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_ARCH) THEN
  GEN_TAC THEN POP_ASSUM(ASSUME_TAC o SPEC `x:real`) THEN
  POP_ASSUM(X_CHOOSE_THEN `n:num` MP_TAC o
        ONCE_REWRITE_RULE[num_WOP]) THEN
  REWRITE_TAC[REAL_NOT_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SPEC `PRE n`)) THEN
  DISCH_TAC THEN EXISTS_TAC `PRE n` THEN
  SUBGOAL_THEN `SUC(PRE n) = n` ASSUME_TAC THENL
   [DISJ_CASES_THEN2 SUBST_ALL_TAC (CHOOSE_THEN SUBST_ALL_TAC)
        (SPEC `n:num` num_CASES) THENL
     [UNDISCH_TAC `x < &0 * y` THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; GSYM REAL_NOT_LE];
      REWRITE_TAC[PRE]];
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[PRE; LESS_SUC_REFL]]);;

(*============================================================================*)
(* Topologies and metric spaces, including metric on real line                *)
(*============================================================================*)

parse_as_infix("re_union",(15,"right"));;
parse_as_infix("re_intersect",(17,"right"));;
parse_as_infix("re_subset",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Minimal amount of set notation is convenient                               *)
(*----------------------------------------------------------------------------*)

let re_Union = new_definition(
  `re_Union S = \x:A. ?s. S s /\ s x`);;

let re_union = new_definition(
  `P re_union Q = \x:A. P x \/ Q x`);;

let re_intersect = new_definition
  `P re_intersect Q = \x:A. P x /\ Q x`;;

let re_null = new_definition(
  `re_null = \x:A. F`);;

let re_universe = new_definition(
  `re_universe = \x:A. T`);;

let re_subset = new_definition(
  `P re_subset Q = !x:A. P x ==> Q x`);;

let re_compl = new_definition(
  `re_compl S = \x:A. ~(S x)`);;

let SUBSETA_REFL = prove(
  `!S:A->bool. S re_subset S`,
  GEN_TAC THEN REWRITE_TAC[re_subset]);;

let COMPL_MEM = prove(
  `!S:A->bool. !x. S x = ~(re_compl S x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[re_compl] THEN
  BETA_TAC THEN REWRITE_TAC[]);;

let SUBSETA_ANTISYM = prove(
  `!P:A->bool. !Q. P re_subset Q /\ Q re_subset P = (P = Q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[re_subset] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (b ==> a) = (a = b)`] THEN
  CONV_TAC(RAND_CONV FUN_EQ_CONV) THEN REFL_TAC);;

let SUBSETA_TRANS = prove(
  `!P:A->bool. !Q R. P re_subset Q /\ Q re_subset R ==> P re_subset R`,
  REPEAT GEN_TAC THEN REWRITE_TAC[re_subset] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  DISCH_THEN(MATCH_ACCEPT_TAC o GEN `x:A` o end_itlist IMP_TRANS o
    CONJUNCTS o SPEC `x:A`));;

(*----------------------------------------------------------------------------*)
(* Characterize an (A)topology                                                *)
(*----------------------------------------------------------------------------*)

let istopology = new_definition(
  `!L:(A->bool)->bool. istopology L =
            L re_null /\
            L re_universe /\
     (!a b. L a /\ L b ==> L (a re_intersect b)) /\
       (!P. P re_subset L ==> L (re_Union P))`);;

let topology_tybij = new_type_definition "topology" ("topology","open")
 (prove(`?t:(A->bool)->bool. istopology t`,
        EXISTS_TAC `re_universe:(A->bool)->bool` THEN
        REWRITE_TAC[istopology; re_universe]));;

let TOPOLOGY = prove(
  `!L:(A)topology. open(L) re_null /\
                   open(L) re_universe /\
            (!x y. open(L) x /\ open(L) y ==> open(L) (x re_intersect y)) /\
              (!P. P re_subset (open L) ==> open(L) (re_Union P))`,
  GEN_TAC THEN REWRITE_TAC[GSYM istopology] THEN
  REWRITE_TAC[topology_tybij]);;

let TOPOLOGY_UNION = prove(
  `!L:(A)topology. !P. P re_subset (open L) ==> open(L) (re_Union P)`,
  REWRITE_TAC[TOPOLOGY]);;

(*----------------------------------------------------------------------------*)
(* Characterize a neighbourhood of a point relative to a topology             *)
(*----------------------------------------------------------------------------*)

let neigh = new_definition(
  `neigh(top)(N,(x:A)) = ?P. open(top) P /\ P re_subset N /\ P x`);;

(*----------------------------------------------------------------------------*)
(* Prove various properties / characterizations of open sets                  *)
(*----------------------------------------------------------------------------*)

let OPEN_OWN_NEIGH = prove(
  `!S top. !x:A. open(top) S /\ S x ==> neigh(top)(S,x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[neigh] THEN
  EXISTS_TAC `S:A->bool` THEN ASM_REWRITE_TAC[SUBSETA_REFL]);;

let OPEN_UNOPEN = prove(
  `!S top. open(top) S =
           (re_Union (\P:A->bool. open(top) P /\ P re_subset S) = S)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM SUBSETA_ANTISYM] THEN
    REWRITE_TAC[re_Union; re_subset] THEN
    BETA_TAC THEN CONJ_TAC THEN GEN_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN EXISTS_TAC `S:A->bool` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC TOPOLOGY_UNION THEN
    REWRITE_TAC[re_subset] THEN BETA_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

let OPEN_SUBOPEN = prove(
  `!S top. open(top) S =
           !x:A. S x ==> ?P. P x /\ open(top) P /\ P re_subset S`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    EXISTS_TAC `S:A->bool` THEN ASM_REWRITE_TAC[SUBSETA_REFL];
    DISCH_TAC THEN C SUBGOAL_THEN SUBST1_TAC
     `S = re_Union (\P:A->bool. open(top) P /\ P re_subset S)` THENL
     [ONCE_REWRITE_TAC[GSYM SUBSETA_ANTISYM] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[re_subset] THEN REWRITE_TAC [re_Union] THEN
        BETA_TAC THEN GEN_TAC THEN
        DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
        DISCH_THEN(X_CHOOSE_TAC `P:A->bool`) THEN EXISTS_TAC `P:A->bool` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[re_subset; re_Union] THEN BETA_TAC THEN GEN_TAC THEN
        DISCH_THEN(CHOOSE_THEN STRIP_ASSUME_TAC) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC TOPOLOGY_UNION THEN ONCE_REWRITE_TAC[re_subset] THEN
      GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]]);;

let OPEN_NEIGH = prove(
  `!S top. open(top) S = !x:A. S x ==> ?N. neigh(top)(N,x) /\ N re_subset S`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `S:A->bool` THEN
    REWRITE_TAC[SUBSETA_REFL; neigh] THEN
    EXISTS_TAC `S:A->bool` THEN ASM_REWRITE_TAC[SUBSETA_REFL];
    DISCH_TAC THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN
    GEN_TAC THEN DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))
    THEN REWRITE_TAC[neigh] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `P:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSETA_TRANS THEN EXISTS_TAC `N:A->bool` THEN
    ASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* Characterize closed sets in a topological space                            *)
(*----------------------------------------------------------------------------*)

let closed = new_definition(
  `closed(L:(A)topology) S = open(L)(re_compl S)`);;

(*----------------------------------------------------------------------------*)
(* Define limit point in topological space                                    *)
(*----------------------------------------------------------------------------*)

let limpt = new_definition(
  `limpt(top) x S =
      !N:A->bool. neigh(top)(N,x) ==> ?y. ~(x = y) /\ S y /\ N y`);;

(*----------------------------------------------------------------------------*)
(* Prove that a set is closed iff it contains all its limit points            *)
(*----------------------------------------------------------------------------*)

let CLOSED_LIMPT = prove(
  `!top S. closed(top) S = (!x:A. limpt(top) x S ==> S x)`,
  REPEAT GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
  REWRITE_TAC[closed; limpt] THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  FREEZE_THEN (fun th -> ONCE_REWRITE_TAC[th])
    (SPEC `S:A->bool` COMPL_MEM) THEN
  REWRITE_TAC[] THEN
  SPEC_TAC(`re_compl(S:A->bool)`,`S:A->bool`) THEN
  GEN_TAC THEN REWRITE_TAC[NOT_IMP] THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  REWRITE_TAC[OPEN_NEIGH; re_subset] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `(S:A->bool) x` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TAUT `a \/ b \/ ~c = c ==> a \/ b`] THEN
  EQUAL_TAC THEN
  REWRITE_TAC[TAUT `(a = b \/ a) = b ==> a`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  POP_ASSUM ACCEPT_TAC);;

(*----------------------------------------------------------------------------*)
(* Characterize an (A)metric                                                  *)
(*----------------------------------------------------------------------------*)

let ismet = new_definition(
  `ismet (m:A#A->real) = (!x y. (m(x,y) = &0) = (x = y)) /\
                         (!x y z. m(y,z) <= m(x,y) + m(x,z))`);;

let metric_tybij = new_type_definition "metric" ("metric","mdist")
      (prove(`?m:(A#A->real). ismet m`,
        EXISTS_TAC `\((x:A),(y:A)). (x = y) => &0 | &1` THEN
        REWRITE_TAC[ismet] THEN
        CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
        CONJ_TAC THEN REPEAT GEN_TAC THENL
         [BOOL_CASES_TAC `x:A = y` THEN REWRITE_TAC[REAL_10];
          REPEAT LCOND_CASES_TAC THEN
          ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID; REAL_LE_REFL; REAL_LE_01]
          THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_LID] THEN
          TRY(MATCH_MP_TAC REAL_LE_ADD2) THEN
          REWRITE_TAC[REAL_LE_01; REAL_LE_REFL] THEN
          FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl) THEN
          EVERY_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]));;

(*----------------------------------------------------------------------------*)
(* Derive the metric properties                                               *)
(*----------------------------------------------------------------------------*)

let METRIC_ISMET = prove(
  `!m:(A)metric. ismet (mdist m)`,
  GEN_TAC THEN REWRITE_TAC[metric_tybij]);;

let METRIC_ZERO = prove(
  `!m:(A)metric. !x y. ((mdist m)(x,y) = &0) = (x = y)`,
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC `m:(A)metric` METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN ASM_REWRITE_TAC[]);;

let METRIC_SAME = prove(
  `!m:(A)metric. !x. (mdist m)(x,x) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[METRIC_ZERO]);;

let METRIC_POS = prove(
  `!m:(A)metric. !x y. &0 <= (mdist m)(x,y)`,
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC `m:(A)metric` METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`; `y:A`] o CONJUNCT2) THEN
  REWRITE_TAC[REWRITE_RULE[] (SPECL [`m:(A)metric`; `y:A`; `y:A`] METRIC_ZERO)]
  THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2 o W CONJ) THEN
  REWRITE_TAC[REAL_ADD_LID]);;

let METRIC_SYM = prove(
  `!m:(A)metric. !x y. (mdist m)(x,y) = (mdist m)(y,x)`,
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC `m:(A)metric` METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN FIRST_ASSUM
   (MP_TAC o GENL [`y:A`; `z:A`] o SPECL [`z:A`; `y:A`; `z:A`] o CONJUNCT2)
  THEN REWRITE_TAC[METRIC_SAME; REAL_ADD_RID] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM]);;

let METRIC_TRIANGLE = prove(
  `!m:(A)metric. !x y z. (mdist m)(x,z) <= (mdist m)(x,y) + (mdist m)(y,z)`,
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC `m:(A)metric` METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [METRIC_SYM] THEN
  ASM_REWRITE_TAC[]);;

let METRIC_NZ = prove(
  `!m:(A)metric. !x y. ~(x = y) ==> &0 < (mdist m)(x,y)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [`m:(A)metric`; `x:A`; `y:A`] METRIC_ZERO)) THEN
  ONCE_REWRITE_TAC[TAUT `~a ==> b = b \/ a`] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[GSYM REAL_LE_LT; METRIC_POS]);;

(*----------------------------------------------------------------------------*)
(* Now define metric topology and prove equivalent definition of `open`       *)
(*----------------------------------------------------------------------------*)

let mtop = new_definition(
  `!m:(A)metric. mtop m =
    topology(\S. !x. S x ==> ?e. &0 < e /\ (!y. (mdist m)(x,y) < e ==> S y))`);;

let mtop_istopology = prove(
  `!m:(A)metric. istopology
    (\S. !x. S x ==> ?e. &0 < e /\ (!y. (mdist m)(x,y) < e ==> S y))`,
  GEN_TAC THEN
  REWRITE_TAC[istopology; re_null; re_universe; re_Union;
              re_intersect; re_subset] THEN
  CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `&1` THEN MATCH_ACCEPT_TAC REAL_LT_01;
        REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    DISCH_THEN(fun th -> POP_ASSUM(CONJUNCTS_THEN(MP_TAC o SPEC `x:A`))
                    THEN REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_TAC `e1:real`) THEN
    DISCH_THEN(X_CHOOSE_TAC `e2:real`) THEN
    REPEAT_TCL DISJ_CASES_THEN MP_TAC
        (SPECL [`e1:real`; `e2:real`] REAL_LT_TOTAL) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC `e2:real` THEN
      ASM_REWRITE_TAC[] THEN GEN_TAC THEN
      DISCH_THEN(fun th -> EVERY_ASSUM(ASSUME_TAC o C MATCH_MP th o CONJUNCT2))
      THEN ASM_REWRITE_TAC[];
      DISCH_THEN(prefix THEN (EXISTS_TAC `e1:real`) o MP_TAC);
      DISCH_THEN(prefix THEN (EXISTS_TAC `e2:real`) o MP_TAC)] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th2 -> GEN_TAC THEN DISCH_THEN(fun th1 ->
      ASSUME_TAC th1 THEN ASSUME_TAC (MATCH_MP REAL_LT_TRANS (CONJ th1 th2))))
    THEN CONJ_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o CONJUNCT2)
    THEN FIRST_ASSUM ACCEPT_TAC;
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A->bool`
     (fun th -> POP_ASSUM(X_CHOOSE_TAC `e:real` o C MATCH_MP (CONJUNCT2 th) o
                     C MATCH_MP (CONJUNCT1 th)) THEN ASSUME_TAC th)) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A` THEN
    DISCH_THEN
      (fun th -> FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th o CONJUNCT2)) THEN
    EXISTS_TAC `y:A->bool` THEN ASM_REWRITE_TAC[]]);;

let MTOP_OPEN = prove(
  `!m:(A)metric. open(mtop m) S =
      (!x. S x ==> ?e. &0 < e /\ (!y. (mdist m(x,y)) < e ==> S y))`,
  GEN_TAC THEN REWRITE_TAC[mtop] THEN
  REWRITE_TAC[REWRITE_RULE[topology_tybij] mtop_istopology] THEN
  BETA_TAC THEN REFL_TAC);;

(*----------------------------------------------------------------------------*)
(* Define open ball in metric space + prove basic properties                  *)
(*----------------------------------------------------------------------------*)

let ball = new_definition(
  `!m:(A)metric. !x e. B(m)(x,e) = \y. (mdist m)(x,y) < e`);;

let BALL_OPEN = prove(
  `!m:(A)metric. !x e. &0 < e ==> open(mtop(m))(B(m)(x,e))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MTOP_OPEN] THEN
  X_GEN_TAC `z:A` THEN REWRITE_TAC[ball] THEN BETA_TAC THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  EXISTS_TAC `e - mdist(m:(A)metric)(x,z)` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[REAL_LT_SUB_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mdist(m)((x:A),z) + mdist(m)(z,y)` THEN
  ASM_REWRITE_TAC[METRIC_TRIANGLE]);;

let BALL_NEIGH = prove(
  `!m:(A)metric. !x e. &0 < e ==> neigh(mtop(m))(B(m)(x,e),x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[neigh] THEN EXISTS_TAC `B(m)((x:A),e)` THEN
  REWRITE_TAC[SUBSETA_REFL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BALL_OPEN;
    REWRITE_TAC[ball] THEN BETA_TAC THEN REWRITE_TAC[METRIC_SAME]] THEN
  POP_ASSUM ACCEPT_TAC);;

(*----------------------------------------------------------------------------*)
(* Characterize limit point in a metric topology                              *)
(*----------------------------------------------------------------------------*)

let MTOP_LIMPT = prove(
  `!m:(A)metric. !x S. limpt(mtop m) x S =
      !e. &0 < e ==> ?y. ~(x = y) /\ S y /\ (mdist m)(x,y) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[limpt] THEN EQ_TAC THENL
   [DISCH_THEN(prefix THEN (GEN_TAC THEN DISCH_TAC) o
      MP_TAC o SPEC `B(m)((x:A),e)`) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP BALL_NEIGH th]) THEN
    REWRITE_TAC[ball] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
    DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[neigh] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:A->bool`
      (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[MTOP_OPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(P:A->bool) re_subset N` THEN
    REWRITE_TAC[re_subset] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Define the usual metric on the real line                                   *)
(*----------------------------------------------------------------------------*)

let ISMET_R1 = prove(
  `ismet (\(x,y). abs(y - x))`,
  REWRITE_TAC[ismet] THEN CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ABS_ZERO; REAL_SUB_0] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN REFL_TAC;
    SUBST1_TAC(SYM(SPECL [`x:real`; `y:real`] REAL_NEG_SUB)) THEN
    REWRITE_TAC[ABS_NEG] THEN SUBGOAL_THEN `z - y = (x - y) + (z - x)`
      (fun th -> SUBST1_TAC th THEN MATCH_ACCEPT_TAC ABS_TRIANGLE) THEN
    REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC REAL_ADD_AC
      `(a + b) + (c + d) = (d + a) + (c + b)`] THEN
    REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID]]);;

let mr1 = new_definition(
  `mr1 = metric(\(x,y). abs(y - x))`);;

let MR1_DEF = prove(
  `!x y. (mdist mr1)(x,y) = abs(y - x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mr1; REWRITE_RULE[metric_tybij] ISMET_R1]
  THEN CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN REFL_TAC);;

let MR1_ADD = prove(
  `!x d. (mdist mr1)(x,x+d) = abs(d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF; REAL_ADD_SUB]);;

let MR1_SUB = prove(
  `!x d. (mdist mr1)(x,x-d) = abs(d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF; REAL_SUB_SUB; ABS_NEG]);;

let MR1_ADD_LE = prove(
  `!x d. &0 <= d ==> ((mdist mr1)(x,x+d) = d)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MR1_ADD; real_abs]);;

let MR1_SUB_LE = prove(
  `!x d. &0 <= d ==> ((mdist mr1)(x,x-d) = d)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MR1_SUB; real_abs]);;

let MR1_ADD_LT = prove(
  `!x d. &0 < d ==> ((mdist mr1)(x,x+d) = d)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MATCH_ACCEPT_TAC MR1_ADD_LE);;

let MR1_SUB_LT = prove(
  `!x d. &0 < d ==> ((mdist mr1)(x,x-d) = d)`,
   REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MATCH_ACCEPT_TAC MR1_SUB_LE);;

let MR1_BETWEEN1 = prove(
  `!x y z. x < z /\ (mdist mr1)(x,y) < (z - x) ==> y < z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF; ABS_BETWEEN1]);;

(*----------------------------------------------------------------------------*)
(* Every real is a limit point of the real line                               *)
(*----------------------------------------------------------------------------*)

let MR1_LIMPT = prove(
  `!x. limpt(mtop mr1) x re_universe`,
  GEN_TAC THEN REWRITE_TAC[MTOP_LIMPT; re_universe] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `x + (e / &2)` THEN
  REWRITE_TAC[MR1_ADD] THEN
  SUBGOAL_THEN `&0 <= (e / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1]; ALL_TAC] THEN
  ASM_REWRITE_TAC[real_abs; REAL_LT_HALF2] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_ADD_RID_UNIQ] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1]);;

(*============================================================================*)
(* Theory of Moore-Smith covergence nets, and special cases like sequences    *)
(*============================================================================*)

parse_as_infix ("tends",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Basic definitions: directed set, net, bounded net, pointwise limit         *)
(*----------------------------------------------------------------------------*)

let dorder = new_definition(
  `dorder (g:A->A->bool) =
     !x y. g x x /\ g y y ==> ?z. g z z /\ (!w. g w z ==> g w x /\ g w y)`);;

let tends = new_definition
  `(s tends l)(top,g) =
      !N:A->bool. neigh(top)(N,l) ==>
            ?n:B. g n n /\ !m:B. g m n ==> N(s m)`;;

let bounded = new_definition(
  `bounded((m:(A)metric),(g:B->B->bool)) f =
      ?k x N. g N N /\ (!n. g n N ==> (mdist m)(f(n),x) < k)`);;

let tendsto = new_definition(
  `tendsto((m:(A)metric),x) y z =
      &0 < (mdist m)(x,y) /\ (mdist m)(x,y) <= (mdist m)(x,z)`);;

parse_as_infix("-->",(12,"right"));;

override_interface ("-->",`(tends)`);;

let DORDER_LEMMA = prove(
  `!g:A->A->bool.
      dorder g ==>
        !P Q. (?n. g n n /\ (!m. g m n ==> P m)) /\
              (?n. g n n /\ (!m. g m n ==> Q m))
                  ==> (?n. g n n /\ (!m. g m n ==> P m /\ Q m))`,
  GEN_TAC THEN REWRITE_TAC[dorder] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `N1:A` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `N2:A` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`N1:A`; `N2:A`]) THEN
  REWRITE_TAC[ASSUME `(g:A->A->bool) N1 N1`;ASSUME `(g:A->A->bool) N2 N2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n:A` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:A` THEN DISCH_TAC THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o
    assert(is_conj o snd o dest_imp o snd o dest_forall) o concl) THEN
  DISCH_THEN(MP_TAC o SPEC `m:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Following tactic is useful in the following proofs                         *)
(*----------------------------------------------------------------------------*)

let DORDER_THEN tac th =
  let findpr = snd o dest_imp o body o rand o rand o body o rand in
  let [t1;t2] = map (rand o rand o body o rand) (conjuncts(concl th)) in
  let dog = (rator o rator o rand o rator o body) t1 in
  let thl = map ((uncurry X_BETA_CONV) o (I F_F rand) o dest_abs) [t1;t2] in
  let th1 = CONV_RULE(EXACT_CONV thl) th in
  let th2 = MATCH_MP DORDER_LEMMA (ASSUME (list_mk_icomb "dorder" [dog])) in
  let th3 = MATCH_MP th2 th1 in
  let th4 = CONV_RULE(EXACT_CONV(map SYM thl)) th3 in
  tac th4;;

(*----------------------------------------------------------------------------*)
(* Show that sequences and pointwise limits in a metric space are directed    *)
(*----------------------------------------------------------------------------*)

let DORDER_NGE = prove(
  `dorder ((>=) :num->num->bool)`,
  REWRITE_TAC[dorder; GE; LE_REFL] THEN
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(SPECL [`x:num`; `y:num`] LE_CASES) THENL
    [EXISTS_TAC `y:num`; EXISTS_TAC `x:num`] THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THENL
    [EXISTS_TAC `y:num`; EXISTS_TAC `x:num`] THEN
  ASM_REWRITE_TAC[]);;

let DORDER_TENDSTO = prove(
  `!m:(A)metric. !x. dorder(tendsto(m,x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dorder; tendsto] THEN
  MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC(SPECL [`(mdist m)((x:A),v)`; `(mdist m)((x:A),u)`]
    REAL_LE_TOTAL)
  THENL [EXISTS_TAC `v:A`; EXISTS_TAC `u:A`] THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN FIRST_ASSUM (fun th ->
   (EXISTS_TAC o rand o concl) th THEN ASM_REWRITE_TAC[] THEN NO_TAC));;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of limit in a metric topology                     *)
(*----------------------------------------------------------------------------*)

let MTOP_TENDS = prove(
  `!d g. !x:B->A. !x0. (x --> x0)(mtop(d),g) =
     !e. &0 < e ==> ?n. g n n /\ !m. g m n ==> mdist(d)(x(m),x0) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends] THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `B(d)((x0:A),e)`) THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (rand o rator) o snd) THENL
     [MATCH_MP_TAC BALL_NEIGH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[ball] THEN
    BETA_TAC THEN GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [METRIC_SYM] THEN REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[neigh] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:A->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `open(mtop(d)) (P:A->bool)` THEN
    REWRITE_TAC[MTOP_OPEN] THEN DISCH_THEN(MP_TAC o SPEC `x0:A`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `d:real`) THEN
    REWRITE_TAC[ASSUME `&0 < d`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `n:B` THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `(P:A->bool) re_subset N` THEN
    REWRITE_TAC[re_subset] THEN DISCH_TAC THEN
    REPEAT(FIRST_ASSUM MATCH_MP_TAC) THEN
    ONCE_REWRITE_TAC[METRIC_SYM] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Prove that a net in a metric topology cannot converge to different limits  *)
(*----------------------------------------------------------------------------*)

let MTOP_TENDS_UNIQ = prove(
  `!g d. dorder (g:B->B->bool) ==>
      (x --> x0)(mtop(d),g) /\ (x --> x1)(mtop(d),g) ==> (x0:A = x1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MTOP_TENDS] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) = a ==> b /\ c`] THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
  CONV_TAC NOT_FORALL_CONV THEN
  EXISTS_TAC `mdist(d:(A)metric)(x0,x1) / &2` THEN
  W(C SUBGOAL_THEN ASSUME_TAC o rand o rator o rand o snd) THENL
   [REWRITE_TAC[REAL_LT_HALF1] THEN MATCH_MP_TAC METRIC_NZ THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:B` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `N:B`) THEN ASM_REWRITE_TAC[] THEN
  BETA_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
  REWRITE_TAC[REAL_HALF_DOUBLE; REAL_NOT_LT] THEN
  GEN_REWRITE_TAC(RAND_CONV o LAND_CONV) [METRIC_SYM] THEN
  MATCH_ACCEPT_TAC METRIC_TRIANGLE);;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of limit of a sequence in a metric topology       *)
(*----------------------------------------------------------------------------*)

let SEQ_TENDS = prove(
  `!d:(A)metric. !x x0. (x --> x0)(mtop(d), (>=) :num->num->bool) =
     !e. &0 < e ==> ?N. !n. n >= N ==> mdist(d)(x(n),x0) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS; GE; LE_REFL]);;

(*----------------------------------------------------------------------------*)
(* And of limit of function between metric spaces                             *)
(*----------------------------------------------------------------------------*)

let LIM_TENDS = prove(
  `!m1:(A)metric. !m2:(B)metric. !f x0 y0.
      limpt(mtop m1) x0 re_universe ==>
        ((f --> y0)(mtop(m2),tendsto(m1,x0)) =
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (mdist m1)(x,x0) /\ (mdist m1)(x,x0) <= d
                ==> (mdist m2)(f(x),y0) < e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MTOP_TENDS; tendsto] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(mdist m1)((x0:A),z)` THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(ISPECL [`m1:(A)metric`; `x0:A`; `x:A`] METRIC_SYM) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `limpt(mtop m1) (x0:A) re_universe` THEN
    REWRITE_TAC[MTOP_LIMPT] THEN
    DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[re_universe] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:A` THEN CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_NZ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[METRIC_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(mdist m1)((x0:A),y)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Similar, more conventional version, is also true at a limit point          *)
(*----------------------------------------------------------------------------*)

let LIM_TENDS2 = prove(
  `!m1:(A)metric. !m2:(B)metric. !f x0 y0.
      limpt(mtop m1) x0 re_universe ==>
        ((f --> y0)(mtop(m2),tendsto(m1,x0)) =
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (mdist m1)(x,x0) /\ (mdist m1)(x,x0) < d ==>
              (mdist m2)(f(x),y0) < e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LIM_TENDS th]) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_LT_HALF2]]);;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of boundedness for the real line                  *)
(*----------------------------------------------------------------------------*)

let MR1_BOUNDED = prove(
  `!(g:A->A->bool) f. bounded(mr1,g) f =
        ?k N. g N N /\ (!n. g n N ==> abs(f n) < k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bounded; MR1_DEF] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV)
   [SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  CONV_TAC(REDEPTH_CONV EXISTS_AND_CONV) THEN
  AP_TERM_TAC THEN EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:real` MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_TAC `x:real`) THEN
    EXISTS_TAC `abs(x) + k` THEN GEN_TAC THEN DISCH_TAC THEN
    SUBST1_TAC(SYM(SPECL [`(f:A->real) n`; `x:real`] REAL_SUB_ADD)) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs((f:A->real) n - x) + abs(x)` THEN
    REWRITE_TAC[ABS_TRIANGLE] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN
    REWRITE_TAC[REAL_LT_RADD] THEN
    ONCE_REWRITE_TAC[ABS_SUB] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`k:real`; `&0`] THEN
    ASM_REWRITE_TAC[REAL_SUB_LZERO; ABS_NEG]]);;

(*----------------------------------------------------------------------------*)
(* Firstly, prove useful forms of null and bounded nets                       *)
(*----------------------------------------------------------------------------*)

let NET_NULL = prove(
  `!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) = ((\n. x(n) - x0) --> &0)(mtop(mr1),g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS] THEN BETA_TAC THEN
  REWRITE_TAC[MR1_DEF; REAL_SUB_LZERO] THEN EQUAL_TAC THEN
  REWRITE_TAC[REAL_NEG_SUB]);;

let NET_CONV_BOUNDED = prove(
  `!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) ==> bounded(mr1,g) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS; bounded] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN
  REWRITE_TAC[REAL_LT; num_CONV `1`; LT_0] THEN
  REWRITE_TAC[GSYM(num_CONV `1`)] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`&1`; `x0:real`; `N:A`] THEN
  ASM_REWRITE_TAC[]);;

let NET_CONV_NZ = prove(
  `!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        ?N. g N N /\ (!n. g n N ==> ~(x n = &0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS; bounded] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `abs(x0)`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN EXISTS_TAC `N:A` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MR1_DEF; REAL_SUB_RZERO; REAL_LT_REFL]);;

let NET_CONV_IBOUNDED = prove(
  `!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        bounded(mr1,g) (\n. inv(x n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS; MR1_BOUNDED; MR1_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[ABS_NZ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `abs(x0) / &2`) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`&2 / abs(x0)`; `N:A`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:A` THEN
  DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(abs(x0) / & 2) < abs(x(n:A))` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(SPECL [`abs(x0) / &2`; `abs(x0) / &2`; `abs(x(n:A))`]
      REAL_LT_LADD)) THEN
    REWRITE_TAC[REAL_HALF_DOUBLE] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(x0 - x(n:A)) + abs(x(n))` THEN
    ASM_REWRITE_TAC[REAL_LT_RADD] THEN
    SUBST1_TAC(SYM(AP_TERM `abs`
      (SPECL [`x0:real`; `x(n:A):real`] REAL_SUB_ADD))) THEN
    MATCH_ACCEPT_TAC ABS_TRIANGLE; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs(x(n:A))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `abs(x0) / &2` THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 / abs(x0) = inv(abs(x0) / &2)` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_RINV_UNIQ THEN REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
        `(a * b) * (c * d) = (d * a) * (b * c)`] THEN
    SUBGOAL_THEN `~(abs(x0) = &0) /\ ~(&2 = &0)`
      (fun th -> CONJUNCTS_THEN(SUBST1_TAC o MATCH_MP REAL_MUL_LINV) th
            THEN REWRITE_TAC[REAL_MUL_LID]) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[ABS_NZ; ABS_ABS];
      REWRITE_TAC[REAL_INJ; num_CONV `2`; NOT_SUC]]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x(n:A) = &0)` (SUBST1_TAC o MATCH_MP ABS_INV) THENL
   [ASM_REWRITE_TAC[ABS_NZ]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_HALF1]);;

(*----------------------------------------------------------------------------*)
(* Now combining theorems for null nets                                       *)
(*----------------------------------------------------------------------------*)

let NET_NULL_ADD = prove(
  `!g:A->A->bool. dorder g ==>
        !x y. (x --> &0)(mtop(mr1),g) /\ (y --> &0)(mtop(mr1),g) ==>
                ((\n. x(n) + y(n)) --> &0)(mtop(mr1),g)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MTOP_TENDS; MR1_DEF; REAL_SUB_LZERO; ABS_NEG] THEN
  DISCH_THEN(prefix THEN (X_GEN_TAC `e:real` THEN DISCH_TAC) o
    MP_TAC o end_itlist CONJ o map (SPEC `e / &2`) o CONJUNCTS) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(DORDER_THEN (X_CHOOSE_THEN `N:A` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `N:A` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(x(m:A)) + abs(y(m:A))` THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN RULE_ASSUM_TAC BETA_RULE THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]);;

let NET_NULL_MUL = prove(
  `!g:A->A->bool. dorder g ==>
      !x y. bounded(mr1,g) x /\ (y --> &0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) --> &0)(mtop(mr1),g)`,
  GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_BOUNDED] THEN
  REWRITE_TAC[MTOP_TENDS; MR1_DEF; REAL_SUB_LZERO; ABS_NEG] THEN
  DISCH_THEN(prefix THEN (X_GEN_TAC `e:real` THEN DISCH_TAC) o MP_TAC) THEN
  CONV_TAC(LAND_CONV LEFT_AND_EXISTS_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o uncurry CONJ o (I F_F SPEC `e / k`) o CONJ_PAIR) THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `N:A`
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPEC `N:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(x(N:A))` THEN ASM_REWRITE_TAC[ABS_POS]; ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  SUBGOAL_THEN `&0 < e / k` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_LT_RDIV_0 th] THEN
    ASM_REWRITE_TAC[] THEN NO_TAC); ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DORDER_THEN(X_CHOOSE_THEN `N:A` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `N:A` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN (ASSUME_TAC o BETA_RULE)) THEN
  SUBGOAL_THEN `e = k * (e / k)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&0 < &0` THEN
    REWRITE_TAC[REAL_LT_REFL]; ALL_TAC] THEN BETA_TAC THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2_ALT THEN
  ASM_REWRITE_TAC[ABS_POS]);;

let NET_NULL_CMUL = prove(
  `!g:A->A->bool. !k x.
      (x --> &0)(mtop(mr1),g) ==> ((\n. k * x(n)) --> &0)(mtop(mr1),g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS; MR1_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_LZERO; ABS_NEG] THEN
  DISCH_THEN(prefix THEN (X_GEN_TAC `e:real` THEN DISCH_TAC) o MP_TAC) THEN
  ASM_CASES_TAC `k = &0` THENL
   [DISCH_THEN(MP_TAC o SPEC `&1`) THEN
    REWRITE_TAC[REAL_LT; num_CONV `1`; LESS_SUC_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:A` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; real_abs; REAL_LE_REFL];
    DISCH_THEN(MP_TAC o SPEC `e / abs(k)`) THEN
    SUBGOAL_THEN `&0 < e / abs(k)` ASSUME_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_POS THEN
      ASM_REWRITE_TAC[GSYM ABS_NZ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:A` THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `e = abs(k) * (e / abs(k))` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
      ASM_REWRITE_TAC[ABS_ZERO]; ALL_TAC] THEN
    REWRITE_TAC[ABS_MUL] THEN
    SUBGOAL_THEN `&0 < abs k` (fun th -> REWRITE_TAC[MATCH_MP REAL_LT_LMUL_EQ th])
    THEN ASM_REWRITE_TAC[GSYM ABS_NZ]]);;

(*----------------------------------------------------------------------------*)
(* Now real arithmetic theorems for convergent nets                           *)
(*----------------------------------------------------------------------------*)

let NET_ADD = prove(
  `!g:A->A->bool. dorder g ==>
      !x x0 y y0. (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g) ==>
                      ((\n. x(n) + y(n)) --> (x0 + y0))(mtop(mr1),g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[NET_NULL] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM
    (MP_TAC o C MATCH_MP th o MATCH_MP NET_NULL_ADD))
  THEN MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN EQUAL_TAC THEN
  BETA_TAC THEN REWRITE_TAC[real_sub; REAL_NEG_ADD] THEN
  REWRITE_TAC[REAL_ADD_AC]);;

let NET_NEG = prove(
  `!g:A->A->bool. dorder g ==>
        (!x x0. (x --> x0)(mtop(mr1),g) =
                  ((\n. --(x n)) --> --x0)(mtop(mr1),g))`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MTOP_TENDS; MR1_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_NEG2] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB] THEN
  REFL_TAC);;

let NET_SUB = prove(
  `!g:A->A->bool. dorder g ==>
      !x x0 y y0. (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g) ==>
                      ((\n. x(n) - y(n)) --> (x0 - y0))(mtop(mr1),g)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_sub] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV `n:A` `--(y(n:A))`]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP NET_NEG th)]) THEN
  ASM_REWRITE_TAC[]);;

let NET_MUL = prove(
  `!g:A->A->bool. dorder g ==>
        !x y x0 y0. (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) --> (x0 * y0))(mtop(mr1),g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[NET_NULL] THEN
  DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `!a b c d. (a * b) - (c * d) = (a * (b - d)) + ((a - c) * d)`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[real_sub; REAL_LDISTRIB; REAL_RDISTRIB; GSYM REAL_ADD_ASSOC]
    THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID]; ALL_TAC] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV `n:A` `x(n:A) * (y(n) - y0)`]) THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV `n:A` `(x(n:A) - x0) * y0`]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_NULL_ADD) THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  (CONV_TAC o EXACT_CONV o map (X_BETA_CONV `n:A`))
   [`y(n:A) - y0`; `x(n:A) - x0`] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_NULL_MUL) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NET_CONV_BOUNDED THEN
    EXISTS_TAC `x0:real` THEN ONCE_REWRITE_TAC[NET_NULL] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC NET_NULL_CMUL THEN ASM_REWRITE_TAC[]]);;

let NET_INV = prove(
  `!g:A->A->bool. dorder g ==>
        !x x0. (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
                   ((\n. inv(x(n))) --> inv x0)(mtop(mr1),g)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC(CONJ (MATCH_MP NET_CONV_IBOUNDED th)
                    (MATCH_MP NET_CONV_NZ th))) THEN
  REWRITE_TAC[MR1_BOUNDED] THEN
  CONV_TAC(ONCE_DEPTH_CONV LEFT_AND_EXISTS_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` MP_TAC) THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o C CONJ
   (ASSUME `(x --> x0)(mtop mr1,(g:A->A->bool))`)) THEN
  ONCE_REWRITE_TAC[NET_NULL] THEN
  REWRITE_TAC[MTOP_TENDS; MR1_DEF; REAL_SUB_LZERO; ABS_NEG] THEN BETA_TAC
  THEN DISCH_THEN(prefix THEN
   (X_GEN_TAC `e:real` THEN DISCH_TAC) o MP_TAC) THEN
  ONCE_REWRITE_TAC[RIGHT_AND_FORALL_THM] THEN
  DISCH_THEN(ASSUME_TAC o SPEC `e * abs(x0) * (inv k)`) THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPEC `N:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(inv(x(N:A)))` THEN
    ASM_REWRITE_TAC[ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e * abs(x0) * inv k` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[GSYM ABS_NZ] THEN
    MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A` (CONJUNCTS_THEN ASSUME_TAC)) THEN
  EXISTS_TAC `N:A` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:A` THEN DISCH_THEN(ANTE_RES_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC BETA_RULE THEN POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `inv(x n) - inv x0 =
                inv(x n) * inv x0 * (x0 - x(n:A))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME `~(x0 = &0)`)] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN REPEAT AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_RINV (ASSUME `~(x(n:A) = &0)`)] THEN
    REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  REWRITE_TAC[ABS_MUL] THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  SUBGOAL_THEN `e = e * (abs(inv x0) * abs(x0)) * (inv k * k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM ABS_MUL] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME `~(x0 = &0)`)] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV
      (GSYM(MATCH_MP REAL_LT_IMP_NE (ASSUME `&0 < k`)))] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    REWRITE_TAC[real_abs; REAL_LE; LE_LT; num_CONV `1`; LESS_SUC_REFL] THEN
    REWRITE_TAC[SYM(num_CONV `1`); REAL_MUL_RID]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
    `a * (b * c) * (d * e) = e * b * (a * c * d)`] THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  MATCH_MP_TAC ABS_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ABS_MUL] THEN SUBGOAL_THEN `&0 < abs(inv x0)`
    (fun th -> ASM_REWRITE_TAC[MATCH_MP REAL_LT_LMUL_EQ th]) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  MATCH_MP_TAC REAL_INV_NZ THEN ASM_REWRITE_TAC[]);;

let NET_DIV = prove(
  `!g:A->A->bool. dorder g ==>
      !x x0 y y0. (x --> x0)(mtop(mr1),g) /\
                  (y --> y0)(mtop(mr1),g) /\ ~(y0 = &0) ==>
                      ((\n. x(n) / y(n)) --> (x0 / y0))(mtop(mr1),g)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV `n:A` `inv(y(n:A))`]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_INV) THEN
  ASM_REWRITE_TAC[]);;

let NET_ABS = prove(
  `!x x0. (x --> x0)(mtop(mr1),g) ==>
               ((\n:A. abs(x n)) --> abs(x0))(mtop(mr1),g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(fun th -> POP_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:A` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:A` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mdist(mr1)(x(n:A),x0)` THEN CONJ_TAC THENL
   [REWRITE_TAC[MR1_DEF; ABS_SUB_ABS];
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Comparison between limits                                                  *)
(*----------------------------------------------------------------------------*)

let NET_LE = prove(
  `!g:A->A->bool. dorder g ==>
      !x x0 y y0. (x --> x0)(mtop(mr1),g) /\
                  (y --> y0)(mtop(mr1),g) /\
                  (?N. g N N /\ !n. g n N ==> x(n) <= y(n))
                        ==> x0 <= y0`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[MTOP_TENDS] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o
    map (SPEC `(x0 - y0) / &2`) o CONJUNCTS) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_exists o concl) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN (fun th2 -> MP_TAC(CONJ th1 th2))) THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  BETA_TAC THEN DISCH_THEN(MP_TAC o SPEC `N:A`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MR1_DEF] THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC ABS_BETWEEN2 THEN
  MAP_EVERY EXISTS_TAC [`y0:real`; `x0:real`] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM ACCEPT_TAC);;

(*============================================================================*)
(* Theory of sequences and series of real numbers                             *)
(*============================================================================*)

parse_as_infix ("tends_num_real",(12,"right"));;

parse_as_infix ("sums",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Specialize net theorems to sequences:num->real                             *)
(*----------------------------------------------------------------------------*)

let tends_num_real = new_definition(
  `x tends_num_real x0 = (x tends x0)(mtop(mr1), (>=) :num->num->bool)`);;

override_interface ("-->",`(tends_num_real)`);;

let SEQ = prove(
  `!x x0. (x --> x0) =
          !e. &0 < e ==> ?N. !n. n >= N ==> abs(x(n) - x0) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real; SEQ_TENDS; MR1_DEF] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB] THEN
  REFL_TAC);;

let SEQ_CONST = prove(
  `!k. (\x. k) --> k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEQ; REAL_SUB_REFL; ABS_0] THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let SEQ_ADD = prove(
  `!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) + y(n)) --> (x0 + y0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_ADD THEN
  MATCH_ACCEPT_TAC DORDER_NGE);;

let SEQ_MUL = prove(
  `!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) * y(n)) --> (x0 * y0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_MUL THEN
  MATCH_ACCEPT_TAC DORDER_NGE);;

let SEQ_NEG = prove(
  `!x x0. x --> x0 = (\n. --(x n)) --> --x0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_NEG THEN
  MATCH_ACCEPT_TAC DORDER_NGE);;

let SEQ_INV = prove(
  `!x x0. x --> x0 /\ ~(x0 = &0) ==> (\n. inv(x n)) --> inv x0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_INV THEN
  MATCH_ACCEPT_TAC DORDER_NGE);;

let SEQ_SUB = prove(
  `!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) - y(n)) --> (x0 - y0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_SUB THEN
  MATCH_ACCEPT_TAC DORDER_NGE);;

let SEQ_DIV = prove(
  `!x x0 y y0. x --> x0 /\ y --> y0 /\ ~(y0 = &0) ==>
                  (\n. x(n) / y(n)) --> (x0 / y0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_DIV THEN
  MATCH_ACCEPT_TAC DORDER_NGE);;

let SEQ_UNIQ = prove(
  `!x x1 x2. x --> x1 /\ x --> x2 ==> (x1 = x2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC MTOP_TENDS_UNIQ THEN
  MATCH_ACCEPT_TAC DORDER_NGE);;

(*----------------------------------------------------------------------------*)
(* Define convergence and Cauchy-ness                                         *)
(*----------------------------------------------------------------------------*)

let convergent = new_definition(
  `convergent f = ?l. f --> l`);;

let cauchy = new_definition(
  `cauchy f = !e. &0 < e ==>
        ?N:num. !m n. m >= N /\ n >= N ==> abs(f(m) - f(n)) < e`);;

let lim = new_definition(
  `lim f = @l. f --> l`);;

let SEQ_LIM = prove(
  `!f. convergent f = (f --> lim f)`,
  GEN_TAC THEN REWRITE_TAC[convergent] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[lim];
    DISCH_TAC THEN EXISTS_TAC `lim f` THEN POP_ASSUM ACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Define a subsequence                                                       *)
(*----------------------------------------------------------------------------*)

let subseq = new_definition(
  `subseq (f:num->num) = !m n. m < n ==> (f m) < (f n)`);;

let SUBSEQ_SUC = prove(
  `!f. subseq f = !n. f(n) < f(SUC n)`,
  GEN_TAC THEN REWRITE_TAC[subseq] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `n:num` THEN POP_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LESS_SUC_REFL];
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC[GSYM ADD1] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
    SPEC_TAC(`p:num`,`p:num`) THEN INDUCT_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `f(m + (SUC p)):num`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES]]);;

(*----------------------------------------------------------------------------*)
(* Define monotonicity                                                        *)
(*----------------------------------------------------------------------------*)

let mono = new_definition(
  `mono (f:num->real) =
            (!m n. m <= n ==> f(m) <= f(n)) \/
            (!m n. m <= n ==> f(m) >= f(n))`);;

let MONO_SUC = prove(
  `!f. mono f = (!n. f(SUC n) >= f(n)) \/ (!n. f(SUC n) <= f(n))`,
  GEN_TAC THEN REWRITE_TAC[mono; real_ge] THEN
  MATCH_MP_TAC(TAUT `(a = c) /\ (b = d) ==> (a \/ b = c \/ d)`) THEN
  CONJ_TAC THEN (EQ_TAC THENL
    [DISCH_THEN(MP_TAC o GEN `n:num` o SPECL [`n:num`; `SUC n`]) THEN
     REWRITE_TAC[LESS_EQ_SUC_REFL];
     DISCH_TAC THEN REPEAT GEN_TAC THEN
     DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD) THEN
     SPEC_TAC(`p:num`,`p:num`) THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `f(m + p:num):real` THEN
     ASM_REWRITE_TAC[]]));;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of bounded sequence                               *)
(*----------------------------------------------------------------------------*)

let MAX_LEMMA = prove(
  `!s N. ?k. !n:num. n < N ==> abs(s n) < k`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0] THEN
  POP_ASSUM(X_CHOOSE_TAC `k:real`) THEN
  DISJ_CASES_TAC (SPECL [`k:real`; `abs(s(N:num))`] REAL_LET_TOTAL) THENL
   [EXISTS_TAC `abs(s(N:num)) + &1`; EXISTS_TAC `k:real`] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[CONJUNCT2 LT] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
  TRY(MATCH_MP_TAC REAL_LT_ADD1) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LT_ADD1 THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k:real` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  ASM_REWRITE_TAC[]);;

let SEQ_BOUNDED = prove(
  `!s. bounded(mr1, (>=)) s = ?k. !n:num. abs(s n) < k`,
  GEN_TAC THEN REWRITE_TAC[MR1_BOUNDED] THEN
  REWRITE_TAC[GE; LE_REFL] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `k:real` (X_CHOOSE_TAC `N:num`)) THEN
    MP_TAC(SPECL [`s:num->real`; `N:num`] MAX_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
    DISJ_CASES_TAC (SPECL [`k:real`; `l:real`] REAL_LE_TOTAL) THENL
     [EXISTS_TAC `l:real`; EXISTS_TAC `k:real`] THEN
    X_GEN_TAC `n:num` THEN MP_TAC(SPECL [`n:num`; `N:num`] LTE_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN(ANTE_RES_THEN ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC);
    DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
    MAP_EVERY EXISTS_TAC [`k:real`; `0`] THEN
    GEN_TAC THEN ASM_REWRITE_TAC[]]);;

let SEQ_BOUNDED_2 = prove(
  `!f k K. (!n:num. k <= f(n) /\ f(n) <= K) ==> bounded(mr1, (>=)) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SEQ_BOUNDED] THEN
  EXISTS_TAC `(abs(k) + abs(K)) + &1` THEN GEN_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(k) + abs(K)` THEN
  REWRITE_TAC[REAL_LT_ADDR; REAL_LT_01] THEN
  GEN_REWRITE_TAC LAND_CONV [real_abs] THEN LCOND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(K)` THEN
    REWRITE_TAC[REAL_LE_ADDL; ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[ABS_LE];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(k)` THEN
    REWRITE_TAC[REAL_LE_ADDR; ABS_POS] THEN
    REWRITE_TAC[real_abs] THEN
    LCOND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_NEG] THEN
    SUBGOAL_THEN `&0 <= f(n:num)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

(*----------------------------------------------------------------------------*)
(* Show that every Cauchy sequence is bounded                                 *)
(*----------------------------------------------------------------------------*)

let SEQ_CBOUNDED = prove(
  `!f. cauchy f ==> bounded(mr1, (>=)) f`,
  GEN_TAC THEN REWRITE_TAC[bounded; cauchy] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MAP_EVERY EXISTS_TAC [`&1`; `(f:num->real) N`; `N:num`] THEN
  REWRITE_TAC[GE; LE_REFL] THEN
  POP_ASSUM(MP_TAC o SPEC `N:num`) THEN
  REWRITE_TAC[GE; LE_REFL; MR1_DEF]);;

(*----------------------------------------------------------------------------*)
(* Show that a bounded and monotonic sequence converges                       *)
(*----------------------------------------------------------------------------*)

let SEQ_ICONV = prove(
  `!f. bounded(mr1, (>=)) f /\ (!m n. m >= n ==> f(m) >= f(n))
           ==> convergent f`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPEC `\x:real. ?n:num. x = f(n)` REAL_SUP) THEN BETA_TAC THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`f(0):real`; `0`] THEN REFL_TAC;
      POP_ASSUM(MP_TAC o REWRITE_RULE[SEQ_BOUNDED] o CONJUNCT1) THEN
      DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN EXISTS_TAC `k:real` THEN
      GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(f(n:num))` THEN
      ASM_REWRITE_TAC[ABS_LE]]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  REWRITE_TAC[convergent] THEN EXISTS_TAC `sup(\x. ?n:num. x = f(n))` THEN
  REWRITE_TAC[SEQ] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o assert(is_forall o concl)) THEN
  DISCH_THEN(MP_TAC o SPEC `sup(\x. ?n:num. x = f(n)) - e`) THEN
  REWRITE_TAC[REAL_LT_SUB_RADD; REAL_LT_ADDR] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` MP_TAC) THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[GSYM REAL_LT_SUB_RADD] THEN
  DISCH_TAC THEN SUBGOAL_THEN `!n. f(n) <= sup(\x. ?n:num. x = f(n))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `sup(\x. ?n:num. x = f(n))`) THEN
    REWRITE_TAC[REAL_LT_REFL] THEN
    CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
    REWRITE_TAC[TAUT `~(a /\ b) = a ==> ~b`] THEN
    REWRITE_TAC[REAL_NOT_LT] THEN
    CONV_TAC(ONCE_DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
    DISCH_THEN(MP_TAC o GEN `n:num` o SPECL [`(f:num->real) n`; `n:num`]) THEN
    REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_LT_SUB_RADD]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[REAL_ADD_SYM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_LT_SUB_RADD]) THEN
  REWRITE_TAC[real_ge] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(sup(\x. ?m:num. x = f(m)) - e) < f(m)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(f:num->real) n` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_abs] THEN LCOND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_NEG_SUB] THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&0` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_sub] THEN
    (SUBST1_TAC o REWRITE_RULE[REAL_ADD_RINV] o C SPECL REAL_LE_RADD)
      [`(f:num->real) m`; `(sup(\x. ?n:num. x = f(n)))`;
       `--(sup(\x. ?n:num. x = f(n)))`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_LT_SUB_RADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    REWRITE_TAC[GSYM REAL_LT_SUB_RADD] THEN ASM_REWRITE_TAC[]]);;

let SEQ_NEG_CONV = prove(
  `!f. convergent f = convergent (\n. --(f n))`,
  GEN_TAC THEN REWRITE_TAC[convergent] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
  EXISTS_TAC `--l` THEN POP_ASSUM MP_TAC THEN
  SUBST1_TAC(SYM(SPEC `l:real` REAL_NEGNEG)) THEN
  REWRITE_TAC[GSYM SEQ_NEG] THEN REWRITE_TAC[REAL_NEGNEG]);;

let SEQ_NEG_BOUNDED = prove(
  `!f. bounded(mr1, (>=))(\n:num. --(f n)) = bounded(mr1, (>=)) f`,
  GEN_TAC THEN REWRITE_TAC[SEQ_BOUNDED] THEN BETA_TAC THEN
  REWRITE_TAC[ABS_NEG]);;

let SEQ_BCONV = prove(
  `!f. bounded(mr1, (>=)) f /\ mono f ==> convergent f`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[mono] THEN DISCH_THEN DISJ_CASES_TAC THENL
   [MATCH_MP_TAC SEQ_ICONV THEN ASM_REWRITE_TAC[GE; real_ge];
    ONCE_REWRITE_TAC[SEQ_NEG_CONV] THEN MATCH_MP_TAC SEQ_ICONV THEN
    ASM_REWRITE_TAC[SEQ_NEG_BOUNDED] THEN BETA_TAC THEN
    REWRITE_TAC[GE; real_ge; REAL_LE_NEG] THEN
    ONCE_REWRITE_TAC[GSYM real_ge] THEN ASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* Show that every sequence contains a monotonic subsequence                  *)
(*----------------------------------------------------------------------------*)

let SEQ_MONOSUB = prove(
  `!s:num->real. ?f. subseq f /\ mono(\n.s(f n))`,
  GEN_TAC THEN
  ASM_CASES_TAC `!n:num. ?p. p > n /\ !m. m >= p ==> s(m) <= s(p)` THENL
   [(X_CHOOSE_THEN `f:num->num` MP_TAC o EXISTENCE o C ISPECL num_Axiom)
     [`@p. p > 0 /\ (!m. m >= p ==> (s m) <= (s p))`;
      `\x. \n:num. @p:num. p > x /\
                       (!m. m >= p ==> (s m) <= (s p))`] THEN
    BETA_TAC THEN RULE_ASSUM_TAC(GEN `n:num` o SELECT_RULE o SPEC `n:num`) THEN
    POP_ASSUM(fun th -> DISCH_THEN(ASSUME_TAC o GSYM) THEN
    MP_TAC(SPEC `0` th) THEN
    MP_TAC(GEN `n:num` (SPEC `(f:num->num) n` th))) THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `f:num->num` THEN ASM_REWRITE_TAC[SUBSEQ_SUC; GSYM GT] THEN
    SUBGOAL_THEN `!p q. p:num >= (f q) ==> s(p) <= s(f(q:num))` MP_TAC THENL
     [REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `q:num` num_CASES) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o GEN `q:num` o SPECL [`f(SUC q):num`; `q:num`]) THEN
    SUBGOAL_THEN `!q. f(SUC q):num >= f(q)` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[GE] THEN
      MATCH_MP_TAC LT_IMP_LE
      THEN ASM_REWRITE_TAC[GSYM GT]; ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[MONO_SUC] THEN DISJ2_TAC THEN
    BETA_TAC THEN ASM_REWRITE_TAC[];
    POP_ASSUM(X_CHOOSE_TAC `N:num` o CONV_RULE NOT_FORALL_CONV) THEN
    POP_ASSUM(MP_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
    REWRITE_TAC[TAUT `~(a /\ b) = a ==> ~b`] THEN
    CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
    REWRITE_TAC[NOT_IMP; REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `!p. p >= SUC N ==> (?m. m > p /\ s(p) < s(m))`
    MP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[GE; LE_SUC_LT] THEN
      REWRITE_TAC[GSYM GT] THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      REWRITE_TAC[GE; LE_LT; RIGHT_AND_OVER_OR; GT] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:num` DISJ_CASES_TAC) THENL
       [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[REAL_LT_REFL]]; ALL_TAC] THEN
    POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
    (X_CHOOSE_THEN `f:num->num` MP_TAC o EXISTENCE o C ISPECL num_Axiom)
     [`@m. m > (SUC N) /\ s(SUC N) < s(m)`;
      `\x. \n:num. @m:num. m > x /\ s(x) < s(m)`] THEN
    BETA_TAC THEN DISCH_THEN ASSUME_TAC THEN SUBGOAL_THEN
      `!n. f(n) >= (SUC N) /\
           f(SUC n) > f(n) /\ s(f n) < s(f(SUC n):num)` MP_TAC THENL
     [INDUCT_TAC THENL
       [SUBGOAL_THEN `f(0) >= (SUC N)` MP_TAC THENL
         [FIRST_ASSUM(MP_TAC o SPEC `SUC N`) THEN
          REWRITE_TAC[GE; LE_REFL] THEN
          DISCH_THEN(MP_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
          MATCH_MP_TAC LT_IMP_LE THEN
          ASM_REWRITE_TAC[GSYM GT]; ALL_TAC] THEN
        DISCH_THEN(fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
        CONV_TAC SELECT_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM(UNDISCH_TAC o
          assert(prefix=3 o length o conjuncts) o concl) THEN
        DISCH_THEN STRIP_ASSUME_TAC THEN CONJ_TAC THENL
         [REWRITE_TAC[GE] THEN MATCH_MP_TAC LE_TRANS THEN
          EXISTS_TAC `(f:num->num) n` THEN REWRITE_TAC[GSYM GE] THEN
          CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
          REWRITE_TAC[GE] THEN MATCH_MP_TAC LT_IMP_LE THEN
          REWRITE_TAC[GSYM GT] THEN FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM(SUBST1_TAC o SPEC `SUC n` o CONJUNCT2) THEN
          CONV_TAC SELECT_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[GE] THEN MATCH_MP_TAC LE_TRANS THEN
          EXISTS_TAC `(f:num->num) n` THEN
          REWRITE_TAC[GSYM GE] THEN CONJ_TAC THEN
          TRY(FIRST_ASSUM ACCEPT_TAC) THEN
          REWRITE_TAC[GE] THEN MATCH_MP_TAC LT_IMP_LE THEN
          REWRITE_TAC[GSYM GT] THEN
          FIRST_ASSUM ACCEPT_TAC]]; ALL_TAC] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    EXISTS_TAC `f:num->num` THEN REWRITE_TAC[SUBSEQ_SUC; MONO_SUC] THEN
    ASM_REWRITE_TAC[GSYM GT] THEN DISJ1_TAC THEN BETA_TAC THEN
    GEN_TAC THEN REWRITE_TAC[real_ge] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* Show that a subsequence of a bounded sequence is bounded                   *)
(*----------------------------------------------------------------------------*)

let SEQ_SBOUNDED = prove(
  `!s (f:num->num). bounded(mr1, (>=)) s ==> bounded(mr1, (>=)) (\n. s(f n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEQ_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN EXISTS_TAC `k:real` THEN
  GEN_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Show we can take subsequential terms arbitrarily far up a sequence         *)
(*----------------------------------------------------------------------------*)

let SEQ_SUBLE = prove(
  `!f. subseq f ==> !n. n <= f(n)`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT; NOT_LESS_0];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `SUC(f(n:num))` THEN
    ASM_REWRITE_TAC[LE_SUC] THEN
    REWRITE_TAC[LE_SUC_LT] THEN
    UNDISCH_TAC `subseq f` THEN REWRITE_TAC[SUBSEQ_SUC] THEN
    DISCH_THEN MATCH_ACCEPT_TAC]);;

let SEQ_DIRECT = prove(
  `!f. subseq f ==> !N1 N2. ?n. n >= N1 /\ f(n) >= N2`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (SPECL [`N1:num`; `N2:num`] LE_CASES) THENL
   [EXISTS_TAC `N2:num` THEN ASM_REWRITE_TAC[GE] THEN
    MATCH_MP_TAC SEQ_SUBLE THEN
    FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC `N1:num` THEN REWRITE_TAC[GE; LE_REFL] THEN
    REWRITE_TAC[GE] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `N1:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SEQ_SUBLE THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Now show that every Cauchy sequence converges                              *)
(*----------------------------------------------------------------------------*)

let SEQ_CAUCHY = prove(
  `!f. cauchy f = convergent f`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEQ_CBOUNDED) THEN
    MP_TAC(SPEC `f:num->real` SEQ_MONOSUB) THEN
    DISCH_THEN(X_CHOOSE_THEN `g:num->num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `bounded(mr1, (>=) :num->num->bool)(\n. f(g(n):num))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SEQ_SBOUNDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `convergent (\n. f(g(n):num))` MP_TAC THENL
     [MATCH_MP_TAC SEQ_BCONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[convergent] THEN DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
    EXISTS_TAC `l:real` THEN REWRITE_TAC[SEQ] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(\n. f(g(n):num)) --> l` THEN REWRITE_TAC[SEQ] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    UNDISCH_TAC `cauchy f` THEN REWRITE_TAC[cauchy] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP SEQ_DIRECT) THEN
    DISCH_THEN(MP_TAC o SPECL [`N1:num`; `N2:num`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N2:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `!n:num. n >= N1 ==> abs(f(g n:num) - l) < (e / &2)` THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [`g(n:num):num`; `m:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    SUBGOAL_THEN `f(m:num) - l = (f(m) - f(g(n:num))) + (f(g n) - l)`
    SUBST1_TAC THENL [REWRITE_TAC[REAL_SUB_TRIANGLE]; ALL_TAC] THEN
    EXISTS_TAC `abs(f(m:num) - f(g(n:num))) + abs(f(g n) - l)` THEN
    REWRITE_TAC[ABS_TRIANGLE] THEN
    SUBST1_TAC(SYM(SPEC `e:real` REAL_HALF_DOUBLE)) THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[ABS_SUB] THEN ASM_REWRITE_TAC[];

    REWRITE_TAC[convergent] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` MP_TAC) THEN
    REWRITE_TAC[SEQ; cauchy] THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    SUBGOAL_THEN `f(m:num) - f(n) = (f(m) - l) + (l - f(n))`
    SUBST1_TAC THENL [REWRITE_TAC[REAL_SUB_TRIANGLE]; ALL_TAC] THEN
    EXISTS_TAC `abs(f(m:num) - l) + abs(l - f(n))` THEN
    REWRITE_TAC[ABS_TRIANGLE] THEN
    SUBST1_TAC(SYM(SPEC `e:real` REAL_HALF_DOUBLE)) THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[ABS_SUB] THEN ASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* The limit comparison property for sequences                                *)
(*----------------------------------------------------------------------------*)

let SEQ_LE = prove(
  `!f g l m. f --> l /\ g --> m /\ (?N. !n. n >= N ==> f(n) <= g(n))
        ==> l <= m`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(>=) :num->num->bool` NET_LE) THEN
  REWRITE_TAC[DORDER_NGE; tends_num_real; GE; LE_REFL] THEN
  DISCH_THEN MATCH_ACCEPT_TAC);;

(*----------------------------------------------------------------------------*)
(* We can displace a convergent series by 1                                   *)
(*----------------------------------------------------------------------------*)

let SEQ_SUC = prove(
  `!f l. f --> l = (\n. f(SUC n)) --> l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEQ; GE] THEN EQ_TAC THEN
  DISCH_THEN(fun th -> X_GEN_TAC `e:real` THEN
    DISCH_THEN(MP_TAC o MATCH_MP th)) THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THENL
   [EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `SUC N` THEN ASM_REWRITE_TAC[LE_SUC; LESS_EQ_SUC_REFL];
    EXISTS_TAC `SUC N` THEN X_GEN_TAC `n:num` THEN
    STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THENL
     [REWRITE_TAC[GSYM NOT_LT; LT_0];
      REWRITE_TAC[LE_SUC] THEN DISCH_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(*----------------------------------------------------------------------------*)
(* Prove a sequence tends to zero iff its abs does                            *)
(*----------------------------------------------------------------------------*)

let SEQ_ABS = prove(
  `!f. (\n. abs(f n)) --> &0 = f --> &0`,
  GEN_TAC THEN REWRITE_TAC[SEQ] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO; ABS_ABS]);;

(*----------------------------------------------------------------------------*)
(* Half this is true for a general limit                                      *)
(*----------------------------------------------------------------------------*)

let SEQ_ABS_IMP = prove(
  `!f l. f --> l ==> (\n. abs(f n)) --> abs(l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_ACCEPT_TAC NET_ABS);;

(*----------------------------------------------------------------------------*)
(* Prove that an unbounded sequence's inverse tends to 0                      *)
(*----------------------------------------------------------------------------*)

let SEQ_INV0 = prove(
  `!f. (!y. ?N. !n. n >= N ==> f(n) > y)
        ==> (\n. inv(f n)) --> &0`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SEQ; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `inv e`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN ANTE_RES_THEN MP_TAC th) THEN
  REWRITE_TAC[real_gt] THEN BETA_TAC THEN
  IMP_RES_THEN ASSUME_TAC REAL_INV_POS THEN
  SUBGOAL_THEN `&0 < f(n:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv e` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM real_gt] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(f(n:num))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(f(n:num) = &0)` ASSUME_TAC THENL
   [CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ABS_INV th]) THEN
  SUBGOAL_THEN `e = inv(inv e)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INVINV THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(f:num->real) n` THEN
  ASM_REWRITE_TAC[ABS_LE]);;

(*----------------------------------------------------------------------------*)
(* Important limit of c^n for |c| < 1                                         *)
(*----------------------------------------------------------------------------*)

let SEQ_POWER_ABS = prove(
  `!c. abs(c) < &1 ==> (\n. abs(c) pow n) --> &0`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `c:real` ABS_POS) THEN
  REWRITE_TAC[REAL_LE_LT] THEN DISCH_THEN DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `!n. abs(c) pow n = inv(inv(abs(c) pow n))`
      (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INVINV THEN
      MATCH_MP_TAC POW_NZ THEN
      ASM_REWRITE_TAC[ABS_NZ; ABS_ABS]; ALL_TAC] THEN
    CONV_TAC(EXACT_CONV[X_BETA_CONV `n:num` `inv(abs(c) pow n)`]) THEN
    MATCH_MP_TAC SEQ_INV0 THEN BETA_TAC THEN X_GEN_TAC `y:real` THEN
    SUBGOAL_THEN `~(abs(c) = &0)`
         (fun th -> REWRITE_TAC[MATCH_MP POW_INV th]) THENL
     [CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[real_gt] THEN
    SUBGOAL_THEN `&0 < inv(abs c) - &1` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_SUB_LADD] THEN REWRITE_TAC[REAL_ADD_LID] THEN
      ONCE_REWRITE_TAC[GSYM REAL_INV1] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `inv(abs c) - &1` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num` o SPEC `y:real`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN
    DISCH_TAC THEN SUBGOAL_THEN `y < (&n * (inv(abs c) - &1))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `&N * (inv(abs c) - &1)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th ->
        GEN_REWRITE_TAC I [MATCH_MP REAL_LE_RMUL_EQ th]) THEN
      ASM_REWRITE_TAC[REAL_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `&n * (inv(abs c) - &1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&1 + (&n * (inv(abs c) - &1))` THEN
    REWRITE_TAC[REAL_LT_ADDL; REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + (inv(abs c) - &1)) pow n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC POW_PLUS1 THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[REAL_SUB_ADD] THEN
      REWRITE_TAC[REAL_LE_REFL]];
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SEQ] THEN
    GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN BETA_TAC THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THENL
     [REWRITE_TAC[GSYM NOT_LT; num_CONV `1`; LT_0];
      REWRITE_TAC[POW_0; REAL_SUB_RZERO; ABS_0] THEN
      REWRITE_TAC[ASSUME `&0 < e`]]]);;

(*----------------------------------------------------------------------------*)
(* Similar version without the abs                                            *)
(*----------------------------------------------------------------------------*)

let SEQ_POWER = prove(
  `!c. abs(c) < &1 ==> (\n. c pow n) --> &0`,
  GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM SEQ_ABS] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM POW_ABS] THEN
  POP_ASSUM(ACCEPT_TAC o MATCH_MP SEQ_POWER_ABS));;

(*----------------------------------------------------------------------------*)
(* Useful lemmas about nested intervals and proof by bisection                *)
(*----------------------------------------------------------------------------*)

let NEST_LEMMA = prove(
  `!f g. (!n. f(SUC n) >= f(n)) /\
         (!n. g(SUC n) <= g(n)) /\
         (!n. f(n) <= g(n)) ==>
                ?l m. l <= m /\ ((!n. f(n) <= l) /\ f --> l) /\
                                ((!n. m <= g(n)) /\ g --> m)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `f:num->real` MONO_SUC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `g:num->real` MONO_SUC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN SUBGOAL_THEN `bounded((mr1), (>=) :num->num->bool) f`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SEQ_BOUNDED_2 THEN
    MAP_EVERY EXISTS_TAC [`(f:num->real) 0`; `(g:num->real) 0`] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) n` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `g(SUC n):real` THEN
      ASM_REWRITE_TAC[] THEN SPEC_TAC(`SUC n`,`m:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `g(m:num):real` THEN
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `bounded((mr1), (>=) :num->num->bool) g` ASSUME_TAC THENL
   [MATCH_MP_TAC SEQ_BOUNDED_2 THEN
    MAP_EVERY EXISTS_TAC [`(f:num->real) 0`; `(g:num->real) 0`] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) (SUC n)` THEN
      ASM_REWRITE_TAC[] THEN SPEC_TAC(`SUC n`,`m:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) m` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(g:num->real) n` THEN
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  MP_TAC(SPEC `f:num->real` SEQ_BCONV) THEN ASM_REWRITE_TAC[SEQ_LIM] THEN
  DISCH_TAC THEN MP_TAC(SPEC `g:num->real` SEQ_BCONV) THEN
  ASM_REWRITE_TAC[SEQ_LIM] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`lim f`; `lim g`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SEQ_LE THEN
    MAP_EVERY EXISTS_TAC [`f:num->real`; `g:num->real`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `m:num` THEN GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
    PURE_REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `f --> lim f` THEN REWRITE_TAC[SEQ] THEN
    DISCH_THEN(MP_TAC o SPEC `f(m) - lim f`) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `p + m:num`) THEN
    REWRITE_TAC[GE; LE_ADD] THEN REWRITE_TAC[real_abs] THEN
    SUBGOAL_THEN `!p. lim f <= f(p + m:num)` ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `f(p + m:num):real` THEN
        RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[REAL_SUB_LE] THEN
      REWRITE_TAC[REAL_NOT_LT; real_sub; REAL_LE_RADD] THEN
      SPEC_TAC(`p:num`,`p:num`) THEN INDUCT_TAC THEN
      REWRITE_TAC[REAL_LE_REFL; ADD_CLAUSES] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `f(p + m:num):real` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `m:num` THEN GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
    PURE_REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `g --> lim g` THEN REWRITE_TAC[SEQ] THEN
    DISCH_THEN(MP_TAC o SPEC `lim g - g(m)`) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `p + m:num`) THEN
    REWRITE_TAC[GE; LE_ADD] THEN REWRITE_TAC[real_abs] THEN
    SUBGOAL_THEN `!p. g(p + m:num) < lim g` ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `g(p + m:num):real` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_SUB_LE] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
      REWRITE_TAC[REAL_NOT_LT; REAL_NEG_SUB] THEN
      REWRITE_TAC[real_sub; REAL_LE_LADD; REAL_LE_NEG] THEN
      SPEC_TAC(`p:num`,`p:num`) THEN INDUCT_TAC THEN
      REWRITE_TAC[REAL_LE_REFL; ADD_CLAUSES] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `g(p + m:num):real` THEN
      ASM_REWRITE_TAC[]]]);;

let NEST_LEMMA_UNIQ = prove(
  `!f g. (!n. f(SUC n) >= f(n)) /\
         (!n. g(SUC n) <= g(n)) /\
         (!n. f(n) <= g(n)) /\
         (\n. f(n) - g(n)) --> &0 ==>
                ?l. ((!n. f(n) <= l) /\ f --> l) /\
                    ((!n. l <= g(n)) /\ g --> l)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NEST_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `l:real = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`f:num->real`; `l:real`; `g:num->real`; `m:real`] SEQ_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJ(ASSUME `(\n. f(n) - g(n)) --> &0`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_UNIQ) THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_SUB_0]);;

let BOLZANO_LEMMA = prove(
  `!P. (!a b c. a <= b /\ b <= c /\ P(a,b) /\ P(b,c) ==> P(a,c)) /\
       (!x. ?d. &0 < d /\ !a b. a <= x /\ x <= b /\ (b - a) < d ==> P(a,b))
      ==> !a b. a <= b ==> P(a,b)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN DISCH_TAC THEN
  (X_CHOOSE_THEN `f:num->real#real` STRIP_ASSUME_TAC o
   EXISTENCE o BETA_RULE o C ISPECL num_Axiom)
    [`(a:real,(b:real))`;
     `\fn (n:num). P(FST fn,(FST fn + SND fn)/ &2) =>
                        ((FST fn + SND fn)/ &2,SND fn) |
                        (FST fn,(FST fn + SND fn)/ &2)`] THEN
  MP_TAC(SPECL
    [`\n:num. FST(f(n) :real#real)`; `\n:num. SND(f(n) :real#real)`]
    NEST_LEMMA_UNIQ) THEN BETA_TAC THEN
  SUBGOAL_THEN `!n:num. FST(f n) <= SND(f n)` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    LCOND_CASES_TAC THEN REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_MIDDLE2; MATCH_MP_TAC REAL_MIDDLE1] THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN REWRITE_TAC[real_ge] THEN
  SUBGOAL_THEN `!n. FST(f n :real#real) <= FST(f(SUC n))`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_ge] THEN INDUCT_TAC THEN
    FIRST_ASSUM
     (fun th -> GEN_REWRITE_TAC (funpow 2 RAND_CONV) [th]) THEN
    LCOND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_MIDDLE1 THEN FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~P(FST((f:num->real#real) n),SND(f n))` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    LCOND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `~P(FST((f:num->real#real) n),SND(f n))` THEN
    PURE_REWRITE_TAC[IMP_CLAUSES; NOT_CLAUSES] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(FST(f(n:num)) + SND(f(n))) / &2` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MIDDLE1; MATCH_MP_TAC REAL_MIDDLE2] THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. SND(f(SUC n) :real#real) <= SND(f n)` ASSUME_TAC THENL
   [BETA_TAC THEN INDUCT_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
      (LAND_CONV o RAND_CONV) [th]) THEN
    LCOND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_MIDDLE2 THEN FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. SND(f n) - FST(f n) = (b - a) / (&2 pow n)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[pow; real_div; REAL_INV1; REAL_MUL_RID]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN LCOND_CASES_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN EXISTS_TAC `&2` THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    (SUBGOAL_THEN `~(&2 = &0)` (fun th -> REWRITE_TAC[th] THEN
     REWRITE_TAC[MATCH_MP REAL_DIV_LMUL th]) THENL
      [REWRITE_TAC[REAL_INJ; num_CONV `2`; NOT_SUC]; ALL_TAC]) THEN
    REWRITE_TAC[GSYM REAL_DOUBLE] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ADD_SYM] THEN
    (SUBGOAL_THEN `!x y z. (x + y) - (x + z) = y - z`
     (fun th -> REWRITE_TAC[th])
     THENL
      [REPEAT GEN_TAC THEN REWRITE_TAC[real_sub; REAL_NEG_ADD] THEN
       GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_RID] THEN
       SUBST1_TAC(SYM(SPEC `x:real` REAL_ADD_LINV)) THEN
       REWRITE_TAC[REAL_ADD_AC]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[REAL_DOUBLE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[pow] THEN
    (SUBGOAL_THEN `~(&2 = &0) /\ ~(&2 pow n = &0)`
       (fun th -> REWRITE_TAC[MATCH_MP REAL_INV_MUL_WEAK th]) THENL
      [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC POW_NZ] THEN
       REWRITE_TAC[REAL_INJ] THEN
       REWRITE_TAC[num_CONV `2`; NOT_SUC];
       ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
       GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
         [GSYM REAL_MUL_LID] THEN
       AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
       MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC[REAL_INJ] THEN
       REWRITE_TAC[num_CONV `2`; NOT_SUC]]);
    ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert (can (find_term is_cond)) o concl) THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN
    (fun t -> REWRITE_TAC[t]) o fst o dest_imp o rand o snd) THENL
   [ONCE_REWRITE_TAC[SEQ_NEG] THEN BETA_TAC THEN
    ASM_REWRITE_TAC[REAL_NEG_SUB; REAL_NEG_0] THEN
    REWRITE_TAC[real_div] THEN SUBGOAL_THEN `~(&2 = &0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_INJ; num_CONV `2`; NOT_SUC]; ALL_TAC] THEN
    (MP_TAC o C SPECL SEQ_MUL)
      [`\n:num. b - a`; `b - a`; `\n. (inv (&2 pow n))`; `&0`] THEN
    REWRITE_TAC[SEQ_CONST; REAL_MUL_RZERO] THEN BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP POW_INV th]) THEN
    ONCE_REWRITE_TAC[GSYM SEQ_ABS] THEN BETA_TAC THEN
    REWRITE_TAC[GSYM POW_ABS] THEN MATCH_MP_TAC SEQ_POWER_ABS THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ABS_INV th]) THEN
    REWRITE_TAC[ABS_N] THEN SUBGOAL_THEN `&0 < &2`
    (fun th -> ONCE_REWRITE_TAC [GSYM (MATCH_MP REAL_LT_RMUL_EQ th)]) THENL
     [REWRITE_TAC[REAL_LT; num_CONV `2`; LT_0]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
    REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[REAL_LT] THEN
    REWRITE_TAC[num_CONV `2`; LESS_SUC_REFL];
    DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `d:real` MP_TAC o SPEC `l:real`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    UNDISCH_TAC `(\n:num. SND(f n :real#real)) --> l` THEN
    UNDISCH_TAC `(\n:num. FST(f n :real#real)) --> l` THEN
    REWRITE_TAC[SEQ] THEN DISCH_THEN(MP_TAC o SPEC `d / &2`) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (ASSUME_TAC o BETA_RULE)) THEN
    DISCH_THEN(MP_TAC o SPEC `d / &2`) THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (ASSUME_TAC o BETA_RULE)) THEN
    DISCH_THEN(MP_TAC o
      SPECL [`FST((f:num->real#real) (N1 + N2))`;
             `SND((f:num->real#real) (N1 + N2))`]) THEN
    UNDISCH_TAC `!n. (SND(f n)) - (FST(f n)) = (b - a) / ((& 2) pow n)` THEN
    DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(FST(f(N1 + N2:num)) - l) +
                abs(SND(f(N1 + N2:num)) - l)` THEN
    GEN_REWRITE_TAC (funpow 2 RAND_CONV) [GSYM REAL_HALF_DOUBLE] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ABS_SUB] THEN
      ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN
      REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC] THEN
      REWRITE_TAC[AC REAL_ADD_AC `a + b + c + d = (d + a) + (c + b)`] THEN
      REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LT_ADD2 THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[GE; LE_ADD] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LE_ADD]]]);;

(*----------------------------------------------------------------------------*)
(* Define infinite sums                                                       *)
(*----------------------------------------------------------------------------*)

let sums = new_definition
  `f sums s = (\n. Sum(0,n) f) --> s`;;

let summable = new_definition(
  `summable f = ?s. f sums s`);;

let suminf = new_definition(
  `suminf f = @s. f sums s`);;

(*----------------------------------------------------------------------------*)
(* If summable then it sums to the sum (!)                                    *)
(*----------------------------------------------------------------------------*)

let SUM_SUMMABLE = prove(
  `!f l. f sums l ==> summable f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[summable] THEN
  EXISTS_TAC `l:real` THEN POP_ASSUM ACCEPT_TAC);;

let SUMMABLE_SUM = prove(
  `!f. summable f ==> f sums (suminf f)`,
  GEN_TAC THEN REWRITE_TAC[summable; suminf] THEN
  DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  MATCH_ACCEPT_TAC SELECT_AX);;

(*----------------------------------------------------------------------------*)
(* And the sum is unique                                                      *)
(*----------------------------------------------------------------------------*)

let SUM_UNIQ = prove(
  `!f x. f sums x ==> (x = suminf f)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `summable f` MP_TAC THENL
   [REWRITE_TAC[summable] THEN EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o MATCH_MP SUMMABLE_SUM) THEN
    MATCH_MP_TAC SEQ_UNIQ THEN
    EXISTS_TAC `\n. Sum(0,n) f` THEN ASM_REWRITE_TAC[GSYM sums]]);;

(*----------------------------------------------------------------------------*)
(* Series which is zero beyond a certain point                                *)
(*----------------------------------------------------------------------------*)

let SER_0 = prove(
  `!f n. (!m. n <= m ==> (f(m) = &0)) ==>
        f sums (Sum(0,n) f)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[sums; SEQ] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `n:num` THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[GE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD) THEN
  W(C SUBGOAL_THEN SUBST1_TAC o C (curry mk_eq) `&0` o rand o rator o snd) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ABS_ZERO; REAL_SUB_0] THEN
  BETA_TAC THEN REWRITE_TAC[GSYM SUM_TWO; REAL_ADD_RID_UNIQ] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[GE] SUM_ZERO)) THEN
  MATCH_ACCEPT_TAC LE_REFL);;

(*----------------------------------------------------------------------------*)
(* Summable series of positive terms has limit >(=) any partial sum           *)
(*----------------------------------------------------------------------------*)

let SER_POS_LE = prove(
  `!f n. summable f /\ (!m. n <= m ==> &0 <= f(m))
        ==> Sum(0,n) f <= suminf f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN REWRITE_TAC[sums] THEN
  MP_TAC(SPEC `Sum(0,n) f` SEQ_CONST) THEN
  GEN_REWRITE_TAC I [TAUT `a ==> b ==> c = a /\ b ==> c`] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d = c ==> a /\ b ==> d`]
    SEQ_LE) THEN BETA_TAC THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN REWRITE_TAC[GE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD) THEN
  REWRITE_TAC[GSYM SUM_TWO; REAL_LE_ADDR] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let SER_POS_LT = prove(
  `!f n. summable f /\ (!m. n <= m ==> &0 < f(m))
        ==> Sum(0,n) f < suminf f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `Sum(0,n + 1) f` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_TWO; REAL_LT_ADDR] THEN
    REWRITE_TAC[num_CONV `1`; Sum; REAL_ADD_LID; ADD_CLAUSES] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN MATCH_ACCEPT_TAC LE_REFL;
    MATCH_MP_TAC SER_POS_LE THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `SUC n` THEN
    REWRITE_TAC[LESS_EQ_SUC_REFL] THEN ASM_REWRITE_TAC[ADD1]]);;

(*----------------------------------------------------------------------------*)
(* Theorems about grouping and offsetting, *not* permuting, terms             *)
(*----------------------------------------------------------------------------*)

let SER_GROUP = prove(
  `!f k. summable f /\ 0 < k ==>
          (\n. Sum(n * k,k) f) sums (suminf f)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  REWRITE_TAC[sums; SEQ] THEN BETA_TAC THEN
  DISCH_THEN(fun t -> X_GEN_TAC `e:real` THEN
  DISCH_THEN(MP_TAC o MATCH_MP t)) THEN
  REWRITE_TAC[GE] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  REWRITE_TAC[SUM_GROUP] THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `0 < k` THEN
  STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
  REWRITE_TAC[MULT_CLAUSES; LE_ADD; CONJUNCT1 LE] THEN
  REWRITE_TAC[LT_REFL]);;

let SER_PAIR = prove(
  `!f. summable f ==> (\n. Sum(2 * n,2) f) sums (suminf f)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o C CONJ (SPEC `1:num` LT_0)) THEN
  REWRITE_TAC[SYM(num_CONV `2`)] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_ACCEPT_TAC SER_GROUP);;

let SER_OFFSET = prove(
  `!f. summable f ==> !k. (\n. f(n + k)) sums (suminf f - Sum(0,k) f)`,
  GEN_TAC THEN
  DISCH_THEN(prefix THEN GEN_TAC o MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  REWRITE_TAC[sums; SEQ] THEN
  DISCH_THEN(fun th -> GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  BETA_TAC THEN REWRITE_TAC[GE] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[SUM_OFFSET] THEN
  REWRITE_TAC[real_sub; REAL_NEG_ADD; REAL_NEGNEG] THEN
  ONCE_REWRITE_TAC[AC REAL_ADD_AC
    `(a + b) + (c + d) = (b + d) + (a + c)`] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID] THEN REWRITE_TAC[GSYM real_sub] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[LE_ADD]);;

(*----------------------------------------------------------------------------*)
(* Similar version for pairing up terms                                       *)
(*----------------------------------------------------------------------------*)

let SER_POS_LT_PAIR = prove(
  `!f n. summable f /\
         (!d. &0 < (f(n + (2 * d))) +
               f(n + ((2 * d) + 1)))
        ==> Sum(0,n) f < suminf f`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  REWRITE_TAC[sums; SEQ] THEN BETA_TAC THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `f(n) + f(n + 1)`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
  SUBGOAL_THEN `Sum(0,n + 2) f <= Sum(0,(2 * (SUC N)) + n) f`
  ASSUME_TAC THENL
   [SPEC_TAC(`N:num`,`N:num`) THEN INDUCT_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
      MATCH_ACCEPT_TAC REAL_LE_REFL;
      ABBREV_TAC `M = SUC N` THEN
      REWRITE_TAC[MULT_CLAUSES] THEN
      REWRITE_TAC[num_CONV `2`; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[ADD_SYM] ADD1)] THEN
      REWRITE_TAC[SYM(num_CONV `2`)] THEN REWRITE_TAC[ADD_CLAUSES] THEN
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [ADD1] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      REWRITE_TAC[GSYM ADD1; SYM(num_CONV `2`)] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Sum(0,(2 * M) + n) f` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[Sum] THEN
      REWRITE_TAC[GSYM REAL_ADD_ASSOC; REAL_LE_ADDR] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[ADD1] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      ONCE_REWRITE_TAC[SPEC `1` ADD_SYM] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `(2 * (SUC N)) + n`) THEN
    W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o
      funpow 2(fst o dest_imp) o snd) THENL
     [REWRITE_TAC[num_CONV `2`; MULT_CLAUSES] THEN
      ONCE_REWRITE_TAC[AC ADD_AC
       `(a + (b + c)) + d:num = b + (a + (c + d))`] THEN
      REWRITE_TAC[GE; LE_ADD]; ALL_TAC] THEN
    SUBGOAL_THEN `(suminf f + (f(n) + f(n + 1))) <=
                              Sum(0,(2 * (SUC N)) + n) f`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Sum(0,n + 2) f` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Sum(0,n) f + (f(n) + f(n + 1))` THEN
      ASM_REWRITE_TAC[REAL_LE_RADD] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      CONV_TAC(REDEPTH_CONV num_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; Sum; REAL_ADD_ASSOC]; ALL_TAC] THEN
    SUBGOAL_THEN `suminf f <= Sum(0,(2 * (SUC N)) + n) f`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `suminf f + (f(n) + f(n + 1))` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_LE_ADDR] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_LT_SUB_RADD] THEN
    GEN_REWRITE_TAC (funpow 2 RAND_CONV) [REAL_ADD_SYM] THEN
    ASM_REWRITE_TAC[REAL_NOT_LT]]);;

(*----------------------------------------------------------------------------*)
(* Prove a few composition formulas for series                                *)
(*----------------------------------------------------------------------------*)

let SER_ADD = prove(
  `!x x0 y y0. x sums x0 /\ y sums y0 ==> (\n. x(n) + y(n)) sums (x0 + y0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sums; SUM_ADD] THEN
  CONV_TAC((RAND_CONV o EXACT_CONV)[X_BETA_CONV `n:num` `Sum(0,n) x`]) THEN
  CONV_TAC((RAND_CONV o EXACT_CONV)[X_BETA_CONV `n:num` `Sum(0,n) y`]) THEN
  MATCH_ACCEPT_TAC SEQ_ADD);;

let SER_CMUL = prove(
  `!x x0 c. x sums x0 ==> (\n. c * x(n)) sums (c * x0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sums; SUM_CMUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\n. (\n. c) n * (\n. Sum(0,n) x) n) --> c * x0` MP_TAC THENL
   [MATCH_MP_TAC SEQ_MUL THEN ASM_REWRITE_TAC[SEQ_CONST];
    REWRITE_TAC[BETA_THM]]);;

let SER_NEG = prove(
  `!x x0. x sums x0 ==> (\n. --(x n)) sums --x0`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  MATCH_ACCEPT_TAC SER_CMUL);;

let SER_SUB = prove(
  `!x x0 y y0. x sums x0 /\ y sums y0 ==> (\n. x(n) - y(n)) sums (x0 - y0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC (MATCH_MP SER_ADD
      (CONJ (CONJUNCT1 th) (MATCH_MP SER_NEG (CONJUNCT2 th))))) THEN
  BETA_TAC THEN REWRITE_TAC[real_sub]);;

let SER_CDIV = prove(
  `!x x0 c. x sums x0 ==> (\n. x(n) / c) sums (x0 / c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC SER_CMUL);;

(*----------------------------------------------------------------------------*)
(* Prove Cauchy-type criterion for convergence of series                      *)
(*----------------------------------------------------------------------------*)

let SER_CAUCHY = prove(
  `!f. summable f =
          !e. &0 < e ==> ?N. !m n. m >= N ==> abs(Sum(m,n) f) < e`,
  GEN_TAC THEN REWRITE_TAC[summable; sums] THEN
  REWRITE_TAC[GSYM convergent] THEN
  REWRITE_TAC[GSYM SEQ_CAUCHY] THEN REWRITE_TAC[cauchy] THEN
  AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[GE] THEN BETA_TAC THEN
  REWRITE_TAC[TAUT `((a ==> b) = (a ==> c)) = a ==> (b = c)`] THEN
  DISCH_TAC THEN EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [ONCE_REWRITE_TAC[SUM_DIFF] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[LE_ADD];
    DISJ_CASES_THEN MP_TAC (SPECL [`m:num`; `n:num`] LE_CASES) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC o
      MATCH_MP LESS_EQUAL_ADD) THENL
     [ONCE_REWRITE_TAC[ABS_SUB]; ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_DIFF] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* Show that if a series converges, the terms tend to 0                       *)
(*----------------------------------------------------------------------------*)

let SER_ZERO = prove(
  `!f. summable f ==> f --> &0`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SEQ] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `summable f` THEN REWRITE_TAC[SER_CAUCHY] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
  DISCH_THEN(prefix THEN (EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC) o MP_TAC) THEN DISCH_THEN(MP_TAC o SPECL [`n:num`; `SUC 0`]) THEN
  ASM_REWRITE_TAC[Sum; REAL_SUB_RZERO; REAL_ADD_LID; ADD_CLAUSES]);;

(*----------------------------------------------------------------------------*)
(* Now prove the comparison test                                              *)
(*----------------------------------------------------------------------------*)

let SER_COMPAR = prove(
  `!f g. (?N. !n. n >= N ==> abs(f(n)) <= g(n)) /\ summable g ==>
            summable f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SER_CAUCHY; GE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `N1:num`) MP_TAC) THEN
  REWRITE_TAC[SER_CAUCHY; GE] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N1 + N2:num` THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `Sum(m,n)(\k. abs(f k))` THEN REWRITE_TAC[ABS_SUM] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `Sum(m,n) g` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN BETA_TAC THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `N1 + N2:num` THEN ASM_REWRITE_TAC[LE_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(Sum(m,n) g)` THEN
  REWRITE_TAC[ABS_LE] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N1 + N2:num` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[LE_ADD]);;

(*----------------------------------------------------------------------------*)
(* And a similar version for absolute convergence                             *)
(*----------------------------------------------------------------------------*)

let SER_COMPARA = prove(
  `!f g. (?N. !n. n >= N ==> abs(f(n)) <= g(n)) /\ summable g ==>
            summable (\k. abs(f k))`,
  REPEAT GEN_TAC THEN SUBGOAL_THEN `!n. abs(f(n)) = abs((\k:num. abs(f k)) n)`
  (fun th -> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [GEN_TAC THEN BETA_TAC THEN REWRITE_TAC[ABS_ABS];
    MATCH_ACCEPT_TAC SER_COMPAR]);;

(*----------------------------------------------------------------------------*)
(* Limit comparison property for series                                       *)
(*----------------------------------------------------------------------------*)

let SER_LE = prove(
  `!f g. (!n. f(n) <= g(n)) /\ summable f /\ summable g
        ==> suminf f <= suminf g`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th -> ASSUME_TAC th THEN ASSUME_TAC
    (REWRITE_RULE[sums] (MATCH_MP SUMMABLE_SUM th)))) THEN
  MATCH_MP_TAC SEQ_LE THEN REWRITE_TAC[CONJ_ASSOC] THEN
  MAP_EVERY EXISTS_TAC [`\n. Sum(0,n) f`; `\n. Sum(0,n) g`] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM sums] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUMMABLE_SUM THEN FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC `0` THEN REWRITE_TAC[GE; LE_0] THEN
    GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_LE THEN
    GEN_TAC THEN ASM_REWRITE_TAC[LE_0]]);;

let SER_LE2 = prove(
  `!f g. (!n. abs(f n) <= g(n)) /\ summable g ==>
                summable f /\ suminf f <= suminf g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `summable f` ASSUME_TAC THENL
   [MATCH_MP_TAC SER_COMPAR THEN EXISTS_TAC `g:num->real` THEN
    ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SER_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(f(n:num))` THEN ASM_REWRITE_TAC[ABS_LE]);;

(*----------------------------------------------------------------------------*)
(* Show that absolute convergence implies normal convergence                  *)
(*----------------------------------------------------------------------------*)

let SER_ACONV = prove(
  `!f. summable (\n. abs(f n)) ==> summable f`,
  GEN_TAC THEN REWRITE_TAC[SER_CAUCHY] THEN REWRITE_TAC[SUM_ABS] THEN
  DISCH_THEN(prefix THEN (X_GEN_TAC `e:real` THEN DISCH_TAC) o MP_TAC) THEN
  DISCH_THEN(IMP_RES_THEN (X_CHOOSE_TAC `N:num`)) THEN
  EXISTS_TAC `N:num` THEN REPEAT GEN_TAC THEN
  DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `Sum(m,n)(\m. abs(f m))` THEN ASM_REWRITE_TAC[ABS_SUM]);;

(*----------------------------------------------------------------------------*)
(* Absolute value of series                                                   *)
(*----------------------------------------------------------------------------*)

let SER_ABS = prove(
  `!f. summable(\n. abs(f n)) ==> abs(suminf f) <= suminf(\n. abs(f n))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUMMABLE_SUM o MATCH_MP SER_ACONV) THEN
  POP_ASSUM(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  REWRITE_TAC[sums] THEN DISCH_TAC THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE o MATCH_MP SEQ_ABS_IMP) THEN
  MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC
   [`\n. abs(Sum(0,n)f)`; `\n. Sum(0,n)(\n. abs(f n))`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN MATCH_ACCEPT_TAC SUM_ABS_LE);;

(*----------------------------------------------------------------------------*)
(* Prove sum of geometric progression (useful for comparison)                 *)
(*----------------------------------------------------------------------------*)

let GP_FINITE = prove(
  `!x. ~(x = &1) ==>
        !n. (Sum(0,n) (\n. x pow n) = ((x pow n) - &1) / (x - &1))`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[Sum; pow; REAL_SUB_REFL; REAL_DIV_LZERO];
    REWRITE_TAC[Sum; pow] THEN BETA_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN `~(x - &1 = &0)` ASSUME_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_0] THEN
    MP_TAC(GENL [`p:real`; `q:real`]
     (SPECL [`p:real`; `q:real`; `x - &1`] REAL_EQ_RMUL)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[REAL_RDISTRIB] THEN SUBGOAL_THEN
      `!p. (p / (x - &1)) * (x - &1) = p` (fun th -> REWRITE_TAC[th]) THENL
      [GEN_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC]
    THEN REWRITE_TAC[REAL_SUB_LDISTRIB] THEN REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC REAL_ADD_AC
      `(a + b) + (c + d) = (c + b) + (d + a)`] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_ADD_LINV; REAL_ADD_RID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM]);;

let GP = prove(
  `!x. abs(x) < &1 ==> (\n. x pow n) sums inv(&1 - x)`,
  GEN_TAC THEN ASM_CASES_TAC `x = &1` THEN
  ASM_REWRITE_TAC[ABS_1; REAL_LT_REFL] THEN DISCH_TAC THEN
  REWRITE_TAC[sums] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP GP_FINITE th]) THEN
  REWRITE_TAC[REAL_INV_1OVER] THEN REWRITE_TAC[real_div] THEN
  GEN_REWRITE_TAC (LAND_CONV o ABS_CONV) [GSYM REAL_NEG_MUL2] THEN
  SUBGOAL_THEN `~(x - &1 = &0)`
    (fun t -> REWRITE_TAC[MATCH_MP REAL_NEG_INV t]) THENL
    [ASM_REWRITE_TAC[REAL_SUB_0]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_SUB; GSYM real_div] THEN
  SUBGOAL_THEN `(\n. (\n. &1 - x pow n) n / (\n. &1 - x) n) --> &1 / (&1 - x)`
  MP_TAC THENL [ALL_TAC; REWRITE_TAC[BETA_THM]] THEN
  MATCH_MP_TAC SEQ_DIV THEN BETA_TAC THEN REWRITE_TAC[SEQ_CONST] THEN
  REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `(\n. (\n. &1) n - (\n. x pow n) n) --> &1 - &0`
  MP_TAC THENL [ALL_TAC; REWRITE_TAC[BETA_THM]] THEN
  MATCH_MP_TAC SEQ_SUB THEN BETA_TAC THEN REWRITE_TAC[SEQ_CONST] THEN
  MATCH_MP_TAC SEQ_POWER THEN FIRST_ASSUM ACCEPT_TAC);;

(*----------------------------------------------------------------------------*)
(* Now prove the ratio test                                                   *)
(*----------------------------------------------------------------------------*)

let ABS_NEG_LEMMA = prove(
  `!c. c <= &0 ==> !x y. abs(x) <= c * abs(y) ==> (x = &0)`,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NEG_GE0] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`--c`; `abs(y)`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ABS_POS; GSYM REAL_NEG_LMUL; REAL_NEG_GE0] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C CONJ th)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[ABS_NZ; REAL_NOT_LE]);;

let SER_RATIO = prove(
  `!f c N. c < &1 /\
           (!n. n >= N ==> abs(f(SUC n)) <= c * abs(f(n))) ==>
       summable f`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  DISJ_CASES_TAC (SPECL [`c:real`; `&0`] REAL_LET_TOTAL) THENL
   [REWRITE_TAC[SER_CAUCHY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!n. n >= N ==> (f(SUC n) = &0)` ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      MATCH_MP_TAC ABS_NEG_LEMMA THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `!n. n >= (SUC N) ==> (f(n) = &0)` ASSUME_TAC THENL
     [GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THENL
       [REWRITE_TAC[GE] THEN DISCH_THEN(MP_TAC o MATCH_MP OR_LESS) THEN
        REWRITE_TAC[NOT_LESS_0];
        REWRITE_TAC[GE; LE_SUC] THEN
        ASM_REWRITE_TAC[GSYM GE]]; ALL_TAC] THEN
    EXISTS_TAC `SUC N` THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUM_ZERO) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(ANTE_RES_THEN (fun th -> REWRITE_TAC[th])) THEN
    ASM_REWRITE_TAC[ABS_0];

    MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC `\n. (abs(f N) / c pow N) * (c pow n)` THEN CONJ_TAC THENL
     [EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[GE] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD)
      THEN BETA_TAC THEN REWRITE_TAC[POW_ADD] THEN REWRITE_TAC[real_div] THEN
      ONCE_REWRITE_TAC[AC REAL_MUL_AC
        `(a * b) * (c * d) = (a * d) * (b * c)`] THEN
      SUBGOAL_THEN `~(c pow N = &0)`
        (fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_LINV th; REAL_MUL_RID]) THENL
       [MATCH_MP_TAC POW_NZ THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
        MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
      REWRITE_TAC[pow; ADD_CLAUSES; REAL_MUL_RID; REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * abs(f(N + d:num))` THEN
      CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GE; LE_ADD];
        ONCE_REWRITE_TAC[AC REAL_MUL_AC
          `a * (b * c) = b * (a * c)`] THEN
        FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL_LOCAL th])];

      REWRITE_TAC[summable] THEN
      EXISTS_TAC `(abs(f(N:num)) / (c pow N)) * inv(&1 - c)` THEN
      MATCH_MP_TAC SER_CMUL THEN MATCH_MP_TAC GP THEN
      ASSUME_TAC(MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < c`)) THEN
      ASM_REWRITE_TAC[real_abs]]]);;

(*============================================================================*)
(* Theory of limits, continuity and differentiation of real->real functions   *)
(*============================================================================*)

parse_as_infix ("tends_real_real",(12,"right"));;

parse_as_infix ("diffl",(12,"right"));;
parse_as_infix ("contl",(12,"right"));;
parse_as_infix ("differentiable",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Specialize nets theorems to the pointwise limit of real->real functions    *)
(*----------------------------------------------------------------------------*)

let tends_real_real = new_definition
  `(f tends_real_real l)(x0) =
        (f tends l)(mtop(mr1),tendsto(mr1,x0))`;;

override_interface ("-->",`(tends_real_real)`);;

let LIM = prove(
  `!f y0 x0. (f --> y0)(x0) =
        !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < abs(x - x0) /\ abs(x - x0) < d ==>
                abs(f(x) - y0) < e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[tends_real_real; MATCH_MP LIM_TENDS2 (SPEC `x0:real` MR1_LIMPT)]
  THEN REWRITE_TAC[MR1_DEF] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB] THEN
  REFL_TAC);;

let LIM_CONST = prove(
  `!k x. ((\x. k) --> k)(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real; MTOP_TENDS] THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[METRIC_SAME] THEN
  REWRITE_TAC[tendsto; REAL_LE_REFL] THEN
  MP_TAC(REWRITE_RULE[MTOP_LIMPT] (SPEC `x:real` MR1_LIMPT)) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` (ASSUME_TAC o CONJUNCT1)) THEN
  EXISTS_TAC `z:real` THEN REWRITE_TAC[MR1_DEF; GSYM ABS_NZ] THEN
  REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
  ASM_REWRITE_TAC[]);;

let LIM_ADD = prove(
  `!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) + g(x)) --> (l + m))(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_ADD THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_MUL = prove(
  `!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) * g(x)) --> (l * m))(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_MUL THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_NEG = prove(
  `!f l. (f --> l)(x) = ((\x. --(f(x))) --> --l)(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_NEG THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_INV = prove(
  `!f l. (f --> l)(x) /\ ~(l = &0) ==>
        ((\x. inv(f(x))) --> inv l)(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_INV THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_SUB = prove(
  `!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) - g(x)) --> (l - m))(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_SUB THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_DIV = prove(
  `!f g l m. (f --> l)(x) /\ (g --> m)(x) /\ ~(m = &0) ==>
      ((\x. f(x) / g(x)) --> (l / m))(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_DIV THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_NULL = prove(
  `!f l x. (f --> l)(x) = ((\x. f(x) - l) --> &0)(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_ACCEPT_TAC NET_NULL);;

(*----------------------------------------------------------------------------*)
(* One extra theorem is handy                                                 *)
(*----------------------------------------------------------------------------*)

let LIM_X = prove(
  `!x0. ((\x. x) --> x0)(x0)`,
  GEN_TAC THEN REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Uniqueness of limit                                                        *)
(*----------------------------------------------------------------------------*)

let LIM_UNIQ = prove(
  `!f l m x. (f --> l)(x) /\ (f --> m)(x) ==> (l = m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC MTOP_TENDS_UNIQ THEN
  MATCH_ACCEPT_TAC DORDER_TENDSTO);;

(*----------------------------------------------------------------------------*)
(* Show that limits are equal when functions are equal except at limit point  *)
(*----------------------------------------------------------------------------*)

let LIM_EQUAL = prove(
  `!f g l x0. (!x. ~(x = x0) ==> (f x = g x)) ==>
        ((f --> l)(x0) = (g --> l)(x0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ONCE_REWRITE_TAC[TAUT `(a ==> b = a ==> c) = a ==> (b = c)`] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  ASM_REWRITE_TAC[ABS_NZ]);;

(*----------------------------------------------------------------------------*)
(* A more general theorem about rearranging the body of a limit               *)
(*----------------------------------------------------------------------------*)

let LIM_TRANSFORM = prove(
  `!f g x0 l. ((\x. f(x) - g(x)) --> &0)(x0) /\ (g --> l)(x0)
        ==> (f --> l)(x0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  DISCH_THEN(prefix THEN (X_GEN_TAC `e:real` THEN DISCH_TAC) o MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `e / &2`)) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`c:real`; `d:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real` THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(e / &2) + (e / &2)` THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_HALF_DOUBLE] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(f(x:real) - g(x)) + abs(g(x) - l)` THEN
  SUBST1_TAC(SYM(SPECL
    [`(f:real->real) x`; `(g:real->real) x`; `l:real`] REAL_SUB_TRIANGLE)) THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN MATCH_MP_TAC REAL_LT_ADD2 THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `b:real` THEN
  ASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Define differentiation and continuity                                      *)
(*----------------------------------------------------------------------------*)

let diffl = new_definition
  `(f diffl l)(x) = ((\h. (f(x+h) - f(x)) / h) --> l)(&0)`;;

let contl = new_definition
  `f contl x = ((\h. f(x + h)) --> f(x))(&0)`;;

let differentiable = new_definition
  `f differentiable x = ?l. (f diffl l)(x)`;;

(*----------------------------------------------------------------------------*)
(* Derivative is unique                                                       *)
(*----------------------------------------------------------------------------*)

let DIFF_UNIQ = prove(
  `!f l m x. (f diffl l)(x) /\ (f diffl m)(x) ==> (l = m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  MATCH_ACCEPT_TAC LIM_UNIQ);;

(*----------------------------------------------------------------------------*)
(* Differentiability implies continuity                                       *)
(*----------------------------------------------------------------------------*)

let DIFF_CONT = prove(
  `!f l x. (f diffl l)(x) ==> f contl x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl; contl] THEN DISCH_TAC THEN
  REWRITE_TAC[tends_real_real] THEN ONCE_REWRITE_TAC[NET_NULL] THEN
  REWRITE_TAC[GSYM tends_real_real] THEN BETA_TAC THEN
  SUBGOAL_THEN `((\h. f(x + h) - f(x)) --> &0)(&0) =
                ((\h. ((f(x + h) - f(x)) / h) * h) --> &0)(&0)` SUBST1_TAC
  THENL
   [MATCH_MP_TAC LIM_EQUAL THEN
    X_GEN_TAC `z:real` THEN BETA_TAC THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP REAL_DIV_RMUL th]); ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV o RAND_CONV)
    [SYM(BETA_CONV `(\h:real. h) h`)] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV `h:real` `(f(x + h) - f(x)) / h`]) THEN
  SUBST1_TAC(SYM(SPEC `l:real` REAL_MUL_RZERO)) THEN
  MATCH_MP_TAC LIM_MUL THEN BETA_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIM] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e:real` THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Alternative definition of continuity                                       *)
(*----------------------------------------------------------------------------*)

let CONTL_LIM = prove(
  `!f x. f contl x = (f --> f(x))(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contl; LIM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ONCE_REWRITE_TAC[TAUT `(a ==> b = a ==> c) = a ==> (b = c)`] THEN
  DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real` THENL
   [DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[REAL_SUB_ADD2];
    DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_ADD_SUB]]);;

(*----------------------------------------------------------------------------*)
(* Simple combining theorems for continuity                                   *)
(*----------------------------------------------------------------------------*)

let CONT_CONST = prove(
  `!x. (\x. k) contl x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN
  MATCH_ACCEPT_TAC LIM_CONST);;

let CONT_ADD = prove(
  `!x. f contl x /\ g contl x ==> (\x. f(x) + g(x)) contl x`,
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_ADD);;

let CONT_MUL = prove(
  `!x. f contl x /\ g contl x ==> (\x. f(x) * g(x)) contl x`,
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_MUL);;

let CONT_NEG = prove(
  `!x. f contl x ==> (\x. --(f(x))) contl x`,
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM LIM_NEG]);;

let CONT_INV = prove(
  `!x. f contl x /\ ~(f x = &0) ==> (\x. inv(f(x))) contl x`,
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_INV);;

let CONT_SUB = prove(
  `!x. f contl x /\ g contl x ==> (\x. f(x) - g(x)) contl x`,
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_SUB);;

let CONT_DIV = prove(
  `!x. f contl x /\ g contl x /\ ~(g x = &0) ==>
        (\x. f(x) / g(x)) contl x`,
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_DIV);;

(* ------------------------------------------------------------------------- *)
(* Composition of continuous functions is continuous.                        *)
(* ------------------------------------------------------------------------- *)

let CONT_COMPOSE = prove(
  `!f g x. f contl x /\ g contl (f x) ==> (\x. g(f x)) contl x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contl; LIM; REAL_SUB_RZERO] THEN
  BETA_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:real` THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  ASM_CASES_TAC `&0 < abs(f(x + h) - f(x))` THENL
   [UNDISCH_TAC `&0 < abs(f(x + h) - f(x))` THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o CONJ th)) THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[REAL_SUB_ADD2];
    UNDISCH_TAC `~(&0 < abs(f(x + h) - f(x)))` THEN
    REWRITE_TAC[GSYM ABS_NZ; REAL_SUB_0] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; ABS_0]]);;

(*----------------------------------------------------------------------------*)
(* Intermediate Value Theorem (we prove contrapositive by bisection)          *)
(*----------------------------------------------------------------------------*)

let IVT = prove(
  `!f a b y. a <= b /\
             (f(a) <= y /\ y <= f(b)) /\
             (!x. a <= x /\ x <= b ==> f contl x)
        ==> (?x. a <= x /\ x <= b /\ (f(x) = y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  CONV_TAC CONTRAPOS_CONV THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
  (MP_TAC o C SPEC BOLZANO_LEMMA)
    `\(u,v). a <= u /\ u <= v /\ v <= b ==> ~(f(u) <= y /\ y <= f(v))` THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o
  funpow 2 (fst o dest_imp) o snd) THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL [`a:real`; `b:real`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `w:real`] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM; NOT_IMP] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY ASM_CASES_TAC [`u <= v`; `v <= w`] THEN ASM_REWRITE_TAC[] THEN
    DISJ_CASES_TAC(SPECL [`y:real`; `(f:real->real) v`] REAL_LE_TOTAL) THEN
    ASM_REWRITE_TAC[] THENL [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `w:real`; EXISTS_TAC `u:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN ASM_CASES_TAC `a <= x /\ x <= b` THENL
   [ALL_TAC;
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC `~(a <= x /\ x <= b)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `u:real`; EXISTS_TAC `v:real`] THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `!x. ~(a <= x /\ x <= b /\ (f(x) = (y:real)))` THEN
  DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `!x. a <= x /\ x <= b ==> f contl x` THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[contl; LIM] THEN
  DISCH_THEN(MP_TAC o SPEC `abs(y - f(x:real))`) THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM ABS_NZ] THEN
  REWRITE_TAC[REAL_SUB_0; REAL_SUB_RZERO] THEN BETA_TAC THEN
  ASSUM_LIST(fun thl -> REWRITE_TAC(map GSYM thl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(f:real->real) x`; `y:real`] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THENL
   [DISCH_THEN(MP_TAC o SPEC `v - x`) THEN REWRITE_TAC[NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[real_abs; REAL_SUB_LE; REAL_SUB_LT] THEN
      ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `f(v:real) < y` THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE];
      ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `v - u` THEN
      ASM_REWRITE_TAC[real_sub; REAL_LE_LADD; REAL_LE_NEG; REAL_LE_RADD];
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[REAL_SUB_ADD] THEN
      REWRITE_TAC[REAL_NOT_LT; real_abs; REAL_SUB_LE] THEN
      SUBGOAL_THEN `f(x:real) <= y` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `f(x:real) <= f(v)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `y:real`; ALL_TAC] THEN
      ASM_REWRITE_TAC[real_sub; REAL_LE_RADD]];
    DISCH_THEN(MP_TAC o SPEC `u - x`) THEN REWRITE_TAC[NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ABS_SUB] THEN
      ASM_REWRITE_TAC[real_abs; REAL_SUB_LE; REAL_SUB_LT] THEN
      ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `y < f(x:real)` THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE];
      ONCE_REWRITE_TAC[ABS_SUB] THEN ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `v - u` THEN
      ASM_REWRITE_TAC[real_sub; REAL_LE_LADD; REAL_LE_NEG; REAL_LE_RADD];
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[REAL_SUB_ADD] THEN
      REWRITE_TAC[REAL_NOT_LT; real_abs; REAL_SUB_LE] THEN
      SUBGOAL_THEN `f(u:real) < f(x)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `y:real` THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
      ASM_REWRITE_TAC[REAL_NOT_LT; REAL_LE_NEG; real_sub; REAL_LE_RADD]]]);;

(*----------------------------------------------------------------------------*)
(* Intermediate value theorem where value at the left end is bigger           *)
(*----------------------------------------------------------------------------*)

let IVT2 = prove(
  `!f a b y. (a <= b) /\ (f(b) <= y /\ y <= f(a)) /\
             (!x. a <= x /\ x <= b ==> f contl x) ==>
        ?x. a <= x /\ x <= b /\ (f(x) = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. --(f x)`; `a:real`; `b:real`; `--y`] IVT) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_LE_NEG; REAL_NEG_EQ; REAL_NEGNEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC CONT_NEG THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Prove the simple combining theorems for differentiation                    *)
(*----------------------------------------------------------------------------*)

let DIFF_CONST = prove(
  `!k x. ((\x. k) diffl &0)(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO] THEN
  MATCH_ACCEPT_TAC LIM_CONST);;

let DIFF_ADD = prove(
  `!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD2_SUB2] THEN
  REWRITE_TAC[real_div; REAL_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV `h:real` `(f(x + h) - f(x)) / h`]) THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV `h:real` `(g(x + h) - g(x)) / h`]) THEN
  MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[]);;

let DIFF_MUL = prove(
  `!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                  ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  DISCH_TAC THEN BETA_TAC THEN SUBGOAL_THEN
    `!a b c d. (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))`
  (fun th -> ONCE_REWRITE_TAC[GEN_ALL th]) THENL
   [REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC REAL_ADD_AC
      `(a + b) + (c + d) = (b + c) + (a + d)`] THEN
    REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN SUBGOAL_THEN
    `!a b c d e. ((a * b) + (c * d)) / e = ((b / e) * a) + ((c / e) * d)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
    REWRITE_TAC[REAL_RDISTRIB] THEN BINOP_TAC THEN
    REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ADD_SYM] THEN
  CONV_TAC(EXACT_CONV(map (X_BETA_CONV `h:real`)
    [`((g(x + h) - g(x)) / h) * f(x + h)`;
     `((f(x + h) - f(x)) / h) * g(x)`])) THEN
  MATCH_MP_TAC LIM_ADD THEN
  CONV_TAC(EXACT_CONV(map (X_BETA_CONV `h:real`)
    [`(g(x + h) - g(x)) / h`; `f(x + h):real`;
     `(f(x + h) - f(x)) / h`; `g(x:real):real`])) THEN
  CONJ_TAC THEN MATCH_MP_TAC LIM_MUL THEN
  BETA_TAC THEN ASM_REWRITE_TAC[LIM_CONST] THEN
  REWRITE_TAC[GSYM contl] THEN
  MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `l:real` THEN
  ASM_REWRITE_TAC[diffl]);;

let DIFF_CMUL = prove(
  `!f c l x. (f diffl l)(x) ==> ((\x. c * f(x)) diffl (c * l))(x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONJ (SPECL [`c:real`; `x:real`] DIFF_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  MATCH_MP_TAC(TAUT(`(a = b) ==> a ==> b`)) THEN AP_THM_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[]);;

let DIFF_NEG = prove(
  `!f l x. (f diffl l)(x) ==> ((\x. --(f x)) diffl --l)(x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  MATCH_ACCEPT_TAC DIFF_CMUL);;

let DIFF_SUB = prove(
  `!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD o (uncurry CONJ) o
              (I F_F MATCH_MP DIFF_NEG) o CONJ_PAIR) THEN
  BETA_TAC THEN REWRITE_TAC[real_sub]);;

(* ------------------------------------------------------------------------- *)
(* Carathe'odory definition makes the chain rule proof much easier.          *)
(* ------------------------------------------------------------------------- *)

let DIFF_CARAT = prove(
  `!f l x. (f diffl l)(x) =
      ?g. (!z. f(z) - f(x) = g(z) * (z - x)) /\ g contl x /\ (g(x) = l)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [EXISTS_TAC `\z. (z = x) => l | (f(z) - f(x)) / (z - x)` THEN
    BETA_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real` THEN LCOND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
      ASM_REWRITE_TAC[REAL_SUB_0];
      POP_ASSUM MP_TAC THEN MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
      REWRITE_TAC[diffl; contl] THEN BETA_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC LIM_EQUAL THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
      ASM_REWRITE_TAC[REAL_ADD_RID_UNIQ; REAL_ADD_SUB]];
    POP_ASSUM(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN UNDISCH_TAC `g contl x` THEN
    ASM_REWRITE_TAC[contl; diffl; REAL_ADD_SUB] THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
    MATCH_MP_TAC LIM_EQUAL THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
    REWRITE_TAC[REAL_MUL_RID]]);;

(*----------------------------------------------------------------------------*)
(* Now the chain rule                                                         *)
(*----------------------------------------------------------------------------*)

let DIFF_CHAIN = prove(
  `!f g l m x.
     (f diffl l)(g x) /\ (g diffl m)(x) ==> ((\x. f(g x)) diffl (l * m))(x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(fun th -> MP_TAC th THEN ASSUME_TAC(MATCH_MP DIFF_CONT th)) THEN
  REWRITE_TAC[DIFF_CARAT] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real->real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z. (z = x) => l * m | (f(g(z):real) - f(g(x))) / (z - x)` THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN LCOND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REWRITE_TAC[REAL_SUB_0];
    MP_TAC(CONJ (ASSUME `g contl x`) (ASSUME `f' contl (g(x:real))`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONT_COMPOSE) THEN
    DISCH_THEN(MP_TAC o C CONJ (ASSUME `g' contl x`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONT_MUL) THEN BETA_TAC THEN
    ASM_REWRITE_TAC[contl] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
    MATCH_MP_TAC LIM_EQUAL THEN X_GEN_TAC `z:real` THEN
    DISCH_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RID_UNIQ] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_ADD_SUB] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
    REWRITE_TAC[REAL_MUL_RID]]);;

(*----------------------------------------------------------------------------*)
(* Differentiation of natural number powers                                   *)
(*----------------------------------------------------------------------------*)

let DIFF_X = prove(
  `!x. ((\x. x) diffl &1)(x)`,
  GEN_TAC THEN REWRITE_TAC[diffl] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD_SUB] THEN REWRITE_TAC[LIM; REAL_SUB_RZERO] THEN
  BETA_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP REAL_DIV_REFL th]) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; ABS_0]);;

let DIFF_POW = prove(
  `!n x. ((\x. x pow n) diffl (&n * (x pow (n - 1))))(x)`,
  INDUCT_TAC THEN REWRITE_TAC[pow; DIFF_CONST; REAL_MUL_LZERO] THEN
  X_GEN_TAC `x:real` THEN
  POP_ASSUM(MP_TAC o CONJ(SPEC `x:real` DIFF_X) o SPEC `x:real`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  REWRITE_TAC[REAL; REAL_RDISTRIB; REAL_MUL_LID] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN BINOP_TAC THENL
   [REWRITE_TAC[ADD1; ADD_SUB];
    STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[ADD1; ADD_SUB; POW_ADD] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[num_CONV `1`; pow] THEN
    REWRITE_TAC[SYM(num_CONV `1`); REAL_MUL_RID]]);;

(*----------------------------------------------------------------------------*)
(* Now power of -1 (then differentiation of inverses follows from chain rule) *)
(*----------------------------------------------------------------------------*)

let DIFF_XM1 = prove(
  `!x. ~(x = &0) ==> ((\x. inv(x)) diffl (--(inv(x) pow 2)))(x)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[diffl] THEN BETA_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\h. --(inv(x + h) * inv(x))` THEN
  BETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `abs(x)` THEN
    EVERY_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[ABS_NZ] th]) THEN
    X_GEN_TAC `h:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN BETA_TAC THEN
    W(C SUBGOAL_THEN SUBST1_TAC o C (curry mk_eq) `&0` o
      rand o rator o snd) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ABS_ZERO; REAL_SUB_0] THEN
    SUBGOAL_THEN `~(x + h = &0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LNEG_UNIQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `abs(h) < abs(--h)` THEN
      REWRITE_TAC[ABS_NEG; REAL_LT_REFL]; ALL_TAC] THEN
    W(fun (asl,w) -> MP_TAC
        (SPECL [`x * (x + h)`; lhs w; rhs w] REAL_EQ_LMUL)) THEN
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[real_div; REAL_SUB_LDISTRIB; REAL_SUB_RDISTRIB] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
      `(a * b) * (c * d) = (c * b) * (d * a)`] THEN
    REWRITE_TAC(map (MATCH_MP REAL_MUL_LINV o ASSUME)
     [`~(x = &0)`; `~(x + h = &0)`]) THEN REWRITE_TAC[REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
      `(a * b) * (c * d) = (a * d) * (c * b)`] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME `~(x = &0)`)] THEN
    REWRITE_TAC[REAL_MUL_LID; GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REWRITE_RULE[REAL_NEG_SUB]
      (AP_TERM `(--)` (SPEC_ALL REAL_ADD_SUB))] THEN
    REWRITE_TAC[GSYM REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[ABS_NZ];

    REWRITE_TAC[POW_2] THEN
    CONV_TAC(EXACT_CONV[X_BETA_CONV `h:real` `inv(x + h) * inv(x)`]) THEN
    REWRITE_TAC[GSYM LIM_NEG] THEN
    CONV_TAC(EXACT_CONV(map (X_BETA_CONV `h:real`) [`inv(x + h)`; `inv(x)`]))
    THEN MATCH_MP_TAC LIM_MUL THEN BETA_TAC THEN
    REWRITE_TAC[LIM_CONST] THEN
    CONV_TAC(EXACT_CONV[X_BETA_CONV `h:real` `x + h`]) THEN
    MATCH_MP_TAC LIM_INV THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
    CONV_TAC(EXACT_CONV(map (X_BETA_CONV `h:real`) [`x:real`; `h:real`])) THEN
    MATCH_MP_TAC LIM_ADD THEN BETA_TAC THEN REWRITE_TAC[LIM_CONST] THEN
    MATCH_ACCEPT_TAC LIM_X]);;

(*----------------------------------------------------------------------------*)
(* Now differentiation of inverse and quotient                                *)
(*----------------------------------------------------------------------------*)

let DIFF_INV = prove(
  `!f l x. (f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl --(l / (f(x) pow 2)))(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div; REAL_NEG_RMUL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN DISCH_TAC THEN
  MATCH_MP_TAC DIFF_CHAIN THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP POW_INV (CONJUNCT2 th)]) THEN
  MATCH_MP_TAC(CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) DIFF_XM1) THEN
  ASM_REWRITE_TAC[]);;

let DIFF_DIV = prove(
  `!f g l m. (f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[real_div] THEN
  MP_TAC(SPECL [`g:real->real`; `m:real`; `x:real`] DIFF_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJ(ASSUME `(f diffl l)(x)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  W(C SUBGOAL_THEN SUBST1_TAC o mk_eq o
      ((rand o rator) F_F (rand o rator)) o dest_imp o snd) THEN
  REWRITE_TAC[] THEN REWRITE_TAC[real_sub] THEN
  REWRITE_TAC[REAL_LDISTRIB; REAL_RDISTRIB] THEN BINOP_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[POW_2] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_INV_MUL_WEAK (W CONJ th)]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
    REWRITE_TAC[REAL_MUL_LID];
    REWRITE_TAC[real_div; GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL] THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_AC]]);;

(*----------------------------------------------------------------------------*)
(* Differentiation of finite sum                                              *)
(*----------------------------------------------------------------------------*)

let DIFF_SUM = prove(
  `!f f' m n x. (!r. m <= r /\ r < (m + n)
                 ==> ((\x. f r x) diffl (f' r x))(x))
     ==> ((\x. Sum(m,n)(\n. f n x)) diffl (Sum(m,n) (\r. f' r x)))(x)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[Sum; DIFF_CONST] THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC DIFF_ADD THEN
  BETA_TAC THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `m + n:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES; LESS_SUC_REFL];
    REWRITE_TAC[LE_ADD; ADD_CLAUSES; LESS_SUC_REFL]]);;

(*----------------------------------------------------------------------------*)
(* By bisection, function continuous on closed interval is bounded above      *)
(*----------------------------------------------------------------------------*)

let CONT_BOUNDED = prove(
  `!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. !x. a <= x /\ x <= b ==> f(x) <= M`,
  REPEAT STRIP_TAC THEN
  (MP_TAC o C SPEC BOLZANO_LEMMA)
    `\(u,v). a <= u /\ u <= v /\ v <= b ==>
               ?M. !x. u <= x /\ x <= v ==> f x <= M` THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o
  funpow 2(fst o dest_imp) o snd) THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL [`a:real`; `b:real`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `w:real`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    DISCH_TAC THEN
    REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `v <= b` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `w:real` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `a <= v` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `u:real` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `M1:real`) THEN
    DISCH_THEN(X_CHOOSE_TAC `M2:real`) THEN
    DISJ_CASES_TAC(SPECL [`M1:real`; `M2:real`] REAL_LE_TOTAL) THENL
     [EXISTS_TAC `M2:real` THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      DISJ_CASES_TAC(SPECL [`x:real`; `v:real`] REAL_LE_TOTAL) THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M1:real` THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `M1:real` THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      DISJ_CASES_TAC(SPECL [`x:real`; `v:real`] REAL_LE_TOTAL) THENL
       [ALL_TAC; MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `M2:real` THEN ASM_REWRITE_TAC[]] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN ASM_CASES_TAC `a <= x /\ x <= b` THENL
   [ALL_TAC;
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC `~(a <= x /\ x <= b)` THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `u:real`; EXISTS_TAC `v:real`] THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `!x. a <= x /\ x <= b ==> f contl x` THEN
  DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[contl; LIM] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `abs(f(x:real)) + &1` THEN
  X_GEN_TAC `z:real` THEN STRIP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(MP_TAC o SPEC `z - x`) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`f(z:real) - f(x)`; `(f:real->real) x`] ABS_TRIANGLE) THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[REAL_ADD_SYM]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(f(z:real))` THEN
  REWRITE_TAC[ABS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(f(x:real)) + (abs(f(z) - f(x)))` THEN
  ASM_REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  ASM_CASES_TAC `z:real = x` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; ABS_0; REAL_LT_01];
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GSYM ABS_NZ] THEN
    ASM_REWRITE_TAC[REAL_SUB_0; real_abs; REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_NEG_SUB] THEN LCOND_CASES_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `v - u` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `v - x`; EXISTS_TAC `v - z`] THEN
    ASM_REWRITE_TAC[real_sub; REAL_LE_RADD; REAL_LE_LADD; REAL_LE_NEG]]);;

(*----------------------------------------------------------------------------*)
(* Refine the above to existence of least upper bound                         *)
(*----------------------------------------------------------------------------*)

let CONT_HASSUP = prove(
  `!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (!N. N < M ==> ?x. a <= x /\ x <= b /\ N < f(x))`,
  let tm = `\y:real. ?x. a <= x /\ x <= b /\ (y = f(x))` in
  REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC tm REAL_SUP_LE) THEN
  BETA_TAC THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd)
  THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`(f:real->real) a`; `a:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_LT];
      POP_ASSUM(X_CHOOSE_TAC `M:real` o MATCH_MP CONT_BOUNDED) THEN
      EXISTS_TAC `M:real` THEN X_GEN_TAC `y:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real` MP_TAC) THEN
      REWRITE_TAC[CONJ_ASSOC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
      POP_ASSUM MATCH_ACCEPT_TAC];
    DISCH_TAC THEN EXISTS_TAC (mk_comb(`sup`,tm)) THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC (mk_comb(`sup`,tm))) THEN
      REWRITE_TAC[REAL_LT_REFL] THEN
      CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      DISCH_THEN(MP_TAC o SPEC `(f:real->real) x`) THEN
      REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LT] THEN
      CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `N:real`) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real` MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real` MP_TAC) THEN
      REWRITE_TAC[CONJ_ASSOC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
      DISCH_TAC THEN EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[]]]);;

(*----------------------------------------------------------------------------*)
(* Now show that it attains its upper bound                                   *)
(*----------------------------------------------------------------------------*)

let CONT_ATTAINS = prove(
  `!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC o MATCH_MP CONT_HASSUP)
  THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
  CONV_TAC(RAND_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) = a /\ b ==> ~c`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x. a <= x /\ x <= b ==> f(x) < M` MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  PURE_ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. a <= x /\ x <= b ==> (\x. inv(M - f(x))) contl x`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN
    MATCH_MP_TAC CONT_INV THEN BETA_TAC THEN
    REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN
    MATCH_MP_TAC CONT_SUB THEN BETA_TAC THEN
    REWRITE_TAC[CONT_CONST] THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?k. !x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x <= k`
  MP_TAC THENL
   [MATCH_MP_TAC CONT_BOUNDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
  SUBGOAL_THEN `!x. a <= x /\ x <= b ==> &0 < inv(M - f(x))` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_INV_POS THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x < (k + &1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `k:real` THEN REWRITE_TAC[REAL_LT_ADDR; REAL_LT_01] THEN
    BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. a <= x /\ x <= b ==>
         inv(k + &1) < inv((\x. inv(M - (f x))) x)` MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    CONJ_TAC THENL
     [BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. a <= x /\ x <= b ==> inv(k + &1) < (M - (f x))`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(M - f(x:real) = &0)`
      (SUBST1_TAC o SYM o MATCH_MP REAL_INVINV) THENL
     [CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_SUB_LADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LT_SUB_LADD] THEN DISCH_TAC THEN
  UNDISCH_TAC `!N. N < M ==> (?x. a <= x /\ x <= b /\ N < (f x))` THEN
  DISCH_THEN(MP_TAC o SPEC `M - inv(k + &1)`) THEN
  REWRITE_TAC[REAL_LT_SUB_RADD; REAL_LT_ADDR] THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `k:real` THEN REWRITE_TAC[REAL_LT_ADDR; REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(M - f(a:real))` THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    DISCH_THEN(X_CHOOSE_THEN `x:real` MP_TAC) THEN REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_SUB_LADD] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* Same theorem for lower bound                                               *)
(*----------------------------------------------------------------------------*)

let CONT_ATTAINS2 = prove(
  `!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> M <= f(x)) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `!x. a <= x /\ x <= b ==> (\x. --(f x)) contl x` MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONT_NEG THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME `a <= b`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` MP_TAC o MATCH_MP CONT_ATTAINS) THEN
  BETA_TAC THEN DISCH_TAC THEN EXISTS_TAC `--M` THEN CONJ_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_REWRITE_TAC[REAL_NEGNEG];
    ASM_REWRITE_TAC[GSYM REAL_NEG_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Another version.                                                          *)
(* ------------------------------------------------------------------------- *)

let CONT_ATTAINS_ALL = prove(
  `!f a b. (a <= b /\ !x. a <= x /\ x <= b ==>  f contl x)
        ==> ?L M. (!x. a <= x /\ x <= b ==> L <= f(x) /\ f(x) <= M) /\
                  !y. L <= y /\ y <= M ==> ?x. a <= x /\ x <= b /\ (f(x) = y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `L:real` MP_TAC o MATCH_MP CONT_ATTAINS2) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `M:real` MP_TAC o MATCH_MP CONT_ATTAINS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `x2:real` STRIP_ASSUME_TAC) THEN
   MAP_EVERY EXISTS_TAC [`L:real`; `M:real`] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_TAC(SPECL [`x1:real`; `x2:real`] REAL_LE_TOTAL) THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`f:real->real`; `x1:real`; `x2:real`; `y:real`] IVT) THEN
    ASM_REWRITE_TAC[] THEN W(C SUBGOAL_THEN
    (fun t -> REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd) THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2);
      DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN

      ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[]] THEN
    (CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
      [EXISTS_TAC `x1:real`; EXISTS_TAC `x2:real`] THEN
     ASM_REWRITE_TAC[]);
    MP_TAC(SPECL [`f:real->real`; `x2:real`; `x1:real`; `y:real`] IVT2) THEN
    ASM_REWRITE_TAC[] THEN W(C SUBGOAL_THEN
    (fun t -> REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd) THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2);
      DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
     ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[]] THEN
    (CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
      [EXISTS_TAC `x2:real`; EXISTS_TAC `x1:real`] THEN
     ASM_REWRITE_TAC[])]);;

(*----------------------------------------------------------------------------*)
(* If f'(x) > 0 then x is locally strictly increasing at the right            *)
(*----------------------------------------------------------------------------*)

let DIFF_LINC = prove(
  `!f x l. (f diffl l)(x) /\ &0 < l ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x + h)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[diffl; LIM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `l:real`) THEN ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INV_POS o CONJUNCT1) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_RMUL_EQ th)]) THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC ABS_SIGN THEN EXISTS_TAC `l:real` THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o CONJUNCT1) THEN
  ASM_REWRITE_TAC[real_abs]);;

(*----------------------------------------------------------------------------*)
(* If f'(x) < 0 then x is locally strictly increasing at the left             *)
(*----------------------------------------------------------------------------*)

let DIFF_LDEC = prove(
  `!f x l. (f diffl l)(x) /\ l < &0 ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x - h)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[diffl; LIM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `--l`) THEN
  ONCE_REWRITE_TAC[GSYM REAL_NEG_LT0] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INV_POS o CONJUNCT1) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_RMUL_EQ th)]) THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM REAL_NEG_LT0; REAL_NEG_RMUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_NEG_INV
   (GSYM (MATCH_MP REAL_LT_IMP_NE (CONJUNCT1 th)))]) THEN
  MATCH_MP_TAC ABS_SIGN2 THEN EXISTS_TAC `l:real` THEN
  REWRITE_TAC[GSYM real_div] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o funpow 3 LAND_CONV o RAND_CONV)
    [real_sub] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o CONJUNCT1) THEN
  REWRITE_TAC[real_abs; GSYM REAL_NEG_LE0; REAL_NEGNEG] THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT]);;

(*----------------------------------------------------------------------------*)
(* If f is differentiable at a local maximum x, f'(x) = 0                     *)
(*----------------------------------------------------------------------------*)

let DIFF_LMAX = prove(
  `!f x l. (f diffl l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(y) <= f(x))) ==> (l = &0)`,
  REPEAT GEN_TAC THEN DISCH_THEN
   (CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC)) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [`l:real`; `&0`] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o C CONJ(ASSUME `l < &0`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_LDEC) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPECL [`k:real`; `e:real`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC `x - d`) THEN REWRITE_TAC[REAL_SUB_SUB2] THEN
    SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[real_abs] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT];
    DISCH_THEN(MP_TAC o C CONJ(ASSUME `&0 < l`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_LINC) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPECL [`k:real`; `e:real`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC `x + d`) THEN REWRITE_TAC[REAL_ADD_SUB2] THEN
    SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ABS_NEG] THEN
    ASM_REWRITE_TAC[real_abs] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT]]);;

(*----------------------------------------------------------------------------*)
(* Similar theorem for a local minimum                                        *)
(*----------------------------------------------------------------------------*)

let DIFF_LMIN = prove(
  `!f x l. (f diffl l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(x) <= f(y))) ==> (l = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`\x:real. --(f x)`; `x:real`; `--l`] DIFF_LMAX) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_LE_NEG; REAL_NEG_EQ0] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFF_NEG THEN ASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* In particular if a function is locally flat                                *)
(*----------------------------------------------------------------------------*)

let DIFF_LCONST = prove(
  `!f x l. (f diffl l)(x) /\
         (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x)))) ==> (l = &0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC DIFF_LMAX THEN
  MAP_EVERY EXISTS_TAC [`f:real->real`; `x:real`] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(SUBST1_TAC o C MATCH_MP th)) THEN
  MATCH_ACCEPT_TAC REAL_LE_REFL);;

(*----------------------------------------------------------------------------*)
(* Lemma about introducing open ball in open interval                         *)
(*----------------------------------------------------------------------------*)

let INTERVAL_LEMMA_LT = prove(
  `!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a < y /\ y < b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ABS_BETWEEN] THEN
  DISJ_CASES_TAC(SPECL [`x - a`; `b - x`] REAL_LE_TOTAL) THENL
   [EXISTS_TAC `x - a`; EXISTS_TAC `b - x`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN GEN_TAC THEN
  REWRITE_TAC[REAL_LT_SUB_LADD; REAL_LT_SUB_RADD] THEN
  REWRITE_TAC[real_sub; REAL_ADD_ASSOC] THEN
  REWRITE_TAC[GSYM real_sub; REAL_LT_SUB_LADD; REAL_LT_SUB_RADD] THEN
  FREEZE_THEN(fun th -> ONCE_REWRITE_TAC[th]) (SPEC `x:real` REAL_ADD_SYM) THEN
  REWRITE_TAC[REAL_LT_RADD] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (MATCH_MP_TAC o GEN_ALL o fst o EQ_IMP_RULE o SPEC_ALL) REAL_LT_RADD THENL
   [EXISTS_TAC `a:real` THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `x + x` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x - a) <= (b - x)`;
     EXISTS_TAC `b:real` THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `x + x` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(b - x) <= (x - a)`] THEN
  REWRITE_TAC[REAL_LE_SUB_LADD; GSYM REAL_LE_SUB_RADD] THEN
  MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_sub] THEN
  REWRITE_TAC[REAL_ADD_AC]);;

let INTERVAL_LEMMA = prove(
  `!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a <= y /\ y <= b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `d:real` o MATCH_MP INTERVAL_LEMMA_LT) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th o CONJUNCT2)) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Now Rolle's theorem                                                        *)
(*----------------------------------------------------------------------------*)

let ROLLE = prove(
  `!f a b. a < b /\
           (f(a) = f(b)) /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?z. a < z /\ z < b /\ (f diffl &0)(z)`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MP_TAC(SPECL [`f:real->real`; `a:real`; `b:real`] CONT_ATTAINS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `x1:real`)) THEN
  MP_TAC(SPECL [`f:real->real`; `a:real`; `b:real`] CONT_ATTAINS2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `x2:real`)) THEN
  ASM_CASES_TAC `a < x1 /\ x1 < b` THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `d:real` MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN EXISTS_TAC `x1:real` THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN
     `?l. (f diffl l)(x1) /\
          ?d. &0 < d /\ (!y. abs(x1 - y) < d ==> f(y) <= f(x1))` MP_TAC THENL
     [CONV_TAC EXISTS_AND_CONV THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN
        DISCH_TAC THEN REPEAT(FIRST_ASSUM MATCH_MP_TAC) THEN
        ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` MP_TAC) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
                         SUBST_ALL_TAC(MATCH_MP DIFF_LMAX th))
    THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `a < x2 /\ x2 < b` THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `d:real` MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN EXISTS_TAC `x2:real` THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN
     `?l. (f diffl l)(x2) /\
          ?d. &0 < d /\ (!y. abs(x2 - y) < d ==> f(x2) <= f(y))` MP_TAC THENL
     [CONV_TAC EXISTS_AND_CONV THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN
        DISCH_TAC THEN REPEAT(FIRST_ASSUM MATCH_MP_TAC) THEN
        ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` MP_TAC) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
                         SUBST_ALL_TAC(MATCH_MP DIFF_LMIN th)) THEN
  ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. a <= x /\ x <= b ==> (f(x):real = f(b))` MP_TAC THENL
   [REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl)) THEN
    ASM_REWRITE_TAC[REAL_LT_LE] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    REPEAT (DISCH_THEN(DISJ_CASES_THEN2 (MP_TAC o SYM) MP_TAC) THEN
            DISCH_THEN(SUBST_ALL_TAC o AP_TERM `f:real->real`)) THEN
    UNDISCH_TAC `(f:real->real) a = f b` THEN
    DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    (CONJ_TAC THENL
      [SUBGOAL_THEN `(f:real->real) b = M` SUBST1_TAC THENL
        [FIRST_ASSUM(ACCEPT_TAC o el 2 o CONJUNCTS);
         FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
       SUBGOAL_THEN `(f:real->real) b = m` SUBST1_TAC THENL
        [FIRST_ASSUM(ACCEPT_TAC o el 2 o CONJUNCTS);
         FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);
    X_CHOOSE_TAC `x:real` (MATCH_MP REAL_MEAN (ASSUME `a < b`)) THEN
    DISCH_TAC THEN EXISTS_TAC `x:real` THEN
    REWRITE_TAC[ASSUME `a < x /\ x < b`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?l. (f diffl l)(x) /\
        (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x))))` MP_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV EXISTS_AND_CONV) THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
        DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
        DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
        DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `l:real` (fun th ->
       ASSUME_TAC th THEN SUBST_ALL_TAC(MATCH_MP DIFF_LCONST th))) THEN
      ASM_REWRITE_TAC[]]]);;

(*----------------------------------------------------------------------------*)
(* Mean value theorem                                                         *)
(*----------------------------------------------------------------------------*)

let MVT_LEMMA = prove(
  `!(f:real->real) a b.
        (\x. f(x) - (((f(b) - f(a)) / (b - a)) * x))(a) =
        (\x. f(x) - (((f(b) - f(a)) / (b - a)) * x))(b)`,
  REPEAT GEN_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC `b:real = a` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_0]) THEN
  MP_TAC(GENL [`x:real`; `y:real`]
   (SPECL [`x:real`; `y:real`; `b - a`] REAL_EQ_RMUL)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_DIV_RMUL th]) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[real_sub; REAL_LDISTRIB; REAL_RDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL;
              REAL_NEG_ADD; REAL_NEGNEG] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  REWRITE_TAC[AC REAL_ADD_AC
    `w + x + y + z = (y + w) + (x + z)`; REAL_ADD_LINV; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_ADD_RID]);;

let MVT = prove(
  `!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?l z. a < z /\ z < b /\ (f diffl l)(z) /\
            (f(b) - f(a) = (b - a) * l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\x. f(x) - (((f(b) - f(a)) / (b - a)) * x)`;
                `a:real`; `b:real`] ROLLE) THEN
  W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
  funpow 2 (fst o dest_imp) o snd) THENL
   [ASM_REWRITE_TAC[MVT_LEMMA] THEN BETA_TAC THEN
    CONJ_TAC THEN X_GEN_TAC `x:real` THENL
     [DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN
      MATCH_MP_TAC CONT_SUB THEN CONJ_TAC THENL
       [CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC CONT_MUL THEN
        REWRITE_TAC[CONT_CONST] THEN MATCH_MP_TAC DIFF_CONT THEN
        EXISTS_TAC `&1` THEN MATCH_ACCEPT_TAC DIFF_X];
      DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[differentiable] THEN DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
      EXISTS_TAC `l - ((f(b) - f(a)) / (b - a))` THEN
      CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC DIFF_SUB THEN
      CONJ_TAC THENL
       [CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN FIRST_ASSUM ACCEPT_TAC;
        CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC DIFF_CMUL THEN MATCH_ACCEPT_TAC DIFF_X]];
    ALL_TAC] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(X_CHOOSE_THEN `z:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(prefix THEN (MAP_EVERY EXISTS_TAC
   [`((f(b) - f(a)) / (b - a))`; `z:real`]) o MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(prefix THEN CONJ_TAC o MP_TAC) THENL
   [ALL_TAC; DISCH_THEN(K ALL_TAC) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC[REAL_SUB_0] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `a < a` THEN
    REWRITE_TAC[REAL_LT_REFL]] THEN
  SUBGOAL_THEN `((\x. ((f(b) - f(a)) / (b - a)) * x ) diffl
                      ((f(b) - f(a)) / (b - a)))(z)`
  (fun th -> DISCH_THEN(MP_TAC o C CONJ th)) THENL
   [CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC DIFF_CMUL THEN REWRITE_TAC[DIFF_X]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  REWRITE_TAC[REAL_ADD_LID]);;

(*----------------------------------------------------------------------------*)
(* Theorem that function is constant if its derivative is 0 over an interval. *)
(*                                                                            *)
(* We could have proved this directly by bisection; consider instantiating    *)
(* BOLZANO_LEMMA with                                                         *)
(*                                                                            *)
(*     \(x,y). f(y) - f(x) <= C * (y - x)                                     *)
(*                                                                            *)
(* However the Rolle and Mean Value theorems are useful to have anyway        *)
(*----------------------------------------------------------------------------*)

let DIFF_ISCONST_END = prove(
  `!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> (f b = f a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:real->real`; `a:real`; `b:real`] MVT) THEN
  ASM_REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [GEN_TAC THEN REWRITE_TAC[differentiable] THEN
    DISCH_THEN(prefix THEN (EXISTS_TAC `&0`) o MP_TAC) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` (X_CHOOSE_THEN `x:real` MP_TAC)) THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d = (a /\ b) /\ (c /\ d)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME `(f diffl l)(x)`)) THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP DIFF_UNIQ) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_RZERO; REAL_SUB_0]) THEN
  FIRST_ASSUM ACCEPT_TAC);;

let DIFF_ISCONST = prove(
  `!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> !x. a <= x /\ x <= b ==> (f x = f a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:real->real`; `a:real`; `x:real`] DIFF_ISCONST_END) THEN
  DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME `a <= x`)) THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN X_GEN_TAC `z:real` THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x:real`;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `x:real`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let DIFF_ISCONST_ALL = prove(
  `!f. (!x. (f diffl &0)(x)) ==> (!x y. f(x) = f(y))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. f contl x` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN MP_TAC
   (SPECL [`x:real`; `y:real`] REAL_LT_TOTAL) THENL
   [DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    CONV_TAC(RAND_CONV SYM_CONV);
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC DIFF_ISCONST_END THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Boring lemma about distances                                             *)
(* ------------------------------------------------------------------------ *)

let INTERVAL_ABS = prove(
  `!x z d. (x - d) <= z /\ z <= (x + d) = abs(z - x) <= d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_abs; REAL_LE_SUB_RADD] THEN EQ_TAC THENL
   [STRIP_TAC THEN LCOND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_SUB_RADD; REAL_NEG_SUB] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_SUB_LE] THEN LCOND_CASES_TAC THEN
    REWRITE_TAC[REAL_NEG_SUB; REAL_LE_SUB_RADD] THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(MATCH_MP REAL_LT_IMP_LE o REWRITE_RULE[REAL_NOT_LE])] THEN
    DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[REAL_ADD_SYM]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `x + d`; EXISTS_TAC `z + d`] THEN
    ASM_REWRITE_TAC[REAL_LE_RADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `z:real`; EXISTS_TAC `x:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------ *)
(* Dull lemma that an continuous injection on an interval must have a strict*)
(* maximum at an end point, not in the middle.                              *)
(* ------------------------------------------------------------------------ *)

let CONT_INJ_LEMMA = prove(
  `!f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(z) <= f(x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  IMP_RES_THEN ASSUME_TAC REAL_LT_IMP_LE THEN
  DISCH_THEN(fun th -> MAP_EVERY (MP_TAC o C SPEC th) [`x - d`; `x + d`]) THEN
  REWRITE_TAC[REAL_ADD_SUB; REAL_SUB_SUB; ABS_NEG] THEN
  ASM_REWRITE_TAC[real_abs; REAL_LE_REFL] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISJ_CASES_TAC
    (SPECL [`f(x - d):real`; `f(x + d):real`] REAL_LE_TOTAL) THENL
   [MP_TAC(SPECL [`f:real->real`; `x - d`; `x:real`; `f(x + d):real`] IVT) THEN
    ASM_REWRITE_TAC[REAL_LE_SUB_RADD; REAL_LE_ADDR] THEN
    W(C SUBGOAL_THEN MP_TAC o fst o dest_imp o dest_neg o snd) THENL
     [X_GEN_TAC `z:real` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
      REWRITE_TAC[real_abs; REAL_SUB_LE] THEN
      ASM_REWRITE_TAC[REAL_NEG_SUB; REAL_SUB_LE; REAL_LE_SUB_RADD] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o AP_TERM `g:real->real`) THEN
      SUBGOAL_THEN `g((f:real->real) z) = z` SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
        REWRITE_TAC[real_abs; REAL_SUB_LE] THEN
        ASM_REWRITE_TAC[REAL_NEG_SUB; REAL_SUB_LE; REAL_LE_SUB_RADD] THEN
        ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `g(f(x + d):real) = x + d` SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_ADD_SUB] THEN
        ASM_REWRITE_TAC[real_abs; REAL_LE_REFL]; ALL_TAC] THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x:real` THEN
      ASM_REWRITE_TAC[REAL_LT_ADDR]];
    MP_TAC(SPECL [`f:real->real`; `x:real`; `x + d`; `f(x - d):real`] IVT2) THEN
    ASM_REWRITE_TAC[REAL_LE_SUB_RADD; REAL_LE_ADDR] THEN
    W(C SUBGOAL_THEN MP_TAC o fst o dest_imp o dest_neg o snd) THENL
     [X_GEN_TAC `z:real` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[real_abs; REAL_SUB_LE; REAL_LE_SUB_RADD] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o AP_TERM `g:real->real`) THEN
      SUBGOAL_THEN `g((f:real->real) z) = z` SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[real_abs; REAL_SUB_LE; REAL_LE_SUB_RADD] THEN
        ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `g(f(x - d):real) = x - d` SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[REAL_SUB_SUB; ABS_NEG] THEN
        ASM_REWRITE_TAC[real_abs; REAL_LE_REFL]; ALL_TAC] THEN
      REWRITE_TAC[] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `x:real` THEN
      ASM_REWRITE_TAC[REAL_LT_SUB_RADD; REAL_LT_ADDR]]]);;

(* ------------------------------------------------------------------------ *)
(* Similar version for lower bound                                          *)
(* ------------------------------------------------------------------------ *)

let CONT_INJ_LEMMA2 = prove(
  `!f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(x) <= f(z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. --(f x)`; `\y. (g(--y):real)`; `x:real`; `d:real`]
    CONT_INJ_LEMMA) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_NEGNEG; REAL_LE_NEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONT_NEG THEN
  FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------ *)
(* Show there's an interval surrounding f(x) in f[[x - d, x + d]]           *)
(* ------------------------------------------------------------------------ *)

let CONT_INJ_RANGE = prove(
  `!f g x d.  &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
        ?e. &0 < e /\
            (!y. abs(y - f(x)) <= e ==> ?z. abs(z - x) <= d /\ (f z = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  IMP_RES_THEN ASSUME_TAC REAL_LT_IMP_LE THEN
  MP_TAC(SPECL [`f:real->real`; `x - d`; `x + d`] CONT_ATTAINS_ALL) THEN
  ASM_REWRITE_TAC[INTERVAL_ABS; REAL_LE_SUB_RADD] THEN
  ASM_REWRITE_TAC[GSYM REAL_ADD_ASSOC; REAL_LE_ADDR; REAL_LE_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (X_CHOOSE_THEN `M:real` MP_TAC)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `L <= f(x:real) /\ f(x) <= M` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; ABS_0]; ALL_TAC] THEN
  SUBGOAL_THEN `L < f(x:real) /\ f(x:real) < M` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THENL
     [DISCH_THEN SUBST_ALL_TAC THEN (MP_TAC o C SPECL CONT_INJ_LEMMA2)
        [`f:real->real`; `g:real->real`; `x:real`; `d:real`];
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN (MP_TAC o C SPECL CONT_INJ_LEMMA)
        [`f:real->real`; `g:real->real`; `x:real`; `d:real`]] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    DISCH_THEN(fun t -> FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th t] THEN
      NO_TAC));
    MP_TAC(SPECL [`f(x:real) - L`; `M - f(x:real)`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM INTERVAL_ABS] THEN
    REWRITE_TAC[REAL_LE_SUB_RADD] THEN ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `abs(y - f(x:real)) <= e` THEN
    REWRITE_TAC[GSYM INTERVAL_ABS] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `f(x:real) - e` THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_LE_SUB_LADD] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      REWRITE_TAC[GSYM REAL_LE_SUB_LADD];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `f(x:real) + (M - f(x))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `f(x:real) + e` THEN
        ASM_REWRITE_TAC[REAL_LE_LADD];
        REWRITE_TAC[REAL_SUB_ADD2; REAL_LE_REFL]]] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------ *)
(* Continuity of inverse function                                           *)
(* ------------------------------------------------------------------------ *)

let CONT_INVERSE = prove(
  `!f g x d. &0 < d /\
             (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
             (!z. abs(z - x) <= d ==> f contl z)
        ==> g contl (f x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[contl; LIM] THEN
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:real`; `d:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  IMP_RES_THEN ASSUME_TAC REAL_LT_IMP_LE THEN
  SUBGOAL_THEN `!z. abs(z - x) <= e ==> (g(f z :real) = z)` ASSUME_TAC THENL
   [X_GEN_TAC `z:real` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. abs(z - x) <= e ==> (f contl z)` ASSUME_TAC THENL
   [X_GEN_TAC `z:real` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `!z. abs(z - x) <= d ==> (g(f z :real) = z)` THEN
  UNDISCH_TAC `!z. abs(z - x) <= d ==> (f contl z)` THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(K ALL_TAC) THEN
  (MP_TAC o C SPECL CONT_INJ_RANGE)
    [`f:real->real`; `g:real->real`; `x:real`; `e:real`] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:real` THEN BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
    (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPEC `f(x:real) + h` th) THEN
    REWRITE_TAC[REAL_ADD_SUB; ASSUME `abs(h) <= k`] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e:real` THEN
  SUBGOAL_THEN `(g((f:real->real)(z)) = z) /\ (g(f(x)) = x)`
    (fun t -> ASM_REWRITE_TAC[t]) THEN CONJ_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; ABS_0]);;

(* ------------------------------------------------------------------------ *)
(* Differentiability of inverse function                                    *)
(* ------------------------------------------------------------------------ *)

let DIFF_INVERSE = prove(
  `!f g l x d. &0 < d /\
               (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) <= d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `(f diffl l)(x)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP DIFF_CONT th) THEN MP_TAC th) THEN
  REWRITE_TAC[DIFF_CARAT] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y. (y = f(x)) =>
    inv(h(g y)) | (g(y) - g(f(x:real))) / (y - f(x))` THEN BETA_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real` THEN LCOND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REWRITE_TAC[REAL_SUB_0];
    ALL_TAC;
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REPEAT AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; ABS_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `g((f:real->real)(x)) = x` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_SUB_REFL; ABS_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN EXISTS_TAC `\y:real. inv(h(g(y):real))` THEN
  BETA_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    (SUBST1_TAC o SYM o ONCE_DEPTH_CONV BETA_CONV)
      `\y. inv((\y:real. h(g(y):real)) y)` THEN
    MATCH_MP_TAC LIM_INV THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\y:real. h(g(y):real)) contl (f(x:real))` MP_TAC THENL
     [MATCH_MP_TAC CONT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONT_INVERSE THEN EXISTS_TAC `d:real`;
      REWRITE_TAC[CONTL_LIM] THEN BETA_TAC] THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `?e. &0 < e /\
                    !y. &0 < abs(y - f(x:real)) /\
                        abs(y - f(x:real)) < e ==>
                            (f(g(y)) = y) /\ ~(h(g(y)) = &0)`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LIM] THEN X_GEN_TAC `k:real` THEN DISCH_TAC THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th) THEN
      ASSUME_TAC(REWRITE_RULE[GSYM ABS_NZ; REAL_SUB_0] (CONJUNCT1 th))) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `y - f(x) = h(g(y)) * (g(y) - x)` SUBST1_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
      REWRITE_TAC[ASSUME `f((g:real->real)(y)) = y`];
      UNDISCH_TAC `&0 < k` THEN
      MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN REWRITE_TAC[ABS_ZERO; REAL_SUB_0]] THEN
    SUBGOAL_THEN `~(g(y:real) - x = &0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_SUB_0] THEN
      DISCH_THEN(MP_TAC o AP_TERM `f:real->real`) THEN
      ASM_REWRITE_TAC[]; REWRITE_TAC[real_div]] THEN
    SUBGOAL_THEN `inv((h(g(y))) * (g(y:real) - x)) =
      inv(h(g(y))) * inv(g(y) - x)` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INV_MUL_WEAK THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN
    `?e. &0 < e /\
         !y. &0 < abs(y - f(x:real)) /\ abs(y - f(x)) < e ==> (f(g(y)) = y)`
  (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THENL
   [MP_TAC(SPECL [`f:real->real`; `g:real->real`; `x:real`; `d:real`]
      CONT_INJ_RANGE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real` THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(f:real->real)(z) = y` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `?e. &0 < e /\
         !y. &0 < abs(y - f(x:real)) /\ abs(y - f(x)) < e
                    ==> ~((h:real->real)(g(y)) = &0)`
  (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THENL
   [ALL_TAC;
    MP_TAC(SPECL [`b:real`; `c:real`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `e:real` THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(\y. h(g(y:real):real)) contl (f(x:real))` MP_TAC THENL
   [MATCH_MP_TAC CONT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONT_INVERSE THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONTL_LIM; LIM] THEN DISCH_THEN(MP_TAC o SPEC `abs(l)`) THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[ABS_NZ] THEN X_GEN_TAC `y:real` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ABS_NZ]) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_LZERO; ABS_NEG; REAL_LT_REFL]);;

let DIFF_INVERSE_LT = prove(
  `!f g l x d. &0 < d /\
               (!z. abs(z - x) < d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) < d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_INVERSE THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d / &2` THEN
  ASM_REWRITE_TAC[REAL_LT_HALF2]);;

(* ------------------------------------------------------------------------- *)
(* Every derivative is Darboux continuous.                                   *)
(* ------------------------------------------------------------------------- *)

let IVT_DERIVATIVE_0 = prove
 (`!f f' a b.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) > &0 /\ f'(b) < &0
        ==> ?z. a < z /\ z < b /\ (f'(z) = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_gt] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_LE_LT] THEN
  STRIP_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LT_ANTISYM]] THEN
  SUBGOAL_THEN `?w. (!x. a <= x /\ x <= b ==> f x <= w) /\
                    (?x. a <= x /\ x <= b /\ (f x = w))`
  MP_TAC THENL
   [MATCH_MP_TAC CONT_ATTAINS THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; DIFF_CONT]; ALL_TAC] THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:real` THEN ASM_CASES_TAC `z:real = a` THENL
   [UNDISCH_THEN `z:real = a` SUBST_ALL_TAC  THEN
    MP_TAC(SPECL[`f:real->real`; `a:real`; `(f':real->real) a`] DIFF_LINC) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`d:real`; `b - a`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[REAL_LT_SUB_LADD; REAL_ADD_LID] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `!h. &0 < h /\ h < d ==> w < f (a + h)` THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    ASM_SIMP_TAC[REAL_LE_ADDL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_CASES_TAC `z:real = b` THENL
   [UNDISCH_THEN `z:real = b` SUBST_ALL_TAC  THEN
    MP_TAC(SPECL[`f:real->real`; `b:real`; `(f':real->real) b`] DIFF_LDEC) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`d:real`; `b - a`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[REAL_LT_SUB_LADD; REAL_ADD_LID] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `!h. &0 < h /\ h < d ==> w < f (b - h)` THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LE_SUB_LADD; REAL_LE_SUB_RADD] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    ASM_SIMP_TAC[REAL_LE_ADDL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `a < z /\ z < b` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFF_LMAX THEN
  MP_TAC(SPECL [`z - a`; `b - z`] REAL_DOWN2) THEN
  ASM_REWRITE_TAC[REAL_LT_SUB_LADD; REAL_ADD_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`f:real->real`; `z:real`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
  MAP_EVERY UNDISCH_TAC [`e + z < b`; `e + a < z`] THEN
  REAL_ARITH_TAC);;

let IVT_DERIVATIVE_POS = prove
 (`!f f' a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) > y /\ f'(b) < y
        ==> ?z. a < z /\ z < b /\ (f'(z) = y)`,
  REWRITE_TAC[real_gt] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x. f(x) - y * x`; `\x:real. f'(x) - y`;
                `a:real`; `b:real`] IVT_DERIVATIVE_0) THEN
  ASM_REWRITE_TAC[real_gt] THEN
  ASM_REWRITE_TAC[REAL_LT_SUB_LADD; REAL_LT_SUB_RADD] THEN
  ASM_REWRITE_TAC[REAL_EQ_SUB_RADD; REAL_ADD_LID] THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV o BINDER_CONV o RAND_CONV o
                   LAND_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
  ASM_SIMP_TAC[DIFF_SUB; DIFF_X; DIFF_CMUL]);;

let IVT_DERIVATIVE_NEG = prove
 (`!f f' a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) < y /\ f'(b) > y
        ==> ?z. a < z /\ z < b /\ (f'(z) = y)`,
  REWRITE_TAC[real_gt] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. --(f x)`; `\x:real. --(f' x)`;
                `a:real`; `b:real`; `--y`] IVT_DERIVATIVE_POS) THEN
  ASM_REWRITE_TAC[real_gt; REAL_LT_NEG2; REAL_EQ_NEG2] THEN
  ASM_SIMP_TAC[DIFF_NEG]);;
