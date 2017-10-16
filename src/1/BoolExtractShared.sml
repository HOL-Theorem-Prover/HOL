(* ===================================================================== *)
(* FILE          : BoolExtractShared                                     *)
(* DESCRIPTION   : Tools to extract shared terms from a boolean          *)
(*                 expression                                            *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : July 3, 2008                                          *)
(* ===================================================================== *)


structure  BoolExtractShared :>  BoolExtractShared =
struct

(*
quietdec := true;
*)

open HolKernel Parse boolLib

(*
quietdec := false;
*)


(*---------------------------------------------------------------------------
 * dest_neg_eq (``~(a = b)``) = (``a``, ``b``);
 *---------------------------------------------------------------------------*)
  fun dest_neg_eq t = dest_eq (dest_neg t);
  val is_neg_eq = can dest_neg_eq;


(*---------------------------------------------------------------------------
 * mk_neg___idempot a = ~a
 * mk_neg___idempot ~a = a
 * with a not being a negationg
 *---------------------------------------------------------------------------*)
  fun mk_neg___idempot t =
    if is_neg t then dest_neg t else mk_neg t;


(*---------------------------------------------------------------------------
 * for t1 and t2 being disequations,
 * eq_sym_acond tests, wether they are alpha convertible with
 * respect to the symmetry of equaltity
 *---------------------------------------------------------------------------*)
  fun eq_sym_aconv t1 t2 =
      aconv t1 t2 orelse
      (is_eq t1 andalso is_eq t2 andalso
       let
           val (t1l, t1r) = dest_eq t1;
           val (t2l, t2r) = dest_eq t2;
       in
          (aconv t1r t2l) andalso (aconv t1l t2r)
       end) orelse
      (is_neg_eq t1 andalso is_neg_eq t2 andalso
       let
           val (t1l, t1r) = dest_neg_eq t1;
           val (t2l, t2r) = dest_neg_eq t2;
       in
          (aconv t1r t2l) andalso (aconv t1l t2r)
       end);




  fun eq_sym_mem e [] = false
    | eq_sym_mem e (h::l) =
      (eq_sym_aconv e h) orelse eq_sym_mem e l;


  fun findMatches ([], l2) = []
    | findMatches (a::l1, l2) =
	 let val l1' = filter (fn e => not (eq_sym_aconv e a)) l1;
             val l2' = filter (fn e => not (eq_sym_aconv e a)) l2;
	     val l = (findMatches (l1',l2')); in
         if eq_sym_mem a l2 then a::l else l end;

  fun find_negation_pair [] = NONE |
      find_negation_pair (e::l) =
      if eq_sym_mem (mk_neg___idempot e) l then SOME e else
      find_negation_pair l;


  fun dest_quant t = dest_abs (snd (dest_comb t));
  fun is_quant t = is_forall t orelse is_exists t orelse
		 is_exists1 t;


  fun findMatches___multiple (l1:(term * bool) list,l2:(term * bool) list) =
      map (fn t => (t, true)) (findMatches (map fst l1, map fst l2));


  (*get_impl_terms returns a list of terms that imply the whole term and
    a list of terms that are implied. Thus if get_impl_terms t = (disjL,conjL) then

    forall x in disjL. x implies t and
    forall x in conjL. t implies x holds.


    so e. g. get_impl_terms ``a \/ b \/ ~c`` returns
     ([``a \/ b \/ ~c``, ``a``, ``b \/ ~c``, ``b``, ``~c``], [``a \/ b \/ ~c``])


    get_impl_terms___multiple augments the results with information, whether
    multiple occurences of a term have been abbriated to one.
   *)
  fun get_impl_terms___multiple t =
      if is_disj t then
	  (let val (t1,t2)=dest_disj t;
               val (l11,l12)= get_impl_terms___multiple t1;
               val (l21,l22)= get_impl_terms___multiple t2;
	   in
              ((t,false)::(l11 @ l21), (t,false)::findMatches___multiple (l12, l22))
           end)
      else
      if is_conj t then
	  (let val (t1,t2)=dest_conj t;
               val (l11,l12)= get_impl_terms___multiple t1;
               val (l21,l22)= get_impl_terms___multiple t2;
	   in
              ((t,false)::findMatches___multiple (l11, l21), (t,false)::(l12 @ l22))
           end)
      else
      if is_neg t then
	  (let val (l1,l2) = get_impl_terms___multiple (dest_neg t) in
	      (map (fn (t,b) => (mk_neg___idempot t, b)) l2, map (fn (t,b) => (mk_neg___idempot t, b)) l1)
          end)
      else
      if is_imp t then
	  (let val (t1,t2)=dest_imp_only t;
               val (l11',l12')= get_impl_terms___multiple t1;
               val (l11, l12) = (map (fn (t,b) => (mk_neg___idempot t, b)) l12',
                                 map (fn (t,b) => (mk_neg___idempot t, b)) l11')
               val (l21,l22)= get_impl_terms___multiple t2;
	   in
              ((t,false)::(l11 @ l21), (t,false)::findMatches___multiple (l12, l22))
           end)
      else
      if is_quant t then
          (let
	      val (v, b) = dest_quant t
	      val (l1,l2) = get_impl_terms___multiple b
	      fun filter_pred (t,b) = not (free_in v t)
	  in
              ((t,false)::filter filter_pred l1,
               (t,false)::filter filter_pred l2)
          end)
      else
        (if same_const T t orelse same_const F t then ([],[]) else
           ([(t,false)],[(t,false)]));


  fun clean_term_multiple_list [] = []
    | clean_term_multiple_list ((t,b)::L) =
        if op_mem aconv t (map fst L) then
          (t,true) ::
          clean_term_multiple_list (filter (fn (t',b') => not (aconv t t')) L)
        else
          (t,b)::clean_term_multiple_list L


  fun get_impl_terms t =
     let
        val (l1,l2) = get_impl_terms___multiple t;
     in
        (map fst l1, map fst l2)
     end





fun get_rewrite_assumption_thms rewr =
   let val match_thm = ASSUME rewr; in
   if is_eq rewr then
      [EQT_INTRO match_thm, EQT_INTRO (GSYM match_thm)]
   else if (is_neg_eq rewr) then
      [match_thm, GSYM match_thm]
   else [match_thm]
   end

fun case_split_REWRITE_CONV [] t =
    EQT_ELIM (REWRITE_CONV [] t)
  | case_split_REWRITE_CONV (m::matches) t =
    let
       fun rec_prove rewr =
       let
          val match_thms = get_rewrite_assumption_thms rewr;
          val thm = REWRITE_CONV match_thms t handle UNCHANGED => REFL t;
          val r = rhs (concl thm);
       in
          if aconv r T then thm else
	  TRANS thm (case_split_REWRITE_CONV matches r)
       end;

       val m_no_neg = fst (strip_neg m);
       val thm1 = rec_prove m_no_neg;
       val thm2 = rec_prove (mk_neg m_no_neg);


       val disj_thm = SPEC m_no_neg EXCLUDED_MIDDLE
       val thm = DISJ_CASES disj_thm thm1 thm2
    in
       thm
    end;




fun bool_eq_imp_real_imp_CONV matches t =
   let
      val matches_thms = flatten (map get_rewrite_assumption_thms matches)
      val conc_term = rhs (concl (REWRITE_CONV matches_thms t))
      val _ = if aconv conc_term F then raise UNCHANGED else ()

      val goal_term = if aconv conc_term T then T
                      else mk_imp (list_mk_conj matches, conc_term)
      val _ = if aconv t goal_term then raise UNCHANGED else ()
      val goal_eq_term = mk_eq (t, goal_term)

      val thm = EQT_ELIM (case_split_REWRITE_CONV matches goal_eq_term)
   in
      thm
   end;






fun bool_extract_common_terms_internal_CONV disj matches t =
   let
      val neg_matches = if disj then map mk_neg___idempot matches else matches
      val matches_thms = flatten (map get_rewrite_assumption_thms neg_matches)
      val conc_term = rhs (concl (REWRITE_CONV matches_thms t))


      val goal_term = if (disj) then
			  if aconv conc_term T then T else
                             list_mk_disj (conc_term::matches)
		      else
			  if aconv conc_term F then F else
                             list_mk_conj (conc_term::matches)

      val _ = if aconv t goal_term then raise UNCHANGED else ()
      val goal_eq_term = mk_eq (t, goal_term)
      val thm = EQT_ELIM (case_split_REWRITE_CONV matches goal_eq_term)
   in
      thm
   end;






(*cleans up the found matches by using just the simplest ones.
  So clean_disj_matches removes terms from the list that are implied by
  one other in the list and clean_conj_matches removes terms that imply
  another term*)

infix +=+
val E = empty_tmset and op+=+ = HOLset.addList;


fun clean_disj_matches [] acc = acc
  | clean_disj_matches (t::ts) acc =
    let
      open HOLset
      val (disj_imp,_) = get_impl_terms t
      val acc' = if isEmpty(intersection(E +=+ disj_imp, E +=+ ts +=+ acc)) then
		   t::acc
                 else
		   acc
    in
       clean_disj_matches ts acc'
    end;


fun clean_conj_matches [] acc = acc
  | clean_conj_matches (t::ts) acc =
    let
       val (_, conj_imp) = get_impl_terms t
       open HOLset
       val acc' =
           if isEmpty(intersection(E +=+ conj_imp, E +=+ ts +=+ acc)) then
	     t::acc
           else
	     acc
    in
       clean_conj_matches ts acc'
    end;








(*---------------------------------------------------------------------------
 * Given a equation with boolean expressions on both sides (b1 = b2),
 * this conversion tries to extract common parts of b1 and b2 into a precondition.
 *
 * e.g.          (A \/ B \/ C) = (A \/ D) is converted to
 *       ~A ==> ((     B \/ C) =       D )
 *
 *---------------------------------------------------------------------------*)

fun BOOL_EQ_IMP_CONV t =
   let
      val (l,r) = dest_eq t;
      val _ = if (type_of l = bool) then ()
              else raise mk_HOL_ERR "Conv" "bool_eq_imp_CONV" ""
      val (disj_l, conj_l) = get_impl_terms l
      val (disj_r, conj_r) = get_impl_terms r

      val disj_matches = clean_disj_matches (findMatches (disj_l, disj_r)) []
      val conj_matches = clean_conj_matches (findMatches (conj_l, conj_r)) []

      val matches = (map mk_neg___idempot disj_matches) @ conj_matches
      val _ = if null matches then raise UNCHANGED else ()
   in
      bool_eq_imp_real_imp_CONV matches t
   end;




(*---------------------------------------------------------------------------
 * Tries to convert a boolean expression to true or false by
 * searching for a case split that will prove this expression.
 *
 * e.g. this conversion is able to prove
 *        (A \/ B \/ ~A) = T
 *   or   (A \/ B \/ ((D /\ A) ==> C)) = T
 *   or   (A /\ B /\ ~A) = F
 *
 *---------------------------------------------------------------------------*)


fun BOOL_NEG_PAIR_CONV t =
   let
      val _ = if (type_of t = bool) then () else raise mk_HOL_ERR "Conv" "bool_negation_pair_CONV" "";
      val (disj_t, conj_t) = get_impl_terms t;
      val solving_case_split = find_negation_pair disj_t;
      val disj = isSome solving_case_split;
      val solving_case_split = if disj then solving_case_split else
			       find_negation_pair conj_t;

      val _ = if (isSome solving_case_split) then () else raise UNCHANGED;

      val thm_term = mk_eq (t, if disj then T else F);
      val thm = EQT_ELIM (case_split_REWRITE_CONV [valOf solving_case_split] thm_term)
   in
      thm
   end;



(*---------------------------------------------------------------------------
 * Tries to extract parts of a boolean terms that occur several times.
 *
 * e.g.   (D /\ A /\ ~C) \/ (A /\ B /\ ~C) = (D \/ B) /\ ~C /\ A
 *   or   A \/ B \/ A = B \/ A
 *
 *---------------------------------------------------------------------------*)
fun BOOL_EXTRACT_SHARED_CONV t =
   let
      val _ = if (type_of t = bool) then () else raise mk_HOL_ERR "Conv" "bool_imp_extract_CONV" "";
      val (disj_t___multiple,conj_t___multiple) = get_impl_terms___multiple t;
      val disj_t___multiple = clean_term_multiple_list disj_t___multiple;
      val conj_t___multiple = clean_term_multiple_list conj_t___multiple;
      val disj_t = clean_disj_matches (map fst (filter snd disj_t___multiple)) [];
      val conj_t = clean_conj_matches (map fst (filter snd conj_t___multiple)) [];
   in
      if (not (null disj_t)) then
         bool_extract_common_terms_internal_CONV true disj_t t
      else if (not (null conj_t)) then
         bool_extract_common_terms_internal_CONV false conj_t t
      else raise UNCHANGED
   end;




val BOOL_EQ_IMP_convdata = {name = "BOOL_EQ_IMP_CONV",
            trace = 2,
            key = SOME ([],``(a:bool) = (b:bool)``),
            conv = K (K BOOL_EQ_IMP_CONV)}:simpfrag.convdata;

val BOOL_EXTRACT_SHARED_convdata =  {name = "BOOL_EXTRACT_SHARED_CONV",
            trace = 2,
            key = SOME ([],``a:bool``),
            conv = K (K BOOL_EXTRACT_SHARED_CONV)}:simpfrag.convdata;

val BOOL_NEG_PAIR_convdata = {name = "BOOL_NEG_PAIR_CONV",
            trace = 2,
            key = SOME ([],``a:bool``),
            conv = K (K BOOL_NEG_PAIR_CONV)}:simpfrag.convdata;



end
