structure GenPolyCanon :> GenPolyCanon =
struct

open HolKernel boolLib

datatype assoc_mode = L | R | L_Cflipped

datatype gci =
         GCI of {dest : term -> term * term,
                 is_literal : term -> bool,
                 assoc : thm (* right to left *),
                 symassoc : thm (* left to right *),
                 comm : thm,
                 assoc_mode : assoc_mode,
                 r_asscomm : thm (* swaps 1 and 2 in r-associated triple *),
                 l_asscomm : thm (* swaps 2 and 3 in l-associated triple *),
                 non_coeff : term -> term,
                 merge : term -> thm,
                 postnorm : term -> thm,
                 left_id : thm (* id on left can be rewritten away *),
                 right_id : thm (* id on right can be rewritten away *),
                 reducer : term -> thm}

fun update_mode m (GCI {dest,is_literal,assoc,symassoc,comm,assoc_mode,
                        l_asscomm,r_asscomm, non_coeff, merge, postnorm,
                        left_id, right_id, reducer}) =
    GCI {dest = dest, is_literal = is_literal, comm = comm, assoc = assoc,
         symassoc = symassoc, l_asscomm = l_asscomm, r_asscomm = r_asscomm,
         non_coeff = non_coeff, merge = merge, postnorm = postnorm,
         left_id = left_id, right_id = right_id, reducer = reducer,
         assoc_mode = m}

fun gencanon (gci as GCI g) = let
  val {dest,non_coeff,comm,assoc,symassoc,merge,postnorm,is_literal,...} = g
  val REDUCE_CONV = #reducer g
  fun ra_swapmerge t = let
    val (l,r) = dest t
    val (r',merge_conval,post_conval,swapper) = let
      val (l',_) = dest r
    in
      (l', (fn c => REWR_CONV assoc THENC LAND_CONV c), LAND_CONV,
       REWR_CONV (#r_asscomm g))
    end handle HOL_ERR _ => (r,I,I,REWR_CONV comm)
    val swap_action = swapper THENC
                      RAND_CONV (ra_swapmerge THENC
                                 TRY_CONV (REWR_CONV (#left_id g))) THENC
                      TRY_CONV (REWR_CONV (#right_id g))
    val eq_action = merge_conval merge THENC post_conval postnorm
    val non_action = LAND_CONV postnorm
  in
    case
      (is_literal l, is_literal r', Term.compare (non_coeff l, non_coeff r'))
     of
      (true, false, _) => swap_action
    | (true, true, _) => eq_action
    | (false, true, _) => non_action
    | (false, false, LESS) => non_action
    | (false, false, EQUAL) => eq_action
    | (false, false, GREATER) => swap_action
  end t handle HOL_ERR _ => postnorm t
  fun la_swapmerge t = let
    val (l,r) = dest t
    val (l', merge_conval, post_conval, swapper) = let
      val (_, r') = dest l
    in
      (r', (fn c => REWR_CONV symassoc THENC RAND_CONV c), RAND_CONV,
       REWR_CONV (#l_asscomm g))
    end handle HOL_ERR _ => (l,I,I,REWR_CONV comm)
    val non_action = RAND_CONV postnorm
    val eq_action = merge_conval merge THENC post_conval postnorm
    val swap_action = swapper THENC
                      LAND_CONV (la_swapmerge THENC
                                 TRY_CONV (REWR_CONV (#right_id g))) THENC
                      TRY_CONV (REWR_CONV (#left_id g))
  in
    case
      (is_literal l', is_literal r, Term.compare (non_coeff l', non_coeff r))
     of
      (true, false, _) => swap_action
    | (true, true, _) => eq_action
    | (false, true, _) => non_action
    | (false, false, LESS) => non_action
    | (false, false, EQUAL) => eq_action
    | (false, false, GREATER) => swap_action
  end t handle HOL_ERR _ => postnorm t
  fun ra_recurse t = let
    val (l,r) = dest t
  in
    if can dest l then
      REWR_CONV symassoc THENC ra_recurse
    else
      RAND_CONV ra_recurse THENC ra_swapmerge THENC
      TRY_CONV (REWR_CONV (#left_id g))
  end t handle HOL_ERR _ => postnorm t
  fun la_recurse t = let
    val (l,r) = dest t
  in
    if can dest r then
      REWR_CONV assoc THENC la_recurse
    else
      LAND_CONV la_recurse THENC la_swapmerge THENC
      TRY_CONV (REWR_CONV (#right_id g))
  end t handle HOL_ERR _ => postnorm t
  fun lcflipped t = let
    val (l,r) = dest t
    fun finish_have_left_lit t = let
      val r = rand t
    in
      if can dest r then
        if is_literal (rand r) then
          RAND_CONV (REWR_CONV comm) THENC
          REWR_CONV assoc THENC LAND_CONV REDUCE_CONV
        else ALL_CONV
      else if is_literal r then
        REDUCE_CONV
      else ALL_CONV
    end t
    fun finish_no_left_lit t = let
      val (l,r) = dest t
    in
      if is_literal r then REWR_CONV comm
      else ALL_CONV
    end t handle HOL_ERR _ => ALL_CONV t
  in
    if is_literal l then
      RAND_CONV la_recurse THENC finish_have_left_lit
    else la_recurse THENC finish_no_left_lit
  end t handle HOL_ERR _ => postnorm t
in
  case #assoc_mode g of
    L => la_recurse
  | R => ra_recurse
  | L_Cflipped => lcflipped
end

fun derive_l_asscomm assoc0 comm0 = let
  val assoc = SPEC_ALL assoc0
  val comm = SPEC_ALL comm0
in
  SYM (CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV comm) THENC
                             REWR_CONV assoc)) assoc)
end
fun derive_r_asscomm assoc0 comm0 = let
  val assoc = SPEC_ALL assoc0
  val comm = SPEC_ALL comm0
in
  CONV_RULE (RAND_CONV (LAND_CONV (REWR_CONV comm) THENC
                        REWR_CONV (SYM assoc))) assoc
end

end (* struct *)

(*


val realadd_gci = let
  open realTheory realSyntax
  val assoc = SPEC_ALL REAL_ADD_ASSOC
  val comm = SPEC_ALL REAL_ADD_COMM
  val asscomm = derive_asscomm assoc comm
  fun is_good t = let
    val (l,r) = dest_mult t
  in
    is_real_literal l orelse
    (is_div l andalso is_real_literal (rand l) andalso
     is_real_literal (rand (rator l)))
  end handle HOL_ERR _ => false
  fun add_coeff t = if is_good t then ALL_CONV t
                    else if is_negated t then REWR_CONV REAL_NEG_MINUS1 t
                    else REWR_CONV (GSYM REAL_MUL_LID) t
  fun non_coeff t = if is_good t orelse is_negated t then rand t
                    else t
in
  GCI { dest = dest_plus, assoc = assoc, symassoc = SYM assoc, comm = comm,
        asscomm = derive_asscomm assoc comm,
        non_coeff = non_coeff, distrib = GSYM REAL_RDISTRIB,
        distrib_left = true, add_coeff = add_coeff,
        postnorm = REWR_CONV REAL_MUL_LZERO ORELSEC
                   REWR_CONV REAL_MUL_LID ORELSEC
                   TRY_CONV (REWR_CONV (GSYM REAL_NEG_MINUS1)),
        left_id = REAL_ADD_LID, right_id = REAL_ADD_RID,
        reducer = computeLib.CBV_CONV (realSimps.real_compset())}
end



*)