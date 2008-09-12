structure intSimps :> intSimps =
struct

open HolKernel boolLib integerTheory intSyntax simpLib

val ERR = mk_HOL_ERR "intSimps";

open intReduce

(* ----------------------------------------------------------------------
    integer normalisations
   ---------------------------------------------------------------------- *)


local
  open intSyntax integerTheory GenPolyCanon
  val assoc = INT_ADD_ASSOC
  val comm = INT_ADD_COMM
  fun is_good t = let
    val (l,r) = dest_mult t
  in
    is_int_literal l
  end handle HOL_ERR _ => false
  fun non_coeff t = if is_good t then rand t
                    else if is_negated t then rand t
                    else t
  fun add_coeff t =
      if is_good t then ALL_CONV t
      else if is_negated t then REWR_CONV INT_NEG_MINUS1 t
      else REWR_CONV (GSYM INT_MUL_LID) t
  val distrib = GSYM INT_RDISTRIB
  fun merge t = let
    val (l,r) = dest_plus t
  in
    if is_int_literal l andalso is_int_literal r then
      REDUCE_CONV
    else BINOP_CONV add_coeff THENC
         REWR_CONV distrib THENC
         LAND_CONV REDUCE_CONV
  end t
in
  val lintadd_gci =
      GCI { dest = dest_plus,
            assoc_mode = L,
            is_literal = is_int_literal,
            assoc = assoc,
            symassoc = GSYM assoc,
            comm = comm,
            l_asscomm = derive_l_asscomm assoc comm,
            r_asscomm = derive_r_asscomm assoc comm,
            non_coeff = non_coeff,
            merge = merge,
            postnorm = REWR_CONV INT_MUL_LZERO ORELSEC
                       REWR_CONV INT_MUL_LID ORELSEC
                       TRY_CONV (REWR_CONV (GSYM INT_NEG_MINUS1)),
            left_id = INT_ADD_LID,
            right_id = INT_ADD_RID,
            reducer = REDUCE_CONV }
  val rintadd_gci = update_mode R lintadd_gci
  val ADDL_CANON_CONV = gencanon lintadd_gci
  val ADDR_CANON_CONV = gencanon rintadd_gci
end



(*---------------------------------------------------------------------------*)
(* Support for ordered AC rewriting                                          *)
(*---------------------------------------------------------------------------*)

val INT_ADD_AC_ss = ac_ss [(INT_ADD_ASSOC,INT_ADD_COMM)]
val INT_MUL_AC_ss = ac_ss [(INT_MUL_ASSOC,INT_MUL_COMM)]
val INT_AC_ss = merge_ss [INT_ADD_AC_ss,INT_MUL_AC_ss]


(*---------------------------------------------------------------------------*)
(* Standard simplifications for the integers. Does not use the integer       *)
(* decision procedure.                                                       *)
(*---------------------------------------------------------------------------*)

val INT_RWTS_ss = integerTheory.integer_rwts;

val int_ss =
  boolSimps.bool_ss ++ pairSimps.PAIR_ss ++ optionSimps.OPTION_ss ++
  sumSimps.SUM_ss ++ combinSimps.COMBIN_ss ++
  numSimps.REDUCE_ss ++ numSimps.ARITH_ss ++ INT_REDUCE_ss ++
  INT_RWTS_ss;

(* Formerly the following underpowered version was used:
  val int_ss = boolSimps.bool_ss ++ INT_REDUCE_ss;
*)

(* ----------------------------------------------------------------------
    INT_ARITH_ss

    embedding Omega into a simpset fragment.
    Derived from code to do the same for the natural numbers, which is in
      src/num/arith/src/numSimps.sml
    and
      src/num/arith/src/Gen_arith.sml
   ---------------------------------------------------------------------- *)

fun contains_var tm =
    if is_var tm then true
    else if is_int_literal tm then false
    else let
        val (l, r) = dest_plus tm
                     handle HOL_ERR _ =>
                            dest_mult tm
                            handle HOL_ERR _ => dest_minus tm
      in
          contains_var l orelse contains_var r
      end handle HOL_ERR _ => contains_var (dest_absval tm)
                              handle HOL_ERR _ => true
 (* final default value is true because the term in question must be a
    complicated non-presburger thing that will get treated as a variable
    anyway. *)

fun is_linear_mult tm = let
  val (l,r) = dest_mult tm
in
  not (contains_var l andalso contains_var r)
end

fun arg1 tm = rand (rator tm)
val arg2 = rand

val non_presburger_subterms = IntDP_Munge.non_presburger_subterms

fun is_arith tm =
    List.all (fn t => type_of t = int_ty) (non_presburger_subterms tm)

fun contains_forall sense tm =
  if is_conj tm orelse is_disj tm then
    List.exists (contains_forall sense) (#2 (strip_comb tm))
  else if is_neg tm then
    contains_forall (not sense) (rand tm)
  else if is_imp tm then
    contains_forall (not sense) (rand (rator tm)) orelse
    contains_forall sense (rand tm)
  else if is_forall tm then
    sense orelse contains_forall sense (#2 (dest_forall tm))
  else if is_exists tm then
    not sense orelse contains_forall sense (#2 (dest_exists tm))
  else false

fun is_arith_thm thm =
  not (null (hyp thm)) andalso is_arith (concl thm)

val is_arith_asm = is_arith_thm o ASSUME

open Trace Cache Traverse
fun CTXT_ARITH DP DPname thms tm = let
  val context = map concl thms
  fun try gl = let
    val gl' = list_mk_imp(context,gl)
    val _ = trace (5, LZ_TEXT (fn () => "Trying cached arithmetic d.p. on "^
                                        term_to_string gl'))
  in
    rev_itlist (C MP) thms (DP gl')
  end
  val thm = EQT_INTRO (try tm)
      handle (e as HOL_ERR _) =>
             if tm <> F then EQF_INTRO (try(mk_neg tm)) else raise e
in
  trace(1,PRODUCE(tm,DPname,thm)); thm
end

fun crossprod (ll : 'a list list) : 'a list list =
    case ll of
      [] => [[]]
    | h::t => let
        val c = crossprod t
      in
        List.concat (map (fn hel => map (cons hel) c) h)
      end
fun prim_dest_const t = let
  val {Thy,Name,...} = dest_thy_const t
in
  (Thy,Name)
end

fun dpvars t = let
  fun recurse bnds acc t = let
    val (f, args) = strip_comb t
    fun go2() = let
      val (t1, t2) = (hd args, hd (tl args))
    in
      recurse bnds (recurse bnds acc t1) t2
    end
    fun go1 () = recurse bnds acc (hd args)
  in
    case Lib.total prim_dest_const f of
      SOME ("bool", "~") => go1()
    | SOME ("bool", "/\\") => go2()
    | SOME ("bool", "\\/") => go2()
    | SOME ("min", "==>") => go2()
    | SOME ("min", "=") => go2()
    | SOME ("bool", "COND") => let
        val (t1,t2,t3) = (hd args, hd (tl args), hd (tl (tl args)))
      in
        recurse bnds (recurse bnds (recurse bnds acc t1) t2) t3
      end
    | SOME ("integer", "int_add") => go2()
    | SOME ("integer", "int_sub") => go2()
    | SOME ("integer", "int_gt") => go2()
    | SOME ("integer", "int_lt") => go2()
    | SOME ("integer", "int_le") => go2()
    | SOME ("integer", "int_ge") => go2()
    | SOME ("integer", "int_mod") => go2()
    | SOME ("integer", "int_div") => go2()
    | SOME ("integer", "int_neg") => go1()
    | SOME ("integer", "ABS") => go1()
    | SOME ("integer", "int_mul") => let
        val args = intSyntax.strip_mult t
        val arg_vs = map (HOLset.listItems o recurse bnds empty_tmset) args
        val cs = crossprod (filter (not o null) arg_vs)
      in
        case cs of
          [] => acc
        | [[]] => acc
        | _ => let
            val var_ts = map (intSyntax.list_mk_mult o
                              Listsort.sort Term.compare) cs
          in
            List.foldl (fn (t,acc)=>HOLset.add(acc,t)) acc var_ts
          end
      end
    | SOME ("bool", "!") => let
        val (v, bod) = dest_abs (hd args)
      in
        recurse (HOLset.add(bnds, v)) acc bod
      end
    | SOME ("bool", "?") => let
        val (v, bod) = dest_abs (hd args)
      in
        recurse (HOLset.add(bnds, v)) acc bod
      end
    | SOME _ => if is_int_literal t then acc
                else HOLset.add(acc, t)
    | NONE => if is_var t then if HOLset.member(bnds, t) then acc
                               else HOLset.add(acc, t)
              else HOLset.add(acc, t)
  end
in
  HOLset.listItems (recurse empty_tmset empty_tmset t)
end


fun mkSS DPname DP = let
  val (CDP, cache) = let
    fun check tm =
        type_of tm = Type.bool andalso is_arith tm andalso tm <> boolSyntax.T
  in
    RCACHE (dpvars,check,CTXT_ARITH DP DPname)
  (* the check function determines whether or not a term might be handled
     by the decision procedure -- we want to handle F, because it's possible
     that we have accumulated a contradictory context. *)
  end
  val ARITH_REDUCER = let
    exception CTXT of thm list
    fun get_ctxt e = (raise e) handle CTXT c => c
    fun add_ctxt(ctxt, newthms) = let
      val addthese = filter is_arith_thm (flatten (map CONJUNCTS newthms))
    in
      CTXT (addthese @ get_ctxt ctxt)
    end
  in
    REDUCER {name = SOME DPname,
             addcontext = add_ctxt,
             apply = fn args => CDP (get_ctxt (#context args)),
             initial = CTXT []}
  end
in
  (SSFRAG {name=SOME (DPname ^ "_ss"),
           convs = [], rewrs = [], congs = [],
           filter = NONE, ac = [], dprocs = [ARITH_REDUCER]},
    cache)
end

val (OMEGA_ss, omega_cache) = mkSS "OMEGA" Omega.OMEGA_PROVE
val (COOPER_ss, cooper_cache) = mkSS "COOPER" Cooper.COOPER_PROVE
val INT_ARITH_ss = OMEGA_ss


end
