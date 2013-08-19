structure GcbvLib <: gcbvLib = struct

open HolKernel GcbvTheory Parse Lib Feedback

val ERR = mk_HOL_ERR "GcbvLib"

val is_VALUE = can (match_term ``Gcbv$VALUE x``)
fun is_val tm = is_abs tm orelse is_const tm orelse is_VALUE tm

fun add_VALUE tm = if is_val tm then raise UNCHANGED else ISPEC tm VALUE_thm
fun drop_VALUE tm = if is_VALUE tm then ISPEC (rand tm) (GSYM VALUE_thm) else raise ERR "drop_VALUE" "not a VALUE"

fun add_rwt net th = Net.insert(lhs(concl th),th) net

val add_rwts = foldl (uncurry (C add_rwt))

fun RANDS_CONV conv tm = (TRY_CONV(RAND_CONV conv THENC (RATOR_CONV (RANDS_CONV conv)))) tm
rand``f x y``

fun add_thm net th = let
  val ths = CONJUNCTS th
  val ths = map SPEC_ALL ths
  val net = add_rwts net ths
  val vths = mapfilter (CONV_RULE(CHANGED_CONV(LAND_CONV(RANDS_CONV add_VALUE)))) ths
  val net = add_rwts net vths
  in net end

local

  val ERR = ERR "GcbvConv"

  fun check_var tm = if is_var tm then raise ERR ("encountered variable: "^(term_to_string tm)) else ()

  fun TRY_RIGHT_BETA th = RIGHT_BETA th handle HOL_ERR _ => th

  fun beta_reduce1 th = TRY_RIGHT_BETA o C AP_TERM th

  fun FIRST_RATOR_CONV conv tm = (RATOR_CONV conv ORELSEC FIRST_RATOR_CONV (RATOR_CONV conv)) tm

  fun beta_reduce [] = REFL
    | beta_reduce [th] = beta_reduce1 th
    | beta_reduce (th::ths) = fn f => let
        val th1 = beta_reduce1 th f
        val th2 = beta_reduce ths (rhs(concl th1))
      in CONV_RULE (LAND_CONV(FIRST_RATOR_CONV(REWR_CONV (SYM th1)))) th2 end

  fun rewriteC net tm = let
    val th = hd (Net.match tm net)
     (* TODO: Need to deal with the VALUE tags in the way? Or can just
              preprocess theorems before putting them in the net?
              Currently doing the latter: add_thm adds two versions of each
              theorem, one with top-level VALUE tags on the arguments and one
              with no tags.
      *)
    in PART_MATCH lhs th tm
    end handle Empty => raise UNCHANGED

  fun pullValC tm = if is_VALUE tm then raise UNCHANGED else
    (TOP_SWEEP_CONV drop_VALUE THENC add_VALUE) tm

in

  fun GcbvConv net tm =
    if (check_var tm; is_val tm) then raise UNCHANGED else
    (applyC net THENC (TRY_CONV(CHANGED_CONV (rewriteC net) THENC GcbvConv net)) THENC pullValC) tm

  and applyC net tm =
    let
      val (f,ts) = strip_comb tm
      val _ = check_var f
      (* TODO: check for case constant and don't evaluate the arguments if so *)
      val ths = map (QCONV (GcbvConv net)) ts
      (* t1 = v1, ..., tn = vn *)
    in beta_reduce ths f end
      (* (\z1...zk. fb) t1 ... tn = fb[v1..k/z1..k] vk+1 ... vn *)
      (*                       or = \zn+1...zk. fb[v1..n/z1..n] *)

end

(*

val net = Net.empty
val net = add_thm net listTheory.LENGTH
val tm = ``LENGTH []``
val res = GcbvConv net tm
val tm = ``LENGTH [[]]``
val res = GcbvConv net tm
val tm = ``LENGTH [1;2;3]``
val res = GcbvConv net tm

*)

end
