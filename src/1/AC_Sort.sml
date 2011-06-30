structure AC_Sort :> AC_Sort =
struct

open HolKernel Rewrite Conv

fun gstrip dest t = let
  fun recurse acc worklist =
      case worklist of
        [] => acc
      | t::ts => let
        in
          case Lib.total dest t of
            NONE => recurse (t::acc) ts
          | SOME (t1, t2) => recurse acc (t2::t1::ts)
        end
in
  recurse [] [t]
end

fun lmk mk ts = List.foldl mk (hd ts) (tl ts)

fun balance (dest,mk) assoc t = let
  val ts = gstrip dest t
  fun recurse ts = let
    val l = length ts div 2
    val (p,s) = split_after l ts
  in
    if l = 0 then hd ts
    else mk(recurse p, recurse s)
  end
in
  if length ts < 4 then ALL_CONV t
  else let
      val btree_norm = QCONV (PURE_REWRITE_CONV [assoc]) (recurse ts)
      val t_norm = QCONV (PURE_REWRITE_CONV [assoc]) t
    in
      TRANS t_norm (SYM btree_norm)
    end
end


fun sort {cmp, combine, dest, mk, assoc, comm, preprocess} = let
  val wassoc = REWR_CONV assoc
  val wassoc' = REWR_CONV (GSYM assoc)
  val wcomm = REWR_CONV comm
  fun toList t =
      case Lib.total dest t of
        NONE => (t, NONE)
      | SOME (t1, t2) => (t1, SOME t2)
  fun merge t = let
    val (t1, t2) = dest t
    val (h1, rest1) = toList t1
    val (h2, rest2) = toList t2
    val p = (isSome rest1, isSome rest2)
    fun lift_equal (true, true) =
        RAND_CONV wcomm THENC wassoc' THENC RAND_CONV (wassoc THENC wcomm) THENC
        wassoc THENC LAND_CONV combine THENC RAND_CONV merge
      | lift_equal (false, true) = wassoc THENC LAND_CONV combine
      | lift_equal (true, false) = wcomm THENC wassoc THENC LAND_CONV combine
      | lift_equal (false, false) = combine
    fun lift_left (true, _) = wassoc' THENC RAND_CONV merge
      | lift_left (false, _) = ALL_CONV
    fun lift_right (_, true) = wcomm THENC wassoc' THENC RAND_CONV merge
      | lift_right (_, false) = wcomm
  in
    case cmp (h1, h2) of
      EQUAL => lift_equal p
    | LESS => lift_left p
    | GREATER => lift_right p
  end t

  fun recurse t =
      case Lib.total dest t of
        NONE => TRY_CONV (QCHANGED_CONV preprocess THENC recurse) t
      | SOME (t1, t2) => (BINOP_CONV recurse THENC merge) t
in
  balance (dest, mk) assoc THENC recurse
end

(*

-- booleans over \/, with idempotency and cancellation

val boolcombine = let
  val porp = last (CONJUNCTS (SPEC_ALL OR_CLAUSES))
  val pornotp = EXCLUDED_MIDDLE |> SPEC_ALL |> EQT_INTRO
  val notporp = pornotp |> CONV_RULE (LAND_CONV (REWR_CONV DISJ_COMM))
in
  TRY_CONV (REWR_CONV porp ORELSEC REWR_CONV pornotp ORELSEC
            REWR_CONV notporp)
end

fun boolcompare (t1, t2) = let
  val (t1',_) = strip_neg t1
  val (t2',_) = strip_neg t2
in
  Term.compare(t1',t2')
end

val boolpreprocess = REPEATC (REWR_CONV (hd (CONJUNCTS NOT_CLAUSES)))

val booldisj_sort = sort {mk = mk_disj, dest = dest_disj,
                          cmp = boolcompare, comm = DISJ_COMM,
                          assoc = DISJ_ASSOC,
                          combine = boolcombine,
                          preprocess = boolpreprocess}

val b1 = time booldisj_sort ``p \/ r \/ q``
val b2 = time booldisj_sort ``~p \/ r \/ q \/ a \/ p``
val b3 = time booldisj_sort ``~~~p \/ r \/ q \/ a \/ p \/ b``
val b4 = time booldisj_sort ``p \/ r \/ q \/ p``
val b5 = time booldisj_sort ``~a \/ p \/ r \/ q \/ ~~~~p``

-- integers with coefficient gathering

fun intcombine t = let
  open intSyntax
  val (t1, t2) = intSyntax.dest_mult t
in
  if is_int_literal t1 then intLib.REDUCE_CONV t
  else ALL_CONV t
end

fun intcompare(t1, t2) = let
  open intSyntax
in
  case (is_int_literal t1, is_int_literal t2) of
    (true, true) => EQUAL
  | (true, false) => LESS
  | (false, true) => GREATER
  | (false, false) => Term.compare(t1, t2)
end

fun preprocess t =
    if intSyntax.is_int_literal t then NO_CONV t
    else REWR_CONV integerTheory.INT_NEG_MINUS1 t

val intmul =
    sort {mk = intSyntax.mk_mult, dest = intSyntax.dest_mult,
          cmp = intcompare, comm = integerTheory.INT_MUL_COMM,
          assoc = integerTheory.INT_MUL_ASSOC, combine = intcombine,
          preprocess = preprocess}

val test1 = time intmul ``2 * x * -7 * -y``
val test2 = time intmul ``2 * a * -x * a * 6 * b``
val test3 = time intmul ``x:int * y``   (* UNCHANGED *)
val test4 = time intmul ``y:int * x``
val test5 = time intmul ``2 * x * -1``
val test6 = time intmul ``1 * x:int``  (* UNCHANGED *)
val test7 = time intmul ``x * y * 0 : int``

*)
end (* struct *)
