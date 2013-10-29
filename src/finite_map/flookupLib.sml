structure flookupLib :> flookupLib =
struct

open finite_mapSyntax

fun memoize size cmp f =
   let
      val d = ref (Redblackmap.mkDict cmp)
      val k = ref []
      val finite = 0 < size
   in
      fn v =>
         case Redblackmap.peek (!d, v) of
            SOME r => r
          | NONE =>
               let
                  val r = f v
               in
                  if finite
                     then (k := !k @ [v]
                           ; if size < Redblackmap.numItems (!d)
                                then case List.getItem (!k) of
                                        SOME (h, t) =>
                                          (d := fst (Redblackmap.remove (!d, h))
                                           ; k := t)
                                      | NONE => raise ERR "memoize" "empty"
                              else ())
                  else ()
                  ; d := Redblackmap.insert (!d, v, r)
                  ; r
               end
   end

local
   fun one_ones ty =
      Option.getOpt (Lib.total (CONJUNCTS o TypeBase.one_one_of) ty, [])
   val eqf_into = List.map (EQF_INTRO o SPEC_ALL) o CONJUNCTS
in
   val datatype_eq_conv =
      memoize 20 Type.compare
        (fn ty =>
            case Lib.total TypeBase.distinct_of ty of
               SOME th =>
                  PURE_REWRITE_CONV
                     (one_ones ty @ eqf_into th @ eqf_into (GSYM th))
             | NONE => EVAL)
end

fun eq_conv ty =
   (!Defn.const_eq_ref)
   ORELSEC (datatype_eq_conv ty
            THENC (fn tm =>
                      case Lib.total boolSyntax.dest_eq tm of
                         SOME (l, r) =>
                            if l = r
                               then Drule.ISPEC l boolTheory.REFL_CLAUSE
                            else eq_conv (Term.type_of l) tm
                       | NONE => ALL_CONV tm))


(* --------------------------------------------------------------------------
    FLOOKUP_DEFN_CONV thm

    Given a definition of the form

    |- fmap = base_fmap |+ (i_1, d_1) ... |+ (i_n, d_n)

    where each i_j is ground, FLOOKUP_DEFN_CONV returns a conversion that
    succeeds on terms of the form

     ``FLOOKUP fmap x``

    where x is ground. If x = i_j for some j then the result will be

    |- FLOOKUP fmap i_j = SOME d_j

    Otherwise, if x is not equal to any i_j then the result will be

    |- FLOOKUP fmap x = FLOOKUP base_fmap x

    The complexity of building the conversion is quadratic, so this routine
    does not scale well to very large finite map definitions.
   -------------------------------------------------------------------------- *)

local
   val not_F_imp = DECIDE ``(~F ==> a) = a``
   val flookup_id = Q.prove(
      `FLOOKUP (fm |+ (a:'a, b)) a = SOME b`,
      REWRITE_TAC [finite_mapTheory.FLOOKUP_UPDATE]
      )
   val flookup_rest = Q.prove(
      `a <> x ==> (FLOOKUP (fm |+ (a, b)) x = FLOOKUP fm x)`,
      SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_UPDATE]
      )
      |> UNDISCH_ALL
   val err = ERR "FLOOKUP_DEFN_CONV" ""
in
   fun FLOOKUP_DEFN_CONV thm =
      let
         val (d, t) = boolSyntax.dest_eq (Thm.concl thm)
         val (dty, rty) = finite_mapSyntax.dest_fmap_ty (Term.type_of d)
         val tms = List.rev (List.map (fst o pairSyntax.dest_pair)
                               (snd (finite_mapSyntax.strip_fupdate t)))
         val inst_ty = Thm.INST_TYPE [alpha |-> dty, beta |-> rty]
         val flookup_id = inst_ty flookup_id
         val flookup_rest = inst_ty flookup_rest
         val id_rule = Conv.RIGHT_CONV_RULE (Conv.REWR_CONV flookup_id)
         val neqs_rule = Conv.CONV_RULE
                             (Conv.LAND_CONV (Conv.RAND_CONV (eq_conv dty))
                              THENC Conv.REWR_CONV not_F_imp)
         fun rule thm =
            List.foldl (neqs_rule o Lib.uncurry Thm.DISCH) thm (Thm.hyp thm)
         val rest_rule = Conv.RIGHT_CONV_RULE (Conv.REWR_CONV flookup_rest)
         val a = Term.mk_var ("a", dty)
         val x = Term.mk_var ("x", dty)
         val th = Conv.RATOR_CONV (Conv.RAND_CONV (Conv.REWR_CONV thm))
                    (finite_mapSyntax.mk_flookup (d, x))
         val (dict, rest) =
            List.foldl
               (fn (t, (dict, th)) =>
                  let
                     val rwt =
                        Lib.total (rule o id_rule o Thm.INST [x |-> t]) th
                  in
                    (case rwt of
                        SOME r => Redblackmap.insert (dict, t, r)
                      | NONE => dict,
                     Conv.RIGHT_CONV_RULE
                        (Conv.REWR_CONV (Thm.INST [a |-> t] flookup_rest)) th)
                  end)
               (Redblackmap.mkDict Term.compare, th) tms
      in
         fn tm =>
            let
               val (fm, i) = Lib.with_exn finite_mapSyntax.dest_flookup tm err
            in
               if fm = d
                  then case Redblackmap.peek (dict, i) of
                          SOME th => th
                        | NONE =>
                            Lib.with_exn (rule o Thm.INST [x |-> i]) rest err
               else raise err
            end
      end
end

end

(* ----------------------------------------------------------------------- *)
(* Testing

open flookupLib wordsLib

val () = Hol_datatype `enum = One | Two | Three | Four | Five`

val () = Hol_datatype`
     data = Num of num
          | String of string
          | Word of word32
          | Enum of enum
          | Other1
          | Other2`

val fempty_tm =
   Term.inst [alpha |-> numSyntax.num, beta |-> numSyntax.num]
      finite_mapSyntax.fempty_t

fun mk_fmap t b n =
   finite_mapSyntax.list_mk_fupdate
     (t, List.tabulate
           (n, fn i => let
                          val j = numLib.term_of_int (b + i)
                       in
                          pairSyntax.mk_pair (j, j)
                       end))

val dict2_def = Define `dict2 = ^(mk_fmap fempty_tm 0 1000)`
val dict3_def = Define `dict3 = ^(mk_fmap ``dict2`` 1000 400)`
val dict4_def = Define `dict4 = FEMPTY |+ (1, 1) |+ (2, 2) |+ (2, 3)`
val dict5_def = Define`
   dict5 =
   FEMPTY |+ (Num 1, 1)
          |+ (String "s", 2)
          |+ (Other1, 3)
          |+ (Other2, 4)
          |+ (Num 2, 1)
          |+ (Enum One, 5)
          |+ (Enum Two, 6)
          |+ (Word 32w, 7)
          |+ (Word 31w, 8)`

val d2_conv = Count.apply FLOOKUP_DEFN_CONV dict2_def
val d3_conv = Count.apply FLOOKUP_DEFN_CONV dict3_def
val d4_conv = Count.apply FLOOKUP_DEFN_CONV dict4_def
val d5_conv = Count.apply FLOOKUP_DEFN_CONV dict5_def

Count.apply d3_conv ``FLOOKUP dict3 1``;
Count.apply d3_conv ``FLOOKUP dict3 1000``;
Count.apply d4_conv ``FLOOKUP dict4 1``;
Count.apply d5_conv ``FLOOKUP dict5 (Num 1)``;

*)
