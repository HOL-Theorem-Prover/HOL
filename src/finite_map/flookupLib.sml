structure flookupLib :> flookupLib =
struct

open HolKernel boolLib bossLib finite_mapSyntax

(* ------------------------------------------------------------------------- *)

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

local
   val not_F_imp = DECIDE ``(~F ==> a) = a``
in
   fun neqs_rule ty =
      let
         val neqs_rule =
            Conv.CONV_RULE (Conv.LAND_CONV (Conv.RAND_CONV (eq_conv ty))
                            THENC Conv.REWR_CONV not_F_imp)
      in
         fn thm =>
            List.foldl (neqs_rule o Lib.uncurry Thm.DISCH) thm (Thm.hyp thm)
      end
end

local
   val flookup_id = Q.prove(
      `FLOOKUP (fm |+ (a:'a, b)) a = SOME b`,
      REWRITE_TAC [finite_mapTheory.FLOOKUP_UPDATE]
      )
   val flookup_rest = Q.prove(
      `a <> x ==> (FLOOKUP (fm |+ (a, b)) x = FLOOKUP fm x)`,
      SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_UPDATE]
      )
      |> UNDISCH_ALL
   val updates = List.rev o List.map (fst o pairSyntax.dest_pair) o snd o
                 finite_mapSyntax.strip_fupdate
   val err = ERR "extend_flookup_thms" "not an extension"
   fun get_delta tm1 tm2 =
      let
         val u1 = updates tm1
         val u2 = updates tm2
         val l1 = List.length u1
         val l2 = List.length u2
         val d = l2 - l1
      in
         if 0 <= d
            then ( List.drop (u2, d) = u1 orelse raise err
                 ; (List.take (u2, d), u1) )
         else raise err
      end
   fun get_b rest =
      let
         val t = boolSyntax.lhs (Thm.concl rest)
      in
         case Lib.total finite_mapSyntax.dest_flookup t of
            SOME (fmap, _) => fmap
          | NONE => t
      end
   fun is_refl th =
      case Lib.total boolSyntax.dest_eq (Thm.concl th) of
         SOME (l, r) => l = r
       | NONE => false
in
   fun extend_flookup_thms (dict, rest) tm =
      let
         val base = get_b rest
         val (dty, rty) = finite_mapSyntax.dest_fmap_ty (Term.type_of base)
         val (tms, old_tms) = get_delta base tm
         val inst_ty = Thm.INST_TYPE [alpha |-> dty, beta |-> rty]
         val flookup_id = inst_ty flookup_id
         val flookup_rest = inst_ty flookup_rest
         val id_rule = Conv.RIGHT_CONV_RULE (Conv.REWR_CONV flookup_id)
         val rule = neqs_rule dty
         val a = Term.mk_var ("a", dty)
         val x = Term.mk_var ("x", dty)
         val th = Thm.REFL (finite_mapSyntax.mk_flookup (tm, x))
         val (dict', rest') =
            List.foldl
               (fn (t, (d, th)) =>
                 (case Lib.total (rule o id_rule o Thm.INST [x |-> t]) th of
                     SOME r => Redblackmap.insert (d, t, r)
                   | NONE => d,
                  Conv.RIGHT_CONV_RULE
                     (Conv.REWR_CONV (Thm.INST [a |-> t] flookup_rest)) th))
               (Redblackmap.mkDict Term.compare, th) tms
         val dict'' =
            List.foldl
               (fn (t, d) =>
                  case Redblackmap.peek (dict, t) of
                     SOME r => Redblackmap.insert
                                 (d, t,
                                  (rule o
                                   Conv.RIGHT_CONV_RULE (Conv.REWR_CONV r))
                                      (Thm.INST [x |-> t] rest'))
                   | NONE => raise err) dict' old_tms
         val rest'' = if is_refl rest
                         then rest'
                      else Conv.RIGHT_CONV_RULE (Conv.REWR_CONV rest) rest'
      in
         (dict'', rest'')
      end
end

val const_name = ref "gen_fmap_"
val new_const_size = ref 100

(* --------------------------------------------------------------------------
    FLOOKUP_DEFN_CONV

    Conversion for term of the form ``FLOOKUP fmap i``.

    Will abbreviate "fmap" when it contains lots of updates. Otherwise it
    will employ a database to lookup values.

    To activate in the context of EVAL do:

    val () =
      ( computeLib.del_consts [finite_mapSyntax.flookup_t]
      ; computeLib.add_convs
           [(finite_mapSyntax.flookup_t, 2, FLOOKUP_DEFN_CONV)] )

   -------------------------------------------------------------------------- *)

local
   val completed_fmap_convs =
      ref (Redblackmap.mkDict Term.compare: (term, conv) Redblackmap.dict)
   val head_fmaps =
      ref (Redblackmap.mkDict Term.compare:
             (term, (term, thm) Redblackmap.dict * thm) Redblackmap.dict)
   fun introduce_fmap_consts _ = ALL_CONV
   val const_number = ref 0
   val flookup_fallback_conv =
      Conv.REWR_CONV finite_mapTheory.FLOOKUP_UPDATE
      ORELSEC Conv.REWR_CONV finite_mapTheory.FLOOKUP_EMPTY
   val rwts = ref ([] : thm list)
   val rwt_cnv = ref ALL_CONV
   val err = ERR "FLOOKUP_DEFN_CONV" ""
   fun DICT_REST_CONV (dr as (dict, rest)) tm =
      let
         val i = snd (finite_mapSyntax.dest_flookup tm)
      in
         case Redblackmap.peek (dict, i) of
            SOME thm => Conv.REWR_CONV thm tm
          | NONE => let
                       val x = Term.rand (boolSyntax.rhs (Thm.concl rest))
                    in
                       neqs_rule (Term.type_of x) (Thm.INST [x |-> i] rest)
                    end
      end
   fun introduce_fmap_consts (x as (base, _)) =
      let
         val ty = Term.type_of base
         fun new_var () =
            Term.mk_var (!const_name ^ Int.toString (!const_number), ty) before
            Portable.inc const_number
         fun iter a (c, l) =
            let
               val r = List.take (l, !new_const_size)
               val v = new_var()
               val s = fst (Term.dest_var v)
               val t = finite_mapSyntax.list_mk_fupdate (c, r)
               val def = Definition.new_definition (s, boolSyntax.mk_eq (v, t))
               val () = print ("Defined " ^ quote s ^ "\n")
               val sym_def = SYM def
               val (c', tm) = boolSyntax.dest_eq (Thm.concl def)
               val (dict, rest) =
                  extend_flookup_thms
                    (Redblackmap.mkDict Term.compare, Thm.REFL c) tm
               val cnv = Conv.REWR_CONV sym_def
               val rule =
                  Conv.CONV_RULE
                     (Conv.LAND_CONV (Conv.RATOR_CONV (Conv.RAND_CONV cnv)))
               val dict = Redblackmap.transform rule dict
               val rest = rule rest
               val () =
                  completed_fmap_convs :=
                  Redblackmap.insert
                    (!completed_fmap_convs, c', DICT_REST_CONV (dict, rest))
            in
               iter (sym_def :: a) (c', List.drop (l, !new_const_size))
            end
            handle General.Subscript => a
         val defs = iter [] x
      in
         rwts := defs @ (!rwts); rwt_cnv := PURE_REWRITE_CONV (!rwts)
      end
in
   fun FLOOKUP_DEFN_CONV tm =
      let
         val fm = Lib.with_exn (fst o finite_mapSyntax.dest_flookup) tm err
         val (base, ups) = finite_mapSyntax.strip_fupdate fm
         val n = List.length ups
      in
         if not (List.null (Term.free_vars tm))
            then flookup_fallback_conv tm
         else if List.null ups
            then case Redblackmap.peek (!completed_fmap_convs, base) of
                    SOME cnv => cnv tm
                  | NONE => flookup_fallback_conv tm
         else if n < !new_const_size
            then let
                    val dr =
                       case Redblackmap.peek (!head_fmaps, base) of
                          SOME dr => dr
                        | NONE =>
                            (Redblackmap.mkDict Term.compare, Thm.REFL base)
                 in
                    case Lib.total (extend_flookup_thms dr) fm of
                       SOME dr' =>
                          ( head_fmaps :=
                               Redblackmap.insert (!head_fmaps, base, dr')
                          ; DICT_REST_CONV dr' tm
                          )
                     | NONE => flookup_fallback_conv tm
                 end
         else Conv.RATOR_CONV (Conv.RAND_CONV (!rwt_cnv)) tm
              handle Conv.UNCHANGED =>
                 ( introduce_fmap_consts (base, ups)
                 ; FLOOKUP_DEFN_CONV ) tm
      end
end

end

(* ----------------------------------------------------------------------- *)

(* Testing...

open flookupLib wordsLib
open flookupLib

val () =
   ( computeLib.del_consts [finite_mapSyntax.flookup_t]
   ; computeLib.add_convs [(finite_mapSyntax.flookup_t, 2, FLOOKUP_DEFN_CONV)] )

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

Count.apply EVAL ``FLOOKUP (FEMPTY |+ (a, 1)) a``

Count.apply EVAL ``FLOOKUP ^(mk_fmap fempty_tm 0 1000) 999``

Count.apply EVAL ``FLOOKUP gen_fmap_0 44``
Count.apply EVAL ``FLOOKUP (gen_fmap_0 |+ (1000, 1000)) 44``
Count.apply EVAL ``FLOOKUP (gen_fmap_0 |+ (44, 45)) 44``
Count.apply EVAL ``FLOOKUP gen_fmap_1 99``
Count.apply EVAL ``FLOOKUP gen_fmap_9 99``
Count.apply EVAL ``FLOOKUP gen_fmap_9 901``
Count.apply EVAL ``FLOOKUP gen_fmap_9 801``

val () = Hol_datatype `enum = One | Two | Three | Four | Five`

val () = Hol_datatype`
     data = Num of num
          | String of string
          | Word of word32
          | Enum of enum
          | Other1
          | Other2`

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
