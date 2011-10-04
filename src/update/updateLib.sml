structure updateLib :> updateLib =
struct

open HolKernel Parse boolLib bossLib computeLib;
open wordsLib updateTheory;

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars updateTheory.update_grammars
end
open Parse

(* ------------------------------------------------------------------------ *)

val LIST_UPDATE_INTRO_CONV =
  PURE_REWRITE_CONV [LIST_UPDATE_THMS, listTheory.APPEND, listTheory.SNOC]

val LIST_UPDATE_ELIM_CONV =
  PURE_REWRITE_CONV
    [LIST_UPDATE_def, pairTheory.FST, pairTheory.SND, combinTheory.I_o_ID]
  THENC PURE_REWRITE_CONV [combinTheory.o_THM];

(* ----------------------------------------------------------------------- *)

fun dest_list_update tm =
  case boolSyntax.dest_strip_comb tm
  of ("update$LIST_UPDATE", [l]) =>
       List.map pairSyntax.dest_pair (fst (listSyntax.dest_list l))
   | _ => raise ERR "dest_list_update" "";

val is_ground = List.null o Term.free_vars;

fun is_ground_update tm =
  case Lib.total combinSyntax.dest_update tm
  of SOME (l,_) => is_ground l
   | NONE => false;

fun is_ground_list_update tm =
  case Lib.total dest_list_update tm
  of SOME l => Lib.all (is_ground o fst) l
   | NONE => false;

fun is_ground_upd tm = is_ground_update tm orelse is_ground_list_update tm;

fun is_o_expr tm =
  is_ground_upd tm orelse
  case Lib.total combinSyntax.dest_o tm
  of SOME (l,r) =>
       is_ground_upd l andalso is_o_expr r orelse
       is_o_expr l andalso is_ground_upd r
   | NONE => false;

fun is_base tm =
  case Lib.total Term.dest_comb tm
  of SOME (l,_) => not (is_ground_upd l)
   | NONE => true;

fun is_c_expr tm =
  case Lib.total Term.dest_comb tm
  of SOME (l,r) => is_o_expr l andalso (is_base r orelse is_c_expr r)
   | NONE => false;

fun is_update_expr tm = is_o_expr tm orelse is_c_expr tm;

(* ----------------------------------------------------------------------- *)

fun UNCHANGED_CONV conv tm =
let val res = conv tm in
  if term_eq tm (rhs (concl res)) then
    raise Conv.UNCHANGED
  else
    res
end

fun OVERRIDE_UPDATES_CONV ty rwts =
let
  val cmp = reduceLib.num_compset()
  val _ = computeLib.add_thms
            ([OVERRIDE_def, listTheory.FILTER, pairTheory.PAIR_EQ,
              pairTheory.FST, pairTheory.SND] @ rwts) cmp
  val OVERRIDE_CONV = computeLib.CBV_CONV cmp
in
  fn tm =>
    let
      val tm_ty = Term.type_of tm
      val _ = Lib.can (Type.match_type ty) tm_ty andalso is_c_expr tm orelse
              Lib.can (Type.match_type (ty --> ty)) tm_ty andalso is_o_expr tm
              orelse raise ERR "SORT_UPDATES_CONV" "Not expected type/form"
    in
      UNCHANGED_CONV
        (LIST_UPDATE_INTRO_CONV
         THENC PURE_ONCE_REWRITE_CONV [LIST_UPDATE_OVERRIDE]
         THENC OVERRIDE_CONV
         THENC LIST_UPDATE_ELIM_CONV) tm
    end
end

fun SORT_UPDATES_CONV ord rwts =
let
  val (ty1,ty2) = ord |> Term.type_of |> Type.dom_rng |> fst
                      |> pairSyntax.dest_prod
  val ty3 = ty1 --> ty2
  val thm = Drule.ISPEC ord LIST_UPDATE_SORT_OVERRIDE
  val cmp = reduceLib.num_compset()
  val _ = computeLib.add_thms (rwts @
            [OVERRIDE_def, listTheory.FILTER, listTheory.APPEND,
             pairTheory.PAIR_EQ, pairTheory.FST, pairTheory.SND,
             pairTheory.CURRY_DEF, pairTheory.UNCURRY_DEF,
             combinTheory.o_THM, sortingTheory.PART_DEF,
             sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF]) cmp
  val SORT_CONV = computeLib.CBV_CONV cmp
in
  fn tm =>
    let
      val ty = Term.type_of tm
      val _ = Lib.can (Type.match_type ty3) ty andalso is_c_expr tm orelse
              Lib.can (Type.match_type (ty3 --> ty3)) ty andalso is_o_expr tm
              orelse raise ERR "SORT_UPDATES_CONV" "Not expected type/form"
    in
      UNCHANGED_CONV
        (LIST_UPDATE_INTRO_CONV
         THENC PURE_ONCE_REWRITE_CONV [thm] THENC SORT_CONV
         THENC LIST_UPDATE_ELIM_CONV) tm
    end
end

fun SORT_UPDATES_MAPTO_CONV f ord =
let
  val (uty,oty) = Type.dom_rng (Term.type_of f)
  val _ = (Term.type_of ord = (oty --> oty --> Type.bool)) orelse
          raise ERR "SORT_UPDATES_CONV"
                    "Map and ordering have inconsistent types"
  val x = Term.mk_var ("x", uty)
  val y = Term.mk_var ("y", uty)
  val f_x = Term.mk_comb (f, x)
  val f_y = Term.mk_comb (f, y)
  val f_ord = Term.list_mk_abs ([x,y], Term.list_mk_comb (ord, [f_x,f_y]))
in
  SORT_UPDATES_CONV f_ord
end

(* ----------------------------------------------------------------------- *)

val SORT_NUM_UPDATES_CONV =
  SORT_UPDATES_MAPTO_CONV ``FST : num # 'a -> num`` numSyntax.less_tm [];

local
  val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;
  val rule = REWRITE_RULE [wordsTheory.MOD_2EXP_DIMINDEX]
  val word_lo = rule wordsTheory.word_lo_n2w
  val word_eq = rule wordsTheory.word_eq_n2w
in
  fun SORT_WORD_UPDATES_CONV ty =
    let
      val dimindex = wordsLib.SIZES_CONV (wordsSyntax.mk_dimindex ty)
                     handle HOL_ERR _ =>
                       raise ERR "SORT_WORD_UPDATES_CONV"
                                 "Cannot compute size or word type"
    in
      SORT_UPDATES_MAPTO_CONV
        ``FST : ^(ty_antiq ty) word # 'a -> ^(ty_antiq ty) word``
        (Term.inst [Type.alpha |-> ty] wordsSyntax.word_lo_tm)
        [word_lo, word_eq, dimindex,
         SUC_RULE numeral_bitTheory.MOD_2EXP_EQ,
         SUC_RULE numeral_bitTheory.MOD_2EXP_MAX]
    end
end

fun SORT_ENUM_UPDATES_CONV ty =
let
  val {Thy, Args, Tyop} = Type.dest_thy_type ty
  val _ = List.null Args orelse
            raise ERR "SORT_ENUM_UPDATES_CONV"
                      "Not an enumerated type"
  val ty2num = Tyop ^ "2num"
  val ty2num_tm = Term.prim_mk_const {Thy = Thy, Name = ty2num}
  val ty2num_11 = DB.fetch Thy (ty2num ^ "_11")
  val ty2num_thm = DB.fetch Thy (ty2num ^ "_thm")
in
  SORT_UPDATES_MAPTO_CONV
    ``(^ty2num_tm o FST) : ^(ty_antiq ty) # 'a -> num`` numSyntax.less_tm
    [GSYM ty2num_11, ty2num_thm]
end

end
