structure Import :> Import =
struct

open HolKernel boolLib bossLib
open state_transformerTheory bitstringLib stringLib machine_ieeeSyntax
open intSyntax integer_wordSyntax bitstringSyntax state_transformerSyntax

val ERR = mk_HOL_ERR "Import"

(* ------------------------------------------------------------------------ *)

local
   val boolify_vals = ref (Redblackset.empty Int.compare)
   val type_names = ref []
   val const_names = ref []
   fun decl s = "val " ^ s
   val typ = "{Thy: string, T: string list, C: string list, N: int list}"
in
   fun log_boolify n = boolify_vals := Redblackset.add (!boolify_vals, n)
   fun log_type s = type_names := s :: !type_names
   fun log_constant s = const_names := (s ^ "_def") :: !const_names
   fun start thy =
      (type_names := []
       ; const_names := []
       ; Theory.new_theory thy)
   fun finish i =
      (Theory.adjoin_to_theory {
         sig_ps =
           SOME (fn ppstrm =>
                   (PP.add_string ppstrm (decl "inventory:")
                    ; PP.add_break ppstrm (1, 2)
                    ; PP.add_string ppstrm typ)),
         struct_ps =
           SOME (fn ppstrm =>
                    let
                       val name = Lib.quote (Theory.current_theory ())
                       fun bl f s l =
                          ( PP.add_break ppstrm (1, 0)
                          ; PP.add_string ppstrm (s ^ " [")
                          ; PP.begin_block ppstrm PP.INCONSISTENT 0
                          ; Portable.pr_list
                              (PP.add_string ppstrm o f)
                              (fn () => PP.add_string ppstrm ",")
                              (fn () => PP.add_break ppstrm (1, 0)) l
                          ; PP.add_string ppstrm "]"
                          ; PP.end_block ppstrm)
                    in
                       PP.add_string ppstrm (decl "inventory = {")
                       ; PP.add_break ppstrm (0, 2)
                       ; PP.begin_block ppstrm PP.CONSISTENT 0
                       ; PP.add_string ppstrm ("Thy = " ^ name ^ ",")
                       ; bl Lib.quote "T =" (!type_names)
                       ; PP.add_string ppstrm (",")
                       ; bl Lib.quote "C =" (!const_names)
                       ; PP.add_string ppstrm (",")
                       ; bl Int.toString "N ="
                           (Redblackset.listItems (!boolify_vals))
                       ; PP.add_string ppstrm "}"
                       ; PP.end_block ppstrm
                       ; PP.add_newline ppstrm
                    end)}
       ; Feedback.set_trace "TheoryPP.include_docs" i
       ; Theory.export_theory ()
       ; type_names := []
       ; const_names := [])
end

(* ------------------------------------------------------------------------ *)

val Ty = ParseDatatype.pretypeToType
fun typeName ty = String.extract (Parse.type_to_string ty, 1, NONE)

(* Constant type *)
local
   fun mkTy (t, n) = ParseDatatype.dTyop {Thy = t, Tyop = n, Args = []}
   fun mkListTy a =
      ParseDatatype.dTyop {Thy = SOME "list", Tyop = "list", Args = [a]}
in
   val uTy = mkTy (SOME "one", "one")
   val iTy = mkTy (SOME "integer", "int")
   val nTy = mkTy (SOME "num", "num")
   val bTy = mkTy (SOME "min", "bool")
   val rTy = mkTy (SOME "binary_ieee", "rounding")
   val cTy = mkTy (SOME "string", "char")
   val sTy = mkListTy cTy
   val vTy = mkListTy bTy
   fun CTy n = mkTy (NONE, n)
end

(* Variable type *)
fun VTy s = ParseDatatype.dVartype ("'" ^ s)

(* Fixed-width bit-vector type *)
val FTy = ParseDatatype.dAQ o wordsSyntax.mk_int_word_type

val F1 = FTy 1
val F4 = FTy 4
val F8 = FTy 8
val F16 = FTy 16
val F32 = FTy 32
val F64 = FTy 64

(* N-bit type *)
fun typevar s = Type.mk_vartype ("'" ^ s)
fun BTy s = ParseDatatype.dAQ (wordsSyntax.mk_word_type (typevar s))

(* Arrow type *)
fun ATy (t1, t2) =
   ParseDatatype.dTyop {Thy = SOME "min", Tyop = "fun", Args = [t1, t2]}

(* Product type *)
fun PTy (t1, t2) =
   ParseDatatype.dTyop {Thy = SOME "pair", Tyop = "prod", Args = [t1, t2]}

(* Set type *)
fun STy t = ATy (t, bTy)

(* List type *)
fun LTy t =
   ParseDatatype.dTyop {Thy = SOME "list", Tyop = "list", Args = [t]}

(* Option type *)
fun OTy t =
   ParseDatatype.dTyop {Thy = SOME "option", Tyop = "option", Args = [t]}

(* ------------------------------------------------------------------------ *)

val myDatatype =
   let
      val w = String.size "Defined type: \""
   in
      (Lib.with_flag
         (Feedback.MESG_to_string,
          fn s => (log_type
                     (String.extract (s, w, SOME (String.size s - w - 1)))
                   ; s ^ "\n")) o
       Feedback.trace ("Theory.save_thm_reporting", 0) o
       Lib.with_flag (Datatype.big_record_size, 25))
       Datatype.astHol_datatype
   end

(* Record type *)
fun Record (n, l) = myDatatype [(n, ParseDatatype.Record l)]

(* Algebraic type *)
val Construct = myDatatype o List.map (I ## ParseDatatype.Constructors)

(* ------------------------------------------------------------------------ *)

fun mk_local_const (n, ty) =
   Term.mk_thy_const {Ty = ty, Thy = Theory.current_theory (), Name = n}

(* Literals *)

(* Unit *)
val LU = oneSyntax.one_tm
(* Bool *)
val LT = boolSyntax.T
val LF = boolSyntax.F
(* Integer *)
fun LI i = intSyntax.term_of_int (Arbint.fromInt i)
(* Natural *)
fun LN n = numSyntax.term_of_int n
(* Char *)
fun LSC c = stringSyntax.fromMLchar c
(* String *)
fun LS s = stringSyntax.fromMLstring s
(* Bitstring *)
fun LV v = bitstringSyntax.bitstring_of_binstring v
(* Fixed-width  *)
fun LW (i, w) = wordsSyntax.mk_wordii (i, w)
(* N-bit  *)
fun LY (i, n) = wordsSyntax.mk_n2w (LN i, typevar n)
(* Enumerated  *)
fun LC (c, ty) = mk_local_const (c, Ty ty)
(* NONE *)
fun LO ty = optionSyntax.mk_none (Ty ty)
(* Empty set *)
fun LE ty = pred_setSyntax.mk_empty (Ty ty)
(* Empty list (Nil) *)
fun LNL ty = listSyntax.mk_nil (Ty ty)
(* UNKNOWN  *)
fun LX ty = boolSyntax.mk_arb (Ty ty)

(* ------------------------------------------------------------------------ *)

(* Function call *)

fun Call (f, ty, tm) =
   let
      val typ = Type.--> (Term.type_of tm, Ty ty)
      val vc = mk_local_const (f, typ)
               handle HOL_ERR {origin_function = "mk_thy_const", ...} =>
                 Term.mk_var (f, typ) (* for recursion *)
   in
      Term.mk_comb (vc, tm)
   end

(* Constants *)

fun Const (c, ty) =
   let
      val typ = Ty ty
   in
      mk_local_const (c, typ)
      handle HOL_ERR {origin_function = "mk_thy_const", ...} =>
        Term.mk_var (c, typ) (* for recursion *)
   end

(* Variables *)

local
   val anon = ref 0
   fun anonSuffix () = (if !anon = 0 then "" else Int.toString (!anon))
                       before anon := !anon + 1
in
   fun resetAnon () = anon := 0
   fun AVar ty = Term.mk_var ("_" ^ anonSuffix(), Ty ty)
end

fun Var (v, ty) = Term.mk_var (v, Ty ty)

fun uVar v = Term.mk_var (v, oneSyntax.one_ty)
fun bVar v = Term.mk_var (v, Type.bool)
fun nVar v = Term.mk_var (v, numSyntax.num)
fun iVar v = Term.mk_var (v, intSyntax.int_ty)
fun sVar v = Term.mk_var (v, stringSyntax.string_ty)
fun vVar v = Term.mk_var (v, bitstringSyntax.bitstring_ty)

(* Closure *)

val Close = pairSyntax.mk_pabs

(* Application *)

val Apply = Term.mk_comb

(* Tuple *)

fun TP l =
   let
      val (f, lst) = Lib.front_last l
   in
      List.foldr pairSyntax.mk_pair lst f
   end

(* Map update *)

fun Fupd (m, i, e) = Term.mk_comb (combinSyntax.mk_update (i, e), m)

(* Cases *)

(* val CS = TypeBase.mk_case *)

fun CS (x, cs) =
   Term.beta_conv (Term.mk_comb
     (Lib.with_flag (Feedback.emit_MESG, false)
        (Lib.with_flag (Globals.priming, SOME "_")
           TypeBase.mk_pattern_fn) cs, x))
   before resetAnon ()

(* Let-expression *)

fun Let (v,e,b) =
   boolSyntax.mk_let (Close (v, b), e)
   handle HOL_ERR {origin_function = "mk_pabs", ...} => CS (e, [(v, b)])

(* Set of list *)

val SL =
   fn [] => raise ERR "SL" "empty"
    | l as (h::_) => pred_setSyntax.prim_mk_set (l, Term.type_of h)

(* List of list *)

val LL =
   fn [] => raise ERR "LL" "empty"
    | l as (h::_) => listSyntax.mk_list (l, Term.type_of h)

local
   fun gen_mk_list (l, tm) = List.foldr listSyntax.mk_cons tm l
in
   val LLC =
      fn ([], tm) =>
           let
              val ty = fst (pairSyntax.dest_prod (Term.type_of tm))
              val cons = Term.inst [Type.alpha |-> ty] listSyntax.cons_tm
           in
              pairSyntax.mk_uncurry (cons, tm)
           end
       | ltm => gen_mk_list ltm
end

(* Record constructor (may not work for really big records) *)

local
   fun strip_fun_type ty =
      let
         fun strip (a, ty) =
            case Lib.total Type.dom_rng ty of
              SOME (ty1, ty2) => strip (ty1::a, ty2)
            | NONE => (List.rev a, ty)
      in
         strip ([], ty)
      end
   fun get_cons ty =
      let
         val tm = Lib.singleton_of_list (TypeBase.constructors_of ty)
      in
         (fst (strip_fun_type (Term.type_of tm)), tm)
      end
   fun split l = Lib.split_after (List.length l)
in
   fun Rec (ty, l) =
      let
         val (tys, tm) = get_cons (Ty ty)
      in
         if List.length l = List.length tys
            then Term.list_mk_comb (tm, l)
         else let
                 val cs = List.map get_cons tys
                 val (tms, rst) =
                    List.foldl
                      (fn ((tys, f), (a, r)) =>
                          let
                              val (args, rst) = split tys r
                          in
                             (Term.list_mk_comb (f, args) :: a, rst)
                          end) ([], l) cs
              in
                 List.null rst orelse raise ERR "Rec" "too many arguments";
                 Term.list_mk_comb (tm, List.rev tms)
              end
      end
end

(* Record destructor *)

fun Dest (f, ty, tm) = Call (typeName (Term.type_of tm) ^ "_" ^ f, ty, tm)

(* Record update *)

fun smart_dest_pair tm =
   case Lib.total pairSyntax.dest_pair tm of
      SOME p => p
    | NONE => (pairSyntax.mk_fst tm, pairSyntax.mk_snd tm)

fun Rupd (f, tm) =
   let
      val (rty, fty) = pairSyntax.dest_prod (Term.type_of tm)
      val typ = Type.--> (Type.--> (fty, fty), Type.--> (rty, rty))
      val fupd = mk_local_const (typeName rty ^ "_" ^ f ^ "_fupd", typ)
      val (x, d) = smart_dest_pair tm
   in
      Term.list_mk_comb (fupd, [combinSyntax.mk_K_1 (d, Term.type_of d), x])
   end

(* Boolify constructor *)

val bit_bool =
   Feedback.trace ("Theory.save_thm_reporting", 0) bitstringLib.bitify_boolify

fun BL (i, tm) =
   let
      val () = log_boolify i
      val { mk_boolify, ... } = bit_bool i
   in
      mk_boolify tm
   end

(* If-then-else *)

fun ITE (i, t, e) = boolSyntax.mk_cond (i, t, e)

fun ITB (l, e) = List.foldr (fn ((b, t), e) => ITE (b, t, e)) e l

(* Sub-word extract *)

fun EX (x, h, l, ty) =
   let
      val typ = Ty ty
   in
      if typ = bitstringSyntax.bitstring_ty
         then bitstringSyntax.mk_field (h, l, x)
      else wordsSyntax.mk_word_extract (h, l, x, wordsSyntax.dest_word_type typ)
   end

(* Bit-field insert *)

fun BFI (t as (_, _, x, _)) =
   if Term.type_of x = bitstringSyntax.bitstring_ty
      then bitstringSyntax.mk_field_insert t
   else wordsSyntax.mk_bit_field_insert t

(* Concatenation *)

fun CC [] = raise ERR "CC" "empty"
  | CC l =
   let
      val (f, lst) = Lib.front_last l
      val mk = if listSyntax.is_list_type (Term.type_of lst)
                  then listSyntax.mk_append
               else wordsSyntax.mk_word_concat
   in
      List.foldr mk lst f
   end

(* Equality *)

fun EQ (x, y) = boolSyntax.mk_eq (x, y)

(* Monad operations *)

(* Return/Unit *)

val MU = state_transformerSyntax.mk_unit o (I ## Ty)

(* Bind *)

val MB = state_transformerSyntax.mk_bind

(* Read *)

val MR = state_transformerSyntax.mk_read

(* Write *)

val MW = state_transformerSyntax.mk_write

(* Narrow *)

val MN = state_transformerSyntax.mk_narrow

(* Widen *)

val MD = state_transformerSyntax.mk_widen o (I ## Ty)

(* For-loop *)

val For = HolKernel.mk_monop state_transformerSyntax.for_tm

(* ------------------------------------------------------------------------ *)

(* Primitive binary and unary operations *)

datatype monop =
     Abs
   | Bin
   | BNot
   | Cast of ParseDatatype.pretype
   | Dec
   | Flat
   | FPAbs of int
   | FPAdd of int
   | FPEqual of int
   | FPIsNaN of int
   | FPLess of int
   | FPMul of int
   | FPNeg of int
   | FPSub of int
   | Fst
   | Head
   | Hex
   | IsAlpha
   | IsAlphaNum
   | IsDigit
   | IsHexDigit
   | IsLower
   | IsSome
   | IsSpace
   | IsUpper
   | K1 of ParseDatatype.pretype
   | Length
   | Log
   | Max
   | Min
   | Msb
   | Neg
   | Not
   | PadLeft
   | PadRight
   | Rev
   | SE of ParseDatatype.pretype
   | Size
   | Smax
   | Smin
   | Snd
   | SofL
   | Some
   | Tail
   | ToLower
   | ToUpper
   | ValOf

datatype binop =
     Add
   | And
   | Asr
   | BAnd
   | BOr
   | BXor
   | Bit
   | Div
   | Exp
   | Fld
   | Ge
   | Gt
   | In
   | Insert
   | Le
   | Lsl
   | Lsr
   | Lt
   | Mdfy
   | Mod
   | Mul
   | Or
   | Quot
   | Rem
   | Rep
   | Rol
   | Ror
   | Splitl
   | Splitr
   | Sub
   | Tok
   | Uge
   | Ugt
   | Ule
   | Ult

local
   val m =
      ref (Redblackmap.mkDict String.compare : (string, term) Redblackmap.dict)
in
   fun string2enum ty =
      let
         val name = fst (Type.dest_type ty)
      in
         case Redblackmap.peek (!m, name) of
            SOME tm => tm
          | NONE =>
              let
                 val tm = ty
                          |> stringLib.Define_string2enum
                          |> Thm.concl
                          |> boolSyntax.dest_forall
                          |> snd
                          |> boolSyntax.lhs
                          |> boolSyntax.rator
              in
                 m := Redblackmap.insert (!m, name, tm)
                 ; tm
              end
      end
end

local
   val m =
      ref (Redblackmap.mkDict String.compare : (string, term) Redblackmap.dict)
in
   fun enum2string ty =
      let
         val name = fst (Type.dest_type ty)
      in
         case Redblackmap.peek (!m, name) of
            SOME tm => tm
          | NONE =>
              let
                 val tm = ty
                          |> stringLib.Define_enum2string
                          |> Thm.concl
                          |> boolSyntax.strip_conj
                          |> hd
                          |> boolSyntax.lhs
                          |> boolSyntax.rator
              in
                 m := Redblackmap.insert (!m, name, tm)
                 ; tm
              end
      end
end

local
   local
      val try_pbeta =
         Lib.total (boolSyntax.rhs o Thm.concl o PairedLambda.PAIRED_BETA_CONV)
   in
      fun pbeta t = Option.getOpt (try_pbeta t, t)
   end

   val one_tm = numSyntax.mk_numeral Arbnum.one
   val t_tm = ``#"t"``
   val f_tm = ``#"f"``

   fun mk_w tm ty = wordsSyntax.mk_n2w (tm, wordsSyntax.dest_word_type ty)
   val mk_word0 = mk_w numSyntax.zero_tm
   val mk_word1 = mk_w one_tm

   val mk_map = Lib.curry boolSyntax.mk_icomb listSyntax.map_tm
   val lower_tm = mk_map stringSyntax.tolower_tm
   val upper_tm = mk_map stringSyntax.toupper_tm
   fun mk_lower tm = Term.mk_comb (lower_tm, tm)
   fun mk_upper tm = Term.mk_comb (upper_tm, tm)

   val pad_left_tm = ``\(a:'a, b, c). list$PAD_LEFT a b c``
   val pad_right_tm = ``\(a:'a, b, c). list$PAD_RIGHT a b c``
   fun mk_pad_left tm  = pbeta (boolSyntax.mk_icomb (pad_left_tm, tm))
   fun mk_pad_right tm = pbeta (boolSyntax.mk_icomb (pad_right_tm, tm))

   fun enum2num ty =
      Lib.with_exn mk_local_const
        (typeName ty ^ "2num", Type.--> (ty, numLib.num))
        (ERR "pickCast" "enum2num not found")

   fun num2enum ty =
      Lib.with_exn mk_local_const
        ("num2" ^ typeName ty, Type.--> (numLib.num, ty))
        (ERR "pickCast" "num2enum not found")

   fun mk_test a b c d = boolSyntax.mk_cond (boolSyntax.mk_eq (a, b), c, d)

   val string2bool =
      let
         val v = Term.mk_var ("s", stringSyntax.string_ty)
      in
         Term.mk_abs (v,
            mk_test v (stringSyntax.fromMLstring "true") boolSyntax.T
              (mk_test v (stringSyntax.fromMLstring "false") boolSyntax.F
                 (boolSyntax.mk_arb Type.bool)))
      end

   val fstTy = fst o pairSyntax.dest_prod o Term.type_of

   fun s f (tm1:term) tm2 = pairSyntax.mk_uncurry (f tm2 tm1, tm2)

   fun ialpha tm =
      Term.inst [Type.alpha |-> wordsSyntax.dest_word_type (fstTy tm)]

   fun mk_from_bool (x as (tm, a, b)) =
      if tm = boolSyntax.T
         then a
      else if tm = boolSyntax.F
         then b
      else boolSyntax.mk_cond x

   val mk_word_min  = s ialpha wordsSyntax.word_min_tm
   val mk_word_max  = s ialpha wordsSyntax.word_max_tm
   val mk_word_smin = s ialpha wordsSyntax.word_smin_tm
   val mk_word_smax = s ialpha wordsSyntax.word_smax_tm

   val mk_num_min = s (K I) numSyntax.min_tm
   val mk_num_max = s (K I) numSyntax.max_tm
   val mk_int_min = s (K I) intSyntax.min_tm
   val mk_int_max = s (K I) intSyntax.max_tm

   fun mk_rev tm =
      (if Lib.can wordsSyntax.dim_of tm
          then wordsSyntax.mk_word_reverse
       else listSyntax.mk_reverse) tm

   val c_mk_comb = Lib.curry Term.mk_comb

   fun mk_from_enum ty =
      SOME (Lib.curry Term.mk_comb (enum2num ty)) handle HOL_ERR _ => NONE

   fun mk_fp_binop f =
      let
         val ftm = case f of
                      FPEqual 32 => machine_ieeeSyntax.fp32Syntax.fp_equal_tm
                    | FPEqual 64 => machine_ieeeSyntax.fp64Syntax.fp_equal_tm
                    | FPLess 32 => machine_ieeeSyntax.fp32Syntax.fp_lessThan_tm
                    | FPLess 64 => machine_ieeeSyntax.fp64Syntax.fp_lessThan_tm
                    | _ => raise ERR "mk_fp_binop" ""
         val ty = ftm |> Term.type_of |> Type.dom_rng |> fst
         val b = Term.mk_var ("b", ty)
         val c = Term.mk_var ("c", ty)
         val l = [b, c]
         val p = pairSyntax.list_mk_pair l
         val ptm = pairSyntax.mk_pabs (p, Term.list_mk_comb (ftm, l))
      in
         fn tm => pbeta (Term.mk_comb (ptm, tm))
      end

   fun mk_fp_triop f =
      let
         val ftm = case f of
                      FPAdd 32 => machine_ieeeSyntax.fp32Syntax.fp_add_tm
                    | FPAdd 64 => machine_ieeeSyntax.fp64Syntax.fp_add_tm
                    | FPMul 32 => machine_ieeeSyntax.fp32Syntax.fp_mul_tm
                    | FPMul 64 => machine_ieeeSyntax.fp64Syntax.fp_mul_tm
                    | FPSub 32 => machine_ieeeSyntax.fp32Syntax.fp_sub_tm
                    | FPSub 64 => machine_ieeeSyntax.fp64Syntax.fp_sub_tm
                    | _ => raise ERR "mk_fp_triop" ""
         val ty = ftm |> Term.type_of
                      |> Type.dom_rng |> snd
                      |> Type.dom_rng |> fst
         val a = Term.mk_var ("a", binary_ieeeSyntax.rounding_ty)
         val b = Term.mk_var ("b", ty)
         val c = Term.mk_var ("c", ty)
         val l = [a, b, c]
         val p = pairSyntax.list_mk_pair l
         val ptm = pairSyntax.mk_pabs (p, Term.list_mk_comb (ftm, l))
      in
         fn tm => pbeta (Term.mk_comb (ptm, tm))
      end

   fun pickCast ty2 tm =
      let
         val ty1 = Term.type_of tm
         val dw = wordsSyntax.dest_word_type
      in
         if wordsSyntax.is_word_type ty1
            then if wordsSyntax.is_word_type ty2
                    then wordsSyntax.mk_w2w (tm, dw ty2)
                 else if ty2 = bitstringSyntax.bitstring_ty
                    then bitstringSyntax.mk_w2v tm
                 else if ty2 = numSyntax.num
                    then wordsSyntax.mk_w2n tm
                 else if ty2 = intSyntax.int_ty
                    then integer_wordSyntax.mk_w2i tm
                 else if ty2 = stringSyntax.string_ty
                    then wordsSyntax.mk_word_to_hex_string tm
                 else if ty2 = Type.bool
                    then boolSyntax.mk_neg (boolSyntax.mk_eq (tm, mk_word0 ty1))
                 else if ty2 = stringSyntax.char_ty
                    then stringSyntax.mk_chr (wordsSyntax.mk_w2n tm)
                 else Term.mk_comb (num2enum ty2, wordsSyntax.mk_w2n tm)
         else if ty1 = bitstringSyntax.bitstring_ty
            then if wordsSyntax.is_word_type ty2
                    then bitstringSyntax.mk_v2w (tm, dw ty2)
                 else if ty2 = bitstringSyntax.bitstring_ty
                    then tm
                 else if ty2 = numSyntax.num
                    then bitstringSyntax.mk_v2n tm
                 else if ty2 = intSyntax.int_ty
                    then intSyntax.mk_injected (bitstringSyntax.mk_v2n tm)
                 else if ty2 = stringSyntax.string_ty
                    then bitstringSyntax.mk_v2s tm
                 else if ty2 = Type.bool
                    then boolSyntax.mk_neg (boolSyntax.mk_eq
                           (bitstringSyntax.mk_v2n tm, numSyntax.zero_tm))
                 else if ty2 = stringSyntax.char_ty
                    then stringSyntax.mk_chr (bitstringSyntax.mk_v2n tm)
                 else Term.mk_comb (num2enum ty2, bitstringSyntax.mk_v2n tm)
         else if ty1 = numSyntax.num
            then if wordsSyntax.is_word_type ty2
                    then wordsSyntax.mk_n2w (tm, dw ty2)
                 else if ty2 = bitstringSyntax.bitstring_ty
                    then bitstringSyntax.mk_n2v tm
                 else if ty2 = numSyntax.num
                    then tm
                 else if ty2 = intSyntax.int_ty
                    then intSyntax.mk_injected tm
                 else if ty2 = stringSyntax.string_ty
                    then ASCIInumbersSyntax.mk_num_to_dec_string tm
                 else if ty2 = Type.bool
                    then boolSyntax.mk_neg (boolSyntax.mk_eq
                           (tm, numSyntax.zero_tm))
                 else if ty2 = stringSyntax.char_ty
                    then stringSyntax.mk_chr tm
                 else Term.mk_comb (num2enum ty2, tm)
         else if ty1 = intSyntax.int_ty
            then if wordsSyntax.is_word_type ty2
                    then integer_wordSyntax.mk_i2w (tm, dw ty2)
                 else if ty2 = bitstringSyntax.bitstring_ty
                    then bitstringSyntax.mk_n2v (intSyntax.mk_Num tm)
                 else if ty2 = numSyntax.num
                    then intSyntax.mk_Num tm
                 else if ty2 = intSyntax.int_ty
                    then tm
                 else if ty2 = stringSyntax.string_ty
                    then integer_wordSyntax.mk_toString tm
                 else if ty2 = Type.bool
                    then boolSyntax.mk_neg (boolSyntax.mk_eq
                           (tm, intSyntax.zero_tm))
                 else if ty2 = stringSyntax.char_ty
                    then stringSyntax.mk_chr (intSyntax.mk_Num tm)
                 else Term.mk_comb (num2enum ty2, intSyntax.mk_Num tm)
         else if ty1 = stringSyntax.string_ty
            then if wordsSyntax.is_word_type ty2
                    then wordsSyntax.mk_word_from_hex_string (tm, dw ty2)
                 else if ty2 = bitstringSyntax.bitstring_ty
                    then bitstringSyntax.mk_s2v tm
                 else if ty2 = numSyntax.num
                    then ASCIInumbersSyntax.mk_num_from_dec_string tm
                 else if ty2 = intSyntax.int_ty
                    then integer_wordSyntax.mk_fromString tm
                 else if ty2 = stringSyntax.string_ty
                    then tm
                 else if ty2 = Type.bool
                    then Term.mk_comb (string2bool, tm)
                 else if ty2 = stringSyntax.char_ty
                    then stringSyntax.mk_tochar tm
                 else Term.mk_comb (string2enum ty2, tm)
         else if ty1 = Type.bool
            then if wordsSyntax.is_word_type ty2
                    then mk_from_bool (tm, mk_word1 ty2, mk_word0 ty2)
                 else if ty2 = bitstringSyntax.bitstring_ty
                    then mk_from_bool (tm,
                           bitstringSyntax.bitstring_of_binstring "1",
                           bitstringSyntax.bitstring_of_binstring "0")
                 else if ty2 = numSyntax.num
                    then mk_from_bool (tm, one_tm, numSyntax.zero_tm)
                 else if ty2 = intSyntax.int_ty
                    then mk_from_bool (tm,
                           intSyntax.one_tm, intSyntax.zero_tm)
                 else if ty2 = stringSyntax.string_ty
                    then mk_from_bool (tm,
                           stringSyntax.fromMLstring "true",
                           stringSyntax.fromMLstring "false")
                 else if ty2 = Type.bool
                    then tm
                 else if ty2 = stringSyntax.char_ty
                    then mk_from_bool (tm, t_tm, f_tm)
                 else raise ERR "pickCast" "bool -> ?"
         else if ty1 = stringSyntax.char_ty
            then if wordsSyntax.is_word_type ty2
                    then wordsSyntax.mk_n2w (stringSyntax.mk_ord tm, dw ty2)
                 else if ty2 = bitstringSyntax.bitstring_ty
                    then bitstringSyntax.mk_n2v (stringSyntax.mk_ord tm)
                 else if ty2 = numSyntax.num
                    then stringSyntax.mk_ord tm
                 else if ty2 = intSyntax.int_ty
                    then intSyntax.mk_injected (stringSyntax.mk_ord tm)
                 else if ty2 = stringSyntax.string_ty
                    then stringSyntax.mk_str tm
                 else if ty2 = Type.bool
                    then boolSyntax.mk_eq (tm, t_tm)
                 else if ty2 = stringSyntax.char_ty
                    then tm
                 else Term.mk_comb (num2enum ty2, stringSyntax.mk_ord tm)
         else case mk_from_enum ty1 of
                 SOME e2n =>
                    if wordsSyntax.is_word_type ty2
                       then wordsSyntax.mk_n2w (e2n tm, dw ty2)
                    else if ty2 = bitstringSyntax.bitstring_ty
                       then bitstringSyntax.mk_n2v (e2n tm)
                    else if ty2 = numSyntax.num
                       then e2n tm
                    else if ty2 = intSyntax.int_ty
                       then intSyntax.mk_injected (e2n tm)
                    else if ty2 = stringSyntax.string_ty
                       then Term.mk_comb (enum2string ty1, tm)
                    else if ty2 = Type.bool
                       then boolSyntax.mk_neg (boolSyntax.mk_eq
                              (tm, hd (TypeBase.constructors_of ty1)))
                    else if ty2 = stringSyntax.char_ty
                       then stringSyntax.mk_chr (e2n tm)
                    else Term.mk_comb (num2enum ty2, e2n tm)
               | _ => raise ERR "pickCast"
                        ("bad domain: " ^ typeName ty1 ^ " -> " ^ typeName ty2)
      end

      fun pick (a, b, c) tm =
         let
            val ty = Term.type_of tm
         in
            Option.valOf
              (if Option.isSome a andalso wordsSyntax.is_word_type ty
                  then a
               else if Option.isSome b andalso ty = bitstringSyntax.bitstring_ty
                  then b
               else if Option.isSome c andalso ty = intSyntax.int_ty
                  then c
               else raise ERR "Mop" "pick") tm
         end

      fun pickMinMax (a, b, c) tm =
         let
            val ty = fstTy tm
         in
           (if wordsSyntax.is_word_type ty
               then a
            else if ty = numSyntax.num
               then b
            else if ty = intSyntax.int_ty
               then c
            else raise ERR "Mop" "pickMinMax") tm
         end
in
   fun Mop (m : monop, x) =
      (case m of
         BNot => wordsSyntax.mk_word_1comp
       | Bin => ASCIInumbersSyntax.mk_fromBinString
       | Dec => ASCIInumbersSyntax.mk_fromDecString
       | Hex => ASCIInumbersSyntax.mk_fromHexString
       | Flat => listSyntax.mk_flat
       | Fst => pairSyntax.mk_fst
       | Head => listSyntax.mk_hd
       | IsAlpha => stringSyntax.mk_isalpha
       | IsAlphaNum => stringSyntax.mk_isalphanum
       | IsDigit => stringSyntax.mk_isdigit
       | IsHexDigit => stringSyntax.mk_ishexdigit
       | IsLower => stringSyntax.mk_islower
       | IsSpace => stringSyntax.mk_isspace
       | IsUpper => stringSyntax.mk_isupper
       | IsSome => optionSyntax.mk_is_some
       | Length => listSyntax.mk_length
       | Msb => wordsSyntax.mk_word_msb
       | Not => boolSyntax.mk_neg
       | PadLeft => mk_pad_left
       | PadRight => mk_pad_right
       | Rev => mk_rev
       | Smax => mk_word_smax
       | Smin => mk_word_smin
       | Snd => pairSyntax.mk_snd
       | SofL => listSyntax.mk_list_to_set
       | Some => optionSyntax.mk_some
       | Tail => listSyntax.mk_tl
       | ToLower => mk_lower
       | ToUpper => mk_upper
       | ValOf => optionSyntax.mk_the
       | Min => pickMinMax (mk_word_min, mk_num_min, mk_int_min)
       | Max => pickMinMax (mk_word_max, mk_num_max, mk_int_max)
       | Abs => pick (SOME wordsSyntax.mk_word_abs, NONE,
                      SOME intSyntax.mk_absval)
       | Neg => pick (SOME wordsSyntax.mk_word_2comp, NONE,
                      SOME intSyntax.mk_negated)
       | Size => wordsSyntax.mk_word_len
       | Log => pick (SOME wordsSyntax.mk_word_log2,
                      SOME bitSyntax.mk_log2, NONE)
       | K1 ty => (fn tm => combinSyntax.mk_K_1 (tm, Ty ty))
       | SE ty =>
           (fn tm =>
              wordsSyntax.mk_sw2sw (tm, wordsSyntax.dest_word_type (Ty ty)))
       | Cast ty => pickCast (Ty ty)
       | FPAbs 32 => machine_ieeeSyntax.fp32Syntax.mk_fp_abs
       | FPAbs 64 => machine_ieeeSyntax.fp64Syntax.mk_fp_abs
       | FPAbs i => raise ERR "Mop" ("FPAbs " ^ Int.toString i)
       | FPIsNaN 32 => machine_ieeeSyntax.fp32Syntax.mk_fp_isNan
       | FPIsNaN 64 => machine_ieeeSyntax.fp64Syntax.mk_fp_isNan
       | FPIsNaN i => raise ERR "Mop" ("FPIsNaN " ^ Int.toString i)
       | FPNeg 32 => machine_ieeeSyntax.fp32Syntax.mk_fp_negate
       | FPNeg 64 => machine_ieeeSyntax.fp64Syntax.mk_fp_negate
       | FPNeg i => raise ERR "Mop" ("FPNeg " ^ Int.toString i)
       | FPEqual _ => mk_fp_binop m
       | FPLess _ => mk_fp_binop m
       | _ => mk_fp_triop m
      ) x
end

local
   fun pick (a, b, c, d) (tm1, tm2: term) : term =
      let
         val ty = Term.type_of tm1
      in
         Option.valOf
           (if Option.isSome a andalso wordsSyntax.is_word_type ty
               then a
            else if Option.isSome b andalso ty = bitstringSyntax.bitstring_ty
               then b
            else if Option.isSome c andalso ty = numSyntax.num
               then c
            else if Option.isSome d andalso ty = intSyntax.int_ty
               then d
            else raise ERR "Bop" "pick") (tm1, tm2)
      end
   fun pickShift (a, b) (tm1 : term, tm2) : term =
      (if wordsSyntax.is_word_type (Term.type_of tm2) then a else b) (tm1, tm2)
   fun COMM f (x, y) = f (y, x)
   fun icurry tm =
       Term.mk_comb
          (Term.inst [Type.alpha |-> numSyntax.num, Type.beta |-> Type.bool,
                      Type.gamma |-> Type.bool] pairSyntax.curry_tm, tm)
   fun mk_modify (f, a) = wordsSyntax.mk_word_modify (icurry f, a)
in
   fun Bop (b : binop, x, y) = (x, y) |>
     (case b of
        And    => boolSyntax.mk_conj
      | BAnd   => wordsSyntax.mk_word_and
      | BOr    => wordsSyntax.mk_word_or
      | BXor   => wordsSyntax.mk_word_xor
      | In     => pred_setSyntax.mk_in
      | Insert => pred_setSyntax.mk_insert
      | Mdfy   => mk_modify
      | Or     => boolSyntax.mk_disj
      | Uge    => wordsSyntax.mk_word_hs
      | Ugt    => wordsSyntax.mk_word_hi
      | Ule    => wordsSyntax.mk_word_ls
      | Ult    => wordsSyntax.mk_word_lo
      | Splitl => rich_listSyntax.mk_splitl
      | Splitr => rich_listSyntax.mk_splitr
      | Fld    => stringSyntax.mk_fields
      | Tok    => stringSyntax.mk_tokens
      | Lt   => pick (SOME wordsSyntax.mk_word_lt, NONE,
                      SOME numSyntax.mk_less, SOME intSyntax.mk_less)
      | Gt   => pick (SOME wordsSyntax.mk_word_gt, NONE,
                      SOME numSyntax.mk_greater, SOME intSyntax.mk_great)
      | Le   => pick (SOME wordsSyntax.mk_word_le, NONE,
                      SOME numSyntax.mk_leq, SOME intSyntax.mk_leq)
      | Ge   => pick (SOME wordsSyntax.mk_word_ge, NONE,
                      SOME numSyntax.mk_geq, SOME intSyntax.mk_geq)
      | Bit  => pick (SOME (COMM wordsSyntax.mk_word_bit),
                      SOME (COMM bitstringSyntax.mk_testbit), NONE, NONE)
      | Add  => pick (SOME wordsSyntax.mk_word_add,
                      SOME bitstringSyntax.mk_add, SOME numSyntax.mk_plus,
                      SOME intSyntax.mk_plus)
      | Sub  => pick (SOME wordsSyntax.mk_word_sub, NONE,
                      SOME numSyntax.mk_minus, SOME intSyntax.mk_minus)
      | Mul  => pick (SOME wordsSyntax.mk_word_mul, NONE,
                      SOME numSyntax.mk_mult, SOME intSyntax.mk_mult)
      | Div  => pick (SOME wordsSyntax.mk_word_div, NONE,
                      SOME numSyntax.mk_div, SOME intSyntax.mk_div)
      | Mod  => pick (SOME wordsSyntax.mk_word_mod, NONE,
                      SOME numSyntax.mk_mod, SOME intSyntax.mk_mod)
      | Quot => pick (SOME wordsSyntax.mk_word_sdiv, NONE, NONE,
                      SOME intSyntax.mk_quot)
      | Rem  => pick (SOME wordsSyntax.mk_word_srem, NONE, NONE,
                      SOME intSyntax.mk_rem)
      | Rep  => pick (SOME (wordsSyntax.mk_word_replicate o Lib.swap),
                      SOME bitstringSyntax.mk_replicate, NONE, NONE)
      | Exp  => pick (NONE, NONE, SOME numSyntax.mk_exp, SOME intSyntax.mk_exp)
      | Lsl  => pick (SOME (pickShift (wordsSyntax.mk_word_lsl_bv,
                                       wordsSyntax.mk_word_lsl)),
                      SOME bitstringSyntax.mk_shiftl, NONE, NONE)
      | Ror  => pick (SOME (pickShift (wordsSyntax.mk_word_ror_bv,
                                       wordsSyntax.mk_word_ror)),
                      SOME bitstringSyntax.mk_rotate, NONE, NONE)
      | Lsr  => pickShift (wordsSyntax.mk_word_lsr_bv, wordsSyntax.mk_word_lsr)
      | Asr  => pickShift (wordsSyntax.mk_word_asr_bv, wordsSyntax.mk_word_asr)
      | Rol  => pickShift (wordsSyntax.mk_word_rol_bv, wordsSyntax.mk_word_rol))
end

(* ------------------------------------------------------------------------ *)

(* Definitions *)

local
   val tac = SRW_TAC [listSimps.LIST_ss, numSimps.ARITH_ss] []
in
   fun MEASURE_TAC tm =
      TotalDefn.WF_REL_TAC `^(boolSyntax.mk_icomb (numSyntax.measure_tm, tm))`
      THEN tac
end

fun new_def s x = Definition.new_definition (s ^ "_def", boolSyntax.mk_eq x)

fun z_def def =
   Feedback.trace ("Define.storage_message", 0)
   bossLib.zDefine [HOLPP.ANTIQUOTE (boolSyntax.mk_eq def)]

fun t_def s def m tac =
   Feedback.trace ("Define.storage_message", 0)
   (bossLib.tDefine s [HOLPP.ANTIQUOTE (boolSyntax.mk_eq def)])
     (MEASURE_TAC m THEN tac)

val mesg =
   Lib.with_flag
      (Feedback.MESG_to_string,
       fn s => (log_constant s; "Defined: " ^ s ^ "\n"))
      Feedback.HOL_MESG

fun Def (s, a, b) =
   let
      val ty = Type.--> (Term.type_of a, Term.type_of b)
      val c = Term.mk_var (s, ty)
      val isrec = (HolKernel.find_term (Lib.equal c) b; true)
                  handle HOL_ERR _ => false
      val def = if isrec andalso Term.is_abs b
                   then let
                           val (vs, b1) = Term.strip_abs b
                        in
                           (Term.list_mk_comb (c, a :: vs), b1)
                        end
                else (Term.mk_comb (c, a), b)
      val () = resetAnon ()
   in
      (if isrec then z_def else new_def s) def before mesg s
   end

fun tDef (s, a, b, m, t) =
   let
      val ty = Type.--> (Term.type_of a, Term.type_of b)
      val c = Term.mk_var (s, ty)
      val def = if Term.is_abs b
                   then let
                           val (vs, b1) = Term.strip_abs b
                        in
                           (Term.list_mk_comb (c, a :: vs), b1)
                        end
                else (Term.mk_comb (c, a), b)
      val () = resetAnon ()
   in
      t_def s def m t before mesg s
   end

fun Def0 (s, b) = new_def s (Term.mk_var (s, Term.type_of b), b) before mesg s

end (* Import *)
