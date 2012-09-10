structure stringLib :> stringLib =
struct

open HolKernel boolLib numSyntax reduceLib stringTheory stringSyntax;

val ERR = mk_HOL_ERR "stringLib";

(*---------------------------------------------------------------------------
     Conversions.
 ---------------------------------------------------------------------------*)

local
   val bound = numSyntax.term_of_int 256
   fun cond m = EQT_ELIM (numLib.REDUCE_CONV (numSyntax.mk_less (m, bound)))
   fun lemma m = EQ_MP (Thm.SPEC m stringTheory.ORD_CHR) (cond m)
in
   val ORD_CHR_CONV = lemma o stringSyntax.dest_chr o stringSyntax.dest_ord
end

fun refl_clause ty = Thm.INST_TYPE [Type.alpha |-> ty] boolTheory.REFL_CLAUSE

val char_EQ_CONV =
   let
      open computeLib
      val compset = reduceLib.num_compset ()
      val _ = add_conv (stringSyntax.ord_tm, 1, ORD_CHR_CONV) compset
      val _ = add_thms [stringTheory.CHAR_EQ_THM] compset
      val conv = CBV_CONV compset
      val REFL_CLAUSE_char = refl_clause stringSyntax.char_ty
      val is_char_lit = Lib.can stringSyntax.fromHOLchar
   in
      fn tm =>
         case Lib.total dest_eq tm of
            NONE => raise ERR "char_EQ_CONV" "not a char equality"
          | SOME (c1, c2) =>
               if is_char_lit c1 andalso is_char_lit c2
                  then if c1 = c2 then SPEC c1 REFL_CLAUSE_char else conv tm
               else raise ERR "char_EQ_CONV" "not a char equality"
   end

val string_EQ_CONV =
   let
      open computeLib
      val compset = listSimps.list_compset ()
      val _ = add_conv (stringSyntax.ord_tm, 1, ORD_CHR_CONV) compset
      val _ = add_thms [stringTheory.CHAR_EQ_THM] compset
      val conv = CBV_CONV compset
      val REFL_CLAUSE_string = refl_clause stringSyntax.string_ty
   in
      fn tm =>
         case total dest_eq tm of
            NONE => raise ERR "string_EQ_CONV" "not a string equality"
          | SOME (s1, s2) =>
                if stringSyntax.is_string_literal s1
                   andalso stringSyntax.is_string_literal s2
                   then if s1 = s2 then SPEC s1 REFL_CLAUSE_string else conv tm
                else raise ERR "string_EQ_CONV" "not a string equality"
   end

val () = computeLib.add_funs [stringTheory.IMPLODE_EXPLODE_I]
val () = computeLib.add_convs [(stringSyntax.ord_tm, 1, ORD_CHR_CONV)]

val () = Defn.const_eq_ref :=
           (!Defn.const_eq_ref ORELSEC char_EQ_CONV ORELSEC string_EQ_CONV)

(*---------------------------------------------------------------------------
      Examples.

  val test = Count.apply (string_EQ_CONV o Term);

  test`"" = ""`;
  test`"a" = ""`;
  test`"" = "a"`;
  test`"" = "abc"`;
  test`"abcdefghijklmnopqrstuvwxyz" = "abcdefghijklmnopqrstuvwxyz"`;
  test`"abcdefghijklmnopqrstuvwxyz" = "abcdefghijklmnopqrstuvwxyzA"`;

 ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
     Define enum <-> string maps.
 ---------------------------------------------------------------------------*)

local
   val e2s = stringSyntax.fromMLstring o fst o Term.dest_const
in
   fun Define_string2enum ty =
      let
         val l = TypeBase.constructors_of ty
         val _ = List.all (Lib.equal ty o Term.type_of) l
                 orelse raise ERR "Define_string2enum" "not an enum type"
         val css = List.map (fn c => (e2s c, c)) l
         val cs = Lib.with_flag (Feedback.emit_MESG, false)
                    (Functional.mk_pattern_fn (TypeBase.theTypeBase ())) css
         val (v, b) = Term.dest_abs cs
         val name = "string2" ^ fst (Type.dest_type ty)
         val f = Term.mk_var (name, stringSyntax.string_ty --> ty)
         val d = Definition.new_definition
                   (name, boolSyntax.mk_eq (Term.mk_comb (f, v), b))
         val () = computeLib.add_funs [d]
      in
         d
      end
   fun Define_enum2string ty =
      let
         val l = TypeBase.constructors_of ty
         val _ = List.all (Lib.equal ty o Term.type_of) l
                 orelse raise ERR "Define_string2enum" "not an enum type"
         val name = fst (Type.dest_type ty) ^ "2string"
         val f = Term.mk_var (name, ty --> stringSyntax.string_ty)
         val cs =
            List.map (fn c => boolSyntax.mk_eq (Term.mk_comb (f, c), e2s c)) l
            |> boolSyntax.list_mk_conj
      in
         Feedback.trace ("Define.storage_message", 0)
            TotalDefn.Define [HOLPP.ANTIQUOTE cs]
      end
end

end
