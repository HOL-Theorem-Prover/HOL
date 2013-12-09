structure stringLib :> stringLib =
struct

open HolKernel boolLib numSyntax reduceLib
open stringTheory stringSyntax;

val ERR = mk_HOL_ERR "stringLib";

(*---------------------------------------------------------------------------
     Conversions.
 ---------------------------------------------------------------------------*)

val ORD_CHR_CONV =
   let
      val bound = numSyntax.term_of_int 256
      fun lt_thm m =
         Drule.EQT_ELIM (reduceLib.LT_CONV (numSyntax.mk_less (m, bound)))
      fun lemma m = Thm.EQ_MP (Thm.SPEC m stringTheory.ORD_CHR) (lt_thm m)
   in
      lemma o stringSyntax.dest_chr o stringSyntax.dest_ord
   end

fun refl_clause ty = Thm.INST_TYPE [Type.alpha |-> ty] boolTheory.REFL_CLAUSE

val char_EQ_CONV =
   let
      val conv = Conv.REWR_CONV stringTheory.CHAR_EQ_THM
                 THENC Conv.BINOP_CONV ORD_CHR_CONV
                 THENC reduceLib.NEQ_CONV
      val refl_clause_char = refl_clause stringSyntax.char_ty
      val is_char_lit = Lib.can stringSyntax.fromHOLchar
      val err = ERR "char_EQ_CONV" "not a ground char equality"
   in
      fn tm =>
         let
            val (c1, c2) = Lib.with_exn boolSyntax.dest_eq tm err
            val _ = is_char_lit c1 andalso is_char_lit c2 orelse raise err
         in
            if c1 = c2 then Thm.SPEC c1 refl_clause_char else conv tm
         end
   end

local
   val inst_to_string = Thm.INST_TYPE [Type.alpha |-> stringSyntax.char_ty]
   val cons_11_s = inst_to_string listTheory.CONS_11
   val not_cons_nil_s = inst_to_string listTheory.NOT_CONS_NIL
   val not_nil_cons_s = inst_to_string listTheory.NOT_NIL_CONS
   val refl_clause_string = refl_clause stringSyntax.string_ty
   val total_dest_cons = Lib.total listSyntax.dest_cons
   fun eqf_spec (a, b) = Drule.EQF_INTRO o Drule.SPECL [a, b]
   val err = ERR "string_EQ_CONV" "not a ground string equality"
   val bool_conv = REWRITE_CONV []
   fun string_EQ_CONV' tm =
      let
         val (c1, c2) = Lib.with_exn boolSyntax.dest_eq tm err
      in
         if c1 = c2
            then Thm.SPEC c1 refl_clause_string
         else case (total_dest_cons c1, total_dest_cons c2) of
                 (SOME (a, b), NONE) => eqf_spec (b, a) not_cons_nil_s
               | (NONE, SOME (a, b)) => eqf_spec (b, a) not_nil_cons_s
               | (SOME (a, b), SOME (c, d)) =>
                   let
                      val c_th = char_EQ_CONV (boolSyntax.mk_eq (a, c))
                      val th = Drule.SPECL [a, b, c, d] cons_11_s
                   in
                      if boolSyntax.rhs (Thm.concl c_th) = boolSyntax.T
                         then Conv.RIGHT_CONV_RULE
                                 (Conv.FORK_CONV (Lib.K c_th, string_EQ_CONV')
                                  THENC bool_conv) th
                      else Conv.RIGHT_CONV_RULE
                              (Conv.LAND_CONV (Lib.K c_th) THENC bool_conv) th
                   end
               | _ => raise err
      end
in
   fun string_EQ_CONV tm =
      let
         val (l, r) = Lib.with_exn boolSyntax.dest_eq tm err
         val _ = stringSyntax.is_string_literal l andalso
                 stringSyntax.is_string_literal r orelse raise err
      in
         string_EQ_CONV' tm
      end
end

val () = computeLib.add_funs [stringTheory.IMPLODE_EXPLODE_I]
val () = computeLib.add_convs [(stringSyntax.ord_tm, 1, ORD_CHR_CONV)]

val () = Defn.const_eq_ref :=
           (!Defn.const_eq_ref ORELSEC string_EQ_CONV ORELSEC char_EQ_CONV)

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
                                TypeBase.mk_pattern_fn css
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
