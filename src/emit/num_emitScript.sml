open HolKernel boolLib bossLib Parse;
open EmitML numeralTheory whileTheory arithmeticTheory;
open combin_emitTheory pair_emitTheory;

val _ = new_theory "num_emit";

val addition_thms =
 let val thms = List.take(CONJUNCTS(SPEC_ALL numeral_add), 6)
 in REWRITE_RULE [iZ] (LIST_CONJ thms)
 end;

val T_INTRO = Q.prove(`!x. x = (x = T)`, REWRITE_TAC []);
val F_INTRO = Q.prove(`!x. ~x = (x = F)`, REWRITE_TAC []);

val (even,odd) =
  let val [a,b,c,d,e,f] = CONJUNCTS (SPEC_ALL numeral_evenodd)
      val [a',b',f'] = map (PURE_ONCE_REWRITE_RULE [T_INTRO]) [a,b,f]
      val [c',d',e'] = map (PURE_REWRITE_RULE [F_INTRO]) [c,d,e]
  in
     (LIST_CONJ [a',b',c'], LIST_CONJ [d',e',f'])
  end;

val DIV_FAIL = Q.prove
(`!m.  m DIV ZERO = FAIL $DIV ^(mk_var("zero denominator",bool)) m ZERO`,
REWRITE_TAC [combinTheory.FAIL_THM]);

val MOD_FAIL = Q.prove
(`!m.  m MOD ZERO = FAIL $MOD ^(mk_var("zero denominator",bool)) m ZERO`,
REWRITE_TAC [combinTheory.FAIL_THM]);

val (div_eqns, mod_eqns) =
 let val [a,b,c,d] = CONJUNCTS DIVMOD_NUMERAL_CALC
 in (CONJ DIV_FAIL (CONJ a b),
     CONJ MOD_FAIL (CONJ c d))
 end;

val _ =
  ConstMapML.prim_insert (Term.prim_mk_const{Name="0",Thy="num"},
    (true,"num","ZERO",Type.mk_type("num",[])));

val defs = map DEFN
  [numeral_suc,iZ,iiSUC,addition_thms,
   numeral_lt, numeral_lte,GREATER_DEF,GREATER_OR_EQ,
   numeral_pre,iDUB_removal,iSUB_THM, numeral_sub,
   numeral_mult,iSQR,numeral_exp,even,odd,
   numeral_fact,numeral_funpow,numeral_MIN,numeral_MAX,
   WHILE,LEAST_DEF,REWRITE_RULE [TIMES2,GSYM iDUB] findq_thm,
   DIVMOD_THM,div_eqns, mod_eqns,
   numeral_div2,REWRITE_RULE [iMOD_2EXP] numeral_imod_2exp,DIV_2EXP,
   prim_recTheory.measure_thm]

val _ = EmitML.reshape_thm_hook :=
    (Rewrite.PURE_REWRITE_RULE [arithmeticTheory.NUMERAL_DEF] o
     !EmitML.reshape_thm_hook);

val _ = eSML "num"
    (EQDATATYPE ([], `num = ZERO | BIT1 of num | BIT2 of num`)
     :: OPEN ["combin"]
     :: MLSTRUCT "val num_size = I" (* Not sure this is needed *)
     :: MLSTRUCT "fun NUMERAL x = x"   (* Not sure this is needed *)
     :: MLSTRUCT "val ONE = BIT1 ZERO"
     :: (defs @
     [MLSIG "val num_size : num -> num",
      MLSIG "val NUMERAL  :num -> num",
      MLSIG "val ZERO :num",
      MLSIG "val BIT1 :num -> num",
      MLSIG "val BIT2 :num -> num",
      MLSIG "val ONE :num",
      MLSIG "val TWO :num",
      MLSIG "val fromInt       : int -> num",
      MLSIG "val toInt         : num -> int option",
      MLSIG "val toBinString   : num -> string",
      MLSIG "val toOctString   : num -> string",
      MLSIG "val toDecString   : num -> string",
      MLSIG "val toHexString   : num -> string",
      MLSIG "val toString      : num -> string",
      MLSIG "val fromBinString : string -> num",
      MLSIG "val fromOctString : string -> num",
      MLSIG "val fromDecString : string -> num",
      MLSIG "val fromHexString : string -> num",
      MLSIG "val fromString    : string -> num",
      MLSIG "val ppBin  : ppstream -> num -> unit",
      MLSIG "val ppOct  : ppstream -> num -> unit",
      MLSIG "val ppDec  : ppstream -> num -> unit",
      MLSIG "val ppHex  : ppstream -> num -> unit",
      MLSIG "val pp_num : ppstream -> num -> unit",
      MLSTRUCT "\n\
\ (*---------------------------------------------------------------------------*)\n\
\ (* Supplementary ML, not generated from HOL theorems, aimed at supporting    *)\n\
\ (* parsing and pretty printing of numerals.                                  *)\n\
\ (*---------------------------------------------------------------------------*)\n\
\ \n\
\  val TWO = BIT2 ZERO;\n\
\  val THREE = BIT1 (BIT1 ZERO);\n\
\  val FOUR = BIT2 (BIT1 ZERO);\n\
\  val EIGHT = BIT2(BIT1(BIT1 ZERO));\n\
\  val TEN = BIT2(BIT2(BIT1 ZERO));\n\
\  val SIXTEEN = BIT2(BIT1(BIT1(BIT1 ZERO)));\n\
\\n\
\\n\
\  fun toBaseString divmod_b d n =\n\
\     let fun toBaseStr n s =\n\
\           if n = ZERO then\n\
\             if s = \"\" then \"0\" else s\n\
\           else let val (q, r) = divmod_b n in\n\
\             toBaseStr q (^(str (d r), s))\n\
\           end\n\
\     in\n\
\       toBaseStr n \"\"\n\
\     end\n\
\\n\
\  fun BIN ZERO = #\"0\"\n\
\    | BIN (BIT1 ZERO) = #\"1\"\n\
\    | BIN otherwise   = #\"?\";\n\
\\n\
\  fun UNBIN #\"0\" = ZERO\n\
\    | UNBIN #\"1\" = BIT1 ZERO\n\
\    | UNBIN other = raise Fail \"not a binary character\";\n\
\\n\
\  fun OCT ZERO = #\"0\"\n\
\    | OCT (BIT1 ZERO) = #\"1\"\n\
\    | OCT (BIT2 ZERO) = #\"2\"\n\
\    | OCT (BIT1(BIT1 ZERO)) = #\"3\"\n\
\    | OCT (BIT2(BIT1 ZERO)) = #\"4\"\n\
\    | OCT (BIT1(BIT2 ZERO)) = #\"5\"\n\
\    | OCT (BIT2(BIT2 ZERO)) = #\"6\"\n\
\    | OCT (BIT1(BIT1(BIT1 ZERO))) = #\"7\"\n\
\    | OCT otherwise = #\"?\";\n\
\\n\
\  fun UNOCT #\"0\" = ZERO\n\
\    | UNOCT #\"1\" = BIT1 ZERO\n\
\    | UNOCT #\"2\" = BIT2 ZERO\n\
\    | UNOCT #\"3\" = BIT1(BIT1 ZERO)\n\
\    | UNOCT #\"4\" = BIT2(BIT1 ZERO)\n\
\    | UNOCT #\"5\" = BIT1(BIT2 ZERO)\n\
\    | UNOCT #\"6\" = BIT2(BIT2 ZERO)\n\
\    | UNOCT #\"7\" = BIT1(BIT1(BIT1 ZERO))\n\
\    | UNOCT other = raise Fail \"not an octal character\";\n\
\\n\
\\n\
\  fun DIGIT ZERO = #\"0\"\n\
\    | DIGIT (BIT1 ZERO) = #\"1\"\n\
\    | DIGIT (BIT2 ZERO) = #\"2\"\n\
\    | DIGIT (BIT1(BIT1 ZERO)) = #\"3\"\n\
\    | DIGIT (BIT2(BIT1 ZERO)) = #\"4\"\n\
\    | DIGIT (BIT1(BIT2 ZERO)) = #\"5\"\n\
\    | DIGIT (BIT2(BIT2 ZERO)) = #\"6\"\n\
\    | DIGIT (BIT1(BIT1(BIT1 ZERO))) = #\"7\"\n\
\    | DIGIT (BIT2(BIT1(BIT1 ZERO))) = #\"8\"\n\
\    | DIGIT (BIT1(BIT2(BIT1 ZERO))) = #\"9\"\n\
\    | DIGIT otherwise = #\"?\";\n\
\\n\
\  fun UNDIGIT #\"0\" = ZERO\n\
\    | UNDIGIT #\"1\" = BIT1 ZERO\n\
\    | UNDIGIT #\"2\" = BIT2 ZERO\n\
\    | UNDIGIT #\"3\" = BIT1(BIT1 ZERO)\n\
\    | UNDIGIT #\"4\" = BIT2(BIT1 ZERO)\n\
\    | UNDIGIT #\"5\" = BIT1(BIT2 ZERO)\n\
\    | UNDIGIT #\"6\" = BIT2(BIT2 ZERO)\n\
\    | UNDIGIT #\"7\" = BIT1(BIT1(BIT1 ZERO))\n\
\    | UNDIGIT #\"8\" = BIT2(BIT1(BIT1 ZERO))\n\
\    | UNDIGIT #\"9\" = BIT1(BIT2(BIT1 ZERO))\n\
\    | UNDIGIT other = raise Fail \"not a decimal character\";\n\
\\n\
\  fun HEX ZERO = #\"0\"\n\
\    | HEX (BIT1 ZERO) = #\"1\"\n\
\    | HEX (BIT2 ZERO) = #\"2\"\n\
\    | HEX (BIT1(BIT1 ZERO)) = #\"3\"\n\
\    | HEX (BIT2(BIT1 ZERO)) = #\"4\"\n\
\    | HEX (BIT1(BIT2 ZERO)) = #\"5\"\n\
\    | HEX (BIT2(BIT2 ZERO)) = #\"6\"\n\
\    | HEX (BIT1(BIT1(BIT1 ZERO))) = #\"7\"\n\
\    | HEX (BIT2(BIT1(BIT1 ZERO))) = #\"8\"\n\
\    | HEX (BIT1(BIT2(BIT1 ZERO))) = #\"9\"\n\
\    | HEX (BIT2(BIT2(BIT1 ZERO))) = #\"A\"\n\
\    | HEX (BIT1(BIT1(BIT2 ZERO))) = #\"B\"\n\
\    | HEX (BIT2(BIT1(BIT2 ZERO))) = #\"C\"\n\
\    | HEX (BIT1(BIT2(BIT2 ZERO))) = #\"D\"\n\
\    | HEX (BIT2(BIT2(BIT2 ZERO))) = #\"E\"\n\
\    | HEX (BIT1(BIT1(BIT1(BIT1 ZERO)))) = #\"F\"\n\
\    | HEX otherwise = #\"?\";\n\
\\n\
\  fun UNHEX #\"0\" = ZERO\n\
\    | UNHEX #\"1\" = BIT1 ZERO\n\
\    | UNHEX #\"2\" = BIT2 ZERO\n\
\    | UNHEX #\"3\" = BIT1(BIT1 ZERO)\n\
\    | UNHEX #\"4\" = BIT2(BIT1 ZERO)\n\
\    | UNHEX #\"5\" = BIT1(BIT2 ZERO)\n\
\    | UNHEX #\"6\" = BIT2(BIT2 ZERO)\n\
\    | UNHEX #\"7\" = BIT1(BIT1(BIT1 ZERO))\n\
\    | UNHEX #\"8\" = BIT2(BIT1(BIT1 ZERO))\n\
\    | UNHEX #\"9\" = BIT1(BIT2(BIT1 ZERO))\n\
\    | UNHEX #\"a\" = BIT2(BIT2(BIT1 ZERO))\n\
\    | UNHEX #\"A\" = BIT2(BIT2(BIT1 ZERO))\n\
\    | UNHEX #\"b\" = BIT1(BIT1(BIT2 ZERO))\n\
\    | UNHEX #\"B\" = BIT1(BIT1(BIT2 ZERO))\n\
\    | UNHEX #\"c\" = BIT2(BIT1(BIT2 ZERO))\n\
\    | UNHEX #\"C\" = BIT2(BIT1(BIT2 ZERO))\n\
\    | UNHEX #\"d\" = BIT1(BIT2(BIT2 ZERO))\n\
\    | UNHEX #\"D\" = BIT1(BIT2(BIT2 ZERO))\n\
\    | UNHEX #\"e\" = BIT2(BIT2(BIT2 ZERO))\n\
\    | UNHEX #\"E\" = BIT2(BIT2(BIT2 ZERO))\n\
\    | UNHEX #\"f\" = BIT1(BIT1(BIT1(BIT1 ZERO)))\n\
\    | UNHEX #\"F\" = BIT1(BIT1(BIT1(BIT1 ZERO)))\n\
\    | UNHEX other = raise Fail \"not a hex character\";\n\
\\n\
\\n\
\  val toBinString = toBaseString (fn n => (DIV2 n, MOD_2EXP ONE n)) BIN;\n\
\  fun fromBinString dstr =\n\
\    let val nlist = List.map UNBIN (String.explode dstr)\n\
\    in\n\
\      List.foldl (fn (a,b) =>  + a ( * b TWO)) (hd nlist) (tl nlist)\n\
\    end;\n\
\\n\
\  val toDecString = toBaseString (fn n => DIVMOD(ZERO, (n, TEN))) DIGIT;\n\
\  fun fromDecString dstr =\n\
\    let val nlist = List.map UNDIGIT (String.explode dstr)\n\
\    in\n\
\      List.foldl (fn (a,b) =>  + a ( * b TEN)) (hd nlist) (tl nlist)\n\
\    end;\n\
\\n\
\  val toOctString = toBaseString\n\
\        (fn n => (DIV2 (DIV2 (DIV2 n)), MOD_2EXP THREE n)) OCT;\n\
\  fun fromOctString dstr =\n\
\    let val nlist = List.map UNOCT (String.explode dstr)\n\
\    in\n\
\      List.foldl (fn (a,b) =>  + a ( * b EIGHT)) (hd nlist) (tl nlist)\n\
\    end;\n\
\\n\
\  val toHexString = toBaseString\n\
\        (fn n => (DIV2 (DIV2 (DIV2 (DIV2 n))), MOD_2EXP FOUR n)) HEX;\n\
\  fun fromHexString dstr =\n\
\    let val nlist = List.map UNHEX (String.explode dstr)\n\
\    in\n\
\      List.foldl (fn (a,b) =>  + a ( * b SIXTEEN)) (hd nlist) (tl nlist)\n\
\    end;\n\
\\n\
\  (* Uncomment to add mappings to portableML/Arbnum.sml (+ add to signature)\n\
\\n\
\  fun Arbnum2num m =\n\
\        if m = Arbnum.zero then ZERO else\n\
\          let val n = Arbnum2num (Arbnum.div2 m) in\n\
\            if Arbnum.mod2 m = Arbnum.zero then\n\
\              iDUB n\n\
\            else\n\
\              BIT1 n\n\
\          end\n\
\\n\
\  fun num2Arbnum ZERO = Arbnum.zero\n\
\    | num2Arbnum (BIT1 n) = Arbnum.plus1(Arbnum.times2(num2Arbnum n))\n\
\    | num2Arbnum (BIT2 n) = Arbnum.plus2(Arbnum.times2(num2Arbnum n))\n\
\\n\
\  fun toDecString n = Arbnum.toString (num2Arbnum n);\n\
\  *)\n\
\\n\
\  (* Installed in MoscowML with Meta.installPP *)\n\
\\n\
\  fun ppBin ppstrm n = PP.add_string ppstrm (toBinString n);\n\
\  fun ppOct ppstrm n = PP.add_string ppstrm (toOctString n);\n\
\  fun ppDec ppstrm n = PP.add_string ppstrm (toDecString n);\n\
\  fun ppHex ppstrm n = PP.add_string ppstrm (toHexString n);\n\
\  val toString = toDecString;\n\
\  val fromString = fromDecString;\n\
\  val pp_num = ppHex;\n\
\\n\
\  fun fromInt i = fromDecString (Int.toString i)\n\
\  fun toInt n =\n\
\    let fun num2int ZERO = 0\n\
\      | num2int (BIT1 n) = Int.+(Int.*(2, num2int n), 1)\n\
\      | num2int (BIT2 n) = Int.+(Int.*(2, num2int n), 2)\n\
\    in\n\
\      SOME (num2int n) handle Overflow => NONE\n\
\    end;\n\n"]));

val _ = eCAML "num"
  (DATATYPE (`num = ZERO | BIT1 of num | BIT2 of num`)
  :: map MLSTRUCT
    ["let num_size x = x",
       "let _NUMERAL x = x",
       "let _ONE = BIT1 ZERO",
       "let _TWO = BIT2 ZERO"]
   @ defs
   @ map MLSIG
      ["val num_size : num -> num",
       "val _NUMERAL : num -> num",
       "val _ONE : num",
       "val _TWO : num",
       "val int_of_holnum     : num -> int",
       "val holnum_of_int     : int -> num",
       "val big_int_of_holnum : num -> Big_int.big_int",
       "val holnum_of_big_int : Big_int.big_int -> num",
       "val fromString : string -> num",
       "val toString   : num -> string"]
   @ map MLSTRUCT
      ["",
       "let rec int_of_holnum n = match n with\n\
       \    ZERO -> 0\n\
       \  | BIT1 x -> succ ((int_of_holnum x) lsl 1)\n\
       \  | BIT2 x -> Pervasives.(+) ((int_of_holnum x) lsl 1) 2",
       "",
       "let rec holnum_of_int n =\n\
       \    if n = 0 then ZERO\n\
       \    else let q = n / 2 and r = n mod 2 in\n\
       \         let m = holnum_of_int q in\n\
       \     if r = 0 then iDUB m else BIT1 m", "",
       "let rec big_int_of_holnum n = match n with\n\
       \    ZERO -> Big_int.zero_big_int\n\
       \  | BIT1 x -> Big_int.succ_big_int\n\
       \                (Big_int.mult_int_big_int 2 (big_int_of_holnum x))\n\
       \  | BIT2 x -> Big_int.add_int_big_int 2\n\
       \                (Big_int.mult_int_big_int 2 (big_int_of_holnum x))", "",
       "let rec holnum_of_big_int n =\n\
       \    if Big_int.eq_big_int n Big_int.zero_big_int then ZERO\n\
       \    else let (q,r) = Big_int.quomod_big_int n\
                              \ (Big_int.big_int_of_int 2) in\n\
       \         let m = holnum_of_big_int q in\n\
       \     if Big_int.eq_big_int r Big_int.zero_big_int then\
       \ iDUB m else BIT1 m", "",
       "let fromString s = holnum_of_big_int (Big_int.big_int_of_string s)",
       "let toString n = Big_int.string_of_big_int (big_int_of_holnum n)"]);

(*---------------------------------------------------------------------------*)
(* Map 0 and ZERO to the same thing in generated ML.                         *)
(*---------------------------------------------------------------------------*)
val _ = adjoin_to_theory
{sig_ps = NONE, struct_ps = SOME (fn ppstrm =>
  let val S = PP.add_string ppstrm
      fun NL() = PP.add_newline ppstrm
  in S "val _ = ConstMapML.prim_insert "; NL();
     S "         (Term.prim_mk_const{Name=\"0\",Thy=\"num\"},"; NL();
     S "          (true,\"num\",\"ZERO\",Type.mk_type(\"num\",[])));";
     NL()  end)};

(*---------------------------------------------------------------------------*)
(* Automatic rewrite for definitions                                         *)
(*---------------------------------------------------------------------------*)

val _ = adjoin_to_theory {sig_ps = NONE,
   struct_ps = SOME (fn ppstrm =>
     let val S = PP.add_string ppstrm
         fun NL() = PP.add_newline ppstrm
     in S "val _ = EmitML.reshape_thm_hook :=  "; NL();
        S "    (Rewrite.PURE_REWRITE_RULE [arithmeticTheory.NUMERAL_DEF] o "; NL();
        S "     !EmitML.reshape_thm_hook);";
        NL(); NL()
     end)}

val _ = export_theory ();
