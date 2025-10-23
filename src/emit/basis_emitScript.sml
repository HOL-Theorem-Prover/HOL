Theory basis_emit
Ancestors
  combin pair numeral While arithmetic pred_set option basicSize
  list rich_list string sum finite_map sorting bit numeral_bit
  fcp words integer integer_word numposrep ASCIInumbers pre_emit
Libs
  EmitML fcpLib intSyntax

(* == Combin ============================================================== *)

val defs = map DEFN [S_THM, K_THM, I_THM, W_THM, C_THM, o_THM, APPLY_UPDATE_THM]

val _ = eSML "combin" defs;
val _ = eCAML "combin" defs;

(* == Pair ================================================================ *)

val defs =
  map EmitML.DEFN [CURRY_DEF,UNCURRY_DEF,FST,SND,PAIR_MAP_THM,LEX_DEF_THM];

val _ = eSML "pair" defs;
val _ = eCAML "pair" defs;

val B = PP.block PP.CONSISTENT 0
val S = PP.add_string
val NL = PP.NL
val _ = ConstMapML.insert pairSyntax.comma_tm;

(* == Num ================================================================= *)

val addition_thms =
 let val thms = List.take(CONJUNCTS(SPEC_ALL numeral_add), 6)
 in REWRITE_RULE [iZ] (LIST_CONJ thms)
 end;

Theorem T_INTRO[local]:
  !x. x = (x = T)
Proof REWRITE_TAC []
QED
Theorem F_INTRO[local]:
  !x. ~x = (x = F)
Proof REWRITE_TAC []
QED

val (even,odd) =
  let val [a,b,c,d,e,f] = CONJUNCTS (SPEC_ALL numeral_evenodd)
      val [a',b',f'] = map (PURE_ONCE_REWRITE_RULE [T_INTRO]) [a,b,f]
      val [c',d',e'] = map (PURE_REWRITE_RULE [F_INTRO]) [c,d,e]
  in
     (LIST_CONJ [a',b',c'], LIST_CONJ [d',e',f'])
  end;

Theorem DIV_FAIL[local]:
  !m.  m DIV ZERO = FAIL $DIV ^(mk_var("zero denominator",bool)) m ZERO
Proof
REWRITE_TAC [combinTheory.FAIL_THM]
QED

Theorem MOD_FAIL[local]:
  !m.  m MOD ZERO = FAIL $MOD ^(mk_var("zero denominator",bool)) m ZERO
Proof
REWRITE_TAC [combinTheory.FAIL_THM]
QED

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

val _ = eSML "num"
    (EQDATATYPE ([], `num = ZERO | BIT1 num | BIT2 num`)
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
      MLSIG "val ppBin  : num PP.pprinter",
      MLSIG "val ppOct  : num PP.pprinter",
      MLSIG "val ppDec  : num PP.pprinter",
      MLSIG "val ppHex  : num PP.pprinter",
      MLSIG "val pp_num : num PP.pprinter",
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
\  fun ppBin n = PP.add_string (toBinString n);\n\
\  fun ppOct n = PP.add_string (toOctString n);\n\
\  fun ppDec n = PP.add_string (toDecString n);\n\
\  fun ppHex n = PP.add_string (toHexString n);\n\
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
  (DATATYPE (`num = ZERO | BIT1 num | BIT2 num`)
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
val _ = ConstMapML.prim_insert
                  (Term.prim_mk_const{Name="0",Thy="num"},
                   (true,"num","ZERO",Type.mk_type("num",[])));


(* == Set ================================================================= *)

(*---------------------------------------------------------------------------*)
(* Export an ML model of (finite) sets. Although the representation used in  *)
(* pred_set is 'a -> bool, the ML representation is a concrete type with     *)
(* constructors EMPTY and INSERT. Which is quite different, but we wanted to *)
(* be able to compute cardinality, which would not be possible with sets-as- *)
(* predicates. An alternative would be to have a parallel theory of finite   *)
(* sets, as in hol88, but that could lead to a proliferation of theories     *)
(* which required sets.                                                      *)
(*                                                                           *)
(* The implementation is not efficient. Insertion is constant time, but      *)
(* membership checks are linear and subset checks are quadratic.             *)
(*---------------------------------------------------------------------------*)

fun TAKE2 l = case List.take(l, 2) of [a,b] => (a,b)
  | _ => raise (mk_HOL_ERR "emitCAML" "TAKE2" "Not three elements");

val TAKE2_CONJUNCTS = TAKE2 o CONJUNCTS;

val F_INTRO = PURE_REWRITE_RULE [PROVE[] (Term `~x = (x = F)`)];
val T_INTRO = PURE_ONCE_REWRITE_RULE [PROVE[] (Term `x = (x = T)`)];

Theorem BIGINTER_EMPTY[local]:
  BIGINTER EMPTY = FAIL BIGINTER ^(mk_var("empty set",bool)) EMPTY
Proof
 REWRITE_TAC [combinTheory.FAIL_THM]
QED

Theorem MIN_SET_EMPTY[local]:
  MIN_SET EMPTY = FAIL MIN_SET ^(mk_var("empty set",bool)) EMPTY
Proof
 REWRITE_TAC [combinTheory.FAIL_THM]
QED

val (tyg,tmg) = (type_grammar(),term_grammar())
val tyg' = type_grammar.remove_abbreviation tyg "set"
val _ = temp_set_grammars(tyg',tmg)
val _ = new_type("set",1)
val _ = temp_clear_overloads_on "set"

Definition IS_EMPTY_def:  IS_EMPTY s = if s = {} then T else F
End
Theorem IS_EMPTY_THM[local]:
  (IS_EMPTY {} = T) /\ (IS_EMPTY (x INSERT s) = F)
Proof
 SRW_TAC[][IS_EMPTY_def]
QED
Theorem IS_EMPTY_REWRITE:
  ((s = {}) = IS_EMPTY s) /\ (({} = s) = IS_EMPTY s)
Proof
SRW_TAC[][EQ_IMP_THM,IS_EMPTY_def]
QED

val defs =
  map DEFN_NOSIG [CONJ (F_INTRO NOT_IN_EMPTY) IN_INSERT,
       CONJ (CONJUNCT1 UNION_EMPTY) INSERT_UNION,
       CONJ (CONJUNCT1 INTER_EMPTY) INSERT_INTER,
       CONJ EMPTY_DELETE DELETE_INSERT, CONJ DIFF_EMPTY DIFF_INSERT,
       CONJ (T_INTRO (SPEC_ALL EMPTY_SUBSET)) INSERT_SUBSET, PSUBSET_EQN,
       CONJ IMAGE_EMPTY IMAGE_INSERT, CONJ BIGUNION_EMPTY BIGUNION_INSERT,
       LIST_CONJ [BIGINTER_EMPTY,BIGINTER_SING, BIGINTER_INSERT],
       CONJ CARD_EMPTY (UNDISCH (SPEC_ALL CARD_INSERT)),
       CONJ (T_INTRO (CONJUNCT1 (SPEC_ALL DISJOINT_EMPTY))) DISJOINT_INSERT,
       CROSS_EQNS,
       listTheory.LIST_TO_SET_THM, IS_EMPTY_THM,
       let val (c1,c2) = TAKE2_CONJUNCTS (SPEC_ALL SUM_IMAGE_THM)
       in CONJ c1 (UNDISCH (SPEC_ALL c2)) end,
       let val (c1,c2) = TAKE2_CONJUNCTS SUM_SET_THM
       in CONJ c1 (UNDISCH (SPEC_ALL c2)) end,
       let val (c1,c2) = TAKE2_CONJUNCTS MAX_SET_THM
       in CONJ c1 (UNDISCH (SPEC_ALL c2)) end,
       CONJ MIN_SET_EMPTY MIN_SET_THM, count_EQN,POW_EQNS];

val _ = eSML "set"
   (ABSDATATYPE (["'a"], `set = EMPTY | INSERT 'a set`)
    :: OPEN ["num"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "val EMPTY    : 'a set"
    :: MLSIG "val INSERT   : 'a * 'a set -> 'a set"
    :: MLSIG "val IN       : ''a -> ''a set -> bool"
    :: MLSIG "val UNION    : ''a set -> ''a set -> ''a set"
    :: MLSIG "val INTER    : ''a set -> ''a set -> ''a set"
    :: MLSIG "val DELETE   : ''a set -> ''a -> ''a set"
    :: MLSIG "val DIFF     : ''a set -> ''a set -> ''a set"
    :: MLSIG "val SUBSET   : ''a set -> ''a set -> bool"
    :: MLSIG "val PSUBSET  : ''a set -> ''a set -> bool"
    :: MLSIG "val IMAGE    : ('a -> 'b) -> 'a set -> 'b set"
    :: MLSIG "val BIGUNION : ''a set set -> ''a set"
    :: MLSIG "val BIGINTER : ''a set set -> ''a set"
    :: MLSIG "val CARD     : ''a set -> num"
    :: MLSIG "val DISJOINT : ''a set -> ''a set -> bool"
    :: MLSIG "val CROSS    : ''a set -> ''b set -> (''a * ''b) set"
    :: MLSIG "val LIST_TO_SET : 'a list -> 'a set"
    :: MLSIG "val IS_EMPTY : 'a set -> bool"
    :: MLSIG "val SUM_IMAGE : (''a -> num) -> ''a set -> num"
    :: MLSIG "val SUM_SET  : num set -> num"
    :: MLSIG "val MAX_SET  : num set -> num"
    :: MLSIG "val MIN_SET  : num set -> num"
    :: MLSIG "val count    : num -> num set"
    :: MLSIG "val POW      : ''a set -> ''a set set"
    :: defs
    @ [MLSIG "val fromList : 'a list -> 'a set",
      MLSIG "val toList   : 'a set -> 'a list",
      MLSTRUCT "fun fromList alist =\
               \ listML.FOLDL (fn s => fn a => INSERT(a,s)) EMPTY alist",
      MLSTRUCT "fun toList EMPTY = []\n\
               \    | toList (INSERT(a,s)) = a::toList s"])

val _ = eCAML "set"
  (MLSIGSTRUCT
     ["type num = NumML.num", "",
      "type 'a set = EMPTY | INSERT of 'a * 'a set"] @
   map MLSIG
     ["val _IN        : 'a -> 'a set -> bool",
      "val _UNION     : 'a set -> 'a set -> 'a set",
      "val _INTER     : 'a set -> 'a set -> 'a set",
      "val _DELETE    : 'a set -> 'a -> 'a set",
      "val _DIFF      : 'a set -> 'a set -> 'a set",
      "val _SUBSET    : 'a set -> 'a set -> bool",
      "val _PSUBSET   : 'a set -> 'a set -> bool",
      "val _IMAGE     : ('a -> 'b) -> 'a set -> 'b set",
      "val _BIGUNION  : 'a set set -> 'a set",
      "val _BIGINTER  : 'a set set -> 'a set",
      "val _CARD      : 'a set -> num",
      "val _DISJOINT  : 'a set -> 'a set -> bool",
      "val _CROSS     : 'a set -> 'b set -> ('a * 'b) set",
      "val _SUM_IMAGE : ('a -> num) -> 'a set -> num",
      "val _SUM_SET   : num set -> num",
      "val _MAX_SET   : num set -> num",
      "val _MIN_SET   : num set -> num",
      "val count      : num -> num set",
      "val _POW       : 'a set -> 'a set set"] @
   defs)

(* == Option ============================================================== *)

Theorem THE_NONE[local]:
   THE NONE = FAIL THE ^(mk_var("applied to NONE",bool)) NONE
Proof
  REWRITE_TAC [combinTheory.FAIL_THM]
QED

val _ = ConstMapML.insert_cons(Term.prim_mk_const{Name="SOME",Thy="option"});
val _ = ConstMapML.insert_cons(Term.prim_mk_const{Name="NONE",Thy="option"});

val defs =
  map DEFN [OPTION_MAP_DEF, IS_SOME_DEF, IS_NONE_DEF,
            CONJ THE_NONE THE_DEF, OPTION_JOIN_DEF];

val _ = eSML "option"
  (MLSIGSTRUCT ["datatype option = datatype Option.option"] @ defs);

val _ = eCAML "option" defs;

(* == Option ============================================================== *)

val defs =
  map DEFN [bool_size_def, pair_size_def, one_size_def, option_size_def];

val _ = eSML "basicSize"
  (MLSIG "type num = numML.num" ::
   MLSIG "type 'a  option = 'a optionML.option" ::
   MLSIG "type ('a,'b) sum = ('a,'b) sumML.sum" ::
   OPEN ["num","sum","option"] ::
   defs);

val _ = eCAML "basicSize" (MLSIGSTRUCT ["type num = NumML.num"] @ defs);

(* == List ================================================================ *)

val LENGTH_THM = REWRITE_RULE [arithmeticTheory.ADD1] LENGTH;

Theorem HD_NIL[local]:
  HD [] = FAIL HD ^(mk_var("Empty list",bool)) []
Proof
                     REWRITE_TAC [combinTheory.FAIL_THM]
QED

Theorem TL_NIL[local]:
  TL [] = FAIL TL ^(mk_var("Empty list",bool)) []
Proof
                     REWRITE_TAC [combinTheory.FAIL_THM]
QED

Theorem MAP2_FAIL[local]:
  (!f h t.
   (MAP2 (f:'a->'b->'c) [] (h::t) =
    FAIL MAP2 ^(mk_var("unequal length lists",bool)) f [] (h::t))) /\
  !f h t.
    (MAP2 (f:'a->'b->'c) (h::t) [] =
     FAIL MAP2 ^(mk_var("unequal length lists",bool)) f (h::t) [])
Proof
 REWRITE_TAC [combinTheory.FAIL_THM]
QED

val MAP2_THM = let val [a,b] = CONJUNCTS MAP2
                   val [c,d] = CONJUNCTS MAP2_FAIL
               in LIST_CONJ [a,c,d,b]
               end;

Theorem ZIP_FAIL[local]:
  (!(h:'b) t. ZIP ([]:'a list,h::t) =
         FAIL ZIP ^(mk_var("unequal length lists",bool)) ([],h::t)) /\
  (!(h:'a) t. ZIP (h::t,[]:'b list) =
              FAIL ZIP ^(mk_var("unequal length lists",bool)) (h::t,[]))
Proof
 REWRITE_TAC [combinTheory.FAIL_THM]
QED

val ZIP_THM = let val [a,b] = CONJUNCTS ZIP
                  val [c,d] = CONJUNCTS ZIP_FAIL
               in LIST_CONJ [a,c,d,b]
               end;

Theorem LAST_NIL[local]:
  LAST [] = FAIL LAST ^(mk_var("empty list",bool))  []
Proof
 REWRITE_TAC [combinTheory.FAIL_THM]
QED

Theorem FRONT_NIL[local]:
  FRONT [] = FAIL FRONT ^(mk_var("empty list",bool))  []
Proof
 REWRITE_TAC [combinTheory.FAIL_THM]
QED

Theorem GENLIST_compute[local]:
   !n l.
     GENLIST f n = if n = 0 then [] else SNOC (f (PRE n)) (GENLIST f (PRE n))
Proof
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC arithmeticTheory.num_CASES
    THEN REWRITE_TAC [numTheory.NOT_SUC, prim_recTheory.PRE, GENLIST]
QED

val defs =
  map DEFN [NULL_DEF, CONJ HD_NIL HD, CONJ TL_NIL TL, APPEND, FLAT, MAP,
            FILTER, FOLDR, FOLDL, SNOC, GENLIST_compute, EVERY_DEF,
            EXISTS_DEF, MAP2_THM, ZIP_THM, UNZIP_THM, REVERSE_DEF,
            CONJ LAST_NIL LAST_CONS, CONJ FRONT_NIL FRONT_CONS,
            EL_compute, LENGTH_THM, LEN_DEF, REV_DEF, SUM,
            list_size_def, PAD_LEFT, PAD_RIGHT] @
  [DEFN_NOSIG MEM, DEFN ALL_DISTINCT]

val _ = eSML "list"
  (MLSIG "type num = numML.num" ::
   MLSIG "val MEM : ''a -> ''a list -> bool" ::
   OPEN ["num"] ::
   defs)

val _ = eCAML "list"
  (MLSIG "type num = NumML.num" ::
   MLSIG "val _MEM : 'a -> 'a list -> bool" ::
   MLSTRUCT "type num = NumML.num" ::
   OPEN ["Num"] ::
   defs)

val _ = ConstMapML.insert(Term.prim_mk_const{Name="CONS",Thy="list"});
val _ = ConstMapML.insert(Term.prim_mk_const{Name="NIL",Thy="list"});

(* == Rich list =========================================================== *)

val num_CASES = arithmeticTheory.num_CASES;

val NOT_SUC = numTheory.NOT_SUC;
val PRE = prim_recTheory.PRE;

Theorem BUTFIRSTN_compute[local]:
   !n l. BUTFIRSTN n l =
           if n = 0 then l else
           if l = [] then
             FAIL BUTFIRSTN ^(mk_var("List too short",bool)) n []
           else
             BUTFIRSTN (PRE n) (TL l)
Proof
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES
    THEN1 REWRITE_TAC [BUTFIRSTN]
    THEN STRIP_TAC THEN Q.SPEC_THEN `l` STRUCT_CASES_TAC list_CASES
    THEN REWRITE_TAC [NOT_CONS_NIL, TL, NOT_SUC, PRE, BUTFIRSTN,
                      combinTheory.FAIL_THM]
QED

Theorem ELL_compute[local]:
   !n l. ELL n l = if n = 0 then LAST l else ELL (PRE n) (FRONT l)
Proof
   STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES
     THEN REWRITE_TAC [NOT_SUC, PRE, ELL]
QED

Theorem FIRSTN_compute[local]:
   !n l. FIRSTN n l =
           if n = 0 then [] else
           if l = [] then
             FAIL FIRSTN ^(mk_var("List too short",bool)) n []
           else
             (HD l)::FIRSTN (PRE n) (TL l)
Proof
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES
    THEN1 REWRITE_TAC [FIRSTN]
    THEN STRIP_TAC THEN Q.SPEC_THEN `l` STRUCT_CASES_TAC list_CASES
    THEN REWRITE_TAC [NOT_CONS_NIL, HD, TL, NOT_SUC, PRE, FIRSTN,
                      combinTheory.FAIL_THM]
QED

Theorem REPLICATE_compute[local]:
   !n l. REPLICATE n l = if n = 0 then [] else l::(REPLICATE (PRE n) l)
Proof
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES
    THEN REWRITE_TAC [NOT_SUC, PRE, REPLICATE]
QED

Theorem SEG_compute[local]:
   !m k l. SEG m k l =
             if m = 0 then [] else
             if l = [] then
               FAIL SEG ^(mk_var("List too short",bool)) m k []
             else
               if k = 0 then
                 (HD l)::SEG (PRE m) 0 (TL l)
               else
                 SEG m (PRE k) (TL l)
Proof
  STRIP_TAC THEN Q.SPEC_THEN `m` STRUCT_CASES_TAC num_CASES
    THEN1 REWRITE_TAC [SEG]
    THEN STRIP_TAC THEN Q.SPEC_THEN `k` STRUCT_CASES_TAC num_CASES
    THEN STRIP_TAC THEN Q.SPEC_THEN `l` STRUCT_CASES_TAC list_CASES
    THEN REWRITE_TAC [NOT_CONS_NIL, HD, TL, NOT_SUC, PRE, SEG,
                      combinTheory.FAIL_THM]
QED

Theorem LUPDATE_compute[local]:
 (!e n. LUPDATE e n [] = []) /\
 (!e n x l. LUPDATE e n (x::l) =
  if n = 0 then e::l else x::LUPDATE e (PRE n) l)
Proof
SRW_TAC[][LUPDATE_def] THEN
Cases_on `n` THEN
FULL_SIMP_TAC (srw_ss()) [LUPDATE_def]
QED

val defs =
  map DEFN [AND_EL_DEF,BUTFIRSTN_compute,ELL_compute,FIRSTN_compute,
            BUTLASTN_compute,LASTN_compute,
            IS_PREFIX,IS_SUBLIST,OR_EL_DEF,SPLITP_AUX_def,
            LUPDATE_compute, REWRITE_RULE [FUN_EQ_THM] SPLITP_compute,
            PREFIX_DEF,REPLICATE_compute,
            SCANL,SCANR,SEG_compute,SUFFIX_DEF,UNZIP_FST_DEF,UNZIP_SND_DEF];

val _ = eSML "rich_list"
  (MLSIG "type num = numML.num"
   :: OPEN ["pair","num","list"]
   :: defs)

val _ = eCAML "rich_list"
  (MLSIG "type num = NumML.num"
   :: MLSTRUCT "type num = NumML.num"
   :: OPEN ["pair","num","list"]
   :: defs)

(* == String ============================================================== *)

val _ = app ConstMapML.insert [``$EXPLODE``, ``$IMPLODE``, ``$ORD``, ``$CHR``]

val _ = ConstMapML.insert(prim_mk_const{Name="DEST_STRING",Thy="string"});
val _ = ConstMapML.insert(prim_mk_const{Name="string_lt",Thy="string"});

fun cpi (t,nm) = ConstMapML.prim_insert(t,(false,"",nm,type_of t))

val _ = cpi (``STRCAT``, "STRCAT")
val _ = cpi (``STRLEN``, "STRLEN")
val _ = cpi (``STRING``, "STRING")

Theorem PAD_LEFT[local]:
   PAD_LEFT c n s =
     STRCAT (IMPLODE (GENLIST (K c) (n - STRLEN s))) s
Proof
  REWRITE_TAC [listTheory.PAD_LEFT, IMPLODE_EXPLODE_I]
QED

Theorem PAD_RIGHT[local]:
   PAD_RIGHT c n s =
     STRCAT s (IMPLODE (GENLIST (K c) (n - STRLEN s)))
Proof
  REWRITE_TAC [listTheory.PAD_RIGHT, IMPLODE_EXPLODE_I]
QED

val defs =
  map DEFN [char_size_def, STRCAT_EXPLODE,
            isPREFIX_DEF, isLower_def, isUpper_def, isDigit_def, isAlpha_def,
            isHexDigit_def, isAlphaNum_def, isPrint_def, isSpace_def,
            isGraph_def, isPunct_def, isAscii_def, isCntrl_def,
            toLower_def, toUpper_def, PAD_LEFT, PAD_RIGHT,
            char_lt_def, char_le_def, char_gt_def, char_ge_def,
            string_le_def, string_gt_def, string_ge_def]

val _ = eSML "string"
  (OPEN ["num", "list", "option"]
   :: MLSIG "type num = numML.num"
   :: MLSIG "type char = Char.char"
   :: MLSIG "type string = String.string"
   :: MLSIG "val DEST_STRING : string -> (char * string) option"
   :: MLSIG "val CHR : num -> char"
   :: MLSIG "val ORD : char -> num"
   :: MLSIG "val string_lt : string -> string -> bool"
   :: MLSIG "val IMPLODE : char list -> string"
   :: MLSIG "val EXPLODE : string -> char list"
   :: MLSIG "val STRLEN : string -> num"
   :: MLSTRUCT "type char = Char.char;"
   :: MLSTRUCT "type string = String.string;"
   :: MLSTRUCT "fun CHR n =\
       \ Char.chr(valOf(Int.fromString(numML.toDecString n)));"
   :: MLSTRUCT "fun ORD c = numML.fromDecString(Int.toString(Char.ord c));"
   :: MLSTRUCT "fun STRING c s = String.^(String.str c,s);"
   :: MLSTRUCT "fun DEST_STRING s = if s = \"\" then NONE \n\
       \          else SOME(String.sub(s,0),String.extract(s,1,NONE));"
   :: MLSTRUCT "fun string_lt a b = String.compare(a,b) = LESS"
   :: MLSTRUCT "val IMPLODE = String.implode"
   :: MLSTRUCT "val EXPLODE = String.explode"
   :: MLSTRUCT "fun STRLEN s = LENGTH (EXPLODE s)"
   :: defs)

val _ = eCAML "string"
  (MLSIGSTRUCT ["type num = NumML.num"]
   @ OPEN ["list", "option"]
   :: MLSIG "val _DEST_STRING : string -> (char * string) option"
   :: MLSIG "val _CHR : num -> char"
   :: MLSIG "val _ORD : char -> num"
   :: MLSIG "val string_lt : string -> string -> bool"
   :: MLSIG "val _IMPLODE : char list -> string"
   :: MLSIG "val _EXPLODE : string -> char list"
   :: MLSTRUCT "let _CHR n = Char.chr(NumML.int_of_holnum n)"
   :: MLSTRUCT "let _ORD c = NumML.holnum_of_int(Char.code c)"
   :: MLSTRUCT "let _STRING c s = String.concat \"\" [Char.escaped c; s]"
   :: MLSTRUCT "let _DEST_STRING s = if s = \"\" then None\n\
    \          else Some(String.get s 0,String.sub s 1 (String.length s - 1))"
   :: MLSTRUCT "let string_lt a b = String.compare a b < 0"
   :: MLSTRUCT "let _IMPLODE l =\n\
    \     let s = String.create (List.length l) in\n\
    \     let _ = List.fold_left\n\
    \               (function n -> function c ->\
    \ (String.set s n c; n + 1)) 0 l in s"
   :: MLSTRUCT "let _EXPLODE s =\n\
    \     Rich_listML._GENLIST\n\
    \        (function n -> String.get s (NumML.int_of_holnum n))\n\
    \        (NumML.holnum_of_int (String.length s))"
   :: map DEFN [char_size_def, isLower_def, isUpper_def, isDigit_def,
        isAlpha_def, isHexDigit_def, isAlphaNum_def, isPrint_def, isSpace_def,
        isGraph_def, isPunct_def, isAscii_def, isCntrl_def,
        toLower_def, toUpper_def,
        char_lt_def, char_le_def, char_gt_def, char_ge_def,
        string_le_def, string_gt_def, string_ge_def])

val _ = app (fn n => ConstMapML.insert
                               (prim_mk_const{Name=n,Thy="string"}))
            ["CHR","ORD","DEST_STRING","string_lt","IMPLODE","EXPLODE"];

(* == Finite map ========================================================== *)

Theorem FAPPLY_FEMPTY[local]:
  FAPPLY (FEMPTY:('a,'b)fmap) x :'b =
  FAIL FAPPLY ^(mk_var("empty map",bool)) FEMPTY x
Proof
 REWRITE_TAC [combinTheory.FAIL_THM]
QED

val DRESTRICT_PRED_THM =
  SIMP_RULE std_ss [boolTheory.IN_DEF]
   (CONJ DRESTRICT_FEMPTY DRESTRICT_FUPDATE);

val DRESTRICT_PRED_THM =
  SIMP_RULE std_ss [boolTheory.IN_DEF]
   (CONJ DRESTRICT_FEMPTY DRESTRICT_FUPDATE);

val th = GEN_ALL
             (CONV_RULE (DEPTH_CONV ETA_CONV)
               (ABS (Term `a:'a`)
                 (SIMP_RULE std_ss [IN_SING,IN_DEF]
                   (Q.SPEC `{x}` (Q.SPEC `a` IN_COMPL)))));

Theorem RRESTRICT_PRED_THM[local]:
  (!P. RRESTRICT (FEMPTY:'a|->'b) P = (FEMPTY:'a|->'b)) /\
  (!(f:'a|->'b) P x y.
       RRESTRICT (f |+ (x,y)) P =
        if P y then RRESTRICT f P |+ (x,y)
          else RRESTRICT (DRESTRICT f (\a. ~(a = x))) P)
Proof
 REWRITE_TAC [RRESTRICT_FEMPTY]
  THEN METIS_TAC [REWRITE_RULE [th] RRESTRICT_FUPDATE, IN_DEF]
QED

Theorem FRANGE_EQNS[local]:
  (FRANGE (FEMPTY:'a|->'b) = ({}:'b -> bool)) /\
  (!(f:'a |-> 'b) (x:'a) (y:'b).
         FRANGE (f |+ (x,y)) = y INSERT FRANGE (DRESTRICT f (\a. ~(a = x))))
Proof
 METIS_TAC [REWRITE_RULE [th] FRANGE_FUPDATE, FRANGE_FEMPTY]
QED

Theorem o_f_EQNS[local]:
  (f          o_f (FEMPTY:'a|->'b) = (FEMPTY:'a|->'c)) /\
  ((f:'b->'c) o_f ((fm:'a|->'b) |+ (k,v)) = (f o_f fm) |+ (k,f v))
Proof
 METIS_TAC [o_f_FEMPTY, o_f_FUPDATE]
QED

val T_INTRO = PURE_ONCE_REWRITE_RULE [PROVE[] (Term `x = (x = T)`)]

val defs =
  DEFN_NOSIG (CONJ FDOM_FEMPTY FDOM_FUPDATE)
  :: map DEFN [CONJ FAPPLY_FEMPTY FAPPLY_FUPDATE_THM,
       FCARD_DEF, FLOOKUP_DEF, REWRITE_RULE [FUN_EQ_THM] FUPDATE_LIST,
       CONJ FUNION_FEMPTY_1 (CONJ FUNION_FEMPTY_2 FUNION_FUPDATE_1),
       CONJ DOMSUB_FEMPTY DOMSUB_FUPDATE_THM,
       CONJ (T_INTRO (SPEC_ALL SUBMAP_FEMPTY)) SUBMAP_FUPDATE,
       DRESTRICT_PRED_THM, RRESTRICT_PRED_THM]
   @ DEFN_NOSIG FRANGE_EQNS
  :: map DEFN [o_f_EQNS, CONJ (T_INTRO (SPEC_ALL FEVERY_FEMPTY))
       (REWRITE_RULE [th] FEVERY_FUPDATE)]

val _ = eSML "fmap"
  (ABSDATATYPE (["'a","'b"], `fmap = FEMPTY | FUPDATE fmap ('a#'b)`)
   :: OPEN ["num", "list", "set", "option"]
   :: MLSIG "type num = numML.num"
   :: MLSIG "type 'a set = 'a setML.set"
   :: MLSIG "val FEMPTY   : ('a,'b) fmap"
   :: MLSIG "val FUPDATE  : ('a,'b) fmap * ('a * 'b) -> ('a,'b)fmap"
   :: MLSIG "val FDOM     : ('a,'b) fmap -> 'a set"
   :: defs)

val _ = eCAML "fmap"
  (MLSIGSTRUCT ["type num = NumML.num", "type 'a set = 'a SetML.set"]
   @ ABSDATATYPE (["'a","'b"], `fmap = FEMPTY | FUPDATE fmap ('a # 'b)`)
   :: OPEN ["num", "list", "set", "option"]
   :: MLSIG "val _FDOM     : ('a,'b) fmap -> 'a set"
   :: MLSIG "val _FRANGE   : ('a,'b) fmap -> 'b set"
   :: defs)

(* == Sum ================================================================= *)

Theorem OUTL_INR[local]:
  !y. OUTL(INR y:'a+'b) =
      FAIL OUTL ^(mk_var("applied to INR",bool)) (INR y:'a+'b)
Proof
 REWRITE_TAC [combinTheory.FAIL_THM]
QED

Theorem OUTR[local]:
  (!x. OUTR(INL x:'a+'b) =
      FAIL OUTR ^(mk_var("applied to INL",bool)) (INL x:'a+'b)) /\
  (!y. OUTR(INR y:'a+'b) = y)
Proof
 REWRITE_TAC [combinTheory.FAIL_THM,OUTR]
QED

Theorem ISL_THM[local]:
  (!x. ISL (INL x:'a+'b) = T) /\ !y. ISL (INR y:'a+'b) = F
Proof
 REWRITE_TAC[ISL]
QED

Theorem ISR_THM[local]:
  (!x. ISR (INL x:'a+'b) = F) /\ !y. ISR (INR y:'a+'b) = T
Proof
 REWRITE_TAC[ISR]
QED

val defs =
  DATATYPE `sum = INL 'a | INR 'b`
  :: map DEFN [CONJ OUTL OUTL_INR, OUTR, ISL_THM, ISR_THM]

val _ = eSML "sum" defs
val _ = eCAML "sum" defs;

(* == Bit ================================================================= *)

val PRE = prim_recTheory.PRE;
val NOT_SUC = numTheory.NOT_SUC;

Theorem NUMERAL_1[local]:
   !n. (NUMERAL (BIT1 n) = 1) = (n = 0)
Proof
  REWRITE_TAC [GSYM (REWRITE_CONV [GSYM ALT_ZERO] ``NUMERAL (BIT1 0)``)]
    THEN SIMP_TAC bool_ss [BIT1, NUMERAL_DEF]
    THEN DECIDE_TAC
QED

Theorem NUMERAL_1b[local]:
   !n. ~(NUMERAL (BIT2 n) = 1)
Proof
  REWRITE_TAC [GSYM (REWRITE_CONV [GSYM ALT_ZERO] ``NUMERAL (BIT1 0)``)]
    THEN SIMP_TAC bool_ss [BIT1, BIT2, NUMERAL_DEF]
    THEN DECIDE_TAC
QED

Theorem iDUB_SUC[local]:
  !n. numeral$iDUB (SUC n) = BIT2 n
Proof
  SIMP_TAC bool_ss [iDUB, BIT2, ADD1] THEN DECIDE_TAC
QED

Theorem DIV2_BIT1_SUC[local]:
   !n. DIV2 (NUMERAL (BIT1 (SUC n))) = n + 1
Proof
  REWRITE_TAC [DIV2_def]
    THEN GEN_REWRITE_TAC (DEPTH_CONV o RATOR_CONV o RAND_CONV) empty_rewrites
         [BIT1, Q.SPEC `BIT1 (SUC n)` NUMERAL_DEF]
    THEN SIMP_TAC arith_ss [ADD1, ONCE_REWRITE_RULE [MULT_COMM] ADD_DIV_ADD_DIV]
QED

Theorem LOG2_compute[local]:
   !n. LOG2 n =
         if n = 0 then
           FAIL LOG2 ^(mk_var("undefined",bool)) n
         else
           if n = 1 then
             0
           else
             1 + LOG2 (DIV2 n)
Proof
  Cases THEN REWRITE_TAC [NOT_SUC, combinTheory.FAIL_THM]
    THEN Q.SPEC_TAC (`n'`,`n`) THEN CONV_TAC numLib.SUC_TO_NUMERAL_DEFN_CONV
    THEN STRIP_TAC
    THENL [
       REWRITE_TAC [NUMERAL_1] THEN Cases THEN RW_TAC arith_ss [numeral_log2]
         THENL [PROVE_TAC [iDUB_removal, numeral_ilog2, ALT_ZERO],
                REWRITE_TAC [iDUB_SUC, DIV2_BIT1_SUC, numeral_ilog2]
                  THEN SIMP_TAC arith_ss [iLOG2_def]],
       REWRITE_TAC [NUMERAL_1b, numeral_div2, numeral_ilog2, numeral_log2,
                    NUMERAL_DEF, iLOG2_def, ADD1]]
QED

Theorem BITWISE_compute[local]:
   !n opr a b.
      BITWISE n opr a b =
        if n = 0 then 0 else
          2 * BITWISE (PRE n) opr (DIV2 a) (DIV2 b) +
          (if opr (ODD a) (ODD b) then 1 else 0)
Proof
  Cases THEN1 REWRITE_TAC [CONJUNCT1 BITWISE_def]
    THEN REWRITE_TAC
         [DIV2_def, NOT_SUC, PRE, EXP, BITWISE_EVAL, BIT0_ODD, SBIT_def]
QED

Theorem BIT_MODF_compute[local]:
   !n f x b e y.
      BIT_MODF n f x b e y =
        if n = 0 then y else
          BIT_MODF (PRE n) f (DIV2 x) (b + 1) (2 * e)
           (if f b (ODD x) then e + y else y)
Proof
  Cases THEN REWRITE_TAC [DIV2_def, NOT_SUC, PRE, BIT_MODF_def]
QED

Theorem BIT_REV_compute[local]:
   !n x y.
      BIT_REV n x y =
        if n = 0 then y else
          BIT_REV (PRE n) (DIV2 x) (2 * y + (if ODD x then 1 else 0))
Proof
  Cases THEN REWRITE_TAC [DIV2_def, NOT_SUC, PRE, BIT_REV_def, EXP, SBIT_def]
QED

Theorem TIMES_2EXP_lem[local]:
   !n. FUNPOW numeral$iDUB n 1 = 2 ** n
Proof
  Induct THEN ASM_SIMP_TAC arith_ss
    [EXP,CONJUNCT1 FUNPOW,FUNPOW_SUC,iDUB,GSYM TIMES2]
QED

Theorem TIMES_2EXP_compute[local]:
   !n x. TIMES_2EXP n x = if x = 0 then 0 else x * FUNPOW numeral$iDUB n 1
Proof
  RW_TAC bool_ss [MULT, TIMES_2EXP_lem, CONJUNCT1 FUNPOW, TIMES_2EXP_def]
QED

val TIMES_2EXP1 =
  (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
   Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def;

Theorem MOD_2EXP_EQ_compute[local]:
   !n a b. MOD_2EXP_EQ n a b =
             if n = 0 then T else
               (ODD a = ODD b) /\ MOD_2EXP_EQ (n - 1) (DIV2 a) (DIV2 b)
Proof
  Cases THEN SRW_TAC [] [MOD_2EXP_EQ]
QED

Theorem BOOLIFY_compute[local]:
   !n. BOOLIFY n m a =
         if n = 0 then
           a
         else
           BOOLIFY (PRE n) (DIV2 m) (ODD m::a)
Proof
  Cases THEN SRW_TAC [] [BOOLIFY_def]
QED

Theorem HEX_compute[local]:
   !n. HEX n =
          if n = 0 then #"0"
     else if n = 1 then #"1"
     else if n = 2 then #"2"
     else if n = 3 then #"3"
     else if n = 4 then #"4"
     else if n = 5 then #"5"
     else if n = 6 then #"6"
     else if n = 7 then #"7"
     else if n = 8 then #"8"
     else if n = 9 then #"9"
     else if n = 10 then #"A"
     else if n = 11 then #"B"
     else if n = 12 then #"C"
     else if n = 13 then #"D"
     else if n = 14 then #"E"
     else if n = 15 then #"F"
     else FAIL HEX ^(mk_var("not a hex digit",bool)) n
Proof
  SRW_TAC [] [HEX_def,combinTheory.FAIL_THM]
QED

Theorem UNHEX_compute[local]:
   !n. UNHEX c =
          if c = #"0" then 0
     else if c = #"1" then 1
     else if c = #"2" then 2
     else if c = #"3" then 3
     else if c = #"4" then 4
     else if c = #"5" then 5
     else if c = #"6" then 6
     else if c = #"7" then 7
     else if c = #"8" then 8
     else if c = #"9" then 9
     else if c = #"A" then 10
     else if c = #"B" then 11
     else if c = #"C" then 12
     else if c = #"D" then 13
     else if c = #"E" then 14
     else if c = #"F" then 15
     else FAIL UNHEX ^(mk_var("not a hex digit",bool)) c
Proof
  SRW_TAC [] [UNHEX_def,combinTheory.FAIL_THM]
QED

Theorem LOWEST_SET_BIT_emit[local]:
   !n. LOWEST_SET_BIT n =
         if n = 0 then
           FAIL LOWEST_SET_BIT ^(mk_var("zero value",bool)) n
         else if ODD n then
           0
         else
           1 + LOWEST_SET_BIT (DIV2 n)
Proof
  SRW_TAC [] [LOWEST_SET_BIT, combinTheory.FAIL_THM]
QED

val defs =
  map (DEFN o PURE_REWRITE_RULE [TIMES_2EXP1])
       [TIMES_2EXP_compute,BITWISE_compute,LOG_compute,LOWEST_SET_BIT_emit,
        l2n_def,n2l_def,s2n_compute,n2s_compute,HEX_compute,UNHEX_compute,
        num_from_bin_list_def,num_from_oct_list_def,num_from_dec_list_def,
        num_from_hex_list_def,num_to_bin_list_def,num_to_oct_list_def,
        num_to_dec_list_def,num_to_hex_list_def,num_from_bin_string_def,
        num_from_oct_string_def,num_from_dec_string_def,num_from_hex_string_def,
        num_to_bin_string_def,num_to_oct_string_def,num_to_dec_string_def,
        num_to_hex_string_def,
        BIT_MODF_compute, BIT_MODIFY_EVAL,
        BIT_REV_compute, BIT_REVERSE_EVAL,
        LOG2_compute, DIVMOD_2EXP, SBIT_def, BITS_def, MOD_2EXP_EQ_compute,
        BITV_def, BIT_def, SLICE_def, SIGN_EXTEND_def, BOOLIFY_compute]

val _ = eSML "bit"
  (MLSIG  "type num = numML.num" ::
   OPEN ["num"] ::
   defs)

val _ = eCAML "bit"
  (MLSIGSTRUCT ["type num = NumML.num"] @
   OPEN ["num"] ::
   defs)

(* == FCP ================================================================= *)

Definition FCPi_def:   FCPi (f, (:'b)) = ($FCP f):'a ** 'b
End

Definition mk_fcp_def:   mk_fcp = FCPi
End

val index_comp = REWRITE_RULE [GSYM FCPi_def] index_comp;
val fcp_subst_comp = REWRITE_RULE [GSYM FCPi_def] fcp_subst_comp;

val _ = new_constant("ITSELF", ``:num -> 'a itself``);

val _ = new_constant("SUMi", ``:'a itself # 'b itself -> 'c itself``);
val _ = new_constant("MULi", ``:'a itself # 'b itself -> 'c itself``);
val _ = new_constant("EXPi", ``:'a itself # 'b itself -> 'c itself``);

val SUMi  = new_axiom("SUMi", ``SUMi (ITSELF a, ITSELF b) = ITSELF (a + b)``);
val MULi  = new_axiom("MULi", ``MULi (ITSELF a, ITSELF b) = ITSELF (a * b)``);
val EXPi  = new_axiom("EXPi", ``EXPi (ITSELF a, ITSELF b) = ITSELF (a ** b)``);

val dimindexi = new_axiom("dimindexi", ``dimindex (ITSELF a) = a``);

val _ = type_pp.pp_array_types := false

val defs = [SUMi, MULi, EXPi, dimindexi, mk_fcp_def, index_comp, fcp_subst_comp]

val _ = eSML "fcp"
  ([OPEN ["num"],
    MLSIG "type num = numML.num",
    DATATYPE(`itself = ITSELF num`),
    ABSDATATYPE (["'a","'b"], `cart = FCPi ((num -> 'a) # 'b itself)`),
    EQDATATYPE (["'a"],`bit0 = BIT0A 'a | BIT0B 'a`),
    EQDATATYPE (["'a"],`bit1 = BIT1A 'a | BIT1B 'a | BIT1C`)] @
   map DEFN defs)

val _ = eCAML "fcp"
 (MLSIGSTRUCT ["type num = NumML.num"]
   @ OPEN ["num"]
  :: DATATYPE(`itself = ITSELF num`)
  :: ABSDATATYPE (["'a","'b"], `cart = FCPi ((num -> 'a) # 'b itself)`)
  :: EQDATATYPE (["'a"],`bit0 = BIT0A 'a | BIT0B 'a`)
  :: EQDATATYPE (["'a"],`bit1 = BIT1A 'a | BIT1B 'a | BIT1C`)
  :: map (DEFN o REWRITE_RULE [GSYM FCPi_def, FUN_EQ_THM]) defs)

(* == Words =============================================================== *)

val _ = ConstMapML.insert_cons ``n2w_itself``;

val sizes = [1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 28, 30, 32, 64, 128, 256]

val ALPHA_BETA_RULE = GEN_ALL o Q.INST [`a` |-> `m`, `b` |-> `n`] o SPEC_ALL

val MOD_WL =
    (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV (ONCE_REWRITE_CONV [GSYM n2w_mod]))))

val TIMES_2EXP1 =
    (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
     Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def

Theorem word_reduce[local]:
   !b. $FCP (K b) = n2w (if b then 1 else 0) : 1 word
Proof
  SRW_TAC [fcpLib.FCP_ss]
     [word_index, DECIDE ``x < 1 <=> (x = 0n)``, fcpTheory.index_one,
      bitTheory.BITS_THM, bitTheory.BIT_def]
QED

Theorem bit_field_insert[local]:
   !h l a.
     bit_field_insert h l a w =
       word_modify
         (\i b. if l <= i /\ i <= h then word_index a (i - l) else b) w
Proof
  SRW_TAC [fcpLib.FCP_ss]
    [word_index_def, bit_field_insert_def, word_modify_def]
QED

val n2w_w2n_RULE = REWRITE_RULE [n2w_w2n] o Q.SPEC `w2n w`
val word_eq_n2w = REWRITE_RULE [n2w_11] (Q.SPECL [`n2w m`,`n2w n`] word_eq_def)
val word_reduce_n2w = REWRITE_RULE [word_reduce] word_reduce_n2w
val word_eq_n2w = n2w_w2n_RULE (GEN_ALL word_eq_n2w)
val word_or_n2w = n2w_w2n_RULE word_or_n2w
val word_and_n2w = n2w_w2n_RULE word_and_n2w
val word_xor_n2w = n2w_w2n_RULE word_xor_n2w
val word_nor_n2w = n2w_w2n_RULE word_nor_n2w
val word_nand_n2w = n2w_w2n_RULE word_nand_n2w
val word_xnor_n2w = n2w_w2n_RULE word_xnor_n2w
val word_add_n2w = n2w_w2n_RULE word_add_n2w
val word_mul_n2w = n2w_w2n_RULE word_mul_n2w
val word_ge_n2w = n2w_w2n_RULE word_ge_n2w
val word_gt_n2w = n2w_w2n_RULE word_gt_n2w
val word_hi_n2w = n2w_w2n_RULE word_hi_n2w
val word_hs_n2w = n2w_w2n_RULE word_hs_n2w
val word_le_n2w = n2w_w2n_RULE word_le_n2w
val word_lo_n2w = n2w_w2n_RULE word_lo_n2w
val word_ls_n2w = n2w_w2n_RULE word_ls_n2w
val word_lt_n2w = n2w_w2n_RULE word_lt_n2w
val word_join_n2w = Q.SPECL [`n2w m`,`n2w n`] word_join_def
val word_div_n2w = Q.SPEC `n2w m` word_div_def
val word_asr_n2w = Q.SPECL [`n`,`n2w m`] word_asr_n2w
val word_lsr_n2w = Q.SPEC `n2w m` word_lsr_n2w
val word_rol_n2w = Q.SPEC `n2w m` word_rol_def
val reduce_and_n2w = Q.SPEC `n2w m` reduce_and
val reduce_or_n2w = Q.SPEC `n2w m` reduce_or
val sw2sw_n2w = Q.SPEC `n2w n` sw2sw_def
val add_with_carry_n2w = Q.SPEC `n2w n` add_with_carry_def
val word_sign_extend_n2w =
  REWRITE_RULE [w2n_n2w] (Q.SPECL [`n`,`n2w w`] word_sign_extend_def)
val reduce_xnor =
  ONCE_REWRITE_RULE [METIS_PROVE [] ``(<=>) = (\x y. x = y)``] reduce_xnor_def

val f =
  map (DEFN o REWRITE_RULE
         [GSYM n2w_itself_def, GSYM w2w_itself_def,
          GSYM sw2sw_itself_def, GSYM word_concat_itself_def,
          GSYM word_extract_itself_def, word_T_def, word_L_def, word_H_def,
          TIMES_2EXP1, FUN_EQ_THM] o ALPHA_BETA_RULE)

fun mk_index ocaml i =
  let val n = Arbnum.fromInt i
      val x = Int.toString i
      val typ = fcpLib.index_type n
      val s = String.extract(with_flag (type_pp.pp_num_types, false)
                 type_to_string typ, 1, NONE)
      val w = "type word" ^ x ^ " = " ^ s ^ " word"
      val numML = if ocaml then "numML." else "NumML."
      val (a,b,c) =
              if ocaml then
                ("let toWord" ^ x ^
                 " n = fromNum (n,ITSELF(NumML.holnum_of_int " ^ x ^ "))",
                 "val toWord" ^ x ^ " : NumML.num -> word" ^ x,
                 "let fromString" ^ x ^
                 " = CombinML.o toWord" ^ x ^ " NumML.fromString")
              else
                ("fun toWord" ^ x ^
                 " n = fromNum (n,ITSELF(numML.fromInt " ^ x ^ "))",
                 "val toWord" ^ x ^ " : numML.num -> word" ^ x,
                 "val fromString" ^ x ^
                 " = o(toWord" ^ x ^ ", numML.fromString) : string -> word" ^ x)
      val d = "val fromString" ^ x ^ " : string -> word" ^ x
  in
    [EmitML.MLSTRUCT w, EmitML.MLSIG w,
     EmitML.MLSTRUCT a, EmitML.MLSIG b,
     EmitML.MLSTRUCT c, EmitML.MLSIG d]
  end;

fun defs ocaml =
    f [dimword_def, fromNum_def] @ List.concat (map (mk_index ocaml) sizes) @
    f [wordsTheory.INT_MIN_def, wordsTheory.UINT_MAX_def,
       wordsTheory.INT_MAX_def,
       w2n_n2w, word_eq_n2w, w2w_n2w, word_or_n2w, word_lsl_n2w,
       word_bits_n2w, word_signed_bits_n2w, Q.SPEC `c` word_bit_n2w,
       word_join_n2w, sw2sw_n2w, word_extract_n2w, word_slice_n2w,
       word_concat_def, word_log2_n2w, word_reverse_n2w, word_modify_n2w,
       word_lsb_n2w, word_msb_n2w, add_with_carry_n2w,
       word_1comp_n2w, word_and_n2w, word_xor_n2w,
       word_2comp_n2w, word_div_n2w, word_quot_def,
       MOD_WL word_add_n2w, word_sub_def, MOD_WL word_mul_n2w,
       word_lsr_n2w, word_asr_n2w, word_ror_n2w, word_rol_n2w,
       word_rrx_n2w, REWRITE_RULE [GSYM word_index_def] word_index_n2w,
       word_ge_n2w, word_gt_n2w, word_hi_n2w, word_hs_n2w,
       word_le_n2w, word_lo_n2w, word_ls_n2w, word_lt_n2w,
       word_reduce_n2w, reduce_and_n2w, reduce_or_n2w, reduce_xor_def,
       reduce_xnor, reduce_nand_def, reduce_nor_def, bit_field_insert,
       w2l_def,w2s_def,
       word_sign_extend_n2w,
       word_to_bin_list_def,word_to_oct_list_def,
       word_to_dec_list_def,word_to_hex_list_def,
       word_to_bin_string_def,word_to_oct_string_def,
       word_to_dec_string_def,word_to_hex_string_def]

val _ = eSML "words"
  (OPEN ["sum", "num", "fcp", "bit"]
   :: MLSIG "type ('a, 'b) sum = ('a, 'b) sumML.sum"
   :: MLSIG "type 'a itself = 'a fcpML.itself"
   :: MLSIG "type 'a bit0 = 'a fcpML.bit0"
   :: MLSIG "type 'a bit1 = 'a fcpML.bit1"
   :: MLSIG "type num = numML.num"
   :: MLSIG "datatype 'a word = n2w_itself of num * 'a itself"
   :: MLSTRUCT "datatype 'a word = n2w_itself of num * 'a itself"
   :: defs false)

val _ = eCAML "words"
  (MLSIGSTRUCT
     ["type num = NumML.num",
      "type ('a, 'b) sum = ('a, 'b) SumML.sum",
      "type 'a itself = 'a FcpML.itself",
      "type 'a bit0 = 'a FcpML.bit0",
      "type 'a bit1 = 'a FcpML.bit1", "",
      "type 'a word = N2w_itself of num * 'a itself"] @
   OPEN ["sum", "num", "fcp", "bit"] ::
   defs true)

(* == Integer ============================================================= *)

Definition neg_int_of_num_def:   neg_int_of_num n = ~ int_of_num (n + 1)
End
Definition i2w_itself_def:   i2w_itself(i,(:'a)) = i2w i : 'a word
End

val i2w_itself = REWRITE_RULE [i2w_def] i2w_itself_def;

val emit_rule = SIMP_RULE std_ss [numeralTheory.iZ, NUMERAL_DEF];

fun emit_conv l1 l2 = LIST_CONJ
 (map (GEN_ALL o (SIMP_CONV (srw_ss()) (neg_int_of_num_def::l1)
    THENC REWRITE_CONV [GSYM neg_int_of_num_def])) l2);

val lem1 = DECIDE ``~(n + 1n <= m) ==> (n + 1 - m = (n - m) + 1)``;
val lem2 = DECIDE ``m + 1n + (n + 1) = m + n + 1 + 1``;

Theorem INT_NEG_EMIT[local]:
   (!n. ~ (int_of_num n) =
         if n = 0 then int_of_num 0 else neg_int_of_num (n - 1)) /\
   (!n. ~ (neg_int_of_num n) = int_of_num (n + 1))
Proof
  SRW_TAC [ARITH_ss] [neg_int_of_num_def]
QED

val INT_ADD_EMIT = emit_conv [emit_rule INT_ADD_REDUCE, lem1, lem2]
   [``int_of_num m + int_of_num n``,
    ``neg_int_of_num m + int_of_num n``,
    ``int_of_num m + neg_int_of_num n``,
    ``neg_int_of_num m + neg_int_of_num n``];

val INT_SUB_EMIT = emit_conv [emit_rule INT_SUB_REDUCE]
   [``int_of_num m - int_of_num n``,
    ``neg_int_of_num m - int_of_num n``,
    ``int_of_num m - neg_int_of_num n``,
    ``neg_int_of_num m - neg_int_of_num n``];

val INT_MUL_EMIT = emit_conv [emit_rule INT_MUL_REDUCE]
   [``int_of_num m * int_of_num n``,
    ``neg_int_of_num m * int_of_num n``,
    ``int_of_num m * neg_int_of_num n``,
    ``neg_int_of_num m * neg_int_of_num n``];

val INT_LT_EMIT = emit_conv [emit_rule INT_LT_CALCULATE]
   [``int_of_num m < int_of_num n``,
    ``neg_int_of_num m < int_of_num n``,
    ``int_of_num m < neg_int_of_num n``,
    ``neg_int_of_num m < neg_int_of_num n``];

Theorem INT_NEG_EXP[local]:
   !m n.
      neg_int_of_num m ** n =
        if EVEN n then
          int_of_num ((m + 1) ** n)
        else
          ~int_of_num ((m + 1) ** n)
Proof
  SRW_TAC [] [neg_int_of_num_def, INT_EXP_NEG]
    THEN FULL_SIMP_TAC std_ss [INT_EXP_NEG, GSYM ODD_EVEN]
QED

val INT_EXP_EMIT = CONJ INT_EXP INT_NEG_EXP;

Theorem INT_Num_EMIT[local]:
   (!n. Num (int_of_num n) = n) /\
   (!n. Num (neg_int_of_num n) =
     FAIL $Num ^(mk_var("negative",bool)) (neg_int_of_num n))
Proof
  SRW_TAC [] [combinTheory.FAIL_THM]
QED

Theorem INT_DIV_EMIT[local]:
   !i j. i / j =
      if j = 0 then FAIL $/ ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_div)
Proof
  SRW_TAC [] [combinTheory.FAIL_THM, int_div]
QED

Theorem INT_MOD_EMIT[local]:
   !i j. i % j =
      if j = 0 then FAIL $% ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_mod)
Proof
  SRW_TAC [] [combinTheory.FAIL_THM, int_mod]
QED

Theorem INT_QUOTE_EMIT[local]:
   !i j. i quot j =
      if j = 0 then FAIL $quot ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_quot)
Proof
  SRW_TAC [] [combinTheory.FAIL_THM, int_quot]
QED

Theorem INT_REM_EMIT[local]:
   !i j. i rem j =
      if j = 0 then FAIL $rem ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_rem)
Proof
  SRW_TAC [] [combinTheory.FAIL_THM, int_rem]
QED

val _ = temp_clear_overloads_on "&";
Overload int_of_num[local] = ``integer$int_of_num``

val _ = eSML "int"
 (OPEN ["num", "words"]
  :: EQDATATYPE ([], `int = int_of_num num | neg_int_of_num num`)
  :: MLSIG "type num = numML.num"
  :: MLSIG "type 'a itself = 'a fcpML.itself"
  :: MLSIG "type 'a word = 'a wordsML.word"
  :: MLSIG "val int_of_num : num -> int"
  :: MLSIG "val fromInt : Int.int -> int"
  :: MLSIG "val toInt : int -> Int.int option"
  :: MLSIG "val fromString : string -> int"
  :: MLSTRUCT
        "fun fromString s =\n\
      \    let val s = String.extract(s,0,SOME (Int.-(String.size s,1))) in\n\
      \      if String.sub(s,0) = #\"-\" then\n\
      \        let val s = String.extract(s,1,NONE) in\n\
      \          neg_int_of_num (numML.PRE (numML.fromString s))\n\
      \        end\n\
      \      else\n\
      \        int_of_num (numML.fromString s)\n\
      \    end\n"
  :: MLSTRUCT
        "fun fromInt i =\n\
      \    fromString (String.map (fn c => if c = #\"~\" then #\"-\" else c)\n\
      \      (String.^(Int.toString i,\"i\")))\n"
  :: MLSTRUCT
        "fun toInt (int_of_num n) = numML.toInt n\n\
      \    | toInt (neg_int_of_num n) =\n\
      \         case numML.toInt n of\n\
      \           SOME v => SOME (Int.-(Int.~ v,1))\n\
      \         | NONE => NONE\n"
  :: map DEFN
      [INT_NEG_EMIT, INT_Num_EMIT,
       INT_LT_EMIT, INT_LE_CALCULATE, INT_GT_CALCULATE, INT_GE_CALCULATE,
       INT_ABS, INT_ADD_EMIT, INT_SUB_EMIT, INT_MUL_EMIT, INT_EXP_EMIT,
       INT_DIV_EMIT, INT_MOD_EMIT, INT_QUOTE_EMIT, INT_REM_EMIT,
       INT_MAX_def, INT_MIN_def, UINT_MAX_def, i2w_itself, w2i_def])

val _ = eCAML "int"
 (MLSIGSTRUCT
    ["type num = NumML.num",
     "type 'a itself = 'a FcpML.itself",
     "type 'a word = 'a WordsML.word"]
   @ EQDATATYPE ([], `int = int_of_num num | neg_int_of_num num`)
  :: MLSIG "val fromString : string -> int"
  :: MLSTRUCT
       "let fromString s =\n\
       \    let s' = String.sub s 0 (String.length s - 1) in\n\
       \      if String.get s' 0 = '-' then\n\
       \        let s' = String.sub s' 1 (String.length s' - 1) in\n\
       \          Neg_int_of_num (NumML._PRE (NumML.fromString s'))\n\
       \      else\n\
       \        Int_of_num (NumML.fromString s')\n"
  :: map DEFN
      [INT_NEG_EMIT, INT_Num_EMIT,
       INT_LT_EMIT, INT_LE_CALCULATE, INT_GT_CALCULATE, INT_GE_CALCULATE,
       INT_ABS, INT_ADD_EMIT, INT_SUB_EMIT, INT_MUL_EMIT, INT_EXP_EMIT,
       INT_DIV_EMIT, INT_MOD_EMIT, INT_QUOTE_EMIT, INT_REM_EMIT,
       INT_MAX_def, INT_MIN_def, UINT_MAX_def, i2w_itself, w2i_def])

(* == Sorting ============================================================= *)

val defs =
  OPEN ["list"] :: map DEFN [PART_DEF, PARTITION_DEF, QSORT_DEF, SORTED_DEF];

val _ = eSML "sorting" defs;
val _ = eCAML "sorting" defs;

(* restore "standard" set type abbreviation to have pride of place *)
Type set = alpha --> bool
