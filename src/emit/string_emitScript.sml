open HolKernel boolLib bossLib Parse;
open EmitML stringTheory;
open option_emitTheory list_emitTheory rich_list_emitTheory;

val _ = new_theory "string_emit";

val _ = app ConstMapML.insert [``$EXPLODE``, ``$IMPLODE``, ``$ORD``, ``$CHR``]

val _ = ConstMapML.insert(prim_mk_const{Name="DEST_STRING",Thy="string"});
val _ = ConstMapML.insert(prim_mk_const{Name="string_lt",Thy="string"});

fun cpi (t,nm) = ConstMapML.prim_insert(t,(false,"",nm,type_of t))

val _ = cpi (``STRCAT``, "STRCAT")
val _ = cpi (``STRLEN``, "STRLEN")
val _ = cpi (``STRING``, "STRING")

val PAD_LEFT = Q.prove(
  `PAD_LEFT c n s =
     STRCAT (IMPLODE (GENLIST (K c) (n − STRLEN s))) s`,
  REWRITE_TAC [PAD_LEFT_def, IMPLODE_EXPLODE_I]);

val PAD_RIGHT = Q.prove(
  `PAD_RIGHT c n s =
     STRCAT s (IMPLODE (GENLIST (K c) (n − STRLEN s)))`,
  REWRITE_TAC [PAD_RIGHT_def, IMPLODE_EXPLODE_I]);

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
   :: MLSTRUCT "fun STRING c s = String.^(Char.toString c,s);"
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
   :: MLSIG "val _CHR : num -> char"
   :: MLSIG "val _ORD : char -> num"
   :: MLSTRUCT "let _CHR n = Char.chr(NumML.int_of_holnum n)"
   :: MLSTRUCT "let _ORD c = NumML.holnum_of_int(Char.code c)"
   :: MLSTRUCT "let _STRING c s = String.concat \"\" [Char.escaped c; s]"
   :: MLSTRUCT "let _DEST_STRING s = if s = \"\" then None \n\
    \          else Some(String.get s 0,String.sub s 1 (String.length s - 1))"
   :: map DEFN [char_size_def, isLower_def, isUpper_def, isDigit_def,
        isAlpha_def, isHexDigit_def, isAlphaNum_def, isPrint_def, isSpace_def,
        isGraph_def, isPunct_def, isAscii_def, isCntrl_def,
        toLower_def, toUpper_def,
        char_lt_def, char_le_def, char_gt_def, char_ge_def,
        string_le_def, string_gt_def, string_ge_def])

fun adjoin_to_theory_struct l = adjoin_to_theory {sig_ps = NONE,
  struct_ps = SOME (fn ppstrm =>
    app (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm)) l)};

val _ = adjoin_to_theory_struct [
  "val _ = app (fn n => ConstMapML.insert\
  \ (prim_mk_const{Name=n,Thy=\"string\"}))",
  "      [\"CHR\",\"ORD\",\"DEST_STRING\",\"string_lt\",\
  \       \"IMPLODE\",\"EXPLODE\"]"];

val _ = export_theory ();
