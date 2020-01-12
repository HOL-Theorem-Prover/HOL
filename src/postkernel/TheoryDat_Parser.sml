structure TheoryDat_Parser :> TheoryDat_Parser =
struct

open TheoryDat_Types TheoryDat_Reader

(* grammar :



NumList ::=  | <num> NumList
NumCommaList1 ::= <num> ("," <num>)*
BrStringList ::= '[' ']' | '[' <string> (',' <string>)* ']'

*)

fun require0 pfx0 tok buf =
    let
      val pfx = if pfx0 = "" then "E" else pfx0 ^ ": e"
    in
      if current buf = tok then advance buf
      else raise ParseError (pfx ^ "xpecting a " ^ toString tok ^ "; saw " ^
                             toString (current buf))
    end
val require = require0 ""

fun bracketed nm parser buf =
    let
      val _ = require0 nm LBr buf
      val v = parser buf handle ParseError s => raise ParseError (nm ^ ": " ^ s)
      val _ = require0 nm RBr buf
    in
      v
    end
fun tagged s parser buf = (require (ID s) buf; parser buf)

fun commafy1 parser buf =
    let
      val v = parser buf
      fun recurse A =
          case current buf of
              Comma => (advance buf; recurse (parser buf::A))
            | _ => List.rev A
    in
      recurse [v]
    end

fun commafy firstP parser buf =
    if firstP (current buf) then commafy1 parser buf
    else []

fun list1 firstP parser buf =
    let
      fun recurse A =
          if firstP (current buf) then recurse (parser buf :: A)
          else List.rev A
    in
      recurse [parser buf]
    end
fun list firstP parser buf =
    let
      fun recurse A =
          if firstP (current buf) then recurse (parser buf :: A)
          else List.rev A
    in
      recurse []
    end


fun parseNum buf =
    case current buf of
        Num n => (advance buf; n)
      | t => raise ParseError ("Expecting a number; saw " ^ toString t)

val parseInt = Arbnum.toInt o parseNum


fun parseString buf =
    case current buf of
        QString s => (advance buf; s)
      | t => raise ParseError ("Expecting a quoted string; saw " ^ toString t)

fun BrStringList buf = (
  require LBr buf;
  case current buf of
      RBr => (advance buf; [])
    | _ => commafy1 parseString buf before require RBr buf
)

(*
ThyData ::= 'LOADABLE_THYDATA' '[' ThyDataElements ']'
ThyDataElements ::= | ThyDataElement (',' ThyDataElement)*
ThyDataElement ::= <string> <string>+
*)
fun isQString (QString _) = true | isQString _ = false
fun isNum     (Num _)     = true | isNum     _ = false

fun ThyDataElement buf =
    let
      val ty = parseString buf
      val ds = list1 isQString parseString buf
    in
      {ty = ty, data = String.concat ds}
    end
fun ThyDataElements buf =
    case current buf of
        QString _ => commafy1 ThyDataElement buf
      | _ => []
val ThyData = tagged "LOADABLE_THYDATA" (bracketed "thydata" ThyDataElements)

(*
ClassInfo ::= 'CLASSES' '[' ClassMapletList ']'
ClassMapletList ::= | <string> Thmclass (',' <string> Thmclass)*
Thmclass = 'Def' | 'Thm' | 'Axm'
*)
fun Thmclass buf =
    case current buf of
        ID "Def" => (advance buf; DB.Def)
      | ID "Axm" => (advance buf; DB.Axm)
      | ID "Thm" => (advance buf; DB.Thm)
      | t => raise ParseError ("Expected a thm-class; saw "^toString t)
fun ClassMaplet buf =
    let
      val s = parseString buf
      val c = Thmclass buf
    in
      (s,c)
    end
fun ClassMapletList buf =
    case current buf of
        QString _ => commafy1 ClassMaplet buf
      | _ => []
val ClassInfo = tagged "CLASSES" (bracketed "CLASSES" ClassMapletList)

(*
Thms ::= 'THEOREMS' ThmList
ThmList ::= | Thm ThmList
Thm ::= <string> DepInfo Tags EncodedTerms
DepInfo ::= '[' DepHead (',' Deps)? ']'
DepHead ::= <string> <num>
Deps ::= Dep (',' Dep) *
Dep ::= <string> NumList1
Tags ::= BrStringList
EncodedTerms ::= BrStringList
*)

fun Dep buf = (parseString buf, list1 isNum parseInt buf)
val Deps = commafy1 Dep
fun DepHead buf = (parseString buf, parseInt buf)
fun DepInfo buf =
    let
      fun hddeps buf =
          let
            val hd = DepHead buf
            val deps =
                case current buf of
                    Comma => (advance buf; Deps buf)
                  | _ => []
          in
            (hd, deps)
          end
      val (hd,deps) = bracketed "dep-info" hddeps buf
    in
      {head = hd, deps = deps}
    end
fun Thm buf : encoded_thm =
    let
      val nm = parseString buf
      val depi = DepInfo buf
      val tags = BrStringList buf
      val tms = BrStringList buf
    in
      {name = nm, depinfo = depi, tagnames = tags, encoded_hypscon = tms}
    end
val ThmList = list isQString Thm
val Thms = tagged "THEOREMS" ThmList

(*
SharedTerms ::= 'TERMS' '[' TermList ']'
TermList ::= | SharedTerm (',' SharedTerm)*
SharedTerm ::= 'TMV' <string> <num> | 'TMC' <num> <num>
*)
fun SharedTerm buf =
    case current buf of
        ID "TMV" => (
                      advance buf;
                      SharingTables.TMV(parseString buf, parseInt buf)
                    )
      | ID "TMC" => (
                      advance buf;
                      SharingTables.TMC (parseInt buf, parseInt buf)
                    )
      | t => raise ParseError ("Expected SharingTerm op; saw " ^ toString t)
fun first_SharedTerm t =
    case t of
        ID s => s = "TMV" orelse s = "TMC"
      | _ => false
val TermList = commafy first_SharedTerm SharedTerm
val SharedTerms = tagged "TERMS" (bracketed "TERMS" TermList)

(*
NewConsts ::= 'INCORPORATE_CONSTS' '[' NewConstList ']'
NewConstList ::= | <string> <num> (',' <string> <num>)*
*)
fun NewConst buf = (parseString buf, parseInt buf)
val NewConsts =
    tagged "INCORPORATE_CONSTS"
           (bracketed "INCORPORATE_CONSTS" (commafy isQString NewConst))

(*
SharedTypes ::= 'TYPES' '[' TyList ']'
TyList ::= | SharedType (',' SharedType)*
SharedType ::= 'TYOP' <num> NumList | 'TYV' <string>
*)

fun first_SharedType t =
    case t of
        ID s => s = "TYOP" orelse s = "TYV"
      | _ => false
fun SharedType buf =
    case current buf of
        ID "TYOP" => let val _ = advance buf
                         val ns = list1 isNum parseInt buf
                     in
                       SharingTables.TYOP ns
                     end
      | ID "TYV" => (advance buf; SharingTables.TYV (parseString buf))
      | t => raise ParseError ("Expected Sharing type; saw " ^ toString t)
val SharedTypes =
    tagged "TYPES" (bracketed "TYPES" (commafy first_SharedType SharedType))

(*
IdVector ::= 'IDS' '[' IdList ']'
IdList ::=  | Id (',' Id)*
Id ::= <string> <string>
*)

fun Id buf =
    let val (thy,other) = (parseInt buf, parseInt buf)
    in
      (thy, other)
    end
val IdVector = tagged "IDS" (bracketed "IDS" (commafy isNum Id))

(*
Strings ::= 'STRINGS' NewStringList
NewStringList ::= '[' <string>* ']'
*)
val StringVector  =
    Vector.fromList o
    tagged "STRINGS" (bracketed "STRINGS" (list isQString parseString))

(*
NewTypes ::= 'INCORPORATE_TYPES' NewTypeList
NewTypeList ::= '[' ']' | '[' <string> <num> (',' <string> <num>)* ']'
*)
fun newtype buf = (parseString buf, parseInt buf)
val NewTypes =
    tagged "INCORPORATE_TYPES"
           (bracketed "INCORPORATE_TYPES" (commafy isQString newtype))


(*
datfile ::=
   'THEORY_AND_PARENTS' ThyName Parents
   NewTypes IdVector SharedTypes NewConsts SharedTerms Thms
   ClassInfo ThyData

ThyName ::= <string> <num> <num>

Parents ::= '[' ThyName (',' ThyName)* ']'
*)

fun ThyName buf = (parseString buf, parseNum buf, parseNum buf)
val Parents = bracketed "PARENTS" (commafy1 ThyName)

fun raw_read_dat buf : dat_info =
    let
      val _ = require (ID "THEORY_AND_PARENTS") buf
      val thyname = ThyName buf
      val parents = Parents buf
      val new_types = NewTypes buf
      val strvector = StringVector buf
      val idvector = IdVector buf
      val shared_types = SharedTypes buf
      val new_consts = NewConsts buf
      val shared_terms = SharedTerms buf
      val theorems = Thms buf
      val classinfo = ClassInfo buf
      val thydata = ThyData buf
    in
      {thyname = thyname, parents = parents, new_types = new_types,
       strvector = strvector,
       idvector = idvector, shared_types = shared_types,
       new_consts = new_consts, shared_terms = shared_terms,
       theorems = theorems, classinfo = classinfo, thydata = thydata}
    end

fun read_dat_file {filename} =
    let
      val istrm = TextIO.openIn filename
      val buf = TheoryDat_Reader.datBuffer istrm
      val v = Exn.capture raw_read_dat buf
    in
      TextIO.closeIn istrm; Exn.release v
    end

end (* struct *)
