structure GrammarDeltas :> GrammarDeltas =
struct

open HolKernel type_grammar_dtype term_grammar_dtype term_grammar
open HOLgrammars LoadableThyData

val ERROR = mk_HOL_ERR "GrammarDeltas"
type tmg_delta = term_grammar.user_delta
type tyg_delta = type_grammar.delta
datatype gdelta = TYD of tyg_delta | TMD of tmg_delta
fun fopt >> g = Option.map g o fopt

open ThyDataSexp
fun assoc_decode t =
    case t of
        String "LEFT" => SOME LEFT
      | String "RIGHT" => SOME RIGHT
      | String "NONASSOC" => SOME NONASSOC
      | _ => NONE
fun assoc_encode LEFT = String "LEFT"
  | assoc_encode RIGHT = String "RIGHT"
  | assoc_encode NONASSOC = String "NONASSOC"

val tydelta_decode =
  let
    open ThyDataSexp
    infix ||
    fun new_infix (nm,pnm,assoc,prec) =
      NEW_INFIX {Name = nm, ParseName = pnm, Assoc = assoc, Prec = prec}
    fun tyabbrev (kid, ty, p) = TYABBREV (kid, ty, p)
  in
    (tag_decode "new-type" kname_decode >> NEW_TYPE) ||
    (tag_decode "new-tyinfix"
                (pair4_decode (string_decode,string_decode,assoc_decode,
                               int_decode)) >> new_infix) ||
    (tag_decode "type-abbrev"
                (pair3_decode (kname_decode, type_decode, bool_decode)) >>
                tyabbrev) ||
    (tag_decode "disable-typrint" string_decode >> DISABLE_TYPRINT) ||
    (tag_decode "remove-knm-tyabbrev" kname_decode >> RM_KNM_TYABBREV)||
    (tag_decode "remove-tyabbrev" string_decode >> RM_TYABBREV)
  end

fun tydelta_encode tyd =
  let
    open ThyDataSexp
  in
    case tyd of
        NEW_TYPE kid => tag_encode "new-type" KName kid
      | NEW_INFIX{Name,ParseName,Assoc,Prec} =>
          tag_encode "new-tyinfix"
                     (pair4_encode (String,String,assoc_encode,Int))
                     (Name,ParseName,Assoc,Prec)
      | TYABBREV (kid, ty, prp) =>
          tag_encode "type-abbrev" (pair3_encode(KName,Type,Bool)) (kid,ty,prp)
      | DISABLE_TYPRINT s =>
          tag_encode "disable-typrint" String s
      | RM_KNM_TYABBREV kid => tag_encode "remove-knm-tyabbrev" KName kid
      | RM_TYABBREV s => tag_encode "remove-tyabbrev" String s
  end

fun check_tydelta (d: type_grammar.delta) =
  case d of
      NEW_TYPE knm => Type.uptodate_kname knm
    | TYABBREV (_, ty, _) => Type.uptodate_type ty
    | _ => true

(* ----------------------------------------------------------------------
    encoding and decoding grammars to and from s-expresions
   ---------------------------------------------------------------------- *)
open ThyDataSexp term_grammar_dtype
infix ||
fun brks_encode PP.CONSISTENT = String "C"
  | brks_encode PP.INCONSISTENT = String "I"
fun brks_decode (String "C") = SOME PP.CONSISTENT
  | brks_decode (String "I") = SOME PP.INCONSISTENT
  | brks_decode _ = NONE

val binfo_encode = pair_encode (brks_encode, Int)
val binfo_decode = pair_decode (brks_decode, int_decode)

fun style_encode AroundEachPhrase = String "each-phrase"
  | style_encode AroundSamePrec = String "same-prec"
  | style_encode AroundSameName = String "same-name"
  | style_encode NoPhrasing = String "no-phrasing"
fun style_decode (String "each-phrase") = SOME AroundEachPhrase
  | style_decode (String "same-prec") = SOME AroundSamePrec
  | style_decode (String "same-name") = SOME AroundSameName
  | style_decode (String "no-phrasing") = SOME NoPhrasing
  | style_decode _ = NONE

val block_style_encode = pair_encode (style_encode, binfo_encode)
val block_style_decode = pair_decode (style_decode, binfo_decode)

fun rule_element_encode rel =
    case rel of
      TOK s => tag_encode "TOK" String s
    | TM => Sym "TM"
    | ListTM{nilstr,cons,sep} =>
        tag_encode "ListTM" (pair3_encode(String,String,String))
                   (nilstr,cons,sep)
val rule_element_decode =
    (tag_decode "TOK" string_decode >> TOK) ||
    (require_tag "TM" >> (fn _ => TM)) ||
    (tag_decode "ListTM"
                (pair3_decode(string_decode,string_decode,string_decode)) >>
     (fn (n,c,s) => ListTM {nilstr=n,cons=c,sep=s}))

fun paren_style_encode Always = String "A"
  | paren_style_encode OnlyIfNecessary = String "O"
  | paren_style_encode ParoundPrec = String "C"
  | paren_style_encode ParoundName = String "N"
  | paren_style_encode NotEvenIfRand = String "R"
fun paren_style_decode t =
    case t of
        String "A" => SOME Always
      | String "O" => SOME OnlyIfNecessary
      | String "C" => SOME ParoundPrec
      | String "N" => SOME ParoundName
      | String "R" => SOME NotEvenIfRand
      | _ => NONE

fun ppel_encode ppel =
    case ppel of
      PPBlock (ppels, binfo) =>
        tag_encode "P" (pair_encode (mk_list ppel_encode, binfo_encode))
                   (ppels, binfo)
    | EndInitialBlock binfo => tag_encode "E" binfo_encode binfo
    | BeginFinalBlock binfo => tag_encode "B" binfo_encode binfo
    | HardSpace i => tag_encode "H" Int i
    | BreakSpace (x,y) => tag_encode "S" (pair_encode(Int,Int)) (x,y)
    | RE rel => tag_encode "R" rule_element_encode rel
    | ListForm lspec => tag_encode "ListForm" lspec_encode lspec
    | LastTM => Sym "L"
    | FirstTM => Sym "F"
and lspec_encode {separator, block_info, cons, nilstr} =
    pair4_encode (mk_list ppel_encode, String, String, binfo_encode)
                 (separator, cons, nilstr, block_info)


fun ppel_decode s =
    ((tag_decode "P" (pair_decode (list_decode ppel_decode, binfo_decode)) >>
                 PPBlock) ||
     (tag_decode "E" binfo_decode >> EndInitialBlock) ||
     (tag_decode "B" binfo_decode >> BeginFinalBlock) ||
     (tag_decode "H" int_decode >> HardSpace) ||
     (tag_decode "S" (pair_decode(int_decode,int_decode)) >> BreakSpace) ||
     (tag_decode "R" rule_element_decode >> RE) ||
     (tag_decode "ListForm" lspec_decode >> ListForm) ||
     (require_tag "L" >> (fn _ => LastTM)) ||
     (require_tag "F" >> (fn _ => FirstTM))) s
and lspec_decode s = let
  fun f (separator,cons,nilstr,binfo) =
      {separator = separator, nilstr = nilstr, block_info = binfo, cons = cons}
in
  (pair4_decode
     (list_decode ppel_decode,string_decode,string_decode,binfo_decode) >> f) s
end

fun rrule_encode {term_name,elements,timestamp,block_style,paren_style} =
    pair_encode(String,
                pair4_encode(mk_list ppel_encode, Int,
                             block_style_encode, paren_style_encode))
               (term_name, (elements, timestamp, block_style, paren_style))
val rrule_decode = let
  fun f (term_name, (elements, timestamp, block_style, paren_style)) =
      {term_name = term_name, timestamp = timestamp,
       block_style = block_style, paren_style = paren_style,
       elements = elements}
in
  pair_decode(string_decode,
              pair4_decode(list_decode ppel_decode, int_decode,
                           block_style_decode, paren_style_decode)) >> f
end;

fun binder_encode b =
    case b of
      LAMBDA => Sym "L"
    | BinderString{tok,term_name,timestamp} =>
      tag_encode "B" (pair3_encode (String,String,Int))
                 (tok,term_name,timestamp)
val binder_decode = let
  fun f (tok,term_name,timestamp) =
      BinderString {tok = tok, term_name = term_name,
                    timestamp = timestamp}
in
  (require_tag "L" >> (fn _ => LAMBDA)) ||
  (tag_decode "B" (pair3_decode(string_decode, string_decode, int_decode)) >> f)
end

fun pfxrule_encode prule =
    case prule of
      STD_prefix rrl => tag_encode "S" (mk_list rrule_encode) rrl
    | BINDER bl => tag_encode "B" (mk_list binder_encode) bl
val pfxrule_decode =
    (tag_decode "S" (list_decode rrule_decode) >> STD_prefix) ||
    (tag_decode "B" (list_decode binder_decode) >> BINDER)

fun sfxrule_encode srule =
    case srule of
      STD_suffix rrl => tag_encode "S" (mk_list rrule_encode) rrl
    | TYPE_annotation => Sym "T"
val sfxrule_reader =
    (tag_decode "S" (list_decode rrule_decode) >> STD_suffix) ||
    (require_tag "T" >> (fn _ => TYPE_annotation))

fun ifxrule_encode irule =
    case irule of
      STD_infix (rrl,a) =>
        tag_encode "S" (pair_encode (mk_list rrule_encode, assoc_encode))
                   (rrl, a)
    | RESQUAN_OP => Sym "R"
    | VSCONS => Sym "V"
    | FNAPP rrl => tag_encode "F" (mk_list rrule_encode) rrl
val ifxrule_reader =
    (tag_decode "S" (pair_decode(list_decode rrule_decode, assoc_decode)) >>
                STD_infix) ||
    (require_tag "R" >> K RESQUAN_OP) ||
    (require_tag "V" >> K VSCONS) ||
    (tag_decode "F" (list_decode rrule_decode) >> FNAPP);

fun fixity_encode f =
    case f of
      Infix(a,p) => tag_encode "I" (pair_encode(assoc_encode,Int)) (a,p)
    | Suffix p => tag_encode "S" Int p
    | Prefix p => tag_encode "P" Int p
    | Closefix => Sym "C"
    | Binder => Sym "B"
val fixity_decode =
    (tag_decode "I" (pair_decode(assoc_decode, int_decode)) >> Infix) ||
    (tag_decode "S" int_decode >> Suffix) ||
    (tag_decode "P" int_decode >> Prefix) ||
    (require_tag "C" >> K Closefix) ||
    (require_tag "B" >> K Binder)

fun grule_encode (gr : grule) =
  let
    val {term_name, pp_elements, paren_style, block_style, fixity} = gr
  in
    pair_encode (String,
                 pair4_encode(paren_style_encode,
                              block_style_encode,
                              fixity_encode,
                              mk_list ppel_encode))
                (term_name, (paren_style, block_style, fixity, pp_elements))
  end
val grule_decode : grule dec = let
  fun grule (tn,(ps,bs,f,ppels)) =
      {term_name = tn, paren_style = ps, block_style = bs,
       fixity = f, pp_elements = ppels}
in
  pair_decode(string_decode,
              pair4_decode(paren_style_decode, block_style_decode,
                           fixity_decode, list_decode ppel_decode)) >> grule
end

val skid_encode = pair_encode (String, KName)
val skid_decode = pair_decode (string_decode, kname_decode)

fun user_delta_encode ud =
    case ud of
      ADD_ABSYN_POSTP {codename} => tag_encode "AAPP" String codename
    | ADD_NUMFORM (c,s) =>
        tag_encode "AN" (pair_encode(Char,option_encode String)) (c,s)
    | ADD_STRLIT {tmnm,ldelim} =>
        tag_encode "AS" (pair_encode(String,String)) (tmnm,ldelim)
    | ADD_UPRINTER{codename=s,pattern=tm} =>
        tag_encode "AUP" (pair_encode(String,Term)) (s,tm)
    | ASSOC_RESTR {binder,resbinder} =>
        tag_encode "AR" (pair_encode (option_encode String, String))
                   (binder,resbinder)
    | CLR_OVL s => tag_encode "COV" String s
    | GRMOVMAP(s,tm) =>
        tag_encode "RMG" (pair_encode(String,Term)) (s,tm)
    | GRULE gr => tag_encode "G" grule_encode gr
    | IOVERLOAD_ON (s,t) => tag_encode "OI" (pair_encode(String,Term)) (s,t)
    | MOVE_OVLPOSN {frontp,skid} =>
        tag_encode "MOP" (pair_encode(Bool,skid_encode)) (frontp,skid)
    | OVERLOAD_ON (s,t) => tag_encode "OO" (pair_encode(String,Term)) (s,t)
    | RMOVMAP skid => tag_encode "RMO" skid_encode skid
    | RMTMNM s => tag_encode "RN" String s
    | RMTMTOK {term_name,tok} =>
        tag_encode "RK" (pair_encode(String,String)) (term_name,tok)
    | RMTOK s => tag_encode "RMT" String s
    | RM_STRLIT {tmnm} => tag_encode "RMS" String tmnm;


val user_delta_decode =
  (tag_decode "AAPP" string_decode >> (fn s => ADD_ABSYN_POSTP{codename = s}))||
  (tag_decode "AN" (pair_decode(char_decode, option_decode string_decode)) >>
              ADD_NUMFORM) ||
  (tag_decode "AS" (pair_decode(string_decode,string_decode)) >>
              (fn (tmnm,ldelim) => ADD_STRLIT{tmnm=tmnm,ldelim=ldelim})) ||
  (tag_decode "AUP" (pair_decode(string_decode,term_decode)) >>
              (fn (s,p) => ADD_UPRINTER {codename = s, pattern = p})) ||
  (tag_decode  "AR" (pair_decode(option_decode string_decode, string_decode)) >>
               (fn (b,rb) => ASSOC_RESTR {binder = b, resbinder = rb})) ||
  (tag_decode "COV" string_decode >> CLR_OVL) ||
  (tag_decode "RMG" (pair_decode (string_decode,term_decode)) >> GRMOVMAP) ||
  (tag_decode "G" grule_decode >> GRULE) ||
  (tag_decode "OI" (pair_decode(string_decode,term_decode)) >> IOVERLOAD_ON) ||
  (tag_decode "MOP" (pair_decode(bool_decode, skid_decode)) >>
              (fn (frontp,skid) => MOVE_OVLPOSN {frontp=frontp,skid=skid})) ||
  (tag_decode "OO" (pair_decode(string_decode,term_decode)) >> OVERLOAD_ON) ||
  (tag_decode "RMO" skid_decode >> RMOVMAP) ||
  (tag_decode "RN" string_decode >> RMTMNM) ||
  (tag_decode "RK" (pair_decode(string_decode,string_decode)) >>
              (fn (nm,tok) => RMTMTOK {term_name = nm, tok = tok})) ||
  (tag_decode "RMT" string_decode >> RMTOK) ||
  (tag_decode "RMS" string_decode >> (fn s => RM_STRLIT{tmnm=s}));

fun grammar_rule_encode grule =
    case grule of
      PREFIX pr => tag_encode "P" pfxrule_encode pr
    | SUFFIX sr => tag_encode "S" sfxrule_encode sr
    | INFIX ir => tag_encode "I" ifxrule_encode ir
    | CLOSEFIX rrl => tag_encode "C" (mk_list rrule_encode) rrl

val grammar_rule_decode =
    (tag_decode "P" pfxrule_decode >> PREFIX) ||
    (tag_decode "S" sfxrule_reader >> SUFFIX) ||
    (tag_decode "I" ifxrule_reader >> INFIX) ||
    (tag_decode "C" (list_decode rrule_decode) >> CLOSEFIX);

fun gdelta_encode (TMD udelta) = user_delta_encode udelta
  | gdelta_encode (TYD tydelta) = tydelta_encode tydelta
val gdelta_decode = (user_delta_decode >> TMD) || (tydelta_decode >> TYD);

fun check_delta (d: user_delta) =
  case d of
      MOVE_OVLPOSN {skid = (_, kid), ...} => can prim_mk_const kid
    | RMOVMAP (_, kid) => can prim_mk_const kid
    | OVERLOAD_ON(_, t) => Term.uptodate_term t
    | IOVERLOAD_ON(_, t) => Term.uptodate_term t
    | GRMOVMAP(_, t) => Term.uptodate_term t
    | ADD_UPRINTER{pattern,...} => Term.uptodate_term pattern
    | _ => true

fun part tyds tmds gds =
    case gds of
        [] => (List.rev tyds, List.rev tmds)
      | TMD d :: rest => part tyds (d::tmds) rest
      | TYD d :: rest => part (d::tyds) tmds rest

fun nopp s _ = HOLPP.add_string ("<" ^ s ^ ">")

fun other_tds (t, thyevent) =
    case list_decode gdelta_decode t of
        NONE => raise Fail ("GrammarDelta: encoding failure: t = \n  " ^
                            HOLPP.pp_to_string 70
                             (pp_sexp (nopp"ty") (nopp"tm") (nopp"thm"))
                             t)
      | SOME gds =>
        let
          val (tyds, tmds) = part [] [] gds
          val (goodtyds, badtyds) = Lib.partition check_tydelta tyds
          val (goodtmds, badtmds) = Lib.partition check_delta tmds
        in
          if null badtyds andalso null badtmds then NONE
          else
            SOME (mk_list gdelta_encode (map TYD goodtyds @ map TMD goodtmds))
        end

val {export, segment_data, set} = ThyDataSexp.new {
      thydataty = "grammardelta",
      merge = append_merge,
      load = fn _ => (),
      other_tds = other_tds
    }

fun thy_deltas {thyname} =
    case segment_data {thyname = thyname} of
        NONE => ([], [])
      | SOME gds =>
        case list_decode gdelta_decode gds of
            NONE => raise Fail "GrammarDelta: encoding failure 2"
          | SOME gds =>
            let
            in
              part [] [] gds
            end



fun userdelta_toString ud =
  case ud of
      OVERLOAD_ON (s, _) => "overload_on(" ^ Lib.mlquote s ^ ")"
    | CLR_OVL s => "clear_overloads_on(" ^ Lib.mlquote s ^ ")"
    | _ => ""

fun record_tmdelta d = export (mk_list gdelta_encode [TMD d])

fun record_tydelta d = export (mk_list gdelta_encode [TYD d])

fun clear_deltas() = set (mk_list gdelta_encode [])

end
