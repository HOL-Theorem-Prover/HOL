structure ParseDoc :> ParseDoc =
struct

open Substring;
exception ParseError of string

fun I x = x;

fun curry f x y = f (x,y)
fun equal x y = (x=y)
infix ##;
fun (f##g) (x,y) = (f x, g y);

fun butlast [] = raise Fail "butlast"
  | butlast [x] = []
  | butlast (h::t) = h::butlast t;

fun flat [] = []
  | flat ([]::rst) = flat rst
  | flat ((h::t)::rst) = h::flat(t::rst);

infixr 4 \/
infixr 5 /\
fun (f \/ g) x = f x orelse g x
fun (f /\ g) x = f x andalso g x;

fun occurs s ss = not (isEmpty (#2 (position s ss)));

fun fetch_contents docfile =
  let val istrm = TextIO.openIn docfile
      val contents = Substring.all (TextIO.inputAll istrm)
      val _ = TextIO.closeIn istrm
  in contents
  end;

fun fetch str = Substring.string (fetch_contents str);

(*---------------------------------------------------------------------------
       A HOL ".doc" file has the format

         \DOC <ident>

         ( \<keyword> <paragraph>* )*

         \ENDDOC
 ---------------------------------------------------------------------------*)

datatype markup
   = PARA
   | TEXT of substring
   | BRKT of substring
   | XMPL of substring;

datatype section
   = TYPE of substring
   | FIELD of string * markup list
   | SEEALSO of substring list;


val valid_keywords =
    Binaryset.addList(Binaryset.empty String.compare,
                      ["DOC", "ELTYPE", "BLTYPE", "TYPE", "SYNOPSIS",
                       "COMMENTS", "USES", "SEEALSO", "KEYWORDS", "DESCRIBE",
                       "FAILURE", "EXAMPLE", "ENDDOC", "LIBRARY",
                       "STRUCTURE"])

fun check_string ss = let
  val s = Substring.string ss
in
  if Binaryset.member(valid_keywords, s) then
    s
  else
    raise ParseError ("Unknown keyword: "^s)
end


fun divide ss =
  if isEmpty ss
    then []
    else let val (ss1,ss2) = position "\n\\" ss
         in
           if isEmpty ss1 then divide (triml 2 ss2)
           else ss1::divide (triml 2 ss2)
         end;

local val BLTYPE = Substring.all "BLTYPE"
      val ELTYPE = Substring.all "ELTYPE"
      val TYPEss = Substring.all "TYPE"
      val BLTYPEsize = Substring.size ELTYPE
in
fun longtype_elim (l as (doc::ss1::ss2::rst)) =
     let val (ssa,ssb) = position "BLTYPE" ss1
         val (ssc,ssd) = position "ELTYPE" ss2
     in if isEmpty ssa andalso isEmpty ssc
          then doc :: all(concat[TYPEss, triml BLTYPEsize ssb]) :: rst
          else l
     end
  | longtype_elim l = l
end;

fun warn s = TextIO.output(TextIO.stdErr, s)

fun find_doc ss = let
  val (ssa, ssb) = position "\\DOC" ss
  val _ = not (isEmpty ssb) orelse raise ParseError "No \\DOC beginning entry"
  val _ = isEmpty ssa orelse raise ParseError "Text before \\DOC"
  val (docpart, rest) = position "\n" ss
  val docheader = slice(docpart, 1, NONE)
in
  (docheader, slice(rest,1,NONE))
end

fun to_sections ss =
  let open Substring
      val (docpart, rest) = find_doc ss
      val sslist = docpart :: divide rest
      (* butlast below drops final \enddoc *)
      val sslist1 = longtype_elim (butlast sslist)
  in
   map ((check_string ## dropl Char.isSpace) o
        splitl (not o Char.isSpace)) sslist1
  end;

(*---------------------------------------------------------------------------
        Divide into maximal chunks of text enclosed by braces.
 ---------------------------------------------------------------------------*)

(* skips over text until it finds the end of a brace delimited bit of text *)
fun braces ss = let
  fun recurse ss n =
      case getc ss of
        SOME(#"}", ss1) => if n = 1 then ss1
                           else recurse ss1 (n - 1)
      | SOME(#"{", ss1) => recurse ss1 (n + 1)
      | SOME (_, ss1) => recurse ss1 n
      | NONE => raise ParseError "No closing brace"
in
  recurse ss 0
end

fun markup ss =
 let val (ssa,ssb) = position "{" ss
 in if isEmpty ssb then [TEXT ss]
    else let val ssc = braces ssb
             val (s,i,n) = base ssa
             val (_,j,_) = base ssc
             val chunk = substring (s,i+n+1,j-(i+n+2))
         in TEXT ssa
             :: (if occurs "\n" chunk then XMPL chunk else BRKT chunk)
             :: markup ssc
         end
 end;

val paragraphs =
  let fun para (TEXT ss) =
           let fun insP ss =
                let val (ssa,ssb) = position "\n\n" ss
                in if isEmpty ssb then [TEXT ss]
                   else TEXT ssa::PARA::insP (dropl Char.isSpace ssb)
                end
           in insP ss
           end
        | para other = [other]
  in flat o map para
  end;


(* Translates out escaped braces wherever they might appear.  *)
fun unescape_braces ss = let
  fun isBrace c = c = #"{" orelse c = #"}"
  fun recurse acc ss = let
    val (ssa, ssb) = splitl (not o equal #"\\") ss
  in
    if size ssb = 0 then
      concat (List.rev (ssa::acc))
    else if isPrefix "\\lbrace" ssb then
      recurse (all "{"::ssa::acc) (triml 7 ssb)
    else if isPrefix "\\rbrace" ssb then
      recurse (all "}"::ssa::acc) (triml 7 ssb)
    else
      recurse (slice(ss,0,SOME (size ssa + 1))::acc) (triml 1 ssb)
  end
in
  all (recurse [] ss)
end

fun parse_type ss =
 let val ss' =
      case getc (dropl Char.isSpace ss)
       of SOME(#"{", ss1) =>
           let val ss2 = dropr Char.isSpace ss1
           in if sub(ss2,size ss2 - 1) = #"}" then trimr 1 ss2
              else raise ParseError "Closing brace not found in \\TYPE"
           end
        | other => ss
  in unescape_braces ss'
  end

fun trimws mlist =
    case mlist of
      [] => []
    | [TEXT ss] => let val newss = dropr Char.isSpace ss
                   in
                     if size newss > 0 then [TEXT newss] else []
                   end
    | (x::xs) => x :: trimws xs



(* if the firstpass has an empty DOC component, then give it a full one
   generated from the name of the file. *)
fun name_from_fname fname = let
  val ss0 = all (Path.file fname)
  val (ss1,_) = position ".doc" ss0
in
  case tokens (equal #".") (all (Symbolic.tosymb (string ss1))) of
    [] => raise Fail "Can't happen"
  | [x] => x
  | (_::y::_) => y
end

fun install_doc_part fname sections =
    case sections of
      (FIELD("DOC", []) :: ss) =>
         FIELD("DOC", [TEXT (name_from_fname fname)]) :: ss
    | x => x

fun check_char_markup m = let
  fun illegal_char c = c = #"{" orelse c = #"}" orelse c = #"\\"
in
  case m of
    TEXT ss => let
      val (ssa, ssb) = splitl (not o illegal_char) ss
    in
      if not (isEmpty ssb) then let
          val (s0, j, _) = base ssb
          val lo = if j > 5 then j - 5 else 0
          val hi = if j + 5 > String.size s0 then NONE else SOME (j + 5 - lo)
        in
          raise ParseError ("Illegal character "^str (sub(ssb,0))^ " in "^
                            "context: "^string (extract(s0,lo,hi)))
        end
      else ()
    end
  | _ => ()
end


fun check_char_section s =
    case s of
      FIELD (fname, mlist) => if fname <> "DOC" then
                                List.app check_char_markup mlist
                              else ()
    | _ => ()

fun final_char_check slist = (List.app check_char_section slist; slist)

fun parse_file docfile =
 let fun db_out (BRKT ss) = BRKT (unescape_braces ss)
       | db_out (XMPL ss) = XMPL (unescape_braces ss)
       | db_out otherwise = otherwise

     fun section (tag, ss) =
       case tag
        of "TYPE" => TYPE (parse_type ss)
         | "SEEALSO" => SEEALSO
                          (tokens (Char.isSpace \/ equal #",")
                             (dropr (Char.isSpace \/ equal #".") ss))
         | otherwise =>
           FIELD (tag, trimws (List.map db_out (paragraphs (markup ss))))
     val firstpass = List.map section (to_sections (fetch_contents docfile))
  in
   final_char_check (install_doc_part docfile firstpass)
  end handle ParseError s => raise ParseError (docfile^": "^s)
           | x => (warn ("Exception raised in "^docfile^"\n"); raise x)

end; (* struct *)