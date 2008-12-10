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
      val contents = Substring.full (TextIO.inputAll istrm)
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


val valid_keywords =   (* not currently used *)
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

local val BLTYPE = Substring.full "BLTYPE"
      val ELTYPE = Substring.full "ELTYPE"
      val TYPEss = Substring.full "TYPE"
      val BLTYPEsize = Substring.size ELTYPE
in
fun longtype_elim (l as (doc::ss1::ss2::rst)) =
     let val (ssa,ssb) = position "BLTYPE" ss1
         val (ssc,ssd) = position "ELTYPE" ss2
     in if isEmpty ssa andalso isEmpty ssc
          then doc :: full(concat[TYPEss, triml BLTYPEsize ssb]) :: rst
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
      recurse (full "{"::ssa::acc) (triml 7 ssb)
    else if isPrefix "\\rbrace" ssb then
      recurse (full "}"::ssa::acc) (triml 7 ssb)
    else
      recurse (slice(ss,0,SOME (size ssa + 1))::acc) (triml 1 ssb)
  end
in
  full (recurse [] ss)
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
  val ss0 = full (OS.Path.file fname)
  val (ss1,_) = position ".doc" ss0
in
  case tokens (equal #".") (full (Symbolic.tosymb (string ss1))) of
    [] => raise Fail "Can't happen"
  | [x] => x
  | (_::y::_) => y
end

fun install_doc_part fname sections =
    case sections of
      FIELD("DOC", []) :: ss =>
         FIELD("DOC", [TEXT (name_from_fname fname)]) :: ss
    | FIELD("DOC", [TEXT m]) :: ss => sections
    | _ => raise ParseError "Ill-formed \\DOC section"

(* if there isn't a STRUCTURE section, then add one if the filename of the
   docfile suggests that there should be. *)
fun install_structure_part fname sections = let
  fun has_struct_section slist =
      case slist of
        [] => false
      | FIELD("STRUCTURE", m)::_ =>
        (case m of
           [TEXT ss] => if length (tokens Char.isSpace ss) <> 1 then
                          raise ParseError "Multi-word \\STRUCTURE section"
                        else true
         | _ => raise ParseError "Ill-formed \\STRUCTURE section")
    | _::t => has_struct_section t
  fun insert3 x [] = [x]
    | insert3 x [y] = [y, x]
    | insert3 x (h1::h2::t) = h1::h2::x::t
  val name_parts = String.tokens (equal #".") (#file (OS.Path.splitDirFile fname))
in
  if not (has_struct_section sections) andalso length name_parts = 3
  then
    insert3 (FIELD("STRUCTURE", [TEXT (full (hd name_parts))])) sections
  else sections
end


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

(* check that the second field is the "TYPE" one *)
fun check_type_field2 [] = raise ParseError "Empty field list!"
  | check_type_field2 [x] = raise ParseError "Only one field!"
  | check_type_field2 (x as (_::TYPE _::_)) = x
  | check_type_field2 _ = raise ParseError "\\TYPE field not second"

fun parse_file docfile = let
  fun db_out (BRKT ss) = BRKT (unescape_braces ss)
    | db_out (XMPL ss) = XMPL (unescape_braces ss)
    | db_out otherwise = otherwise

  fun section (tag, ss) =
      case tag of
        "TYPE" => TYPE (parse_type ss)
      | "SEEALSO" => let
          val args = tokens (Char.isSpace \/ equal #",")
                            (dropr (Char.isSpace \/ equal #".") ss)
        in
          if null args then
            raise ParseError "Empty SEEALSO list"
          else
            SEEALSO args
        end
      | otherwise =>
        FIELD (tag, trimws (List.map db_out (paragraphs (markup ss))))
  val firstpass = List.map section (to_sections (fetch_contents docfile))
  val finalisation = final_char_check o
                     check_type_field2 o
                     install_structure_part docfile o
                     install_doc_part docfile
in
  finalisation firstpass
end handle ParseError s => raise ParseError (docfile^": "^s)
         | x => (warn ("Exception raised in "^docfile^"\n"); raise x)

(* ----------------------------------------------------------------------
    File handling routines
   ---------------------------------------------------------------------- *)

open String
fun stripdoc_suff s = String.extract(s, 0, SOME (size s - 4))
fun hasdoc_suff s =
    String.extract(s, size s - 4, NONE) = ".doc"
    handle Subscript => false

fun valid_doc_name s = hasdoc_suff s

fun core_dname dnm = let
  val toks = String.tokens (equal #".") dnm
in
  if length toks = 2 then hd (tl toks) else hd toks
end

fun structpart dnm =  hd (String.tokens (equal #".") dnm)

(* returns a set of file-names from the given directory that are .doc
   files *)
fun find_docfiles dirname = let
  val dirstr = OS.FileSys.openDir dirname
  fun name_compare(s1,s2) = let
    (* names already less .doc suffix *)
    val lower = String.map Char.toLower
    val s1tok = lower (core_dname (Symbolic.tosymb s1))
    val s2tok = lower (core_dname (Symbolic.tosymb s2))
  in
    case String.compare (s1tok, s2tok) of
      EQUAL => String.compare(lower (structpart s1), lower (structpart s2))
    | x => x
  end
  fun insert s t =
      if valid_doc_name s then Binaryset.add(t, stripdoc_suff s)
      else t
  fun loop acc =
      case OS.FileSys.readDir dirstr of
        SOME s => loop (insert s acc)
      | NONE => (OS.FileSys.closeDir dirstr; acc)
in
  loop (Binaryset.empty name_compare)
end


end
