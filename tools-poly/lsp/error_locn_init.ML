(* ----------------------------------------------------------------------
   Installs `LSPExtension.exnReport': what a HOL exception says about
   itself, as a file position and a message.

   `server.ML' is compiled into `bin/hol' before HOL exists, so it
   cannot name `Feedback' or `locn' and has to treat every exception
   escaping a declaration as an opaque `exn'.  That is why a type error
   in a `Theorem' goal used to squiggle the `Theorem' keyword: the
   position was the declaration's start, the only one available.

   The position is there for the taking.  `HOLSourceExpand.mkLocPragma'
   prefixes every quotation literal the expander emits with
   `(*#loc LINE COL*)' in whole-file coordinates; `base_lexer's
   `dolocpragma' reads it and rebases each token through
   `locn.rel_to_abs'.  So the `locn' inside a `HOL_ERR' raised while
   elaborating a `Theorem', `Definition', `Inductive' or `Datatype'
   body is already an absolute `LocA' pair in the buffer the client
   sent.  All this file does is dig it out.

   Only `HOL_ERR' is handled.  `base_tokens.LEX_ERR' and
   `parse_term.ParseTermError' also carry a `locn', but `TermParse.sml'
   converts both to located `HOL_ERR's at the one boundary they cross,
   and naming a structure the bare heap might not have is exactly the
   startup failure `tests/load-init-files.ML --bare' exists to catch.

   `Feedback' and `locn' are both in `hol.state0', which is the least
   heap a server ever starts on.
   ---------------------------------------------------------------------- *)

local

(* --- Locations ------------------------------------------------------- *)

fun unNear (locn.Loc_Near l) = unNear l
  | unNear l = l

(* A `locn' as the pair of file positions the hook promises, or NONE.
   Both ends are `LocA's, so both are 0-origin and count bytes, and
   the end is the last character rather than one past it -- the
   caller widens it by a byte once it is an offset, which is what
   `hover_quote_init's `locn_range' does and the reason it does it:
   the end column of a region ending at a line's last character is
   past that line, and converting it as a column clamps it back onto
   the character before it.

   Anything that is not a pair of `LocA's -- a `LocP' from a
   quotation with no pragma, `Loc_None', `Loc_Unknown' -- has no file
   position, and says so. *)
fun usableLocn l =
  case unNear l of
    locn.Loc (locn.LocA (l1, c1), locn.LocA (l2, c2)) =>
      if l1 < l2 orelse (l1 = l2 andalso c1 <= c2) then
        SOME ((l1, c1), (l2, c2))
      else NONE
  | _ => NONE

(* The origins of a `HOL_ERR' run outermost-first, and only the
   innermost one is any use.  `Q.store_thm_at' catches and re-raises
   through `wrap_exn', which conses an origin carrying `Loc_Unknown'
   onto the FRONT -- so `Feedback.top_location_of' answers about the
   wrapper, never about the term.  Nor is the first *located* origin
   right: an intermediate one can hold a `locn.between'-merged span
   straddling two different pragmas, which for a `Definition' reads as
   a range running from the enclosing SML quotation to the fault.  The
   last usable one is the one that was raised closest to the mistake. *)
fun innermostLocn (origins : Feedback.origin list) =
  List.foldl (fn (org, best) =>
                 case usableLocn (#source_location org) of
                     NONE => best
                   | found => found)
             NONE origins

(* --- Messages -------------------------------------------------------- *)

fun trimWS s = let
  val n = size s
  fun lead i = if i < n andalso Char.isSpace (String.sub (s, i))
               then lead (i + 1) else i
  fun trail i = if i > 0 andalso Char.isSpace (String.sub (s, i - 1))
                then trail (i - 1) else i
  val a = lead 0
  val b = trail n
in
  if b <= a then "" else String.substring (s, a, b - a)
end

(* Every rendering `locn.toString' can produce starts with one of
   these.  Used to spot a line that is nothing but location text. *)
val locnLeadIns =
  ["at ", "on ", "between ", "roughly ",
   "in compiler-generated text", "in unknown location"]

fun isLocnLine l =
  String.isSuffix "." l andalso
  List.exists (fn p => String.isPrefix p l) locnLeadIns

(* The term grammar bakes its own location into its message:
   `parse_term.sml' builds "Don't expect to find a X in this position
   after a Y\n" ^ locn.toString a ^ " and " ^ locn.toString b ^ ".\n".
   Once the squiggle is on the right characters that last line is
   saying twice what the editor already shows, so drop it -- but only
   when there IS a squiggle, and only when something is left. *)
fun dropLocnTail msg = let
  val msg = trimWS msg
in
  case rev (String.fields (fn c => c = #"\n") msg) of
    [] => msg
  | last :: revInit =>
      if isLocnLine (trimWS last) then
        (case trimWS (String.concatWith "\n" (rev revInit)) of
             "" => msg
           | kept => kept)
      else msg
end

(* `Feedback.message_of' rather than `format_ERR': that prepends
   "Exception raised " and prints the whole origin chain WITH its
   locations, which is the squiggle's job.  What is wanted here is the
   sentence HOL wrote about the mistake.  An error with no message of
   its own -- all of its information in its origins -- falls back to
   HOL's full rendering rather than to nothing. *)
fun messageOf e err = let
  val body = case trimWS (Feedback.message_of err) of
                 "" => trimWS (Feedback.exn_to_string e)
               | m => m
in
  if body = "" then "HOL error" else body
end

fun report e =
  case e of
    Feedback.HOL_ERR err => let
      val range = innermostLocn (Feedback.origins_of err)
      val body = messageOf e err
      val body = case range of NONE => body | SOME _ => dropLocnTail body
    in
      {range = range, message = SOME body}
    end
    (* Not a HOL error: no position, and no opinion about how the
       server should render it. *)
  | _ => {range = NONE, message = NONE}

in

val () = LSPExtension.exnReport := report

end (* local *)
