structure internal_functions :> internal_functions =
struct

fun member e [] = false
  | member e (h::t) = e = h orelse member e t

fun spacify0 acc [] = List.rev acc
  | spacify0 acc [x] = List.rev (x::acc)
  | spacify0 acc (h::t) = spacify0 (" "::h::acc) t

val spacify = String.concat o spacify0 []

fun find_unescaped cset = let
  open Substring
  fun recurse i ss =
      case getc ss of
        NONE => NONE
      | SOME(c', ss') => if member c' cset then SOME i
                         else if c' = #"\\" then
                           case getc ss' of
                             NONE => NONE
                           | SOME (_, ss'') => recurse (i + 2) ss''
                         else recurse (i + 1) ss'
in
  recurse 0
end

fun tokenize s = let
  (* could be a call to tokens, but for escaped spaces getting in the way *)
  open Substring
  val ss = dropl Char.isSpace (full s)
  fun recurse acc ss =
      (* assumes first character of ss is not isSpace, or size ss = 0  *)
      if size ss = 0 then List.rev acc
      else
        case find_unescaped [#" ", #"\t"] ss of
          NONE => List.rev (string ss::acc)
        | SOME i => let
            val (t1, rest) = splitAt(ss, i)
          in
            recurse (string t1::acc) (dropl Char.isSpace rest)
          end
in
  recurse [] ss
end

fun subst(from,to,on) = let
  open Substring
  val (from,to,on) = (full from, full to, full on)
  val _ = size from > 0 orelse
          raise Fail "empty from argument to `subst' function"
  fun recurse acc ss = let
    val (ok, rest) = position (string from) ss
  in
    if size rest > 0 then
      recurse (to::ok::acc) (slice(rest, size from, NONE))
    else concat (List.rev (ok::acc))
  end
in
  recurse [] on
end


fun find_percent ss = let
  open Substring
  fun recurse acc ss =
      case getc ss of
        NONE => (full (String.implode (List.rev acc)), full "")
      | SOME(c, ss') => let
        in
          case c of
            #"\\" => let
            in
              case getc ss' of
                NONE => (full (String.implode (List.rev (c::acc))), full "")
              | SOME(c',ss'') =>
                if c' = #"%" orelse c' = #"\\" then
                  recurse (c'::acc) ss''
                else
                  recurse (c'::c::acc) ss''
            end
          | _ => if c = #"%" then (full (String.implode(List.rev acc)), ss)
                 else recurse (c::acc) ss'
        end
in
  recurse [] ss
end

fun pattern_match pattern object = let
  open Substring
  fun translate_pattern patss = let
    val (pfx, rest) = find_percent patss
    val sfx = if size rest > 0 then let
                  val (sfx, rest') = find_percent (slice(rest, 1, NONE))
                in
                  if size rest' > 0 then
                    raise Fail "Multiple % chars in pattern"
                  else
                    SOME sfx
                end
              else NONE
  in
    (pfx, sfx)
  end
  fun fromright (patss, i) (objss, j) =
      if j = ~1 then NONE
      else if i = ~1 then SOME (slice(objss, 0, SOME (j + 1)))
      else let
          val pc = sub(patss, i)
          val oc = sub(objss, j)
        in
          if pc = oc then fromright(patss, i - 1) (objss, j - 1)
          else NONE
        end

  val (patpfx, patsfx) = translate_pattern (full pattern)
  val objss = full object
in
  if isPrefix (string patpfx) objss then let
      val objrest = slice(objss, size patpfx, NONE)
    in
      case patsfx of
        NONE => if size objrest = 0 then SOME "" else NONE
      | SOME sfx => Option.map string
                               (fromright (sfx, size sfx - 1)
                                          (objrest, size objrest - 1))
    end
  else NONE
end

fun pcsubst (residue, pattern) = let
  open Substring
  val patss = full pattern
  val resss = full residue
  fun recurse acc ss =
      case find_unescaped [#"%"] ss of
        NONE => concat (List.rev (ss::acc))
      | SOME i => let
          val (pfx, sfx) = splitAt(ss, i)
        in
          recurse (resss::pfx::acc) (slice(sfx, 1, NONE))
        end
in
  recurse [] (full pattern)
end

fun patsubst (from,to,arglist) = let
  fun mapthis s =
      case pattern_match from s of
        NONE => s
      | SOME stem => pcsubst(stem,to)
in
  spacify (map mapthis (tokenize arglist))
end

fun function_call (fnname, args, eval) = let
  open Substring
in
  case fnname of
    "if" =>
    if length args <> 2 andalso length args <> 3 then
      raise Fail "Bad number of arguments to `if' function."
    else let
        val condition = dropr Char.isSpace (hd args)
        val condition_evalled = eval condition
      in
        if condition_evalled <> "" then eval (List.nth(args, 1))
        else if length args = 3 then eval (List.nth(args, 2))
        else ""
      end
  | "subst" =>
    if length args <> 3 then
      raise Fail "Bad number of arguments to `subst' function."
    else let
        val args_evalled = map eval args
        val tuple = case args_evalled of
                      [x,y,z] => (x,y,z)
                    | _ => raise Fail "Can't happen"
      in
        subst tuple
      end
  | "patsubst" =>
    if length args <> 3 then
      raise Fail "Bad number of arguments to `patsubst' function."
    else let
        val args_evalled = map eval args
        val tuple = case args_evalled of
                      [x,y,z] => (x,y,z)
                    | _ => raise Fail "Can't happen"
      in
        patsubst tuple
      end
  | "protect" => if length args <> 1 then
                   raise Fail "Bad number of arguments to `protect' function."
                 else
                   Systeml.protect (eval (hd args))
  | "dprot" => if length args <> 1 then
                 raise Fail "Bad number of arguments to 'dprot' function."
               else subst(" ", "\\ ", eval (hd args))
  | "findstring" => if length args <> 2 then
                      raise Fail "Bad number of arguments to 'findstring' \
                                 \function."
                    else let
                        val (findstr, instr) = case map eval args of
                                                 [x,y] => (x,y)
                                               | _ => raise Fail "Can't happen"
                        open Substring
                        val (pfx,sfx) = position findstr (full instr)
                      in
                        if size sfx = 0 then "" else findstr
                      end
  | _ => raise Fail ("Unknown function name: "^fnname)
end


end (* struct *)
