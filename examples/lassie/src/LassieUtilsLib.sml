structure LassieUtilsLib =
struct

  open Lib;
(*********************************)
(*            Utils              *)
(*********************************)
fun sleep t =
  let
    val wakeUp = Time.+ (Time.now(), Time.fromReal(t))
    fun wait () = if Time.> (Time.now(), wakeUp) then () else wait ()
  in
    wait ()
  end;

fun flushStream instream =
  case TextIO.canInput(instream, 5000) of
    NONE => ()
    | SOME n =>
      if n = 0 then ()
      else (TextIO.input(instream); flushStream(instream));

(* some string editing to remove long package names esp. in call formulas *)
fun simplifyAbsoluteNames str =
  let
    fun isSep s = mem s [#" ", #"(", #")", #"\""]
    fun append s l =
      case l of
        [] => [s]
        | hd::tl => (s ^ hd)::tl
    val tokens =
      List.foldl
        (fn (c,l) => if isSep c then ""::(String.str c)::l else append (String.str c) l)
        []
        (List.rev (String.explode str))
    fun isNotEmpty s = not (s = "")
    fun getLocalName s = List.hd (List.rev (String.tokens (fn c => c = #".") s))
  in
    String.concat (map getLocalName (List.filter isNotEmpty tokens))
  end;

(* escape quotes and backslashes before writing to a string *)
fun escape str =
  let
    val escEsc = map (fn c => if c = "\\" then "\\\\" else c)
    val escQuotes = map (fn c => if c = "\"" then "\\\"" else c)
  in
    str |> String.explode
        |> map String.str
        |> escEsc
        |> escQuotes
        |> String.concat
  end;

(* normalize a string representing an HOL4 expression for viewing *)
fun normalize str =
  let
  (* space out function applications through direct parens e.g. map(f)lst *)
    fun injectSpc sl =
      case sl of
        s1::s2::tl =>
          if (s2 = "(" andalso not (mem s1 ["("," ",")"])) orelse
             (s1 = ")" andalso not (mem s2 [")"," "]))
          then injectSpc (s1::" "::s2::tl)
          else s1::(injectSpc (s2::tl))
        | other => other
    (* rewrite string with a minimal number of parentheses *)
    fun paren str b = if b then ("("::str) @ [")"] else str
    fun rmParens left p right =
      case right of
        [] => (left, false, []) (* base case *)
        | c::tail =>
          if c = ")" then (left, p, tail) (* base case of rec calls *)
          else if c = "("
          then
            let (* inductive case *)
              val (left', p', right') = rmParens [] false tail (* rec *)
              (* if nothing on left do not parenthesize, applications are left associative *)
              val left' = if left = [] then left' else paren left' p'
              val left' = if left' = [] then ["(",")"] else left' (* unit *)
            in
              rmParens (left @ left') p right'
            end (* continue *)
          else rmParens (left@[c]) (p orelse c = " ") tail
    val (retStr, _, _) =
      rmParens [] false ( str |> String.explode
                              |> (map String.str)
                              |> injectSpc )
  in
    String.concat retStr
  end;

exception VariableUndefined of string;

fun endsWith (s:string) (c:char) : bool =
  let
    val sl = explode s;
  in
    (hd (List.rev sl) = c)
  end;

fun getOSVar name =
  case OS.Process.getEnv name of
    NONE => raise VariableUndefined ("Variable " ^ name ^ " not defined in environment")
  | SOME s => s;

fun string_split s cr =
  let
    fun nextStr cr [] strAcc = ([],List.rev strAcc) |
        nextStr cr (c::res) strAcc =
          if c = cr
          then (res, List.rev strAcc)
          else nextStr cr res (c :: strAcc);
    fun splitAll cr [] acc = List.rev acc |
        splitAll cr chrl acc =
          let val (res, nextStr) = nextStr cr chrl [] in splitAll cr res (implode nextStr::acc) end;
  in
    splitAll cr (explode s) []
  end;

exception NotFoundException;

fun get_suffix_after_match str1 str2 =
  let
    fun get_suffix_after_match_list flag ls1 ls2 =
      case (ls1,ls2) of
      ([], _) =>  if flag then ls2 else raise NotFoundException
      | (_, []) => raise NotFoundException
      | (c1::ls1, c2::ls2) =>
        if (c1 = c2) then
          get_suffix_after_match_list true ls1 ls2
        else if flag then
          raise NotFoundException
        else get_suffix_after_match_list false (c1::ls1) ls2
  in
    implode (get_suffix_after_match_list false (explode str1) (explode str2))
  end;

fun get_prefix_before_match str1 str2 =
  let
    fun get_prefix_before_match_akk str1 str2 akk =
      if (String.isPrefix str1 str2) then implode (List.rev akk)
      else
        if (str2 = "") then raise NotFoundException
        else get_prefix_before_match_akk str1 (implode (tl (explode str2))) (hd(explode str2)::akk);
  in
    get_prefix_before_match_akk str1 str2 []
  end;

fun list_replace n x l =
  if (n = 0)
  then
    case l of
    [] => []
    | y::l' => x::l'
  else
    case l of
    [] => []
    | y :: l' => y :: (list_replace (n-1) x l');

fun matchRBrack [] = NONE |
  matchRBrack (s::sl) =
    if (String.isPrefix "(" s)
    then
      if (String.isSuffix ")" s)
      then case matchRBrack sl of
        NONE => NONE
      | SOME (sNew, rs) => SOME (s ^ sNew, rs)
      else
        case matchRBrack sl of
          NONE => NONE
        | SOME (sNew1, rs1) =>
          case matchRBrack rs1 of
            NONE => NONE
          | SOME (sNew2, rs2) =>
            SOME (s^ sNew1 ^ sNew2, rs2)
    else if (String.isSuffix ")" s)
    then SOME (s, sl)
    else
      case matchRBrack sl of
        NONE => NONE
      | SOME (sNew, rs) =>
        SOME (s ^ sNew, rs);

fun rejoin_pars [] = [] |
  rejoin_pars (s::sl) =
    if (String.isPrefix "(" s)
    then
      if (String.isSuffix ")" s)
      then s :: rejoin_pars sl
      else
        let val (sNew, rs) = valOf (matchRBrack sl) in
          (s ^ sNew) :: rejoin_pars rs
        end
    else s :: (rejoin_pars sl);

  fun stripSpaces s =
    case s of
     [] => ""
    | c::cs => if (c = #" ")
              then stripSpaces cs
              else implode (c::cs);

  fun preprocess s =
    let
      val strs = string_split s #")"
      val remainder =
        if (String.isPrefix "(*#loc" (stripSpaces (explode (hd (strs)))))
        then tl (strs)
        else strs
      val noBreaks =
        List.map (String.translate
          (fn c => if c = #"\n" then " " else if Char.isCntrl c then "" else implode [c]))
          remainder
      val res =
        if String.isPrefix " " (hd noBreaks)
        then String.concatWith ")" (stripSpaces (explode (hd noBreaks)) :: (tl noBreaks))
        else String.concatWith ")"noBreaks
      in
        if (String.isSuffix ")" s)
        then (res^")")
        else res
    end;

  fun listStrip ls1 ls2 =
    case (ls1, ls2) of
    ([], _) => ls2
    | (i1::ls1, i2::ls2) => if (i1 = i2) then listStrip ls1 ls2 else []
    | (_,_) => [];

  fun removeTrailing str fullStr =
    implode (rev (listStrip (List.rev (explode str)) (List.rev (explode fullStr))));

end
