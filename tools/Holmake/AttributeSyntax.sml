structure AttributeSyntax :> AttributeSyntax =
struct

infix |>
fun x |> f = f x
fun mlquote s = "\"" ^ String.toString s ^ "\""

fun bslash_escape c =
    "\\" ^ StringCvt.padLeft #"0" 3 (Int.toString (Char.ord c))

fun bslash_escape_s s = bslash_escape (String.sub(s, 0))

val mk_strsafe =
    String.translate (fn c => if Char.isPrint c then str c else
                              bslash_escape c)

fun kill_enveloping_space s =
      s |> Substring.full
        |> Substring.dropl Char.isSpace
        |> Substring.dropr Char.isSpace
        |> Substring.string

(* if each attr from attrs is of form attr=...|...|... then return an alist
   of type (string * string list) list
*)
fun key_vallist1 attr =
    case String.fields (fn c => c = #"=") attr of
        [] => raise Fail "String.fields can't return an empty list"
      | [key] => (kill_enveloping_space key, [])
      | key::vals::_ => (kill_enveloping_space key,
                         String.tokens Char.isSpace vals)
val key_vallist = map key_vallist1

fun mk_tacmodifier1 (k,vals) =
    case k of
        "exclude_simps" => "(simpLib.remove_simps [" ^
                           String.concatWith "," (map mlquote vals) ^ "])"
      | "exclude_frags" => "(simpLib.remove_ssfrags [" ^
                           String.concatWith "," (map mlquote vals) ^ "])"
      | _ => k
local
val bpwsu = "BasicProvers.with_simpset_updates "
in
fun mk_tacmodifier_string attrs =
    case attrs of
        [] => ""
      | [tm] => bpwsu ^ mk_tacmodifier1 tm
      | _ => bpwsu ^ "(" ^
             String.concatWith "o" (map mk_tacmodifier1 attrs) ^ ")"
end
fun dest_name_attrs s =
    let val ss = Substring.full s
        val (nmss, attrs) =
            if Substring.sub(ss, 0) = #"\"" then
              let val ss' = Substring.slice(ss, 1, NONE)
                  val (nm,rest) = Substring.position "\"" ss'
              in
                (nm, Substring.slice(rest,1,NONE))
              end
            else
              Substring.position "[" ss
        val nms = nmss |> Substring.string |> mk_strsafe
    in
      (nms,
       if Substring.isEmpty attrs then []
       else
         Substring.slice(attrs, 1, SOME (Substring.size attrs - 2))
                        |> Substring.string
                        |> String.fields (fn c => c = #",")
                        |> map kill_enveloping_space)
    end

fun dest_ml_thm_binding s =
    let
      (* s matches {keyword}{ws}+{ident}[attrs]
         ident is either a standard ML identifier, or something in double quotes
         NB: If it's in double quotes, the thing in quotes might include square
         brackets!

         returns the ident, the original string corresponding to the string +
         attributes, and the attributes as a separate list of strings
      *)
      val (kwordss, restss) =
          s |> Substring.full |> Substring.splitl Char.isAlpha
      val ss = restss |> Substring.dropl Char.isSpace
      val nao = Substring.string ss
      val (nms, attrs) = dest_name_attrs nao
    in
      {keyword = Substring.string kwordss, name = nms, name_attr_original = nao,
       attributes = attrs}
    end

end
