(* json-decode.sml
 *
 * COPYRIGHT (c) 2023 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *)

structure JSONDecode :> JSONDecode =
struct

structure U = JSONUtil

(* import the error exceptions and exnMessage *)
open JSONErrors

datatype value = datatype JSON.value

datatype 'a decoder = D of value -> 'a

fun decode (D d) jv = d jv

fun decodeString decoder s =
    (decode decoder (JSONParser.parse(JSONParser.openString s)))

fun decodeFile decoder fname =
    (decode decoder (JSONParser.parseFile fname))

fun asBool (BOOL b) = b
  | asBool v = notBool v
val bool = D asBool

fun asInt jv =
    case jv of
        INT n =>
        (Int.fromLarge n handle Overflow => raise (JSONError(Overflow, jv)))
      | _ => notInt jv
val int = D asInt

fun asIntInf (INT n) = n
  | asIntInf v = notInt v
val intInf = D asIntInf

fun asNumber (INT n) = Real.fromLargeInt n
  | asNumber (FLOAT f) = f
  | asNumber v = notNumber v
val number = D asNumber

fun asString (STRING s) = s
  | asString v = notString v
val string = D asString

fun null dflt = D(fn NULL => dflt | jv => notNull jv)

val raw = D(fn jv => jv)

val rawObject = D(fn (OBJECT fields) => fields | jv => notObject jv)

val rawArray = D(fn (ARRAY elems) => Vector.fromList elems
                | jv => notArray jv)

fun nullable (D decoder) = let
  fun decoder' NULL = NONE
    | decoder' jv = SOME(decoder jv)
in
  D decoder'
end

fun array (D elemDecoder) =
    let
      fun decodeList ([], elems) = List.rev elems
        | decodeList (jv::jvs, elems) = decodeList(jvs, elemDecoder jv :: elems)
      fun decoder (ARRAY elems) = decodeList (elems, [])
        | decoder jv = notArray jv
    in
      D decoder
    end

fun try (D d) =
    D(fn jv => (SOME(d jv) handle JSONError _ => NONE | ex => raise ex))

fun seq (D d1) (D d2) = D(fn jv => let
                            val v = d1 jv
                            val k = d2 jv
                          in
                            k v
                          end)

fun field key valueDecoder =
    D(fn jv => (case jv of
                    OBJECT fields =>
                    (case List.find (fn (l, v) => (l = key)) fields of
                         SOME(_, v) => decode valueDecoder v
                       | _ => fieldNotFound(key, jv)
                    (* end case *))
                  | _ => notObject jv
     (* end case *)))

fun reqField key valueDecoder k = seq (field key valueDecoder) k

fun optField key (D valueDecoder) (D objDecoder) = let
  fun objDecoder' optFld jv = (objDecoder jv) optFld
  fun decoder jv = (case U.findField jv key
                     of SOME NULL => objDecoder' NONE jv
                      | SOME jv' => objDecoder' (SOME(valueDecoder jv')) jv
                      | NONE => objDecoder' NONE jv
                   (* end case *))
in
  D decoder
end

fun dfltField key (D valueDecoder) dfltVal (D objDecoder) = let
  fun objDecoder' fld jv = (objDecoder jv) fld
  fun decoder jv = (case U.findField jv key
                     of SOME NULL => objDecoder' dfltVal jv
                      | SOME jv' => objDecoder' (valueDecoder jv') jv
                      | NONE => objDecoder' dfltVal jv
                   (* end case *))
in
  D decoder
end

fun sub i (D d) =
    D(fn jv => (case jv of
                    jv as ARRAY arr =>
                    let
                      fun get (0, item::_) = d item
                        | get (_, []) = arrayBounds(i, jv)
                        | get (i, _::r) = get (i-1, r)
                    in
                      if i < 0 then arrayBounds(i, jv) else get (i, arr)
                    end
                  | _ => notArray jv
                   (* end case *)))

fun at path (D d) = D(fn jv => d (U.get(jv, path)))

fun succeed x = D(fn _ => x)

fun fail msg = D(fn jv => failure(msg, jv))

fun andThen f (D d) = D(fn jv => decode (f (d jv)) jv)

fun orElse (D d1, D d2) =
    (* try the first decoder.  If it fails with a `JSONError` exception, then
     * we try the second.
     *)
    D(fn jv => (d1 jv handle JSONError _ => d2 jv | ex => raise ex))

(* `choose [d1, ..., dn]` is equivalent to
 * `orElse(d1, orElse(d2, ..., orElse(dn, fail "no choice") ... ))`
 *)
fun choose [] = fail "no choice"
  | choose (d::ds) = orElse(d, choose ds)

fun map f (D decoder) = D(fn jv => f (decoder jv))

fun map2 f (D d1, D d2) = D(fn jv => f(d1 jv, d2 jv))
fun map3 f (D d1, D d2, D d3) = D(fn jv => f(d1 jv, d2 jv, d3 jv))
fun map4 f (D d1, D d2, D d3, D d4) = D(fn jv => f(d1 jv, d2 jv, d3 jv, d4 jv))

fun tuple2 (d1, d2) = map2 (fn x => x) (d1, d2)
fun tuple3 (d1, d2, d3) = map3 (fn x => x) (d1, d2, d3)
fun tuple4 (d1, d2, d3, d4) = map4 (fn x => x) (d1, d2, d3, d4)

fun delay dd = andThen dd (succeed ())

end
