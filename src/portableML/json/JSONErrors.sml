(* errors.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * The error exceptions used in JSONDecode and JSONUtil.
 *)

structure JSONErrors :> JSONErrors =
struct

(* exceptions used as errors *)
exception JSONError of exn * JSON.value

(* specific errors that are used as the first argument to `JSONError` *)
exception NotNull
exception NotBool
exception NotInt
exception NotNumber
exception NotString
exception NotObject
exception FieldNotFound of string
exception NotArray
exception ArrayBounds of int
exception ElemNotFound

(* map the above exceptions to a message string; we use `General.exnMessage`
 * for other exceptions.
 *)
fun exnMessage (JSONError(exn, v)) =
    let
      fun v2s (JSON.ARRAY _) = "array"
        | v2s (JSON.BOOL false) = "'false'"
        | v2s (JSON.BOOL true) = "'true'"
        | v2s (JSON.FLOAT _) = "number"
        | v2s (JSON.INT _) = "number"
        | v2s JSON.NULL = "'null'"
        | v2s (JSON.OBJECT _) = "object"
        | v2s (JSON.STRING _) = "string"
    in
      case exn of
          Fail msg => String.concat["Failure: ", msg]
        | Overflow => "integer too large"
        | NotNull => String.concat[
                      "expected 'null', but found ", v2s v
                    ]
        | NotBool => String.concat[
                      "expected boolean, but found ", v2s v
                    ]
        | NotInt => (case v
                      of JSON.FLOAT _ => "expected integer, but found \
                                         \floating-point number"
                       | _ => String.concat["expected integer, but found ",
                                            v2s v]
                (* end case *))
        | NotString => String.concat[
                        "expected string, but found ", v2s v
                       ]
        | NotObject => String.concat[
                        "expected object, but found ", v2s v
                       ]
        | FieldNotFound fld => String.concat[
                                "no definition for field \"", fld,
                                "\" in object"
                              ]
        | NotArray => String.concat[
                       "expected array, but found ", v2s v
                      ]
        | ArrayBounds i => String.concat[
                            "index ", Int.toString i, " out of bounds for array"
                           ]
        | ElemNotFound => String.concat[
                           "no matching element found in ", v2s v
                          ]
    | _ => String.concat[
            "Unknown JSON error (", General.exnMessage exn, ") on ", v2s v
           ]
    end
  | exnMessage exn = General.exnMessage exn

fun failure (arg, v) = raise JSONError(Fail arg, v)
fun notNull v = raise JSONError(NotNull, v)
fun notBool v = raise JSONError(NotBool, v)
fun notInt v = raise JSONError(NotInt, v)
fun notNumber v = raise JSONError(NotNumber, v)
fun notString v = raise JSONError(NotString, v)
fun notObject v = raise JSONError(NotObject, v)
fun fieldNotFound (arg, v) = raise JSONError(FieldNotFound arg, v)
fun notArray v = raise JSONError(NotArray, v)
fun arrayBounds (arg, v) = raise JSONError(ArrayBounds arg, v)
fun elemNotFound v = raise JSONError(ElemNotFound, v)

end
