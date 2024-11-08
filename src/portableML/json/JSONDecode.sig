signature JSONDecode =
sig

    (* exceptions used as errors; note that most of these come from the
     * JSONUtil module.  The standard practice is to raise `JSONError(ex, v)`
     * for an error on JSON value `v`, where `ex` specifies more detail about
     * the actual error.
     *)
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

    val exnMessage : exn -> string

    type 'a decoder

    val decode : 'a decoder -> JSON.value -> 'a
    val decodeString : 'a decoder -> string -> 'a
    val decodeFile : 'a decoder -> string -> 'a

    val bool : bool decoder
    val int : int decoder
    val intInf : IntInf.int decoder
    val number : Real.real decoder
    val string : string decoder

    val null : 'a -> 'a decoder

    (* returns the raw JSON value without further decoding *)
    val raw : JSON.value decoder

    (* decides a JSON OBJECT into a list of labeled JSON values *)
    val rawObject : (string * JSON.value) list decoder

    (* decides a JSON ARRAY into a vector of JSON values *)
    val rawArray : JSON.value vector decoder

    (* returns a decoder that maps the JSON `null` value to `NONE` and otherwise
     * returns `SOME v`, where `v` is the result of decoding the value using
     * the supplied decoder.
     *)
    val nullable : 'a decoder -> 'a option decoder

    (* returns a decoder that attempts to decode a value and returns `NONE`
     * on failure (instead of an error result).
     *)
    val try : 'a decoder -> 'a option decoder

    (* sequence decoders using "continuation-passing" style; for example
     *
     *  seq (field "x" number)
     *      (succeed (fn x => x*x))
     *)
    val seq : 'a decoder -> ('a -> 'b) decoder -> 'b decoder

    (* `field key d` returns a decoder that decodes the specified object field
     * using the decoder `d`.
     *)
    val field : string -> 'a decoder -> 'a decoder

    (* decode a required field *)
    val reqField : string -> 'a decoder -> ('a -> 'b) decoder -> 'b decoder

    (* decode an optional field *)
    val optField : string -> 'a decoder -> ('a option -> 'b) decoder ->
                   'b decoder

    (* decode an optional field that has a default value *)
    val dfltField : string -> 'a decoder -> 'a -> ('a -> 'b) decoder ->
                    'b decoder

    (* decodes a JSON ARRAY into a list of values *)
    val array : 'a decoder -> 'a list decoder

    (* `sub i d` returns a decoder that when given a JSON array, decodes
       the i'th array element.
     *)
    val sub : int -> 'a decoder -> 'a decoder

    (* returns a decoder that decodes the value at the location specified by
     * the path.
     *)
    val at : JSONUtil.path -> 'a decoder -> 'a decoder

    (* `succeed v` returns a decoder that always yields `v` for any
       JSON input *)
    val succeed : 'a -> 'a decoder

    (* `fail msg` returns a decoder that raises `JSONError(Fail msg, jv)` for
     * any JSON input `jv`.
     *)
    val fail : string -> 'a decoder

    val andThen : ('a -> 'b decoder) -> 'a decoder -> 'b decoder

    (* `orElse (d1, d2)` returns a decoder that first trys `d1` and returns its
       result if it succeeds.  If `d1` fails, then it returns the result of
       trying `d2`.
     *)
    val orElse : 'a decoder * 'a decoder -> 'a decoder

    (* `choose [d1, ..., dn]` is equivalent to
     * `orElse(d1, orElse(d2, ..., orElse(dn, fail "no choice") ... ))`
     *)
    val choose : 'a decoder list -> 'a decoder

    val map : ('a -> 'b) -> 'a decoder -> 'b decoder
    val map2 : ('a * 'b -> 'res)
          -> ('a decoder * 'b decoder)
          -> 'res decoder
    val map3 : ('a * 'b * 'c -> 'res)
          -> ('a decoder * 'b decoder * 'c decoder)
          -> 'res decoder
    val map4 : ('a * 'b * 'c * 'd -> 'res)
          -> ('a decoder * 'b decoder * 'c decoder * 'd decoder)
          -> 'res decoder

    (* versions of the map combinators that just apply the identity to the
       tuple *)
    val tuple2 : ('a decoder * 'b decoder) -> ('a * 'b) decoder
    val tuple3 : ('a decoder * 'b decoder * 'c decoder) ->
                 ('a * 'b * 'c) decoder
    val tuple4 : ('a decoder * 'b decoder * 'c decoder * 'd decoder) ->
                 ('a * 'b * 'c * 'd) decoder

    (* a delay combinator for defining recursive decoders *)
    val delay : (unit -> 'a decoder) -> 'a decoder

  end
