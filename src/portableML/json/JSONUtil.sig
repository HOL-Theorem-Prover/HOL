signature JSONUtil =
sig

    (* exceptions used as errors; note that most of these come from the
     * JSONUtil module.  The standard practice is to raise `JSONError(ex, v)`
     * for an error on JSON value `v`, where `ex` specifies more detail about
     * the actual error.
     *)
    exception JSONError of exn * JSON.value

    (* exceptions for conversion functions *)
    exception NotBool
    exception NotInt
    exception NotNumber
    exception NotString

    (* exception that is raised when trying to process a non-object
       value as an object *)
    exception NotObject

    (* exception that is raised when the given field is not found in an
       object *)
    exception FieldNotFound of string

    (* exception that is raised when trying to process a non-array value as an
       array *)
    exception NotArray

    (* exception that is raised when access to an array value is out
       of bounds *)
    exception ArrayBounds of int

    (* exception that is raised when a `FIND` edge does not match any array
       element *)
    exception ElemNotFound

    (* map the above exceptions to a message string; we use General.exnMessage
     * for other exceptions.
     *)
    val exnMessage : exn -> string

    (* conversion functions for atomic values.  These raise the JSONError
       exception wrapped around the corresponding "NotXXX" exceptions when
       their argument has the wrong shape.  Also note that asNumber will
       accept both integers and floats and asInt may raise
       `JSONError(Overflow, ...)` if the number is too large.
     *)
    val asBool : JSON.value -> bool
    val asInt : JSON.value -> Int.int
    val asIntInf : JSON.value -> IntInf.int
    val asNumber : JSON.value -> Real.real
    val asString : JSON.value -> string

    (* find a field in an object; this function raises the NotObject exception
       when the supplied value is not an object.
     *)
    val findField : JSON.value -> string -> JSON.value option

    (* lookup a field in an object; this function raises the NotObject exception
       when the supplied value is not an object and raises FieldNotFound if the
       value is an object, but does not have the specified field.
     *)
    val lookupField : JSON.value -> string -> JSON.value

    (* does a JSON object have a given field?  This function returns false
       if called on a non-object value.
     *)
    val hasField : string -> JSON.value -> bool

    (* does the specified field of an object satisfy the given predicate?
       This function returns false if called on a non-object value.
     *)
    val testField : string -> (JSON.value -> bool) -> JSON.value -> bool

    (* convert a JSON array to an SML vector *)
    val asArray : JSON.value -> JSON.value vector

    (* map a conversion function over a JSON array to produce a list;
       this function raises the NotArray exception if the second argument is
       not an array.
     *)
    val arrayMap : (JSON.value -> 'a) -> JSON.value -> 'a list

    (* path specification for indexing into JSON values *)
    datatype edge
      = SEL of string   (* select field of object *)
      | SUB of int      (* index into array component *)
      | FIND of JSON.value -> bool
                        (* first array component that satisfies the predicate *)

    type path = edge list

    (* `get (jv, path)` returns the component of `jv` named by `path`.  It
       raises the NotObject, NotArray, FieldNotFound, and ArrayBounds
       exceptions if there is an inconsistency between the path and the
       structure of `jv`.
     *)
    val get : JSON.value * path -> JSON.value

    (* `replace (jv, path, v)` replaces the component of `jv` named by `path`
     * with the value `v`.
     *)
    val replace : JSON.value * path * JSON.value -> JSON.value

    (* `insert (jv, path, lab, v)` inserts `lab : v` into the object named by
       `path` in `jv`
     *)
    val insert : JSON.value * path * string * JSON.value -> JSON.value

    (* `append (jv, path, vs)` appends the list of values `vs` onto the array
       named by `path` in `jv`
     *)
    val append : JSON.value * path * JSON.value list -> JSON.value

  end
