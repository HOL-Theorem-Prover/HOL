signature JSONErrors =
sig

  val failure : string * JSON.value -> 'a
  val notNull : JSON.value -> 'a
  val notBool : JSON.value -> 'a
  val notInt : JSON.value -> 'a
  val notNumber : JSON.value -> 'a
  val notString : JSON.value -> 'a
  val notObject : JSON.value -> 'a
  val fieldNotFound : string * JSON.value -> 'a
  val notArray : JSON.value -> 'a
  val arrayBounds : int * JSON.value -> 'a
  val elemNotFound : JSON.value -> 'a

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

  val exnMessage : exn -> string

end
