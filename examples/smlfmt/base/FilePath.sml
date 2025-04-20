(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure FilePath :>
sig
  type filepath
  type t = filepath

  exception InvalidPathString of string

  (** path/to/file  ==>  ["path", "to", "file"] *)
  val toFields: filepath -> string list
  val fromFields: string list -> filepath

  val dirname: filepath -> filepath
  val basename: filepath -> filepath

  (** Eliminates redundant fields, e.g.
    *    ./path/./to/the/../file    ==>    path/to/file
    *)
  val normalize: filepath -> filepath

  (** Append filepaths. Doesn't normalize! *)
  val join: filepath * filepath -> filepath

  val fromUnixPath: string -> filepath
  val toUnixPath: filepath -> string
  val toHostPath: filepath -> string

  val isAbsolute: filepath -> bool

  val sameFile: filepath * filepath -> bool
end =
struct

  (** Path fields in reverse order *)
  type filepath = string list
  type t = filepath

  exception InvalidPathString of string
  exception EmptyPath

  fun toFields path = List.rev path
  fun fromFields fields =
    case fields of
      [] => raise EmptyPath
    | _ => List.rev fields

  fun dirname (fields: filepath) =
    case fields of
      [] => raise Fail "FilePath bug (dirname: empty path)"
    | [_] => ["."]
    | _ :: rest => rest

  fun basename (fields: filepath) =
    case fields of
      [] => raise Fail "FilePath bug (basename: empty path)"
    | name :: _ => [name]

  fun normalize (fields: filepath) =
    let
      fun addParent (".", fields) = fields
        | addParent ("..", fields) = ".." :: fields
        | addParent (_, ".." :: fields) = fields
        | addParent (parent, fields) = parent :: fields
    in
      List.rev (List.foldl addParent (basename fields) (dirname fields))
    end

  fun sameFile (fp1, fp2) =
    Util.equalLists op= (normalize fp1, normalize fp2)

  fun join (fields1, fields2) = fields2 @ fields1

  fun fromUnixPath s =
    if String.size s = 0 then raise InvalidPathString s
    else List.rev (String.fields (fn c => c = #"/") s)

  fun toUnixPath s =
    String.concatWith "/" (List.rev s)

  (** The first field of an (absolute) Unix path is always the empty string.
    * So look at the last, because we represent path fields in reverse order.
    *)
  fun isAbsolute path = List.last path = ""

  fun toHostPath path =
    OS.Path.fromUnixPath (toUnixPath path)
end
