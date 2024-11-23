(* json.sml
 *
 * COPYRIGHT (c) 2008 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * This is the tree representation of a JSON data as produced/consumed
 * by the tree parser.
 *)

structure JSON =
  struct

    datatype value
      = OBJECT of (string * value) list
      | ARRAY of value list
      | NULL
      | BOOL of bool
      | INT of IntInf.int
      | FLOAT of real
      | STRING of string        (* note that string is assumed to be UTF-8 *)

  end
