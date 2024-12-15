(* json-util.sml
 *
 * COPYRIGHT (c) 2017 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * Utility functions for processing the JSON in-memory representation.
 *)

structure JSONUtil :> JSONUtil = struct

    structure J = JSON

    (* import the error exceptions and exnMessage *)
    open JSONErrors

    fun asBool (J.BOOL b) = b
      | asBool v = notBool v

    fun asInt (J.INT n) = Int.fromLarge n
      | asInt v = notInt v

    fun asIntInf (J.INT n) = n
      | asIntInf v = notInt v

    fun asNumber (J.INT n) = Real.fromLargeInt n
      | asNumber (J.FLOAT f) = f
      | asNumber v = notNumber v

    fun asString (J.STRING s) = s
      | asString v = notString v

    fun findField (J.OBJECT fields) = let
          fun find lab = (case List.find (fn (l, v) => (l = lab)) fields
                 of NONE => NONE
                  | SOME(_, v) => SOME v
                (* end case *))
          in
            find
          end
      | findField v = notObject v

    fun lookupField (v as J.OBJECT fields) = let
          fun find lab = (case List.find (fn (l, v) => (l = lab)) fields
                 of NONE => fieldNotFound(lab, v)
                  | SOME(_, v) => v
                (* end case *))
          in
            find
          end
      | lookupField v = notObject v

    fun hasField lab (J.OBJECT fields) =
          List.exists (fn (lab', _) => lab = lab') fields
      | hasField _ _ = false

    fun testField lab pred (J.OBJECT fields) = (
          case List.find (fn (lab', _) => lab = lab') fields
           of SOME(_, v) => pred v
            | NONE => false
          (* end case *))
      | testField _ _ _ = false

    fun asArray (J.ARRAY vs) = Vector.fromList vs
      | asArray v = notArray v

    fun arrayMap f (J.ARRAY vs) = List.map f vs
      | arrayMap f v = notArray v

  (* path specification for indexing into JSON values *)
    datatype edge
      = SEL of string   (* select field of object *)
      | SUB of int      (* index into array component *)
      | FIND of JSON.value -> bool
                        (* first array component that satisfies the predicate *)

    type path = edge list

    fun get (v, []) = v
      | get (v as J.OBJECT fields, SEL lab :: rest) =
          (case List.find (fn (l, v) => (l = lab)) fields
           of NONE => fieldNotFound(lab, v)
            | SOME(_, v) => get (v, rest)
          (* end case *))
      | get (v, SEL _ :: _) = notObject v
      | get (v as J.ARRAY vs, SUB i :: rest) = let
          fun nth ([], _) = arrayBounds(i, v)
            | nth (elem::_, 0) = elem
            | nth (_::r, i) = nth(r, i-1)
          in
            if (i < 0)
              then arrayBounds(i, v)
              else get (nth(vs, i), rest)
          end
      | get (v, SUB _ :: _) = notArray v
      | get (v as J.ARRAY vs, FIND pred :: rest) = (case List.find pred vs
           of NONE => elemNotFound v
            | SOME v => get (v, rest)
          (* end case *))
      | get (v, FIND _ :: _) = notArray v

  (* top-down zipper to support functional editing *)
    datatype zipper
      = ZNIL
      | ZOBJ of {
            prefix : (string * J.value) list,
            label : string,
            child : zipper,
            suffix : (string * J.value) list
          }
      | ZARR of {
            prefix : J.value list,
            child : zipper,
            suffix : J.value list
          }

  (* follow a path into a JSON value while constructing a zipper *)
    fun unzip (v, []) = (ZNIL, v)
      | unzip (v as J.OBJECT fields, SEL lab :: rest) = let
          fun find (_, []) = fieldNotFound(lab, v)
            | find (pre, (l, v)::flds) = if (l = lab)
                then let
                  val (zipper, v) = unzip (v, rest)
                  in
                    (ZOBJ{prefix=pre, label=lab, suffix=flds, child=zipper}, v)
                  end
                else find ((l, v)::pre, flds)
          in
            find ([], fields)
          end
      | unzip (v, SEL _ :: _) = notObject v
      | unzip (v as J.ARRAY vs, SUB i :: rest) = let
          fun sub (_, [], _) = arrayBounds(i, v)
            | sub (prefix, v::vs, 0) = let
                val (zipper, v) = unzip (v, rest)
                in
                  (ZARR{prefix = prefix, child = zipper, suffix = vs}, v)
                end
            | sub (prefix, v::vs, i) = sub (v::prefix, vs, i-1)
          in
            sub ([], vs, i)
          end
      | unzip (v, SUB _ :: _) = notArray v
      | unzip (v as J.ARRAY vs, FIND pred :: rest) = let
          fun find (_, []) = elemNotFound v
            | find (prefix, v::vs) = if pred v
                then let
                  val (zipper, v) = unzip (v, rest)
                  in
                    (ZARR{prefix = prefix, child = zipper, suffix = vs}, v)
                  end
                else find (v::prefix, vs)
          in
            find ([], vs)
          end
      | unzip (v, FIND _ :: _) = notArray v

  (* zip up a zipper *)
    fun zip (zipper, v) = let
          fun zip' ZNIL = v
            | zip' (ZOBJ{prefix, label, suffix, child}) =
                J.OBJECT(List.revAppend(prefix, (label, zip' child)::suffix))
            | zip' (ZARR{prefix, child, suffix}) =
                J.ARRAY(List.revAppend(prefix, zip' child :: suffix))
          in
            zip' zipper
          end

    fun replace (jv, path, v) = zip (#1 (unzip (jv, path)), v)

    fun insert (jv, path, label, v) =
        case unzip (jv, path) of
            (zipper, J.OBJECT fields) =>
              zip (zipper, J.OBJECT((label, v)::fields))
          | (_, v) => notObject v

    fun append (jv, path, vs) =
        case unzip (jv, path) of
            (zipper, J.ARRAY jvs) => zip (zipper, J.ARRAY(jvs @ vs))
          | (_, v) => notArray v

  end
