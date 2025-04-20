(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure MLtonPathMap :>
sig
  type pathmap = (string * string) list
  type t = pathmap

  val getPathMap: unit -> pathmap
  val fromString: string -> pathmap
  val lookup: pathmap -> string -> string option

  (** Recursively expand a path until convergence. In addition to the
    * final path, returns which keys were used.
    *)
  val expandPath: pathmap
                  -> FilePath.t
                  -> {result: FilePath.t, used: string list}
end =
struct

  type pathmap = (string * string) list
  type t = pathmap

  (** A bit of a hack... *)


  fun fromString str =
    let
      val lines = String.tokens (fn c => c = #"\n") str
      fun parseLine ln =
        case String.tokens Char.isSpace ln of
          [key, value] => SOME (key, value)
        | _ => NONE
    in
      List.mapPartial parseLine lines
    end


  fun getPathMap () =
    let
      val mltonPath =
        case FindInPath.find "mlton" of
          SOME path => FilePath.toHostPath path
        | NONE =>
            ( TextIO.output
                (TextIO.stdErr, "[WARN] could not find 'mlton' in PATH\n")
            ; "mlton"
            )

      val output =
        RunProcess.captureOutput
          {cmdPath = mltonPath, args = ["-show", "path-map"]}
    in
      fromString output
    end
    handle _ => []


  fun lookup pathmap key =
    case pathmap of
      [] => NONE
    | (k, v) :: pathmap' => if key = k then SOME v else lookup pathmap' key


  fun tryExpandField (pathmap: pathmap) (field: string) =
    let
      val n = String.size field
      fun c i = String.sub (field, i)
      fun slice (i, j) =
        String.substring (field, i, j - i)


      fun findNextKeyStart (i: int) =
        if i >= n then
          NONE
        else if i + 1 < n andalso c i = #"$" andalso c (i + 1) = #"(" then
          SOME i
        else
          findNextKeyStart (i + 1)


      fun findNextKeyEnd (i: int) =
        if i >= n then NONE
        else if c i = #")" then SOME (i + 1)
        else findNextKeyEnd (i + 1)


      fun finishLoop (usedKeys, acc) =
        (usedKeys, String.concat (List.rev acc))

      (** Example:
        *   abc$(foo)def$(bar)...
        *                     ^
        *                     i
        *   acc is ["abc", X, "def", Y], but in reverse order,
        *   where X = replacement for foo and similarly Y for bar.
        *)
      fun loop usedKeys acc i =
        if i >= n then
          finishLoop (usedKeys, acc)
        else
          case findNextKeyStart i of
            NONE => finishLoop (usedKeys, slice (i, n) :: acc)
          | SOME j =>
              case findNextKeyEnd (j + 2) of
                NONE => finishLoop (usedKeys, slice (i, n) :: acc)
              | SOME k =>
                  let
                    val prefix = slice (i, j)
                    val key = slice (j + 2, k - 1)
                  in
                    case lookup pathmap key of
                      NONE => loop usedKeys (slice (j, k) :: prefix :: acc) k
                    | SOME v => loop (key :: usedKeys) (v :: prefix :: acc) k
                  end

      val (usedKeys, expanded) = loop [] [] 0
    in
      if List.null usedKeys then NONE else SOME (usedKeys, expanded)
    end


  fun expandPath pathmap path =
    let
      fun expandField field =
        case tryExpandField pathmap field of
          NONE => ([], [field])
        | SOME (usedKeys, field') =>
            let
              val (usedKeys', field'') = expand
                (FilePath.toFields (FilePath.fromUnixPath field'))
            in
              (usedKeys' @ usedKeys, field'')
            end

      and expand (fields: string list) =
        let
          val expanded = List.map expandField fields
        in
          ( List.concat (List.map #1 expanded)
          , List.concat (List.map #2 expanded)
          )
        end

      val (usedKeys, result) = expand (FilePath.toFields path)
    in
      {result = FilePath.fromFields result, used = usedKeys}
    end

(* val expandPath = fn pathmap => fn path =>
  let
    val _ = print ("expanding " ^ FilePath.toUnixPath path ^ "\n")
    val result = expandPath pathmap path
    val _ = print ("result: " ^ FilePath.toUnixPath result ^ "\n")
  in
    result
  end *)

end
