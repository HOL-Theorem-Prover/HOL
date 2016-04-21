structure tailbuffer :> tailbuffer =
struct

type t = {v : string Vector.vector, i: int, full : bool, s : string, max : int}

fun new {numlines} : t =
  if numlines < 1 then raise Fail "tailbuffer.new: numlines <= 0"
  else
    let
      val v = Vector.tabulate(numlines, (fn _ => ""))
    in
      {v = v, i = 0, full = false, s = "", max = numlines}
    end

fun front_last l =
  let
    fun recurse acc l =
      case l of
          [] => NONE
        | [h] => SOME (List.rev acc, h)
        | h::t => recurse (h::acc) t
  in
    recurse [] l
  end

fun fill1 (news, {v,i,full,s,max}) : t =
  {v = Vector.update(v,i,s^news),
   i = (i + 1) mod max,
   full = full orelse i + 1 = max,
   s = "",
   max = max}

fun add_incomplete_line l ({v,i,full,s,max}:t) : t =
  {v = v, i = i, full = full, max = max,
   s = s ^ l}

fun append s' (tb:t) : t =
  let
    val lines = String.fields (fn c => c = #"\n") s'
  in
    case front_last lines of
        NONE => raise Fail "tailbuffer.append: can't happen"
      | SOME(lines, line) =>
        let
          val tb' = List.foldl fill1 tb lines
        in
          add_incomplete_line line tb'
        end
  end

fun output ({v,i,full,s,max,...}:t) =
  if not full andalso i = 0 then ([], s)
  else
    let
      val limit = if full then i else 0
      fun recurse acc j =
        if j = limit then
          Vector.sub(v, j)::acc
        else recurse (Vector.sub(v,j)::acc) ((j - 1) mod max)
    in
      (recurse [] ((i - 1) mod max), s)
    end

end
