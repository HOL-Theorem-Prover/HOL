structure tailbuffer :> tailbuffer =
struct

type t = {v : string Vector.vector, i: int, full : bool, s : string, max : int,
          patterns : (string * bool) list}

fun new {numlines,patterns} : t =
  if numlines < 1 then raise Fail "tailbuffer.new: numlines <= 0"
  else
    let
      val v = Vector.tabulate(numlines, (fn _ => ""))
    in
      {v = v, i = 0, full = false, s = "", max = numlines,
       patterns = List.map (fn p => (p, false)) patterns}
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

fun fill1 (news, {v,i,full,s,max,patterns} : t) : t =
  let
    val newline = s^news
  in
    {v = Vector.update(v,i,newline),
     i = (i + 1) mod max,
     full = full orelse i + 1 = max,
     s = "",
     max = max,
     patterns =
       List.map (fn pat as (_, true) => pat
                  | (p, _) => (p, String.isSubstring p newline)) patterns}
  end

fun add_incomplete_line l ({v,i,full,s,max,patterns}:t) : t =
  {v = v, i = i, full = full, max = max, patterns = patterns, s = s ^ l}

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

fun last_line ({v,i,full,max,...} : t) =
  if not full andalso i = 0 then NONE
  else SOME (Vector.sub(v,(i - 1) mod max))

fun output ({v,i,full,s,max,patterns,...}:t) =
  let
    val patterns_seen = List.map #1 (List.filter #2 patterns)
  in
    if not full andalso i = 0 then
      { fulllines = [], lastpartial = s, patterns_seen = patterns_seen }
    else
      let
        val limit = if full then i else 0
        fun recurse acc j =
          if j = limit then
            Vector.sub(v, j)::acc
          else recurse (Vector.sub(v,j)::acc) ((j - 1) mod max)
      in
        { fulllines = recurse [] ((i - 1) mod max), lastpartial = s,
          patterns_seen = patterns_seen }
      end
  end

end
