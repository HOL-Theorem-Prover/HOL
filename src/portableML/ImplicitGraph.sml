structure ImplicitGraph :> ImplicitGraph =
struct

type 'a graph = 'a -> 'a list

fun smem s e = HOLset.member(s,e)
fun sadd e s = HOLset.add(s,e)

fun dfs g cmp fold start A0 =
    let
      fun recurse seen to_visit A =
          case to_visit of
              [] => A
            | (v,d)::vs =>
              if smem seen v then recurse seen vs A
              else recurse (sadd v seen)
                           (map (fn v => (v,d+1)) (g v) @ vs)
                           (fold d v A)
    in
      recurse (HOLset.empty cmp) [(start,0)] A0
    end

fun bfs g cmp fold start A0 =
    let
      fun recurse seen to_visit A =
          case to_visit of
              [] => A
            | (v,d)::vs =>
              if smem seen v then recurse seen vs A
              else recurse (sadd v seen)
                           (vs @ map (fn v => (v,d+1)) (g v))
                           (fold d v A)
    in
      recurse (HOLset.empty cmp) [(start,0)] A0
    end

fun limdfs g cmp fold max_depth start A0 =
    let
      fun recurse seen to_visit A =
          case to_visit of
              [] => A
            | (v,d) :: vs =>
              if d > max_depth orelse smem seen v then recurse seen vs A
              else recurse (sadd v seen)
                           (map (fn v => (v,d+1)) (g v) @ vs)
                           (fold d v A)
    in
      recurse (HOLset.empty cmp) [(start,0)] A0
    end

fun limbfs g cmp fold max_depth start A0 =
    let
      fun recurse seen to_visit A =
          case to_visit of
              [] => A
            | (v,d) :: vs =>
              if d > max_depth orelse smem seen v then recurse seen vs A
              else recurse (sadd v seen)
                           (vs @ map (fn v => (v,d+1)) (g v))
                           (fold d v A)
    in
      recurse (HOLset.empty cmp) [(start,0)] A0
    end

end (* struct *)
