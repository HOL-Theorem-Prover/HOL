structure stringfindreplace :> stringfindreplace =
struct

datatype 'a trie = Nd of 'a option * (char, 'a trie) Binarymap.dict

fun dictOf (Nd(_, d)) = d
fun valueOf (Nd(v,_)) = v

fun empty() = Nd (NONE, Binarymap.mkDict Char.compare)

fun insert (t, s, v) =
  let
    fun recurse t ss =
      let
        val Nd (val0, dict) = t
      in
        case Substring.getc ss of
            NONE => Nd(SOME v, dict)
          | SOME (c, ss') =>
            let
              val subt = case Binarymap.peek(dict, c) of
                             NONE => empty()
                           | SOME t => t
            in
              Nd(val0, Binarymap.insert(dict,c,recurse subt ss'))
            end
      end
  in
    recurse t (Substring.full s)
  end

fun foldl f acc t =
  let
    fun recurse k acc0 t =
      let
        val acc = case valueOf t of
                      NONE => acc0
                    | SOME v => f(k,v,acc0)
      in
        Binarymap.foldl (fn (c,t,a) => recurse (k ^ str c) a t) acc (dictOf t)
      end
  in
    recurse "" acc t
  end

fun final_replacement s imaps =
  case imaps of
      [] => s
    | (i, (repl, numtoremove)) :: rest =>
      let
        val _ = i >= 0 orelse raise Fail "Negative index in alist"
        val resti = i + numtoremove
      in
        String.extract(s,0, SOME i) ^ repl ^
        final_replacement (String.extract(s, resti, NONE))
                          (map (fn (i,v) => (i - resti, v)) rest)
      end

fun foldcheck trie0 s =
  let
    val sz = size s
    fun onestep i done cont k =
      (*
         cont is a map (alist) from indexes into the string to a pair of
         a trie and an optional "best value to date" coupled with the number
         of characters that best value is replacing.  done is similar.
      *)
      if i >= sz then
        let
          fun updcurrent (i, (t, NONE)) = NONE
            | updcurrent (i, (t, SOME v)) = SOME (i, v)
        in
          k (List.revAppend (done, List.mapPartial updcurrent cont))
        end
      else
        let
          val c = String.sub(s,i)
          fun newcellf inv old =
            if inv then old
            else
              case Binarymap.peek(dictOf trie0, c) of
                  NONE => old
                | SOME t =>
                    (i, (t, Option.map (fn v => (v,1)) (valueOf t)))::old
          fun updcells doneA continuingA cells invalidate k =
            case cells of
                [] => k doneA (List.rev (newcellf invalidate continuingA))
              | ((cell as (starti, (t, bestopt)))::rest) =>
                let
                in
                  case Binarymap.peek(dictOf t, c) of
                      NONE =>
                        (case bestopt of
                             NONE => updcells doneA continuingA
                                              rest invalidate k
                           | SOME (v,c) =>
                             updcells ((starti,(v,c)) :: doneA) continuingA
                                      rest invalidate k)
                    | SOME t' =>
                      (case valueOf t' of
                           NONE => updcells
                                     doneA
                                     ((starti,(t',bestopt)) :: continuingA)
                                     rest
                                     invalidate k
                         | SOME v' =>
                           let
                             val cnt = i - starti + 1
                           in
                             updcells
                               doneA
                               ((starti, (t', SOME (v',cnt))) :: continuingA)
                               (List.filter (fn (j, _) => j > i) rest)
                               true
                               k
                           end)
                end
        in
          updcells done [] cont false
                   (fn done => fn cont => onestep (i + 1) done cont k)
        end
  in
    onestep 0 [] [] (fn m => final_replacement s m)
  end

fun subst theta =
  let
    fun foldthis ({redex,residue}, t) =
      if size redex <> 0 then
        insert(t, redex, residue)
      else raise Fail "stringfindreplace.subst : redex is empty string"
    val t = List.foldl foldthis (empty()) theta
  in
    foldcheck t
  end

end
