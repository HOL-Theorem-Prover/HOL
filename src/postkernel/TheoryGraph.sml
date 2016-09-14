structure TheoryGraph :> TheoryGraph =
struct

open Portable Theory


type thy = {thyname : string}
exception NotFound of thy
val thy_compare : thy * thy -> order =
    inv_img_cmp #thyname String.compare

type thyset = thy HOLset.set

fun toThy s : thy = {thyname = s}
val slist_to_thyset =
  List.foldl (fn (s,acc) => HOLset.add(acc,{thyname = s}))
             (HOLset.empty thy_compare)

type t = (thy,thyset) Binarymap.dict

val empty : t = Binarymap.mkDict thy_compare

fun member G thy =
  case Binarymap.peek(G, thy) of
      NONE => false
    | SOME _ => true

fun parents G thy = Binarymap.find (G, thy)

fun ancestors G thy =
  let
    fun recurse worklist acc =
      case worklist of
          [] => acc
        | thy::rest =>
          let
            val ps_set = parents G thy
          in
            recurse (HOLset.listItems ps_set @ rest)
                    (HOLset.union(acc,ps_set))
          end
  in
    recurse [thy] (HOLset.empty thy_compare)
  end

(* GREATER implies that thy1 is a descendent of thy2 *)
fun ancestor_compare G (thy1,thy2) =
  if thy1 = thy2 then SOME EQUAL
  else
    let
      val ancs1 = ancestors G thy1
    in
      if HOLset.member(ancs1,thy2) then SOME GREATER
      else
        let
          val ancs2 = ancestors G thy2
        in
          if HOLset.member(ancs2, thy1) then SOME LESS
          else NONE
        end
    end

fun eliminate_redundant_ancestors G thylist =
  let
    fun do1 thy rest acclist all_incomparable =
      case rest of
          [] => (thy::acclist, all_incomparable)
        | thy'::rest' =>
          case ancestor_compare G (thy, thy') of
              NONE => do1 thy rest' (thy'::acclist) all_incomparable
            | SOME LESS => (acclist @ rest, false)
            | SOME EQUAL => (acclist @ rest, false)
            | SOME GREATER => do1 thy rest' acclist false
    fun recurse thylist =
      case thylist of
          [] => []
        | th::rest =>
          let
            val (rest', all_incomparable) = do1 th rest [] true
          in
            if all_incomparable then hd rest' :: recurse (tl rest')
            else recurse rest'
          end
  in
    recurse thylist
  end

fun insert (newthy, parents) G =
  case List.find (not o member G) parents of
      SOME p => raise NotFound p
    | NONE =>
      let
        val ps' = eliminate_redundant_ancestors G parents
      in
        Binarymap.insert(G, newthy, HOLset.fromList thy_compare ps')
      end

fun current () =
  let
    fun recurse g thy_s =
      let
        val ps = Theory.parents thy_s
        val g = List.foldl (fn (p,g) => recurse g p) g ps
      in
        insert(toThy thy_s, map toThy ps) g
      end
  in
    recurse empty (current_theory())
  end



end
