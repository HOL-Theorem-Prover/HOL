structure TexTokenMap :> TexTokenMap =
struct

  open HolKernel
  type deltas = {hol:string,TeX:string*int} list

  val read_deltas = let
    open Coding
    infix >*
  in
    many (map (fn (s1,(s2,i)) => {hol=s1,TeX=(s2,i)})
              (StringData.reader >* (StringData.reader >* IntData.reader)))
  end

  fun write_deltas dlist = let
    open Coding
    val enc = StringData.encode
    val ienc = IntData.encode
    fun recurse acc dlist =
      case dlist of
        [] => String.concat (List.rev acc)
      | {hol,TeX=(s,i)}::t => recurse (ienc i :: enc s :: enc hol :: acc) t
  in
    recurse [] dlist
  end
  val tyname = "TexTokenMap"

  fun pr_delta {hol,TeX = (t,i)} =
      "{hol = " ^ hol ^ ", TeX = (" ^ t ^ ", " ^ Int.toString i ^ "}"

  infix oo
  fun (f oo g) = Option.mapPartial f o g

  val (mk,dest) = Theory.LoadableThyData.new {
        thydataty = tyname, merge = op@, terms = K [], strings = K [],
        read = K (Coding.lift read_deltas oo HOLsexp.string_decode),
        pp = fn dl => "[" ^
                      String.concatWith ", " (map pr_delta dl) ^
                      "]",
        write = K (HOLsexp.String o write_deltas)
      }


  val tokmap = ref (Binarymap.mkDict String.compare)
  fun the_map() = !tokmap

  fun temp_TeX_notation0 src thy {hol,TeX} =
      case Binarymap.peek (!tokmap, hol) of
        NONE => tokmap := Binarymap.insert(!tokmap,hol,{thy = thy,info = TeX})
      | SOME {thy = oldthy, info = oldt} => let
          fun ttoString (t,i) = "(\"" ^ String.toString t ^ "\", "^
                                Int.toString i ^ ")"
        in
          if oldt <> TeX then
            HOL_WARNING "TexTokenMap" "TeX_notation"
                        (src^" overrides \""^
                         String.toString hol^"\" (was "^
                         ttoString oldt^", from "^oldthy^"); now \""^
                         ttoString TeX^"\"")
          else ();
          tokmap := Binarymap.insert(!tokmap,hol,{thy = thy,info = TeX})
        end

  val temp_TeX_notation =
      temp_TeX_notation0 "TeX_notation call" (current_theory())

  fun TeX_notation record = let
  in
    temp_TeX_notation record;
    Theory.LoadableThyData.write_data_update {thydataty = tyname,
                                              data = mk [record]}
  end


  fun onload thyname = let
    open Theory
  in
    case LoadableThyData.segment_data {thy = thyname, thydataty = tyname} of
      NONE => ()
    | SOME t => let
        open Feedback
        val deltas = valOf (dest t)
            handle Option => (HOL_WARNING "TexTokenMap" "onload"
                                          ("Data for theory "^thyname^
                                           " appears corrupted.");
                              [])
      in
        List.app (temp_TeX_notation0 ("Theory "^thyname) thyname) deltas
      end
  end

  val _ = map onload (ancestry "-")

  val _ = Theory.register_hook
          ("TexTokenMap.onload",
           fn TheoryDelta.TheoryLoaded s => onload s
            | _ => ())


end (* struct *)
