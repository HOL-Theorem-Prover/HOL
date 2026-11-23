(* ========================================================================= *)
(* FILE          : hhFactIndex.sml                                           *)
(* DESCRIPTION   : Lookup of facts by name                                   *)
(* AUTHOR        : Lukasz Czajka                                             *)
(* ========================================================================= *)

structure hhFactIndex :> hhFactIndex =
struct

open aiLib

type 'a index =
  {name_of : 'a -> string, facts : 'a list, size : int,
   positions : (string, (int * 'a) list) Redblackmap.dict Susp.susp}

fun create name_of facts =
  let
    fun index _ table [] = table
      | index position table (fact :: rest) =
          let
            val name = name_of fact
            val entries = Option.getOpt (Redblackmap.peek (table, name), [])
            val table' = dadd name ((position, fact) :: entries) table
          in
            index (position + 1) table' rest
          end
  in
    {name_of = name_of, facts = facts, size = length facts,
     positions = Susp.delay (fn () => index 0 (dempty String.compare) facts)}
  end

fun select_sparse ({size, positions, ...} : 'a index) wanted =
  let val count = dlength wanted in
    if count = 0 then SOME []
    else if count < size div 8 then
      let
        val index = Susp.force positions
        val entries = dfoldl (fn (name, (), entries) =>
          case Redblackmap.peek (index, name) of
              SOME matches => matches @ entries
            | NONE => entries) [] wanted
      in
        SOME (map #2 (Listsort.sort (fst_compare Int.compare) entries))
      end
    else NONE
  end

fun select (index as {name_of, facts, ...} : 'a index) wanted =
  case select_sparse index wanted of
      SOME facts => facts
    | NONE => List.filter (fn fact => dmem (name_of fact) wanted) facts

end
