structure AncestryData :> AncestryData =
struct

open Theory Lib Feedback
datatype 'd action = Visit of string | Apply of 'd list

type ('delta,'value) adata_info = {
  tag : string, initial_values : (string * 'value) list,
  apply_delta : 'delta -> 'value -> 'value
}

val ERR = mk_HOL_ERR "AncestryData"

fun smem s e = HOLset.member(s,e)
fun sadd e s = HOLset.add(s,e)

val tdebug = get_tracefn "Theory.debug"

fun DPRINT s = if tdebug() > 0 then print s else ()

fun ancestry parents {thyname} =
    ImplicitGraph.bfs parents String.compare (fn _ => sadd) thyname
                      (HOLset.empty String.compare)

type ('d,'v) info =
     {get_deltas : {thyname: string} -> 'd list,
      dblookup : {thyname : string} -> 'v,
      apply_delta : 'd -> 'v -> 'v, tag : string,
      parents : {thyname : string} -> string list}

fun merge_into (info:('d,'v)info) (thyname, (acc_v, visited)) =
    let
      val {parents,get_deltas,apply_delta,...} = info
      fun recurse (A, aset) worklist =
          case worklist of
              [] => (A, aset)
            | Visit thy :: rest =>
              let
                val ps0 = parents {thyname = thy}
                val ps = List.filter (not o smem aset) ps0
                val deltas = get_deltas {thyname = thy}
              in
                recurse (A, sadd thy aset)
                        (map Visit ps @ (Apply deltas :: rest))
              end
            | Apply ds :: rest =>
              recurse (rev_itlist apply_delta ds A, aset) rest
    in
      recurse (acc_v, visited) [Visit thyname]
    end

fun merge (info : ('d,'v) info) thys : 'v =
    let
      val _ = DPRINT ("Calling " ^ #tag info ^ ":merge[" ^
                      String.concatWith ", " thys ^ "]")
    in
      case thys of
          [] => raise mk_HOL_ERR "ThyDeltaMerge" "merge" "Empty ancestor list"
        | h::t =>
          let
            val v0 = #dblookup info {thyname = h}
            fun par_g s = #parents info {thyname = s}
          in
            #1 (List.foldl (merge_into info) (v0, ancestry par_g {thyname=h}) t)
          end
    end

fun parent_onload extras {thyname,data = data_opt} =
    let
      open ThyDataSexp
      val {tag,apply_delta_hook,delta_side_effects,apply_delta,get_deltas,
           value_table} =
          extras
    in
      if thyname = "min" then ()
      else
        let
          val v0 =
              case data_opt of
                  NONE =>
                  let
                    val ps = Theory.parents thyname
                    val _ = DPRINT (tag ^ ":onload(" ^ thyname ^
                                    ",NONE)\n with " ^
                                    "parents = [" ^
                                    String.concatWith ", " ps ^ "]\n")
                  in
                    !apply_delta_hook ps
                  end
                | SOME data => (
                  case list_decode string_decode data of
                      NONE => raise ERR "AncestryData"
                                    ("make("^tag^") got bad ancestor sexp")
                    | SOME sl =>
                      let
                        val _ = DPRINT (tag ^ ":onload(" ^ thyname ^
                                        ",\nSOME [" ^
                                        String.concatWith ", " sl ^ "])\n")
                      in
                        !apply_delta_hook sl
                      end
                )
          val uds = get_deltas {thyname = thyname}
          val _ = List.app delta_side_effects uds
          val v = rev_itlist apply_delta uds v0
        in
          value_table := Symtab.update (thyname,v) (!value_table)
        end
    end



fun make {info : ('delta,'value)adata_info, get_deltas, delta_side_effects} =
    let
      open ThyDataSexp
      val {tag, apply_delta, initial_values, ...} = info
      val value_table =
          ref (itlist Symtab.update initial_values Symtab.empty)
      fun valueDB {thyname} =
          case Symtab.lookup (!value_table) thyname of
              NONE => raise ERR "AncestryData"
                            ("valueDB(" ^ tag ^
                             "): no such theory in ancestry: " ^ thyname)
            | SOME v => v

      val apply_delta_hook =
          ref (fn (ps : string list) =>
                  raise Fail "AncestryData: calling default hook")
      val parent_extras =
          {tag = tag, apply_delta_hook = apply_delta_hook,
           delta_side_effects = delta_side_effects,
           apply_delta = apply_delta, get_deltas = get_deltas,
           value_table = value_table}

      val {export = parent_export,
           segment_data = parent_segment_data, ...} =
          ThyDataSexp.new {
            thydataty = tag, merge = fn {old,new} => new,
            load = parent_onload parent_extras, other_tds = fn (s,_) => SOME s
          }
      fun parents thyname =
          case parent_segment_data thyname of
              NONE => Theory.parents (#thyname thyname)
            | SOME t => valOf (list_decode string_decode t)
      val info = {get_deltas = get_deltas, tag = tag,
                  dblookup = valueDB,
                  apply_delta = apply_delta,
                  parents = parents}
      val _ = apply_delta_hook := merge info
      fun set_ancestry sl =
          let
            val _ = parent_export (List $ map String sl)
            val v = merge info sl
          in
            value_table := Symtab.update (current_theory(), v) (!value_table);
            v
          end
    in
      {merge = merge info, DB = valueDB,
       parents = parents, set_parents = set_ancestry}
    end

(*
fun fullmake {info : ('delta,'value) adata_info, sexps, globinfo} =
    let
      val {apply_to_global,initial_value} = globinfo
      val {initial_values, ...} = info
      val value_ref = ref initial_value
      val value_table =
          ref (itlist Symtab.update initial_values Symtab.empty)
*)


end (* struct *)
