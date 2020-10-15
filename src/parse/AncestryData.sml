structure AncestryData :> AncestryData =
struct

open Theory Lib Feedback
datatype 'd action = Visit of string | Apply of 'd

type ('delta,'value) adata_info = {
  tag : string, initial_values : (string * 'value) list,
  get_delta : {thyname : string} -> 'delta,
  apply_delta : 'delta -> 'value -> 'value,
  delta_side_effects : 'delta -> unit
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
     {get_delta : {thyname: string} -> 'd,
      dblookup : {thyname : string} -> 'v,
      apply_delta : 'd -> 'v -> 'v,
      parents : {thyname : string} -> string list}

fun merge_into (info:('d,'v)info) (thyname, (acc_v, visited)) =
    let
      val {parents,get_delta,apply_delta,...} = info
      fun recurse (A, aset) worklist =
          case worklist of
              [] => (A, aset)
            | Visit thy :: rest =>
              let
                val ps0 = parents {thyname = thy}
                val ps = List.filter (not o smem aset) ps0
                val delta = get_delta {thyname = thy}
              in
                recurse (A, sadd thy aset)
                        (map Visit ps @ (Apply delta :: rest))
              end
            | Apply d :: rest => recurse (apply_delta d A, aset) rest
    in
      recurse (acc_v, visited) [Visit thyname]
    end

fun merge (info : ('d,'v) info) thys : 'v =
    case thys of
        [] => raise mk_HOL_ERR "ThyDeltaMerge" "merge" "Empty ancestor list"
      | h::t =>
        let
          val v0 = #dblookup info {thyname = h}
          fun par_g s = #parents info {thyname = s}
        in
          #1 (List.foldl (merge_into info) (v0, ancestry par_g {thyname=h}) t)
        end


fun make (input_arguments : ('delta,'value) adata_info) =
    let
      val {tag, get_delta, apply_delta, ...} = input_arguments
      val {initial_values, delta_side_effects, ...} = input_arguments
      val value_table =
          ref (itlist Symtab.update initial_values Symtab.empty)
      fun valueDB {thyname} =
          case Symtab.lookup (!value_table) thyname of
              NONE => raise ERR "AncestryData"
                            ("valueDB(" ^ tag ^
                             "): no such theory in ancestry: " ^ thyname)
            | SOME v => v

      val parent_table = ref Symtab.empty
      val apply_delta_hook =
          ref (fn (ps : string list) =>
                  raise Fail "AncestryData: calling default hook")
      open ThyDataSexp
      fun onload {thyname,data = data_opt} =
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
                      case dest_list dest_string data of
                          NONE => raise ERR "AncestryData"
                                        ("make("^tag^") got bad ancestor sexp")
                        | SOME sl =>
                          let
                            val _ = DPRINT (tag ^ ":onload(" ^ thyname ^
                                            ",\nSOME [" ^
                                            String.concatWith ", " sl ^ "])\n")
                            val _ = parent_table :=
                                    Symtab.update (thyname,sl) (!parent_table)
                          in
                            !apply_delta_hook sl
                          end
                    )
              val uds = get_delta {thyname = thyname}
              val _ = delta_side_effects uds
              val v = apply_delta uds v0
            in
              value_table := Symtab.update (thyname,v) (!value_table)
            end

      val {export = parent_export, segment_data = parent_segment_data} =
          ThyDataSexp.new {
            thydataty = tag, merge = fn {old,new} => new,
            load = onload, other_tds = fn (s,_) => SOME s
          }
      fun parents thyname =
          case parent_segment_data thyname of
              NONE => Theory.parents (#thyname thyname)
            | SOME t => valOf (dest_list dest_string t)
      val info = {get_delta = get_delta,
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

end (* struct *)
