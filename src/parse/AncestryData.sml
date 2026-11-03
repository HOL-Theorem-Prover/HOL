structure AncestryData :> AncestryData =
struct

open Theory Lib Feedback
datatype 'd action = Visit of string | Apply of 'd list

type ('delta,'value) adata_info = {
  tag : string, initial_values : (string * 'value) list,
  apply_delta : 'delta -> 'value -> 'value
}

val ERR = mk_HOL_ERR "AncestryData"

val tdebug = get_tracefn "Theory.debug"

fun DPRINT s = if tdebug() > 0 then print ("* " ^s^"\n") else ()

(* theory based topologically sorted ancestry *)
fun tts_ancestry s : string list =
    let val G = SymGraph.make (map (fn s => ((s,()), Theory.parents s))
                                   (ancestry s))
    in
      List.rev (SymGraph.topological_order G)
    end

(* Ancestor sets, each a theory's ancestry (the theory included) as a bit
   vector indexed by numbers given to theories as they are first met.  A
   loaded theory's parents never change, so its set is computed once per
   tag and kept in a context slot.  The current theory's parents can still
   change, so its set is computed afresh on each use, with number 0. *)
type ancestor_memo =
     {next : int, sets : (int * Word8Vector.vector) Symtab.table}
val empty_ancestor_memo = {next = 1, sets = Symtab.empty}

fun bit i = Word8.<< (0w1, Word.fromInt (i mod 8))
fun bits_member bv i =
    i div 8 < Word8Vector.length bv andalso
    Word8.andb (Word8Vector.sub (bv, i div 8), bit i) <> 0w0
fun bits_union (bv1, bv2) =
    let
      fun byte bv j =
          if j < Word8Vector.length bv then Word8Vector.sub (bv, j) else 0w0
    in
      Word8Vector.tabulate
        (Int.max (Word8Vector.length bv1, Word8Vector.length bv2),
         fn j => Word8.orb (byte bv1 j, byte bv2 j))
    end
fun bits_single i =
    Word8Vector.tabulate (i div 8 + 1,
                          fn j => if j = i div 8 then bit i else 0w0)
fun bits_add bv i = bits_union (bv, bits_single i)

fun ancestor_bits (sets : (int * Word8Vector.vector) Symtab.table) n ps =
    foldl (fn (p, bv) => bits_union (bv, #2 (valOf (Symtab.lookup sets p))))
          (bits_single n) ps

(* A parent list may name the theory itself (e.g., after set_parents
   [current_theory()]); that edge adds nothing to its ancestry *)
fun proper_parents parents thy =
    List.filter (fn p => p <> thy) (parents {thyname = thy})

(* Add thy and its ancestors to the memo *)
fun extend_memo parents (thy, memo as {sets, ...} : ancestor_memo) =
    if Symtab.defined sets thy then memo
    else
      let
        val ps = proper_parents parents thy
        val memo' as {next, sets} = foldl (extend_memo parents) memo ps
      in
        if Thm.getCT() = SOME thy then memo'
        else
          {next = next + 1,
           sets = Symtab.update (thy, (next, ancestor_bits sets next ps))
                                sets}
      end

(* A function giving the number and ancestor set of each theory in thys
   and in their ancestries *)
fun ancestor_sets slot parents thys =
    let
      val result = ref Symtab.empty
      fun extend memo =
          let
            val memo' = foldl (extend_memo parents) memo thys
          in
            result := #sets memo'; memo'
          end
      val _ = Context.Data.modify slot extend
      val sets = !result
    in
      fn thy =>
         case Symtab.lookup sets thy of
             SOME e => e
           | NONE => (0, ancestor_bits sets 0 (proper_parents parents thy))
    end

type ('d,'v) info =
     {get_deltas : {thyname: string} -> 'd list,
      dblookup : {thyname : string} -> 'v option,
      apply_delta : 'd -> 'v -> 'v, tag : string,
      parents : {thyname : string} -> string list,
      ancestors : ancestor_memo Context.Data.slot}

fun fpluck _ [] = NONE
  | fpluck f (h::t) = case f h of
                          NONE => Option.map (fn (v,r) => (v,h::r)) (fpluck f t)
                        | SOME v => SOME ((h,v),t)

fun merge (info : ('d,'v) info) thys : 'v option =
    let
      val _ = DPRINT ("Calling " ^ #tag info ^ ":merge[" ^
                      String.concatWith ", " thys ^ "]")
      val {parents,get_deltas,apply_delta,ancestors,...} = info
      val entry = ancestor_sets ancestors parents thys
      fun number thy = #1 (entry thy)
      (* drop the theories that are ancestors of others in the list *)
      fun redundant thy =
          List.exists (fn t => t <> thy andalso
                               bits_member (#2 (entry t)) (number thy))
                      thys
      val thys = List.filter (not o redundant) thys
      fun recurse (A, aset) worklist =
          case worklist of
              [] => SOME A
            | Visit thy :: rest =>
              if bits_member aset (number thy) then recurse (A, aset) rest
              else
                let
                  val ps0 = parents {thyname = thy}
                  val ps = List.filter (not o bits_member aset o number) ps0
                  val deltas = get_deltas {thyname = thy}
                in
                  recurse (A, bits_add aset (number thy))
                          (map Visit ps @ (Apply deltas :: rest))
                end
            | Apply ds :: rest =>
              recurse (rev_itlist apply_delta ds A, aset) rest
    in
      case thys of
          [] => NONE
        | _ => (
          case fpluck (fn thy => #dblookup info {thyname=thy}) thys of
              NONE => NONE
            | SOME ((h,v0),rest) =>
                recurse (v0, #2 (entry h)) (map Visit rest)
        )
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
          val v0_opt =
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
        in
            case v0_opt of
                NONE => ()
              | SOME v0 =>
                let
                  val uds = get_deltas {thyname = thyname}
                  val _ = delta_side_effects thyname uds
                  val v = rev_itlist apply_delta uds v0
                in
                  Context.Data.modify value_table
                    (Symtab.update (thyname,v))
                end
          end
    end



fun make {info : ('delta,'value)adata_info, get_deltas, delta_side_effects} =
    let
      open ThyDataSexp
      val {tag, apply_delta, initial_values, ...} = info
      val value_table : 'value Symtab.table Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".values",
             empty = itlist Symtab.update initial_values Symtab.empty,
             pp = fn _ => "<ancestry." ^ tag ^ ".values>"}
      fun valueDB_of ctxt {thyname} =
          Symtab.lookup (Context.Data.get value_table ctxt) thyname
      fun valueDB arg = valueDB_of (Context.snapshot()) arg

      (* calculates merged values in the "onload" hook *)
      val apply_delta_hook = ref (fn _ => NONE)
      fun side_effects _ = List.app delta_side_effects
      val parent_extras =
          {tag = tag, apply_delta_hook = apply_delta_hook,
           delta_side_effects = side_effects,
           apply_delta = apply_delta, get_deltas = get_deltas,
           value_table = value_table}

      val {export = parent_export,
           segment_data = parent_segment_data, ...} =
          ThyDataSexp.new {
            thydataty = tag, merge = #new,
            load = parent_onload parent_extras, other_tds = fn (s,_) => SOME s
          }
      fun parents thyname =
          case parent_segment_data thyname of
              NONE => Theory.parents (#thyname thyname)
            | SOME t => valOf (list_decode string_decode t)
      val ancestors : ancestor_memo Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".ancestors",
             empty = empty_ancestor_memo,
             pp = fn _ => "<ancestry." ^ tag ^ ".ancestors>"}
      val info = {get_deltas = get_deltas, tag = tag,
                  dblookup = valueDB,
                  apply_delta = apply_delta,
                  parents = parents, ancestors = ancestors}
      val _ = apply_delta_hook := merge info
      fun set_ancestry sl =
          let
            val _ = parent_export (List $ map String sl)
            val vopt = merge info sl
          in
            (case vopt of
                SOME v =>
                Context.Data.modify value_table
                                    (Symtab.update (current_theory(), v))
              | NONE => ());
            vopt
          end
      fun onload s =
          parent_onload parent_extras {
            thyname = s, data = parent_segment_data {thyname = s}
          }
    in
      List.app onload (tts_ancestry "-");
      {merge = merge info, DB = valueDB, DB_of = valueDB_of,
       parents = parents, set_parents = set_ancestry}
    end

fun gen_other_tds {tag,dec,enc,P} = let
  val last_scan_epoch = ref []
  (* P is a retire-state predicate (kernel-side via retire_epoch, DB-side
     via DB.fetch_knm which only transitions on DelBinding).  When
     retire_epoch is unchanged and the event is retire_captured, no
     stored delta's uptodate-status has moved. *)
  fun scan t =
    case t of
        ThyDataSexp.List raw_ds =>
        let
          val (rawgds, rawbads) = List.partition ThyDataSexp.uptodate raw_ds
        in
          case ThyDataSexp.list_decode dec (ThyDataSexp.List rawgds) of
              SOME ds =>
              let
                val (gds, bads) = List.partition P ds
              in
                if null rawbads andalso null bads then NONE
                else SOME (ThyDataSexp.mk_list enc gds)
              end
            | NONE => raise ERR "gen_other_tds"
                            ("Bad encoding (1) for tag: "^tag)
        end
      | _ => raise ERR "gen_other_tds" ("Bad encoding (2) for tag: "^tag)
  in fn (t, thyevent) =>
        let val cur = [Type.type_epoch(), Term.term_epoch ()] in
          if TheoryDelta.retire_captured thyevent andalso !last_scan_epoch = cur
          then NONE
          else scan t before last_scan_epoch := cur
        end
  end

type ('delta,'value) fullresult =
     { merge : string list -> 'value option,
       DB : {thyname : string} -> 'value option,
       DB_of : Context.t -> {thyname : string} -> 'value option,
       get_deltas : {thyname : string} -> 'delta list,
       record_delta : 'delta -> unit,
       parents : {thyname : string} -> string list,
       set_parents : string list -> 'value option,
       get_global_value : unit -> 'value,
       get_global_value_of : Context.t -> 'value,
       update_global_value : ('value -> 'value) -> unit,
       update_global_value_of : ('value -> 'value) -> Context.t ->
                                Context.t }

fun fullmake {adinfo:('delta,'value)adata_info, sexps, globinfo, uptodate_delta} =
    let
      open ThyDataSexp
      val {dec,enc} = sexps
      val {apply_to_global,initial_value,thy_finaliser} = globinfo
      val {initial_values, tag, apply_delta, ...} = adinfo

      (* single global value *)
      val global_slot : 'value Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".global",
             empty = initial_value,
             pp = fn _ => "<ancestry." ^ tag ^ ".global>"}
      fun get_global_value_of ctxt = Context.Data.get global_slot ctxt
      fun get_global_value () = get_global_value_of (Context.snapshot())
      val update_global_value = Context.Data.modify global_slot
      val update_global_value_of = Context.Data.update global_slot

      (* table of values per theory *)
      val value_table : 'value Symtab.table Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".values",
             empty = itlist Symtab.update initial_values Symtab.empty,
             pp = fn _ => "<ancestry." ^ tag ^ ".values>"}
      fun valueDB_of ctxt {thyname} =
          Symtab.lookup (Context.Data.get value_table ctxt) thyname
      fun valueDB arg = valueDB_of (Context.snapshot()) arg

      (* store deltas *)
      val {export = export_raw_delta, segment_data = get_raw_deltas,
           set = set_raw_deltas} =
          ThyDataSexp.new {thydataty = tag ^ ".deltas",
                           merge = ThyDataSexp.append_merge,
                           load = fn _ => (),
                           other_tds = gen_other_tds {tag=tag ^ ".deltas",
                                                      P = uptodate_delta,
                                                      enc = enc, dec = dec
                                                     }
                          }
      fun get_deltas {thyname} =
          case get_raw_deltas {thyname=thyname} of
              NONE => []
            | SOME d => (
              case ThyDataSexp.list_decode dec d of
                  SOME ds => ds
                | NONE => raise ERR "fullmake" "get_deltas: bad decode"
            )

      (* store parentage *)
      val apply_delta_hook = ref (fn _ => NONE)
      fun delta_side_effects thyname ds =
          case thy_finaliser of
              NONE => List.app (update_global_value o apply_to_global) ds
            | SOME f => update_global_value (f {thyname=thyname} ds)
      val parent_extras =
          {tag = tag, apply_delta_hook = apply_delta_hook,
           delta_side_effects = delta_side_effects,
           apply_delta = apply_delta, get_deltas = get_deltas,
           value_table = value_table}
      val {export = export_raw_parents, segment_data = get_raw_parents, ...} =
          ThyDataSexp.new {thydataty = tag ^ ".parents",
                           merge = #new,
                           load = parent_onload parent_extras,
                           other_tds = (fn (t,_) => SOME t)}
      fun get_parents {thyname} =
          case get_raw_parents {thyname=thyname} of
              NONE => Theory.parents thyname
            | SOME t => valOf (list_decode string_decode t)

      val ancestors : ancestor_memo Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".ancestors",
             empty = empty_ancestor_memo,
             pp = fn _ => "<ancestry." ^ tag ^ ".ancestors>"}
      val info =
          {get_deltas = get_deltas, dblookup = valueDB,
           apply_delta = apply_delta, tag = tag, parents = get_parents,
           ancestors = ancestors}
      val _ = apply_delta_hook := merge info
      fun set_ancestry sl =
          let
            val _ = set_raw_deltas (List [])
            val _ = export_raw_parents (List $ map String sl)
            val vopt = merge info sl
          in
            case vopt of
                SOME v =>
                (Context.Data.modify value_table
                                     (Symtab.update (current_theory(), v));
                 update_global_value (K v))
              | NONE => ();
            vopt
          end
      fun record_delta d = export_raw_delta (ThyDataSexp.List [enc d])
      fun onload s =
          parent_onload parent_extras {thyname = s,
                                       data = get_raw_parents {thyname = s}}
      val _ = List.app onload (tts_ancestry "-")
    in
      {merge = merge info, DB = valueDB, DB_of = valueDB_of,
       get_deltas = get_deltas,
       record_delta = record_delta,
       parents = get_parents,
       set_parents = set_ancestry,
       get_global_value = get_global_value,
       get_global_value_of = get_global_value_of,
       update_global_value = update_global_value,
       update_global_value_of = update_global_value_of}
    end

fun with_temp_value (fr:('delta,'value)fullresult) v =
    Portable.genwith_flag ({ get = #get_global_value fr,
                             set = #update_global_value fr o K }, v)


end; (* struct *)
