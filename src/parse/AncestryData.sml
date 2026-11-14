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

fun smem s e = HOLset.member(s,e)
fun sadd e s = HOLset.add(s,e)

(* Each theory's ancestry, the theory included.  A loaded theory's parents
   never change, so its ancestry is computed once per tag and kept in a
   context slot.  The current theory's parents can still change, as can
   those of "-" (the fringe of the theory graph), so their ancestries, and
   those of theories whose parents name them, are computed afresh on each
   use.  Each theory in the memo has a number, given in the order theories
   enter it, so its ancestors all have smaller numbers; its ancestry is a
   bit vector over those numbers. *)
type bitsets = (int * Word8Vector.vector) Symtab.table
type ancestor_memo = {next : int, sets : bitsets}
val empty_ancestor_memo : ancestor_memo = {next = 0, sets = Symtab.empty}

fun bit i = Word8.<< (0w1, Word.fromInt (i mod 8))
fun bits_member bv i =
    i div 8 < Word8Vector.length bv andalso
    Word8.andb (Word8Vector.sub (bv, i div 8), bit i) <> 0w0
fun byte bv j =
    if j < Word8Vector.length bv then Word8Vector.sub (bv, j) else 0w0
fun bits_union (bv1, bv2) =
    Word8Vector.tabulate
      (Int.max (Word8Vector.length bv1, Word8Vector.length bv2),
       fn j => Word8.orb (byte bv1 j, byte bv2 j))

(* A parent list may name the theory itself (e.g., after set_parents
   [current_theory()]); that edge adds nothing to its ancestry *)
fun proper_parents parents thy =
    List.filter (fn p => p <> thy) (parents {thyname = thy})

(* thy (numbered n) and the union of its parents' sets *)
fun ancestor_bits (sets : bitsets) n ps =
    let
      val pbvs = map (fn p => #2 (valOf (Symtab.lookup sets p))) ps
    in
      Word8Vector.tabulate
        (n div 8 + 1,
         fn j => foldl (fn (bv, w) => Word8.orb (w, byte bv j))
                       (if j = n div 8 then bit n else 0w0) pbvs)
    end

fun memo_member (sets : bitsets) bv s =
    case Symtab.lookup sets s of
        SOME (i, _) => bits_member bv i
      | NONE => false

(* Add thy and its ancestors to the memo, except those described above.
   "-" is not visited: the fringe can include a theory whose parents name
   "-" *)
fun extend_memo parents (thy, memo : ancestor_memo) =
    if Symtab.defined (#sets memo) thy orelse thy = "-" then memo
    else
      let
        val ps = proper_parents parents thy
        val memo' as {next, sets} = foldl (extend_memo parents) memo ps
      in
        if Thm.getCT() = SOME thy orelse
           not (List.all (Symtab.defined sets) ps)
        then memo'
        else {next = next + 1,
              sets = Symtab.update (thy, (next, ancestor_bits sets next ps))
                                   sets}
      end

(* The theories extend_memo would add to the memo, by the same rule but
   without their sets: whether a theory's ancestry is fixed is decided at
   load, its set only when its value is first read *)
type fixed_set = unit Symtab.table
fun extend_fixed parents (thy, fx) =
    if Symtab.defined fx thy orelse thy = "-" then fx
    else
      let
        val ps = proper_parents parents thy
        val fx' = foldl (extend_fixed parents) fx ps
      in
        if Thm.getCT() = SOME thy orelse
           not (List.all (Symtab.defined fx') ps)
        then fx'
        else Symtab.update (thy, ()) fx'
      end

(* The ancestry of a theory not in the memo, as a membership test: the
   theories met outside the memo, and the union of the sets of those in it *)
fun fresh_ancestry ({sets, ...} : ancestor_memo) parents thy =
    let
      fun visit (t, acc as (names, bv)) =
          if smem names t orelse memo_member sets bv t then acc
          else
            case Symtab.lookup sets t of
                SOME (_, b) => (names, bits_union (bv, b))
              | NONE => foldl visit (sadd t names, bv) (parents {thyname = t})
      val (names, bv) =
          visit (thy, (HOLset.empty String.compare, Word8Vector.fromList []))
    in
      fn s => smem names s orelse memo_member sets bv s
    end

(* A function giving the ancestry, as a membership test, of each theory in
   thys and in their ancestries *)
fun ancestor_sets slot parents thys =
    let
      val result = ref empty_ancestor_memo
      fun extend memo =
          let
            val memo' = foldl (extend_memo parents) memo thys
          in
            result := memo'; memo'
          end
      val _ = Context.Data.modify slot extend
      val memo as {sets, ...} = !result
    in
      fn thy =>
         case Symtab.lookup sets thy of
             SOME (_, bv) => memo_member sets bv
           | NONE => fresh_ancestry memo parents thy
    end

type ('d,'v) info =
     {get_deltas : {thyname: string} -> 'd list,
      dblookup : {thyname : string} -> 'v Susp.susp option,
      apply_delta : 'd -> 'v -> 'v, tag : string,
      parents : {thyname : string} -> string list,
      ancestors : ancestor_memo Context.Data.slot,
      fixed : fixed_set Context.Data.slot}

fun fpluck _ [] = NONE
  | fpluck f (h::t) = case f h of
                          NONE => Option.map (fn (v,r) => (v,h::r)) (fpluck f t)
                        | SOME v => SOME ((h,v),t)

(* What a merge of thys starts from: the value of the first theory listed
   that has one, its ancestry, and the other theories, less those that are
   ancestors of theories listed.  NONE when no such theory has a value. *)
fun merge_start_with lookup (info : ('d,'v) info) thys =
    let
      val {parents,ancestors,...} = info
      val ancs = ancestor_sets ancestors parents thys
      (* drop the theories that are ancestors of others in the list *)
      fun redundant thy =
          List.exists (fn t => t <> thy andalso ancs t thy) thys
      val thys = List.filter (not o redundant) thys
    in
      case fpluck (fn thy => lookup {thyname=thy}) thys of
          NONE => NONE
        | SOME ((h,v0),rest) => SOME (v0, ancs h, rest)
    end
fun merge_start (info : ('d,'v) info) thys =
    merge_start_with (#dblookup info) info thys

(* Apply, to the starting value, the deltas of the other theories and of
   their ancestors, each theory once *)
fun merge_from (info : ('d,'v) info) (v0, inanc0, rest) : 'v =
    let
      val {parents,get_deltas,apply_delta,...} = info
      fun seen aset t = inanc0 t orelse smem aset t
      fun recurse (A, aset) worklist =
          case worklist of
              [] => A
            | Visit thy :: rest =>
              if seen aset thy then recurse (A, aset) rest
              else
                let
                  val ps0 = parents {thyname = thy}
                  val ps = List.filter (not o seen aset) ps0
                  val deltas = get_deltas {thyname = thy}
                in
                  recurse (A, sadd thy aset)
                          (map Visit ps @ (Apply deltas :: rest))
                end
            | Apply ds :: rest =>
              recurse (rev_itlist apply_delta ds A, aset) rest
    in
      recurse (Susp.force v0, HOLset.empty String.compare) (map Visit rest)
    end

fun merge (info : ('d,'v) info) thys : 'v option =
    let
      val _ = DPRINT ("Calling " ^ #tag info ^ ":merge[" ^
                      String.concatWith ", " thys ^ "]")
    in
      Option.map (merge_from info) (merge_start info thys)
    end

(* A theory's value is computed when first read, or at once when the
   theory's ancestry is not fixed (its parents lead to the current theory
   or to "-"), since it would then depend on when it is read. *)
fun now v = Susp.delay (fn () => v)

(* thy's ancestry is fixed when it is not the current theory and its parents
   are fixed, as extend_memo would then add it to the memo *)
fun fixed_ancestry (info : ('d,'v) info) thy ps =
    let
      val {fixed, parents, ...} = info
      val result = ref Symtab.empty
      fun extend fx =
          let val fx' = foldl (extend_fixed parents) fx ps
          in result := fx'; fx' end
      val _ = Context.Data.modify fixed extend
      val fx = !result
    in
      Thm.getCT() <> SOME thy andalso
      List.all (Symtab.defined fx) ps
    end

fun parent_onload extras {thyname,data = data_opt} =
    let
      open ThyDataSexp
      val {tag,info_ref,delta_side_effects,value_table} = extras
    in
      (* info_ref is NONE while ThyDataSexp.new runs this hook over the
         theories already loaded; the instance's own onload pass follows *)
      case (thyname = "min", !info_ref) of
          (true, _) => ()
        | (_, NONE) => ()
        | (false, SOME info) =>
        let
          val {apply_delta,get_deltas,...} = info
          val ps =
              case data_opt of
                  NONE =>
                  let
                    val ps = Theory.parents thyname
                    val _ = DPRINT (tag ^ ":onload(" ^ thyname ^
                                    ",NONE)\n with " ^
                                    "parents = [" ^
                                    String.concatWith ", " ps ^ "]\n")
                  in
                    ps
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
                        sl
                      end
                )
          (* a parent list may name the theory itself; the edge adds
             nothing, and merging from it would find no value *)
          val ps = List.filter (fn p => p <> thyname) ps
          val _ = DPRINT ("Calling " ^ tag ^ ":merge[" ^
                          String.concatWith ", " ps ^ "]")
          fun store v =
              Context.Data.modify value_table (Symtab.update (thyname,v))
          val fixed = fixed_ancestry info thyname ps
          (* With a fixed ancestry, the ancestor sets and the start of the
             merge wait for the first read, from the parents' values as
             they are now.  The theory gets a value when a parent has
             one: merge_start drops only parents that are ancestors of
             another listed, which then has a value too. *)
          val start =
              if fixed then
                let
                  val caps = map (fn p => (p, #dblookup info {thyname = p})) ps
                  fun lookup {thyname} =
                      case List.find (fn (p, _) => p = thyname) caps of
                          SOME (_, v) => v
                        | NONE => NONE
                in
                  if List.exists (Option.isSome o #2) caps then
                    SOME (fn () => valOf (merge_start_with lookup info ps))
                  else NONE
                end
              else Option.map K (merge_start info ps)
        in
          case start of
              NONE => ()
            | SOME get_start =>
              let
                (* the theory's own deltas are read now *)
                val uds = get_deltas {thyname = thyname}
                fun value () =
                    rev_itlist apply_delta uds
                               (merge_from info (get_start ()))
                val v = if fixed then Susp.delay value
                        else now (value ())
              in
                delta_side_effects thyname uds;
                store v
              end
          end
    end

fun make {info : ('delta,'value)adata_info, get_deltas, delta_side_effects} =
    let
      open ThyDataSexp
      val {tag, apply_delta, initial_values, ...} = info
      val value_table : 'value Susp.susp Symtab.table Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".values",
             empty = itlist (fn (thy,v) => Symtab.update (thy, now v))
                            initial_values Symtab.empty,
             pp = fn _ => "<ancestry." ^ tag ^ ".values>"}
      fun dbsusp_of ctxt {thyname} =
          Symtab.lookup (Context.Data.get value_table ctxt) thyname
      fun dbsusp arg = dbsusp_of (Context.snapshot()) arg
      fun valueDB_of ctxt arg = Option.map Susp.force (dbsusp_of ctxt arg)
      fun valueDB arg = valueDB_of (Context.snapshot()) arg

      (* calculates merged values in the "onload" hook *)
      fun side_effects _ = List.app delta_side_effects
      val info_ref = ref NONE
      val parent_extras =
          {tag = tag, info_ref = info_ref, delta_side_effects = side_effects,
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
      val fixed : fixed_set Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".fixed",
             empty = Symtab.empty,
             pp = fn _ => "<ancestry." ^ tag ^ ".fixed>"}
      val info = {get_deltas = get_deltas, tag = tag,
                  dblookup = dbsusp,
                  apply_delta = apply_delta,
                  parents = parents, ancestors = ancestors, fixed = fixed}
      val _ = info_ref := SOME info
      fun set_ancestry sl =
          let
            val _ = parent_export (List $ map String sl)
            val vopt = merge info sl
          in
            (case vopt of
                SOME v =>
                Context.Data.modify value_table
                                    (Symtab.update (current_theory(), now v))
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

fun fullmake {adinfo:('delta,'value)adata_info, sexps, globinfo,
              uptodate_delta} =
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
      val value_table : 'value Susp.susp Symtab.table Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".values",
             empty = itlist (fn (thy,v) => Symtab.update (thy, now v))
                            initial_values Symtab.empty,
             pp = fn _ => "<ancestry." ^ tag ^ ".values>"}
      fun dbsusp_of ctxt {thyname} =
          Symtab.lookup (Context.Data.get value_table ctxt) thyname
      fun dbsusp arg = dbsusp_of (Context.snapshot()) arg
      fun valueDB_of ctxt arg = Option.map Susp.force (dbsusp_of ctxt arg)
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
      fun delta_side_effects thyname ds =
          case thy_finaliser of
              NONE => List.app (update_global_value o apply_to_global) ds
            | SOME f => update_global_value (f {thyname=thyname} ds)
      val info_ref = ref NONE
      val parent_extras =
          {tag = tag, info_ref = info_ref,
           delta_side_effects = delta_side_effects,
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
      val fixed : fixed_set Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".fixed",
             empty = Symtab.empty,
             pp = fn _ => "<ancestry." ^ tag ^ ".fixed>"}
      val info =
          {get_deltas = get_deltas, dblookup = dbsusp,
           apply_delta = apply_delta, tag = tag, parents = get_parents,
           ancestors = ancestors, fixed = fixed}
      val _ = info_ref := SOME info
      fun set_ancestry sl =
          let
            val _ = set_raw_deltas (List [])
            val _ = export_raw_parents (List $ map String sl)
            val vopt = merge info sl
          in
            case vopt of
                SOME v =>
                (Context.Data.modify value_table
                                     (Symtab.update (current_theory(), now v));
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
