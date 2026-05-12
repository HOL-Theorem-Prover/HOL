structure ThmSrc_tr :> ThmSrc_tr =
struct

open HolKernel RawTheory_dtype

fun load_thydata {thyname, path, hash} =
    let
      open HOLsexp
      (* Parse the .dat file for metadata only *)
      val rawthy as {parents, tables, exports, name=stored_name, ...} =
            RawTheoryReader.load_raw_thydata {path = path}
      fun mungename {thy,hash} = (thy,hash)
      val _ = thyname = stored_name orelse
              raise Fail ("ThmSrc_tr: reading at " ^ path ^ " for theory " ^
                          thyname ^ " and got " ^ stored_name ^ " instead")

      (* Link parents in the theory graph *)
      val _ = Theory.link_parents (thyname, hash) (map mungename parents)

      (* Replay theorems via ProofTraceReplay.
         This defines all types and constants via kernel primitives
         (prim_new_type, prim_new_const, prim_type_definition,
         gen_prim_specification, etc.) as side effects of replaying
         the definition proofs. *)
      val fspath = case HFS_NameMunge.HOLtoFS path of
                       SOME {dir, ...} => dir
                     | NONE => OS.Path.dir path
      val trfile = OS.Path.concat
                     (if fspath <> "" then fspath else ".",
                      thyname ^ "Theory.tr.gz")
      val _ = ProofTraceReplay.replay trfile
      val (named_dict, anon_list) = ProofTraceReplay.replayed_thms thyname

      (* Extract theorem name/info from the raw .dat exports.
         We need thminfo (class, private) from the raw thm records. *)
      val {thms = raw_thms, ...} = exports
      fun get_thminfo (raw : string raw_thm) : thminfo =
          {private = #private raw,
           loc = Unknown,
           class = #class raw}

      (* Build the named theorem list for DB.bindl.
         Match raw_thm records (which have names and thminfo) with
         replayed theorems (which have the actual thm values). *)
      val named_thms : (string * Thm.thm * thminfo) list =
          List.mapPartial
            (fn raw =>
                let val nm = #name raw
                in case Redblackmap.peek(named_dict, nm) of
                       SOME th => SOME (nm, th, get_thminfo raw)
                     | NONE => NONE
                end)
            raw_thms

      (* Register replayed axioms so that uptodate_axioms can find them.
         Axiom nonces survive in replayed theorem tags (unlike disk_thm
         which strips them), so they need to be in the registry for
         theorems derived from them to pass uptodate checks. *)
      val _ = List.app (fn (_, th, {class,...}: thminfo) =>
                  if class = Axm
                  then Theory.register_replayed_axiom th
                  else ()) named_thms

      val thmdict =
          List.foldl (fn ((n,th,i), D) => Symtab.update (n, (th,i)) D)
                     Symtab.empty
                     named_thms
      val _ = DB.bindl thyname named_thms

      (* Process thydata (simp sets, grammar updates, etc.).
         Build only the string and term vectors needed for decoding
         thydata s-expressions — no theorem construction involved. *)
      val {stringt = strv, idt = intplist,
           typet = shtylist, termt = shtmlist} = tables
      val idv = SharingTables.build_id_vector strv intplist
      val tyv = SharingTables.build_type_vector idv shtylist
      val tmv = SharingTables.build_term_vector idv tyv shtmlist
      val shared_readmaps = {strings = fn i => Vector.sub(strv, i),
                             terms = Term.read_raw tmv}
      val _ =
          app (fn {data,ty} =>
                  Theory.LoadableThyData.temp_encoded_update {
                    thy = thyname,
                    thydataty = ty,
                    shared_readmaps = shared_readmaps,
                    data = data
                  })
              (case list_decode(pair_decode(string_decode, SOME))
                                (#thydata rawthy)
                of SOME items => map (fn (ty,d) => {data=d,ty=ty}) items
                 | NONE => raise Fail "ThmSrc_tr: couldn't decode thydata")
    in
      thmdict
    end handle Interrupt => raise Interrupt
             | e => raise Fail ("ThmSrc_tr: " ^ General.exnMessage e)

(* Set up anonymous theorem lookup to use replayed theorems
   instead of creating disk_thms during thydata processing.
   This is set once and handles all theories via replayed_thms. *)
val _ = ThyDataSexp.anon_thm_lookup :=
    (fn (thy, id) =>
        let val (_, anons) = ProofTraceReplay.replayed_thms thy
        in SOME (List.nth(anons, id))
        end handle _ => NONE)

(* Install ourselves as the theorem loader *)
val _ = TheoryReader.load_thydata_fn := load_thydata

end
