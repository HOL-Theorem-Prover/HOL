structure DiskThms :> DiskThms =
struct

  open HolKernel SharingTables
  val dflt_info = {loc = Unknown, private = false, class = DB_dtype.Thm}
  fun to_sexp thms =
       let
         val ed = {
           named_terms = [], unnamed_terms = [],
           named_types = [], unnamed_types = [],
           theorems = map (fn (n,th) => (n,th,dflt_info)) thms
         } : extract_data
         val sdo = build_sharing_data ed
       in
         enc_sdata sdo
       end

  fun write_stream hnd named_thms =
    HOLPP.prettyPrint ((fn s => TextIO.output(hnd, s)), 75)
                      (HOLsexp.printer (to_sexp named_thms))

  fun write_file fname named_thms = let
    open TextIO
    val outstream = TextIO.openOut fname
  in
    write_stream outstream named_thms before TextIO.closeOut outstream
  end

  fun read_stream instream =
      let
        val t = HOLsexp.fromStream instream
                handle Interrupt => raise Interrupt
                     | _ => raise Fail "Couldn't parse sexp from file"
      in
        case dec_sdata {with_strings = fn _ => (), with_stridty = fn _ => ()} t
         of
            NONE => raise Fail "Couldn't decode sexp"
          | SOME sdi =>
            map (fn (n,th,i) => (n,th))
                (#theorems (export_from_sharing_data sdi))
      end

  fun read_file fname =
      let
        val strm = TextIO.openIn fname
        val r = Exn.capture read_stream strm
        val _ = TextIO.closeIn strm
      in
        Exn.release r
      end

end (* struct *)
