structure DiskThms :> DiskThms =
struct

  open HolKernel

  fun ppwrite (named_thms : (string * thm) list) = let
    open smpp
    fun out s = add_string s
    val NL = add_newline
    val SPC = add_break(1,0)
    fun cblock i = block PP.CONSISTENT i
    fun iblock i = block PP.INCONSISTENT i
    fun qstr s = String.concat ["\"", String.toString s,  "\""]
    fun emit_string s = out (qstr s)

    val thms = map #2 named_thms
    fun thm_terms (th, acc) = let
      val hyps = hypset th
    in
      HOLset.add(HOLset.union(acc,hyps), concl th)
    end
    val allterms = List.foldl thm_terms empty_tmset thms
    fun leavesl (acc, tlist) =
        case tlist of
          [] => acc
        | t::ts => let
          in
            case dest_term t of
              COMB(t1, t2) => leavesl(acc, t1::t2::ts)
            | LAMB(t1, t2) => leavesl(acc, t1::t2::ts)
            | v => leavesl(HOLset.add(acc,t), ts)
          end
    fun leaves (t, acc) = leavesl(acc, [t])
    val allleaves = HOLset.foldl leaves empty_tmset allterms

    open SharingTables
    fun doterms (t, tables) = #2 (make_shared_term t tables)
    val (strtable,idtable,tytable,tmtable) =
        HOLset.foldl
          doterms
          (empty_strtable,empty_idtable,empty_tytable,empty_termtable)
          allleaves
    fun pr_sty sty =
        case sty of
          TYV s => out ("TYV" ^ qstr s)
        | TYOP ilist =>
            out "TYOP[" >>
            block PP.INCONSISTENT 5 (
              pr_list (fn i => out (Int.toString i)) SPC ilist
            ) >> out "]"
    fun pr_stm stm =
        case stm of
          TMV(s, i) =>
            out "TMV[" >> block PP.CONSISTENT 4 (
              out (qstr s) >> SPC >> out (Int.toString i ^ "]")
            )
        | TMC(i, j) =>
            out "TMC[" >> block PP.CONSISTENT 4 (
              out (Int.toString i) >> SPC >> out (Int.toString j ^ "]")
            )
        | _ => raise Fail "Expect only vars and consts in term table"
    fun paren b p = if b then iblock 1 (out "(" >> p >> out ")") else p
    fun pr_term t = let
      fun recurse newcomb t =
          case dest_term t of
            COMB(t1, t2) =>
              paren newcomb (recurse false t1 >> SPC >> recurse true t2)
          | LAMB(t1,t2) =>
              paren true (
                out "\\" >> recurse false t1 >> out "." >> SPC >>
                recurse false t2
              )
          | _ => let
              val i = Map.find(#termmap tmtable, t)
            in
              out (Int.toString i)
            end
    in
      iblock 1 (paren true (recurse false t))
    end

    fun pr_thm th =
      block PP.CONSISTENT 0 (pr_list pr_term SPC (concl th::hyp th))

    fun pr_namedthm (n,th) =
      block PP.CONSISTENT 2 (out (qstr n) >> SPC >> pr_thm th)

    val m =
        cblock 0 (* whole file block *) (
          cblock 0 (* STRINGS *) (
            out "STRINGS [" >>
            pr_list (fn s => out (Lib.mlquote s)) SPC
                    (List.rev (#list strtable)) >>
            out "]"
          ) >> SPC >>
          cblock 2 (* IDs block *) (
            cblock 2 (* IDs title block *) (
              out "IDS" >> SPC >> out "["
            ) >>
            iblock 0 (
              pr_list
                (fn (Thy,Other) => out (Int.toString Thy) >> SPC >>
                                   out (Int.toString Other))
                (out "," >> SPC)
                (List.rev (#idlist idtable))
            ) >> out "]"
          ) (* end IDs block *) >> SPC >>

          block PP.CONSISTENT 2 (* types block *) (
            out "TYPES" >> SPC >>
            block PP.INCONSISTENT 0 (
              pr_list pr_sty SPC (List.rev (#tylist tytable))
            )
          ) >> SPC >> (* end types block *)

          block PP.CONSISTENT 2 (* terms block *) (
            out "TERMS" >> SPC >>
            block PP.INCONSISTENT 0 (
              pr_list pr_stm SPC (List.rev (#termlist tmtable))
            )
          ) (* end terms block *) >> SPC >>

          block PP.CONSISTENT 2 (* theorems block *) (
            out "THEOREMS" >> SPC >> block PP.CONSISTENT 0 (
              pr_list pr_namedthm SPC named_thms
            )
          )
        )
  in
    Parse.mlower m
  end


  fun write_stream hnd named_thms =
    HOLPP.prettyPrint ((fn s => TextIO.output(hnd, s)), 75) (ppwrite named_thms)

  fun write_file fname named_thms = let
    open TextIO
    val outstream = TextIO.openOut fname
  in
    write_stream outstream named_thms before TextIO.closeOut outstream
  end

  val read_file = DiskFilesHeader.convert_prethms o
                  AssembleDiskFiles.raw_read_file
  val read_stream =
      DiskFilesHeader.convert_prethms o AssembleDiskFiles.raw_read_stream

end (* struct *)
