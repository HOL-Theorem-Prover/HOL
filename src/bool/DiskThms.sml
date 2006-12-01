structure DiskThms :> DiskThms =
struct

  open HolKernel

  fun ppwrite pps (named_thms : (string * thm) list) = let
    fun out s = PP.add_string pps s
    fun NL () = PP.add_newline pps
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
    val (idtable,tytable,tmtable) =
        HOLset.foldl doterms (empty_idtable, empty_tytable, empty_termtable)
                     allleaves

    val _ = PP.begin_block pps PP.CONSISTENT 0 (* whole file block *)

    val _ = PP.begin_block pps PP.CONSISTENT 2 (* IDs block *)
    val _ = PP.begin_block pps PP.CONSISTENT 2 (* IDs title block *)
    val _ = out "IDS"
    val _ = PP.add_break pps (1,0)
    val _ = out (Int.toString (#idsize idtable))
    val _ = PP.end_block pps                   (* end IDs title block *)
    val _ = PP.add_break pps (1,0)
    val _ = PP.begin_block pps PP.INCONSISTENT 0
    val _ =
        Portable.pr_list
          (fn {Thy,Other} => PP.add_string pps (qstr Thy ^ "$" ^ qstr Other))
          (fn () => ()) (fn () => PP.add_break pps (1,0))
          (List.rev (#idlist idtable))
    val _ = PP.end_block pps
    val _ = PP.end_block pps                   (* end IDs block *)
    val _ = PP.add_break pps (1,0)

    val _ = PP.begin_block pps PP.CONSISTENT 2 (* types block *)
    val _ = PP.begin_block pps PP.CONSISTENT 2 (* type title block *)
    val _ = out "TYPES"
    val _ = PP.add_break pps (1,0)
    val _ = out (Int.toString (#tysize tytable))
    val _ = PP.end_block pps                   (* end type title block *)
    val _ = PP.add_break pps (1,0)
    val _ = PP.begin_block pps PP.INCONSISTENT 0
    fun pr_sty sty =
        case sty of
          TYV s => PP.add_string pps ("TYV" ^ qstr s)
        | TYOP ilist => let
          in
            PP.add_string pps "TYOP[";
            PP.begin_block pps PP.INCONSISTENT 0;
            Portable.pr_list (fn i => PP.add_string pps (Int.toString i))
                             (fn () => ()) (fn () => PP.add_break pps (1,0))
                             ilist;
            PP.end_block pps;
            PP.add_string pps "]"
          end
    val _ = Portable.pr_list pr_sty (fn () => ())
                             (fn () => PP.add_break pps (1,0))
                             (List.rev (#tylist tytable))
    val _ = PP.end_block pps
    val _ = PP.end_block pps (* end types block *)
    val _ = PP.add_break pps (1,0)

    val _ = PP.begin_block pps PP.CONSISTENT 2 (* terms block *)
    val _ = PP.begin_block pps PP.CONSISTENT 2 (* terms title block *)
    val _ = out "TERMS"
    val _ = PP.add_break pps (1,0)
    val _ = out (Int.toString (#termsize tmtable))
    val _ = PP.end_block pps                   (* end terms title block *)
    val _ = PP.add_break pps (1,0)
    val _ = PP.begin_block pps PP.INCONSISTENT 0
    fun pr_stm stm =
        case stm of
          TMV(s, i) => let
          in
            PP.add_string pps "TMV[";
            PP.begin_block pps PP.CONSISTENT 0;
            PP.add_string pps (qstr s);
            PP.add_break pps (1,0);
            PP.add_string pps (Int.toString i ^ "]");
            PP.end_block pps
          end
        | TMC(i, j) => let
          in
            PP.add_string pps "TMC[";
            PP.begin_block pps PP.CONSISTENT 0;
            PP.add_string pps (Int.toString i);
            PP.add_break pps (1,0);
            PP.add_string pps (Int.toString j ^ "]");
            PP.end_block pps
          end
        | _ => raise Fail "Expect only vars and consts in term table"
    val _ = Portable.pr_list pr_stm (fn () => ())
                             (fn () => PP.add_break pps (1,0))
                             (List.rev (#termlist tmtable))
    val _ = PP.end_block pps
    val _ = PP.end_block pps                   (* end terms block *)
    val _ = PP.add_break pps (1,0)


    val _ = PP.begin_block pps PP.CONSISTENT 2 (* theorems block *)
    val _ = out "THEOREMS"
    val _ = PP.add_break pps (1,0)
    fun pr_term t = let
      fun recurse newcomb t =
          case dest_term t of
            COMB(t1, t2) => let
            in
              if newcomb then PP.add_string pps "(" else ();
              recurse false t1;
              PP.add_break pps (1,0);
              recurse true t2;
              if newcomb then PP.add_string pps ")" else ()
            end
          | LAMB(t1,t2) => let
            in
              PP.add_string pps "(\\";
              recurse false t1;
              PP.add_string pps ".";
              PP.add_break pps (1,0);
              recurse false t2;
              PP.add_string pps ")"
            end
          | _ => let
              val i = Map.find(#termmap tmtable, t)
            in
              PP.add_string pps (Int.toString i)
            end
    in
      PP.add_string pps "(";
      PP.begin_block pps PP.INCONSISTENT 2;
      recurse false t;
      PP.end_block pps;
      PP.add_string pps ")"
    end

    fun pr_thm th = let
      val hs = hyp th
      val c = concl th
    in
      PP.begin_block pps PP.CONSISTENT 0;
      Portable.pr_list pr_term (fn () => ()) (fn () => PP.add_break pps (1,0))
                       (c::hs);
      PP.end_block pps
    end

    fun pr_namedthm (n,th) = let
    in
      PP.begin_block pps PP.CONSISTENT 2;
      PP.add_string pps (qstr n);
      PP.add_break pps (1,0);
      pr_thm th;
      PP.end_block pps
    end

    val _ = PP.begin_block pps PP.CONSISTENT 0
    val _ = Portable.pr_list pr_namedthm (fn () => ())
                             (fn () => PP.add_break pps (1,0))
                             named_thms
    val _ = PP.end_block pps
    val _ = PP.end_block pps (* end theorems block *)
    val _ = PP.add_break pps (1,0)


    val _ = PP.end_block pps (* end whole file block *)
    val _ = PP.flush_ppstream pps
  in
    ()
  end


  fun write_stream hnd named_thms = let
    open TextIO
    val pps = PP.mk_ppstream {consumer = (fn s => TextIO.output(hnd, s)),
                              linewidth = 79,
                              flush = (fn () => TextIO.flushOut hnd)}
  in
    ppwrite pps named_thms
  end

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
