(* Load from src/portableML/rawtheory after parent-benchmark-load.ML.
   Measurements exclude startup and correctness checks. No files are written. *)
structure ParentBenchmark =
struct

(* The pre-TheoryDat Holmake scanner, retained verbatim for comparison. *)
fun old_parents dat_path =
    let
      val ins = TextIO.openIn dat_path
      val content = TextIO.inputAll ins
      val _ = TextIO.closeIn ins
      val full = Substring.full content
      val (_, at_theory) = Substring.position "(theory" full
    in
      if Substring.size at_theory < 7 then []
      else
        let
          val after_theory =
              Substring.dropl Char.isSpace (Substring.triml 7 at_theory)
          val (header, _) = Substring.position "(core-data" after_theory
          fun loop ss acc =
              let val (_, rest) = Substring.position "(\"" ss
              in
                if Substring.size rest < 2 then List.rev acc
                else
                  let
                    val after_open = Substring.triml 2 rest
                    val (xss, ass) = Substring.position "\"" after_open
                  in
                    if Substring.size ass < 1 then List.rev acc
                    else
                      let val ass1 = Substring.triml 1 ass
                      in
                        if Substring.isPrefix " . \"" ass1 then
                          let
                            val ass2 = Substring.triml 4 ass1
                            val (yss, ass3) = Substring.position "\"" ass2
                          in
                            if Substring.size ass3 >= 1 then
                              loop (Substring.triml 1 ass3)
                                   ((Substring.string xss,
                                     Substring.string yss) :: acc)
                            else List.rev acc
                          end
                        else loop ass1 acc
                      end
                  end
              end
        in loop header [] end
    end
    handle _ => []

fun new_parents path =
    case TheoryDat.read_parents path of
        TheoryDat.Success ps => map (fn {thy, hash} => (thy, hash)) ps
      | TheoryDat.Failure s => raise Fail (path ^ ": " ^ s)

(* load_raw_thydata uses HOLFileSys name munging. Read a physical path
   through a stream, then use exactly the same parser and decoder. *)
fun full_parents path =
    let
      val ins = TextIO.openIn path
      val raw = HOLsexp.fromStream ins
                handle e => (TextIO.closeIn ins; raise e)
      val _ = TextIO.closeIn ins
      val thy = case RawTheoryReader.decode raw of
                    SOME thy => thy
                  | NONE => raise Fail ("Invalid theory: " ^ path)
    in map (fn {thy, hash} => (thy, hash)) (#parents thy) end

fun canonical ps =
    Listsort.sort
      (fn ((a,b), (c,d)) =>
          case String.compare (a,c) of
              EQUAL => String.compare (b,d) | ord => ord) ps

fun repeat n f = if n <= 0 then () else (f (); repeat (n - 1) f)
fun seconds t = Real.fmt (StringCvt.FIX (SOME 6)) (Time.toReal t)

(* CPU/GC counters are portable Basis timers; allocation is not measured.
   Force GC outside the timed interval to reduce previous-reader carryover. *)
fun measure iterations label f =
    let
      val _ = PolyML.fullGC ()
      val wall = Timer.startRealTimer ()
      val cpu = Timer.startCPUTimer ()
      val _ = repeat iterations f
      val elapsed = Timer.checkRealTimer wall
      val {usr, sys} = Timer.checkCPUTimer cpu
      val gc = Timer.checkGCTime cpu
    in
      print (label ^ "," ^ Int.toString iterations ^ "," ^
             seconds elapsed ^ "," ^ seconds usr ^ "," ^
             seconds sys ^ "," ^ seconds gc ^ "\n")
    end

fun rotate [] = []
  | rotate (x::xs) = xs @ [x]

(* Resolver is supplied by the operator, exactly as for a real builder.
   It must resolve every non-bootstrap parent, without modifying files. *)
fun run {paths, resolve, iterations, rounds} =
    let
      val _ = if iterations > 0 andalso rounds > 0 andalso not (null paths)
              then () else raise Fail "Need paths and positive counts"
      fun file path =
          let
            val ps = canonical (full_parents path)
            val _ = if canonical (old_parents path) = ps andalso
                       canonical (new_parents path) = ps
                    then () else raise Fail ("Reader disagreement: " ^ path)
            val _ =
                if null (TheoryDat.validate {path = path, resolve = resolve})
                then () else raise Fail ("Parent validation failed: " ^ path)
            val artifacts =
                List.mapPartial
                  (fn (thy, _) =>
                      if thy = "min" then NONE
                      else case resolve thy of
                               TheoryDat.Artifact p => SOME p
                             | _ => raise Fail ("Unresolved parent: " ^ thy))
                  ps
            fun hash () =
                List.app (fn p => ignore (SHA1.sha1_file {filename = p}))
                         artifacts
            val readers =
                [("old", fn () => ignore (old_parents path)),
                 ("header", fn () => ignore (new_parents path)),
                 ("full", fn () => ignore (full_parents path)),
                 ("parent-sha1", hash),
                 ("validation", fn () =>
                    if null (TheoryDat.validate
                               {path = path, resolve = resolve}) then ()
                    else raise Fail "Parent changed during benchmark")]
            fun round n jobs =
                if n > rounds then ()
                else
                  (print ("# round " ^ Int.toString n ^ "\n");
                   List.app (fn (label, f) => measure iterations label f) jobs;
                   round (n + 1) (rotate jobs))
          in
            print ("# file " ^ path ^ " bytes=" ^
                   Position.toString (OS.FileSys.fileSize path) ^
                   " parents=" ^ Int.toString (length ps) ^ "\n");
            (* Warm all paths and implementations before timing. *)
            List.app (fn (_, f) => f ()) readers;
            round 1 readers
          end
    in
      print "reader,iterations,wall_seconds,user_seconds,sys_seconds,gc_seconds\n";
      List.app file paths
    end

end
