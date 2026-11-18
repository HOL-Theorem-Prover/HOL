open HolKernel boolLib
local open smlExecute smlInfix smlLexer smlOpen smlParser smlPrettify
  smlRedirect smlTimeout smlParallel in end

(*
local open smlParallel in
  val l1 = List.tabulate (10,I);
  val _ = parmap_queue_extern 2 examplespec () l1;
end
*)

local open aiLib smlTimeout in
  fun f () = 5;
  val (_,t1) = add_time (timeout 1.0 f) ();
  fun loop () = loop ();
  fun g () = (timeout 0.01 loop ()) handle FunctionTimeout => ();
  val (_,t2) = add_time g ();

  val cleanup_done = ref false;
  fun cleanup_worker () =
    (loop () handle Interrupt =>
      (OS.Process.sleep (Time.fromReal 0.05);
       cleanup_done := true;
       raise Interrupt));
  val _ = (timeout 0.01 cleanup_worker () handle FunctionTimeout => ());
  val _ = if !cleanup_done then ()
          else raise Fail "timeout interrupted worker cleanup";
end

(* Unless HOL4_SCRATCH names it, aiLib.scratch_dir is private to each
   process and removed when the process exits.  Probed in child HOL
   processes, so that the environment is under the test's control. *)
local open aiLib in
  val tmp = OS.FileSys.tmpName ()
  val _ = (remove_file tmp; mkDir_err tmp)
  val xdg = tmp ^ "/xdg"
  val scratch_root = xdg ^ "/hol4/scratch"
  fun fail s = raise Fail ("scratch_dir: " ^ s)

  (* A child records its scratch_dir, after doing [body] in it *)
  fun child_cmd env name body =
    let
      val script = tmp ^ "/" ^ name ^ ".sml"
      val _ = writel script
        [body,
         "val _ = aiLib.writel " ^ mlquote (tmp ^ "/" ^ name ^ ".out") ^
         " [!aiLib.scratch_dir];"]
    in
      "env -u HOL4_SCRATCH -u HOL4_TACTICTOE_CACHE XDG_CACHE_HOME=" ^
      shell_quote xdg ^ " " ^ env ^ " " ^
      shell_quote (HOLDIR ^ "/bin/hol") ^ " run aiLib " ^
      shell_quote script ^ " > " ^ shell_quote (tmp ^ "/" ^ name ^ ".log") ^
      " 2>&1"
    end
  fun result name = hd (readl (tmp ^ "/" ^ name ^ ".out"))
  fun run cmd = if OS.Process.isSuccess (OS.Process.system cmd) then ()
                else fail ("child failed: " ^ cmd)
  (* Two at once, so that they are distinct processes *)
  fun run2 c1 c2 = run (c1 ^ " & p=$!; " ^ c2 ^ " && wait $p")
  val mk = "val _ = aiLib.mkDir_err (aiLib.scratch_dir_of ());"
  fun under root d = String.isPrefix (root ^ "/") d

  val _ = run2 (child_cmd "" "a" mk) (child_cmd "" "b" mk)
  val (a, b) = (result "a", result "b")
  val _ = if a <> b then () else fail ("processes share " ^ a)
  val _ = if under scratch_root a andalso under scratch_root b then ()
          else fail ("not under " ^ scratch_root ^ ": " ^ a ^ ", " ^ b)
  val _ = if exists_file a orelse exists_file b
          then fail "left behind after exit" else ()

  val ttt = tmp ^ "/ttt"
  val _ = run (child_cmd ("HOL4_TACTICTOE_CACHE=" ^ shell_quote ttt) "c" "")
  val _ = if under (ttt ^ "/tmp/scratch") (result "c") then ()
          else fail ("HOL4_TACTICTOE_CACHE ignored: " ^ result "c")

  val given = tmp ^ "/given"
  val _ = run (child_cmd ("HOL4_SCRATCH=" ^ shell_quote given) "d" mk)
  val _ = if result "d" = given then ()
          else fail ("HOL4_SCRATCH ignored: " ^ result "d")
  val _ = if exists_file given then ()
          else fail "HOL4_SCRATCH directory removed"

  val _ = if exists_file scratch_root andalso
             not (null (listDir scratch_root))
          then fail ("files left in " ^ scratch_root) else ()
  val _ = run ("rm -rf " ^ shell_quote tmp)
end
