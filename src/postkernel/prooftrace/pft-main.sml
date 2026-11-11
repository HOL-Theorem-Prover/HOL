val () = loadPath :=
  (case OS.Process.getEnv "HOL_PFT_LIB_DIR" of
     SOME dir => dir
   | NONE => raise Fail "run this driver through the pft script") :: !loadPath;
val () = load "PFTCLI";

val () =
  let
    val file = case OS.Process.getEnv "HOL_PFT_ARGS_FILE" of
                 SOME file => file
               | NONE => raise Fail "run this driver through the pft script"
    val ins = BinIO.openIn file
    val data = (BinIO.inputAll ins before BinIO.closeIn ins)
               handle exn => (BinIO.closeIn ins; raise exn)
    val fields = String.fields (fn c => c = #"\000")
                   (Byte.bytesToString data)
    val args = List.take(fields, length fields - 1)
  in PFTCLI.main args end;
