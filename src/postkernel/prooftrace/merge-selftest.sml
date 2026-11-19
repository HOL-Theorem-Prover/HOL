fun check name ok =
  if ok then print (name ^ ": OK\n")
  else (print (name ^ ": FAILED\n"); OS.Process.exit OS.Process.failure)

val files = ref ([] : string list)
fun temp () =
  let val base = OS.FileSys.tmpName ()
      val file = base ^ ".pft"
      val () = if OS.FileSys.access(base, []) then
                 OS.FileSys.remove base else ()
  in files := file :: !files; file end
fun bytes file =
  let val ins = BinIO.openIn file
  in BinIO.inputAll ins before BinIO.closeIn ins end
fun output ruleset =
  let val file = temp ()
  in (file, PFTWriter.openOut {file=file,version="0.1.0",ruleset=ruleset}) end
fun finish out = PFTWriter.closeOut out
  {n_ty=4,n_tm=4,n_th=32}
fun merged inputs targets =
  let val file = temp ()
  in PFTMerge.merge
       {inputs=inputs,targets=targets,output=file,binary=true}; file end
fun merge_test name f = check name (f ())
val names = ref ([] : string list)
val fh : PFTReader.format_handler =
  {tyvar=fn _ => (),tyop=fn _ => (),var=fn _ => (),const=fn _ => (),
   comb=fn _ => (),abs=fn _ => (),new_type=fn _ => (),
   new_const=fn (name,_) => names := name :: !names,
   axiom=fn _ => (),save=fn (name,_) => names := name :: !names,
   load=fn _ => raise Fail "unresolved LOAD",
   del=fn _ => (),
   del_range=fn _ => ()}
fun read_commands file command =
  let val {ruleset,...} = PFTReader.read_header {file=file,binary=true}
      val descs = PFTOpcodes.descs_for_ruleset ruleset
  in ignore (PFTReader.read {file=file,binary=true,format_handler=fh,
       ruleset_handler=fn opc => fn sr =>
         let val desc = PFTOpcodes.lookup_desc descs opc
             val id = if null (#results desc) then 0 else #readVarint sr ()
         in command (opc,id,PFTReader.read_raw_args desc sr) end})
  end
(* CONJ uses its connective through the kernel cache, not a term ID. *)
val (conj,out) = output "hol4"
val () = PFTWriter.tyop out 0 "min$bool" []
val () = PFTWriter.tyop out 1 "min$fun" [0,0]
val () = PFTWriter.tyop out 2 "min$fun" [0,1]
val () = PFTWriter.new_const out "bool$/\\" 2
val () = PFTWriter.var out 0 "p" 0
val () = PFTWriter.HOL4.assume out 0 0
val () = PFTWriter.HOL4.conj out 1 0 0
val () = PFTWriter.save out "conj$RESULT" 1
val () = finish out
val () = names := []
val () = read_commands (merged [conj] [PFTMerge.ThyAll("conj",false)])
                      (fn _ => ())
val () = check "merge retains the implicit conjunction declaration"
               (List.exists (fn name => name = "bool$/\\") (!names))

fun preserves_alias options =
  let val alias = temp ()
      val original = bytes conj
      val () = if OS.FileSys.access(alias, []) then
                 OS.FileSys.remove alias else ()
      val () = if OS.Process.isSuccess
        (Systeml.systeml (["ln"] @ options @ [conj,alias])) then ()
        else raise Fail "could not create input alias"
      val rejected =
        ((PFTMerge.merge {inputs=[conj],
            targets=[PFTMerge.ThyAll("conj",false)],output=alias,binary=true};
          false) handle Fail _ => true)
  in rejected andalso bytes conj = original andalso bytes alias = original end
val () = merge_test "merge preserves input aliased by its output"
  (fn () => preserves_alias ["-s"] andalso preserves_alias [])

(* A later SAVE must not change what an earlier LOAD imported. *)
val (rebind,out) = output "hol4"
val () = PFTWriter.tyop out 0 "min$bool" []
val () = PFTWriter.var out 0 "p" 0
val () = PFTWriter.HOL4.assume out 0 0
val () = PFTWriter.save out "rebind$X" 0
val () = PFTWriter.load out 1 "rebind$X"
val () = PFTWriter.save out "rebind$X" 1
val () = PFTWriter.save out "rebind$RESULT" 1
val () = finish out
val () = names := []
val () = read_commands
  (merged [rebind] [PFTMerge.ThyThm("rebind","RESULT",false)]) (fn _ => ())
val () = check "merge keeps the preceding SAVE binding"
  (List.exists (fn name => name = "rebind$RESULT") (!names))

(* Independent definitions with different per-target SAVE settings. *)
val (defs,out) = output "hol4"
val () = PFTWriter.tyop out 0 "min$bool" []
val () = PFTWriter.tyop out 1 "min$fun" [0,0]
val () = PFTWriter.tyop out 2 "min$fun" [1,0]
val () = PFTWriter.tyop out 3 "min$fun" [1,2]
val () = PFTWriter.const out 0 "min$=" 3
val () = PFTWriter.var out 1 "x" 0
val () = PFTWriter.abs out 2 1 1
val () = List.app (fn (base,th,name) =>
  (PFTWriter.var out base name 1;
   PFTWriter.comb out (base+1) 0 base;
   PFTWriter.comb out (base+2) (base+1) 2;
   PFTWriter.HOL4.assume out th (base+2);
   PFTWriter.HOL4.def_spec_gen out (th+1) th ["defs$" ^ name]))
  [(3,0,"a"),(6,2,"b")]
val () = PFTWriter.save out "defs$A" 1
val () = PFTWriter.save out "defs$B" 3
val () = PFTWriter.closeOut out {n_ty=4,n_tm=9,n_th=4}
val () = names := []
val () = read_commands (merged [defs]
  [PFTMerge.ThyThm("defs","A",true),PFTMerge.ThyThm("defs","B",false)])
  (fn _ => ())
val () = check "merge saves only the flagged target's definitions"
  (length (List.filter (String.isPrefix "def:") (!names)) = 1)
val () = List.app OS.FileSys.remove (!files)
