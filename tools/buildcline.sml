structure buildcline :> buildcline =
struct

open buildcline_dtype GetOpt

type 'a cline_result = { update : (string -> unit) * 'a -> 'a }

local
  open FunctionalRecordUpdate
  fun makeUpdateT z = makeUpdate7 z
in
fun updateT z = let
  fun from build_theory_graph help jobcount kernelspec relocbuild selftest
           seqname =
    {build_theory_graph = build_theory_graph,
     help = help,
     jobcount = jobcount,
     kernelspec = kernelspec,
     relocbuild = relocbuild,
     selftest = selftest,
     seqname = seqname}
  fun from' seqname selftest relocbuild kernelspec jobcount help
            build_theory_graph =
    {build_theory_graph = build_theory_graph,
     help = help,
     jobcount = jobcount,
     kernelspec = kernelspec,
     relocbuild = relocbuild,
     selftest = selftest,
     seqname = seqname}
  fun to f {build_theory_graph, help, jobcount, kernelspec, relocbuild,
            selftest, seqname} =
    f build_theory_graph help jobcount kernelspec relocbuild selftest seqname
in
  makeUpdateT (from, from', to)
end z
val U = U
val $$ = $$
end (* local *)

fun mkBool sel (b:bool) =
  NoArg (fn () => { update = fn (wn,t) => updateT t (U sel b) $$ })
fun mkBoolOpt sel (b:bool) =
  NoArg (fn () => { update = fn (wn,t) => updateT t (U sel (SOME b)) $$ })

fun mkInt nm sel =
  ReqArg ((fn s => { update = fn (wn,t) =>
             case Int.fromString s of
                 NONE => (wn ("Couldn't read integer from "^s); t)
               | SOME i => if i < 0 then
                             (wn ("Ignoring negative number for "^nm); t)
                           else
                             updateT t (U sel i) $$ }),
          "int")
fun mkIntOpt nm sel =
  ReqArg ((fn s => { update = fn (wn,t) =>
             case Int.fromString s of
                 NONE => (wn ("Couldn't read integer from "^s); t)
               | SOME i => if i < 0 then
                             (wn ("Ignoring negative number for "^nm); t)
                           else updateT t (U sel (SOME i)) $$ }),
          "int")

val setSeqNameOnce =
  ReqArg ((fn s => { update = fn (wn,t) =>
             (case #seqname t of
                 NONE => ()
               | SOME _ =>
                 wn ("Multiple --seq specs; ignoring earlier spec(s)");
              updateT t (U #seqname (SOME s)) $$) }),
          "fname")



val cline_opt_descrs = [
  {help = "build a theory dependency graph", long = ["graph"], short = "",
   desc = mkBoolOpt #build_theory_graph true},
  {help = "don't build a thy dep. graph", long = ["nograph"], short = "",
   desc = mkBoolOpt #build_theory_graph false},
  {help = "specify selftest level", long = ["selftest"], short = "t",
   desc = mkInt "selftest" #selftest},
  {help = "specify concurrency limit", long = [], short = "j",
   desc = mkIntOpt "-j" #jobcount},
  {help = "display help", long = ["help", "h"], short = "h",
   desc = mkBool #help true},
  {help = "do relocation build", long = ["relocbuild"], short = "",
   desc = mkBool #relocbuild true},
  {help = "build this directory sequence", long = ["seq"], short = "",
   desc = setSeqNameOnce}
]

end (* struct *)
