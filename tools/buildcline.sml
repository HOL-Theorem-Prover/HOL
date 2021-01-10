structure buildcline :> buildcline =
struct

open buildcline_dtype GetOpt

type 'a cline_result = {
  update : {warn:string -> unit, die:string -> unit, arg:'a} -> 'a
}

local
  open FunctionalRecordUpdate
  fun makeUpdateT z = makeUpdate9 z
in
fun updateT z = let
  fun from build_theory_graph debug help jobcount kernelspec multithread
           relocbuild selftest
           seqname =
    {build_theory_graph = build_theory_graph,
     debug = debug,
     help = help,
     jobcount = jobcount,
     kernelspec = kernelspec,
     multithread = multithread,
     relocbuild = relocbuild,
     selftest = selftest,
     seqname = seqname}
  fun from' seqname selftest relocbuild multithread kernelspec jobcount help
            debug
            build_theory_graph =
    {build_theory_graph = build_theory_graph,
     debug = debug,
     help = help,
     jobcount = jobcount,
     kernelspec = kernelspec,
     multithread = multithread,
     relocbuild = relocbuild,
     selftest = selftest,
     seqname = seqname}
  fun to f {build_theory_graph, debug, help, jobcount, kernelspec, multithread,
            relocbuild,
            selftest, seqname} =
    f build_theory_graph debug help jobcount kernelspec multithread relocbuild
      selftest
      seqname
in
  makeUpdateT (from, from', to)
end z
val U = U
val $$ = $$
end (* local *)

fun mkBool sel (b:bool) =
  NoArg (fn () => { update = fn {warn,die,arg} => updateT arg (U sel b) $$ })
fun mkBoolOpt sel (b:bool) =
  NoArg (fn () => { update =
                    fn {warn,die,arg} => updateT arg (U sel (SOME b)) $$ })

fun mkInt nm sel =
  ReqArg ((fn s => { update = fn {warn=wn,die,arg} =>
             case Int.fromString s of
                 NONE => (die ("Couldn't read integer from "^s); arg)
               | SOME i => if i < 0 then
                             (wn ("Ignoring negative number for "^nm); arg)
                           else
                             updateT arg (U sel i) $$ }),
          "int")
fun mkIntOpt nm sel =
  ReqArg ((fn s => { update = fn {warn=wn,die,arg} =>
             case Int.fromString s of
                 NONE => (die ("Couldn't read integer from "^s); arg)
               | SOME i => if i < 0 then
                             (wn ("Ignoring negative number for "^nm); arg)
                           else updateT arg (U sel (SOME i)) $$ }),
          "int")

datatype res = Bad of string | OK of int
fun optInt nm dflt sel = let
  fun doit ires {warn=wn,die,arg=t} =
    case ires of
        Bad s => (die ("Couldn't read integer from "^s); t)
      | OK i => if i < 0 then
                  (wn ("Ignoring negative number for " ^ nm); t)
                else
                  updateT t (U sel (SOME i)) $$
  fun readInt s =
    case Int.fromString s of
        NONE => Bad s
      | SOME i => OK i
in
  OptArg ((fn sopt =>
              case sopt of
                  NONE => {update = doit (OK dflt)}
                | SOME i_s => {update = doit (readInt i_s)}), "int")
end

val setSeqNameOnce =
  ReqArg ((fn s => { update = fn {warn=wn,die,arg=t} =>
             (case #seqname t of
                 NONE => ()
               | SOME _ =>
                 wn "Multiple sequence specs; ignoring earlier spec(s)";
              updateT t (U #seqname (SOME s)) $$) }),
          "fname")

fun setKname k =
  NoArg (fn () =>
            { update =
              fn {warn=wn,arg=t,die} =>
                 (case #kernelspec t of
                      NONE => ()
                    | SOME _ => wn "Multiple kernel specs; \
                                   \ignoring earlier spec(s)";
                  updateT t (U #kernelspec (SOME k)) $$) })

val cline_opt_descrs = [
  {help = "build with experimental kernel", long = ["expk"], short = "",
   desc = setKname "--expk"},
  {help = "build a theory dependency graph", long = ["graph"], short = "",
   desc = mkBoolOpt #build_theory_graph true},
  {help = "build with full sequence", long = ["fullbuild"], short = "F",
   desc = NoArg (fn () => {
     update = fn {warn=wn,arg=t,die} =>
       (case #seqname t of
           NONE => ()
         | SOME _ => wn "Multiple sequence specs; ignoring earlier spec(s)";
        updateT t (U #seqname (SOME "")) $$) })},
  {help = "enable debugging output", long = ["dbg"], short = "d",
   desc = mkBool #debug true},
  {help = "display help", long = ["help", "h"], short = "h?",
   desc = mkBool #help true},
  {help = "specify concurrency limit", long = [], short = "j",
   desc = mkIntOpt "-j" #jobcount},
  {help = "thread count", long = ["mt"], short = "",
   desc = optInt "thread count" 0 #multithread},
  {help = "don't build a thy dep. graph", long = ["nograph"], short = "",
   desc = mkBoolOpt #build_theory_graph false},
  {help = "build with logging kernel", long = ["otknl"], short = "",
   desc = setKname "--otknl"},
  {help = "do relocation build (e.g., after a cleanForReloc)",
   long = ["relocbuild"], short = "",
   desc = mkBool #relocbuild true},
  {help = "specify selftest level (default = 1)", long = ["selftest"],
   short = "t",
   desc = optInt "selftest level" 1 #selftest},
  {help = "build this directory sequence", long = ["seq"], short = "",
   desc = setSeqNameOnce},
  {help = "build with standard kernel", long = ["stdknl"], short = "",
   desc = setKname "--stdknl"}
]

end (* struct *)
