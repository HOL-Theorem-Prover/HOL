structure HM_Cline :> HM_Cline =
struct

type t = {
  holstate : string option,
  poly : string option,
  polymllibdir : string option,
  poly_not_hol : bool,
  time_limit : Time.time option,
  relocbuild : bool,
  core : HM_Core_Cline.t
}

local
  open FunctionalRecordUpdate
  fun makeUpdateT z = makeUpdate7 z
in
fun updateT z = let
  fun from core holstate poly polymllibdir poly_not_hol relocbuild time_limit =
    {core = core, holstate = holstate, poly = poly,
     polymllibdir = polymllibdir, poly_not_hol = poly_not_hol,
     relocbuild = relocbuild, time_limit = time_limit}
  fun from' time_limit relocbuild poly_not_hol polymllibdir poly holstate
            core =
    {core = core, holstate = holstate, poly = poly,
     polymllibdir = polymllibdir, poly_not_hol = poly_not_hol,
     relocbuild = relocbuild, time_limit = time_limit}
  fun to f {core, holstate, poly, polymllibdir, poly_not_hol, relocbuild,
            time_limit} =
    f core holstate poly polymllibdir poly_not_hol relocbuild time_limit
in
  makeUpdateT (from, from', to)
end z
val U = U
val $$ = $$
end (* local *)


val default_options = {
  core = HM_Core_Cline.default_core_options,
  holstate = NONE,
  poly = NONE,
  polymllibdir = NONE,
  poly_not_hol = false,
  relocbuild = false,
  time_limit = NONE
}

fun fupdcore f x =
  let
    val {update = u, hmakefile, no_hmf} = f x
  in
    {update = fn (wn, t : t) => updateT t (U #core (u (wn, #core t))) $$,
     hmakefile = hmakefile, no_hmf = no_hmf}
  end

open GetOpt

type core_t = HM_Core_Cline.t
type 'a cline_result = 'a HM_Core_Cline.cline_result
type 'a arg_descr = 'a GetOpt.arg_descr

fun resfn f : t cline_result = {update = f, hmakefile = NONE, no_hmf = false}

fun set_poly s =
  resfn (fn (wn, t : t) =>
            (if isSome (#poly t) then
               wn ("Poly executable already set; ignoring earlier spec")
             else ();
             updateT t (U #poly (SOME s)) $$))
fun set_polymllibdir s =
  resfn (fn (wn, t : t) =>
            (if isSome (#polymllibdir t) then
               wn ("Poly/ML lib directory already set; ignoring earlier spec")
             else ();
             updateT t (U #polymllibdir (SOME s)) $$))
fun set_holstate s =
  resfn (fn (wn, t : t) =>
            (if isSome (#holstate t) then
               wn ("HOL state-file already set; ignoring earlier spec")
             else ();
             updateT t (U #holstate (SOME s)) $$))
fun set_time_limit s =
  resfn (fn (wn, t : t) =>
            case LargeInt.fromString s of
                NONE => (wn ("Bad time string: \""^s^"\"; ignored"); t)
              | SOME i => updateT t
                                  (U #time_limit (SOME (Time.fromSeconds i)))
                                  $$)

val poly_option_descriptions = [
  {help = "specify HOL state", long = ["holstate"], short = "",
   desc = ReqArg (set_holstate, "holstate")},
  {help = "specify Poly executable", long = ["poly"], short = "",
   desc = ReqArg (set_poly, "executable")},
  {help = "use poly rather than a HOL heap", long = ["poly_not_hol"],
   short = "",
   desc = NoArg (fn () =>
                    resfn (fn (wn,t) => updateT t (U #poly_not_hol true) $$))},
  {help = "perform a relocation build", long = ["relocbuild"], short = "",
   desc = NoArg (fn () =>
                    resfn (fn (_,t) => updateT t (U #relocbuild true) $$))},
  {help = "specify Poly/ML lib directory", long = ["polymllibdir"],
   short = "",
   desc = ReqArg (set_polymllibdir, "directory")},
  {help = "set time limit (in seconds)", long = ["time_limit"], short = "t",
   desc = ReqArg (set_time_limit, "delay")}
]

fun mapd (d : core_t cline_result arg_descr) : t cline_result arg_descr =
  case d of
      NoArg f => NoArg(fupdcore f)
    | ReqArg (f, s) => ReqArg (fupdcore f, s)
    | OptArg (f, s) => OptArg (fupdcore f, s)

val option_descriptions =
    HM_Core_Cline.sort_descriptions
      (map (fn {desc,help,short,long} =>
               {desc = mapd desc, help = help, long = long, short = short})
           HM_Core_Cline.core_option_descriptions @
       poly_option_descriptions)

end
