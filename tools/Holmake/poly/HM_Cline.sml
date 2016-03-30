structure HM_Cline :> HM_Cline =
struct

type t = {
  holstate : string option,
  poly : string option,
  polymllibdir : string option,
  poly_not_hol : bool,
  core : HM_Core_Cline.t
}

local
  open FunctionalRecordUpdate
  fun makeUpdateT z = makeUpdate5 z
in
fun updateT z = let
  fun from core holstate poly polymllibdir poly_not_hol =
    {core = core, holstate = holstate, poly = poly,
     polymllibdir = polymllibdir, poly_not_hol = poly_not_hol}
  fun from' poly_not_hol polymllibdir poly holstate core =
    {core = core, holstate = holstate, poly = poly,
     polymllibdir = polymllibdir, poly_not_hol = poly_not_hol}
  fun to f {core, holstate, poly, polymllibdir, poly_not_hol} =
    f  core holstate poly polymllibdir poly_not_hol
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
  poly_not_hol = false
}

fun fupdcore f (wn, t : t) : t =
  updateT t (U #core (f (wn, #core t))) $$

open GetOpt
fun set_poly s (wn, t : t) : t =
  (if isSome (#poly t) then
     wn ("Poly executable already set; ignoring earlier spec")
   else ();
   updateT t (U #poly (SOME s)) $$)
fun set_polymllibdir s (wn, t : t) : t =
  (if isSome (#polymllibdir t) then
     wn ("Poly/ML lib directory already set; ignoring earlier spec")
   else ();
   updateT t (U #polymllibdir (SOME s)) $$)
fun set_holstate s (wn, t : t) : t =
  (if isSome (#holstate t) then
     wn ("HOL state-file already set; ignoring earlier spec")
   else ();
   updateT t (U #holstate (SOME s)) $$)
val poly_option_descriptions = [
  {help = "specify HOL state", long = ["holstate"], short = "",
   desc = ReqArg (set_holstate, "holstate")},
  {help = "specify Poly executable", long = ["poly"], short = "",
   desc = ReqArg (set_poly, "executable")},
  {help = "use poly rather than a HOL heap", long = ["poly_not_hol"],
   short = "",
   desc = NoArg (fn () => fn (wn,t) => updateT t (U #poly_not_hol true) $$)},
  {help = "specify Poly/ML lib directory", long = ["polymllibdir"],
   short = "",
   desc = ReqArg (set_polymllibdir, "directory")}
]

type core_t = HM_Core_Cline.t

fun mapd
      (d : ((string -> unit) * core_t -> core_t) GetOpt.arg_descr)
    : ((string -> unit) * t -> t) GetOpt.arg_descr
=
  case d of
      NoArg f => NoArg(fupdcore o f)
    | ReqArg (f, s) => ReqArg (fupdcore o f, s)
    | OptArg (f, s) => OptArg (fupdcore o f, s)

val option_descriptions =
    HM_Core_Cline.sort_descriptions
      (map (fn {desc,help,short,long} =>
               {desc = mapd desc, help = help, long = long, short = short})
           HM_Core_Cline.core_option_descriptions @
       poly_option_descriptions)

end
