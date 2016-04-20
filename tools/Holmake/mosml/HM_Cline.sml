structure HM_Cline :> HM_Cline =
struct

type t = {
  core : HM_Core_Cline.t,
  mosmldir : string option,
  no_basis2002 : bool
}

local
  open FunctionalRecordUpdate
  fun makeUpdateT z = makeUpdate3 z
in
fun updateT z = let
  fun from  core mosmldir no_basis2002 =
    {
      no_basis2002 = no_basis2002, mosmldir = mosmldir, core = core
    }
  fun from' no_basis2002 mosmldir core =
    {
      no_basis2002 = no_basis2002, mosmldir = mosmldir, core = core
    }
  fun to f {core, mosmldir, no_basis2002} =
    f core mosmldir no_basis2002
in
  makeUpdateT (from, from', to)
end z
val U = U
val $$ = $$
end (* local *)


val default_options = {
  no_basis2002 = false,
  mosmldir = NONE,
  core = fupd_jobs (fn _ => 1) HM_Core_Cline.default_core_options
}


fun fupdcore f (wn, t : t) : t =
  updateT t (U #core (f (wn, #core t))) $$

open GetOpt
fun set_mosmldir s (wn, t : t) : t =
  (if isSome (#mosmldir t) then
     wn ("Moscow ML dir already set; ignoring earlier spec")
   else ();
   updateT t (U #mosmldir (SOME s)) $$)
val mosml_option_descriptions = [
  {help = "don't use HOL's provided basis 2002", long = ["no_basis2002"],
   short = "",
   desc = NoArg (fn () => fn (wn,t) => updateT t (U #no_basis2002 true) $$)},
  {help = "specify Moscow ML's base directory", long = ["mosmldir"],
   short = "",
   desc = ReqArg (set_mosmldir, "directory")}
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
       mosml_option_descriptions)

end
