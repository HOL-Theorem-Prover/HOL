structure HM_Cline :> HM_Cline =
struct

type t = {
  core : HM_Core_Cline.t,
  mosmldir : string option
}

local
  open FunctionalRecordUpdate
  fun makeUpdateT z = makeUpdate2 z
in
fun updateT z = let
  fun from  core mosmldir =
    {
      mosmldir = mosmldir, core = core
    }
  fun from' mosmldir core =
    {
      mosmldir = mosmldir, core = core
    }
  fun to f {core, mosmldir} =
    f core mosmldir
in
  makeUpdateT (from, from', to)
end z
val U = U
val $$ = $$
end (* local *)


val default_options = {
  mosmldir = NONE,
  core = HM_Core_Cline.fupd_jobs (fn _ => 1) HM_Core_Cline.default_core_options
}
fun fupd_core f t = updateT t (U #core (f (#core t))) $$

(* this fupdcore function is used internally to build command-line options *)
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

fun set_mosmldir s =
  resfn (fn (wn, t : t) =>
            (if isSome (#mosmldir t) then
               wn ("Moscow ML dir already set; ignoring earlier spec")
             else ();
             updateT t (U #mosmldir (SOME s)) $$))
val mosml_option_descriptions = [
  {help = "specify Moscow ML's base directory", long = ["mosmldir"],
   short = "",
   desc = ReqArg (set_mosmldir, "directory")}
]

type core_t = HM_Core_Cline.t

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
       mosml_option_descriptions)

end
