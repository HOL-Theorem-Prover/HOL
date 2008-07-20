structure SatisfySimps :> SatisfySimps =
struct

open Lib simpLib Satisfy Traverse;

val SATISFY_REDUCER =
  let exception FACTDB of factdb;
      fun get_db e = (raise e) handle FACTDB db => db
  in REDUCER
    {name=SOME"SATISFY",
     initial = FACTDB ([],[]),
     apply=SATISFY_CONV o get_db o #context,
     addcontext=(fn (ctxt,thms) => FACTDB (add_facts (get_db ctxt) thms))}
  end;

val SATISFY_ss = dproc_ss SATISFY_REDUCER;

end (* struct *)
