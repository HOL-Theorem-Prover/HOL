structure SatisfySimps :> SatisfySimps =
struct

open Lib simpLib Satisfy Traverse;

val SATISFY_REDUCER =
  let val FACTDB : factdb Universal.tag = Universal.tag()
      fun get_db e = Universal.tagProject FACTDB e
  in REDUCER
    {name=SOME"SATISFY",
     initial = Universal.tagInject FACTDB ([],[]),
     apply=SATISFY_CONV o get_db o #context,
     addcontext=(fn (ctxt,thms) => Universal.tagInject FACTDB (add_facts (get_db ctxt) thms))}
  end;

val SATISFY_ss = register_frag $ name_ss "SATISFY" (dproc_ss SATISFY_REDUCER);

end (* struct *)
