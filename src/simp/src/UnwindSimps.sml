structure UnwindSimps :> UnwindSimps = 
struct
open Lib simpLib Parse;

(*------------------------------------------------------------------------
 * UNWIND_ss
 *------------------------------------------------------------------------*)

val UNWIND_ss = SIMPSET
  {convs=[{name="UNWIND_EXISTS_CONV",
           trace=1,
           key=SOME ([],(--`?x:'a. P`--)),
           conv=K (K Unwind.UNWIND_EXISTS_CONV)},
          {name="UNWIND_FORALL_CONV",
           trace=1,
           key=SOME ([],(--`!x:'a. P`--)),
           conv=K (K Unwind.UNWIND_FORALL_CONV)}],
   rewrs=[],filter=NONE,ac=[],dprocs=[],congs=[]};

end;
