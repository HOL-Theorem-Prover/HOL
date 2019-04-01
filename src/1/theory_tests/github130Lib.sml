structure github130Lib =
struct

open HolKernel
val _ = Feedback.WARNINGs_as_ERRs := true;
val _ = Globals.print_thy_loads := true;

val ghdata = ref [] : thm list ref
fun add_ghdata (_, th) = (ghdata := th :: !ghdata)

val {export = export_gh130, ...} = ThmSetData.new_exporter {
      settype = "gh130",
      efns = {add = fn {thy,named_thms} => List.app add_ghdata named_thms,
              remove = fn _ => ()}
    }

end
