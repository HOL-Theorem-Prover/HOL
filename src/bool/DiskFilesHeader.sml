structure DiskFilesHeader :> DiskFilesHeader =
struct
open HolKernel
type 'a updtable = { size : int ref, table : 'a array ref }
fun init {size,table} (dflt, n) = (size := 0; table := Array.array(n,dflt))
fun update {size,table} value = (Array.update(!table,!size,value);
                                 size := !size + 1)
fun lookup {size,table} i = Array.sub(!table,i)
fun new() = {size = ref 0, table = ref (Array.fromList [])}


datatype dftables = DF of { idtable : {Thy:string,Other:string} updtable,
                            tytable : hol_type updtable,
                            tmtable : term updtable }

fun type_init (DF t) n = init (#tytable t) (Type.alpha, n)
fun lookup_type (DF t) i = lookup (#tytable t) i
fun newtype ty (DF t) = update (#tytable t) ty

fun term_init (DF t) n = init (#tmtable t) (mk_var("ERR", alpha), n)
fun lookup_term (DF t) i = lookup (#tmtable t) i
fun newterm (DF t) tm = update (#tmtable t) tm

fun id_init (DF t) n = init (#idtable t) ({Thy="",Other=""}, n)
fun lookup_id (DF t) i = lookup (#idtable t) i
fun newid (DF t) id = update (#idtable t) id

fun initial_tables() = DF {idtable = new(), tytable = new(), tmtable = new()}

end;
