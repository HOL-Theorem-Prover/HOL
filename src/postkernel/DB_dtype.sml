structure DB_dtype =
struct

open RawTheory_dtype
(* two flavours of "location"; the first with exactly that name is the logical/signature
   location of a theorem: it's either local to the current session/segment and is not
   going to persist, or it's bound to a particular kernelname
*)
datatype location = Local of string | Stored of KernelSig.kernelname
(* the second flavour is the location of the SML declaration and definition of the
   theorem value *)
datatype thm_src_location =
         Located of {scriptpath: string, linenum : int, exact : bool}
       | Unknown
fun inexactify_locn (Located{scriptpath,linenum,exact}) =
      Located{scriptpath=scriptpath,linenum=linenum,exact=false}
  | inexactify_locn Unknown = Unknown
fun mkloc(s,i,b) =
    Located{
      scriptpath = holpathdb.reverse_lookup{path=s},
      linenum = i,
      exact = b
    }

type thminfo = {private: bool, loc:thm_src_location,class:class}
fun updsrcloc f {private,loc,class} =
    {private = private,loc = f loc,class = class}

datatype theory =
         THEORY of string *
                   {types       : (string * int) list,
                    consts      : (string * Type.hol_type) list,
                    parents     : string list,
                    axioms      : (string * Thm.thm) list,
                    definitions : (string * Thm.thm) list,
                    theorems    : (string * Thm.thm) list}

datatype selector = SelTM of Term.term | SelNM of string | SelTHY of string
type data_value = (Thm.thm * thminfo)
type public_data_value = Thm.thm * class * thm_src_location
fun dvdrop_private ((th,i) : data_value) : public_data_value =
    (th,#class i,#loc i)
type 'a named = (string * string) * 'a
type data = data_value named
type public_data = public_data_value named
fun drop_private (nms, dv) = (nms, dvdrop_private dv)


end
