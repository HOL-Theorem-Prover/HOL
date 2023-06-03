signature KernelSig =
sig

  type kernelname = {Thy : string, Name : string}
  val name_compare : kernelname * kernelname -> order
  val name_toString : kernelname -> string
  val name_toMLString : kernelname -> string

  eqtype kernelid

  val id_compare : kernelid * kernelid -> order
  val name_of_id : kernelid -> kernelname
  val id_toString : kernelid -> string
  val new_id : kernelname -> kernelid
  val uptodate_id : kernelid -> bool
  val retire_id : kernelid -> unit
  val name_of : kernelid -> string
  val seg_of : kernelid -> string

  type 'a symboltable
  datatype 'a symtab_error = Success of 'a
                           | Failure of exn
  val isSuccess : 'a symtab_error -> bool
  exception NoSuchThy of string
  exception NotPresent of kernelname
  val new_table : unit -> 'a symboltable
  val insert : 'a symboltable * kernelname * 'a -> kernelid
  val find : 'a symboltable * kernelname -> kernelid * 'a
  val peek : 'a symboltable * kernelname -> (kernelid * 'a) symtab_error

  val numItems : 'a symboltable -> int
  val listItems : 'a symboltable -> (kernelname * (kernelid * 'a)) list
  val listThy : 'a symboltable -> string -> (kernelname * (kernelid * 'a)) list
  val listName : 'a symboltable -> string -> (kernelname * (kernelid * 'a)) list

  val app : (kernelname * (kernelid * 'a) -> unit) -> 'a symboltable -> unit
  val foldl : (kernelname * (kernelid * 'a) * 'b -> 'b) -> 'b ->
              'a symboltable -> 'b
  val retire_name : 'a symboltable * kernelname -> unit
  val uptodate_name : 'a symboltable * kernelname -> bool
  val del_segment : 'a symboltable * string -> unit

end
