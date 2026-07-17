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
  val name_of : kernelid -> string
  val seg_of : kernelid -> string
  val epoch_of : kernelid -> int

  type 'a symboltable
  datatype 'a symtab_error = Success of 'a
                           | Failure of exn
  val isSuccess : 'a symtab_error -> bool
  exception NoSuchThy of string
  exception NotPresent of kernelname
  val empty_table : 'a symboltable
  val insert : kernelname * 'a -> 'a symboltable -> 'a symboltable * kernelid
  val find : 'a symboltable * kernelname -> kernelid * 'a
  val peek : 'a symboltable * kernelname -> (kernelid * 'a) symtab_error
  val symtab_epoch : 'a symboltable -> int

  val numItems : 'a symboltable -> int
  val listItems : 'a symboltable -> (kernelname * (kernelid * 'a)) list
  val listThy : 'a symboltable -> string -> (kernelname * (kernelid * 'a)) list
  val listName : 'a symboltable -> string -> (kernelname * (kernelid * 'a)) list
  val nameExists : 'a symboltable -> string -> bool
  val thyExists : 'a symboltable -> string -> bool

  val app : (kernelname * (kernelid * 'a) -> unit) -> 'a symboltable -> unit
  val foldl : (kernelname * (kernelid * 'a) * 'b -> 'b) -> 'b ->
              'a symboltable -> 'b
  val del_segment : string -> 'a symboltable -> 'a symboltable

  val uptodate_id : 'a symboltable -> kernelid -> bool
  val display_name_of_id : 'a symboltable -> kernelid -> string
    (* oldified iff retired *)
  val retire_name : kernelname -> 'a symboltable ->
                    'a symboltable * (kernelid * 'a) symtab_error

end
