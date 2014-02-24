signature assemblerLib =
sig
   type lines = {line: int, string: string} list

   exception Assembler of lines

   val dropLastChar: string -> string
   val hex: BitsN.nbit -> string
   val printLines: lines -> unit
   val printn: string -> unit
   val quote_to_strings: string quotation -> string list
   val word: int -> string -> BitsN.nbit
end
