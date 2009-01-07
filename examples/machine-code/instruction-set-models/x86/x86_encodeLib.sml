structure x86_encodeLib :> x86_encodeLib =
struct

open HolKernel boolLib bossLib;
open x86_decoderTheory;

val car = fst o dest_comb;
val cdr = snd o dest_comb;

val instructions = let 
  fun div_at [] ys = (ys,[])
    | div_at (x::xs) ys = if x = "|" then (rev ys,xs) else
      div_at xs (x::ys)
  fun d xs = div_at xs []
  val t = String.tokens (fn x => mem x [#" ",#","])
  in (map (d o t) o map stringSyntax.fromHOLstring o fst o 
     listSyntax.dest_list o cdr o cdr o concl o SPEC_ALL) x86_decode_aux_def end;

fun x86_encode s = let
  fun rem [] b ys = rev ys
    | rem (x::xs) b ys = 
         if x = #"[" then rem xs true (x::ys) else
         if x = #"]" then rem xs false (x::ys) else
         if x = #" " then if b then rem xs b ys else rem xs b (x::ys) else
           rem xs b (x::ys)
  val s = implode (rem (explode s) false [])
  val s = String.translate (fn x => implode [Char.toUpper x]) s
  val xs = String.tokens (fn x => mem x [#" ",#","]) s
  val ys = filter (fn (x,y) => ((hd y = hd xs) handle _ => false)) instructions
  fun pos x [] = hd []
    | pos x (y::ys) = if x = y then 0 else 1 + pos x ys
  fun find x [] = hd []
    | find x ((y,z)::ys) = if x = y then z else find x ys
  val regs = ["EAX","ECX","EDX","EBX","ESP","EBP","ESI","EDI"] 
  fun fill n s = if size s < n then fill n ("0" ^ s) else s
  fun try_all f [] = []
    | try_all f (x::xs) = f x :: try_all f xs handle e => try_all f xs
  fun unsigned_hex n s = let
    val i = fill n (Arbnum.toHexString (Arbnum.fromString s))
    val i = (substring(i,6,2) ^ substring(i,4,2) ^ substring(i,2,2) ^ 
             substring(i,0,2)) handle e => i
    in if size i = n then i else hd [] end
  fun signed_hex n i = let
    val m = Arbnum.pow(Arbnum.fromInt 2, Arbnum.fromInt (4 * n))
    val m2 = Arbnum.pow(Arbnum.fromInt 2, Arbnum.fromInt (4 * n - 1))
    val j = Arbint.+(i,Arbint.fromNat m)
    val i = if not (Arbint.<(i,Arbint.fromNat m2)) then hd [] else
            if not (Arbint.<=(Arbint.fromNat m2, j)) then hd [] else
            if Arbint.<=(Arbint.zero,i) then fill n (Arbnum.toHexString(Arbint.toNat i))
                                        else fill n (Arbnum.toHexString(Arbint.toNat j))
    val i = (substring(i,6,2) ^ substring(i,4,2) ^ substring(i,2,2) ^ 
             substring(i,0,2)) handle e => i
    in i end
  fun parse_address s = let
    val xs = explode s
    val _ = if hd xs = #"[" then () else hd []
    val _ = if last xs = #"]" then () else hd []
    val ys = String.tokens (fn x => mem x [#" ",#"-",#"+"]) (implode (butlast (tl xs)))
    val m = if can (pos #"-") xs then Arbint.fromInt (0 - 1) else Arbint.fromInt 1  
    val i = Arbint.fromString (hd (filter (can Arbint.fromString) ys @ ["0"]))
    val ys = filter (not o can Arbint.fromString) ys
    val i = Arbint.*(i,m)
    in (pos (hd ys) regs, i) end
(*
  val (zs,ys) = (hd o tl o tl) ys
*)
  fun use_encoding (zs,ys) = let
    val l = filter (fn (x,y) => not (x = y)) (zip xs ys)
    fun foo (y,x) = 
      if x = "imm32" then 
        [("id",unsigned_hex 8 y)]
      else if x = "imm16" then 
        [("iw",signed_hex 4 (Arbint.fromString y))]
      else if x = "imm8" then 
        [("ib",signed_hex 2 (Arbint.fromString y))]
      else if x = "rel8" then 
        [("cb",signed_hex 2 (Arbint.fromString y))]
      else if x = "rel32" then 
        [("cd",signed_hex 8 (Arbint.fromString y))]
      else if x = "r32" then 
        [("Reg/Opcode",int_to_string (pos y regs))] 
      else if (x = "r/m32") andalso (mem y regs) then 
        [("R/M",int_to_string (pos y regs)),("Mod","3")] 
      else if (x = "r/m32") andalso can parse_address y then let
        val (r,disp) = parse_address y
        in if (disp = Arbint.fromInt 0) andalso not (r = 5) then 
          if r = 4 then (* r is ESP, i.e. SIB byte needed *)
            [("R/M",int_to_string r),("Mod","0"),("Base","4"),("Index","4"),
             ("Scale","0")]
          else
            [("R/M",int_to_string r),("Mod","0")]          
        else if not (r = 4) then
          [("R/M",int_to_string r),("Mod","1"),
           ("disp",signed_hex 2 disp)] handle e =>
          [("R/M",int_to_string r),("Mod","2"),
           ("disp",signed_hex 8 disp)] 
        else (* r is ESP, i.e. SIB byte needed *)
          [("R/M",int_to_string r),("Mod","1"),("Base","4"),("Index","4"),
           ("disp",signed_hex 2 disp),("Scale","0")] handle e =>
          [("R/M",int_to_string r),("Mod","2"),("Base","4"),("Index","4"),
           ("disp",signed_hex 8 disp),("Scale","0")] end 
      else hd []
    fun list_append [] = [] | list_append (x::xs) = x @ list_append xs
    val ts = list_append (map foo l)
    fun create_SIB xs = 
      (fill 2 o Arbnum.toHexString o Arbnum.fromInt) 
      (string_to_int (find "Base" xs) +
       string_to_int (find "Index" xs) * 8 +
       string_to_int (find "Scale" xs) * 8 * 8) handle _ => ""
    fun create_ModRM xs = 
      (fill 2 o Arbnum.toHexString o Arbnum.fromInt) 
      (string_to_int (find "R/M" xs) +
       string_to_int (find "Reg/Opcode" xs) * 8 +
       string_to_int (find "Mod" xs) * 8 * 8) ^ 
      create_SIB xs ^ (find "disp" ts handle e => "")    
    fun is_plus x = (implode (tl (tl (explode x))) = "+rd") handle _ => false
    fun do_replace x = 
      if mem x ["id","iw","ib","cb","cw","cd"] then find x ts else 
      if is_plus x then let
        val reg = Arbnum.fromString(find "Reg/Opcode" ts)
        val s = implode [hd (explode x), hd (tl (explode x))]
        in Arbnum.toHexString(Arbnum.+(Arbnum.fromHexString s, reg)) end else
      if can Arbnum.fromHexString x then x else
      if x = "/r" then create_ModRM ts else
      if hd (explode x) = #"/" then  
        create_ModRM (("Reg/Opcode",(implode o tl o explode) x)::ts)
      else hd []
    val e = concat (map do_replace zs) 
    in e end;
  val all = try_all use_encoding ys
  val e = hd (sort (fn x => fn y => size x <= size y) all)
  in e end   

(* fails for [reg+reg+imm], [reg+reg], [4*reg], [2*reg], ... *)

fun x86_supported_instructions () = let
  fun all_distinct [] = []
    | all_distinct (x::xs) = x::all_distinct (filter (fn y => not ((x:string) = y)) xs)
  in all_distinct (map (fn (x,y) => hd y) instructions) end;


end
