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

fun parse_address s = let
  val xs = explode s
  val _ = if hd xs = #"[" then () else fail()
  val _ = if last xs = #"]" then () else fail()
  fun f c = String.tokens (fn x => x = c)
  val ts = f #"+" (implode (butlast (tl xs)))
  fun append_lists [] = []
    | append_lists (x::xs) = x @ append_lists xs
  fun minus [x] = [("+",x)]
    | minus ["",x] = [("-",x)]
    | minus [x,y] = [("+",x),("-",y)]
    | minus (x::xs) = minus [x] @ minus xs
    | minus _ = fail()
  val zs = append_lists (map (minus o f #"-") ts)
  fun prod [x] = (1,x)
    | prod [x,y] = if can string_to_int x then (string_to_int x, y)
                                          else (string_to_int y, x)
    | prod _ = fail()
  val qs = map (fn (s,n) => (s,prod (f #"*" n))) zs
  fun g (c,(3,x)) = [(c,(1,x)),(c,(2,x))]
    | g (c,(5,x)) = [(c,(1,x)),(c,(4,x))]
    | g (c,(9,x)) = [(c,(1,x)),(c,(8,x))]
    | g y = [y]
  val us = append_lists (map g qs)
  fun extract_int ("-",(1,x)) = Arbint.-(Arbint.zero,Arbint.fromString x)
    | extract_int ("+",(1,x)) = Arbint.fromString x
    | extract_int _ = fail()
  fun sum [] = Arbint.zero | sum (i::is) = Arbint.+(i,sum is)
  val imm = sum (map extract_int (filter (can extract_int) us))
  val vs = filter (not o can extract_int) us
  val _ = if filter (fn (x,y) => not (x = "+")) vs = [] then () else fail()
  val ks = map snd vs
  val base = SOME ((snd o hd o filter (fn (x,y) => x = 1)) ks) handle e => NONE
  fun delete_base NONE xs = xs
    | delete_base (SOME b) [] = []
    | delete_base (SOME b) ((n,x)::xs) = if (1,b) = (n,x) then xs else (n,x) :: delete_base (SOME b) xs
  val index = delete_base base ks
  val index = SOME (hd index) handle e => NONE
  in (index,base,imm) end;

fun fill n s = if size s < n then fill n ("0" ^ s) else s

fun unsigned_hex n s = let
  val i = fill n (Arbnum.toHexString (Arbnum.fromString s))
  val i = (substring(i,6,2) ^ substring(i,4,2) ^ substring(i,2,2) ^
           substring(i,0,2)) handle e => i
  in if size i = n then i else fail() end

fun signed_hex n i = let
  val m = Arbnum.pow(Arbnum.fromInt 2, Arbnum.fromInt (4 * n))
  val m2 = Arbnum.pow(Arbnum.fromInt 2, Arbnum.fromInt (4 * n - 1))
  val j = Arbint.+(i,Arbint.fromNat m)
  val i = if not (Arbint.<(i,Arbint.fromNat m2)) then fail() else
          if not (Arbint.<=(Arbint.fromNat m2, j)) then fail() else
          if Arbint.<=(Arbint.zero,i) then fill n (Arbnum.toHexString(Arbint.toNat i))
                                      else fill n (Arbnum.toHexString(Arbint.toNat j))
  val i = (substring(i,6,2) ^ substring(i,4,2) ^ substring(i,2,2) ^
           substring(i,0,2)) handle e => i
  in i end

fun x86_reg2int r = let
  fun find x [] = fail()
    | find x ((y,z)::ys) = if x = y then z else find x ys
  val regs = ["EAX","ECX","EDX","EBX","ESP","EBP","ESI","EDI"]
  val indx = [0,1,2,3,4,5,6,7]
  val r = String.translate (fn x => implode [Char.toUpper x]) r
  in find r (zip regs indx) end

fun x86_address_encode s = let
  val (index,base,imm) = parse_address s
  val rr = int_to_string o x86_reg2int
  fun the (SOME x) = x | the NONE = fail()
  fun get_scale (SOME (1,i)) = [("Scale","0"),("Index",rr i)]
    | get_scale (SOME (2,i)) = [("Scale","1"),("Index",rr i)]
    | get_scale (SOME (4,i)) = [("Scale","2"),("Index",rr i)]
    | get_scale (SOME (8,i)) = [("Scale","3"),("Index",rr i)]
    | get_scale _ = fail()
  fun f (index,base,disp) =
    if index = NONE then
      if base = NONE then
        [("R/M","5"),("Mod","0"),("disp",signed_hex 8 disp)]
      else if base = SOME "ESP" then
        [("R/M",rr "ESP"),("Base","4"),("Index","4"),("Scale","0")] @
        (if disp = Arbint.fromInt 0 then [("Mod","0")]
         else if can (signed_hex 2) disp
         then [("Mod","1"),("disp",signed_hex 2 disp)]
         else [("Mod","2"),("disp",signed_hex 8 disp)])
      else if (disp = Arbint.fromInt 0) andalso not (base = SOME "EBP") then
        [("R/M",rr (the base)),("Mod","0")]
      else if can (signed_hex 2) disp then
        [("R/M",rr (the base)),("Mod","1"),("disp",signed_hex 2 disp)]
      else
        [("R/M",rr (the base)),("Mod","2"),("disp",signed_hex 8 disp)]
    else
      if base = NONE then
        [("R/M",rr "ESP"),("Mod","2"),("Base","5"),("disp",signed_hex 8 disp)]
        @ get_scale index
      else if (disp = Arbint.fromInt 0) andalso not (base = SOME "EBP") then
        [("R/M",rr "ESP"),("Mod","0"),("Base",rr (the base))] @ get_scale index
      else if can (signed_hex 2) disp then
        [("R/M",rr "ESP"),("Mod","1"),("Base",rr (the base))] @ get_scale index
        @ [("disp",signed_hex 2 disp)]
      else
        [("R/M",rr "ESP"),("Mod","2"),("Base",rr (the base))] @ get_scale index
        @ [("disp",signed_hex 8 disp)]
  in f (index,base,imm) end

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
  fun translate "r8" = "r32"
    | translate "r/m8" = "r/m32"
    | translate s = s
  val (xs,ys) = if not (mem "BYTE" xs) then (xs,ys) else
                  (filter (fn x => not (x = "BYTE")) xs,
                   map (fn (x,y) => (x, map translate y))
                   (filter (fn (x,y) => mem "r/m8" y) ys))
  fun pos x [] = fail()
    | pos x (y::ys) = if x = y then 0 else 1 + pos x ys
  fun find x [] = fail()
    | find x ((y,z)::ys) = if x = y then z else find x ys
  val regs = ["EAX","ECX","EDX","EBX","ESP","EBP","ESI","EDI"]
  fun try_all f [] = []
    | try_all f (x::xs) = f x :: try_all f xs handle e => try_all f xs
(*
  val (zs,ys) = (hd) ys
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
      else if ((x = "r/m32") orelse (x = "m")) andalso can x86_address_encode y then
        x86_address_encode y
      else fail()
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
      else fail()
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
