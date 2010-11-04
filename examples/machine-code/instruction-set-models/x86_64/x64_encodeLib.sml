structure x64_encodeLib :> x64_encodeLib =
struct

open HolKernel boolLib bossLib;
open x64_decoderTheory;

val car = fst o dest_comb;
val cdr = snd o dest_comb;

val instructions = let
  fun div_at [] ys = (ys,[])
    | div_at (x::xs) ys = if x = "|" then (rev ys,xs) else
      div_at xs (x::ys)
  fun d xs = div_at xs []
  val t = String.tokens (fn x => mem x [#" ",#","])
  in (map (d o t) o map stringSyntax.fromHOLstring o fst o
     listSyntax.dest_list o cdr o cdr o concl o SPEC_ALL) x64_decode_aux_def end;

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
  val i = (substring(i,14,2) ^ substring(i,12,2) ^ substring(i,10,2) ^ substring(i,8,2) ^ 
           substring(i,6,2) ^ substring(i,4,2) ^ substring(i,2,2) ^ substring(i,0,2)) handle e => 
          (substring(i,6,2) ^ substring(i,4,2) ^ substring(i,2,2) ^ substring(i,0,2)) handle e => i
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

local 
  fun add_reg_type ty xs = map (fn x => (x,ty)) xs 
  val x64_regs =
    zip ["AL","CL","DL","BL","SPL","BPL","SIL","DIL"] (add_reg_type 8 [0,1,2,3,4,5,6,7]) @
    zip ["AX","CX","DX","BX","SP","BP","SI","DI"] (add_reg_type 16 [0,1,2,3,4,5,6,7]) @
    zip ["EAX","ECX","EDX","EBX","ESP","EBP","ESI","EDI"] (add_reg_type 32 [0,1,2,3,4,5,6,7]) @
    zip ["RAX","RCX","RDX","RBX","RSP","RBP","RSI","RDI"] (add_reg_type 64 [0,1,2,3,4,5,6,7]) @
    zip ["R8B","R9B","R10B","R11B","R12B","R13B","R14B","R15B"] (add_reg_type 8 [8,9,10,11,12,13,14,15]) @
    zip ["R8W","R9W","R10W","R11W","R12W","R13W","R14W","R15W"] (add_reg_type 16 [8,9,10,11,12,13,14,15]) @
    zip ["R8D","R9D","R10D","R11D","R12D","R13D","R14D","R15D"] (add_reg_type 32 [8,9,10,11,12,13,14,15]) @
    zip ["R8","R9","R10","R11","R12","R13","R14","R15"] (add_reg_type 64 [8,9,10,11,12,13,14,15]) @
    zip ["R0B","R1B","R2B","R3B","R4B","R5B","R6B","R7B"] (add_reg_type 8 [0,1,2,3,4,5,6,7]) @
    zip ["R0W","R1W","R2W","R3W","R4W","R5W","R6W","R7W"] (add_reg_type 16 [0,1,2,3,4,5,6,7]) @
    zip ["R0D","R1D","R2D","R3D","R4D","R5D","R6D","R7D"] (add_reg_type 32 [0,1,2,3,4,5,6,7]) @
    zip ["R0","R1","R2","R3","R4","R5","R6","R7"] (add_reg_type 64 [0,1,2,3,4,5,6,7])
  fun x64_reg_info r = let
    fun find x [] = fail()
      | find x ((y,z)::ys) = if x = y then z else find x ys
    val r = String.translate (fn x => implode [Char.toUpper x]) r
    in find r x64_regs end
in
  fun x64_reg2int r = fst (x64_reg_info r);
  fun x64_reg_size r = snd (x64_reg_info r);
  fun x64_is_reg r = can x64_reg_info r;
end;

fun x64_address_encode s = let
  val (index,base,disp) = parse_address s
  val rr = int_to_string o x64_reg2int
  fun the (SOME x) = x | the NONE = fail()
  fun get_scale (SOME (1,i)) = [("Scale","0"),("Index",rr i)]
    | get_scale (SOME (2,i)) = [("Scale","1"),("Index",rr i)]
    | get_scale (SOME (4,i)) = [("Scale","2"),("Index",rr i)]
    | get_scale (SOME (8,i)) = [("Scale","3"),("Index",rr i)]
    | get_scale _ = fail()
  fun is_SP (SOME s) = (x64_reg2int s = 5) | is_SP _ = false 
  fun is_BP (SOME s) = (x64_reg2int s = 6) | is_BP _ = false 
  fun f (index,base,disp) =
    if index = NONE then
      if base = NONE then
        [("R/M","5"),("Mod","0"),("disp",signed_hex 8 disp)]
      else if is_SP base then
        [("R/M",rr "ESP"),("Base","4"),("Index","4"),("Scale","0")] @
        (if disp = Arbint.fromInt 0 then [("Mod","0")]
         else if can (signed_hex 2) disp
         then [("Mod","1"),("disp",signed_hex 2 disp)]
         else [("Mod","2"),("disp",signed_hex 8 disp)])
      else if (disp = Arbint.fromInt 0) andalso not (is_BP base) then
        [("R/M",rr (the base)),("Mod","0")]
      else if can (signed_hex 2) disp then
        [("R/M",rr (the base)),("Mod","1"),("disp",signed_hex 2 disp)]
      else
        [("R/M",rr (the base)),("Mod","2"),("disp",signed_hex 8 disp)]
    else
      if base = NONE then
        [("R/M",rr "ESP"),("Mod","2"),("Base","5"),("disp",signed_hex 8 disp)]
        @ get_scale index
      else if (disp = Arbint.fromInt 0) andalso not (is_BP base) then
        [("R/M",rr "ESP"),("Mod","0"),("Base",rr (the base))] @ get_scale index
      else if can (signed_hex 2) disp then
        [("R/M",rr "ESP"),("Mod","1"),("Base",rr (the base))] @ get_scale index
        @ [("disp",signed_hex 2 disp)]
      else
        [("R/M",rr "ESP"),("Mod","2"),("Base",rr (the base))] @ get_scale index
        @ [("disp",signed_hex 8 disp)]
  in f (index,base,disp) end

fun x64_encode s = let
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
  fun token_data_size t = 
    if mem t ["r8","r/m8"] then 8 else
    if mem t ["r16","r/m16"] then 16 else
    if mem t ["r32","r/m32"] then 32 else
    if mem t ["r64","r/m64"] then 64 else 
    if x64_is_reg t then x64_reg_size t else fail();
  fun every p [] = true | every p (x::xs) = p x andalso every p xs
  val use_default_size = every (fn (x,y) => every (fn t => not (can token_data_size t)) y) ys
                         orelse mem (hd xs) ["CALL","JMP"]
  val zsize = if use_default_size then 64 else 
              x64_reg_size (hd (filter x64_is_reg xs))
              handle Empty => if mem "BYTE" xs then 8 else
                              if mem "WORD" xs then 16 else 
                              if mem "DWORD" xs then 32 else
                              if mem "QWORD" xs then 64 else
                                (print ("\n\nERROR: Specify data size using BYTE, WORD, DWORD or QWORD in "^s^".\n\n"); fail())
  val ys = if not (hd xs = "MOVZX") then ys else let
             val x = el 3 xs
             val s = if x64_is_reg x then x64_reg_size x else
                       if x = "WORD" then 16 else 
                       if x = "BYTE" then 8 else fail()
             val _ = if mem s [8,16] then () else fail()
             in filter (fn (x,y) => token_data_size (el 3 y) = s) ys end
  val ys = if not ((hd xs = "MOV") andalso (zsize = 64) andalso (can string_to_int (last xs))) then ys else
             ys |> filter (fn (x,y) => last y = "imm64") 
                |> map (fn (x,y) => (filter (fn t => not (mem t ["REX.W","+"])) x,y)) 
  val xs = filter (fn x => not (mem x ["BYTE","WORD","DWORD","QWORD"])) xs
  val prefixes = if zsize = 16 then "66" else ""
  fun intro_eax s = (if (x64_reg2int s = 0) then "EAX" else s) handle HOL_ERR _ => s
  val xs = map intro_eax xs
  fun pos x [] = fail()
    | pos x (y::ys) = if x = y then 0 else 1 + pos x ys
  fun find x [] = fail()
    | find x ((y,z)::ys) = if x = y then z else find x ys
  fun try_all f [] = []
    | try_all f (x::xs) = f x :: try_all f xs handle e => try_all f xs
  val ys = if zsize = 8 then filter (fn (x,y) => (token_data_size (el 2 y) = 8) handle HOL_ERR _ => true) ys 
                        else filter (fn (x,y) => not (token_data_size (el 2 y) = 8) handle HOL_ERR _ => true) ys
  fun simplify_token t = 
    if mem t ["r8","r16","r32","r64"] then "r32" else
    if mem t ["r/m8","r/m16","r/m32","r/m64"] then "r/m32" else t;  
  val ys = map (fn (x,y) => (x,map simplify_token y)) ys
(*
  val (zs,ys) = el 2 ys 
*)
  fun use_encoding (zs,ys) = let
    val rex = ref (if zsize = 64 then [#"W"] else [])
    fun rex_prefix() = 
      if (!rex) = [] then "" else
        signed_hex 2 (Arbint.fromInt (4 * 16 + (if mem #"W" (!rex) then 8 else 0)
                                             + (if mem #"R" (!rex) then 4 else 0)
                                             + (if mem #"X" (!rex) then 2 else 0)
                                             + (if mem #"B" (!rex) then 1 else 0)))
    val l = filter (fn (x,y) => not (x = y)) (zip xs ys)
    fun foo (y,x) =
      if x = "imm64" then
        [("iq",unsigned_hex 16 y)]
      else if x = "imm32" then
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
        [("Reg/Opcode",int_to_string (x64_reg2int y))]
      else if (x = "r/m32") andalso (x64_is_reg y) then
        [("R/M",int_to_string (x64_reg2int y)),("Mod","3")]
      else if ((x = "r/m32") orelse (x = "m")) andalso can x64_address_encode y then
        x64_address_encode y
      else fail()
    fun list_append [] = [] | list_append (x::xs) = x @ list_append xs
    val ts = list_append (map foo l)
    fun string_to_int_8 s c = let
      val n = string_to_int s
      val _ = (if 8 <= n then (rex := c::(!rex)) else ())
      val _ = (if 4 <= n andalso (zsize = 8) then (rex := #" "::(!rex)) else ())
      in n mod 8 end;
    fun create_SIB xs =
      (fill 2 o Arbnum.toHexString o Arbnum.fromInt)
      (string_to_int_8 (find "Base" xs) #"B" +
       string_to_int_8 (find "Index" xs) #"X" * 8 +
       string_to_int (find "Scale" xs) * 8 * 8) handle _ => ""
    fun create_ModRM xs =
      (fill 2 o Arbnum.toHexString o Arbnum.fromInt)
      (string_to_int_8 (find "R/M" xs) #"B" +
       string_to_int_8 (find "Reg/Opcode" xs) #"R" * 8 +
       string_to_int (find "Mod" xs) * 8 * 8) ^
      create_SIB xs ^ (find "disp" ts handle e => "")
    fun is_plus x = (implode (tl (tl (explode x))) = "+rd") handle _ => false
    fun do_replace x =
      if mem x ["iq","id","iw","ib","cb","cw","cd"] then find x ts else
      if is_plus x then let
        val reg_n = string_to_int_8 (find "Reg/Opcode" ts) #"B"
        val reg = Arbnum.fromInt (reg_n)
        val s = implode [hd (explode x), hd (tl (explode x))]
        in Arbnum.toHexString(Arbnum.+(Arbnum.fromHexString s, reg)) end else
      if can Arbnum.fromHexString x then x else
      if x = "/r" then create_ModRM ts else
      if hd (explode x) = #"/" then
        create_ModRM (("Reg/Opcode",(implode o tl o explode) x)::ts)
      else fail()
    val e = concat (map do_replace zs)
    val e = prefixes ^ (rex_prefix()) ^ e
    in e end;
  val all = try_all use_encoding ys
  val e = hd (sort (fn x => fn y => size x <= size y) all)
  in e end

fun x64_supported_instructions () = let
  fun all_distinct [] = []
    | all_distinct (x::xs) = x::all_distinct (filter (fn y => not ((x:string) = y)) xs)
  in all_distinct (map (fn (x,y) => hd y) instructions) end;


end
