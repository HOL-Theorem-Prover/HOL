structure ppc_encodeLib :> ppc_encodeLib =
struct

open HolKernel boolLib bossLib;
open ppc_decoderTheory;

val car = fst o dest_comb;
val cdr = snd o dest_comb;

val instructions = let
  fun foo tm = let val (x,y) = dest_comb tm in
    foo x @ [stringSyntax.fromHOLstring (cdr y)] end
    handle _ => [(implode o tl o explode o fst o dest_const) tm]
  fun d (x,y) = let
    val xs = (foo o snd o dest_abs) y
    val (i,t) = (hd xs, tl xs)
    val f = String.tokens (fn x => (x = #" ")) (stringSyntax.fromHOLstring x)
    val i = (implode o map (fn x => if x = #"_" then #"." else x) o explode) i
    in (i,(t,f)) end
  in (map d o map pairSyntax.dest_pair o fst o
      listSyntax.dest_list o cdr o cdr o concl o SPEC_ALL) ppc_decode_def end;

fun ppc_encode s = let
  fun token_size name =
    if mem name ["A","B","C","D","S","BO","BI","crbA","crbB","crbD","SH","MB","ME"] then 5
    else if mem name ["BD"] then 14
    else if mem name ["SIMM","UIMM","d"] then 16
    else if mem name ["LI"] then 24
    else if mem name ["AA","Rc","OE","y","z"] then 1
    else fail();
  fun fill n s = if size s < n then fill n ("0" ^ s) else s
  fun to_binary n i = let
    val m = Arbnum.pow(Arbnum.fromInt 2, Arbnum.fromInt n)
    val m2 = Arbnum.pow(Arbnum.fromInt 2, Arbnum.fromInt (n - 1))
    val j = Arbint.+(i,Arbint.fromNat m)
    in if Arbint.<=(Arbint.zero,i) then fill n (Arbnum.toBinString(Arbint.toNat i))
                                   else fill n (Arbnum.toBinString(Arbint.toNat j))
    end
  val xs = String.tokens (fn x => mem x [#",",#" ",#"(",#")",#"[",#"]"]) s
  val (x,xs) = (hd xs, tl xs)
  val (x,xs) = if x = "bne" then ("bc",["4","2"] @ xs) else
               if x = "beq" then ("bc",["12","2"] @ xs) else
               if x = "blt" then ("bc",["12","0"] @ xs) else
               if x = "bge" then ("bc",["4","0"] @ xs) else
               if x = "bgt" then ("bc",["4","1"] @ xs) else
               if x = "ble" then ("bc",["12","1"] @ xs) else (x,xs)
  val (_,(y,z)) = hd (filter (fn y => (fst y = x)) instructions)
  val qs = zip y xs
  val ts = map (fn (t,q) => (t,to_binary (token_size t) (Arbint.fromString q))) qs
  fun find [] c = c
    | find ((x,y)::xs) c = if x = c then y else find xs c
  val res = map (find ts) z
  val res = map (fn x => if mem x ["z","y"] then "0" else x) res
  val result = Arbnum.toHexString(Arbnum.fromBinString (concat res))
  in result end;

fun ppc_supported_instructions () = let
  fun all_distinct [] = []
    | all_distinct (x::xs) = x::all_distinct (filter (fn y => not ((x:string) = y)) xs)
  val i = map fst instructions @ ["bne","beq","blt","bgt","bge","ble"]
  val i = filter (fn x => not (mem x ["bt","bf"])) i
  in all_distinct (sort (fn x => fn y => x < y) i) end;

end
