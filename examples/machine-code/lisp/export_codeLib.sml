structure export_codeLib :> export_codeLib =
struct

open HolKernel boolLib bossLib Parse;

open wordsTheory wordsLib helperLib;

open divideTheory;

val filename = "foo"
val th = arm_div_mod_thm

fun write_code_to_file filename th = let
  val _ = print ("Extracting machine code to file \"" ^ filename ^ "\", ")
  val (m,pre,c,post) = (dest_spec o concl) th
  val model_name = fst (dest_const m)
  val cs = butlast (list_dest pred_setSyntax.dest_insert c)
  val vs = map (pairSyntax.dest_pair) cs
  val vs = map (fn (x,y) => (if is_var x then ``0:num`` else cdr (cdr x),y)) vs
  val vs = map (fn (x,y) => (Arbnum.toInt (numSyntax.dest_numeral x),y)) vs
  val vs = sort (fn (x,_) => fn (y:int,_) => x <= y) vs
  fun del_repetations (x::y::xs) = if x = y then del_repetations (x::xs) else
                                     x :: del_repetations (y::xs)
    | del_repetations zs = zs
  val vs = del_repetations vs
  fun no_duplicates (x::y::xs) = if fst x = fst y then hd [] else no_duplicates (y::xs)
    | no_duplicates _ = true
  val _ = no_duplicates vs
  fun term_byte_size tm =
    if type_of tm = ``:word8`` then 1 else
    if type_of tm = ``:word32`` then 4 else
      foldr (fn (x,y) => x + y) 0 (map term_byte_size (fst (listSyntax.dest_list tm)))
  fun no_holes i [] = true
    | no_holes i ((j,c)::xs) =
       if i = j then no_holes (i + (term_byte_size c)) xs else hd []
  val _ = no_holes 0 vs
  val byte_count = ref 0;
  val big_endian_format = ``[(w2w ((w:word32) >>> 24)):word8;
                             (w2w ((w:word32) >>> 16)):word8;
                             (w2w ((w:word32) >>> 8)):word8;
                             (w2w ((w:word32) >>> 0)):word8]``
  val little_endian_format = ``[(w2w ((w:word32) >>> 0)):word8;
                                (w2w ((w:word32) >>> 8)):word8;
                                (w2w ((w:word32) >>> 16)):word8;
                                (w2w ((w:word32) >>> 24)):word8]``
  val format_tm = if model_name = "PPC_MODEL" then big_endian_format else little_endian_format
  val vs = map (fn (x,y) => (x,(cdr o concl o EVAL o subst [``w:word32``|->y]) format_tm handle e => y)) vs
  fun fill c d n s = if size s < n then fill c d n (c ^ s ^ d) else s
  fun word2hex tm = let
    val _ = (byte_count := !byte_count + (if type_of tm = ``:word8`` then 1 else 4))
    val s = Arbnum.toHexString (numSyntax.dest_numeral (cdr tm))
    in "0x" ^ fill "0" "" (if type_of tm = ``:word8`` then 2 else
                           if type_of tm = ``:word32`` then 8 else hd []) s end
  fun word2string tm = let
    val (tms,ty) = if listSyntax.is_list tm
                   then listSyntax.dest_list tm
                   else ([tm],type_of tm)
    val str = if ty = ``:word8`` then "\t.byte\t" else
              if ty = ``:word32`` then "\t.word\t" else hd []
    fun foo [] = hd []
      | foo [x] = word2hex x ^ "\n"
      | foo (x::y::ys) = word2hex x ^ ", " ^ foo (y::ys)
    in str ^ foo tms end
  val rs = map (word2string o snd) vs
  val instr_count = length rs
  val size_count = (!byte_count)
  val l1 = "Machine code automatically extracted from a HOL4 theorem."
  val l2 = "The code consists of " ^ int_to_string instr_count ^ " instructions (" ^ int_to_string size_count ^ " bytes)."
  val l3 = "End of automatically extracted machine code."
  val o1 = "\t/*  " ^ l1 ^ "  */\n"
  val o2 = "\t/*  " ^ fill "" " " (size l1) l2 ^ "  */\n"
  val o3 = "\t/*  " ^ fill "" " " (size l1) l3 ^ "  */\n"
  val output = ["\n","\n",o1,o2,"\n"] @ rs @ ["\n",o3,"\n"]
  (* val _ = map print output *)
  (* write to text file *)
  val out = TextIO.openOut filename
  fun writeline s = TextIO.output(out,s)
  val _ = map writeline output
  val _ = TextIO.closeOut(out)
  val _ = print "done.\n"
  in () end;

end
