(* interactive use:
val _ = loadPath := !loadPath @
          ["/local/scratch/acjf3/hol98/src/theoryML",
           "/local/scratch/acjf3/hol98/src/portableML"];
val _ = app load ["ListPair", "Arbnum", "Redblackmap", "armML", "assemblerML"];
val _ = load "Mosml";
val _ = load "Random";
val _ = installPP numML.pp_num;
val _ = installPP Arbnum.pp_num;
*)

(* ------------------------------------------------------------------------- *)

fun to_INT_MIN n =
  let open numML in
     ("i" ^ Int.toString n, EXP TWO (fromInt (Int.-(n, 1))))
  end;

fun to_dimword n =
  let open numML in
     ("i" ^ Int.toString n, EXP TWO (fromInt n))
  end;

fun to_dimindex s =
  if String.sub(s,0) = #"i" then
    numML.fromString(String.extract(s,1,NONE))
  else
    raise fcpML.IndexUndefined;

val index_list = [2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 28, 30, 32, 64];

val dict_INT_MIN =
  foldl (fn (n, d) => let val (s,m) = to_INT_MIN n in
           Redblackmap.insert(d,s,m) end)
    (Redblackmap.mkDict String.compare) index_list;

val dict_dimword =
  foldl (fn (n, d) => let val (s,m) = to_dimword n in
           Redblackmap.insert(d,s,m) end)
    (Redblackmap.mkDict String.compare) index_list;

fun lookup_index f g (fcpML.Tyvar s) = raise fcpML.IndexUndefined
  | lookup_index f g (fcpML.Tyop (s, l)) =
      if null l then
        f s handle _ => raise fcpML.IndexUndefined
      else if s = "sum" andalso length l = 2 then
        g (lookup_index f g (hd l)) (lookup_index f g (hd (tl l)))
      else
        raise fcpML.IndexUndefined;

val lookup_INT_MIN =
  lookup_index (fn s => Redblackmap.find(dict_INT_MIN,s)) numML.*;

val lookup_dimword =
  lookup_index (fn s => Redblackmap.find(dict_dimword,s)) numML.*;

val lookup_dimindex = lookup_index to_dimindex numML.+;

val _ = wordsML.lookup_INT_MIN := lookup_INT_MIN;
val _ = wordsML.lookup_dimword := lookup_dimword;
val _ = fcpML.lookup_dimindex := lookup_dimindex;

val _ = fcpML.dimindex (fcpML.Tyop ("i4", []));
val _ = wordsML.dimword (fcpML.Tyop ("i4", []));
val _ = wordsML.INT_MIN (fcpML.Tyop ("i4", []));

val Arbnum2num = numML.fromString o Arbnum.toString;
val num2Arbnum = Arbnum.fromString o numML.toString;

fun fromNum s n = wordsML.fromNum(numML.fromString n, fcpML.Tyop (s, []));
fun fromHexNum s n = wordsML.fromNum(numML.fromHexString n, fcpML.Tyop (s, []));
fun fromArbnum s n = wordsML.fromNum(Arbnum2num n, fcpML.Tyop (s, []));

val fromNum2 = (fromNum "i2"): string -> (bool, armML.i2) fcpML.cart;
val fromNum4 = (fromNum "i4"): string -> (bool, armML.i4) fcpML.cart;
val fromNum5 = (fromNum "i5"): string -> (bool, armML.i5) fcpML.cart;
val fromNum8 = (fromNum "i8"): string -> (bool, armML.i8) fcpML.cart;
val fromNum12 = (fromNum "i12"): string -> (bool, armML.i12) fcpML.cart;
val fromNum16 = (fromNum "i16"): string -> (bool, armML.i16) fcpML.cart;
val fromNum24 = (fromHexNum "i24"): string -> (bool, armML.i24) fcpML.cart;
val fromNum30 = (fromHexNum "i30"): string -> (bool, armML.i30) fcpML.cart;
val fromNum32 = (fromHexNum "i32"): string -> (bool, armML.i32) fcpML.cart;

val fromArbnum30 =
  (fromArbnum "i30"): Arbnum.num -> (bool, armML.i30) fcpML.cart;

val fromArbnum32 =
  (fromArbnum "i32"): Arbnum.num -> (bool, armML.i32) fcpML.cart;

(* ------------------------------------------------------------------------- *)

local
  fun add1 a = Data.add32 a Arbnum.one;
  fun div4 a = Arbnum.div(a,Arbnum.fromInt 4);
  fun mul4 a = Arbnum.*(a,Arbnum.fromInt 4);
  val start = Arbnum.zero;

  fun mk_links [] dict n = dict
    | mk_links (h::r) dict n =
        case h of
          Data.Code c => mk_links r dict (add1 n)
        | Data.BranchS b => mk_links r dict (add1 n)
        | Data.BranchN b => mk_links r dict (add1 n)
        | Data.Label s =>
            mk_links r
             (Redblackmap.insert(dict, s, "0x" ^ Arbnum.toHexString (mul4 n))) n
        | Data.Mark m => mk_links r dict (div4 m);

  fun mk_link_table code =
    let val dict = Redblackmap.mkDict String.compare in
      mk_links code dict start
    end;

  fun br_to_word32 (cond,link,label) dict n =
    let val s = assemblerML.assembler_to_string
                   NONE (Data.BranchS(cond,link,"")) NONE
        val address = Redblackmap.find(dict, label)
    in
      (fromArbnum32 o assemblerML.encode_arm)
        ("0x" ^ Arbnum.toHexString (mul4 n) ^ ": " ^ s ^ address)
    end;

  fun is_label (Data.Label s) = true | is_label _ = false;

  fun lcons h [] = [[h]]
    | lcons h (x::l) = (h::x)::l;

  fun do_link m l [] dict n = ListPair.zip(m, l)
    | do_link m l (h::r) dict n =
        case h of
           Data.Code c =>
             do_link m
               (lcons (fromArbnum32 (assemblerML.arm_to_num (assemblerML.validate_instruction c))) l)
               r dict (add1 n)
         | Data.BranchS b =>
             do_link m (lcons (br_to_word32 b dict n) l) r dict (add1 n)
         | Data.BranchN b =>
             let val t = fromArbnum32 (assemblerML.arm_to_num (assemblerML.branch_to_arm b (mul4 n))) in
               do_link m (lcons t l) r dict (add1 n)
             end
         | Data.Label s => do_link m l r dict n
         | Data.Mark mk => let val k = div4 mk in
               if k = n then
                 do_link m l r dict n
               else if null (hd l) then
                 do_link (k::(tl m)) l r dict k
               else
                 do_link (k::m) ([]::l) r dict k
             end;

  fun do_links code =
        let val l = do_link [start] [[]] code (mk_link_table code) start in
          rev (map (fn (a,b) => (a,rev b)) l)
        end;

  fun assemble_assambler m a = let
    val l = do_links a
    val b = map (fn (m,c) => (fromArbnum30 m, c)) l
  in
    foldr (fn ((a,c),t) => armML.::- a c t) m b
  end
in
  fun assemble m file = assemble_assambler m (assemblerML.parse_arm file);
  fun list_assemble m l =
    let val nll = String.concat (map (fn s => s ^ "\n") l)
        val c = substring(nll,0,size nll - 1)
    in
      assemble_assambler m (assemblerML.parse_arm_buf "" BasicIO.std_in
        (Lexing.createLexerString c))
    end;
  fun assemble1 m t = list_assemble m [t];
end;

(* ------------------------------------------------------------------------- *)

val exc_mem = list_assemble (fn x => fromNum32 "E6000010")
  ["0x0: movs pc, #32",
   "label: b label",
   "movs pc, r14",
   "subs pc, r14, #4",
   "subs pc, r14, #8",
   "movs pc, r14",
   "subs pc, r14, #4",
   "subs pc, r14, #4"];

fun reg armML.r15 = fromNum32 "20"
  | reg _ = fromNum32 "0";

fun psr armML.CPSR =
      armML.SET_NZCV (false,(false,(false,false)))
        (armML.SET_IFMODE false false armML.usr (fromNum32 "0"))
  | psr _ =
      armML.SET_NZCV (false,(false,(false,false)))
        (armML.SET_IFMODE false false armML.usr (fromNum32 "0"));

val state = armML.state_arme (reg,psr,exc_mem,false);

fun done (armML.state_arme (r,p,m,u)) = u;

val count = ref 0;

fun STATE_ARMe printer n s =
  if n = 0 then s
  else
    let val _ = printer s
        val _ = count := !count + 1
        val ns = Mosml.time armML.NEXT_ARMe s in
      if done s then ns else STATE_ARMe printer (n - 1) ns
    end;

fun printer (armML.state_arme (r,p,m,u)) =
  let val pc = armML.FETCH_PC r
      val ireg = m (armML.ADDR30 pc)
  in
    print ("0x" ^ (numML.toHexString (wordsML.w2n pc)) ^ ": ");
    print (assemblerML.decode_arm NONE (num2Arbnum (wordsML.w2n ireg)) ^ "\n")
  end;

val max = valOf Int.maxInt;

val final = STATE_ARMe printer max state;

(* ------------------------------------------------------------------------- *)

val i2s = Int.toString;

fun hs n = "0x" ^ Arbnum.toHexString n;

local
  open Arbnum
  val twoexp32 = pow(two, fromInt 32)
  fun num2words2 n l =
    if n = zero then l else
      let val (q, r) = divmod(n, twoexp32) in
        num2words2 q ((hs r)::l)
      end
  fun words2num2 [] n = n
    | words2num2 (i::t) n = words2num2 t (fromInt i + (n * twoexp32))
in
  fun num2words s = rev (num2words2 s [])
  fun words2num l = words2num2 (rev l) zero
end;

fun num2wordsn n s =
  let val l = num2words s
      val ll = length l
  in
    if n < ll then
      List.take(l, n)
    else
      l @ List.tabulate(n - ll, fn _ => "0x0")
  end;

fun prefix_hd s [] = [s]
  | prefix_hd s (h::t) = (s ^ h)::t;

fun random_word l =
  words2num (Random.rangelist (0, max) (l, Random.newgen()));

(* ------------------------------------------------------------------------- *)

val a = random_word 17;
val b = random_word 17;

val prog = list_assemble
  (assemble exc_mem "../code/add.s")
 (["0x20:\
   \mov sp, #0xA000",
   "mov r0, sp",
   "add r1, r0, #"^i2s(4 * 17),
   "add r2, r1, #"^i2s(4 * 17),
   "bl 0x8000"] @
   (prefix_hd "0xA000: "
    (num2wordsn 17 a)) @
    (num2wordsn 17 b));

val final = Mosml.time (STATE_ARMe printer max) (armML.state_arme (reg,psr,prog,false));

(* ------------------------------------------------------------------------- *)

val a = random_word 9;
val b = random_word 9;

val prog = list_assemble
  (assemble exc_mem "../code/mul9.s")
 (["0x20:\
   \mov sp, #0xA000",
   "mov r0, sp",
   "add r1, r0, #"^i2s(4 * 9),
   "add r2, r1, #"^i2s(4 * 9),
   "bl 0x8000"] @
   (prefix_hd "0xA000: "
    (num2wordsn 9 a)) @
    (num2wordsn 9 b));

val final = Mosml.time (STATE_ARMe printer max) (armML.state_arme (reg,psr,prog,false));

(* ------------------------------------------------------------------------- *)

val a = random_word 17;
val b = random_word 17;

val prog = list_assemble
  (assemble exc_mem "../code/my_mul.s")
 (["0x20:\
   \mov sp, #0xA000",
   "mov r0, sp",
   "add r1, r0, #"^i2s(4 * 17),
   "add r2, r1, #"^i2s(4 * 17),
   "bl 0x8000"] @
   (prefix_hd "0xA000: "
    (num2wordsn 17 a)) @
    (num2wordsn 17 b));

val final = Mosml.time (STATE_ARMe printer max) (armML.state_arme (reg,psr,prog,false));

(* 7.98s, which is 902 times faster and 184 ips *)

(* ------------------------------------------------------------------------- *)
