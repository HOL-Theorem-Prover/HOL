open Lib Type Term Thm;

fun tprint s = print (StringCvt.padRight #" " 65 s);
fun OK () = print "OK\n";
fun die s = (print (s ^ "\n"); OS.Process.exit OS.Process.failure);

val file = "pft-reader-regression.pft.bin";

(* The old converter omitted Mk_abs's continuation binder. Its emitted
   abstraction can use y while the child theorem still uses x'. *)
val () = tprint "PFT Mk_abs with an alpha-renamed body binder";
val out = PFTWriter.openOut {file=file,version="0.1.0",ruleset="hol4"};
val () = PFTWriter.tyop out 0 "min$bool" [];
val () = PFTWriter.tyop out 1 "min$fun" [0,0];
val () = PFTWriter.tyop out 2 "min$fun" [0,1];
val () = PFTWriter.var out 0 "x" 0;
val () = PFTWriter.var out 1 "x'" 0;
val () = PFTWriter.var out 2 "y" 0;
val () = PFTWriter.const out 3 "min$=" 2;
val () = PFTWriter.comb out 4 3 1;
val () = PFTWriter.comb out 5 4 0;
val () = PFTWriter.comb out 6 3 2;
val () = PFTWriter.comb out 7 6 0;
val () = PFTWriter.abs out 8 2 7;
val () = PFTWriter.HOL4.refl out 0 8;
val () = PFTWriter.HOL4.refl out 1 5;
val () = PFTWriter.HOL4.mk_abs_thm out 2 0 1;
val () = PFTWriter.save out "pft-reader-regression$RESULT" 2;
val () = PFTWriter.closeOut out {n_ty=3,n_tm=9,n_th=3};
val db = PFTReplay.replay PFTReplay.empty_trDB file;
val th = valOf (PFTReplay.lookup db "pft-reader-regression$RESULT");
val x = mk_var ("x",bool);
val y = mk_var ("y",bool);
val eq = mk_thy_const {Thy="min",Name="=",Ty=bool --> bool --> bool};
val lam = mk_abs (y,mk_comb (mk_comb (eq,y),x));
val () = if null (hyp th) andalso aconv (concl th) (concl (REFL lam))
         then OK() else die "wrong Mk_abs sequent";
val () = OS.FileSys.remove file;

(* Footer lookup used to allocate almost the entire file. Under Poly/ML,
   Holmake caps the heap at 64 MiB, below the 128 MiB input size. *)
val () = tprint "PFT footer lookup with an input larger than the heap";
val out = BinIO.openOut file;
val chunk = Word8Vector.tabulate (65536, fn _ => 0w0);
val () = funpow 2048 (fn () => BinIO.output (out,chunk)) ();
val () = BinIO.output (out,Word8Vector.fromList [0wxFF,0w3,0w9,0w3,0w4,0w0]);
val () = BinIO.closeOut out;
val limits = PFTReader.read_limits {file=file,binary=true};
val () = OS.FileSys.remove file;
val () = if limits = {n_ty=3,n_tm=9,n_th=3} then OK()
         else die "wrong footer limits";
