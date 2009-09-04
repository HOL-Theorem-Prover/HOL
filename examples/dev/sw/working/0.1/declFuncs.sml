structure declFuncs =
struct

local
open HolKernel Parse
in

  exception undeclFunc;

  val k = ref 0;
  val sizeHint = 128
  val hashtable : ((string, int) Polyhash.hash_table) ref =
           ref (Polyhash.mkTable(Polyhash.hash, op = ) (sizeHint, undeclFunc))

  structure T = IntMapTable(type key = int  fun getInt n = n);

  type func = {name : string, ftype : hol_type, ir : IRSyntax.exp * annotatedIR.anntIR * IRSyntax.exp,
	regs : int Binaryset.set, localNum : int, def : thm};
  val decls : (func T.table) ref = ref (T.empty);

  fun is_decl fun_name =
	case Polyhash.peek (!hashtable) fun_name of
		SOME x => true
	 |      NONE => false

  fun getFunc fun_name =
      let val i = Polyhash.find (!hashtable) fun_name in
	T.look(!decls,i)
      end;

  fun putFunc (name,tp,ir,rs,n,f_def) =
      let
	  val _ = Polyhash.insert (!hashtable) (name, !k)
      in
            ( decls := T.enter(!decls,!k, {name = name, ftype = tp, ir = ir, regs = rs, localNum = n, def = f_def});
	      k := !k + 1
            )
      end

end (* local structure ... *)

end (* structure *)
