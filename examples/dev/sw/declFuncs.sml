structure declFuncs = 
struct

  exception undeclFunc;

  val k = ref 0;
  val sizeHint = 128
  val hashtable : ((string, int) Polyhash.hash_table) ref =
           ref (Polyhash.mkTable(Polyhash.hash, op = ) (sizeHint, undeclFunc))

  structure T = IntMapTable(type key = int  fun getInt n = n);

  type func = {name:string, args:Assem.exp, stms:Assem.instr list, outs:Assem.exp, regs:Assem.exp Binaryset.set};
  val decls : (func T.table) ref = ref (T.empty);

  fun is_decl fun_name = 
	case Polyhash.peek (!hashtable) fun_name of
		SOME x => true
	 |      NONE => false

  fun getFunc fun_name =
      let val i = Polyhash.find (!hashtable) fun_name in
	T.look(!decls,i)
      end;

  fun putFunc (name,args,stms,outs,rs) =
      let 
	  val _ = Polyhash.insert (!hashtable) (name, !k)
      in
            ( decls := T.enter(!decls,!k, {name = name, args = args, 
					   stms = stms, outs = outs, regs = rs});
	      k := !k + 1
            )
      end

end
