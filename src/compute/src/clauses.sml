(*---------------------------------------------------------------------------
 * The functions in this module (except [from_term] and [inst_dterm]) are
 * called only to build the database of rewrite rules. Therefore,
 * optimisation is not so important.
 *
 * [from_term] is the first step of normalisation, and it is not called
 * later on (except with external conv).
 *---------------------------------------------------------------------------*)

structure clauses :> clauses =
struct

open HolKernel boolSyntax Drule compute_rules

val CL_ERR = mk_HOL_ERR "clauses"
infix ##

(*---------------------------------------------------------------------------
 * Checking that a given thm is a reduction rule we can handle:
 *         (c p1...pn) = rhs
 * with p1...pn  either a const applied to patterns or a free variable.
 *---------------------------------------------------------------------------*)

datatype pattern =
    Pvar of int
  | Papp of { Head : term, Args : pattern list}
;

fun check_arg_form trm =
  let fun chk t stk free =
    if is_comb t then
      let val (Rator,Rand) = dest_comb t
          val (free',pat1) = chk Rand [] free in
      chk Rator (pat1::stk) free'
      end
    else if (is_var t)
         then if null stk
              then let val newi = length free
                   in (free, Pvar (newi - index (aconv t) free - 1))
                      handle HOL_ERR _ => (t::free, Pvar newi)
                   end
              else raise CL_ERR "check_arg_form"
                  (Lib.quote (fst(dest_var t))^
                   " occurs as a variable on lhs")
    else if is_const t then (free, Papp{Head=t, Args=rev stk})
    else raise CL_ERR "check_arg_form" "lambda abstraction not allowed on lhs"
  in case chk trm [] [] of
       (fv,Papp{Head,Args}) => (rev fv,Head,Args)
     | _ => raise CL_ERR "check_arg_form" "ill-formed lhs"
  end
;


(*---------------------------------------------------------------------------
 * CLOS denotes a delayed substitution (closure).
 * CST denotes an applied constant. Its first argument is the head constant;
 *   the second is the list of its arguments (we keep both the term and its
 *   abstract representation); the last one is the set of rewrites that
 *   still have a chance to be used, ie. those with a lhs wider than the
 *   number of applied args.
 * NEUTR is a slight improvement of CST with an empty list of rewrites, so
 *   that arguments of a variable are immediatly strongly reduced.
 *---------------------------------------------------------------------------*)

datatype 'a fterm
    = (* order of Args: outermost ahead *)
      CST of { Head : term,
               Args : (term * 'a fterm) list,
               Rws  : 'a,
               Skip : int option }
    | NEUTR
    | CLOS of { Env : 'a fterm list, Term : 'a dterm }


(*---------------------------------------------------------------------------
 * An alternative representation of terms, with all information needed:
 * - they are real de Bruijn terms, so that abstraction destruction is in
 *   constant time.
 * - application is n-ary (slight optimization)
 * - we forget the names of variables
 * - constants are tagged with the set of rewrites that apply to it.
 *   It's a reference since dterm is used to represent rhs of rewrites,
 *   and fixpoints equations add rewrites for a constant that appear in the
 *   rhs.
 *---------------------------------------------------------------------------*)

and 'a dterm
    = Bv of int
    | Fv
    | Cst of term * ('a * int option) ref
    | App of 'a dterm * 'a dterm list  (* order: outermost ahead *)
    | Abs of 'a dterm
;

(* Invariant: the first arg of App never is an App. *)

fun appl(App(a,l1),arg) = App(a,arg::l1)
  | appl(t,arg) = App(t,[arg])
;

(*---------------------------------------------------------------------------
 * Type variable instantiation in dterm. Make it tail-recursive ?
 *---------------------------------------------------------------------------*)

fun inst_type_dterm ([],v) = v
  | inst_type_dterm (tysub,v) =
      let fun tyi_dt (Cst(c,dbsk)) = Cst(Term.inst tysub c, dbsk)
            | tyi_dt (App(h,l))  = App(tyi_dt h, map tyi_dt l)
  	    | tyi_dt (Abs v)     = Abs(tyi_dt v)
  	    | tyi_dt v           = v
      in tyi_dt v end
;


datatype action =
    Rewrite of rewrite list
  | Conv of (term -> Thm.thm * db fterm)

and db =
    EndDb
  | Try of { Hcst : term, Rws : action, Tail : db }
  | NeedArg of db

and rewrite =
    RW of { cst: term,          (* constant which the rule applies to *)
            lhs: pattern list,  (* patterns = constant args in lhs of thm *)
	    npv: int,           (* number of distinct pat vars in lhs *)
	    rhs: db dterm,
            thm: Thm.thm }      (* thm we use for rewriting *)
;

fun add_in_db (n,cst,act,EndDb) =
      funpow n NeedArg (Try{Hcst=cst, Rws=act, Tail=EndDb})
  | add_in_db (0,cst,act as Rewrite nrws,Try{Hcst,Rws as Rewrite rws,Tail}) =
      if aconv cst Hcst then Try{ Hcst=Hcst, Rws=Rewrite(nrws@rws), Tail=Tail }
      else Try { Hcst=Hcst, Rws=Rws, Tail=add_in_db(0,cst,act,Tail) }
  | add_in_db (n,cst,act,Try{Hcst,Rws,Tail}) =
      Try { Hcst=Hcst, Rws=Rws, Tail=add_in_db(n,cst,act,Tail) }
  | add_in_db (0,cst,act,db) = Try{ Hcst=cst, Rws=act, Tail=db }
  | add_in_db (n,cst,act,NeedArg tail) =
      NeedArg(add_in_db(n-1,cst,act,tail))
;

fun key_of (RW{cst, lhs, ...}) =
  let val {Name,Thy,...} = dest_thy_const cst in
  ((Name,Thy), length lhs, cst)
  end
;


fun is_skip (_, CST {Skip=SOME n,Args,...}) = (n <= List.length Args)
  | is_skip _ = false
;

fun partition_skip (SOME n) Args =
  let val len = List.length Args in
     if n <= len
     then Lib.split_after (len - n) Args
     else ([], Args)
  end
   | partition_skip NONE Args = ([], Args)
;

(*---------------------------------------------------------------------------
 * equation database
 * We should try to factorize the rules (cf discrimination nets)
 * Rules are packed according to their head constant, and then sorted
 * according to the width of their lhs.
 *---------------------------------------------------------------------------*)

datatype comp_rws
   = RWS of (string * string, (db * int option) ref) Redblackmap.dict ref;

fun lex_string_comp ((s1, s2), (s3, s4)) =
  case String.compare (s1, s3) of
    EQUAL => String.compare (s2, s4)
  | x => x

fun empty_rws () = RWS (ref (Redblackmap.mkDict lex_string_comp));

fun assoc_clause (RWS rws) cst =
  case Redblackmap.peek (!rws, cst)
   of SOME rl => rl
    | NONE => let val mt = ref (EndDb, NONE)
              in rws := Redblackmap.insert (!rws,cst,mt)
               ; mt
              end
;

fun add_in_db_upd rws (name,arity,hcst) act =
  let val (rl as ref(db,sk)) = assoc_clause rws name
  in rl := (add_in_db (arity,hcst,act,db), sk)
  end
;

fun set_skip (rws as RWS htbl) p sk =
  let val (rl as ref(db,_)) = assoc_clause rws p
  in rl := (db,sk)
  end;

fun scrub_const (RWS htbl) c =
  let val {Thy,Name,Ty} = dest_thy_const c
  in htbl := #1 (Redblackmap.remove (!htbl,(Name,Thy)))
  end;

fun from_term (rws,env,t) =
  let fun down (env,t,c) =
        case dest_term t of
	  VAR _ => up((Bv (index (aconv t) env) handle HOL_ERR _ => Fv), c)
  	| CONST{Name,Thy,...} => up(Cst (t,assoc_clause rws (Name,Thy)),c)
  	| COMB(Rator,Rand) => down(env,Rator,Zrator{Rand=(env,Rand),Ctx=c})
  	| LAMB(Bvar,Body) => down(Bvar :: env, Body, Zabs{Bvar=(), Ctx=c})

      and up (dt, Ztop) = dt
	| up (dt, Zrator{Rand=(env,arg), Ctx=c}) =
	    down (env,arg,Zrand{Rator=dt, Ctx=c})
	| up (dt, Zrand{Rator=dr, Ctx=c}) = up (appl(dr,dt), c)
	| up (dt, Zabs{Ctx=c,...}) = up(Abs dt, c)
  in down (env,t,Ztop)
  end
;



(*---------------------------------------------------------------------------
 * Note: if the list of free variables of the lhs was empty, we could
 * evaluate (weak reduction) the rhs now. This implies that the
 * theorems must be added in dependencies order.
 *---------------------------------------------------------------------------*)

fun mk_rewrite rws eq_thm =
  let val (lhs,rhs) = dest_eq (concl eq_thm)
      val (fv,cst,pats) = check_arg_form lhs
      val gen_thm = foldr (uncurry GEN) eq_thm fv
      val rhsc = from_term (rws, rev fv, rhs)
  in RW{ cst=cst,
	 lhs=pats,
	 rhs=rhsc,
	 npv=length fv,
	 thm=gen_thm }
  end
;

fun unsuitable th = let
  val (l, r) = dest_eq (concl th)
in
  can (match_term l) r
end

fun enter_thm rws thm0 = let
  val thm = eq_intro thm0
in
  if unsuitable thm then ()
  else let
      val rw  = mk_rewrite rws thm
          handle e =>
                 raise (wrap_exn "clauses"
                                 ("enter_thm: computeLib cannot use thm\n"
                                  ^Parse.thm_to_string thm0) e)
    in
      add_in_db_upd rws (key_of rw) (Rewrite [rw])
    end
end

fun add_thms lthm rws =
  List.app (List.app (enter_thm rws) o BODY_CONJUNCTS) lthm;

fun add_thmset setname rws = let
  open ThmSetData
  val data = all_data setname
in
  app (fn (s, namedths) => add_thms (map #2 namedths) rws) data
end

fun add_extern (cst,arity,fconv) rws =
  let val {Name,Thy,...} = dest_thy_const cst in
  add_in_db_upd rws ((Name,Thy),arity,cst) (Conv fconv)
  end;

fun new_rws () =
  let val rws = empty_rws()
  in add_thms [boolTheory.REFL_CLAUSE] rws
   ; rws
  end;

fun from_list lthm =
  let val rws = new_rws()
  in add_thms lthm rws
   ; rws
  end;

fun scrub_thms lthm rws =
 let val tmlist = map (concl o hd o BODY_CONJUNCTS) lthm
     val clist = map (fst o strip_comb o lhs o snd o strip_forall) tmlist
 in List.app (scrub_const rws) clist
 end
 handle e => raise wrap_exn "clauses" "del_list" e;


(*---------------------------------------------------------------------------*)
(* Support for analysis of compsets                                          *)
(*---------------------------------------------------------------------------*)

fun rws_of (RWS (ref rbmap)) =
 let val thinglist = Redblackmap.listItems rbmap
     fun db_of_entry (ss, ref (db,opt)) = db
     val dblist = List.map db_of_entry thinglist
     fun get_actions db =
      case db
       of EndDb => []
        | NeedArg db' => get_actions db'
        | Try{Hcst,Rws,Tail} => (Hcst,Rws)::get_actions Tail
     val actionlist = List.concat (List.map get_actions dblist)
     fun dest (RW{cst,lhs,npv,rhs,thm}) = thm
     fun dest_action (Hcst,Rewrite rws) = (Hcst,map dest rws)
       | dest_action (Hcst,Conv _) = (Hcst,[])
     val rwlist = List.map dest_action actionlist
 in
   rwlist
 end;

datatype transform
  = Conversion of (term -> thm * db fterm)
  | RRules of thm list;

(*---------------------------------------------------------------------------*)
(* Compute the "attachments" for each element of the compset. Fortunately,   *)
(* it seems that the insertion of an attachment into a compset also makes    *)
(* insertions for the constants mentioned in the rhs of the rewrite.         *)
(* Otherwise, one would have to do a transitive closure sort of construction *)
(* to make all the dependencies explicit.                                    *)
(*---------------------------------------------------------------------------*)

fun deplist (RWS (ref rbmap)) =
 let val thinglist = Redblackmap.listItems rbmap
     fun db_of_entry (ss, ref (db,opt)) = (ss,db)
     val dblist = List.map db_of_entry thinglist
     fun get_actions db =
      case db
       of EndDb => []
        | NeedArg db' => get_actions db'
        | Try{Hcst,Rws,Tail} => Rws::get_actions Tail
     val actionlist = List.map (I##get_actions) dblist
     fun dest (RW{cst,lhs,npv,rhs,thm}) = thm
     fun dest_action (Rewrite rws) = RRules (map dest rws)
       | dest_action (Conv ecnv) = Conversion ecnv
     val rwlist = List.map (I##(map dest_action)) actionlist
 in
   rwlist
 end;

fun mkCSET () =
 let val tyinfol = TypeBasePure.listItems (TypeBase.theTypeBase())
     val init_set = HOLset.empty
                      (inv_img_cmp (fn {Thy,Name,Ty} => (Thy,Name))
                              (pair_compare(String.compare,String.compare)))
     fun insert_const c cset = HOLset.add(cset,dest_thy_const c)
     fun insert_tycs tyinfo cset =
        itlist insert_const (TypeBasePure.constructors_of tyinfo) cset
 in
     itlist insert_tycs tyinfol init_set
 end;

(*---------------------------------------------------------------------------*)
(* Compute the attachments for each constant, then delete the constructors.  *)
(*---------------------------------------------------------------------------*)

fun no_transform compset =
 let val CSET = mkCSET()
     fun inCSET t = HOLset.member(CSET, dest_thy_const t)
     fun interesting (ss,_::_) = false
       | interesting ((Name,Thy),[]) =
          let val c = prim_mk_const{Name=Name,Thy=Thy}
          in not(inCSET c)
          end
 in
    map fst (filter interesting (deplist compset))
 end;

end
