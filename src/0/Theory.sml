(* ===================================================================== *)
(* FILE          : Theory.sml                                            *)
(* DESCRIPTION   : Provides management of logical theories.              *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(*                 (also T.U. Munich and Cambridge)                      *)
(* DATE          : September 11, 1991                                    *)
(* REVISION      : August 7, 1997                                        *)
(*               : March 9, 1998                                         *)
(* ===================================================================== *)


(*---------------------------------------------------------------------------*
 * A theory is intended to hold the state of a HOL development. The theory   *
 * structure can be thought of as the backbone of a HOL formalization. (Like *
 * a backbone, it is usually invisible, but of crucial importance.) The      *
 * information held in the current theory provides for several important     *
 * services and helps maintain some critical system invariants. The current  *
 * theory                                                                    *
 *                                                                           *
 *  - stores definitions, axioms, and theorems.                              *
 *                                                                           *
 *  - maintains the dependency relation on theories.                         *
 *                                                                           *
 *  - stores information that aids the parser, e.g., fixity information      *
 *                                                                           *
 *  - stores the type schemes of constants, thus supporting both the         *
 *    explicit construction of well-typed terms and the implicit             *
 *    construction of them, the latter via type inference.                   *
 *                                                                           *
 *  - can be exported to disk, thus providing for persistence.               *
 *                                                                           *
 *---------------------------------------------------------------------------*)

structure Theory :> Theory =
struct

open Term Type Lib Exception;

type hol_type = Type.hol_type
type term = Term.term;
type thm = Thm.thm;
type fixity = Term.fixity;
type ppstream = Portable_PrettyPrint.ppstream

infix ##;


datatype ('a,'b) result = SUCCESS of 'a
                        | FAILURE of 'b

datatype 'a failed = SYSTEM   of exn     (* OS/network not right *)
                   | INTERNAL of exn     (* my mistake *)
                   | CLIENT   of 'a      (* caller problem *)

type thy_addon = {sig_ps    : (ppstream -> unit) option,
                  struct_ps : (ppstream -> unit) option}


fun THEORY_ERR function message =
    HOL_ERR{origin_structure = "Theory",
            origin_function = function,
            message = message}


(*---------------------------------------------------------------------------
 * Miscellaneous support functions.
 *---------------------------------------------------------------------------*)
fun dollar s = "$"^s;
fun dollared s = (Portable_String.sub(s,0) = #"$");

fun st_foldl f b A = Array.foldl (fn (L, A) => List.foldl f A L) b A;
fun st_filter P A = Array.foldl (fn (L, A) => Lib.mapfilter P L@A) [] A;

fun pluck1 x L =
  let fun get [] A = NONE
        | get ((p as (x',_))::rst) A =
           if (x=x') then SOME (p,rst@A)
           else get rst (p::A)
  in get L []
  end;


(*---------------------------------------------------------------------------*
 * Get information from Thm structure (the functions are hidden from the     *
 * rest of the system).                                                      *
 *---------------------------------------------------------------------------*)
local val r1 = ref(fn (_:string ref,tm) => Thm.REFL tm)
      val r2 = ref (fn _:Tag.tag => Thm.REFL)
in
   val _ = Thm.Theory_init r1 r2
   val mk_axiom_thm  = !r1
   val mk_defn_thm   = !r2
end;


(*---------------------------------------------------------------------------*
 * Get constructors and destructors from Type and Term structures (the       *
 * constructors and destructors are hidden from the rest of the system).     *
 *---------------------------------------------------------------------------*)
local val Tyapp_ref = ref(fn _:{name:string,revision:int} * Type.hol_type list
                            => mk_vartype"'x")
      val break_type_ref = ref(fn _:Type.hol_type =>
                              ({name="",revision=0},([]:Type.hol_type list)))
      val _ = Type.Theory_init Tyapp_ref break_type_ref
      val Const_ref = ref(fn _:string ref * Type.hol_type =>
                             mk_var{Name="dummy", Ty=mk_vartype"'x"})
      val break_const_ref = ref(fn _:Term.term => (ref"",mk_vartype"'x"))
      val _ = Term.Theory_init Const_ref break_const_ref
in
   val Const      = !Const_ref
   val Tyapp      = !Tyapp_ref
   val break_type = !break_type_ref
   val break_const = !break_const_ref
end;

(*---------------------------------------------------------------------------*
 * Unique identifiers, for securely linking a theory to its parents when     *
 * loading from disk.                                                        *
 *---------------------------------------------------------------------------*)

abstype thyid = UID of {name:string, timestamp:Portable_Time.time}
with
  fun thyid_eq x (y:thyid) = (x=y);
  fun new_thyid s = UID{name=s, timestamp=Portable_Time.timestamp()};

  fun dest_thyid (UID{name, timestamp}) =
    let val {sec,usec} = Portable_Time.dest_time(timestamp)
    in (name,sec,usec) end;

  val thyid_name = #1 o dest_thyid;

  local val mk_time = Portable_Time.mk_time
  in fun make_thyid(s,i1,i2) = UID{name=s, timestamp=mk_time{sec=i1,usec=i2}}
  end;
end;

(*---------------------------------------------------------------------------*
 * A type for identifying the different kinds of theorems that may be        *
 * stored in a theory.                                                       *
 *---------------------------------------------------------------------------*)
datatype thmkind = Thm of thm | Axiom of string ref * thm | Defn of thm

fun is_axiom (Axiom _) = true  | is_axiom _ = false;
fun is_theorem (Thm _) = true  | is_theorem _ = false;
fun is_defn (Defn _) = true    | is_defn _ = false;

fun drop_thmkind(Axiom(_,th)) = th
  | drop_thmkind(Thm th)    = th
  | drop_thmkind(Defn th)   = th;

fun drop_pthmkind (s,th) = (s,drop_thmkind th);

fun drop_Axkind(Axiom rth) = rth
  | drop_Axkind _ = raise THEORY_ERR"drop_Axkind" "";

(*---------------------------------------------------------------------------*
 *                         HOL SIGNATURES                                    *
 *---------------------------------------------------------------------------*)

datatype stEntry = TYPE of {occ:{name:string,revision:int},
                            arity:int,theory:string,
                            witness:Thm.thm option, utd:bool ref}
                 | TERM of {name:string ref, theory:string, place:fixity,
                            htype:Type.hol_type,
                            witness:Thm.thm option, utd:bool ref}


(*---------------------------------------------------------------------------*
 * The type of HOL theories.                                                 *
 *---------------------------------------------------------------------------*)

type theory = {thid : thyid,                                   (* unique id  *)
               STH  : stEntry list array * (string -> int),  (* symbol table *)
               GR   : thyid Graph.graph,              (* parenthood relation *)
               facts: (string * thmkind) list,      (* stored ax,def,and thm *)
               con_wrt_disk : bool,                 (* consistency with disk *)
               overwritten : bool,                     (* parts overwritten? *)
               adjoin : thy_addon list}                (* extras for export  *)



(*---------------------------------------------------------------------------*
 * Make a fresh theory segment. The timestamp for a theory is its creation   *
 * date. "con_wrt_disk" is set to false because when a theory is created no  *
 * corresponding file gets created (the file is only created on export).     *
 *---------------------------------------------------------------------------*)
fun fresh_theory s STH GR :theory =
   {thid=new_thyid s,  STH=STH, GR=GR, facts=[],
    con_wrt_disk=false, overwritten=false, adjoin=[]};


(*---------------------------------------------------------------------------*
 * Copy a theory.                                                            *
 *---------------------------------------------------------------------------*)
fun theoryClone {thid,con_wrt_disk, STH=(ST,h), GR, facts,overwritten,adjoin} =
   let val table_size = Array.length ST
       val STclone = Array.array (table_size,([]:stEntry list))
       val _ = for_se 0 (table_size-1)
                   (fn i => Array.update(STclone,i,Array.sub(ST,i)))
   in
      {thid=thid, con_wrt_disk=con_wrt_disk,
       STH = (STclone,h), GR=GR, facts=facts,
       overwritten=overwritten, adjoin=adjoin}
   end;

(*---------------------------------------------------------------------------*
 * Filter the ST by a predicate.                                             *
 *---------------------------------------------------------------------------*)
fun filterST P ST =
  for_se 0 (Array.length ST - 1)
      (fn i => Array.update(ST,i,Lib.gather P (Array.sub(ST,i))));

fun mapST f ST =
  for_se 0 (Array.length ST - 1)
      (fn i => Array.update(ST,i,List.map f (Array.sub(ST,i))))

fun zapST str ST =
 let fun chk (TERM{theory,...}) = not(theory=str)
       | chk (TYPE{theory,...}) = not(theory=str)
 in
   filterST chk ST; ST
 end

(*---------------------------------------------------------------------------*
 * Extraction from a theory.                                                 *
 *---------------------------------------------------------------------------*)

fun slice n ({STH=(ST,_),...}:theory) =
   st_foldl (fn (e as TERM{theory,...},D) => if (theory=n) then e::D else D
              | (e as TYPE{theory,...},D) => if (theory=n) then e::D else D)
      [] ST;

fun types_of s thy =
     List.foldl (fn (TYPE r,D) => r::D | (_,D) => D) [] (slice s thy);

fun consts_of s thy =
     List.foldl (fn (TERM r,D) => r::D | (_,D) => D) [] (slice s thy);

fun theory_id (th:theory)       = #thid th
fun thy_types n (th:theory)     = types_of n th;
fun thy_constants n (th:theory) = consts_of n th;
fun thy_axioms (th:theory)      = Lib.filter (is_axiom o #2)   (#facts th);
fun thy_theorems (th:theory)    = Lib.filter (is_theorem o #2) (#facts th);
fun thy_defns (th:theory)       = Lib.filter (is_defn o #2)    (#facts th);
fun thy_addons (th:theory)      = #adjoin th;
fun thy_con_wrt_disk n (th:theory) = #con_wrt_disk th;


(*---------------------------------------------------------------------------*
 * Is a theory empty?                                                        *
 *---------------------------------------------------------------------------*)
fun empty_theory(thy as {thid,facts, ...}:theory) =
      null (slice (thyid_name thid) thy) andalso null facts;


(*---------------------------------------------------------------------------*
 * Adding a symbol table entry. This can be done when a constant is          *
 * (re-)defined, or when a theory is loaded. You are only allowed to         *
 * redeclare a constant in the current theory. The code is subtle. We        *
 * look through the ST for a record with the same name and theory. If we     *
 * find one, it must belong to the current theory (CT) because theories all  *
 * have different names (in a session) and we can only load a theory once.   *
 * If we found a record with the same name but a different theory, that      *
 * is an error. Otherwise, we have the same name, same theory, and so we     *
 * are re-declaring a type in the current theory. In which case we bump up   *
 * its version number.                                                       *
 *                                                                           *
 * When a constant gets added to the ST, it is uninterpreted. If a defn.     *
 * is attached, the interpreting term gets stuck into the record.            *
 *---------------------------------------------------------------------------*)

local val changed = ref false
in
fun add_type_entry {name, theory, arity}
                   {thid,STH,GR,facts,con_wrt_disk,overwritten,adjoin} =
 let val _ = (changed := false)
     val (ST,hasher) = STH
     val i = hasher name
     val L = Array.sub(ST, i)
     val entry = TYPE{occ={name=name, revision=0},
                      theory=theory, arity=arity, witness=NONE, utd=ref true}
   fun del [] = [entry]
     | del ((e as TERM _)::rst) = e::del rst
     | del ((e as TYPE{occ={name=n1,revision},
                       theory=thy1, arity=a1,witness,utd})::rst) =
       if (name=n1) andalso (theory=thy1)  (* implies theory=CT *)
       then (changed := true;
             TYPE{occ={name=n1,revision=revision+1},
                 theory=thy1, arity=a1,witness=NONE,utd=utd}::rst)
       else if (name=n1) andalso (theory<>thy1)
            then raise THEORY_ERR"add_entry"
                           ("attempt to redeclare type "
                                     ^Lib.quote name^" from theory "
                                     ^Lib.quote thy1)
            else e::del rst  (* name <> name1 *)
 in
    Array.update(ST, i, del L);
    {thid=thid,STH=STH,GR=GR,facts=facts,
     con_wrt_disk=con_wrt_disk, adjoin=adjoin,
     overwritten = overwritten orelse !changed}
 end;

fun add_term_entry {name,theory,place,htype}
                   {thid,STH,GR,facts,con_wrt_disk,overwritten,adjoin} =
 let val _ = (changed := false)
     val (ST,hasher) = STH
     val i = hasher name
     val L = Array.sub(ST, i)
     val entry = TERM{name=ref name, utd=ref true,
                theory=theory,place=place, htype=htype,witness=NONE}
    fun del [] = [entry]  (* new addition *)
      | del ((e as TYPE _)::rst) = e::del rst
      | del ((e as TERM{name = ref n1, theory=thy1,place=pl1,
                        htype=ty1,witness,utd})::rst) =
          if (name=n1) andalso (theory=thy1)
          then (changed := true; entry::rst) (* repl. an existing resident *)
          else if (name=n1) andalso (theory<>thy1)
               then raise THEORY_ERR"add_entry"
                          ("attempt to redeclare constant "
                                ^Lib.quote name^" from theory "
                                ^Lib.quote thy1)
               else e::del rst
 in
   Array.update(ST, i, del L);
    {thid=thid,STH=STH,GR=GR,facts=facts,
     con_wrt_disk=con_wrt_disk, adjoin=adjoin,
     overwritten = overwritten orelse !changed}
 end;
end;

(*---------------------------------------------------------------------------*
 * We've made a definition and should now note that the constant has a       *
 * witness that it depends on: if the witness goes out of date, then the     *
 * constant goes out of date.                                                *
 *---------------------------------------------------------------------------*)
fun add_ty_witness (thy as {STH, ...}:theory) s th =
 let val (ST,hasher) = STH
     val i = hasher s
     val L = Array.sub(ST, i)
     fun get [] = raise THEORY_ERR"add_ty_witness" "no such type"
       | get ((e as TERM _)::rst) = e::get rst
       | get ((e as TYPE{occ, theory, arity, witness, utd})::rst) =
         if (#name occ = s)
         then TYPE{occ=occ, theory=theory, arity=arity, utd=utd,
                   witness=SOME th}::rst
         else e::get rst
 in
    Array.update(ST, i, get L); thy
 end;


fun add_tm_witness (thy as {STH, ...}:theory) s th  =
 let val (ST,hasher) = STH
     val i = hasher s
     val L = Array.sub(ST, i)
     fun get [] = raise THEORY_ERR"add_tm_witness" "no such constant"
       | get ((e as TYPE _)::rst) = e::get rst
       | get ((e as TERM{name, theory, place, htype, witness,utd})::rst) =
           if (!name=s)
           then TERM{name=name, theory=theory, place=place, utd=utd,
                     htype=htype, witness=SOME th}::rst
           else e::get rst
 in
    Array.update(ST, i, get L); thy
 end;


fun set_place (s,pl,thyname) (thy as {STH, ...}:theory)  =
 let val (ST,hasher) = STH
     val i = hasher s
     val L = Array.sub(ST, i)
     fun get ((e as TYPE _)::rst) = e::get rst
       | get ((e as TERM{name, theory, place, htype, witness,utd})::rst) =
           if (!name=s) andalso (theory=thyname)
           then TERM{name=name, theory=theory, place=pl, utd=utd,
                     htype=htype, witness=witness}::rst
           else e::get rst
       |  get [] = raise THEORY_ERR "set_place"
                      "no such constant declared in current theory"
 in
    Array.update(ST, i, get L); thy
 end;


fun del_type (name,thyname)
     {thid,STH,GR,facts,con_wrt_disk,overwritten,adjoin} =
 let val (ST,hasher) = STH
     val i = hasher name
     val L = Array.sub(ST, i)
     fun del ((e as TYPE{occ={name=n1,...}, theory=thy1,...})::rst) =
          if (name=n1) andalso (thyname=thy1) then rst else e::del rst
       | del ((e as TERM _)::rst) = e::del rst
       | del [] = raise THEORY_ERR "del_type"
              (Lib.quote name^" not found in current theory")
 in
    Array.update(ST, i, del L);
    {thid=thid,STH=STH,GR=GR,facts=facts,
     con_wrt_disk=con_wrt_disk,adjoin=adjoin,
     overwritten = true}
 end;

fun del_const (name,thyname)
     {thid,STH,GR,facts,con_wrt_disk,overwritten,adjoin} =
 let val (ST,hasher) = STH
     val i = hasher name
     val L = Array.sub(ST, i)
     fun del ((e as TERM{name = ref n1, theory=thy1,...})::rst) =
          if (name=n1) andalso (thyname=thy1) then rst else e::del rst
       | del ((e as TYPE _)::rst) = e::del rst
       | del [] = raise THEORY_ERR "del_const"
                (Lib.quote name^" not found in current theory")
 in
   Array.update(ST, i, del L);
   {thid=thid,STH=STH,GR=GR,facts=facts,
    con_wrt_disk=con_wrt_disk,adjoin=adjoin,
    overwritten = true}

 end;

fun del_axiom name {thid,STH,GR,facts,con_wrt_disk,overwritten,adjoin} =
  let val facts' = filter (fn (s, Axiom _) => (s=name) | _ => false) facts
  in
     {thid=thid, STH=STH, GR=GR, facts=facts', adjoin=adjoin,
      con_wrt_disk=con_wrt_disk, overwritten = true}
  end;

(*---------------------------------------------------------------------------*
 * Deleting a definition does not delete the constant(s) introduced by       *
 * the definition!                                                           *
 *---------------------------------------------------------------------------*)
fun del_defn name {thid,STH,GR,facts,con_wrt_disk,overwritten,adjoin} =
  let val facts' = filter (fn (s, Defn _) => (s=name) | _ => false) facts
  in {thid=thid, STH=STH, GR=GR, facts=facts',
      con_wrt_disk=con_wrt_disk, adjoin=adjoin, overwritten=true}
  end;

fun del_theorem name {thid,STH,GR,facts,con_wrt_disk,overwritten,adjoin} =
  let val facts' = filter (fn (s, Thm _) => (s=name) | _ => false) facts
  in {thid=thid, STH=STH, GR=GR, facts=facts',
      con_wrt_disk=con_wrt_disk, overwritten=overwritten,adjoin=adjoin}
  end;

(*---------------------------------------------------------------------------*
 * Get the current type record attached to the given name.                   *
 *---------------------------------------------------------------------------*)
fun lookup_type ({STH, ...}:theory) s e =
 let val (ST,hasher) = STH
     fun get [] = raise e
       | get (TERM _::rst) = get rst
       | get (TYPE(tr as {occ,...})::rst) =
            if (s = #name occ) then tr else get rst
 in
    get (Array.sub(ST, hasher s))
 end;


(*---------------------------------------------------------------------------*
 * Get the current term constant attached to the given name.                 *
 *---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------
 * This constant family stuff is completely horrible. The number treatment
 * has been removed with  Mike Norrish numbers.  However, until something
 * analogous is done for strings, these will still use the code given.
 *
 * The code takes advantage of the fact that the types of strings and
 * numbers won't get re-defined. The witness for a family literal should be
 * an equation involving its predecessor, e.g., `1 = SUC 0` for
 * "mk_const 1"  but I'll just make it be the base element of the family
 * (0 for nums and "" for strings).
 *---------------------------------------------------------------------------*)

fun lookup_tmc ({STH,...}:theory) s e =
 let val (ST,hasher) = STH
     fun get [] = raise e
       | get (TYPE _::rst) = get rst
       | get (TERM(tr as {name,...})::rst) =
           if (s = !name) then tr else get rst
 in
     get (Array.sub(ST, hasher s))
 end

type term_recd = {name:string ref, theory:string, place:Term.fixity,
                  htype:Type.hol_type, witness:Thm.thm option,utd:bool ref};

local datatype family = Num | String
      fun mk Num thy e n  = (* this case never called *)
          {name=ref n, theory="num", place=Term.Prefix, utd=ref true,
           htype=mk_type{Tyop="num",Args=[]},
           witness = #witness(lookup_tmc thy "0" e)}
        | mk String thy e n =
          {name=ref n, theory="string", place=Term.Prefix, utd=ref true,
           htype=mk_type{Tyop="string",Args=[]},
           witness = #witness(lookup_tmc thy "emptystring" e)}
      val table_size = 11;
      val table = Array.array (table_size,([]:term_recd list))
      fun hasher s = Lib.hash table_size s (0,0)
      fun mkX f s =
        let val i = hasher s
            val L = Array.sub(table,i)
            fun look [] A = let val c = f s in (c, c::A) end
              | look ((c as {name,...})::rst) A =
                 if (!name=s) then (c,c::(A@rst)) else look rst (c::A)
            val (c,L') = look L []
        in
          Array.update(table,i,L'); c
        end
in
fun lookup_const thy s e = lookup_tmc thy s e
  handle HOL_ERR _ =>  (* handle the family cases, if necessary *)
    (case Globals.strings_defined()
     of false => raise e
      | true => if (Lexis.is_string_literal s)
                  then mkX (mk String thy e) s else raise e)
end;

(*---------------------------------------------------------------------------
 * Alteration routines
 *---------------------------------------------------------------------------*)

fun set_consistency b {thid, con_wrt_disk, STH,
                       GR, facts,overwritten,adjoin} =
   {con_wrt_disk=b, thid=thid, STH=STH, GR=GR, facts=facts,
   overwritten=overwritten,adjoin=adjoin};

fun set_overwritten b {thid, con_wrt_disk, STH,
                       GR, facts,overwritten,adjoin} =
   {overwritten=b, con_wrt_disk=con_wrt_disk,adjoin=adjoin,
    thid=thid, STH=STH, GR=GR, facts=facts};

fun zap s {thid, con_wrt_disk, STH=(ST,h), GR, facts,overwritten,adjoin} =
   {overwritten=false, con_wrt_disk=con_wrt_disk, adjoin=[],
    thid=thid, STH=(zapST s ST, h), GR=GR, facts=[]};



(*---------------------------------------------------------------------------
 * We allow axioms to overwrite "themselves", and definitions to overwrite
 * definitions, and axioms, definitions, and theorems to overwrite theorems.
 * We want to prohibit the sequence of steps
 *
 *     |- c = T  (* via mk_axiom *)
 *     |- c = F  (* via mk_axiom *)
 *
 * because we could then conclude |- F, but then the current theory only
 * has the one axiom and we can't find out where to assign blame. This is
 * handled by having axioms be tracked in inference.
 *---------------------------------------------------------------------------*)
fun overwrite (p as (s,f)) l =
 case (pluck1 s l)
  of NONE => (p::l, false)
   | SOME ((_,f'),l') =>
       (case (f,f')
         of (Defn _, Defn _)    => (p::l', true)
          | (Axiom _ , Axiom _) =>  (p::l', true)
          | (_ , Defn _)        => raise THEORY_ERR"overwrite_fact"
                   "overwriting a defn with an axiom or a theorem not allowed"
          | (_, Thm _)          => (p::l', false)
          | (_ , Axiom _)       => raise THEORY_ERR"overwrite_fact"
                  "overwriting an axiom with a defn or a theorem not allowed");

fun add_fact (th as (s,_)) {thid, con_wrt_disk,
                            STH, GR, facts,overwritten,adjoin} =
  let val (X,b) = overwrite th facts
  in
    {facts=X, overwritten = overwritten orelse b,
     thid=thid, con_wrt_disk=con_wrt_disk, STH=STH, GR=GR, adjoin=adjoin}
  end;

fun new_addon a {thid, con_wrt_disk, STH, GR, facts,overwritten,adjoin} =
    {adjoin = a::adjoin, facts=facts, overwritten=overwritten,
     thid=thid, con_wrt_disk=con_wrt_disk, STH=STH, GR=GR};


fun plucky x L =
  let fun get [] A = NONE
        | get ((p as (x',_))::rst) A =
           if (x=x') then SOME (rev A, p, rst)
           else get rst (p::A)
  in get L []
  end;

fun set_MLbind (s1,s2) {thid, con_wrt_disk, STH,
                        GR, facts, overwritten,adjoin} =
   let val facts' =
         case (plucky s1 facts)
          of NONE => raise THEORY_ERR"set_MLbind" "no such binding"
           | SOME (X,(_,b),Y) => X@((s2,b)::Y)
   in
    {facts=facts', overwritten=overwritten, adjoin=adjoin,
     thid=thid, con_wrt_disk=con_wrt_disk, STH=STH, GR=GR}
  end;


(*---------------------------------------------------------------------------*
 * Link a theory to its parents in a theory graph.                           *
 *---------------------------------------------------------------------------*)
fun set_diff a b = gather (fn x => not (Lib.op_mem thyid_eq x b)) a;
fun node_set_eq S1 S2 = null(set_diff S1 S2) andalso null(set_diff S2 S1);

fun graph_link thy p graph =
 let val node = make_thyid thy
     val parents = map make_thyid p
 in
 if (Lib.all (Lib.C Graph.isin graph) parents)
 then if (Graph.isin node graph)
     then if (node_set_eq parents (#2(Graph.assoc node graph))) then graph
          else (Lib.mesg true
                 "link_parents: the theory has two unequal sets of parents";
                raise THEORY_ERR "link_parents" "")
     else Graph.add (node,parents) graph
 else let val baddies = Lib.filter (fn p => not(Graph.isin p graph)) parents
          val names = map thyid_name baddies
    in Lib.mesg true
        ("link_parents: the following parents are not in the graph: "^
          String.concat (commafy names));
       raise THEORY_ERR"link_parents" ""
    end
  end;

fun gen_link_parents thy p {thid,con_wrt_disk,STH,GR,
                            facts,overwritten,adjoin} =
    {GR=graph_link thy p GR,
     thid=thid,con_wrt_disk=con_wrt_disk,STH=STH,adjoin=adjoin,
     facts=facts,overwritten=overwritten};


local fun sfirst s GR = Graph.first (fn n => (thyid_name n = s)) GR
in
  fun parents_of s ({GR,...}:theory) = #2(sfirst s GR)
  fun graph_ancestry s (thy as {GR,...}) = Graph.ancestryl GR(parents_of s thy)
  fun graph_ancestryl nlist ({GR,...}:theory) = Graph.ancestryl GR nlist
  fun graph_fringe ({GR,...}:theory) = Graph.fringe GR
end;


(*---------------------------------------------------------------------------*
 *                 CREATE THE INITIAL THEORY.                                *
 *                                                                           *
 * To build this, we have to create the symbol table. Some day the impl. of  *
 * the ST should be traded in for a professional hashtable. We also create   *
 * an empty theory graph.                                                    *
 *---------------------------------------------------------------------------*)

local val table_size = 1999  (* some prime *)
      fun hasher s = Lib.hash table_size s (0,0);
      val ST = Array.array(table_size, ([]:stEntry list))
      val GR = Graph.empty thyid_eq
      val CT = ref (fresh_theory "scratch" (ST,hasher) GR)
in
  fun theCT() = !CT
  fun makeCT thry = (CT := thry);
end;

val CTid = theory_id o theCT;
val CTname = thyid_name o CTid;
val current_theory = CTname;


(*---------------------------------------------------------------------------*
 *   USING INFORMATION ON SPECIFIED ITEMS IN THE CURRENT THEORY              *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Return type constant just as it was declared.
 *---------------------------------------------------------------------------*)

fun type_decl x =
   lookup_type (theCT()) x
     (THEORY_ERR "type_decl" (Lib.quote x^" not found in signature"));

fun arity x =
   #arity(lookup_type (theCT()) x
           (THEORY_ERR"arity_of_type"
                 (Lib.quote x^" not found in type signature")))

fun is_type x = Lib.can type_decl x;

fun current_revision s = #revision(#occ(type_decl s));


(*---------------------------------------------------------------------------
 * Is an object wellformed (current) wrt the symtab, i.e., have none of its
 * constants been re-declared after it was built? A constant is
 * up-to-date if either 1) it was not declared in the current theory (hence
 * it was declared in an ancestor theory and is thus frozen); or 2) it was
 * declared in the current theory and its witness is up-to-date.
 *
 *---------------------------------------------------------------------------*)

local fun dirty (thy as {STH=(ST,_),...}:theory) =
           (mapST (fn (e as TERM{utd,...}) => (utd := false; e)
                    | (e as TYPE{utd,...}) => (utd := false; e)) ST; thy)

fun up2date_tyc thy (r as {name,...}) =
   let val {occ,theory,arity,witness,utd} =
        lookup_type thy name (THEORY_ERR"" "")
   in if (theory = thyid_name(theory_id thy))
      then (occ=r) andalso
           (!utd orelse
             (if (up2date_thm_opt thy witness)
              then (utd := true; true) else false))
      else true
   end handle HOL_ERR _ => false

and up2date_type thy ty =
   is_vartype ty
    orelse
   let val (c,args) = break_type ty
   in up2date_tyc thy c andalso Lib.all (up2date_type thy) args
   end

and up2date_const thy tm =
  let val (r as ref str,ty) = break_const tm
      val {name,theory,place,htype,witness,utd} =
       lookup_const thy str (THEORY_ERR"" "")
  in
    if (theory = thyid_name(theory_id thy))
    then (name=r) andalso
          (!utd orelse
           (if (up2date_thm_opt thy witness)
            then (utd := true; true) else false))
    else true
  end handle HOL_ERR _ => false

and up2date_term thy tm =  (* could use destructor for Abs, for more speed. *)
  case (Term.dest_term tm)
  of VAR{Ty,...}      => up2date_type  thy Ty
   | CONST _          => up2date_const thy tm
   | COMB{Rator,Rand} => up2date_term thy Rator andalso up2date_term thy Rand
   | LAMB{Bvar,Body}  => up2date_term thy Bvar  andalso up2date_term thy Body

and up2date_thm thy thm =
     Lib.all (up2date_term thy) (Thm.concl thm::Thm.hyp thm)
     andalso
     up2date_axioms thy (Tag.axioms_of (Thm.tag thm))

and up2date_thm_opt thy NONE = true
  | up2date_thm_opt thy (SOME thm) = up2date_thm thy thm

and up2date_axioms thy []    = true
  | up2date_axioms thy rlist =
     let val axs = map (drop_Axkind o snd) (thy_axioms thy)
     in Lib.all (up2date_term thy o Thm.concl o Lib.C Lib.assoc axs) rlist
     end handle HOL_ERR _ => false
in
  fun uptodate_type ty =
      if (#overwritten (theCT()))
      then (dirty (theCT()); up2date_type (theCT()) ty) else true
  fun uptodate_term tm =
      if (#overwritten (theCT()))
      then (dirty (theCT()); up2date_term (theCT()) tm) else true
  fun uptodate_thm thm =
      if (#overwritten (theCT()))
      then (dirty (theCT()); up2date_thm (theCT()) thm) else true

  fun scrub_sig s thy =
    let fun chk (TERM{name, theory, place,htype,witness,utd}) =
             if (theory=s)
             then (!utd orelse
                   (if (up2date_thm_opt thy witness) then (utd := true; true)
                    else false))
               else true
          | chk (TYPE{occ,arity,theory,witness,utd}) =
             if (theory=s)
             then (!utd orelse
                   (if (up2date_thm_opt thy witness) then (utd := true; true)
                    else false))
              else true
    in
      filterST chk (#1(#STH thy)); thy
    end

  fun scrub_ax s (thy as {thid,con_wrt_disk,STH,GR,
                          facts,overwritten,adjoin}) =
    let fun chk (_, Thm _ ) = true
          | chk (_, Defn _) = true
          | chk (_, Axiom(_,th)) = up2date_term thy (Thm.concl th)
    in
      {thid=thid, con_wrt_disk=con_wrt_disk, STH=STH,adjoin=adjoin,
       GR=GR, facts=Lib.gather chk facts,overwritten=overwritten}
    end

  fun scrub_thms s (thy as {thid,con_wrt_disk,STH,GR,
                            facts,overwritten,adjoin}) =
    let fun chk (_, Axiom _) = true
          | chk (_, Thm th ) = up2date_thm thy th
          | chk (_, Defn th) = up2date_thm thy th
    in
      {thid=thid, con_wrt_disk=con_wrt_disk, STH=STH,adjoin=adjoin,
       GR=GR, facts=Lib.gather chk facts, overwritten=overwritten}
    end

  fun scrub_thy s thy =
    let val thy' = dirty thy
        val {thid,con_wrt_disk,STH,GR,facts,overwritten,adjoin}
             = scrub_thms s
                  (scrub_ax s
                     (scrub_sig s thy'))
         in
           {overwritten=false,
            thid=thid,con_wrt_disk=con_wrt_disk,
            STH=STH,GR=GR,facts=facts,adjoin=adjoin}
         end
end;


fun scrub() = makeCT(scrub_thy (CTname()) (theCT()));

fun scrubCT() =
 (if !Globals.show_scrub
  then (Lib.say("Scrubbing "^CTname()^": "); Lib.time scrub()) else scrub()
  ;
  theCT());

fun scrubCT() = (scrub(); theCT());



(*---------------------------------------------------------------------------
 * Return term constant just as it was declared.
 *---------------------------------------------------------------------------*)

fun const_decl x =
  let val {name,htype,place,theory,...} = lookup_const (theCT()) x
          (THEORY_ERR "const_decl" (Lib.quote x^" not found in signature"))
  in
    {const=Const(name,htype),theory=theory,place=place}
  end;


(*---------------------------------------------------------------------------
 * Is a constant infix, prefix, or a binder.
 *---------------------------------------------------------------------------*)
fun fixity x = #place(const_decl x);

fun is_binder "\\" = true
  | is_binder s = (fixity s = Binder) handle HOL_ERR _ => false;

fun is_infix s =
   (case (fixity s) of (Infix _) => true
                     |  _        => false) handle HOL_ERR _ => false;

(*---------------------------------------------------------------------------*
 * The parsing precedence of a constant.                                     *
 *---------------------------------------------------------------------------*)
fun precedence x = case (fixity x) of Infix i => i | _ => 0;

(*---------------------------------------------------------------------------*
 * Is a string the name of a defined constant.                               *
 *---------------------------------------------------------------------------*)
fun is_constant x = Lib.can fixity x;

(*---------------------------------------------------------------------------*
 * Is a string the name of a polymorphic constant.                           *
 *---------------------------------------------------------------------------*)
fun is_polymorphic x =
  Type.polymorphic
    (#Ty(dest_const(#const(const_decl x)))) handle HOL_ERR _ => false;


(*---------------------------------------------------------------------------*
 * Making type constants.                                                    *
 *---------------------------------------------------------------------------*)
fun mk_type{Tyop, Args} =
  let val {occ,arity,...} = lookup_type (theCT()) Tyop
            (THEORY_ERR "mk_type" (Lib.quote Tyop^" is not a known HOL type"))
      val l = length Args
  in if arity = l
      then Tyapp (occ,Args)
       else raise THEORY_ERR "mk_type"
         (String.concat [Lib.quote Tyop, " (arity ", Lib.int_to_string arity,
                 ") is being applied to ", Lib.int_to_string l, " argument(s)"])
  end;

(*---------------------------------------------------------------------------*
 * Making constants without matching. Fails when tried on family members.    *
 *---------------------------------------------------------------------------*)
 fun prim_mk_const name =
   let val {name,htype,...} = lookup_const (theCT()) name
               (THEORY_ERR "mk_const" (Lib.quote name^" has not been defined"))
       val poly = Type.polymorphic htype
       val c = Const(name,htype)
   in fn [] => c
       | theta => if poly then Const(name, Type.type_subst theta htype) else c
   end;


fun get_const_from_theory thy {Name,Ty} =
 let val {name,htype,...} = lookup_const thy Name
                (THEORY_ERR"get_const_from_symtab"
                        (Lib.quote Name^" is not a known HOL constant"))
 in (case Type.match_type htype Ty
      of [] => Const (name,htype)
       | _  => Const (name,Ty))
    handle HOL_ERR _ => raise THEORY_ERR"get_const_from_symtab"
                       ("not a type instance: "^Lib.quote Name)
 end;

fun mk_const r = get_const_from_theory (theCT()) r;



(*---------------------------------------------------------------------------*
 *              WRITING INTO THE CURRENT THEORY                              *
 *---------------------------------------------------------------------------*)

local fun augmentCT f arg = makeCT(set_consistency false (f arg (theCT())))
in
  val add_typeCT        = augmentCT add_type_entry
  val add_termCT        = augmentCT add_term_entry
  fun add_axiomCT(r,ax) = augmentCT add_fact (!r, Axiom(r,ax))
  fun add_defnCT(s,def) = augmentCT add_fact (s,Defn def)
  fun add_thmCT(s,th)   = augmentCT add_fact (s,Thm th)

  fun delete_type n     = augmentCT del_type  (n,CTname())
  fun delete_const n    = (augmentCT del_const (n,CTname());
                           augmentCT del_const ("$"^n,CTname()));
  val delete_axiom      = augmentCT del_axiom
  val delete_theorem    = augmentCT del_theorem
  val delete_definition = augmentCT del_defn

  fun set_fixity s f    = augmentCT set_place (s,f,CTname())
  fun set_MLname s1 s2  = augmentCT set_MLbind (s1,s2)
  val adjoin_to_theory  = augmentCT new_addon
end;

fun set_ct_consistency b = makeCT(set_consistency b (theCT()))

(*---------------------------------------------------------------------------
 *            INSTALLING CONSTANTS IN THE CURRENT THEORY
 *---------------------------------------------------------------------------*)

fun new_type {Name,Arity} =
  if Lexis.allowed_type_constant Name
  then add_typeCT {name=Name, arity=Arity, theory = CTname()}
  else raise THEORY_ERR"new_type"
               (Lib.quote Name^" is not an allowed type name");

fun install_type(s,a,thy) = add_typeCT {name=s, arity=a, theory=thy};


(*---------------------------------------------------------------------------
 * Installing term constants.
 *---------------------------------------------------------------------------*)
local fun dollar {name, theory, place, htype} =
       {name = "$"^name, theory=theory, place=Prefix, htype=htype};
fun infixx s ty =
   if (Lib.can Type.dom_rng (snd(Type.dom_rng ty))) then ()
   else raise THEORY_ERR s "not an infix type"
fun binder s ty =
   if (Lib.can Type.dom_rng (fst(Type.dom_rng ty))) then ()
   else raise THEORY_ERR s "not a binder type"
fun write_constant err_str fixity (c as {Name,Ty}) =
 ( case fixity
     of Prefix => ()
      | Binder => binder err_str Ty
      | Infix prec =>
         (infixx err_str Ty;
          if (prec < 0)
           then raise THEORY_ERR err_str "precedence must be positive"
           else ());
   if (Lexis.allowed_term_constant Name) then ()
   else raise THEORY_ERR err_str
                 (Lib.quote Name^ " is not an allowed constant name");
   let val trec = {name=Name, htype=Ty, place=fixity, theory=CTname()}
       val dtrec = dollar trec
   in
      add_termCT trec; add_termCT dtrec
   end)
in
  val new_constant = write_constant "new_constant" Prefix
  val new_binder   = write_constant "new_binder"   Binder
  fun new_infix{Name,Ty,Prec} =
     write_constant "new_infix" (Infix Prec) {Name=Name,Ty=Ty}

  (*--------------------------------------------------------------------------
   * Add a constant to the signature. This entrypoint is for adding constants
   * from parent theories.
   *-------------------------------------------------------------------------*)
  fun install_const(s,ty,f,thy) =
     let val entry = {name=s, htype=ty, theory=thy, place=f}
     in
       add_termCT entry;
       add_termCT (dollar entry)
     end;
end;


(*---------------------------------------------------------------------------*
 *   WRITING AXIOMS, DEFINITIONS, AND THEOREMS INTO THE CURRENT THEORY       *
 *---------------------------------------------------------------------------*)

local fun check_name (fname,s) = ()
      fun empty_hyp th =
         if (Portable_List.null (Thm.hyp th)) then ()
         else raise THEORY_ERR "save_thm" "non empty assumption set"
in
fun new_axiom (name,tm) =
   let val rname = ref name
       val ax = mk_axiom_thm (rname,tm)
       val  _ = check_name ("new_axiom",name)
   in
     if (uptodate_term tm) then add_axiomCT(rname,ax)
     else raise THEORY_ERR "new_axiom" "out-of-date!";
     ax
   end

fun add_tm_witnessCT s wthm =
   let val thy = theCT()
   in
      add_tm_witness thy s wthm;
      add_tm_witness thy (dollar s) wthm
   end;

fun store_definition(name, consts, wthm, tm) =
  let val () = check_name ("store_definition",name)
      val tag = Thm.tag wthm
      val def = mk_defn_thm tag tm
      val _ = if (uptodate_thm def) then ()
              else raise THEORY_ERR "store_definition" "out-of-date!"
  in
    case consts
      of LEFT s => (add_ty_witness (theCT()) s wthm; ())
       | RIGHT slist => (map (fn s => add_tm_witnessCT s wthm) slist; ());
    add_defnCT(name,def);
    def
  end;


fun save_thm (name,th) =
   ( check_name ("save_thm",name);
     if (uptodate_thm th) then add_thmCT(name,th)
     else raise THEORY_ERR "save_thm" "out-of-date!";
     th )
end;

(*---------------------------------------------------------------------------
 * Adding a new theory into the current theory graph.
 *---------------------------------------------------------------------------*)
fun link_parents thy p = makeCT(gen_link_parents thy p (theCT()));

fun incorporate_types thy tys =
  let fun itype (s,i) = install_type(s,i,thy)
  in app itype tys
  end;

fun incorporate_consts thy consts =
  let fun iconst(s,ty,f) = install_const(s,ty,f,thy)
  in app iconst consts
  end;


(*---------------------------------------------------------------------------*
 *              GENERAL INFORMATION ON THE CURRENT THEORY                    *
 *---------------------------------------------------------------------------*)
local val dollar = #"$"
      val infixed = is_infix o #Name o dest_const
      val bindered = is_binder o #Name o dest_const
      fun convert_type_recd{occ={name,...},arity,...} = {Name=name,Arity=arity}
      fun convert_term_recd{name,htype,...} =
            if (String.sub(!name,0) = dollar)
            then raise THEORY_ERR"convert_term_recd" "dollared"
            else mk_const{Name = !name,Ty=htype}
      fun grab_item style name alist =
         case (Lib.assoc1 name alist)
         of SOME (_,th) => th
          | NONE => raise THEORY_ERR style
                     ("couldn't find "^style^" named "^Lib.quote name)
in
 fun types s     = map convert_type_recd(thy_types s (theCT()))
 fun constants s = mapfilter convert_term_recd (thy_constants s (theCT()))
 fun infixes x   = Lib.gather infixed (constants x)
 fun binders x   = Lib.gather bindered (constants x)
 fun axioms()      = map drop_pthmkind (thy_axioms (theCT()))
 fun definitions() = map drop_pthmkind (thy_defns (theCT()))
 fun theorems()    = map drop_pthmkind (thy_theorems (theCT()))
 fun axiom s       = grab_item "axiom" s (axioms())
 fun definition s  = grab_item "definition" s (definitions())
 fun theorem s     = grab_item "theorem" s (theorems())

 fun parents "-" = map thyid_name (graph_fringe(theCT()))
   | parents str = if (str=CTname()) then parents"-"
      else map thyid_name (parents_of str (theCT()))
         handle HOL_ERR _
           => raise THEORY_ERR"parents" (Lib.quote str^" not in theory graph.")
end;

fun ancestry s0 =
 let val ct = theCT()
     fun anc "-" = map thyid_name (graph_ancestryl (graph_fringe ct) ct)
       | anc s = if (s=CTname()) then anc "-"
                  else map thyid_name (graph_ancestry s ct)
 in anc s0
 end


(*---------------------------------------------------------------------------*
 *          PRINTING THEORIES OUT AS ML STRUCTURES AND SIGNATURES.           *
 *---------------------------------------------------------------------------*)

fun theory_out f {name,style} ostrm =
 let val ppstrm = Portable_PrettyPrint.mk_ppstream
     {consumer = Portable.outputc ostrm,
      linewidth=78, flush = fn () => Portable.flush_out ostrm}
 in f ppstrm handle e => (Portable.close_out ostrm; raise e);
    Portable_PrettyPrint.flush_ppstream ppstrm;
    Portable.close_out ostrm
 end;


fun dconst {name,place,htype,theory,witness,utd} =
  let val _ = Lib.assert (not o dollared) (!name)
  in (!name,htype,place)
  end;

fun dty{occ={name,revision},arity,theory,witness,utd} = (name,arity);

fun unkind facts =
  List.foldl (fn ((s,Axiom (_,th)),(A,D,T)) => ((s,th)::A,D,T)
               | ((s,Defn th),(A,D,T)) => (A,(s,th)::D,T)
               | ((s,Thm th),(A,D,T)) => (A,D,(s,th)::T)) ([],[],[]) facts;

val utd_types  = Lib.gather uptodate_type;
val utd_consts = Lib.gather uptodate_term;
val utd_thms   = Lib.gather uptodate_thm;

(* automatically reverses the list, which is what is needed. *)
fun unadjzip [] A = A
  | unadjzip ({sig_ps,struct_ps}::t) (l1,l2) =
       unadjzip t (sig_ps::l1, struct_ps::l2)

(*---------------------------------------------------------------------------
    We always export the theory, except if it is the initial theory (named
    "scratch") and the initial theory is empty. If the initial theory is
    *not* empty, i.e., the user made some definitions, or stored some
    theorems or whatnot, then the initial theory will be exported.
 ----------------------------------------------------------------------------*)

fun gen_export_theory(thy as {thid,con_wrt_disk,STH,GR,
                              facts,adjoin,...}:theory) =
  if con_wrt_disk
   then (Lib.say ("\nTheory "^Lib.quote(thyid_name thid)^" already \
                    \consistent with disk, hence not exported.\n");
         SUCCESS ())
  else
  let val concat = Portable_String.concat
      val thyname = thyid_name thid
      val name = CTname()^"Theory"
      val (A,D,T) = unkind facts
      val (sig_ps, struct_ps) = unadjzip adjoin ([],[])
      val sigthry = {name = thyname,
                  parents = map thyid_name (Graph.fringe GR),
                   axioms = A,
              definitions = D,
                 theorems = T,
                   sig_ps = sig_ps}
      val structthry
             = {theory = dest_thyid thid,
               parents = map dest_thyid (Graph.fringe GR),
                 types = map dty (thy_types thyname thy),
             constants = Lib.mapfilter dconst (thy_constants thyname thy),
                axioms = A,
           definitions = D,
              theorems = T,
             struct_ps = struct_ps}
  in
   case filter (not o Lexis.ok_sml_identifier) (map fst (A@D@T))
    of [] =>
       (let val ostrm1 = Portable.open_out(concat["./",name,".sig"])
            val ostrm2 = Portable.open_out(concat["./",name,".sml"])
        in
          Lib.say "Exporting theory ... ";
          theory_out (fn ppstrm => TheoryPP.pp_theory_sig ppstrm sigthry)
                     {name = name, style = "signature"} ostrm1;
          theory_out (fn ppstrm => TheoryPP.pp_theory_struct ppstrm structthry)
                     {name = name, style = "structure"} ostrm2;
          set_ct_consistency true;
          Lib.say "done.\n";
          SUCCESS ()
        end
        handle e => (Lib.say "\nFailure while writing theory!\n";
                     FAILURE (SYSTEM e)))
     | badnames =>
        (Lib.say (String.concat
          ["\nThe following ML binding names in the theory to be exported:\n",
           String.concat (Lib.commafy (map Lib.quote badnames)),
           "\n are not acceptable ML identifiers.\n",
              "   Use `set_MLname' to change each name."]);
         FAILURE (CLIENT badnames))
  end
  handle e => FAILURE (INTERNAL e);



fun prim_export_theory () = gen_export_theory (scrubCT());

fun export_theory () =
  case prim_export_theory ()
   of SUCCESS _ => ()
    | FAILURE (CLIENT nl) => ()
    | FAILURE (INTERNAL x) => raise x
    | FAILURE (SYSTEM x)   => raise x;



datatype clientfixable = BADNAMES of string list
                       | EXN of exn

(*---------------------------------------------------------------------------*
 *    Allocate a new theory segment over an existing one.                    *
 *---------------------------------------------------------------------------*)

fun gen_new_theory str (thy as {thid,con_wrt_disk,STH, GR,facts,...}:theory) =
  if not(Lexis.ok_identifier str)
  then FAILURE (CLIENT(EXN (THEORY_ERR"new_theory"
       ("proposed theory name "^Lib.quote str^" is not an identifier"))))
  else
  let val thyname = thyid_name thid
      fun gen_thy g = (Lib.mesg true ("Created theory "^Lib.quote str);
                      SUCCESS(fresh_theory str STH g))
  in
     if (str=thyname)
     then (Lib.mesg true ("Restarting theory "^Lib.quote str);
           SUCCESS (zap str thy) handle e => FAILURE (INTERNAL e))
     else
     if (mem str (map thyid_name (graph_ancestry thyname thy)
        handle HOL_ERR _ => []))
     then FAILURE(CLIENT(EXN(THEORY_ERR "new_theory"
               ("theory: "^Lib.quote str^" already exists."))))
     else
     if (thyname = "scratch" andalso empty_theory thy) then gen_thy GR
     else
     if con_wrt_disk then gen_thy (Graph.add (thid, graph_fringe thy) GR)
     else (scrub_thy thyname thy;
           case gen_export_theory thy
            of SUCCESS () => gen_thy (Graph.add (thid, graph_fringe thy) GR)
             | FAILURE (CLIENT nl) => FAILURE (CLIENT (BADNAMES nl))
             | FAILURE (INTERNAL x) => FAILURE(INTERNAL x)
             | FAILURE (SYSTEM x)   => FAILURE (SYSTEM x))
   end handle e => FAILURE (INTERNAL e);

fun prim_new_theory str =
  case gen_new_theory str (theCT())
   of SUCCESS x => (SUCCESS (makeCT x) handle e => FAILURE (INTERNAL e))
    | FAILURE x  => FAILURE x;

fun new_theory str =
  case prim_new_theory str
   of FAILURE (CLIENT (EXN e)) => raise e
    | FAILURE (CLIENT (BADNAMES _)) => ()
    | FAILURE (INTERNAL e) => raise e
    | FAILURE (SYSTEM e) => raise e
    | SUCCESS _ => ();


(*--------------------------------------------------------------------------*
 * Print a theory for the user.                                             *
 *--------------------------------------------------------------------------*)

val CONSISTENT   = Portable_PrettyPrint.CONSISTENT
val INCONSISTENT = Portable_PrettyPrint.INCONSISTENT;

fun pp_theory ppstrm (thy as {thid,con_wrt_disk,STH,
                              GR,facts,overwritten,adjoin}) =
 let val {add_string,add_break,begin_block,end_block, add_newline,
          flush_ppstream,...} = Portable_PrettyPrint.with_ppstream ppstrm
     val pp_type = Hol_pp.pp_type ppstrm
     val pp_thm = Thm.pp_thm ppstrm
     fun vblock(header, ob_pr, obs) =
           ( begin_block CONSISTENT 4;
             add_string (header^":");
             add_newline();
             Portable_PrettyPrint.pr_list ob_pr
                 (fn () => ()) add_newline obs;
             end_block(); add_newline(); add_newline())
     fun pr_thm (heading, ths) =
        vblock(heading, (fn (s,th) =>
          (begin_block CONSISTENT 0; add_string s; add_break(1,0);
              pp_thm th; end_block())),  ths)
     val thyname = thyid_name thid
     fun pp_consistency b =
        add_string ("Theory "^(Lib.quote thyname)^" is "^
                (if b then "consistent" else "inconsistent")^" with disk.\n")
     val (A,D,T) = unkind facts
     val types = map dty (thy_types thyname thy)
     val constants = Lib.mapfilter dconst (thy_constants thyname thy)
 in
    begin_block CONSISTENT 0;
    add_string ("Theory: "^thyname);
    add_newline();   add_newline() ;
    vblock ("Parents", add_string, map thyid_name (Graph.fringe GR))
      ;
    vblock ("Type constants",
            (fn (name,arity) =>
                (add_string name; add_string (" "^Lib.int_to_string arity))),
            rev types)
      ;
    vblock ("Term constants",
             (fn (name,htype,place)
              => (begin_block CONSISTENT 0;
                  add_string (name^" ");
                  add_string ("("^Term.fixity_to_string place^")");
                  add_break(3,0);
                  add_string ":";
                  pp_type htype;
                  end_block())),
                 rev constants)
      ;
    pr_thm ("Axioms", A);
    pr_thm ("Definitions", D);
    pr_thm ("Theorems", T);
    pp_consistency con_wrt_disk;
    end_block();
    flush_ppstream()
 end;


fun print_theory_to_outstream outstream =
  let val def_Cons = Portable_PrettyPrint.defaultConsumer()
      val consumer = {consumer = Portable.outputc outstream,
                      flush = #flush def_Cons,
                      linewidth = #linewidth def_Cons}
      val _ = pp_theory (Portable_PrettyPrint.mk_ppstream consumer) (theCT())
      val _ = Portable.flush_out outstream
  in outstream end

fun print_theory_to_file file =
    let val outfile = Portable.open_out file
    in Portable.close_out (print_theory_to_outstream outfile)
    end

fun print_theory () =
   pp_theory (Portable_PrettyPrint.mk_ppstream
                     (Portable_PrettyPrint.defaultConsumer()))
             (theCT())


(* Backpatching forward references. *)
val _ = Type.init mk_type current_revision;
val _ = Term.init is_constant mk_const const_decl;

(*---------------------------------------------------------------------------*
 * Provide hidden function "store_definition" to the definition principles.  *
 * Why 3? Because it gets used in Const_spec, Const_def, and Type_def.       *
 *---------------------------------------------------------------------------*)
local val used = ref 0
in
  fun expose_store_definition r =
     if (!used = 3) then ()
     else (r := store_definition; used := !used + 1)
end;

end; (* THEORY *)
