(* ========================================================================== *)
(* FILE          : TheoryReader.sml                                           *)
(* DESCRIPTION   : Read theory data from disk                                 *)
(*                                                                            *)
(* AUTHOR        : Thibault Gauthier, University of Innsbruck                 *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure TheoryReader :> TheoryReader =
struct

type thm      = Thm.thm;
type term     = Term.term
type hol_type = Type.hol_type

open HolKernel SharingTables RawTheory_dtype RawTheoryReader

fun temp_encoded_update (strings, terms) thyname {data,ty} =
    Theory.LoadableThyData.temp_encoded_update {
      thy = thyname,
      thydataty = ty,
      shared_readmaps = {strings = fn i => Vector.sub (strings, i),
                         terms = Term.read_raw terms},
      data = data
    }


(* A theory's data as decoded from its .dat file, with the values the
   source loader built: enough to repeat its registration without
   reading or decoding the file again: the shared strings and terms
   the theory data refers to, not the whole sharing table.  [refs] are
   the other theories' kernel entries the file's id table names, with
   what decoding read from each: a type operator's arity and a
   constant's principal type (NONE where there is no such entry).  The
   decoded values depend on those and on the file's bytes only. *)
type kernel_ref = SharingTables.id * int option * hol_type option
type decoded = {thyname : string,
                parents : (string * string) list,
                new_types : (string * int) list,
                new_consts : (string * hol_type) list,
                refs : kernel_ref list,
                strings : string vector, terms : term vector,
                theorems : (string * thm * DB_dtype.thminfo) list,
                thydata : {data : HOLsexp.t, ty : string} list}

val decoded_tag : decoded MLSYSPortable.persistent_tag =
    MLSYSPortable.new_persistent_tag ()
val values_tag : (string * thm vector) MLSYSPortable.persistent_tag =
    MLSYSPortable.new_persistent_tag ()
val digest_tag : string MLSYSPortable.persistent_tag =
    MLSYSPortable.new_persistent_tag ()

fun decoded_name ({thyname,...} : decoded) = thyname
fun decoded_parents ({parents,...} : decoded) = map #1 parents
fun decoded_theorems ({theorems,...} : decoded) = theorems

fun kernel_ref (id as {Thy,Other}) : kernel_ref =
    (id, Type.op_arity {Thy = Thy, Tyop = Other},
     Lib.total (Term.type_of o Term.prim_mk_const) {Thy = Thy, Name = Other})

fun same_ref ((id, arity, ty) : kernel_ref) =
    let
      val (_, arity', ty') = kernel_ref id
    in
      arity = arity' andalso
      (case (ty, ty') of
           (NONE, NONE) => true
         | (SOME a, SOME b) => Type.compare (a, b) = EQUAL
         | _ => false)
    end

(* Theories whose kernel ids are the same in every process sharing the
   saved state: those in it ("min" is built by the kernel itself) and
   theories loaded with canonical stamps whose parents are canonical. *)
val canonical_thys : string HOLset.set Sref.t =
    Sref.new (HOLset.singleton String.compare "min")
fun is_canonical thy = HOLset.member (Sref.value canonical_thys, thy)

(* An entry of another theory can be relied on to carry the id it was
   decoded with only if that theory is canonical. *)
fun refs_current ({refs,...} : decoded) =
    List.all (fn (r as ({Thy, ...}, _, _) : kernel_ref) =>
                 is_canonical Thy andalso same_ref r)
             refs

fun note_load thyname (parents : (string * string) list) stamps_canonical =
    if stamps_canonical andalso List.all (is_canonical o #1) parents then
      Sref.update canonical_thys (fn s => HOLset.add (s, thyname))
    else ()

(* The rest of a load, once the theory's types and constants exist. *)
fun bind_data ({thyname,strings,terms,theorems,thydata,...} : decoded) =
    (DB.bindl thyname theorems;
     app (temp_encoded_update (strings, terms) thyname) thydata;
     theorems)

val capture = ref false
val captured : decoded option ref = ref NONE

(* Links [thyname] into the theory graph and adds its kernel entries by
   [register], all or nothing: on failure the context is rolled back, so
   no context has the theory linked without its entries; on success the
   theory is sealed, so they can't be changed afterwards.  The flag
   [register] returns says whether the entries got canonical stamps.
   An interrupt arriving before the seal rolls the load back; one
   arriving after it leaves the sealed theory loaded, since the sealed
   set isn't part of the context and a rollback would leave the theory
   sealed but missing. *)
fun register_atomically thyname parents register =
    let
      val _ = not (Thm.is_sealed thyname) orelse
              raise TheoryReader ("theory " ^ thyname ^ " is already sealed")
      val ctxt = Context.snapshot ()
    in
      let
        val (result, stamps_canonical) = register ()
      in
        Thm.mark_sealed thyname;
        note_load thyname parents stamps_canonical;
        result
      end handle e => ((if Thm.is_sealed thyname then ()
                        else Context.restore ctxt);
                       raise e)
    end

(* Decodes a theory's .dat as a load does, linking it into the theory
   graph under [hash], adding its types and constants to the kernel
   signature and sealing it, but registers nothing else.  The flag says
   whether the theory's kernel ids are canonical: its own entries got
   canonical epochs and its parents are canonical. *)
fun decode_thydata {thyname,path,hash} =
    let
      open HOLsexp
      val rawthy as {parents,tables,exports,name=stored_name,...} =
            load_raw_thydata {path=path}
      fun mungename {thy,hash} = (thy,hash)
      val _ = thyname = stored_name orelse
              raise TheoryReader
                    ("reading at " ^ path ^ " for theory " ^ thyname ^
                     " and got theory called " ^ stored_name ^ " instead")
      val parents = map mungename parents
      val {types=new_types,consts=new_consts} = #newsig rawthy
      val stamps = ref true
      val consts = ref []
      fun before_types () =
          stamps := Theory.incorporate_types thyname new_types
      fun before_terms tyv =
          let
            val cs = map (fn (n,i) => (n,Vector.sub(tyv,i))) new_consts
          in
            consts := cs;
            stamps := (Theory.incorporate_consts thyname cs andalso !stamps)
          end
      val thydata =
          force "thydata" (
            Option.map (map (fn (ty,d) => {data=d,ty=ty})) o
            list_decode(pair_decode(string_decode, SOME))
          )
          (#thydata rawthy)
      val share_data =
          register_atomically thyname parents (fn () =>
            (Theory.link_parents (thyname, hash) parents;
             let
               val sd = dec_sdata {
                          before_types = before_types,
                          before_terms = before_terms,
                          tables = tables,
                          exports = exports
                        }
             in
               (sd, !stamps)
             end))
      val (strings, terms) = shared_vectors share_data
      val refs =
          Vector.foldr (fn (id as {Thy,...}, rs) =>
                           if Thy = thyname then rs else kernel_ref id :: rs)
                       [] (shared_ids share_data)
      val {theorems, ...} = export_from_sharing_data share_data
    in
      ({thyname = thyname, parents = parents,
        new_types = new_types, new_consts = !consts, refs = refs,
        strings = strings, terms = terms, theorems = theorems,
        thydata = thydata},
       is_canonical thyname)
    end

fun load_thydata_from_dat args =
    let
      val (d, _) = decode_thydata args
      val named_thms = bind_data d
      val _ = if !capture then captured := SOME d else ()
  in
    List.foldl (fn ((n,th,i), D) => Symtab.update (n, (th,i)) D)
               Symtab.empty
               named_thms
  end handle Interrupt => raise Interrupt
           | e => raise TheoryReader ("Exception raised: " ^
                                      General.exnMessage e)

fun capture_decoded f x =
    let
      val _ = capture := true
      val _ = captured := NONE
      val result = (f x handle e => (capture := false; captured := NONE;
                                     raise e))
      val d = !captured
    in
      capture := false; captured := NONE; (result, d)
    end

(* Whether decoded values mean the same here as where they were decoded:
   their parents are canonical and the other theories' entries they refer
   to are unchanged. *)
fun kernel_refs_ok (d as {parents,...} : decoded) =
    List.all (is_canonical o #1) parents andalso refs_current d

(* The kernel part of load_thydata_from_dat's registration, from decoded
   values for which kernel_refs_ok holds: link the theory under [hash]
   and add its types and constants, which must get their canonical stamps
   again since the values carry them. *)
fun link_kernel hash ({thyname,parents,new_types,new_consts,...}
                      : decoded) =
    let
      fun register () =
          let
            val _ = Theory.link_parents (thyname, hash) parents
            val types_ok = Theory.incorporate_types thyname new_types
            val consts_ok = Theory.incorporate_consts thyname new_consts
          in
            types_ok andalso consts_ok orelse
            raise TheoryReader ("theory " ^ thyname ^
                                ": kernel entries not canonically stamped");
            ((), true)
          end
    in
      register_atomically thyname parents register
    end handle Interrupt => raise Interrupt
             | e as TheoryReader _ => raise e
             | e => raise TheoryReader ("Exception raised: " ^
                                        General.exnMessage e)

fun register_kernel hash (d as {thyname,...} : decoded) =
    (kernel_refs_ok d orelse
     raise TheoryReader ("theory " ^ thyname ^
                         ": decoded against other kernel entries");
     link_kernel hash d)

(* Repeats load_thydata_from_dat's registration in the same order, unless
   kernel_refs_ok fails: then registers nothing and returns false. *)
fun register_decoded hash d =
    kernel_refs_ok d andalso (link_kernel hash d; ignore (bind_data d); true)
    handle Interrupt => raise Interrupt
         | e as TheoryReader _ => raise e
         | e => raise TheoryReader ("Exception raised: " ^
                                    General.exnMessage e)

(* What a theory's load builds from its decoded data [decoded] alone,
   made where the theory's module is written so that loads from the
   module needn't build it again: the read theory data by type and the
   theory's DB shard. *)
type prepared = {decoded : decoded,
                 segments : (string * Theory.LoadableThyData.t) list,
                 names : DB.shard}
val prepared_tag : prepared option MLSYSPortable.persistent_tag =
    MLSYSPortable.new_persistent_tag ()

(* The theory data types prepare reads, as they were when fix_preparers
   was last called: bossLib calls it, so that they are those of
   bin/hol.state and of every state built on it, in the processes that
   write modules and in those that load them.  A module refers to their
   operations in the saved state it depends on rather than copying them.
   Only ThyDataSexp's types are read: their reader builds plain data. *)
val fixed : string list option ref = ref NONE
fun fix_preparers () = fixed := SOME (ThyDataSexp.sexp_types ())

(* From [d] alone; NONE when reading theory data here depends on more
   than the data, or fix_preparers wasn't called. *)
fun prepare (d as {thyname, strings, terms, theorems, thydata, ...}
             : decoded) =
    case (!fixed, ThyDataSexp.default_readers ()) of
        (SOME types, true) =>
        SOME {decoded = d,
              segments =
                Theory.LoadableThyData.read_segments
                  (fn ty => List.exists (fn t => t = ty) types)
                  {strings = fn i => Vector.sub (strings, i),
                   terms = Term.read_raw terms}
                  (map (fn {data, ty} => {thydataty = ty, data = data})
                       thydata),
              names = DB.shard_of thyname theorems}
      | _ => NONE

val offered_segments = ref 0
val installed_segments = ref 0
fun prepared_statistics () =
    {offered = !offered_segments, installed = !installed_segments}

fun bind_prepared ({thyname,strings,terms,theorems,thydata,...} : decoded)
                  ({segments, names, ...} : prepared) =
    let
      val installed = Theory.LoadableThyData.install_segments
                        {thy = thyname, data = segments}
    in
      offered_segments := !offered_segments + length segments;
      installed_segments := !installed_segments + length installed;
      DB.bind_shard thyname names theorems;
      app (fn e as {ty, ...} =>
              if List.exists (fn t => t = ty) installed then ()
              else temp_encoded_update (strings, terms) thyname e)
          thydata
    end

(* register_decoded, using [p] instead of building what it holds again
   when p was made from [d] and reading theory data here depends only on
   the data. *)
fun register_prepared hash d (p : prepared option) =
    case p of
        SOME (p as {decoded, ...}) =>
        if MLSYSPortable.pointer_eq (decoded, d) andalso
           ThyDataSexp.default_readers ()
        then
          kernel_refs_ok d andalso (link_kernel hash d; bind_prepared d p;
                                    true)
          handle Interrupt => raise Interrupt
               | e as TheoryReader _ => raise e
               | e => raise TheoryReader ("Exception raised: " ^
                                          General.exnMessage e)
        else register_decoded hash d
      | NONE => register_decoded hash d

(* Hook for alternative theorem sources. Default is to read from .dat files. *)
val load_thydata_fn :
    ({thyname:string,path:string,hash:string} ->
     (Thm.thm * DB_dtype.thminfo) Symtab.table) ref
    = ref load_thydata_from_dat

fun load_thydata (args as {thyname, hash, ...}) = let
  val result = (!load_thydata_fn) args
  val () = Tracing.record_signature {theory=thyname, hash=hash}
in result end

fun default_loader () =
    MLSYSPortable.pointer_eq (!load_thydata_fn, load_thydata_from_dat)

end;  (* TheoryReader *)
