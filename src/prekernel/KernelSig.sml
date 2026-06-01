structure KernelSig :> KernelSig =
struct

  type kernelname = {Thy : string, Name : string}
  fun equal x y = (x = y)
  fun name_compare ({Thy = thy1, Name = n1}, {Thy = thy2, Name = n2}) =
      case String.compare (n1, n2) of
        EQUAL => String.compare(thy1,thy2)
      | x => x

  fun name_toString {Thy,Name} = Thy ^ "$" ^ Name
  fun name_toMLString {Thy,Name} =
    "{Thy=\"" ^ String.toString Thy ^ "\",Name=\"" ^ String.toString Name ^ "\"}"

  type kernelid = {name : kernelname, epoch : int, uptodate : bool ref}
    (* name and epoch are immutable and together provide id_compare's
       total order, so Termtab keys built on Term.compare stay sorted
       across retires.  The uptodate flag is the only mutable component:
       retire_id flips it to false; consumers read it via uptodate_id. *)

  (* Monotone counter bumped on every retire_id.  Lets downstream listeners
     (ThmSetData, AncestryData, GrammarDeltas) skip their O(n) "scan all
     stored deltas for staleness" work when no constant/type has been
     retired since the last scan.  A constant's uptodate flag only flips
     via retire_id, so the counter is a sound summary of "has any stored
     delta potentially become stale?". *)
  val retire_counter = Sref.new 0
  fun retire_epoch () = Sref.value retire_counter

  fun name_of_id ({name,...} : kernelid) = name
  fun uptodate_id ({uptodate,...} : kernelid) = !uptodate
  fun epoch_of ({epoch,...} : kernelid) = epoch
  fun new_id n = {name = n, epoch = retire_epoch(), uptodate = ref true}
  fun retire_id ({uptodate,...} : kernelid) = (
    uptodate := false;
    Sref.update retire_counter (fn n => n + 1)
  )
  fun name_of ({name = {Name,...}, ...} : kernelid) = Name
  fun seg_of ({name = {Thy,...}, ...} : kernelid) = Thy
  fun id_toString id = name_toString (name_of_id id)
  fun id_compare(id1, id2) =
      case name_compare(name_of_id id1, name_of_id id2) of
          EQUAL => Int.compare(epoch_of id1, epoch_of id2)
        | x => x

  (* Name an id presents to pretty-printers and other display sites.
     For up-to-date ids this is just the bare Name; for retired ones it
     is the Globals.oldify form, which embeds the id's epoch so
     successive retirements of the same name don't collide. *)
  fun display_name_of_id id =
      let val {Name,...} = name_of_id id in
        if uptodate_id id then Name
        else Globals.oldify (epoch_of id) Name
      end

  type 'a thytable = (kernelid * 'a) Symtab.table
  type 'a symboltable =
       ('a thytable Symtab.table * string list Symtab.table *int) Sref.t
  (* components:
       - map from theory*name -> kernelid (staged over two levels),
       - map from name to theory list,
       - total size (number of entries of first map)
  *)
  exception NoSuchThy of string
  exception NotPresent of kernelname
  datatype 'a symtab_error = Success of 'a
                           | Failure of exn
  fun isSuccess (Success _) = true | isSuccess _ = false

  fun new_table() = Sref.new (Symtab.empty, Symtab.empty, 0)
  fun peek(tab : 'a symboltable, knm as {Thy,Name}) =
      case Symtab.lookup (#1 (Sref.value tab)) Thy of
          NONE => Failure (NoSuchThy Thy)
        | SOME m => case Symtab.lookup m Name of
                        NONE => Failure (NotPresent knm)
                      | SOME r => Success r
  fun find(tab,knm) =
      case peek(tab, knm) of
          Failure e => raise e
        | Success r => r
  fun remove(tab, knm as {Thy,Name}) =
      let
        fun upd (t as (kmap,tmap,c)) =
            case Symtab.lookup kmap Thy of
                NONE => (t, Failure (NoSuchThy Thy))
              | SOME m =>
                case Symtab.lookup m Name of
                    NONE => (t, Failure (NotPresent knm))
                  | SOME kid => let val m' = Symtab.delete Name m
                                in
                                  ((Symtab.update(Thy,m') kmap,
                                    Symtab.remove_list equal (Name,Thy) tmap,
                                    c-1),
                                   Success kid)
                                end
      in
        Sref.gen_update tab upd
      end

  fun numItems (tab : 'a symboltable) = #3 (Sref.value tab)

  fun app f (tab : 'a symboltable) =
      let
        fun perthyapp (thy,m) () =
            Symtab.fold (fn (nm,(id,v)) => fn () => f ({Thy=thy,Name=nm},(id,v))) m ()
      in
        Symtab.fold perthyapp (#1 (Sref.value tab)) ()
      end

  fun foldl f acc (tab : 'a symboltable) =
      let
        fun perthyfold (thy,m) A =
            Symtab.fold (fn (nm,id) => fn A => f ({Thy=thy,Name=nm}, id, A)) m A
      in
        Symtab.fold perthyfold (#1 (Sref.value tab)) acc
      end

  fun retire_name (r, n) =
      case remove(r, n) of
        Failure e => raise e
      | Success (kid, _) => retire_id kid

  fun insert(tab : 'a symboltable, n as {Thy,Name}, v) = let
    val _ = retire_name(tab,n) handle NoSuchThy _ => ()
                                    | NotPresent _ => ()
    (* new_id must come AFTER retire_name: retire_name bumps retire_counter,
       so the new id picks up a strictly larger epoch than its retired
       predecessor (if any) and id_compare keeps them distinct. *)
    val id = new_id n
    fun upd (kmap, tmap, c) =
        let val kmap' = Symtab.map_default (Thy,Symtab.make[(Name,(id,v))])
                                           (Symtab.update(Name,(id,v)))
                                           kmap
            val tmap' = Symtab.insert_list equal (Name,Thy) tmap
            val c' = c + 1
        in
          (kmap',tmap',c')
        end
  in
    Sref.update tab upd;
    id
  end

  fun uptodate_name (r, n) = let
    val (kid, _) = find(r, n)
  in
    uptodate_id kid
  end

  fun listItems r =
      List.rev (foldl (fn (knm,v,A) => (knm,v) :: A) [] r)
  fun listThy (tab : 'a symboltable) thy =
      case Symtab.lookup (#1 (Sref.value tab)) thy of
          NONE => []
        | SOME m =>
          Symtab.fold (fn (nm, (kid,v)) => fn A =>
                          if uptodate_id kid then
                            ({Thy = thy,Name = nm},(kid,v)) :: A
                          else A)
                      m
                      []

  fun listName tab nm =
      let
        val (_, tmap, _) = Sref.value tab
        val thys = case Symtab.lookup tmap nm of NONE => [] | SOME xs => xs
        val knms = map (fn thy => {Thy = thy, Name = nm}) thys
      in
        map (fn k => (k, find(tab, k))) knms
      end

  fun del_segment (r : 'a symboltable, thyname) = let
    fun appthis (knm, _) =
        if #Thy knm = thyname then retire_name(r,knm)
        else ()
  in
    app appthis r
  end

  fun thyExists (tab : 'a symboltable) thy =
      Symtab.defined (#1 (Sref.value tab)) thy
  fun nameExists (tab: 'a symboltable) n =
      Symtab.defined (#2 (Sref.value tab)) n


end
