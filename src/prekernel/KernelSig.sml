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

  type kernelid = {name : kernelname, epoch : int}
    (* name and epoch are immutable and together provide id_compare's
       total order, so Termtab keys built on Term.compare stay sorted
       across retires.  The uptodate-ness of the id is calculated with
       respect to a symbol table, if it maps the key to a different epoch
       number, this is out-of-date. *)

  fun name_of_id ({name,...} : kernelid) = name
  fun epoch_of ({epoch,...} : kernelid) = epoch
  fun name_of ({name = {Name,...}, ...} : kernelid) = Name
  fun seg_of ({name = {Thy,...}, ...} : kernelid) = Thy
  fun id_toString id = name_toString (name_of_id id)
  fun id_compare(id1, id2) =
      case name_compare(name_of_id id1, name_of_id id2) of
          EQUAL => Int.compare(epoch_of id1, epoch_of id2)
        | x => x

  type 'a thytable = (kernelid * 'a) Symtab.table
  datatype 'a symboltable =
           KTab of {thymap : 'a thytable Symtab.table,
                    invmap : string list Symtab.table,
                    size : int,
                    epoch : int,
                    retire_epoch : int}
  (* thymap : theory*name -> kernelid (staged in two levels)
     invmap : name -> theory list
     size   : total entries of thymap
     epoch  : bumped every mutation; supplies fresh kernelids
     retire_epoch : bumped only on genuine retirement; the memoization
       gate for ThmSetData / AncestryData / GrammarDeltas. *)
  exception NoSuchThy of string
  exception NotPresent of kernelname
  datatype 'a symtab_error = Success of 'a
                           | Failure of exn
  fun isSuccess (Success _) = true | isSuccess _ = false
  fun symtab_epoch (KTab{retire_epoch,...}) = retire_epoch

  val empty_table = KTab {thymap = Symtab.empty, invmap = Symtab.empty,
                          size = 0, epoch = 0, retire_epoch = 0}
  fun peek(KTab {thymap, ...} : 'a symboltable, knm as {Thy,Name}) =
      case Symtab.lookup thymap Thy of
          NONE => Failure (NoSuchThy Thy)
        | SOME m => case Symtab.lookup m Name of
                        NONE => Failure (NotPresent knm)
                      | SOME r => Success r
  fun uptodate_id tab ({name,epoch,...} : kernelid) =
      case peek (tab, name) of
          Failure _ => false
        | Success (kid, _) => #epoch kid = epoch

  (* Name an id presents to pretty-printers and other display sites.
     For up-to-date ids this is just the bare Name; for retired ones it
     is the Globals.oldify form, which embeds the id's epoch so
     successive retirements of the same name don't collide. *)
  fun display_name_of_id tab id =
      let val {Name,...} = name_of_id id in
        if uptodate_id tab id then Name
        else Globals.oldify (epoch_of id) Name
      end

  fun find(tab,knm) =
      case peek(tab, knm) of
          Failure e => raise e
        | Success r => r
  (* Success bumps both counters; failure leaves the table untouched. *)
  fun remove(t as KTab{thymap,invmap,epoch,retire_epoch,size},
             knm as {Thy,Name}) =
      case Symtab.lookup thymap Thy of
          NONE => (t, Failure (NoSuchThy Thy))
        | SOME m =>
          case Symtab.lookup m Name of
              NONE => (t, Failure (NotPresent knm))
            | SOME kid =>
              let val m' = Symtab.delete Name m
              in
                (KTab{thymap = Symtab.update(Thy,m') thymap,
                      invmap = Symtab.remove_list equal (Name,Thy) invmap,
                      size = size-1, epoch = epoch+1,
                      retire_epoch = retire_epoch+1},
                 Success kid)
              end

  fun numItems (KTab{size,...} : 'a symboltable) = size

  fun app f (KTab{thymap,...} : 'a symboltable) =
      let
        fun perthyapp (thy,m) () =
            Symtab.fold (fn (nm,(id,v)) => fn () =>
                            f ({Thy=thy,Name=nm},(id,v)))
                        m
                        ()
      in
        Symtab.fold perthyapp thymap ()
      end

  fun foldl f acc (KTab{thymap,...} : 'a symboltable) =
      let
        fun perthyfold (thy,m) A =
            Symtab.fold (fn (nm,id) => fn A => f ({Thy=thy,Name=nm}, id, A)) m A
      in
        Symtab.fold perthyfold thymap acc
      end

  fun retire_name n tab = remove(tab, n)

  fun insert(n as {Thy,Name}, v) (tab0 : 'a symboltable) =
      let
        (* A colliding (Thy,Name) is retired transitively by `remove`;
           a fresh insert leaves retire_epoch alone. *)
        val tab1 as KTab{epoch,retire_epoch,size,invmap,thymap} =
            #1 (remove (tab0,n))
        val id = {name = n, epoch = epoch}
        val thymap' =
            Symtab.map_default (Thy,Symtab.make[(Name,(id,v))])
                               (Symtab.update(Name,(id,v)))
                               thymap
        val invmap' = Symtab.insert_list equal (Name,Thy) invmap
      in
        (KTab{epoch = epoch + 1, size = size + 1, invmap = invmap',
              thymap = thymap', retire_epoch = retire_epoch},
         id)
      end

  fun listItems r =
      List.rev (foldl (fn (knm,v,A) => (knm,v) :: A) [] r)
  fun listThy (tab as KTab{thymap,...}) thy =
      case Symtab.lookup thymap thy of
          NONE => []
        | SOME m =>
          Symtab.fold (fn (nm, (kid,v)) => fn A =>
                          if uptodate_id tab kid then
                            ({Thy = thy,Name = nm},(kid,v)) :: A
                          else A)
                      m
                      []

  fun listName tab nm =
      let
        val KTab{invmap,...} = tab
        val thys = case Symtab.lookup invmap nm of NONE => [] | SOME xs => xs
        val knms = map (fn thy => {Thy = thy, Name = nm}) thys
      in
        map (fn k => (k, find(tab, k))) knms
      end

  fun del_segment thyname (tab as KTab{thymap,epoch,retire_epoch,
                                       invmap,size}) =
      case Symtab.lookup thymap thyname of
          NONE => tab
        | SOME m =>
          let
            val thymap' = Symtab.delete thyname thymap
            fun foldthis (nm, _) invmap_acc =
                Symtab.remove_list equal (nm, thyname) invmap_acc
            val invmap' = Symtab.fold foldthis m invmap
          in
            KTab{epoch = epoch+1, retire_epoch = retire_epoch+1,
                 size = size - Symtab.size m,
                 thymap = thymap', invmap = invmap'}
          end

  fun thyExists (KTab{thymap,...}) thy = Symtab.defined thymap thy
  fun nameExists (KTab{invmap,...}) n = Symtab.defined invmap n


end
