structure KernelSig :> KernelSig =
struct

  type kernelname = {Thy : string, Name : string}
  fun name_compare ({Thy = thy1, Name = n1}, {Thy = thy2, Name = n2}) =
      case String.compare (n1, n2) of
        EQUAL => String.compare(thy1,thy2)
      | x => x

  fun name_toString {Thy,Name} = Thy ^ "$" ^ Name

  type kernelid = (kernelname * bool) ref (* bool is uptodate flag *)

  fun name_of_id (ref (n,utd)) = n
  fun uptodate_id (ref (n,utd)) = utd
  fun new_id n = ref (n, true)
  fun retire_id (r as ref ({Thy,Name}, _)) =
      r := ({Thy = Thy, Name = Globals.old Name}, false)
  fun name_of (ref ({Name,Thy},_)) = Name
  fun seg_of (ref ({Thy,Name},_)) = Thy
  fun id_toString id = name_toString (name_of_id id)
  fun id_compare(i1 as ref (n1,_), i2 as ref (n2,_)) =
      if i1 = i2 then EQUAL else name_compare(n1,n2)


  type 'a symboltable = (kernelname, kernelid * 'a) Binarymap.dict ref
  exception NotFound

  fun new_table() = ref (Binarymap.mkDict name_compare)
  fun find(ref tab,n) = Binarymap.find(tab,n)
      handle Binarymap.NotFound => raise NotFound
  fun peek(ref tab,n) = Binarymap.peek(tab,n)
  fun remove(r as ref tab,n) = let
    val (tab', (id,v)) = Binarymap.remove(tab,n)
  in
    r := tab';
    SOME (id,v)
  end handle Binarymap.NotFound => NONE

  fun numItems (ref tab) = Binarymap.numItems tab

  fun app f (ref tab) = Binarymap.app f tab

  fun foldl f acc (ref tab) = Binarymap.foldl f acc tab

  fun retire_name (r as ref tab, n) =
      case remove(r, n) of
        NONE => raise NotFound
      | SOME (kid, v) => retire_id kid

  fun insert(r as ref tab,n,v) = let
    val id = new_id n
  in
    retire_name(r,n) handle NotFound => ();
    r := Binarymap.insert(!r,n,(id, v));
    id
  end


  fun uptodate_name (r as ref tab, n) = let
    val (kid, _) = find(r, n)
  in
    uptodate_id kid
  end

  fun listItems (ref tab) = Binarymap.listItems tab
  fun listThy tab thy = let
    fun foldthis ({Thy,Name},(kid,v),acc) =
        if Thy = thy then ({Thy = Thy,Name = Name},(kid,v)) :: acc
        else acc
  in
    foldl foldthis [] tab
  end

  fun listName tab nm = let
    fun foldthis ({Thy,Name},(kid,v),acc) =
        if Name = nm  then ({Thy = Thy,Name = Name},(kid,v)) :: acc
        else acc
  in
    foldl foldthis [] tab
  end

  fun del_segment (r as ref tab, thyname) = let
    fun appthis (knm as {Name,Thy},(id,v)) =
        if Thy = thyname then retire_name(r,knm)
        else ()
  in
    app appthis r
  end




end

