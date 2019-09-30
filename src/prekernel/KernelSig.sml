structure KernelSig :> KernelSig =
struct

  type kernelname = {Thy : string, Name : string}
  fun name_compare ({Thy = thy1, Name = n1}, {Thy = thy2, Name = n2}) =
      case String.compare (n1, n2) of
        EQUAL => String.compare(thy1,thy2)
      | x => x

  fun name_toString {Thy,Name} = Thy ^ "$" ^ Name
  fun name_toMLString {Thy,Name} =
    "{Thy=\"" ^ String.toString Thy ^ "\",Name=\"" ^ String.toString Name ^ "\"}"

  type kernelid = (kernelname * bool) ref (* bool is uptodate flag *)

  fun name_of_id r = case !r of (n,utd) => n
  fun uptodate_id r = case !r of (n,utd) => utd
  fun new_id n = ref (n, true)
  fun retire_id r = case !r of ({Thy,Name}, _) =>
      r := ({Thy = Thy, Name = Globals.old Name}, false)
  fun name_of r = case !r of  ({Name,Thy},_) => Name
  fun seg_of r = case !r of ({Thy,Name},_) => Thy
  fun id_toString id = name_toString (name_of_id id)
  fun id_compare(i1, i2) =
    case (!i1, !i2) of ((n1,_), (n2,_)) =>
      if i1 = i2 then EQUAL else name_compare(n1,n2)


  type 'a symboltable = (kernelname, kernelid * 'a) Binarymap.dict ref
  exception NotFound

  fun new_table() = ref (Binarymap.mkDict name_compare)
  fun find(tab,n) = Binarymap.find(!tab,n)
      handle Binarymap.NotFound => raise NotFound
  fun peek(tab,n) = Binarymap.peek(!tab,n)
  fun remove(r, n) = let
    val (tab', (id,v)) = Binarymap.remove(!r,n)
  in
    r := tab';
    SOME (id,v)
  end handle Binarymap.NotFound => NONE

  fun numItems r = Binarymap.numItems (!r)

  fun app f r = Binarymap.app f (!r)

  fun foldl f acc r = Binarymap.foldl f acc (!r)

  fun retire_name (r, n) =
      case remove(r, n) of
        NONE => raise NotFound
      | SOME (kid, v) => retire_id kid

  fun insert(r,n,v) = let
    val id = new_id n
  in
    retire_name(r,n) handle NotFound => ();
    r := Binarymap.insert(!r,n,(id, v));
    id
  end


  fun uptodate_name (r, n) = let
    val (kid, _) = find(r, n)
  in
    uptodate_id kid
  end

  fun listItems r = Binarymap.listItems (!r)
  fun listThy tab thy = let
    fun foldthis ({Thy,Name},(kid,v),acc) =
        if Thy = thy andalso uptodate_id kid then
          ({Thy = Thy,Name = Name},(kid,v)) :: acc
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

  fun del_segment (r, thyname) = let
    fun appthis (knm as {Name,Thy},(id,v)) =
        if Thy = thyname then retire_name(r,knm)
        else ()
  in
    app appthis r
  end




end
