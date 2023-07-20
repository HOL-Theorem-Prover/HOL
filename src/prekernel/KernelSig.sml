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


  type 'a thytable = (string, kernelid * 'a) Binarymap.dict
  type 'a symboltable = ((string, 'a thytable) Binarymap.dict * int) ref
  exception NoSuchThy of string
  exception NotPresent of kernelname
  datatype 'a symtab_error = Success of 'a
                           | Failure of exn
  fun isSuccess (Success _) = true | isSuccess _ = false

  fun new_table() = ref (Binarymap.mkDict String.compare, 0)
  fun peek(tab : 'a symboltable, knm as {Thy,Name}) =
      case Binarymap.peek(#1 (!tab),Thy) of
          NONE => Failure (NoSuchThy Thy)
        | SOME m => case Binarymap.peek(m, Name) of
                        NONE => Failure (NotPresent knm)
                      | SOME r => Success r
  fun find(tab,knm) =
      case peek(tab, knm) of
          Failure e => raise e
        | Success r => r
  fun remove(r as ref (thymap, count), knm as {Thy,Name}) =
      case Binarymap.peek (thymap, Thy) of
          NONE => Failure (NoSuchThy Thy)
        | SOME m => case Lib.total Binarymap.remove (m, Name) of
                        NONE => Failure (NotPresent knm)
                      | SOME (m', result) =>
                        let
                        in
                          r := (Binarymap.insert(thymap,Thy,m'), count - 1);
                          Success result
                        end

  fun numItems (r as ref (_, c)) = c

  fun app f (r as ref (thymap, c)) =
      let
        fun nmapp thy (name, i) = f ({Thy=thy,Name=name}, i)
      in
        Binarymap.app
          (fn (thy,submap) => Binarymap.app (nmapp thy) submap)
          thymap
      end

  fun foldl f acc (r as ref (thymap, c)) =
      let
        fun nmfold thy (name, i, A) = f ({Thy=thy,Name=name}, i, A)
      in
        Binarymap.foldl
          (fn (thy,submap,A) => Binarymap.foldl (nmfold thy) A submap)
          acc
          thymap
      end

  fun retire_name (r, n) =
      case remove(r, n) of
        Failure e => raise e
      | Success (kid, v) => retire_id kid

  fun insert(r as ref(thymap,c),n as {Thy,Name},v) = let
    val id = new_id n
    val _ = retire_name(r,n) handle NoSuchThy _ => ()
                                  | NotPresent _ => ()
    val submap0 =
        case Binarymap.peek (thymap,Thy) of
            NONE => Binarymap.mkDict String.compare
          | SOME submap0 => submap0
    val submap = Binarymap.insert(submap0,Name,(id,v))
  in
    r := (Binarymap.insert(thymap,Thy,submap), c + 1);
    id
  end

  fun uptodate_name (r, n) = let
    val (kid, _) = find(r, n)
  in
    uptodate_id kid
  end

  fun listItems r =
      List.rev (foldl (fn (knm,v,A) => (knm,v) :: A) [] r)
  fun listThy (tab as ref (thymap, _)) thy =
      case Binarymap.peek (thymap, thy) of
          NONE => []
        | SOME m =>
          Binarymap.foldl (fn (nm,(kid,v),acc) =>
                              if uptodate_id kid then
                                ({Thy = thy,Name = nm},(kid,v)) :: acc
                              else acc)
                          []
                          m

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
