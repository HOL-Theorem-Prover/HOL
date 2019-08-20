structure FlagDB :> FlagDB =
struct

open Portable
type t = (UniversalType.t * string) Symtab.table

type 'a tag =
     ('a -> UniversalType.t) * (UniversalType.t -> 'a option) * string
fun tagProject (_, Out,_) t = Out t
fun tagInject (In,_, _) v = In v
fun tagDesc (_, _, d) = d

val empty = Symtab.empty

fun update nm (tag, v:'a) t =
    let
      val u = tagInject tag v
    in
      Symtab.map_entry nm (apfst (K u)) t
    end

  fun update_new {desc,name} (tag, v) t =
      let
        val u = tagInject tag v
      in
        Symtab.update (name, (u, desc ^ " (" ^ tagDesc tag ^ ")")) t
      end

  fun peek t tag nm =
      case Symtab.lookup t nm of
          NONE => NONE
        | SOME (u,d) => Option.map (fn v => (v, d)) (tagProject tag u)

  fun mkTag s = let val (In,Out) = UniversalType.embed ()
                in
                  (In,Out,s)
                end

  fun keys t =
      Symtab.fold_rev (fn (k,(_,d)) => fn A => {key = k,desc = d} :: A) t []

  val string : string tag = mkTag "string"
  val int : int tag = mkTag "int"
  val bool : bool tag = mkTag "bool"
  val stringopt : string option tag = mkTag "string-option"

end
