structure Logging :> Logging =
struct

open OpenTheoryCommon
structure Map = OpenTheoryMap.Map

val ERR = Feedback.mk_HOL_ERR "Logging"

datatype log_state =
  Not_logging
| Active_logging of TextIO.outstream

val log_state = ref Not_logging

fun log_raw s =
  case !log_state of
    Active_logging h => TextIO.output (h,s^"\n")
  | Not_logging => ()

fun log_num n = log_raw (Int.toString n)

fun log_name s = log_raw ("\""^String.toString s^"\"")

fun log_command s = log_raw s

fun log_nil () = log_command "nil"

fun log_list log = let
  fun logl []     = log_nil ()
    | logl (h::t) = (log h; logl t; log_command "cons")
in logl end

val (log_term, log_thm, log_clear) = let
  val (reset_key,next_key) = let
    val key = ref 0
    fun reset() = key := 0
    fun next()  = let val k = !key in (key := k+1; k) end
    in (reset,next) end

  val (reset_dict,peek_dict,save_dict) = let
    fun new_dict() = Map.mkDict object_compare
    val dict = ref (new_dict())
    fun reset() = dict := new_dict()
    fun peek x = Map.peek(!dict,x)
    fun save x = case peek x of
      SOME k => k
    | NONE => let
        val k = next_key()
        val _ = Map.insert(!dict,x,k)
        val _ = log_num k
        val _ = log_command "def"
      in k end
    in (reset,peek,save) end
  fun saved ob = case peek_dict ob of
    SOME k => let
      val _ = log_num k
      val _ = log_command "ref"
      in true end
  | NONE => false

  fun log_type_var ty = log_name (dest_vartype ty)

  local open OpenTheoryMap in
    fun log_tyop_name tyop =
      Map.find(tyop_to_ot_map(),tyop)
    handle Map.NotFound
    => raise ERR "log_tyop_name" ("No OpenTheory name for "^(#Thy tyop)^"$"^(#Tyop tyop))
    fun log_const_name const =
      Map.find(const_to_ot_map(),const)
    handle Map.NotFound
    => raise ERR "log_const_name" ("No OpenTheory name for "^(#Thy const)^"$"^(#Name const))
  end

  fun log_tyop tyop = let
    val ob = OTypeOp tyop
  in if saved ob then () else let
    val _ = log_tyop_name tyop
    val _ = log_command "typeOp"
    val _ = save_dict ob
    in () end
  end

  fun log_const const = let
    val ob = OConst const
  in if saved ob then () else let
    val _ = log_const_name const
    val _ = log_command "const"
    val _ = save_dict ob
    in () end
  end

  fun log_type ty = let
    val ob = OType ty
  in if saved ob then () else let
    val _ = let
      val {Thy,Args,Tyop} = dest_thy_type ty
      val _ = log_tyop {Thy=Thy,Tyop=Tyop}
      val _ = log_list log_type Args
      val _ = log_command "opType"
    in () end handle HOL_ERR _ => let
      val _ = log_type_var ty
      val _ = log_command "varType"
    in () end
    val _ = save_dict ob
    in () end
  end

  fun log_var v = let
    val ob = OVar v
  in if saved ob then () else let
    val (n,ty) = dest_var v
    val _ = log_name n
    val _ = log_type ty
    val _ = log_command "var"
    val _ = save_dict ob
    in () end
  end

  fun log_term tm = let
    val ob = OTerm tm
  in if saved ob then () else let
    val _ = let
      val {Thy,Name,Ty} = dest_thy_const tm
      val _ = log_const {Thy=Thy,Name=Name}
      val _ = log_type Ty
      val _ = log_command "constTerm"
    in () end handle HOL_ERR _ => let
      val (t1,t2) = dest_comb tm
      val _ = log_term t1
      val _ = log_term t2
      val _ = log_command "appTerm"
    in () end handle HOL_ERR _ => let
      val (v,b) = dest_abs tm
      val _ = log_var v
      val _ = log_term b
      val _ = log_command "absTerm"
    in () end handle HOL_ERR _ => let
      val _ = log_var tm
      val _ = log_command "varTerm"
    in () end
    val _ = save_dict ob
    in () end
  end

  fun log_thm th = raise (Fail "unimplemented")

in (log_term, log_thm, reset_dict) end

fun export_thm th = let
  val _ = case !log_state of
      Not_logging => ()
    | Active_logging _ => let
      val _ = log_thm th
      val _ = log_list log_term (Thm.hyp th)
      val _ = log_term (Thm.concl th)
           in log_command "thm" end
(*  val _ = Thm.delete_proof th *)
in () end

local val op ^ = OS.Path.concat in
  val opentheory_dir = Globals.HOLDIR^"src"^"opentheory"
end

val mk_path = let
  exception exists
  fun mk_path name = let
    val path = OS.Path.concat(opentheory_dir,OS.Path.joinBaseExt{base=name,ext=SOME"4rt"})
  in if OS.FileSys.access(path,[]) then raise exists else path end
in fn name => let
     fun try n = mk_path (name^(Int.toString n)) handle exists => try (n+1)
   in mk_path name handle exists => try 0 end
end

fun start_logging() =
  case !log_state of
    Not_logging => let
      val name = Theory.current_theory()
      val path = mk_path name
      val file = TextIO.openOut path
    in log_state := Active_logging file end
  | Active_logging _ => ()

fun stop_logging() =
  case !log_state of
    Active_logging h => let
      val _ = log_clear ()
      val _ = TextIO.closeOut h
    in log_state := Not_logging end
  | Not_logging => ()

end
