(****************************************************************************)
(* FILE          : types.sml                                                *)
(* DESCRIPTION   : Decision procedure for recursive types.                  *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                     *)
(* DATE          : 31st May 1996                                            *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton, University of Edinburgh                     *)
(* DATE          : 28th January 1998                                        *)
(****************************************************************************)

structure DecideTypes =
struct

local

val make_lazy = HOLTypeInfo.transform_type_info LazyThm.mk_proved_pre_thm;

val decision_type_info = ref [make_lazy HOLTypeInfo.list_type_info];

open Exception Term Dsyntax Psyntax DecisionSupport;

fun types_discrim (_:bool) tm =
   let val type_infos = !decision_type_info
       (* The following info ought to be cached in a dictionary. *)
       val constructor_infos = flat (map #constructors type_infos)
       and discriminator_infos = flat (map #discriminators type_infos)
       val constructors =
          map (fn i => (#name i,length (#arg_types i))) constructor_infos
       and selectors = flat (map (map #1 o #selectors) constructor_infos)
       and discriminators = map #name discriminator_infos
       fun is_constructor name arity = member (name,arity) constructors
       and is_selector name = member name selectors
       and is_discriminator name = member name discriminators
       val (f,args) = strip_comb tm
       val arity = length args
   in  if (is_var f) andalso (arity = 0)
       then (fn _ => tm,[])
       else let val name = #Name (Rsyntax.dest_const f)
            in  if (is_constructor name arity) orelse
                   (is_selector name) orelse
                   (is_discriminator name)
                then if (arity = 0)
                     then (fn _ => tm,[])
                     else (fn args' => list_mk_comb (f,args'),args)
                else Decide.failwith "types_discrim"
            end
            handle HOL_ERR _ => Decide.failwith "types_discrim"
   end;

in

fun known_types () = !decision_type_info;

fun add_type_lazy type_info =
   if (exists (fn i => #name i = #name type_info) (!decision_type_info))
   then ()
   else decision_type_info := type_info :: !decision_type_info;

fun add_type type_info = add_type_lazy (make_lazy type_info);

fun delete_type name =
   if (exists (fn i => #name i = name) (!decision_type_info))
   then decision_type_info :=
           filter (fn i => not (#name i = name)) (!decision_type_info)
   else ();

val types_proc =
   {Name = "types",
    Description = "Theory of equality on recursive types",
    Author = "Richard J. Boulton",
    Discriminator = types_discrim,
    Normalizer = DecisionConv.ALL_CONV,
    Procedure =
       Decide.make_incremental_procedure LazyRules.CONJ
          (fn tm => CongruenceClosureTypes.REC_TYPE_CONV (known_types ()) tm)};

end;

end; (* DecideTypes *)
