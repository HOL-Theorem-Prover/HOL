structure HM_BaseEnv :> HM_BaseEnv =
struct

  open Systeml Holmake_tools

  fun make_base_env (optv : HM_Cline.t) =
    let
      open Holmake_types
      val nob2002 = Systeml.HAVE_BASIS2002 orelse #no_basis2002 optv
      val MOSMLDIR = case #mosmldir optv of
                         NONE => Systeml.MOSMLDIR
                       | SOME s => s
      val MOSMLCOMP = fullPath [MOSMLDIR, "mosmlc"]
      val basis_string = if nob2002 then [] else [LIT " basis2002.ui"]
      val alist = [
        ("DEBUG_FLAG", if #debug (#core optv) then [LIT "--dbg"] else []),
        ("MOSML_INCLUDES",
         [VREF "if $(findstring NO_SIGOBJ,$(OPTIONS)),,-I \
                                   \$(protect $(SIGOBJ))", LIT " "] @
         [VREF ("patsubst %,-I %,$(INCLUDES) $(PREINCLUDES)")]),
        ("HOLMOSMLC", [VREF "MOSMLCOMP", LIT (" -q "), VREF "MOSML_INCLUDES"] @
                      basis_string),
        ("HOLMOSMLC-C",
         [VREF "MOSMLCOMP", LIT (" -q "), VREF "MOSML_INCLUDES", LIT " -c "] @
         basis_string @ [LIT " "] @
         [VREF ("if $(findstring NO_OVERLAY,$(OPTIONS)),,"^DEFAULT_OVERLAY)]),
        ("MOSMLC",  [VREF "MOSMLCOMP", LIT " ", VREF "MOSML_INCLUDES"]),
        ("MOSMLDIR", [LIT MOSMLDIR]),
        ("MOSMLCOMP", [VREF "protect $(MOSMLDIR)/mosmlc"]),
        ("MOSMLLEX", [VREF "protect $(MOSMLDIR)/mosmllex"]),
        ("MOSMLYAC",
         [VREF "protect $(MOSMLDIR)/mosmlyac"])] @
         (if Systeml.HAVE_BASIS2002 then [("HAVE_BASIS2002", [LIT "1"])]
          else [])
    in
      List.foldl (fn (kv,acc) => env_extend kv acc) (base_environment()) alist
    end

  fun debug_info (optv : HM_Cline.t) =
    let
      val MOSMLDIR = case #mosmldir optv of
                         NONE => Systeml.MOSMLDIR
                       | SOME s => s
    in
      "MOSMLDIR = "^MOSMLDIR
    end

end (* struct *)
