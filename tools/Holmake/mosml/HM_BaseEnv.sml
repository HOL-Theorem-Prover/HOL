structure HM_BaseEnv :> HM_BaseEnv =
struct

  open Systeml Holmake_tools

  fun make_base_env (optv : HM_Cline.t) =
    let
      open Holmake_types
      val MOSMLDIR = case #mosmldir optv of
                         NONE => Systeml.MOSMLDIR
                       | SOME s => s
      val MOSMLCOMP = fullPath [MOSMLDIR, "mosmlc"]
      val alist = [
        ("DEBUG_FLAG", if #debug (#core optv) then [LIT "--dbg"] else []),
        ("MOSML_INCLUDES",
         [VREF "if $(findstring NO_SIGOBJ,$(OPTIONS)),,-I \
                                   \$(protect $(SIGOBJ))", LIT " "] @
         [VREF ("patsubst %,-I %,$(INCLUDES) $(PREINCLUDES)")]),
        ("HOLMOSMLC", [VREF "MOSMLCOMP", LIT (" -q "), VREF "MOSML_INCLUDES"]),
        ("HOLMOSMLC-C",
         [VREF "MOSMLCOMP", LIT (" -q "), VREF "MOSML_INCLUDES", LIT " -c ",
          VREF ("if $(findstring NO_OVERLAY,$(OPTIONS)),,"^DEFAULT_OVERLAY)]),
        ("MOSMLC",  [VREF "MOSMLCOMP", LIT " ", VREF "MOSML_INCLUDES"]),
        ("MOSMLDIR", [LIT MOSMLDIR]),
        ("MOSMLCOMP", [VREF "protect $(MOSMLDIR)/mosmlc"]),
        ("MOSMLLEX", [VREF "protect $(MOSMLDIR)/mosmllex"]),
        ("MOSMLYAC", [VREF "protect $(MOSMLDIR)/mosmlyac"])
      ]
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
