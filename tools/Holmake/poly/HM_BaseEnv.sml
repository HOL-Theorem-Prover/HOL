structure HM_BaseEnv :> HM_BaseEnv =
struct

  open Systeml Holmake_tools
  val mosml_indicator = "%%MOSCOWML_INDICATOR%%"

  val POLYMLLIBDIR0 = Systeml.POLYMLLIBDIR;


  fun make_base_env (cline : HM_Cline.t) = let
    open Holmake_types
    val POLYMLLIBDIR =
        case #polymllibdir cline of NONE => POLYMLLIBDIR0 | SOME s => s
    val alist = [
      ("DEBUG_FLAG", if #debug (#core cline) then [LIT "--dbg"] else []),
      ("ISIGOBJ", [VREF "if $(findstring NO_SIGOBJ,$(OPTIONS)),,$(SIGOBJ)"]),
      ("MOSML_INCLUDES", [VREF ("patsubst %,-I %,$(ISIGOBJ) \
                                \ $(INCLUDES) $(PREINCLUDES)")]),
      ("HOLMOSMLC", [VREF "MOSMLCOMP"]),
      ("HOLMOSMLC-C", [VREF "MOSMLCOMP", LIT " -c "]),
      ("MOSMLC",  [VREF "MOSMLCOMP"]),
      ("MOSMLCOMP", [LIT mosml_indicator]),
      ("POLY", [LIT (Systeml.protect Systeml.POLY)]),
      ("POLYMLLIBDIR", [LIT POLYMLLIBDIR]),
      ("POLY_LDFLAGS", [LIT (spacify (map Systeml.protect POLY_LDFLAGS))]),
      ("POLY_LDFLAGS_STATIC",
       [LIT (spacify (map Systeml.protect POLY_LDFLAGS_STATIC))]),
      ("RELOCBUILD", if #relocbuild cline then [LIT "1"] else [])
    ]
  in
    List.foldl (fn (kv,acc) => env_extend kv acc) (base_environment()) alist
  end

  fun debug_info (cline : HM_Cline.t) = let
    val POLYMLLIBDIR =
        case #polymllibdir cline of NONE => POLYMLLIBDIR0 | SOME s => s
  in
    "POLYMLLIBDIR = "^POLYMLLIBDIR
  end



end
