structure HM_BaseEnv :> HM_BaseEnv =
struct

  open Systeml Holmake_tools
  val mosml_indicator = "%%MOSCOWML_INDICATOR%%"

  val POLYMLLIBDIR0 = Systeml.POLYMLLIBDIR;


  fun extend_env (cline : HM_Cline.t) e = let
    open Holmake_types
    val POLYMLLIBDIR =
        case #polymllibdir cline of NONE => POLYMLLIBDIR0 | SOME s => s
    val alist = [
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
       [LIT (spacify (map Systeml.protect POLY_LDFLAGS_STATIC))])]
  in
    List.foldl (fn (kv,acc) => env_extend kv acc) e alist
  end

  fun print_debug_info cline = let
    val POLYMLLIBDIR =
        case #polymllibdir cline of NONE => POLYMLLIBDIR0 | SOME s => s
  in
    print ("POLYMLLIBDIR = "^POLYMLLIBDIR^"\n")
  end



end
