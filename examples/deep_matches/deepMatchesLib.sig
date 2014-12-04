signature deepMatchesLib =
sig
  include Abbrev

  (********************************)
  (* turn shallow case-terms into *)
  (* deeply embedded ones         *)
  (********************************)

  val convert_case : term -> term
  val PMATCH_INTRO_CONV : conv


  (********************************)
  (* simplify PMATCH-terms        *)
  (********************************)

  (* There are various ways of simplifying
     PMATCH. One can e.g. remove redundant rows
     or partially evaluate it. The conversion
     PMATCH_SIMP_CONV does this. *)  
  val PMATCH_SIMP_CONV : conv

  (* There is also a more generic version that
     allows to provide extra ssfrags. This might
     be handy, if the PMATCH contains functions
     not known by the default methods. *)
  val PMATCH_SIMP_CONV_GEN : ssfrag list -> conv


  (* PMATCH_SIMP_CONV consists of various
     component conversions. These can be used 
     independently as well. *)
  val PMATCH_REMOVE_ARB_CONV : conv
  val PMATCH_REMOVE_ARB_CONV_GEN : ssfrag list -> conv

  val PMATCH_CLEANUP_PVARS_CONV : conv

  val PMATCH_CLEANUP_CONV : conv
  val PMATCH_CLEANUP_CONV_GEN : ssfrag list -> conv

  val PMATCH_SIMP_COLS_CONV : conv
  val PMATCH_SIMP_COLS_CONV_GEN : ssfrag list -> conv
 
  val PMATCH_EXPAND_COLS_CONV : conv


end
