mosmlc -c TOMLerror.sml
mosmlc -c TOMLvalue_dtype.sml
mosmlc -c TOMLvalue.sig
mosmlc -c TOMLvalue.sml
mosmlc -c parseTOMLUtil.sml
mosmlc -c -toplevel parseTOMLFunctor.sml
mosmlc -c parseTOMLFunctor.ui parseTOML.sml
mosmlc -c TOML.sig
mosmlc -c TOML.sml
