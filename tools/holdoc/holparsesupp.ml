
type mode =
    ModeMosml
  | ModeHol
  | ModeText
  | ModeTex
  | ModeDir
  | ModeNone

let render_mode m =
  List.assoc m
    [
     (ModeMosml, "MoSML");
     (ModeHol  , "HOL");
     (ModeText , "text");
     (ModeTex  , "TeX");
     (ModeDir  , "directive");
     (ModeNone , "<none>");
   ]

type delim =
  | DelimHolTex      (* delimit HOL within TeX *)
  | DelimHolTexMath  (* etc *)
  | DelimHolMosml
  | DelimHolMosmlD
  | DelimText
  | DelimTex
  | DelimDir
  | DelimEOF

type delim_info = { imode : mode; sopen : string; sclose : string }

let delim_info d =
  List.assoc d
    [
     (DelimHolTex    ,{imode=ModeHol ;sopen="[["   ;sclose="]]"   });
     (DelimHolTexMath,{imode=ModeHol ;sopen="<["   ;sclose="]>"   });
     (DelimHolMosml  ,{imode=ModeHol ;sopen="`"    ;sclose="`"    });
     (DelimHolMosmlD ,{imode=ModeHol ;sopen="``"   ;sclose="``"   });
     (DelimText      ,{imode=ModeText;sopen="(*"   ;sclose="*)"   });
     (DelimTex       ,{imode=ModeTex ;sopen="(*:"  ;sclose=":*)"  });
     (DelimDir       ,{imode=ModeDir ;sopen="(*["  ;sclose="]*)"  });
     (DelimEOF       ,{imode=ModeNone;sopen="<bof>";sclose="<eof>"});
   ]

