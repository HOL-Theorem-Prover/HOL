(*---------------------------------------------------------------------------*
 * Things like Globals, Lexis, and Hol_pp haven't been opened.               *
 *---------------------------------------------------------------------------*)
structure HolKernel =
struct
 open Exception 
      Lib 
      Type 
      Term
      Dsyntax 
      Thm 
      Theory
      Const_def 
      Const_spec 
      Type_def;
end
