signature ISPEGParse =
sig

  datatype locrel = datatype ISPEG_dtype.locrel
  datatype ispegsym = datatype ISPEG_dtype.ispegsym
  datatype locpred = datatype ISPEG_dtype.locpred
  datatype kont = datatype ISPEG_dtype.kont
  datatype ispegresult = datatype ISPEG_dtype.ispegresult
  datatype hlocn = datatype ISPEG_dtype.hlocn
  datatype hlocs = datatype ISPEG_dtype.hlocs
  type ('tok,'nt,'val,'e) ispeg = ('tok,'nt,'val,'e) ISPEG_dtype.ispeg



  val ispeg_exec :
      ('tok,'nt,'val,'e) ispeg ->
      ('tok,'nt,'val,'e) ispegsym ->
      ('tok * hlocs) list ->
      locpred ->
      'val option list ->
      (hlocs * 'e) option ->
      (hlocs * 'e) list ->
      ('tok,'nt,'val,'e) kont ->
      ('tok,'nt,'val,'e) kont ->
      (('tok * hlocs) list,'val,'e) ispegresult

end

(* [pegexec ntmap gettok sym input stk success failure]

   The input/gettok pairing must be functional. In particular, PEGs
   support backtracking so sensible behaviour can only be guaranteed
   if repeated calls to the same input ('source) arguments always give
   the same result.

   The standard initial call to pegexec should be

     pegexec ntmap gettok symbol input [] kdone kfailed
*)
