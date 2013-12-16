signature PEGParse =
sig

  datatype ('tok,'nt,'value)pegsym =
           empty of 'value
         | any of 'tok -> 'value
         | tok of ('tok -> bool) * ('tok -> 'value)
         | nt of 'nt * ('value -> 'value)
         | seq of ('tok,'nt,'value)pegsym * ('tok,'nt,'value)pegsym *
                  ('value -> 'value -> 'value)
         | choice of ('tok,'nt,'value)pegsym * ('tok,'nt,'value)pegsym *
                     ('value -> 'value) * ('value -> 'value)
         | rpt of ('tok,'nt,'value)pegsym * ('value list -> 'value)
         | not of ('tok,'nt,'value)pegsym * 'value

  datatype ('tok,'nt,'value) grammar =
           PEG of { start : ('tok,'nt,'value)pegsym,
                    rules : 'nt -> ('tok,'nt,'value)pegsym option }

  datatype ('source,'tok,'nt,'value)kont =
           ksym of ('tok,'nt,'value)pegsym * ('source,'tok,'nt,'value)kont *
                   ('source,'tok,'nt,'value)kont
         | appf1 of ('value -> 'value) * ('source,'tok,'nt,'value)kont
         | appf2 of ('value -> 'value -> 'value) * ('source,'tok,'nt,'value)kont
         | returnTo of 'source * 'value option list *
                       ('source,'tok,'nt,'value)kont
         | poplist of ('value list -> 'value) * ('source,'tok,'nt,'value)kont
         | listsym of ('tok,'nt,'value)pegsym * ('value list -> 'value) *
                      ('source,'tok,'nt,'value)kont
         | kdone
         | kfailed


  val pegexec : ('nt -> ('tok,'nt,'value) pegsym) ->
                ('source -> ('source * 'tok) option) ->
                ('tok,'nt,'value)pegsym ->
                'source ->
                'value option list ->
                ('source,'tok,'nt,'value)kont ->
                ('source,'tok,'nt,'value)kont ->
                ('source * 'value) option

end

(* [pegexec ntmap gettok sym input stk success failure]

   The input/gettok pairing must be functional. In particular, PEGs
   support backtracking so sensible behaviour can only be guaranteed
   if repeated calls to the same input ('source) arguments always give
   the same result.

   The standard initial call to pegexec should be

     pegexec ntmap gettok symbol input [] kdone kfailed
*)
