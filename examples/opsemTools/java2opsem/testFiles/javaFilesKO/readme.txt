This directory contains examples of java files that can't yet
be translated automatically using java2opsem package.

The main reason is that the conversion "Num" from int
to numeral is not yet introduced correctly. 
For the moment, Num is introduced during parsing of an array index
and also for lengths of arrays used inside a  \forall statement.
But a statement such as !i. i<9 ==> i>f(x) would not be correctly 
translated, since f(x) would not be converted as num.

The right way to introduce Num would be to introduce it inside 
array indexes and also for each variable that appears in an expression
that contains a quantified variables. This will require to
build another visitor for \forall statement that tag variables 
that appear in expressions involving the quantified variable. 


For each program in this directory, the corresponding .sml
file has been modified by hand in order to be built with Holmake
and then used as opsem program example. 

Problems in the translation process are the following:

Partition.java, PartitionKO1.java and 
   
    (\state1 state2.
      ((0<=ScalarOf (state2 ' "Result"))/\(ScalarOf (state2 ' "Result")<ScalarOf (state1 ' "aLength")))
     /\(!i . ((0<=i)/\(i<ScalarOf (state2 ' "Result")))==>
    (((ArrayOf (state2 ' "a") ' (i))<(ArrayOf (state2 ' "a") ' (Num(ScalarOf (state2 ' "Result")))))))
    /\(!i . ((ScalarOf (state2 ' "Result")<i)/\(i<Num(ScalarOf (state1 ' "aLength"))))==>
      (((ArrayOf (state2 ' "a") ' (i))>=(ArrayOf (state2 ' "a") ' (Num(ScalarOf (state2 ' "Result"))))))))

 (ScalarOf (state2 ' "Result")<i) must be changed as
  Num(ScalarOf (state2 ' "Result"))<i


BubleSortMantovani.java

    (\state.
      (!i . ((0<=i)/\(i<Num(ScalarOf (state ' "aLength"))))==>(((ArrayOf (state ' "a") ' (i))=Num(ScalarOf (state ' "aLength")))-1)-i)))

must be replaced with

    (\state.
      (!i . ((0<=i)/\(i<Num(ScalarOf (state ' "aLength"))))==>(((ArrayOf (state ' "a") ' (i))=(ScalarOf (state ' "aLength"))-1)-i)))


AbsMinusAssert.java

  Translate JML //@ assert into opsem Assert
