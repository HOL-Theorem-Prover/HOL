Top-level format:

(theory
  (<ancestor-data>)
  (core-data
    (tables
       (string-table <list-of-strings>)
       (id-table ...)
       (type-table ...)
       (term-table ...))
    exports
    (..)
    (..)
    (<theorems>)
  )
  (incorporate ...)
  (thm-classes ...)
  (loadable-thydata ..)
)


<ancestor-data> ::= (<thy>+)  ; first thy is name of this theory;
                              ; subsequent ones are parents

<thy> ::= ($string$ $string$ $string$) ; first string is name; others are encoded timestamps

<theorems> ::= <thm> <thm> <thm> ...

<thm> ::=

  ($n$ ; number from string-table
    <dependency-info>
    (
     $string$  ; string encoding logical structure
    )
  )


<dependency-info> ::=
  (
   <thm-deps>
   <tag>*
  )

<thm-deps> ::=
  (<selfid> <other-dep>*)

<selfid> ::= ($n$ $n$)  ; first number is theory name,
                        ; second is this theorem's number

<other-dep> ::= ($n$ $n$+)  ; first number is theory name, subsequent numbers
                            ; are numbers identifying theorems within that
                            ; theory

<tag> ::= $string$  ; usually "DISK_THM"

# How constants appear within the string “encoding logical structure”:

(Example is from HOL/src/list/src/.holobjs/listTheory.dat)

In the string-table, element 5 is "list" and element 26 is "ALL_DISTINCT".
In the id-table, element 21 is (5 . 26)

In the term-table, there is a big list of the form
either

   ("some-string" number)

or

   (number number)

There will be at least one (21 ...) form because 21 corresponds to a constant.

In fact, there are three.

In every theorem statement, there is a big string of characters.  The only entries you're interested in are the %nnnnn components.  Each of these correspond to either a variable or a constant, and are indexes into the term-table.

## Sample Problem:

Imagine the aim is list all theorems that mention a particular constant (`list$ALL_DISTINCT`).

When scanning a .dat file, first look at the string-table, to see if it lists entries for `list` and `ALL_DISTINCT`.  Then you will have a number for `list` (5, say) and a number for `ALL_DISTINCT` (26, say).

Then scan id-table for (5 . 26).  If that appears in the id-table, you know that the constant appears somewhere.  Then you have a number/index for (5 . 26) with that table, say it is 21. Let this number be `i` below.

Then scan term-table for `(i <sometypenumber>)`.  There may be multiple such pairs.

  ... (21 10) (21 12) (21 34) (21 345) ...

Record all the indexes in term-table  (1001, 1002, 1003, 1004)  (wrong numbers, just for example)

Then, scan all of the blob-strings in the theorem statements, for %1001, or %1002, or %1003, or %1004.

list$CONS : num -> num list -> num list   (i 10) ; 10 encodes "num -> num list -> num list"
list$CONS : α -> α list -> α list (i 20) ; 20 encodes "α -> α list -> α list"

Then when you find the %code print the name of the theorem and the theory.

(Make sure not to report a match for %10, if you are looking at %101.)
