# A script to clean .doc files up so that they are presentable in raw
# ASCII
#
# Get rid of lines with just opening or closing braces on them, these
# delimit verbatim texts.  Better to just use blank lines in ASCII text
s/^{ *$//
s/^} *$//
# Leading \noindents should just go entirely.
s/^\\noindent *//
# KEYWORDS and LIBRARY entries aren't sufficiently interesting to
# warrant keeping
/^\\KEYWORDS/,/^ *$/d
/^\\LIBRARY/,/^ *$/d
# Turn \DESCRIBE into DESCRIPTION followed by a blank line
s/^\\DESCRIBE/----------------------------------------------------------------------\
DESCRIPTION\
/
# Likewise with EXAMPLE
s/^\\EXAMPLE/----------------------------------------------------------------------\
EXAMPLE\
/
# Put the thing being documented in a "fancy" box at the top of the page
/^\\DOC/{
s/^\\DOC *//
s/ *$//
s/^/   /
i\
======================================================================
a\
======================================================================
# h ; s/[A-Za-z0-9_]/-/g
# s/^/--/
# s/$/--/
# p ; x ; s/^/  /; p ; x
}
# Do nice things with the \TYPE line
/\\TYPE/ {
# get rid of leading and trailing braces
s/\\TYPE *{//
t fake
: fake
s/} *$//
t fake1
: fake1
h
s/[^:]*: */TYPE: /
t fake2
: fake2
p
x
s/^ *\([A-Za-z_][A-Za-z_]*\)\..*/\1/
t wasmod
d
: wasmod
s/^/STRUCTURE: /
}
# Get rid of any remaining backslashes starting lines
s/^\\//
# Turn double braces into single braces
s/{{/{/
s/}}/}/
# Delete the ENDDOC
/ENDDOC/d
# delete BLTYPE and ELTYPE
/ELTYPE/d
/BLTYPE/d

