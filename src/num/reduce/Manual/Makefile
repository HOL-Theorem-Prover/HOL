#==========================================#
# Make the manual for the "reduce" library #
#==========================================#

Help=../help
DOCTOTEX=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=../../../Manual/LaTeX/makeindex ../../../

all:; make clean; make ids; make reduce; make index; make reduce

clean:;                                                                 \
    rm -f *.dvi *.aux *.toc *.log *.idx *.ilg entries.tex;              \
    echo "\begin{theindex}" >index.tex;                                 \
    echo "\mbox{}" >>index.tex;                                         \
    echo "\end{theindex}" >>index.tex

ids:;                                                                   \
    echo "\chapter{ML Functions in the reduce Library}" >entries.tex;   \
    echo "\input{entries-intro}" >>entries.tex;                         \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

index:;                                                                 \
    ${MAKEINDEX} reduce.idx index.tex

reduce:;                                                                \
    latex reduce.tex
