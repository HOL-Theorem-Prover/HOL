#===========================================#
# Make the manual for the "pair" library	#
#===========================================#

# ---------------------------------------------------------------------
# Pathname to the string help files
# ---------------------------------------------------------------------
Help=../help

# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file 
# ---------------------------------------------------------------------
DOCTOTEX=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed

# ---------------------------------------------------------------------
# Pathname to the makeindex program
# ---------------------------------------------------------------------
MAKEINDEX=../../../Manual/LaTeX/makeindex ../../../

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make the documentation"

# ---------------------------------------------------------------------
# Remove all trace of previous LaTeX jobs
# ---------------------------------------------------------------------
clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg entries.tex theorems.tex; \
	echo "\begin{theindex}" >index.tex;                                 \
	echo "\mbox{}" >>index.tex;                                         \
	echo "\end{theindex}" >>index.tex

tex: ids theorems
	@echo "TeX files made"

ids:
	echo "\chapter{ML Functions in the pair Library}" >entries.tex;   	\
	echo "\input{entries-intro}" >>entries.tex;                         \
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{Theorems}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms theorems.tex

index:
	${MAKEINDEX} pair.idx index.tex

pair:
	latex pair.tex

all:
	make clean;	\
	make tex;	\
	make pair;	\
	make index;	\
	make pair
