#==========================================#
# Make the manual for the "reduce" library #
#==========================================#

Help=../help
DOCTOTEXEXE=../../../../help/src/Doc2Tex.exe

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=makeindex

all:; make clean; make ids; make reduce; make index; make reduce ps pdf

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg entries.tex

ids:
	echo "\chapter{ML Functions in the reduce Library}" >entries.tex
	echo "\input{entries-intro}" >>entries.tex
	${DOCTOTEXEXE} ${Help}/entries entries.tex

index:
	${MAKEINDEX} reduce.idx

reduce:
	latex reduce.tex

ps:
	dvips reduce.dvi -o

pdf:
	pdflatex reduce.tex
