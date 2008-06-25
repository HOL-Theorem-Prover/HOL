# =====================================================================
# Makefile for the hol manual
# =====================================================================

default: all

clean:
	(cd Description; make clean; cd ..)
	(cd Tutorial; make clean; cd ..)
	(cd Logic; make clean; cd ..)
	(cd Reference; make clean; cd ..)
	(cd Interaction; make clean; cd ..)
	(cd Quick; make clean; cd ..)

description:
	(cd Description; make; cd ..)
	@echo "====> DESCRIPTION made"

logic:
	(cd Logic; make; cd ..)
	@echo "====> LOGIC made"

tutorial:
	(cd Tutorial; make; cd ..)
	@echo "====> TUTORIAL made"

reference:
	(cd Reference; make; cd ..)
	@echo "====> REFERENCE made"

interaction:
	(cd Interaction; make; cd ..)
	@echo "====> Quick Reference made"

quick:
	(cd Quick; make; cd ..)
	@echo "====> Quick Reference made"

# libraries:
# 	(cd Libraries; make all; cd ..)
# 	@echo "====> LIBRARIES made"

all: description tutorial logic reference interaction quick
	@echo "=======> MANUAL made"

