# =====================================================================
# Makefile for the hol manual
# =====================================================================

default: all

tutorial:
	(cd Tutorial; make all; cd ..)
	@echo "====> TUTORIAL made"

description:
	(cd Description; make all; cd ..)
	@echo "====> DESCRIPTION made"

interaction:
	(cd Interaction; make; cd ..)
	@echo "====> Quick Reference made"

reference:
	(cd Reference; make all; cd ..)
	@echo "====> REFERENCE made"

logic:
	(cd Logic; make all; cd ..)
	@echo "====> LOGIC made"

# libraries:
# 	(cd Libraries; make all; cd ..)
# 	@echo "====> LIBRARIES made"

covers:
	(cd Covers; make all; cd ..)
	@echo "====> Fancy covers made"

quick:
	(cd Quick; make all; cd ..)
	@echo "====> Quick Reference made"

all:
	make tutorial; make description; make interaction; make reference; make covers; make quick ; make logic
	@echo "=======> MANUAL made"

