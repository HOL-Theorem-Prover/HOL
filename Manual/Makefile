# =====================================================================
# Makefile for the HOL manual
# =====================================================================

default: all

clean:
	(cd Description; Holmake cleanAll; cd ..)
	(cd Tutorial; Holmake cleanAll; cd ..)
	(cd Logic; make clean; cd ..)
	(cd Reference; make clean; cd ..)
	(cd Interaction; make clean; cd ..)
	(cd Quick; make clean; cd ..)

Description/description.pdf:
	(cd Description; Holmake; cd ..)
	@echo "====> DESCRIPTION made"

Logic/logic.pdf:
	(cd Logic; make; cd ..)
	@echo "====> LOGIC made"

Tutorial/tutorial.pdf:
	(cd Tutorial; Holmake; cd ..)
	@echo "====> TUTORIAL made"

Reference/reference.pdf:
	(cd Reference; make; cd ..)
	@echo "====> REFERENCE made"

Interaction/HOL-interaction.pdf:
	(cd Interaction; Holmake; cd ..)
	@echo "====> Quick Reference made"

Quick/quick.pdf:
	(cd Quick; make; cd ..)
	@echo "====> Quick Reference made"

# libraries:
# 	(cd Libraries; make all; cd ..)
# 	@echo "====> LIBRARIES made"

description: Description/description.pdf
logic: Logic/logic.pdf
tutorial: Tutorial/tutorial.pdf
reference: Reference/reference.pdf
interaction: Interaction/HOL-interaction.pdf
quick: Quick/quick.pdf

all: description tutorial logic reference interaction quick
	@echo "=======> MANUAL made"
