# =====================================================================
# Makefile for the hol manual
# =====================================================================

default:
	@echo "INSTRUCTIONS:"
	@echo ""
	@echo "1) type \"make reference\" to make only REFERENCE, or"
	@echo ""
	@echo "2) type \"make description\" to make only DESCRIPTION, or"
	@echo ""
	@echo "3) type \"make tutorial\" to make only TUTORIAL, or"
	@echo ""
# 	@echo "4) type \"make libraries\" to make only LIBRARIES, or"
# 	@echo ""
	@echo "4) type \"make covers\" to make fancy cover pages, or"
	@echo ""
	@echo "5) type \"make quick\" to make only the Quick Reference, or"
	@echo ""
	@echo "6) type \"make interaction\" to make only the Guide to HOL Interaction, or"
	@echo ""
	@echo "7) type \"make all\" to create the entire manual."

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
	make tutorial; make description; make interaction; make reference; make covers; make quick
	@echo "=======> MANUAL made"

