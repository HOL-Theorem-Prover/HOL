.PHONY: all RBD FT case_studies clean

# Change HOLMAKE path according to your hol installation
# Don't forget to change the path for HOLMAKE variable (if defined) in the subdirectories.
# You'll find Holmakefile in each RBD/ FT/ case_studies/ subdirectories.

HOLDIR = /Users/waqarahmed/HOL

HOLMAKE = $(HOLDIR)/bin/Holmake

all:    case_studies
	$(HOLMAKE)
RBD:
	cd RBD/ && $(HOLMAKE)

FT:
	cd FT/ && $(HOLMAKE)

case_studies:
	cd case_studies/ && $(HOLMAKE)
clean:
	$(HOLMAKE) cleanAll
	cd RBD/ && $(HOLMAKE) cleanAll && cd ..
	cd FT/ && $(HOLMAKE) cleanAll && cd ..
	cd case_studies/ && $(HOLMAKE) cleanAll && cd ..
