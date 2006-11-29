###############################################################################
#  Makefile for the HOL pGCL theory.
#  Created by Joe Hurd, December 2002
###############################################################################

.PHONY: all
all: build test

.PHONY: build
build:
	cd src && $(MAKE)

.PHONY: test
test:
	cd examples && $(MAKE)

.PHONY: clean
clean:
	rm -f pgcl.tgz
	cd src && $(MAKE) clean
	cd examples && $(MAKE) clean

.PHONY: world
world: clean all

# Everything below this point is for development use only.

.PHONY: tarball
tarball: clean
	cd .. && tar cvzhf pgcl/pgcl.tgz pgcl --exclude pgcl/pgcl.tgz --exclude CVS
