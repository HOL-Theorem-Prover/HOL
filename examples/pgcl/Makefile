###############################################################################
#  Makefile for the HOL pGCL theory.
#  Created by Joe Hurd, December 2002
###############################################################################

.PHONY: all build test clean world links tarball

all: build test

build:
	cd src && $(MAKE)

test:
	cd examples && $(MAKE)

clean:
	rm -f pgcl.tgz
	cd src      && $(MAKE) clean
	cd examples && $(MAKE) clean

world: clean all

# Everything below this point is for development use only.

links:

tarball: links clean
	cd .. && tar cvzhf pgcl/pgcl.tgz pgcl --exclude pgcl/pgcl.tgz --exclude CVS
