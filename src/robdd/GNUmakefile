# When the Hol98 system is installed (via <holdir>/bin/configure), the file
# GNUmakefile in this directory is generated automatically from
# the file GNUmakefile.src (also in this directory).

# This file assumes that it is being `made' on Linux. If it is being built
# on Solaris, then you must change (1) the definition "CFLAGS" and 
# (2) the building of the library. These are labelled with "LINUX" and
# "SOLARIS" in the following.

MOSMLHOME:=/local/scratch/kxs/143
HOLDIR:=/local/scratch/kxs/working
MOSMLBIN:=$(MOSMLHOME)/bin
MOSMLRUNTIME:=$(MOSMLHOME)/src/runtime
MOSMLTOOLS:=$(MOSMLBIN)/camlrunm $(MOSMLHOME)/tools
MOSMLC:=$(MOSMLBIN)/mosmlc -c -I ${HOLDIR}/sigobj
MOSMLL:=$(MOSMLBIN)/mosmlc 
MOSMLLEX:=$(MOSMLBIN)/mosmllex
MOSMLYACC:=$(MOSMLBIN)/mosmlyac

OPTS:=-fPIC
CINCLUDE:= -I$(MOSMLRUNTIME) -I./buddy16/src

# LINUX
CFLAGS= -Dunix -O3 -rdynamic $(OPTS) $(CINCLUDE)
# SOLARIS
# CFLAGS= -Dunix -O3 $(OPTS) $(CINCLUDE)

LIBS:=-L./buddy16/src -lbdd

CFILES:=$(wildcard *.c)
COBJS:=$(CFILES:.c=.o)
DLLIB:=mlrobdd.so


SMLLS:=$(wildcard *.sml)
SIGLS:=$(wildcard *.sig)

SMLSRC:=$(SMLLS)
SIGSRC:=$(SIGLS)

SMLOBJ:=$(SMLSRC:.sml=.uo)
SIGOBJ:=$(SIGSRC:.sig=.ui)

.PRECIOUS: %.ui %.uo %.o %.sig %.sml
.PHONY: all depend clean

all: $(SMLOBJ) $(SIGOBJ) $(DLLIB)

#LINUX
$(DLLIB): $(COBJS)
	gcc -shared -Wl,-soname,$@ -o $@  $^ $(LIBS)

#SOLARIS
#$(DLLIB): $(COBJS)
#	ld -G -B dynamic -o $@  $^ $(LIBS)


%.ui: %.sig
	$(MOSMLC) $<

%.uo: %.sml
	$(MOSMLC) $<

%.o: %.c
	gcc -c $(CFLAGS) -o $@ $<

clean:
	rm -f *.u? 
	rm -f *.o *.so
	rm -f  GNUmakefile.bak

depend : 
	mv GNUmakefile GNUmakefile.bak
	(sed -n -e '1,/^### DO NOT DELETE THIS LINE/p' GNUmakefile.bak;	 \
         gcc -MM $(CINCLUDE) $(OPTS) *.c) > GNUmakefile
	$(MOSMLTOOLS)/mosmldep >> GNUmakefile


### EVERYTHING THAT GOES BEYOND THIS COMMENT WILL BE ERASED WITHOUT WARNING
### DO NOT DELETE THIS LINE
