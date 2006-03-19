##
##  Makefile for Standard, Profile, Debug, Release, and Release-static versions of MiniSat
##
##    eg: "make rs" for a statically linked release version.
##        "make d"  for a debug version (no optimizations).
##        "make"    for the standard version (optimized, but with debug information and assertions active)

CSRCS     = $(wildcard *.C)
CHDRS     = $(wildcard *.h)
COBJS     = $(addsuffix .o, $(basename $(CSRCS)))

PCOBJS    = $(addsuffix p,  $(COBJS))
DCOBJS    = $(addsuffix d,  $(COBJS))
RCOBJS    = $(addsuffix r,  $(COBJS))

EXEC      = minisat

CXX       = g++
CFLAGS    = -Wall -ffloat-store
COPTIMIZE = -O3


.PHONY : s p d r build clean depend

s:	WAY=standard
p:	WAY=profile
d:	WAY=debug
r:	WAY=release
rs:	WAY=release static

s:	CFLAGS+=$(COPTIMIZE) -ggdb -D DEBUG
p:	CFLAGS+=$(COPTIMIZE) -pg -ggdb -D DEBUG
d:	CFLAGS+=-O0 -ggdb -D DEBUG
r:	CFLAGS+=$(COPTIMIZE) -D NDEBUG
rs:	CFLAGS+=$(COPTIMIZE) -D NDEBUG

s:	build $(EXEC)
p:	build $(EXEC)_profile
d:	build $(EXEC)_debug
r:	build $(EXEC)_release
rs:	build $(EXEC)_static

build:
	@echo Building $(EXEC) "("$(WAY)")"

clean:
	@rm -f $(EXEC) $(EXEC)_profile $(EXEC)_debug $(EXEC)_release $(EXEC)_static \
	  $(COBJS) $(PCOBJS) $(DCOBJS) $(RCOBJS) depend.mak

## Build rule
%.o %.op %.od %.or:	%.C
	@echo Compiling: $<
	@$(CXX) $(CFLAGS) -c -o $@ $<

## Linking rules (standard/profile/debug/release)
$(EXEC): $(COBJS)
	@echo Linking $(EXEC)
	@$(CXX) $(COBJS) -lz -ggdb -Wall -o $@ 

$(EXEC)_profile: $(PCOBJS)
	@echo Linking $@
	@$(CXX) $(PCOBJS) -lz -ggdb -Wall -pg -o $@

$(EXEC)_debug:	$(DCOBJS)
	@echo Linking $@
	@$(CXX) $(DCOBJS) -lz -ggdb -Wall -o $@

$(EXEC)_release: $(RCOBJS)
	@echo Linking $@
	@$(CXX) $(RCOBJS) -lz -Wall -o $@

$(EXEC)_static: $(RCOBJS)
	@echo Linking $@
	@$(CXX) --static $(RCOBJS) -lz -Wall -o $@


## Make dependencies
depend:	depend.mak
depend.mak: $(CSRCS) $(CHDRS)
	@echo Making dependencies ...
	@$(CXX) -MM $(CSRCS) > depend.mak
	@cp depend.mak /tmp/depend.mak.tmp
	@sed "s/o:/op:/" /tmp/depend.mak.tmp >> depend.mak
	@sed "s/o:/od:/" /tmp/depend.mak.tmp >> depend.mak
	@sed "s/o:/or:/" /tmp/depend.mak.tmp >> depend.mak
	@rm /tmp/depend.mak.tmp

include depend.mak
