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

r:	WAY=release
s:	WAY=standard
p:	WAY=profile
d:	WAY=debug
rs:	WAY=release static

r:	CFLAGS+=$(COPTIMIZE) -D NDEBUG
s:	CFLAGS+=$(COPTIMIZE) -ggdb -D DEBUG
p:	CFLAGS+=$(COPTIMIZE) -pg -ggdb -D DEBUG
d:	CFLAGS+=-O0 -ggdb -D DEBUG
rs:	CFLAGS+=$(COPTIMIZE) -D NDEBUG

r:	build $(EXEC)
s:	build $(EXEC)_standard
p:	build $(EXEC)_profile
d:	build $(EXEC)_debug
rs:	build $(EXEC)_static

build:
	@echo Building $(EXEC) "("$(WAY)")"

clean:
	@rm -f $(EXEC)_standard $(EXEC)_profile $(EXEC)_debug $(EXEC) $(EXEC)_static \
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
