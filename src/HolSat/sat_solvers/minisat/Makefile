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

CXX       = $(or $(MINISAT_CXX),c++)
CFLAGS    = -Wall -ffloat-store -fno-strict-aliasing
COPTIMIZE = -O3


.PHONY : s p d r build clean

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
	  $(COBJS) $(PCOBJS) $(DCOBJS) $(RCOBJS)

## Build rule
%.o %.op %.od %.or:	%.C
	@echo Compiling: $<
	@$(CXX) $(CFLAGS) -c -o $@ $<

## Linking rules (standard/profile/debug/release)
$(EXEC): $(COBJS)
	@echo Linking $(EXEC)
	@$(CXX) $(COBJS)  -ggdb -Wall -o $@ 

$(EXEC)_profile: $(PCOBJS)
	@echo Linking $@
	@$(CXX) $(PCOBJS) -ggdb -Wall -pg -o $@

$(EXEC)_debug:	$(DCOBJS)
	@echo Linking $@
	@$(CXX) $(DCOBJS) -ggdb -Wall -o $@

$(EXEC)_release: $(RCOBJS)
	@echo Linking $@
	@$(CXX) $(RCOBJS)  -Wall -o $@

$(EXEC)_static: $(RCOBJS)
	@echo Linking $@
	@$(CXX) --static $(RCOBJS)  -Wall -o $@



File.o: File.C File.h Global.h

Main.o: Main.C Solver.h SolverTypes.h Global.h VarOrder.h Heap.h Proof.h \
  File.h Sort.h

Proof.o: Proof.C Proof.h SolverTypes.h Global.h File.h Sort.h

Solver.o: Solver.C Solver.h SolverTypes.h Global.h VarOrder.h Heap.h \
  Proof.h File.h Sort.h

File.op: File.C File.h Global.h

Main.op: Main.C Solver.h SolverTypes.h Global.h VarOrder.h Heap.h Proof.h \
  File.h Sort.h

Proof.op: Proof.C Proof.h SolverTypes.h Global.h File.h Sort.h

Solver.op: Solver.C Solver.h SolverTypes.h Global.h VarOrder.h Heap.h \
  Proof.h File.h Sort.h

File.od: File.C File.h Global.h

Main.od: Main.C Solver.h SolverTypes.h Global.h VarOrder.h Heap.h Proof.h \
  File.h Sort.h

Proof.od: Proof.C Proof.h SolverTypes.h Global.h File.h Sort.h

Solver.od: Solver.C Solver.h SolverTypes.h Global.h VarOrder.h Heap.h \
  Proof.h File.h Sort.h

File.or: File.C File.h Global.h

Main.or: Main.C Solver.h SolverTypes.h Global.h VarOrder.h Heap.h Proof.h \
  File.h Sort.h

Proof.or: Proof.C Proof.h SolverTypes.h Global.h File.h Sort.h

Solver.or: Solver.C Solver.h SolverTypes.h Global.h VarOrder.h Heap.h \
  Proof.h File.h Sort.h
