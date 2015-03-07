all: clean hh predict

.PHONY: clean hh predict

hh: 
	cd hh/hh1; $(MAKE); \
	cd ..; $(MAKE) hh

predict: 
	cd predict; $(MAKE)

clean: 
	cd hh/hh1; $(MAKE) clean
	cd hh; $(MAKE) clean
	cd predict; $(MAKE) clean
