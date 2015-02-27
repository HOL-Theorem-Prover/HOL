all: clean hh predict

.PHONY: clean hh predict

hh: 
	cd hh/hh1; $(MAKE); \
	cd ..; $(MAKE)

predict: 
	cd predict; $(MAKE)

clean: 
	cd hh/hh1; $(MAKE) -i clean
	cd hh; $(MAKE) -i clean
	cd predict; $(MAKE) -i clean
