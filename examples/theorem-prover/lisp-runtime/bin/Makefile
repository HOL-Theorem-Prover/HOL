
NAME=jitawa

all: verified_code.s
	cpp jit_exec.s jit_exec_cpp.s
	date '+#define NOW "%Y-%m-%d %H:%M:%S"' > wrapper.h
	gcc -O2 wrapper.c jit_exec_cpp.s -o $(NAME)
	/bin/rm -f jit_exec_cpp.s wrapper.h

verified_code.s:
	cd ../implementation && Holmake && cd ../bin

debug:
	cpp jit_exec.s jit_exec_cpp.s
	date '+#define NOW "%Y-%m-%d %H:%M:%S"' > wrapper.h
	gcc -O2 -D DEBUG -g wrapper.c jit_exec_cpp.s -o $(NAME)
	/bin/rm -f jit_exec_cpp.s wrapper.h

clean:
	/bin/rm -fR *.dSYM $(NAME)

zip:
	/bin/rm -fR $(NAME).zip $(NAME)
	zip -r $(NAME).zip Makefile wrapper.c jit_exec.s verified_code.s
