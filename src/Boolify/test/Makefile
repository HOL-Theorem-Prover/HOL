# Makefile for boolification test cases
# Created by Joe Hurd, January 2002

HOL=hol.bare.unquote -I ../src

TMPFILE1=/tmp/test-make-file1
TMPFILE2=/tmp/test-make-file2

all: result diff

clean:
	rm -f result

diff:
	@grep -v 'HOL.* (built \|^\(- \)*runtime: \|User: ' <result.ok >$(TMPFILE1)
	@grep -v 'HOL.* (built \|^\(- \)*runtime: \|User: ' <result >$(TMPFILE2)
	@diff $(TMPFILE1) $(TMPFILE2)

result: test.sml ../src/Encode.uo
	rm -f result
	$(HOL) <test.sml 2>&1 | tee result
