
# =====================================================================
# Makefile for new snow watching lantern logo
# Last updated: MJCG Mon Apr 22 17:10:23 BST 2002
# =====================================================================

TGIF=/home/slind/misc/tgif-QPL-4.1.43/tgif

all:
	make logo.gif;make logo.eps

clean:
	rm -f logo.eps logo.gif

logo.gif: logo.obj
	$(TGIF) -print -gif logo.obj
	@echo "=======> logo.gif made"

logo.eps: logo.obj
	$(TGIF) -print -eps logo.obj
	@echo "=======> logo.eps made"

