
# =====================================================================
# Makefile for new snow watching lantern logo
# Last updated: MJCG Mon Apr 22 17:10:23 BST 2002
# =====================================================================


all:
	make logo.gif;make logo.eps

clean:
	rm -f logo.eps logo.gif

logo.gif: logo.obj
	tgif -print -gif logo.obj
	@echo "=======> logo.gif made"

logo.eps: logo.obj
	tgif -print -eps logo.obj
	@echo "=======> logo.eps made"

