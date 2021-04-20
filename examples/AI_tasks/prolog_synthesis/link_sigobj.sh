SIGOBJ=../../../sigobj
FILE=$(pwd)/$1
BASE=${FILE%.*}
LINK=$SIGOBJ/$(basename $BASE)
ln -sf $BASE.sig $LINK.sig
ln -sf $BASE.uo $LINK.uo
ln -sf $BASE.ui $LINK.ui
