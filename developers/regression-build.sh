#!/bin/bash

die ()
{
    echo "$1" >&2
    exit 1
}

usage()
{
    die "Usage: $0 from-address gbs holdir ML kernelflag [other build options]"
}

if [ $# -lt 5 ]
then
    usage
fi

from=$1
shift
gbs=$1
shift

if [ -x $gbs ]
then
    :
else
    die "Generate build summary program \"$gbs\" not executable."
fi

holdir=$1
ML=$2
kernel=$3
shift 3

if [ -d $holdir -a -x $holdir -a -r $holdir ]
then
  cd $holdir
else
  die "HOL directory \"$holdir\" doesn't exist or is inaccessible."
fi

if [ -r std.prelude -a -d sigobj -a -r tools/smart-configure.sml ]
then
    :
else
    die "Directory \"$holdir\" unlikely (no std.prelude, sigobj or configure.sml)"
fi

if [ -x $ML ]
then
    :
else
    die "ML system \"$ML\" is not executable."
fi

rev=$(svn info 2> /dev/null | grep ^Revision | cut -d' ' -f2)

if [ $? -ne 0 ]
then
    die "$holdir doesn't appear to be a Subversion directory."
fi

case $kernel in -expk | -stdknl ) : ;; * ) die "Bad kernel spec \"$kernel\"."
esac

holid="$kernel:$rev:$(basename $ML)"



(echo "Running in $holdir on machine $(hostname)" &&
  svn update 2>&1 &&
  $ML < tools/smart-configure.sml 2>&1 &&
  bin/build cleanAll 2>&1 &&
  bin/build $kernel "$@" 2>&1) |
  tee build-log |
  $gbs "$from" "$holid"
