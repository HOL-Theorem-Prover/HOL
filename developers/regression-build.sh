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

if [ -d .svn ]
then
    :
else
    die "HOL directory is not under subversion's control"
fi

if [ -x $ML ]
then
    :
else
    die "ML system \"$ML\" is not executable."
fi


if [ $? -ne 0 ]
then
    die "$holdir doesn't appear to be a Subversion directory."
fi

case $kernel in -expk | -stdknl ) : ;; * ) die "Bad kernel spec \"$kernel\"."
esac

if svn update > svn-update 2>&1
then
    updated_ok=ok
else
    updated_ok=
fi

rev=$(svn info 2> /dev/null | grep ^Revision | cut -d' ' -f2)
holid="$kernel:$rev:$(basename $ML)"

case $(uname) in
    Linux )
      cpu=$(grep ^model.name < /proc/cpuinfo |
            perl -ne 'split; shift @_; shift @_; shift @_; $, = " ";
                      print @_; exit;' )
      mem=$(free -m | grep ^Mem | perl -ne 'split; print $_[1], "\n";') ;;
    Darwin )
      cpu=$(system_profiler SPHardwareDataType |
            grep '^ *Processor' |
            perl -ne '$, = " "; split; shift @_; shift @_; print @_, " ";')
      mem=$(top -l 1 | grep ^PhysMem | perl -ne 'split; print $_[7] + $_[9]') ;;
esac

(echo "Running in $holdir on machine $(hostname)" &&
 echo "Uname info (srm): $(uname -srm)" &&
 echo "Cpu: $cpu - Memory: $mem MB" &&
 echo "Started: "$(date +"%a, %d %b %Y %H:%M:%S %z") &&
 echo "Extra commandline arguments: $@" &&
 if [ "$updated_ok" ]
 then
     cat svn-update
 else
     echo "svn update failed - continuing anyway."
 fi &&
 $ML < tools/smart-configure.sml 2>&1 &&
 bin/build cleanAll 2>&1 &&
 bin/build $kernel "$@" 2>&1) |
 tee build-log |
 $gbs "$from" "$holid"
