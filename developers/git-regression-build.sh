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

otheropts=$(echo "$@" | sed '
s/ //g
s/-fullbuild//
')

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

if [ -d .git ]
then
    :
else
    die "HOL directory is not under git's control"
fi

if [ -x $ML ]
then
    :
else
    die "ML system \"$ML\" is not executable."
fi

case $kernel in --expk | --stdknl | --otknl ) : ;; * ) die "Bad kernel spec \"$kernel\"."
esac

if git pull > update-log 2>&1
then
    updated_ok=ok
else
    updated_ok=
fi

rev=$(git log --pretty=format:'%h' -n1 HEAD)
cd developers
mlsys=$($ML < mlsysinfo.sml | grep MLSYSTEM | awk '{print $3}')
cd ..

holid="$kernel:$rev:$mlsys:$otheropts"

cpuperlprog='
  while (<>) {
    if (/^model.name\s*:\s*(.*)$/) {
      $info = $1;
      $info =~ s/\s+/ /g;
      push @cpuinfo, $info;
    }
  }
  $numcpus = scalar(@cpuinfo);
  if ($numcpus == 0) { print "<NO CPU INFO???>\n"; exit; }
  if ($numcpus > 1) {
    $first = $cpuinfo[0];
    $i=1;
    while ($i < $numcpus) {
      break if ($cpuinfo[$i] ne $first);
      $i++;
    }
    if ($i < $numcpus) { $, = ", "; print @cpuinfo; print "\n"; exit }
    print $first, "  x $numcpus\n"; exit;
  }
  print $cpuinfo[0], "\n";'


case $(uname) in
    Linux )
      cpu=$(perl -e "$cpuperlprog" < /proc/cpuinfo)
      mem=$(free -m | grep "^Mem" | awk '{print $2;}') ;;
    Darwin )
      cpu=$(system_profiler SPHardwareDataType |
            grep '^ *Processor' |
            perl -ne '$, = " "; split; shift @_; shift @_; print @_, " ";')
      mem=$(top -l 1 | grep ^PhysMem | perl -ne 'split; print $_[7] + $_[9]') ;;
esac

maybeBuild ()
{
    if [ -r build-running ]
    then
        local now=$(date +%s)
        local brtime=$(stat --format=%Y build-running)
        # if mtime on file is recent enough; don't build.  Otherwise, drop
        # through and allow build to go ahead.  This is because the
        # build-running flag in the file system doesn't seem to be quite
        # reliable in practice.
        if ((now - brtime < 60 * 60 * 24))
        then
            echo "Another build appears to be running - giving up"
            return 0
        fi
    fi
    git clean -xd -e build-logs
    (touch build-running &&
     $ML < tools/smart-configure.sml 2>&1 &&
     bin/build cleanAll 2>&1 &&
     bin/build $kernel "$@" 2>&1 ;
     /bin/rm build-running) | tee build-log
}


(echo "Running in $holdir on machine $(hostname)" &&
 echo "Uname info (srm): $(uname -srm)" &&
 echo "Cpu: $cpu" &&
 echo "Memory: $mem MB" &&
 echo "PATH: $PATH" &&
 echo "ML Implementation: $mlsys" &&
 echo "Started: "$(date +"%a, %d %b %Y %H:%M:%S %z") &&
 echo "Extra commandline arguments: $@" &&
 echo -n "Revision: " &&
 git log -n1 --pretty=format:'%h %s%n' HEAD &&
 if [ "$updated_ok" ]
 then
     cat update-log
 else
     echo "git pull failed - "
     (while read line ; do echo "  $line" ; done) < update-log
     echo "continuing anyway"
 fi &&
 echo "-- Configuration Description Ends --" &&
 echo &&
 maybeBuild "$@") |
 $gbs "$from" "$holid"
