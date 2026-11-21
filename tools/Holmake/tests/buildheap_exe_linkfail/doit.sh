#!/bin/sh
# Driver: `hol buildheap --exe' must fail when linking the executable
# fails.  A `cc' that exits 1 comes first on PATH.  Poly/ML reports
# that exit as wait status 256, whose low byte, all that the process
# exit status keeps, is 0.

set -u

if [ "$#" -ne 1 ]
then
    echo "Usage: $0 hol" 1>&2
    exit 2
fi

hol=$1
dir=$(mktemp -d) || exit 1
trap '/bin/rm -rf "$dir"' EXIT

mkdir "$dir/bin"
printf '#!/bin/sh\ntouch cc-was-run\nexit 1\n' > "$dir/bin/cc"
chmod +x "$dir/bin/cc"
echo 'fun main () = ()' > "$dir/prog.sml"

cd "$dir"
PATH="$dir/bin:$PATH" "$hol" buildheap --poly -o prog --exe=main prog.sml
rc=$?

if [ ! -f cc-was-run ]
then
    echo "FAIL: buildheap did not run cc" 1>&2
    exit 1
fi
if [ $rc -eq 0 ]
then
    echo "FAIL: buildheap --exe exited 0 although cc failed" 1>&2
    exit 1
fi
echo "OK: buildheap --exe exited $rc when cc failed"
