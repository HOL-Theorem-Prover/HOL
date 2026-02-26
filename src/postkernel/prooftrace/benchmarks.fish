#!/usr/bin/env fish
git checkout c38cd4913
git clean -xdf
poly --script tools/smart-configure.sml
/usr/bin/time -v bin/build --nograph &| tee /tmp/bench-a.log
git checkout cc2167173
git clean -xdf
poly --script tools/smart-configure.sml
/usr/bin/time -v bin/build --nograph &| tee /tmp/bench-b.log
git clean -xdf
poly --script tools/smart-configure.sml
/usr/bin/time -v bin/build --nograph --trace &| tee /tmp/bench-c.log
cd examples/formal-languages/regular
/usr/bin/time -v ../../../bin/Holmake --trace &| tee /tmp/bench-c-regexp.log
cd -
find . -name "*.pft" -o -name "*.pft.zst" | \
  xargs du -ch | tee /tmp/bench-c-size.log
/usr/bin/time -v bin/prooftrace merge -o bench.pft \
  arithmetic.DIVISION \
  regexp_compiler.regexp_matcher_correct \
  &| tee /tmp/bench-d.log
zstd bench.pft
ls -lh bench.pft bench.pft.zst | tee -a /tmp/bench-d.log
/usr/bin/time -v bin/prooftrace replay bench.pft \
  &| tee /tmp/bench-e.log
