#!/bin/csh -f

set tests_dir       = ${ACL2_HOL}/tests
set inputs_dir      = $tests_dir/inputs
set results_dir     = $tests_dir/results
set old_results_dir = $tests_dir/old-results
set logs_dir        = $tests_dir/logs
set old_logs_dir    = $tests_dir/old-logs
set gold_dir        = $tests_dir/gold

if ("$argv" == "clean") then
    rm -rf $results_dir $old_results_dir $logs_dir $old_logs_dir diffout diffout.old
    cd $inputs_dir ; make clean ; cd ..
    exit 0
endif

echo "Making books in $inputs_dir..." ; cd $inputs_dir ; make ; cd ..

echo "Converting .lisp files to their essences..."

set tests = `ls $inputs_dir/*.lisp`

rm -rf $old_results_dir
if (-e $results_dir) mv $results_dir $old_results_dir
mkdir $results_dir

rm -rf $old_logs_dir
if (-e $logs_dir) mv $logs_dir $old_logs_dir
mkdir $logs_dir

if (-e diffout) mv diffout diffout.old

foreach test ($tests)
    set test = ${test:t}
    (${ACL2_HOL_LISP}/book-essence.csh $inputs_dir/$test $results_dir/$test) >& $logs_dir/$test.out
end

diff $results_dir $gold_dir >& diffout

if (! -z diffout) then
    echo 'FAILURE!  See diffout for unexpected diffs, and see logs/.'
    exit 1
else
    echo 'Success!'
    exit 0
endif
