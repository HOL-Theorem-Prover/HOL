#!/bin/bash

source ../.acl2holrc.bash

tests_dir=${ACL2_HOL}/tests
inputs_dir=$tests_dir/inputs
results_dir=$tests_dir/results
old_results_dir=$tests_dir/old-results
logs_dir=$tests_dir/logs
old_logs_dir=$tests_dir/old-logs
gold_dir=$tests_dir/gold

if [ "$*" = "clean" ]; then \
    rm -rf $results_dir $old_results_dir $logs_dir $old_logs_dir diffout diffout.old ; \
    cd $inputs_dir ; make clean ; cd .. ; \
    exit 0 ; \
fi

echo "Making books in $inputs_dir..." ; cd $inputs_dir ; make ; cd ..

echo "Converting .lisp files to their essences..."

tests=`ls $inputs_dir/*.lisp`

rm -rf $old_results_dir
if  [ -e $results_dir ]; then mv $results_dir $old_results_dir ; fi
mkdir $results_dir

rm -rf $old_logs_dir
if [ -e $logs_dir ]; then mv $logs_dir $old_logs_dir ; fi
mkdir $logs_dir

if [ -e diffout ]; then mv diffout diffout.old ; fi

for test in $tests ; do \
    test=${test##*/} ; \
    (${ACL2_HOL_LISP}/book-essence.csh $inputs_dir/$test $results_dir/$test) > $logs_dir/$test.out 2> $logs_dir/$test.err ; \
done

(diff $results_dir $gold_dir 2>&1) > diffout

if [ -s diffout ] ; then \
    echo 'FAILURE!  See diffout for unexpected diffs, and see logs/.' ; \
    exit 1 ; \
else \
    echo 'Success!' ; \
    exit 0 ; \
fi
