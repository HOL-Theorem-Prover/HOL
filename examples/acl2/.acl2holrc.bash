# editable variables:

export ACL2_SRC=/home/mk606/acl2/v3-5
if [ "`uname -a | fgrep i686`" != "" ] ; then \
    export ACL2=${ACL2_SRC}/saved_acl2 ; \
elif [ "`uname -a | fgrep x86_64`" != "" ] ; then \
    export ACL2=${ACL2_SRC}/ccl64-saved_acl2 ; \
else \
    echo "ERROR: Unexpected uname." ; \
    exit 1 ; \
fi
export ACL2_HOL=/home/mk606/hol/HOL/examples/acl2

# end of editable variables

export ACL2_SYSTEM_BOOKS=${ACL2_SRC}/books
export ACL2_HOL_LISP=${ACL2_HOL}/lisp
