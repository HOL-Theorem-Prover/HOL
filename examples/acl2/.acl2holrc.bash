# Editable variables (with some attempt to determine them
# automatically for Matt Kaufmann):

hostname=`hostname`

if [ "$hostname" = "kala.cl.cam.ac.uk" ] ; then \
	export ACL2_SRC=/home/mk606/acl2/v4-0/acl2-sources ; \
	export ACL2=${ACL2_SRC}/saved_acl2 ; \
	export ACL2_HOL=/home/mk606/hol/HOL/examples/acl2
elif [ "$hostname" = "oliphaunt-0.cs.utexas.edu" ] ; then \
	export ACL2_SRC=/projects/acl2/v4-0-linux-64 ; \
	export ACL2=${ACL2_SRC}/ccl-saved_acl2 ; \
	export ACL2_HOL=/u/kaufmann/projects/HOL/examples/acl2
else
	export ACL2_SRC=/Users/kaufmann/acl2/v4-0/acl2-sources ; \
	export ACL2=${ACL2_SRC}/saved_acl2 ; \
	export ACL2_HOL=/Users/kaufmann/projects/HOL/examples/acl2
fi

# end of editable variables

export ACL2_SYSTEM_BOOKS=${ACL2_SRC}/books
export ACL2_HOL_LISP=${ACL2_HOL}/lisp
