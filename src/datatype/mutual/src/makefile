SHELL = /bin/sh

mutrec.yak.sml : mutrec.yak
	echo using ml-yacc ; \
	if \
	    ml-yacc mutrec.yak ; \
        then \
            echo ml-yacc succeeded ; \
        else \
	    echo ml-yacc failed, trying sml-yacc ; \
	    sml-yacc mutrec.yak ; \
            echo sml-yacc succeeded ; \
	fi

