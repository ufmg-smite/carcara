SHELL := /bin/bash
SRC := $(wildcard *.lp)
OBJ := $(SRC:%.lp=%.lpo)

all: $(OBJ)

-include lpo.mk

lpo.mk:
	@touch lpo.mk
	@for f in *.lp ; do \
		echo -n "$${f}o:" >> lpo.mk ; \
		gawk 'BEGIN{FS="[ .;]"}/^require open {{proof}}/{printf" %s.lpo",$$4;next}/^[^r\/]/{nextfile}' $$f >> lpo.mk ; \
		echo >> lpo.mk ; \
	done

%.lpo: %.lp
	lambdapi check -v 0 $<

.PHONY: clean
clean:
	@rm -f *.lpo
	@rm -f *.lpo.mk
	@rm -f lpo.mk
