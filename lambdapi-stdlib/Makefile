SRC := $(wildcard *.lp)
OBJ := $(SRC:%.lp=%.lpo)

default: $(OBJ)

# One lambdapi invocation per module: `lambdapi check -c` compiles the
# dependencies on demand, and checking every file in a single process trips
# the .lpo loader on modules that carry string literals (see Tactic.lp).
%.lpo: %.lp
	lambdapi check -c -v 0 -w $<

clean:
	rm -f $(OBJ)

install: $(OBJ)
	lambdapi install lambdapi.pkg $(SRC) $(OBJ)

uninstall:
	lambdapi uninstall lambdapi.pkg
