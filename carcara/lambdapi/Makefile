SRC := $(wildcard *.lp)
OBJ := $(SRC:%.lp=%.lpo)

default: $(OBJ)

$(OBJ)&: $(SRC)
	lambdapi check -c $^

clean:
	rm -f $(OBJ)

install: $(OBJ)
	lambdapi install lambdapi.pkg $(SRC) $(OBJ)

uninstall:
	lambdapi uninstall lambdapi.pkg