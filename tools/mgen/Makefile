BIN = mgen
SRC = \
	match.ml \
	fuzz.ml \
	cgen.ml \
	test.ml

$(BIN): $(SRC)
	ocamlopt -o $(BIN) $(SRC)

clean:
	rm -f *.cm? *.o $(BIN)

.PHONY: clean
