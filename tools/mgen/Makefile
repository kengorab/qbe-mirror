BIN = mgen
SRC = \
	match.ml \
	fuzz.ml \
	cgen.ml \
	sexp.ml \
	test.ml

$(BIN): $(SRC)
	ocamlopt -o $(BIN) str.cmxa $(SRC)

clean:
	rm -f *.cm? *.o $(BIN)

.PHONY: clean
