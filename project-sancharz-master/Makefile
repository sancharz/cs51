all :   miniml expr evaluation tests 

evaluation : evaluation.ml
	ocamlbuild -lib unix evaluation.byte

expr : expr.ml
	ocamlbuild expr.byte 

miniml : miniml.ml
	ocamlbuild -lib unix miniml.byte


tests : tests.ml
	ocamlbuild -lib unix tests.byte

clean:
	rm -rf _build *.byte