polysr.exe: typevar.mli typevar.ml range.mli range.ml types.ml lexer.mll parser.mly main.ml
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlopt typevar.mli typevar.ml range.mli range.ml types.ml parser.mli parser.ml lexer.ml main.ml -o polysr.exe

