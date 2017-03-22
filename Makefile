polysr.exe: range.mli range.ml types.ml lexer.mll parser.mly
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlopt range.mli range.ml types.ml parser.mli parser.ml lexer.ml -o polysr.exe

