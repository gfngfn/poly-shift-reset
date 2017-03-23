polysr.exe: typevar.mli typevar.ml range.mli range.ml types.ml lexer.mll parser.mly typeenv.mli typeenv.ml subst.mli subst.ml typecheck.mli typecheck.ml rename.mli rename.ml evaluator.ml primitives.ml main.ml
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlopt typevar.mli typevar.ml range.mli range.ml types.ml parser.mli parser.ml lexer.ml typeenv.mli typeenv.ml subst.mli subst.ml typecheck.mli typecheck.ml rename.mli rename.ml evaluator.ml primitives.ml main.ml -o polysr.exe

