open Types


let _ =
  let filename_in = Sys.argv.(1) in
  let fin = open_in filename_in in
    Range.initialize_for_lexer () ;
    let sast = Parser.main Lexer.expr (Lexing.from_channel fin) in
    let (vA, _) = Typecheck.fresh () in
    let _ = Typecheck.typecheck Subst.empty Typeenv.empty vA sast in
      print_endline (string_of_source_term sast)
