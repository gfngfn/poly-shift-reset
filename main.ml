open Types


let _ =
  let filename_in = Sys.argv.(1) in
  let fin = open_in filename_in in
    Range.initialize_for_lexer () ;
    let sast = Parser.main Lexer.expr (Lexing.from_channel fin) in
      print_endline (string_of_source_tree sast)
