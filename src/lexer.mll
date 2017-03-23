{
  open Parser

  exception Error of string


  let get_range = Range.from_lexer
}

let space = [' ' '\t']
let break = ['\n']
let digit = ['0'-'9']
let capital = ['A'-'Z']
let small = ['a'-'z']
let latin = ( small | capital )
let identifier = (small (digit | latin | "_")*)

rule expr = parse
  | space { expr lexbuf }
  | break { begin Range.update_line lexbuf ; expr lexbuf end }
  | "("  { LPAREN(get_range lexbuf) }
  | ")"  { RPAREN(get_range lexbuf) }
  | "+"  { PLUS(get_range lexbuf) }
  | "-"  { MINUS(get_range lexbuf) }
  | "*"  { TIMES(get_range lexbuf) }
  | "/"  { DIVIDES(get_range lexbuf) }
  | "."  { DOT(get_range lexbuf) }
  | "\\" { LAMBDA(get_range lexbuf) }
  | "="  { DEFEQ(get_range lexbuf) }
  | "==" { EQUAL(get_range lexbuf) }
  | ">"  { GT(get_range lexbuf) }
  | "<"  { LT(get_range lexbuf) }
  | ">=" { GEQ(get_range lexbuf) }
  | "<=" { LEQ(get_range lexbuf) }
  | "&&" { LAND(get_range lexbuf) }
  | "||" { LOR(get_range lexbuf) }
  | (digit +) { INTCONST(int_of_string (Lexing.lexeme lexbuf), get_range lexbuf) }
  | identifier {
        let rng = get_range lexbuf in
        let tok = Lexing.lexeme lexbuf in
          match tok with
          | "let"    -> LET(rng)
          | "in"     -> IN(rng)
          | "letrec" -> LETREC(rng)
          | "fix"    -> FIX(rng)
          | "if"     -> IF(rng)
          | "then"   -> THEN(rng)
          | "else"   -> ELSE(rng)
          | "true"   -> TRUE(rng)
          | "false"  -> FALSE(rng)
          | "shift"  -> SHIFT(rng)
          | "reset"  -> RESET(rng)
          | _        -> VAR(tok, rng)
      }
  | eof { EOI }
  | _ as c { raise (Error("illegal token '" ^ (String.make 1 c) ^ "'")) }
