%{
  open Types

  type range_kind = Token of Range.t | Source of source_term


  let make_range rngknd1 rngknd2 =
    let extract_range rngknd =
      match rngknd with
      | (Token rng)        -> rng
      | (Source (_, rng)) -> rng
    in
      Range.unite (extract_range rngknd1) (extract_range rngknd2)

  let binary_operator left op right =
    let (opnm, oprng) = op in
    let rng = make_range (Source left) (Source right) in
      (SrcApply((SrcApply((SrcVar(opnm), oprng), left), Range.dummy "lor"), right), rng)

  let make_abstraction params sast =
    List.fold_right (fun param sa -> (SrcLambda(param, sa), Range.dummy "make_abstraction")) params sast

%}

%token EOI
%token<int * Range.t> INTCONST
%token<Types.variable_name * Range.t> VAR
%token<Range.t> LET LETREC IN IF THEN ELSE
%token<Range.t> LPAREN RPAREN DEFEQ LAMBDA FIX DOT
%token<Range.t> SHIFT RESET
%token<Range.t> PLUS MINUS TIMES DIVIDES EQUAL GT LT GEQ LEQ LAND LOR TRUE FALSE

%start main
%type<Types.source_term> main

%%

main:
  | xplet EOI { $1 }
;
xplet:
  | LET VAR params DEFEQ xplet IN xplet {
        let rng = make_range (Token $1) (Source $7) in
          (SrcLetIn($2, make_abstraction $3 $5, $7), rng)
      }
  | LETREC VAR params DEFEQ xplet IN xplet {
        let rng = make_range (Token $1) (Source $7) in
          (SrcLetIn($2, (SrcFixPoint($2, make_abstraction $3 $5), Range.dummy "letrec"), $7), rng)
      }
  | xpif { $1 }
;
params: /* -> (variable_name * Range.t) list */
  |            { [] }
  | VAR params { $1 :: $2 }
;
xpif:
  | IF xplet THEN xplet ELSE xplet { (SrcIfThenElse($2, $4, $6), make_range (Token $1) (Source $6)) }
  | xpfun                          { $1 }
;
xpfun:
  | LAMBDA VAR DOT xplet { (SrcLambda($2, $4), make_range (Token $1) (Source $4)) }
  | FIX VAR DOT xplet    { (SrcFixPoint($2, $4), make_range (Token $1) (Source $4)) }
  | SHIFT VAR DOT xplet  { (SrcShift($2, $4), make_range (Token $1) (Source $4)) }
  | xplor                { $1 }
;
lorop:
  | LOR { ("||", $1) }
;
xplor:
  | xpland lorop xplor { binary_operator $1 $2 $3 }
  | xpland             { $1 }
;
landop:
  | LAND { ("&&", $1) }
;
xpland:
  | xprel landop xpland { binary_operator $1 $2 $3 }
  | xprel               { $1 }
;
relop:
  | EQUAL { ("==", $1) }  | GT { (">", $1) }  | LT { ("<", $1) }  | GEQ { (">=", $1) }  | LEQ { ("<=", $1) }
;
xprel:
  | xptimes relop xprel { binary_operator $1 $2 $3 }
  | xptimes             { $1 }
;
timesop:
  | TIMES { ("*", $1) }  | DIVIDES { ("/", $1) }
;
xptimes:
  | xpplus timesop xptimes { binary_operator $1 $2 $3 }
  | xpplus                 { $1 }
;
plusop:
  | PLUS { ("+", $1) }  | MINUS { ("-", $1) }
xpplus:
  | xpapp plusop xpplus { binary_operator $1 $2 $3 }
  | xpapp               { $1 }
;
xpapp:
  | xpapp xpbot { (SrcApply($1, $2), make_range (Source $1) (Source $2)) }
  | xpbot       { $1 }
;
binop:
  | lorop   { $1 }
  | landop  { $1 }
  | relop   { $1 }
  | timesop { $1 }
  | plusop  { $1 }
;
xpbot:
  | INTCONST              { let (num, rng) = $1 in (SrcIntConst(num), rng) }
  | TRUE                  { (SrcBoolConst(true), $1) }
  | FALSE                 { (SrcBoolConst(false), $1) }
  | VAR                   { let (varnm, rng) = $1 in (SrcVar(varnm), rng) }
  | LPAREN binop RPAREN   { let (opnm, _) = $2 in (SrcVar(opnm), make_range (Token $1) (Token $3)) }
  | LPAREN xplet RPAREN   { let (utastmain, _) = $2 in (utastmain, make_range (Token $1) (Token $3)) }
;
