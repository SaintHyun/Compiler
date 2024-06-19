type token =
  | PLUS
  | MINUS
  | TIMES
  | DIVIDE
  | EQUAL
  | NOTEQ
  | LEQ
  | LESS
  | GEQ
  | GREATER
  | AND
  | OR
  | NOT
  | LPAR
  | RPAR
  | LSQUARE
  | RSQUARE
  | ASSIGN
  | LBRA
  | RBRA
  | SEMICOLON
  | COMMA
  | TRUE
  | FALSE
  | INT
  | BOOL
  | VOID
  | IF
  | ELSE
  | WHILE
  | RETURN
  | EOF
  | NUM of (int)
  | IDENTIFIER of (string)

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Program.program
