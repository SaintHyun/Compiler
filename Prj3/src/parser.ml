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

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
# 41 "parser.ml"
let yytransl_const = [|
  257 (* PLUS *);
  258 (* MINUS *);
  259 (* TIMES *);
  260 (* DIVIDE *);
  261 (* EQUAL *);
  262 (* NOTEQ *);
  263 (* LEQ *);
  264 (* LESS *);
  265 (* GEQ *);
  266 (* GREATER *);
  267 (* AND *);
  268 (* OR *);
  269 (* NOT *);
  270 (* LPAR *);
  271 (* RPAR *);
  272 (* LSQUARE *);
  273 (* RSQUARE *);
  274 (* ASSIGN *);
  275 (* LBRA *);
  276 (* RBRA *);
  277 (* SEMICOLON *);
  278 (* COMMA *);
  279 (* TRUE *);
  280 (* FALSE *);
  281 (* INT *);
  282 (* BOOL *);
  283 (* VOID *);
  284 (* IF *);
  285 (* ELSE *);
  286 (* WHILE *);
  287 (* RETURN *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  288 (* NUM *);
  289 (* IDENTIFIER *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\003\000\003\000\003\000\004\000\004\000\006\000\
\006\000\006\000\007\000\007\000\008\000\008\000\008\000\008\000\
\005\000\005\000\005\000\009\000\009\000\009\000\009\000\009\000\
\009\000\010\000\010\000\012\000\012\000\011\000\011\000\011\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\011\000\011\000\000\000"

let yylen = "\002\000\
\002\000\008\000\001\000\001\000\001\000\001\000\001\000\000\000\
\001\000\003\000\002\000\002\000\002\000\002\000\005\000\005\000\
\000\000\002\000\002\000\002\000\004\000\002\000\003\000\008\000\
\007\000\001\000\004\000\000\000\004\000\001\000\001\000\001\000\
\001\000\004\000\003\000\003\000\003\000\003\000\002\000\002\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\002\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\005\000\004\000\003\000\051\000\000\000\000\000\
\001\000\000\000\000\000\000\000\000\000\006\000\000\000\007\000\
\000\000\012\000\011\000\000\000\000\000\000\000\010\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\019\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\022\000\031\000\032\000\030\000\000\000\
\000\000\000\000\002\000\020\000\018\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\049\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\023\000\000\000\000\000\000\000\000\000\
\000\000\000\000\050\000\000\000\000\000\000\000\037\000\038\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\027\000\021\000\016\000\015\000\000\000\000\000\034\000\000\000\
\000\000\000\000\025\000\000\000\024\000\000\000\000\000\029\000"

let yydgoto = "\002\000\
\006\000\007\000\008\000\015\000\031\000\016\000\017\000\032\000\
\033\000\034\000\049\000\109\000"

let yysindex = "\011\000\
\022\255\000\000\000\000\000\000\000\000\000\000\014\000\242\254\
\000\000\008\255\030\255\017\255\025\255\000\000\045\255\000\000\
\043\255\000\000\000\000\047\255\238\254\017\000\000\000\017\000\
\034\255\035\255\055\255\060\255\038\255\066\255\063\255\059\255\
\017\000\081\255\000\000\068\255\084\255\040\255\040\255\040\255\
\040\255\040\255\040\255\000\000\000\000\000\000\000\000\088\255\
\107\255\040\255\000\000\000\000\000\000\040\255\070\255\073\255\
\251\255\010\000\021\255\021\255\000\000\025\000\040\255\040\255\
\040\255\040\255\040\255\040\255\040\255\040\255\040\255\040\255\
\040\255\040\255\040\255\000\000\217\255\128\255\089\255\103\255\
\102\255\104\255\000\000\234\255\021\255\021\255\000\000\000\000\
\042\255\042\255\042\255\042\255\042\255\042\255\107\000\050\000\
\000\000\000\000\000\000\000\000\017\000\017\000\000\000\105\255\
\106\255\093\255\000\000\108\255\000\000\017\000\121\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\109\255\000\000\000\000\000\000\000\000\000\000\
\127\255\000\000\000\000\000\000\109\255\123\255\000\000\123\255\
\000\000\000\000\000\000\000\000\000\000\126\255\000\000\000\000\
\123\255\000\000\000\000\124\255\137\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\086\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\145\255\162\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\179\255\196\255\000\000\000\000\
\064\255\051\000\058\000\065\000\072\000\079\000\086\000\106\000\
\000\000\000\000\000\000\000\000\123\255\123\255\000\000\000\000\
\000\000\246\254\000\000\000\000\000\000\123\255\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\000\000\232\255\127\000\000\000\000\000\
\000\000\000\000\219\255\000\000"

let yytablesize = 383
let yytable = "\035\000\
\057\000\058\000\059\000\060\000\061\000\062\000\012\000\013\000\
\053\000\028\000\028\000\001\000\077\000\009\000\028\000\028\000\
\078\000\028\000\010\000\028\000\028\000\011\000\028\000\066\000\
\067\000\084\000\085\000\086\000\087\000\088\000\089\000\090\000\
\091\000\092\000\093\000\094\000\095\000\096\000\040\000\041\000\
\040\000\041\000\064\000\065\000\066\000\067\000\003\000\004\000\
\005\000\018\000\042\000\043\000\042\000\043\000\012\000\013\000\
\014\000\019\000\044\000\020\000\045\000\046\000\045\000\046\000\
\021\000\022\000\036\000\037\000\038\000\047\000\048\000\047\000\
\048\000\039\000\041\000\041\000\104\000\105\000\041\000\052\000\
\041\000\050\000\051\000\055\000\041\000\111\000\033\000\033\000\
\033\000\033\000\033\000\033\000\033\000\033\000\033\000\033\000\
\033\000\033\000\054\000\056\000\033\000\079\000\033\000\063\000\
\080\000\099\000\033\000\064\000\065\000\066\000\067\000\068\000\
\069\000\070\000\071\000\072\000\073\000\074\000\075\000\100\000\
\101\000\108\000\102\000\008\000\106\000\107\000\110\000\076\000\
\064\000\065\000\066\000\067\000\068\000\069\000\070\000\071\000\
\072\000\073\000\074\000\075\000\112\000\009\000\017\000\026\000\
\014\000\039\000\039\000\023\000\098\000\039\000\039\000\039\000\
\039\000\039\000\039\000\039\000\039\000\013\000\000\000\039\000\
\000\000\039\000\040\000\040\000\000\000\039\000\040\000\040\000\
\040\000\040\000\040\000\040\000\040\000\040\000\000\000\000\000\
\040\000\000\000\040\000\035\000\035\000\000\000\040\000\035\000\
\035\000\035\000\035\000\035\000\035\000\035\000\035\000\000\000\
\000\000\035\000\000\000\035\000\036\000\036\000\000\000\035\000\
\036\000\036\000\036\000\036\000\036\000\036\000\036\000\036\000\
\000\000\000\000\036\000\000\000\036\000\000\000\000\000\000\000\
\036\000\064\000\065\000\066\000\067\000\068\000\069\000\070\000\
\071\000\072\000\073\000\074\000\075\000\000\000\000\000\000\000\
\000\000\097\000\064\000\065\000\066\000\067\000\068\000\069\000\
\070\000\071\000\072\000\073\000\074\000\075\000\000\000\000\000\
\000\000\000\000\103\000\064\000\065\000\066\000\067\000\068\000\
\069\000\070\000\071\000\072\000\073\000\074\000\075\000\000\000\
\000\000\081\000\064\000\065\000\066\000\067\000\068\000\069\000\
\070\000\071\000\072\000\073\000\074\000\075\000\000\000\000\000\
\082\000\064\000\065\000\066\000\067\000\068\000\069\000\070\000\
\071\000\072\000\073\000\074\000\075\000\024\000\000\000\083\000\
\000\000\025\000\026\000\000\000\027\000\000\000\028\000\029\000\
\000\000\030\000\064\000\065\000\066\000\067\000\068\000\069\000\
\070\000\071\000\072\000\073\000\074\000\042\000\042\000\000\000\
\000\000\042\000\000\000\042\000\043\000\043\000\000\000\042\000\
\043\000\000\000\043\000\044\000\044\000\000\000\043\000\044\000\
\000\000\044\000\045\000\045\000\000\000\044\000\045\000\000\000\
\045\000\046\000\046\000\000\000\045\000\046\000\000\000\046\000\
\047\000\047\000\000\000\046\000\047\000\000\000\047\000\000\000\
\000\000\000\000\047\000\064\000\065\000\066\000\067\000\068\000\
\069\000\070\000\071\000\072\000\073\000\048\000\000\000\000\000\
\048\000\000\000\048\000\000\000\000\000\000\000\048\000"

let yycheck = "\024\000\
\038\000\039\000\040\000\041\000\042\000\043\000\025\001\026\001\
\033\000\020\001\021\001\001\000\050\000\000\000\025\001\026\001\
\054\000\028\001\033\001\030\001\031\001\014\001\033\001\003\001\
\004\001\063\000\064\000\065\000\066\000\067\000\068\000\069\000\
\070\000\071\000\072\000\073\000\074\000\075\000\001\001\002\001\
\001\001\002\001\001\001\002\001\003\001\004\001\025\001\026\001\
\027\001\033\001\013\001\014\001\013\001\014\001\025\001\026\001\
\027\001\033\001\021\001\015\001\023\001\024\001\023\001\024\001\
\022\001\019\001\033\001\033\001\014\001\032\001\033\001\032\001\
\033\001\014\001\011\001\012\001\101\000\102\000\015\001\021\001\
\017\001\016\001\020\001\016\001\021\001\110\000\001\001\002\001\
\003\001\004\001\005\001\006\001\007\001\008\001\009\001\010\001\
\011\001\012\001\018\001\016\001\015\001\032\001\017\001\016\001\
\032\001\017\001\021\001\001\001\002\001\003\001\004\001\005\001\
\006\001\007\001\008\001\009\001\010\001\011\001\012\001\017\001\
\019\001\029\001\019\001\015\001\020\001\020\001\019\001\021\001\
\001\001\002\001\003\001\004\001\005\001\006\001\007\001\008\001\
\009\001\010\001\011\001\012\001\020\001\015\001\020\001\018\001\
\021\001\001\001\002\001\021\000\021\001\005\001\006\001\007\001\
\008\001\009\001\010\001\011\001\012\001\021\001\255\255\015\001\
\255\255\017\001\001\001\002\001\255\255\021\001\005\001\006\001\
\007\001\008\001\009\001\010\001\011\001\012\001\255\255\255\255\
\015\001\255\255\017\001\001\001\002\001\255\255\021\001\005\001\
\006\001\007\001\008\001\009\001\010\001\011\001\012\001\255\255\
\255\255\015\001\255\255\017\001\001\001\002\001\255\255\021\001\
\005\001\006\001\007\001\008\001\009\001\010\001\011\001\012\001\
\255\255\255\255\015\001\255\255\017\001\255\255\255\255\255\255\
\021\001\001\001\002\001\003\001\004\001\005\001\006\001\007\001\
\008\001\009\001\010\001\011\001\012\001\255\255\255\255\255\255\
\255\255\017\001\001\001\002\001\003\001\004\001\005\001\006\001\
\007\001\008\001\009\001\010\001\011\001\012\001\255\255\255\255\
\255\255\255\255\017\001\001\001\002\001\003\001\004\001\005\001\
\006\001\007\001\008\001\009\001\010\001\011\001\012\001\255\255\
\255\255\015\001\001\001\002\001\003\001\004\001\005\001\006\001\
\007\001\008\001\009\001\010\001\011\001\012\001\255\255\255\255\
\015\001\001\001\002\001\003\001\004\001\005\001\006\001\007\001\
\008\001\009\001\010\001\011\001\012\001\021\001\255\255\015\001\
\255\255\025\001\026\001\255\255\028\001\255\255\030\001\031\001\
\255\255\033\001\001\001\002\001\003\001\004\001\005\001\006\001\
\007\001\008\001\009\001\010\001\011\001\011\001\012\001\255\255\
\255\255\015\001\255\255\017\001\011\001\012\001\255\255\021\001\
\015\001\255\255\017\001\011\001\012\001\255\255\021\001\015\001\
\255\255\017\001\011\001\012\001\255\255\021\001\015\001\255\255\
\017\001\011\001\012\001\255\255\021\001\015\001\255\255\017\001\
\011\001\012\001\255\255\021\001\015\001\255\255\017\001\255\255\
\255\255\255\255\021\001\001\001\002\001\003\001\004\001\005\001\
\006\001\007\001\008\001\009\001\010\001\012\001\255\255\255\255\
\015\001\255\255\017\001\255\255\255\255\255\255\021\001"

let yynames_const = "\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIVIDE\000\
  EQUAL\000\
  NOTEQ\000\
  LEQ\000\
  LESS\000\
  GEQ\000\
  GREATER\000\
  AND\000\
  OR\000\
  NOT\000\
  LPAR\000\
  RPAR\000\
  LSQUARE\000\
  RSQUARE\000\
  ASSIGN\000\
  LBRA\000\
  RBRA\000\
  SEMICOLON\000\
  COMMA\000\
  TRUE\000\
  FALSE\000\
  INT\000\
  BOOL\000\
  VOID\000\
  IF\000\
  ELSE\000\
  WHILE\000\
  RETURN\000\
  EOF\000\
  "

let yynames_block = "\
  NUM\000\
  IDENTIFIER\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Program.func) in
    Obj.repr(
# 24 "parser.mly"
                  ( _1 )
# 304 "parser.ml"
               : Program.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 7 : 'ctype) in
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'argdecl) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 26 "parser.mly"
                                                         ( (_2, _1, _4, _7) )
# 314 "parser.ml"
               : Program.func))
; (fun __caml_parser_env ->
    Obj.repr(
# 28 "parser.mly"
             ( failwith "In this phase, cannot have 'void' as return type" )
# 320 "parser.ml"
               : 'ctype))
; (fun __caml_parser_env ->
    Obj.repr(
# 29 "parser.mly"
             ( Program.CBool )
# 326 "parser.ml"
               : 'ctype))
; (fun __caml_parser_env ->
    Obj.repr(
# 30 "parser.mly"
            ( Program.CInt )
# 332 "parser.ml"
               : 'ctype))
; (fun __caml_parser_env ->
    Obj.repr(
# 32 "parser.mly"
               ( failwith "In this phase, cannot have 'void' argument" )
# 338 "parser.ml"
               : 'argdecl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 33 "parser.mly"
               ( _1 )
# 345 "parser.ml"
               : 'argdecl))
; (fun __caml_parser_env ->
    Obj.repr(
# 35 "parser.mly"
                    ( [] )
# 351 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'adecl) in
    Obj.repr(
# 36 "parser.mly"
            ( [_1] )
# 358 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'adecl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 37 "parser.mly"
                       ( _1 :: _3 )
# 366 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 39 "parser.mly"
                        ( (Program.CBool, _2) )
# 373 "parser.ml"
               : 'adecl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 40 "parser.mly"
                       ( (Program.CInt, _2) )
# 380 "parser.ml"
               : 'adecl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 42 "parser.mly"
                        ( (Program.CBool, _2) )
# 387 "parser.ml"
               : 'vdecl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 43 "parser.mly"
                       ( (Program.CInt, _2) )
# 394 "parser.ml"
               : 'vdecl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 44 "parser.mly"
                                            ( (Program.CBoolArr _4, _2) )
# 402 "parser.ml"
               : 'vdecl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 45 "parser.mly"
                                           ( (Program.CIntArr _4, _2) )
# 410 "parser.ml"
               : 'vdecl))
; (fun __caml_parser_env ->
    Obj.repr(
# 47 "parser.mly"
                      ( [] )
# 416 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 48 "parser.mly"
                   ( _1 :: _2 )
# 424 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 49 "parser.mly"
                        ( _2 )
# 431 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'vdecl) in
    Obj.repr(
# 51 "parser.mly"
                      ( Program.LocalDecl _1 )
# 438 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'lvalue) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 52 "parser.mly"
                                  ( Program.Assign (_1, _3) )
# 446 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 53 "parser.mly"
                       ( failwith "In this phase, 'return' must have a value" )
# 452 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 54 "parser.mly"
                           ( Program.ReturnValue _2 )
# 459 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'exp) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'stmts) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'elseopt) in
    Obj.repr(
# 55 "parser.mly"
                                               ( Program.If (_3, _6, _8) )
# 468 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'exp) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 56 "parser.mly"
                                          ( Program.While (_3, _6) )
# 476 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 58 "parser.mly"
                   ( Program.LVar _1 )
# 483 "parser.ml"
               : 'lvalue))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 59 "parser.mly"
                                       ( Program.LArr (_1, _3) )
# 491 "parser.ml"
               : 'lvalue))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
                        ( [] )
# 497 "parser.ml"
               : 'elseopt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 62 "parser.mly"
                               ( _3 )
# 504 "parser.ml"
               : 'elseopt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 64 "parser.mly"
          ( Program.ConstInt _1 )
# 511 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    Obj.repr(
# 65 "parser.mly"
           ( Program.ConstBool true )
# 517 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    Obj.repr(
# 66 "parser.mly"
            ( Program.ConstBool false )
# 523 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 67 "parser.mly"
                 ( Program.Var _1 )
# 530 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 68 "parser.mly"
                                     ( Program.Arr (_1, _3) )
# 538 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 69 "parser.mly"
                   ( Program.Add (_1, _3) )
# 546 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 70 "parser.mly"
                    ( Program.Sub (_1, _3) )
# 554 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 71 "parser.mly"
                    ( Program.Mul (_1, _3) )
# 562 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 72 "parser.mly"
                     ( Program.Div (_1, _3) )
# 570 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 73 "parser.mly"
               ( _2 )
# 577 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 74 "parser.mly"
                ( Program.Neg _2 )
# 584 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 75 "parser.mly"
                    ( Program.Equal (_1, _3) )
# 592 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 76 "parser.mly"
                    ( Program.NotEq (_1, _3) )
# 600 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 77 "parser.mly"
                  ( Program.LessEq (_1, _3) )
# 608 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 78 "parser.mly"
                   ( Program.LessThan (_1, _3) )
# 616 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 79 "parser.mly"
                  ( Program.GreaterEq (_1, _3) )
# 624 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 80 "parser.mly"
                      ( Program.GreaterThan (_1, _3) )
# 632 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 81 "parser.mly"
                  ( Program.And (_1, _3) )
# 640 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 82 "parser.mly"
                 ( Program.Or (_1, _3) )
# 648 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 83 "parser.mly"
              ( Program.Not _2 )
# 655 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 84 "parser.mly"
                    ( _2 )
# 662 "parser.ml"
               : 'exp))
(* Entry program *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let program (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Program.program)
