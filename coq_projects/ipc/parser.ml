type token =
    ATOM of (int)
  | IMP
  | AND
  | OR
  | EQUIV
  | NOT
  | FALSUM
  | LPAREN
  | RPAREN
  | EOL

open Parsing
let yytransl_const = [|
  258 (* IMP *);
  259 (* AND *);
  260 (* OR *);
  261 (* EQUIV *);
  262 (* NOT *);
  263 (* FALSUM *);
  264 (* LPAREN *);
  265 (* RPAREN *);
  266 (* EOL *);
    0|]

let yytransl_block = [|
  257 (* ATOM *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\000\000"

let yylen = "\002\000\
\002\000\001\000\001\000\003\000\003\000\003\000\003\000\003\000\
\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\003\000\000\000\002\000\000\000\010\000\000\000\
\009\000\000\000\000\000\000\000\000\000\000\000\001\000\004\000\
\000\000\008\000\000\000\000\000"

let yydgoto = "\002\000\
\007\000\008\000"

let yysindex = "\012\000\
\024\255\000\000\000\000\024\255\000\000\024\255\000\000\001\255\
\000\000\019\255\024\255\024\255\024\255\024\255\000\000\000\000\
\031\255\000\000\254\254\031\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\007\255\000\000\010\255\017\255"

let yygindex = "\000\000\
\000\000\252\255"

let yytablesize = 36
let yytable = "\009\000\
\012\000\010\000\011\000\012\000\013\000\014\000\017\000\018\000\
\019\000\020\000\015\000\007\000\001\000\007\000\007\000\005\000\
\005\000\000\000\007\000\007\000\011\000\012\000\013\000\014\000\
\003\000\006\000\006\000\016\000\000\000\004\000\005\000\006\000\
\011\000\012\000\013\000\014\000"

let yycheck = "\004\000\
\003\001\006\000\002\001\003\001\004\001\005\001\011\000\012\000\
\013\000\014\000\010\001\002\001\001\000\004\001\005\001\009\001\
\010\001\255\255\009\001\010\001\002\001\003\001\004\001\005\001\
\001\001\009\001\010\001\009\001\255\255\006\001\007\001\008\001\
\002\001\003\001\004\001\005\001"

let yyact = [|
  (fun _ -> failwith "parser")
; (fun parser_env ->
	let _1 = (peek_val parser_env 1 : 'form) in
	Obj.repr((
# 13 "parser.mly"
                           _1 ) : Search.form))
; (fun parser_env ->
	Obj.repr((
# 16 "parser.mly"
                           Falsum ) : 'form))
; (fun parser_env ->
	let _1 = (peek_val parser_env 0 : int) in
	Obj.repr((
# 17 "parser.mly"
                           Atom _1 ) : 'form))
; (fun parser_env ->
	let _2 = (peek_val parser_env 1 : 'form) in
	Obj.repr((
# 18 "parser.mly"
                           _2 ) : 'form))
; (fun parser_env ->
	let _1 = (peek_val parser_env 2 : 'form) in
	let _3 = (peek_val parser_env 0 : 'form) in
	Obj.repr((
# 19 "parser.mly"
                           Imp (_1,_3) ) : 'form))
; (fun parser_env ->
	let _1 = (peek_val parser_env 2 : 'form) in
	let _3 = (peek_val parser_env 0 : 'form) in
	Obj.repr((
# 20 "parser.mly"
                           And (Imp(_1,_3), Imp(_3,_1) ) ) : 'form))
; (fun parser_env ->
	let _1 = (peek_val parser_env 2 : 'form) in
	let _3 = (peek_val parser_env 0 : 'form) in
	Obj.repr((
# 21 "parser.mly"
                           Or (_1,_3) ) : 'form))
; (fun parser_env ->
	let _1 = (peek_val parser_env 2 : 'form) in
	let _3 = (peek_val parser_env 0 : 'form) in
	Obj.repr((
# 22 "parser.mly"
                           And (_1,_3) ) : 'form))
; (fun parser_env ->
	let _2 = (peek_val parser_env 0 : 'form) in
	Obj.repr((
# 23 "parser.mly"
                           Imp (_2,Falsum) ) : 'form))
(* Entry main *)
; (fun parser_env -> raise (YYexit (peek_val parser_env 0)))
|]
let yytables =
  { actions=yyact;
    transl_const=yytransl_const;
    transl_block=yytransl_block;
    lhs=yylhs;
    len=yylen;
    defred=yydefred;
    dgoto=yydgoto;
    sindex=yysindex;
    rindex=yyrindex;
    gindex=yygindex;
    tablesize=yytablesize;
    table=yytable;
    check=yycheck;
    error_function=parse_error }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (yyparse yytables 1 lexfun lexbuf : Search.form)
