%{
open Dyade

let rec i2p = function 
  1 -> XH 
| n -> let n' = i2p (n/2) in 
       if (n mod 2)=0 then XO n' else XI n';;
 

let i2ad = function 
  0 -> N0
| n -> Npos (i2p n)

%}

%token <int> VAR
%token AND OR NOT EQ IMPL TRUE FALSE
%token LPAREN RPAREN
%token EOF

%right EQ IMPL
%left OR
%left AND  
%nonassoc NOT 


%start main      
%type <Dyade.bool_expr> main

%%

main:
    expression EOF              {  $1 }
;
expression :
    VAR                  	{ Var (i2ad $1)  }
  | TRUE 		  	{ One }
  | FALSE		    	{ Zero }
  | LPAREN expression RPAREN    { $2 }
  | expression AND expression 	{ ANd($1,$3) }
  | expression OR expression    { Or($1,$3) }
  | expression IMPL expression  { Impl($1,$3) }
  | expression EQ expression	{ Iff($1,$3) }
  | NOT expression              { Neg $2 }
;


