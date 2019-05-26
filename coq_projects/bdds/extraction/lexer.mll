

{

open Parser       (* The type token is defined in parser.mli *)
open Dyade
exception Erreur_parsage of int * int
let nb_var = ref 0
let h = Hashtbl.create 103

}
rule token = parse
    [' ' '\t' '\n']     { token lexbuf }     (* skip blanks *)
  | "//" [ ^ '\n']* '\n' { token lexbuf }    (* skip coments *)
  | ['0'-'9' 'a'-'z' 'A'-'Z' '_']+    
             { try
                VAR (Hashtbl.find h (Lexing.lexeme lexbuf))
               with Not_found ->
                         ( 
                         let p = !nb_var in
                         (
                         nb_var:= p+1;
                         Hashtbl.add h (Lexing.lexeme lexbuf) p;
                         VAR p))
              }
  | '&'            { AND }
  | '#'            { OR }
  | '~'		   { NOT }
  | "->"	   { IMPL }
  | "<->"	   { EQ }
  | '('            { LPAREN }
  | ')'            { RPAREN }
  | "<T>"          { TRUE }         
  | "<F>"          { FALSE }
  | eof            { EOF }
  | _              { raise ( Erreur_parsage (Lexing.lexeme_start lexbuf,
                                            Lexing.lexeme_end lexbuf) )}
