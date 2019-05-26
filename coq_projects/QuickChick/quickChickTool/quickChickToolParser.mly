%{

open Lexing
open Parsing
open QuickChickToolTypes

(*
type node =
    (* Base chunk of text *)
  | Text of string 
    (* Sections: identifier + a bunch of nodes + extend? *)
  | Section of string * node list * string option
    (* Commented out QuickChick call *)
  | QuickChick of string
    (* Mutant: list of +/- idents, base, list of mutants *)
  | Mutant of (bool * string) list * string * string list 
*)

(* Uncomment for more debugging... *)

%}

%token<string> T_Char 

%token<string> T_Extends

%token<string> T_StartSection
%token<string> T_StartQuickChick
%token<string> T_StartQuickCheck
%token<string> T_StartMutTag
%token<string> T_StartMutant
%token<string> T_StartMutants
%token<string> T_StartComment
%token<string> T_EndComment
%token<string> T_Eof

%start program
%type <QuickChickToolTypes.section list> program
%type <QuickChickToolTypes.section> section
%type <QuickChickToolTypes.section list> sections
%type <QuickChickToolTypes.node list> section_contents
%type <QuickChickToolTypes.node> section_content
%type <mutant list> mutants
%type <mutant> mutant
%type <string list> code
%type <extend option> extends

%% 
program:              default_section T_Eof { [$1] }
                    | default_section sections T_Eof { $1 :: $2 }
                    | error T_Eof { 
                        let pos = Parsing.symbol_start_pos () in
                        failwith (Printf.sprintf "Error in line %d, position %d" 
                                                 pos.pos_lnum (pos.pos_cnum - pos.pos_bol)) }  

default_section:      section_contents
                        { { sec_begin = "" 
                          ; sec_name  = ""
                          ; sec_end   = ""
                          ; sec_extends = None
                          ; sec_nodes = $1 }  }

section_contents:     { [] } 
                    | section_content section_contents { $1 :: $2 }

section_content:      T_Char 
                            {  Text $1 }
                      | T_StartQuickChick code T_EndComment
                            { QuickChick { qc_begin = $1; qc_body = String.concat "" $2; qc_end = $3 } }
                      | T_StartQuickCheck code T_EndComment
                            { QuickChick { qc_begin = $1; qc_body = String.concat "" $2; qc_end = $3 } }
                      | T_StartMutants mutants
                            { Mutants { ms_begin = $1; ms_base = ""; ms_mutants = $2 } }
                      | T_StartMutants code mutants
                            { Mutants { ms_begin = $1; ms_base = String.concat "" $2; ms_mutants = $3 } }
                      | T_StartComment section_contents T_EndComment
                            { Text (Printf.sprintf "%s%s%s" $1 (String.concat "" (List.map output_node $2)) $3) }

code:                 T_Char { [$1] } 
                      | T_Char code { $1 :: $2 }
 /*                     | error { let pos = Parsing.symbol_start_pos () in
                                failwith (Printf.sprintf "Error in line %d, position %d" 
                                                         pos.pos_lnum (pos.pos_cnum - pos.pos_bol)) 
                              } */


mutants:              mutant_tag { [$1] }
                    | mutant_tag mutants { $1 :: $2 }

mutant_tag:           T_StartMutTag code T_EndComment mutant
                        { let m = $4 in {m with mut_info = {m.mut_info with tag = Some (String.concat "" $2)}} }
                    | mutant { $1 }
                                                               
mutant:               T_StartMutant code T_EndComment { let pos = Parsing.symbol_start_pos () in
                                                        { mut_info = { file_name = pos.pos_fname
                                                                     ; line_number = pos.pos_lnum 
                                                                     ; tag = None }
                                                        ; mut_begin = $1 ; mut_body = String.concat "" $2 ; mut_end = $3 } }
                    | T_StartMutants
                        { let pos = Parsing.symbol_start_pos () in
                          { mut_info = { file_name   = pos.pos_fname
                                       ; line_number = pos.pos_lnum 
                                       ; tag = None }
                          ; mut_begin = "(*" ; mut_body = "" ; mut_end = "*)" } }

sections:             section { [$1] }
                    | section sections { $1 :: $2 }
                      
section:              T_StartSection code T_EndComment extends section_contents
                        { { sec_begin   = $1
                          ; sec_name    = String.concat "" $2
                          ; sec_end     = $3
                          ; sec_extends = $4
                          ; sec_nodes   = $5 } }

extends:              { None }
                    | T_Extends code T_EndComment { Some { ext_begin = $1 ; ext_extends = $2 ; ext_end = $3 } }

