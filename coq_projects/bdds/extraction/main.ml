open Unix;;

let analyze_file channel  =
try
  let lexbuf = Lexing.from_channel channel in
    Hashtbl.clear Lexer.h;
    Lexer.nb_var := 0;
    Parser.main Lexer.token lexbuf
with
      _ -> failwith "syntax error"


let _ =
  let channel = (in_channel_of_descr  ( openfile Sys.argv.(1) [O_RDONLY] 0644 ))
  in
  let e = analyze_file channel
  in 
  if Dyade.is_tauto e then
    (Printf.printf "Tautology\n"; exit 0)
  else
    (Printf.printf "Not a tautology"; exit 1)

