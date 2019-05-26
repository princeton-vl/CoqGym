(*==========================================================*)
(*           Auxillary Functions                            *)
(*==========================================================*)

let string_chars s =
  let res = ref [] in
    String.iter (fun x -> res := (List.append !res [x])) s;
    !res

let eq_char x y = if (x = y) then Left else Right

let conv_list l = List.fold_right (fun x y -> (Cons (x,y)))  l Nil

let conv_string l = (conv_list (string_chars l))

let rec conv_bools l = match l with
 Nil -> ""
| Cons (True, l1) -> String.concat ""  ["1";(conv_bools l1)]
| Cons (False, l1) -> String.concat "" ["0";(conv_bools l1)]


let bool_conv l = List.fold_right (fun x y -> (if x = '1' then (Cons (True,y))
else (Cons (False,y))))  l Nil

let bools_string l = (bool_conv (string_chars l))

let rec conv_chars l = match l with
 Nil -> ""
| Cons (a, l1) -> String.concat ""  [(String.make 1 a); (conv_chars l1)]


let huffman m =
    ((huffman '0' eq_char (conv_string m)): (char code))

let encode (c:char code) l =
    (conv_bools (encode eq_char c (conv_string l)))

let decode (c:char code) l =
    (conv_chars (decode c (bools_string l)))

let rec  print_code_char1 f (l:(char code)) = match l with
 Nil -> ()
| Cons ((Pair (a, bs)), l1) -> Format.pp_print_char f a; 
                              Format.pp_print_string f " -> ";
                              Format.pp_print_string f (conv_bools bs);
                              Format.pp_print_newline f (); 
                              print_code_char1 f l1;;

let rec  print_code_char f (l:(char code)) = 
                              Format.pp_print_newline f (); 
                              print_code_char1 f l;;

#install_printer print_code_char;;

(*==========================================================*)
(*           Example                                        *)
(*==========================================================*)

let code = huffman "abbcccddddeeeee";;

let e = encode code "abcde";;

let d = decode code e;;

