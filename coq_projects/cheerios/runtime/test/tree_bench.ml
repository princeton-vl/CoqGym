open Test_utils
open Tree_serializer
open Tree_test
   
let space_main () =
  let max_height = 16 in
  let rec loop i =
    if i < max_height
    then (compare_cheerios_marshal_space (fun n -> make false n 3) (tree_serialize_top) i;
          loop (i + 1))
  in
  Printf.printf "height cheerios marshal\n";
  loop 0   

let _ = space_main ()
