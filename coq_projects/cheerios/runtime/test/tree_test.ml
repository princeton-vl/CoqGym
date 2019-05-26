open Tree_serializer
open Test_utils
       
let rec make elem height width =
  if height = 0
  then Atom elem
  else let rec loop n acc =
         if n = 0
         then acc
         else loop (n - 1) (make elem (height - 1) width :: acc) in
       Node (loop width [])

let test_width_top max_height width =
  let rec loop i =
    if i < max_height
    then (test_serialize_deserialize (make false i width)
                                     tree_serialize_top
                                     (fun w -> match tree_deserialize_top w with
                                               | Some p -> p
                                               | None -> failwith "Deserialization failed")
                                     (fun _ -> Printf.printf "height %d, width %d%!"
                                                             i width);
          loop (i + 1)) in
  loop 0

let test_width_channel max_height width =
  let rec loop i =
    let out_chan = open_out test_file_path in
    let write_out t =
      (try Serializer_primitives.to_channel (tree_serialize0 t) out_chan
       with Sys_error _ -> failwith "Failed serializing!");
      flush out_chan; close_out out_chan;
      open_in test_file_path in
    let read_in (in_chan : in_channel) =
      let res = Serializer_primitives.from_channel tree_deserialize0 in_chan in
      close_in in_chan;
      Printf.printf("Closed! ");
      match res with
      | Some t -> t
      | None -> failwith "Deserialization failed"  in
    if i < max_height
    then (test_serialize_deserialize (make false i width)
                                     write_out
                                     read_in
                                     (fun _ -> Printf.printf "height %d, width %d%!"
                                                             i width);
          loop (i + 1)) in
  loop 0

(* main functions *)
let test_main () =
  test_width_channel 15 2;
  test_width_channel 10 3;
  test_width_channel 10 4;
  test_width_channel 8 5




let bench_main () =
  compare_time_loop (fun n -> make false n 2)
                    20 1 10
                    tree_serialize_top
                    (fun w -> match tree_deserialize_top w with
                              | Some p -> p
                              | None -> failwith "Deserialization failed")

  
let avg_time_height (f : 'a tree -> 'b) (h : int) =
  let num_tries = 10 in
  avg (time_loop (fun n -> make false n 2) h num_tries f)

let main () = test_main ();
              bench_main ()

