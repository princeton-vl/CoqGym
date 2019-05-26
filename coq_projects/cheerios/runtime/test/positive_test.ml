open Positive_serializer
open Test_utils

let rec print_positive p =
  match p with
  | XI p -> Printf.printf "XI "; print_positive p
  | XO p -> Printf.printf "XO "; print_positive p
  | XH -> Printf.printf "XH"

let make_positive n =
  let rec aux n flag k =
    if n = 0
    then k XH
    else aux (n - 1) (not flag) (if flag
                                 then fun p -> XI (k p)
                                 else fun p -> XO (k p)) in
  aux n true (fun p -> p)

let test_cheerios_top p print =
  test_serialize_deserialize p
                             positive_serialize_top
                             (fun w -> match positive_deserialize_top w with
                                       | Some p -> p
                                       | None -> failwith "Deserialization failed")
                             print

let test_cheerios_channel p print =
  let out_chan = open_out test_file_path in
  let write_out (p : positive) : in_channel =
    Serializer_primitives.to_channel (positive_serialize p) out_chan;
    flush out_chan; close_out out_chan;
    open_in test_file_path in
  let read_in (in_chan : in_channel) : positive =
    let res = Serializer_primitives.from_channel positive_deserialize in_chan in
    close_in in_chan;
    match res with
    | Some p -> p
    | None -> failwith "Deserialization failed" in
  test_serialize_deserialize p
                             write_out
                             read_in
                             print

let test_top max =
  let rec loop n =
    if n < max
    then (test_cheerios_top (make_positive n)
                        (fun _ -> Printf.printf "make_positive %d (vector)%!" n);
          loop (n + 1))
  in loop 0

let test_channel max =
  let rec loop n =
    if n < max
    then (test_cheerios_channel (make_positive n)
                        (fun _ -> Printf.printf "make_positive %d (file)%!" n);
          loop (n + 1))
  in loop 0


(* benchmarking *)
let bench_main () =
  compare_time_loop make_positive
                    200000 20000 100
                    positive_serialize_top
                    (fun w -> match positive_deserialize_top w with
                              | Some p -> p
                              | None -> failwith "Deserialization failed")

let space_main () =
  let max_length = 200000 in
  let rec loop i =
    if i < max_length
    then (compare_cheerios_marshal_space make_positive (positive_serialize_top) i;
          loop (i + 10000))
  in
  Printf.printf "height cheerios marshal\n";
  loop 0   
