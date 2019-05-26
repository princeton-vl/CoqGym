open Test_utils

let test_byte_vector (n : int) (f : int -> char) =
  let rec loop_write i =
    if (i = n)
    then Serializer_primitives.empty
    else (Serializer_primitives.append
            (Serializer_primitives.putByte (f i))
            (loop_write (i + 1))) in
  let rec loop_read bytes i =
    if not (i = n)
    then (assert (Bytes.get bytes i = f i);
          loop_read bytes (i + 1)) in
  let w = Serializer_primitives.wire_wrap (loop_write 0) in
  loop_read w 0

let main n =
  let rec loop i =
    if not (i = n)
    then (Printf.printf "Writing %d bytes...\n" i;
          test_byte_vector i (fun n -> Char.chr (n mod 256));
          loop (i + 1)) in
  loop 0

let test_int n =
  let rec loop i =
    if i < n
    then (test_serialize_deserialize
           (Int32.of_int i)
           (fun i -> Serializer_primitives.wire_wrap (Serializer_primitives.putInt i))
           (fun w -> match Serializer_primitives.deserialize_top
                             Serializer_primitives.getInt w with
                     | Some i -> i
                     | None -> failwith "Deserialization failed")
           (fun _ -> Printf.printf "%d" i);
          loop (i + 1)) in
  loop 0

let _ = main 10000;
        test_int 10000
